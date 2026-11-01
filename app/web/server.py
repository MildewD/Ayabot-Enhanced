"""
BiliRobot WebUI — 送礼统计 & 精美导出

Features:
- 登录认证（config.yaml 可配置账号密码）
- 送礼排行 (礼物/盲盒/全部)
- 精美导出：多列布局、时间显示、类型筛选
- 手动清理旧数据
- 礼物图标来自 bilibili-api 官方
"""

from __future__ import annotations

import asyncio
import datetime
import hashlib
import json
import logging
import os
import re
import secrets
import sqlite3
import sys
import time
import uuid
from pathlib import Path
from typing import Any, Optional

import aiohttp
import yaml
from fastapi import FastAPI, Request, Response as FastResponse
from fastapi.responses import HTMLResponse, JSONResponse, Response
import uvicorn

from bilibili_api import live

from app.config import DEFAULT_ROOMS_DIR
from app.process_manager import start_room, stop_room, restart_room, room_status, clean_room, set_rooms_base_dir, start_room_async, stop_room_async, restart_room_async, start_periodic_log_cleanup, cleanup_all_stale_pidfiles, last_exit_code
from app.version import get_version_display

_APP_VERSION = get_version_display()

logger = logging.getLogger("webui")

# 全局配置，由 init_app() 设置
AUTH_USER = "ayabot"
AUTH_PASS = "123456"
_SESSION_TIMEOUT = 3600
_HTTP_HOST = "0.0.0.0"
_HTTP_PORT = int(os.environ.get("AYABOT_PORT", "19810"))
_DB_PATH = "data/bot.db"

# LLM 配置（可变引用，webui 可保存更新）
_LLM_CONFIG_DICT: dict[str, Any] = {}
_CONFIG_YAML_PATH: str = "config.yaml"
# 房间状态持久化文件（记录哪些房间在重启前是启动的）
_ROOM_STATES_PATH: str = "data/room_states.json"
# 外部 API Token（用于 astrbot 插件等第三方查询）
_API_TOKEN: str = ""
# 外部 API 域名（留空则自动检测）
_API_DOMAIN: str = ""

# 图片代理缓存
_IMAGE_CACHE_DIR: str = "data/cache/images"
_IMAGE_CACHE_MAX_AGE = 86400 * 7  # 磁盘缓存保留 7 天
_PROXY_SEMAPHORE = asyncio.Semaphore(3)  # 最多 3 个并发请求
_PROXY_IN_FLIGHT: dict[str, asyncio.Future] = {}  # 正在进行的请求去重


def _get_image_cache_path(url: str) -> Path:
    """根据 URL 生成缓存文件路径（以 URL 的 MD5 命名）。"""
    md5 = hashlib.md5(url.encode()).hexdigest()
    ext = Path(url.split("?")[0]).suffix or ".jpg"
    return Path(_IMAGE_CACHE_DIR) / f"{md5}{ext}"


def _clean_expired_cache() -> None:
    """清理过期缓存文件。"""
    try:
        cache_dir = Path(_IMAGE_CACHE_DIR)
        if not cache_dir.exists():
            return
        now = time.time()
        for f in cache_dir.iterdir():
            if f.is_file() and now - f.stat().st_mtime > _IMAGE_CACHE_MAX_AGE:
                f.unlink(missing_ok=True)
    except Exception:
        pass


def _save_image_cache(url: str, data: bytes) -> None:
    """保存图片到磁盘缓存。"""
    try:
        path = _get_image_cache_path(url)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    except Exception:
        pass


def _load_image_cache(url: str) -> Optional[bytes]:
    """从磁盘缓存读取图片，过期则删除并返回 None。"""
    try:
        path = _get_image_cache_path(url)
        if path.exists():
            age = time.time() - path.stat().st_mtime
            if age < _IMAGE_CACHE_MAX_AGE:
                return path.read_bytes()
            else:
                path.unlink(missing_ok=True)
    except Exception:
        pass
    return None


def _save_room_states() -> None:
    """保存当前各房间的运行状态到文件。"""
    try:
        rooms = _list_rooms_from_disk()
        states = {}
        for r in rooms:
            rid = r["room_id"]
            states[rid] = room_status(rid) == "running"
        Path(_ROOMS_BASE_DIR).resolve().joinpath(_ROOM_STATES_PATH).parent.mkdir(parents=True, exist_ok=True)
        Path(_ROOMS_BASE_DIR).resolve().joinpath(_ROOM_STATES_PATH).write_text(
            json.dumps(states, ensure_ascii=False), encoding="utf-8"
        )
    except Exception as exc:
        logger.warning("save room states failed: %s", exc)


def _load_room_states() -> dict[str, bool]:
    """读取之前保存的房间状态。"""
    try:
        p = Path(_ROOMS_BASE_DIR).resolve() / _ROOM_STATES_PATH
        if p.exists():
            return json.loads(p.read_text(encoding="utf-8"))
    except Exception as exc:
        logger.warning("load room states failed: %s", exc)
    return {}


# ── 期望状态（用户显式 start/stop 决定，守护进程据此自动恢复） ──

_DESIRED_STATES_PATH = "data/desired_states.json"


def _desired_path() -> Path:
    return Path(_ROOMS_BASE_DIR).resolve() / _DESIRED_STATES_PATH


def _load_desired_states() -> dict[str, bool]:
    p = _desired_path()
    if p.exists():
        try:
            data = json.loads(p.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                return {str(k): bool(v) for k, v in data.items()}
        except Exception as exc:
            logger.warning("load desired states failed: %s", exc)
    # 首次升级：从旧 room_states.json 迁移
    legacy = _load_room_states()
    if legacy:
        _save_desired_states(legacy)
        return legacy
    # 再退一步：托盘版会写 running_rooms.json（退出时快照），也当成期望运行
    tray_snapshot = _load_tray_running_rooms()
    if tray_snapshot:
        states = {rid: True for rid in tray_snapshot}
        _save_desired_states(states)
        logger.info("desired states 由 running_rooms.json 迁移: %s", list(states))
        return states
    # 最后一层：从各房间的心跳 phase 推断（崩溃/直接关电脑的用户没有上面两个文件）
    boot = _bootstrap_desired_from_heartbeats()
    if boot:
        _save_desired_states(boot)
        logger.info("desired states 由心跳推断: %s", boot)
        return boot
    return {}


def _bootstrap_desired_from_heartbeats() -> dict[str, bool]:
    """首次升级/首次运行：按心跳文件里的 phase 推断房间是否本来就该在跑。

    只认 phase=running 的（用户之前确实开着）。停过的房间心跳里是 stopped，
    不写进期望状态，避免升级后把用户主动停掉的房间拉起来。
    """
    states: dict[str, bool] = {}
    try:
        from app.config import DEFAULT_ROOMS_DIR  # noqa: PLC0415

        base = Path(_ROOMS_BASE_DIR).resolve() / DEFAULT_ROOMS_DIR
        if not base.exists():
            return {}
        for d in sorted(base.iterdir()):
            hb = d / "data" / "bot_status.json"
            if not hb.exists():
                continue
            try:
                data = json.loads(hb.read_text(encoding="utf-8"))
            except Exception:  # noqa: BLE001
                continue
            if isinstance(data, dict) and data.get("phase") == "running":
                states[d.name] = True
    except Exception as exc:  # noqa: BLE001
        logger.debug("bootstrap desired states failed: %s", exc)
    return states


def _load_tray_running_rooms() -> list[str]:
    """读取旧托盘版退出时写的 running_rooms.json（升级迁移用）。"""
    try:
        p = Path(_ROOMS_BASE_DIR).resolve() / "running_rooms.json"
        if p.exists():
            data = json.loads(p.read_text(encoding="utf-8"))
            if isinstance(data, list):
                return [str(x) for x in data if str(x).strip()]
    except Exception as exc:  # noqa: BLE001
        logger.debug("load running_rooms.json failed: %s", exc)
    return []


def _save_desired_states(states: dict[str, bool]) -> None:
    try:
        p = _desired_path()
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(states, ensure_ascii=False), encoding="utf-8")
    except Exception as exc:
        logger.warning("save desired states failed: %s", exc)


def _mark_desired(room_id: str, running: bool) -> None:
    states = _load_desired_states()
    states[str(room_id)] = bool(running)
    _save_desired_states(states)


def _room_data_file(room_id: str, name: str) -> Path:
    """房间 data 目录下的状态文件（心跳/凭证状态/崩溃记录）。"""
    return Path(_ROOMS_BASE_DIR).resolve() / "rooms" / room_id / "data" / name


def _read_room_json(room_id: str, name: str) -> dict:
    try:
        path = _room_data_file(room_id, name)
        if path.exists():
            data = json.loads(path.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                return data
    except Exception:  # noqa: BLE001
        pass
    return {}



def get_llm_config() -> dict[str, Any]:
    """公开访问 LLM 配置（bot 通过此函数获取运行时配置）."""
    return _LLM_CONFIG_DICT


def init_app(config: Any = None, config_path: str = "config.yaml") -> None:
    """从 AppConfig 初始化 WebUI 配置.
    
    Args:
        config: AppConfig 对象
        config_path: 配置文件的实际路径（用于解析相对路径）
    """
    global AUTH_USER, AUTH_PASS, _SESSION_TIMEOUT, _HTTP_HOST, _HTTP_PORT, _DB_PATH, _LLM_CONFIG_DICT, _CONFIG_YAML_PATH, _ROOMS_BASE_DIR, _API_TOKEN, _API_DOMAIN
    if config is None:
        _fallback_read_config()
        return
    AUTH_USER = config.web_ui.username
    AUTH_PASS = config.web_ui.password
    _SESSION_TIMEOUT = config.web_ui.session_timeout
    _HTTP_HOST = config.web_ui.host
    _HTTP_PORT = config.web_ui.port
    _DB_PATH = config.storage.sqlite_path
    if not os.path.isabs(_DB_PATH):
        _DB_PATH = str(Path(config_path).parent / _DB_PATH)
    _API_TOKEN = config.web_ui.api_token
    _API_DOMAIN = config.web_ui.api_domain
    _LLM_CONFIG_DICT.update({
        "enabled": config.llm.enabled,
        "provider": config.llm.provider,
        "api_key": config.llm.api_key,
        "base_url": config.llm.base_url,
        "model": config.llm.model,
        "wake_word": config.llm.wake_word,
        "temperature": config.llm.temperature,
        "top_p": config.llm.top_p,
        "max_tokens": config.llm.max_tokens,
        "system_prompt": config.llm.system_prompt,
        "context": {
            "enabled": config.llm.context.enabled,
            "mode": config.llm.context.mode,
            "content": config.llm.context.content,
            "max_messages": config.llm.context.max_messages,
        },
    })
    _CONFIG_YAML_PATH = config_path
    # 房间管理的基础目录 = 项目根目录（rooms/ 所在位置）
    # 当 config 在 rooms/<id>/config.yaml 时，往上两级到项目根
    cfg_parent = Path(_CONFIG_YAML_PATH).parent if _CONFIG_YAML_PATH else Path.cwd()
    if cfg_parent.parent.name == DEFAULT_ROOMS_DIR:
        _ROOMS_BASE_DIR = str(cfg_parent.parent.parent.resolve())
    else:
        _ROOMS_BASE_DIR = str(cfg_parent.resolve())
    set_rooms_base_dir(_ROOMS_BASE_DIR)
    logger.info("webui configured: host=%s port=%s db=%s", _HTTP_HOST, _HTTP_PORT, os.path.abspath(_DB_PATH))

    # 初始化/同步 users.json（不覆盖已通过 WebUI 修改过密码的账号）
    _init_users()

    # 初始化图片代理缓存目录
    global _IMAGE_CACHE_DIR
    _IMAGE_CACHE_DIR = str(Path(_ROOMS_BASE_DIR).resolve() / "data/cache/images")
    Path(_IMAGE_CACHE_DIR).mkdir(parents=True, exist_ok=True)
    _clean_expired_cache()
    logger.info("image proxy cache dir: %s", _IMAGE_CACHE_DIR)


def _fallback_read_config() -> None:
    global _DB_PATH, AUTH_USER, AUTH_PASS, _CONFIG_YAML_PATH, _LLM_CONFIG_DICT, _ROOMS_BASE_DIR, _API_TOKEN, _API_DOMAIN
    _cfg_path = Path("config.yaml")
    if _cfg_path.exists():
        _raw = yaml.safe_load(_cfg_path.read_text(encoding="utf-8")) or {}
        _DB_PATH = str(_raw.get("storage", {}).get("sqlite_path", "data/bot.db"))
        if not os.path.isabs(_DB_PATH):
            _DB_PATH = str(_cfg_path.parent / _DB_PATH)
        web_ui = _raw.get("web_ui", {}) or {}
        if web_ui.get("username"):
            AUTH_USER = web_ui["username"]
        if web_ui.get("password"):
            AUTH_PASS = web_ui["password"]
        _API_TOKEN = str(web_ui.get("api_token", ""))
        _API_DOMAIN = str(web_ui.get("api_domain", ""))
    _CONFIG_YAML_PATH = str(_cfg_path.resolve())
    _ROOMS_BASE_DIR = str(Path(_CONFIG_YAML_PATH).parent.resolve())
    set_rooms_base_dir(_ROOMS_BASE_DIR)
    # 加载 LLM 配置到内存
    llm_raw = _raw.get("llm", {}) if _cfg_path.exists() else {}
    _LLM_CONFIG_DICT.update({
        "enabled": llm_raw.get("enabled", False),
        "provider": llm_raw.get("provider", "openai"),
        "api_key": llm_raw.get("api_key", ""),
        "base_url": llm_raw.get("base_url", ""),
        "model": llm_raw.get("model", ""),
        "wake_word": llm_raw.get("wake_word", "ayabot"),
        "temperature": llm_raw.get("temperature", 0.7),
        "top_p": llm_raw.get("top_p", 0.9),
        "max_tokens": llm_raw.get("max_tokens", 150),
        "system_prompt": llm_raw.get("system_prompt", ""),
        "context": {
            "enabled": llm_raw.get("context", {}).get("enabled", True),
            "mode": llm_raw.get("context", {}).get("mode", "isolated"),
            "content": llm_raw.get("context", {}).get("content", "llm_only"),
            "max_messages": llm_raw.get("context", {}).get("max_messages", 10),
        },
    })
    logger.info("webui using db (fallback): %s", os.path.abspath(_DB_PATH))

    # 初始化/同步 users.json（不覆盖已修改过的密码）
    _init_users()


app = FastAPI(title="BiliRobot Manager")

# ══════════════════════════════════════════════════════════════════
#  Auth
# ══════════════════════════════════════════════════════════════════

_SESSIONS: dict[str, tuple[float, str, str, list]] = {}  # token -> (expiry, username, role, allowed_rooms)
_RATE_LIMIT: dict[str, list[float]] = {}  # ip -> [timestamps]
_AUTH_CONFIG_PATH: str = "data/users.json"


def _hash_password(password: str) -> str:
    return hashlib.sha256(password.encode("utf-8")).hexdigest()


def _migrate_old_users(old_file: Path, users: dict) -> dict:
    """Migrate plain-text passwords and old format to new format."""
    try:
        old = json.loads(old_file.read_text(encoding="utf-8"))
    except Exception:
        return users
    for uname, info in old.items():
        if uname in users:
            continue
        pw = info.get("password", "")
        role = info.get("role", "user")
        allowed_rooms = info.get("rooms", info.get("allowed_rooms", []))
        if role == "streamer":
            role = "user"
        users[uname] = {
            "password_hash": _hash_password(pw) if pw else "",
            "role": role,
            "allowed_rooms": allowed_rooms,
        }
    old_file.rename(old_file.with_suffix(".json.bak"))
    return users


def _load_users() -> dict:
    """加载用户配置. 返回 {username: {password_hash, role, allowed_rooms}}"""
    p = Path(_ROOMS_BASE_DIR).resolve() / _AUTH_CONFIG_PATH
    if p.exists():
        try:
            return json.loads(p.read_text(encoding="utf-8"))
        except Exception:
            pass
    # Migrate old auth/users.json if present
    old_p = Path(_ROOMS_BASE_DIR).resolve() / "auth" / "users.json"
    if old_p.exists():
        return _migrate_old_users(old_p, {})
    return {}


def _save_users(users: dict) -> None:
    p = Path(_ROOMS_BASE_DIR).resolve() / _AUTH_CONFIG_PATH
    p.parent.mkdir(parents=True, exist_ok=True)
    # Strip plain-text passwords for safety, keep only password_hash
    clean = {}
    for uname, info in users.items():
        entry = {
            "password_hash": info.get("password_hash", _hash_password(info.get("password", ""))),
            "role": info.get("role", "user"),
            "allowed_rooms": info.get("allowed_rooms", info.get("rooms", [])),
        }
        if info.get("must_reset_password"):
            entry["must_reset_password"] = True
        clean[uname] = entry
    p.write_text(json.dumps(clean, ensure_ascii=False, indent=2), encoding="utf-8")


def _init_users() -> None:
    """初始化 users.json：创建默认账号但不覆盖已通过 WebUI 修改过的密码。"""
    users = _load_users()
    default_pw_hash = _hash_password("123456")
    # AUTH_USER（config.yaml 管理员账号）不存在则创建
    if AUTH_USER not in users:
        users[AUTH_USER] = {"password_hash": _hash_password(AUTH_PASS), "role": "admin", "allowed_rooms": []}
    # ayabot 默认账号不存在则创建
    if "ayabot" not in users:
        users["ayabot"] = {"password_hash": default_pw_hash, "role": "admin", "allowed_rooms": [], "must_reset_password": True}
    else:
        # ayabot 存在且密码仍是默认 123456 → 补 must_reset_password 标记
        ayabot = users["ayabot"]
        if ayabot.get("password_hash") == default_pw_hash and "must_reset_password" not in ayabot:
            ayabot["must_reset_password"] = True
    _save_users(users)


def _user_role(token: str) -> tuple[str, str, list]:
    """返回 (username, role, allowed_rooms) 或 (\"\", \"\", [])"""
    sess = _SESSIONS.get(token)
    if sess and sess[0] > time.time():
        return (sess[1], sess[2], sess[3])
    return ("", "", [])


def _check_auth(request: Request) -> bool:
    token = request.cookies.get("session")
    if token and token in _SESSIONS:
        sess = _SESSIONS[token]
        if sess[0] > time.time():
            return True
        else:
            _SESSIONS.pop(token, None)
    return False


def _rate_limited(ip: str) -> bool:
    now = time.time()
    if ip not in _RATE_LIMIT:
        _RATE_LIMIT[ip] = []
    # Clean old entries (>60s)
    _RATE_LIMIT[ip] = [t for t in _RATE_LIMIT[ip] if now - t < 60]
    if len(_RATE_LIMIT[ip]) >= 60:  # max 60 req/min per IP
        return True
    _RATE_LIMIT[ip].append(now)
    return False


# ══════════════════════════════════════════════════════════════════
#  Gift icon cache
# ══════════════════════════════════════════════════════════════════

_GIFT_ICON_CACHE: dict[int, str] = {}
_GIFT_NAME_CACHE: dict[str, str] = {}
_GIFT_CACHE_BUILT = False


async def _build_gift_cache() -> None:
    global _GIFT_ICON_CACHE, _GIFT_NAME_CACHE, _GIFT_CACHE_BUILT
    if _GIFT_CACHE_BUILT:
        return
    try:
        data = await asyncio.wait_for(live.get_gift_config(), timeout=8)
    except asyncio.TimeoutError:
        logger.warning("get_gift_config timed out (network issue)")
        _GIFT_CACHE_BUILT = True
        return
    except Exception as exc:
        logger.warning("get_gift_config failed: %s", exc)
        _GIFT_CACHE_BUILT = True
        return

    cache_id: dict[int, str] = {}
    cache_name: dict[str, str] = {}
    for g in data.get("list", []):
        gid = _safe_int(g.get("id"))
        name = g.get("name", "")
        icon = g.get("img_basic") or ""
        if not icon:
            continue
        if gid > 0:
            cache_id[gid] = icon
        if name:
            cache_name[name] = icon
    _GIFT_ICON_CACHE = cache_id
    _GIFT_NAME_CACHE = cache_name
    _GIFT_CACHE_BUILT = True
    logger.info("gift cache built: %d by id, %d by name", len(cache_id), len(cache_name))


async def _ensure_gift_cache() -> None:
    if not _GIFT_CACHE_BUILT:
        await _build_gift_cache()


# ══════════════════════════════════════════════════════════════════
#  DB
# ══════════════════════════════════════════════════════════════════

def _get_db() -> sqlite3.Connection:
    conn = sqlite3.connect(_DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn


def _parse_date(d: str) -> tuple[int, int]:
    dt = datetime.datetime.strptime(d, "%Y-%m-%d")
    start = int(dt.timestamp())
    end = int((dt + datetime.timedelta(days=1)).timestamp())
    return start, end


def _safe_int(val: Any) -> int:
    try:
        return int(val)
    except (ValueError, TypeError):
        return 0


# ══════════════════════════════════════════════════════════════════
#  Startup
# ══════════════════════════════════════════════════════════════════

@app.on_event("startup")
async def _startup():
    # 后台加载礼物缓存，不阻塞启动
    asyncio.create_task(_build_gift_cache())
    # 后台预热「检查更新」结果（用户打开页面时秒回）
    asyncio.create_task(_warm_update_cache())
    # 启动定期日志清理（后台线程，默认保留 3 天）
    start_periodic_log_cleanup()
    # 自动启动所有已配置的房间（Docker 部署时自动拉起）
    asyncio.create_task(_auto_start_rooms())
    # 房间守护：崩溃/假死自动恢复
    asyncio.create_task(_supervise_loop())


@app.on_event("shutdown")
async def _shutdown():
    """关闭时停掉所有正在运行的房间 Bot。"""
    logger.info("WebUI shutting down, stopping all room bots...")
    try:
        rooms = _list_rooms_from_disk()
        for r in rooms:
            if r["status"] == "running":
                await stop_room_async(r["room_id"])
    except Exception as exc:
        logger.warning("shutdown cleanup failed: %s", exc)


async def _auto_start_rooms() -> None:
    """延迟扫描 rooms/ 目录，按上次状态自动启停房间 Bot。"""
    try:
        await asyncio.sleep(3)
        cleanup_all_stale_pidfiles()
        saved = _load_room_states()
        desired = _load_desired_states()
        rooms = _list_rooms_from_disk()
        if not rooms:
            logger.info("auto-start: no rooms found on disk")
            return
        started = 0
        for room in rooms:
            room_id = room["room_id"]
            should_run = desired.get(room_id, saved.get(room_id, False))
            status = room_status(room_id)
            if should_run and status != "running":
                logger.info("auto-start: starting room %s (was running before restart)", room_id)
                ok = await start_room_async(room_id)
                if ok:
                    started += 1
                else:
                    logger.warning("auto-start: room %s failed to start", room_id)
            elif not should_run and status == "running":
                logger.info("auto-start: stopping room %s (was stopped before restart)", room_id)
                await stop_room_async(room_id)
            else:
                logger.debug("auto-start: room %s status unchanged, skip", room_id)
        logger.info("auto-start: %d rooms auto-started", started)
        # 保存启动后的状态
        _save_room_states()
    except Exception as exc:
        logger.error("auto-start: error: %s", exc, exc_info=True)


# ══════════════════════════════════════════════════════════════════
#  房间守护：崩溃/假死自动恢复
# ══════════════════════════════════════════════════════════════════

_SUPERVISE_INTERVAL = 20.0          # 巡检间隔（秒）
_HEARTBEAT_STALE_SECONDS = 180      # 心跳超过该时长视为假死
_CRASH_WINDOW = 900.0               # 崩溃统计窗口（15 分钟）
_CRASH_MAX_ATTEMPTS = 5             # 窗口内最多自动重启次数
_CRASH_COOLDOWN = 600.0             # 超过次数后冷却 10 分钟

_restart_attempts: dict[str, list[float]] = {}
_zombie_restarts: dict[str, float] = {}
_no_heartbeat_since: dict[str, float] = {}
_NO_HEARTBEAT_GRACE = 120.0        # 状态 running 但从未写过心跳，宽限这么久


def _crash_info_path(room_id: str) -> Path:
    return Path(_ROOMS_BASE_DIR).resolve() / "rooms" / room_id / "data" / "crash_info.json"


def _write_crash_info(room_id: str, reason: str, exit_code: Optional[int] = None) -> None:
    try:
        path = _crash_info_path(room_id)
        path.parent.mkdir(parents=True, exist_ok=True)
        payload = {
            "ts": int(time.time()),
            "reason": reason,
            "exit_code": exit_code,
            "attempts": len(_restart_attempts.get(room_id, [])),
        }
        path.write_text(json.dumps(payload, ensure_ascii=False), encoding="utf-8")
    except Exception as exc:  # noqa: BLE001
        logger.debug("write crash info failed: %s", exc)


def _read_crash_info(room_id: str) -> dict:
    try:
        path = _crash_info_path(room_id)
        if path.exists():
            data = json.loads(path.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                return data
    except Exception:  # noqa: BLE001
        pass
    return {}


def _restart_allowed(room_id: str, now: float) -> bool:
    """崩溃重启限流：窗口内最多 5 次，超限后冷却。"""
    history = [t for t in _restart_attempts.get(room_id, []) if now - t < _CRASH_WINDOW]
    _restart_attempts[room_id] = history
    if len(history) < _CRASH_MAX_ATTEMPTS:
        return True
    return (now - history[-1]) > _CRASH_COOLDOWN


async def _recover_room(room_id: str, reason: str, now: float) -> None:
    if not _restart_allowed(room_id, now):
        logger.warning(
            "supervisor: room %s crashed too often (%d times/15min), 冷却中，暂停自动重启",
            room_id, len(_restart_attempts.get(room_id, [])),
        )
        return
    _restart_attempts.setdefault(room_id, []).append(now)
    exit_code = last_exit_code(room_id)
    _write_crash_info(room_id, reason, exit_code)
    logger.warning(
        "supervisor: room %s %s (exit_code=%s) — 自动重启 (第 %d 次)",
        room_id, reason, exit_code, len(_restart_attempts[room_id]),
    )
    try:
        ok = await restart_room_async(room_id)
        if not ok:
            logger.error("supervisor: room %s restart failed", room_id)
    except Exception as exc:  # noqa: BLE001
        logger.error("supervisor: room %s restart error: %s", room_id, exc, exc_info=True)


async def _supervise_once() -> None:
    desired = _load_desired_states()
    if not desired:
        return
    rooms = {r["room_id"] for r in _list_rooms_from_disk()}
    now = time.time()
    for room_id, should_run in desired.items():
        if not should_run or room_id not in rooms:
            continue
        try:
            if room_status(room_id) != "running":
                # 用户主动点「停止」会把 desired 置 false，所以这里只可能是崩溃
                await _recover_room(room_id, "进程已退出", now)
                continue

            heartbeat = _read_room_json(room_id, "bot_status.json")
            ts = int(heartbeat.get("ts") or 0)
            if not ts:
                # 状态 running 但从未写过心跳：僵尸 Task（事件循环已关）或卡在启动。
                # 旧版这里直接 continue，于是这类房间永远「看起来在跑、实际全废」。
                first_seen = _no_heartbeat_since.setdefault(room_id, now)
                if now - first_seen <= _NO_HEARTBEAT_GRACE:
                    continue
                if now - _zombie_restarts.get(room_id, 0.0) < _CRASH_COOLDOWN:
                    continue
                _zombie_restarts[room_id] = now
                _write_crash_info(room_id, f"运行中但 {int(now - first_seen)}s 没有心跳（疑似僵尸任务）", None)
                logger.warning(
                    "supervisor: room %s 状态 running 但无心跳 %.0fs — 重启",
                    room_id, now - first_seen,
                )
                try:
                    await restart_room_async(room_id)
                except Exception as exc:  # noqa: BLE001
                    logger.error("supervisor: room %s 僵尸重启失败: %s", room_id, exc)
                continue
            _no_heartbeat_since.pop(room_id, None)
            stale = now - ts
            if stale <= _HEARTBEAT_STALE_SECONDS:
                continue
            # 进程还在但心跳停了：卡死 / 事件循环阻塞 / 连接僵死
            if now - _zombie_restarts.get(room_id, 0.0) < _CRASH_COOLDOWN:
                continue
            _zombie_restarts[room_id] = now
            _write_crash_info(room_id, f"心跳超时 {int(stale)}s（疑似卡死）", None)
            logger.warning(
                "supervisor: room %s heartbeat stale %.0fs — 重启", room_id, stale
            )
            try:
                await restart_room_async(room_id)
            except Exception as exc:  # noqa: BLE001
                logger.error("supervisor: zombie restart failed for %s: %s", room_id, exc)
        except Exception as exc:  # noqa: BLE001
            logger.error("supervisor: room %s check error: %s", room_id, exc, exc_info=True)


async def _supervise_loop() -> None:
    """后台巡检：进程崩溃/假死时自动重启（Windows 上「机器人意外关闭」的兜底）。"""
    await asyncio.sleep(_SUPERVISE_INTERVAL)
    logger.info("room supervisor started (interval=%ss)", int(_SUPERVISE_INTERVAL))
    while True:
        try:
            await _supervise_once()
        except Exception as exc:  # noqa: BLE001
            logger.error("supervisor error: %s", exc, exc_info=True)
        await asyncio.sleep(_SUPERVISE_INTERVAL)


# ══════════════════════════════════════════════════════════════════
#  Auth middleware
# ══════════════════════════════════════════════════════════════════

def _get_current_role(request: Request) -> tuple[str, str, list]:
    """返回 (username, role, allowed_rooms) 或 ("", "", [])"""
    token = request.cookies.get("session", "")
    return _user_role(token)


@app.middleware("http")
async def _auth_middleware(request: Request, call_next):
    client_ip = request.client.host if request.client else "unknown"

    # Allow login page, auth endpoint, image proxy, and static icons without auth
    path = request.url.path
    if (path in ("/", "/api/login", "/favicon.ico", "/icon-192.png")
            or path.startswith("/api/external/")
            or path.startswith("/api/proxy_image")):
        return await call_next(request)

    if _rate_limited(client_ip):
        return JSONResponse({"error": "rate limited"}, status_code=429)

    # API paths need auth
    if not _check_auth(request):
        if path.startswith("/api/"):
            return JSONResponse({"error": "unauthorized"}, status_code=401)
        return FastResponse(
            content='<script>window.location.href="/"</script>',
            status_code=302,
        )

    # ── Role-based access control ──
    _, role, _ = _get_current_role(request)
    method = request.method

    # Admin can do everything
    if role == "admin":
        return await call_next(request)

    # Regular user restrictions
    if role == "user":
        # Blocked paths for regular users
        if path.startswith("/api/admin/"):
            return JSONResponse({"error": "forbidden"}, status_code=403)
        if path == "/api/general_config" and method == "POST":
            return JSONResponse({"error": "forbidden"}, status_code=403)
        if path == "/api/llm_config" and method == "POST":
            return JSONResponse({"error": "forbidden"}, status_code=403)
        if path in ("/api/users", "/api/users/update", "/api/users/admin_password") or \
           path.startswith("/api/users/"):
            return JSONResponse({"error": "forbidden"}, status_code=403)

    return await call_next(request)


# ══════════════════════════════════════════════════════════════════
#  Auth API
# ══════════════════════════════════════════════════════════════════

@app.post("/api/login")
async def api_login(request: Request):
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"error": "bad request"}, status_code=400)

    username = body.get("username", "")
    password = body.get("password", "")

    # 检查多用户配置（使用密码哈希比对）
    users = _load_users()
    user_info = users.get(username)
    must_reset = False
    if user_info:
        stored_hash = user_info.get("password_hash", "")
        if stored_hash and stored_hash == _hash_password(password):
            role = user_info.get("role", "user")
            allowed_rooms = user_info.get("allowed_rooms", [])
            must_reset = user_info.get("must_reset_password", False)
        else:
            return JSONResponse({"error": "wrong credentials"}, status_code=403)
    elif username == AUTH_USER and password == AUTH_PASS:
        # 兼容旧配置（config.yaml 中的账号密码）
        role = "admin"
        allowed_rooms = []
    else:
        return JSONResponse({"error": "wrong credentials"}, status_code=403)

    token = secrets.token_hex(32)
    _SESSIONS[token] = (time.time() + _SESSION_TIMEOUT, username, role, allowed_rooms)

    resp = JSONResponse({"ok": True, "token": token, "role": role, "username": username, "must_reset_password": must_reset})
    resp.set_cookie(
        key="session", value=token,
        max_age=_SESSION_TIMEOUT,
        httponly=True, samesite="lax",
    )
    return resp


# ══════════════════════════════════════════════════════════════════
#  Data API
# ══════════════════════════════════════════════════════════════════

@app.get("/api/ranking")
async def api_ranking(start: str, end: str, gift_type: str = "all"):
    """
    gift_type: all / gift / blindbox
    """
    try:
        s_start, _ = _parse_date(start)
        _, e_end = _parse_date(end)

        where_clause = "ts >= ? AND ts < ?"
        params: list[Any] = [s_start, e_end]

        if gift_type == "blindbox":
            where_clause += " AND is_blind_box = 1"
        elif gift_type == "gift":
            where_clause += " AND is_blind_box = 0"

        conn = _get_db()
        rows = conn.execute(
            f"""
            SELECT uid, uname,
                   CAST(SUM(actual_value) AS REAL) AS total_val,
                   CAST(SUM(profit_value)  AS REAL) AS total_profit,
                   CAST(SUM(CASE WHEN is_blind_box=1 THEN gift_num ELSE 0 END) AS INTEGER) AS blindbox_count,
                   CAST(SUM(CASE WHEN is_blind_box=0 THEN gift_num ELSE 0 END) AS INTEGER) AS gift_count
            FROM gift_events
            WHERE {where_clause}
            GROUP BY uid
            ORDER BY total_val DESC
            LIMIT 20
            """,
            params,
        ).fetchall()
        return [dict(r) for r in rows]
    except Exception as exc:
        logger.exception("ranking api failed")
        return JSONResponse({"error": str(exc)}, status_code=500)


@app.get("/api/user_gifts")
async def api_user_gifts(uid: int, date: str, gift_type: str = "all"):
    try:
        await _ensure_gift_cache()
        day_start, day_end = _parse_date(date)

        where_clause = "uid = ? AND ts >= ? AND ts < ?"
        params: list[Any] = [uid, day_start, day_end]

        if gift_type == "blindbox":
            where_clause += " AND is_blind_box = 1"
        elif gift_type == "gift":
            where_clause += " AND is_blind_box = 0"

        conn = _get_db()
        rows = conn.execute(
            f"SELECT * FROM gift_events WHERE {where_clause} ORDER BY ts ASC",
            params,
        ).fetchall()

        results = []
        last_guard: dict[int, int] = {}  # uid -> 从 SEND_GIFT 记住的 guard_level
        for r in rows:
            item = dict(r)
            raw = json.loads(item.pop("raw_json", "{}")) if isinstance(item.get("raw_json"), str) else {}

            # COMBO_SEND 是连击总结包，其数量是前面SEND_GIFT的总和
            # 过滤掉避免重复计数，SEND_GIFT已完整记录了每次送礼
            if item.get("event_type", "") == "COMBO_SEND":
                # 但它的 guard_level 可以拿来给后续事件兜底（实际上相同UID的后继事件可能有完整数据）
                # 从 sender_uinfo 提取头像兜底
                if not raw.get("face"):
                    raw["face"] = raw.get("sender_uinfo", {}).get("base", {}).get("face", "")
                continue

            # 头像
            face = raw.get("face") or raw.get("data", {}).get("face") or ""
            item["avatar"] = face

            # 大航海等级
            guard = _safe_int(raw.get("guard_level") or raw.get("data", {}).get("guard_level", 0))
            if guard:
                last_guard[item["uid"]] = guard
            item["guard_level"] = guard

            gift_id = _safe_int(raw.get("giftId") or raw.get("gift_id") or 0)
            gift_name = raw.get("giftName") or raw.get("gift_name") or item.get("gift_name", "")
            item["gift_name"] = gift_name

            # 图标：按 id 查，查不到按名字查；COMBO_SEND 额外查 gift_info
            icon = ""
            if gift_id and gift_id in _GIFT_ICON_CACHE:
                icon = _GIFT_ICON_CACHE[gift_id]
            elif gift_name and gift_name in _GIFT_NAME_CACHE:
                icon = _GIFT_NAME_CACHE[gift_name]
            if not icon:
                icon = raw.get("gift_info", {}).get("img_basic", "")
            item["gift_icon"] = icon

            item["price"] = _safe_int(raw.get("price") or raw.get("total_coin") or 0)

            results.append(item)

        # 合并：相同礼物、相同 guard_level、2分钟内 → 合并数量
        merged: list[dict[str, Any]] = []
        for item in results:
            if merged:
                last = merged[-1]
                same_gift = last["gift_name"] == item["gift_name"]
                same_guard = last["guard_level"] == item["guard_level"]
                time_diff = abs(item["ts"] - last["ts"]) < 120
                if same_gift and same_guard and time_diff:
                    last["gift_num"] += item["gift_num"]
                    last["ts"] = max(last["ts"], item["ts"])
                    continue
            merged.append(item)
        return merged
    except Exception as exc:
        logger.exception("user_gifts api failed")
        return JSONResponse({"error": str(exc)}, status_code=500)


@app.get("/api/user_dates")
async def api_user_dates(uid: int):
    """获取某用户有送礼记录的所有日期（去重后的 YYYY-MM-DD 列表）."""
    try:
        conn = _get_db()
        rows = conn.execute(
            """
            SELECT DISTINCT strftime('%Y-%m-%d', ts, 'unixepoch', 'localtime') AS d
            FROM gift_events
            WHERE uid = ?
            ORDER BY d DESC
            LIMIT 60
            """,
            (uid,),
        ).fetchall()
        return [r["d"] for r in rows if r["d"]]
    except Exception as exc:
        logger.exception("user_dates api failed")
        return JSONResponse({"error": str(exc)}, status_code=500)


@app.post("/api/delete_old")
async def api_delete_old(request: Request):
    """删除指定日期之前的数据."""
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"error": "bad request"}, status_code=400)

    date_str = body.get("date", "")
    try:
        dt = datetime.datetime.strptime(date_str, "%Y-%m-%d")
        before_ts = int(dt.timestamp())
    except ValueError:
        return JSONResponse({"error": "bad date format, use YYYY-MM-DD"}, status_code=400)

    try:
        conn = _get_db()
        deleted = conn.execute("DELETE FROM gift_events WHERE ts < ?", (before_ts,)).rowcount
        conn.execute("DELETE FROM monthly_blindbox_stats WHERE month < ?", (dt.strftime("%Y-%m"),))
        conn.execute("DELETE FROM monthly_gift_stats WHERE month < ?", (dt.strftime("%Y-%m"),))
        conn.commit()
        return {"deleted_events": deleted}
    except Exception as exc:
        logger.exception("delete failed")
        return JSONResponse({"error": str(exc)}, status_code=500)


# ══════════════════════════════════════════════════════════════════
#  Image proxy
# ══════════════════════════════════════════════════════════════════

@app.get("/api/proxy_image")
async def api_proxy_image(url: str):
    # 1. 检查磁盘缓存
    cached = _load_image_cache(url)
    if cached is not None:
        return Response(
            content=cached,
            media_type="image/jpeg",
            headers={
                "Access-Control-Allow-Origin": "*",
                "Cache-Control": "public, max-age=86400",
                "X-Cache": "HIT",
            },
        )

    # 2. 请求去重：同一个 URL 正在请求中则等待结果
    if url in _PROXY_IN_FLIGHT:
        try:
            result = await _PROXY_IN_FLIGHT[url]
            if result is not None:
                return result
        except Exception:
            pass

    # 3. 发起请求（限制并发）
    future: asyncio.Future = asyncio.Future()
    _PROXY_IN_FLIGHT[url] = future
    try:
        async with _PROXY_SEMAPHORE:
            async with aiohttp.ClientSession() as session:
                for attempt in range(3):
                    try:
                        async with session.get(
                            url,
                            timeout=aiohttp.ClientTimeout(total=10),
                            headers={"User-Agent": "Mozilla/5.0 Ayabot Proxy"},
                        ) as resp:
                            if resp.status == 429:
                                wait = 1.0 * (2 ** attempt)
                                logger.warning(
                                    "proxy_image 429 for %s, retrying in %.1fs (attempt %d/3)",
                                    url, wait, attempt + 1,
                                )
                                await asyncio.sleep(wait)
                                continue
                            if resp.status != 200:
                                raise ValueError(f"HTTP {resp.status}")
                            body = await resp.read()
                            ct = resp.content_type or "image/jpeg"
                            # 写入磁盘缓存（异步不阻塞）
                            _save_image_cache(url, body)
                            result = Response(
                                content=body,
                                media_type=ct,
                                headers={
                                    "Access-Control-Allow-Origin": "*",
                                    "Cache-Control": "public, max-age=86400",
                                    "X-Cache": "MISS",
                                },
                            )
                            future.set_result(result)
                            return result
                    except (aiohttp.ClientError, asyncio.TimeoutError) as e:
                        if attempt < 2:
                            await asyncio.sleep(0.5 * (2 ** attempt))
                            continue
                        raise
                # 重试耗尽
                raise ValueError("429 retry exhausted")
    except Exception as exc:
        logger.warning("proxy_image failed for %s: %s", url, exc)
        result = Response(status_code=302, headers={"Location": url})
        future.set_result(result)
        return result
    finally:
        _PROXY_IN_FLIGHT.pop(url, None)


# ══════════════════════════════════════════════════════════════════
#  LLM Config API
# ══════════════════════════════════════════════════════════════════


@app.get("/api/llm_config")
async def api_get_llm_config():
    """返回 LLM 配置（含完整 api_key，前端自行决定是否掩码显示）."""
    ctx = _LLM_CONFIG_DICT.get("context", {})
    return {
        "enabled": _LLM_CONFIG_DICT.get("enabled", False),
        "provider": _LLM_CONFIG_DICT.get("provider", "openai"),
        "has_api_key": bool(_LLM_CONFIG_DICT.get("api_key")),
        "api_key": _LLM_CONFIG_DICT.get("api_key", ""),
        "base_url": _LLM_CONFIG_DICT.get("base_url", ""),
        "model": _LLM_CONFIG_DICT.get("model", ""),
        "wake_word": _LLM_CONFIG_DICT.get("wake_word", "ayabot"),
        "temperature": _LLM_CONFIG_DICT.get("temperature", 0.7),
        "top_p": _LLM_CONFIG_DICT.get("top_p", 0.9),
        "max_tokens": _LLM_CONFIG_DICT.get("max_tokens", 150),
        "system_prompt": _LLM_CONFIG_DICT.get("system_prompt", ""),
        "context": {
            "enabled": ctx.get("enabled", True),
            "mode": ctx.get("mode", "isolated"),
            "content": ctx.get("content", "llm_only"),
            "max_messages": ctx.get("max_messages", 10),
        },
    }


@app.post("/api/llm_config")
async def api_save_llm_config(request: Request):
    """保存 LLM 配置到 config.yaml 并更新内存."""
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"error": "bad request"}, status_code=400)

    # 更新内存中的配置
    for key in ("enabled", "provider", "api_key", "base_url", "model", "wake_word", "temperature", "top_p", "max_tokens", "system_prompt"):
        if key in body:
            _LLM_CONFIG_DICT[key] = body[key]
    if "context" in body and isinstance(body["context"], dict):
        _LLM_CONFIG_DICT.setdefault("context", {})
        for ck in ("enabled", "mode", "content", "max_messages"):
            if ck in body["context"]:
                _LLM_CONFIG_DICT["context"][ck] = body["context"][ck]

    # 回写到 config.yaml
    try:
        cfg_path = Path(_CONFIG_YAML_PATH)
        raw = yaml.safe_load(cfg_path.read_text(encoding="utf-8")) or {}

        llm_section = raw.setdefault("llm", {})
        llm_section["enabled"] = _LLM_CONFIG_DICT.get("enabled", False)
        llm_section["provider"] = _LLM_CONFIG_DICT.get("provider", "openai")
        llm_section["api_key"] = _LLM_CONFIG_DICT.get("api_key", "")
        llm_section["base_url"] = _LLM_CONFIG_DICT.get("base_url", "")
        llm_section["model"] = _LLM_CONFIG_DICT.get("model", "")
        llm_section["wake_word"] = _LLM_CONFIG_DICT.get("wake_word", "ayabot")
        llm_section["temperature"] = _LLM_CONFIG_DICT.get("temperature", 0.7)
        llm_section["top_p"] = _LLM_CONFIG_DICT.get("top_p", 0.9)
        llm_section["max_tokens"] = _LLM_CONFIG_DICT.get("max_tokens", 150)
        llm_section["system_prompt"] = _LLM_CONFIG_DICT.get("system_prompt", "")
        llm_section["context"] = {
            "enabled": _LLM_CONFIG_DICT.get("context", {}).get("enabled", True),
            "mode": _LLM_CONFIG_DICT.get("context", {}).get("mode", "isolated"),
            "content": _LLM_CONFIG_DICT.get("context", {}).get("content", "llm_only"),
            "max_messages": _LLM_CONFIG_DICT.get("context", {}).get("max_messages", 10),
        }

        # 手动写 YAML 保留锚点和格式
        cfg_path.write_text(yaml.dump(raw, default_flow_style=False, allow_unicode=True), encoding="utf-8")
        logger.info("llm config saved to %s", cfg_path)
    except Exception as exc:
        logger.warning("failed to save config.yaml: %s", exc)
        return JSONResponse({"error": f"save failed: {exc}"}, status_code=500)

    return {"ok": True}


@app.post("/api/llm_test")
async def api_llm_test(request: Request):
    """测试 LLM 连接."""
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"error": "bad request"}, status_code=400)

    from app.llm_client import LLMClient

    client = LLMClient(
        provider=_LLM_CONFIG_DICT.get("provider", "openai"),
        api_key=_LLM_CONFIG_DICT.get("api_key", ""),
        base_url=_LLM_CONFIG_DICT.get("base_url", ""),
        model=_LLM_CONFIG_DICT.get("model", ""),
        system_prompt=_LLM_CONFIG_DICT.get("system_prompt", ""),
    )
    text = body.get("text", "")
    reply = await client.chat(user_text=text, uname="测试")
    return {"reply": reply or "(无回复)"}


@app.post("/api/restart")
async def api_restart():
    """重启 B站 Bot 服务（委托 ProcessManager 重新启动当前房间）. """
    return {"ok": True, "message": "多房间模式下请在房间详情中操作"}


# ══════════════════════════════════════════════════════════════
#  B站 扫码登录 API
# ══════════════════════════════════════════════════════════════
# ══════════════════════════════════════════════════════════════

import io as _io
import base64 as _base64
from bilibili_api import login_v2

# 存储活跃的 QR 登录会话 (session_id → QRLoginObj + QR image)
_BILI_LOGIN_SESSIONS: dict[str, dict] = {}


@app.post("/api/bili_login/start")
async def api_bili_login_start():
    """生成 B站 QR 登录二维码并返回 session_id."""
    import qrcode
    import uuid
    import time as _time

    session_id = uuid.uuid4().hex[:12]

    qr = login_v2.QrCodeLogin(platform=login_v2.QrCodeLoginChannel.WEB)
    await qr.generate_qrcode()

    # 获取 QR URL（使用属性访问，bilibili_api 内部用 name mangling）
    qr_url = qr._QrCodeLogin__qr_link  # noqa: SLF001

    # 用 Python qrcode 生成 base64 图片
    qr_img = qrcode.make(qr_url)
    buf = _io.BytesIO()
    qr_img.save(buf, format="PNG")
    img_b64 = _base64.b64encode(buf.getvalue()).decode("ascii")

    _BILI_LOGIN_SESSIONS[session_id] = {
        "qr": qr,
        "created_at": _time.time(),
        "state": "waiting",
    }

    return {
        "ok": True,
        "session_id": session_id,
        "qr_image": f"data:image/png;base64,{img_b64}",
        "qr_url": qr_url,
    }


@app.get("/api/bili_login/status")
async def api_bili_login_status(session_id: str):
    """查询 B站 QR 登录状态."""
    sess = _BILI_LOGIN_SESSIONS.get(session_id)
    if not sess:
        return {"state": "expired"}

    qr = sess["qr"]

    if qr.has_done():
        sess["state"] = "done"
        return {"state": "done"}

    try:
        state = await qr.check_state()
        state_str = state.value if hasattr(state, "value") else str(state)
    except Exception as exc:
        logger.warning("bili login check_state error: %s", exc)
        return {"state": "error", "message": str(exc)}

    if state == login_v2.QrCodeLoginEvents.TIMEOUT:
        sess["state"] = "timeout"
        _BILI_LOGIN_SESSIONS.pop(session_id, None)
        return {"state": "timeout"}

    if state == login_v2.QrCodeLoginEvents.SCAN:
        sess["state"] = "scanned"
        return {"state": "scanned"}

    if state == login_v2.QrCodeLoginEvents.CONF:
        sess["state"] = "done"
        return {"state": "done"}

    return {"state": "waiting"}


@app.post("/api/bili_login/save")
async def api_bili_login_save(request: Request):
    """保存 B站 二维码登录凭据并重启服务."""
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"ok": False, "error": "bad request"}, status_code=400)
    session_id = body.get("session_id", "")
    sess = _BILI_LOGIN_SESSIONS.get(session_id)
    if not sess:
        return {"ok": False, "error": "session expired"}

    qr = sess["qr"]
    if not qr.has_done():
        return {"ok": False, "error": "login not completed"}

    try:
        credential = qr.get_credential()
    except Exception as exc:
        return {"ok": False, "error": f"get credential failed: {exc}"}

    # 保存凭据
    cookies = credential.get_cookies()
    store_path = Path(_CONFIG_YAML_PATH).parent / "data" / "credential.json"
    store_path.parent.mkdir(parents=True, exist_ok=True)
    store_path.write_text(
        json.dumps({
            "SESSDATA": cookies.get("SESSDATA", ""),
            "bili_jct": cookies.get("bili_jct", ""),
            "buvid3": cookies.get("buvid3", ""),
            "DedeUserID": cookies.get("DedeUserID", ""),
            "ac_time_value": cookies.get("ac_time_value", ""),
        }, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )

    _BILI_LOGIN_SESSIONS.pop(session_id, None)

    return {"ok": True, "message": "凭据已保存"}


# ══════════════════════════════════════════════════════════════
#  预设模板 API
# ══════════════════════════════════════════════════════════════

_TEMPLATES_PATH: str = "data/templates.json"


def _load_templates() -> dict:
    p = Path(_ROOMS_BASE_DIR).resolve() / _TEMPLATES_PATH
    if p.exists():
        try:
            return json.loads(p.read_text(encoding="utf-8"))
        except Exception:
            pass
    return {"llm_templates": [], "bot_templates": []}


def _save_templates(data: dict) -> None:
    p = Path(_ROOMS_BASE_DIR).resolve() / _TEMPLATES_PATH
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")


@app.get("/api/templates")
async def api_get_templates():
    """获取所有预设模板."""
    return _load_templates()


@app.post("/api/templates")
async def api_save_template(request: Request):
    """保存一个预设模板."""
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"error": "bad request"}, status_code=400)

    ttype = body.get("type", "")  # "llm" or "bot"
    name = body.get("name", "").strip()
    config = body.get("config", {})
    if not name or not config:
        return JSONResponse({"error": "name and config required"}, status_code=400)

    data = _load_templates()
    key = f"{ttype}_templates"
    if key not in data:
        data[key] = []

    # 同名覆盖
    existing = [t for t in data[key] if t.get("name") == name]
    if existing:
        existing[0]["config"] = config
    else:
        data[key].append({"name": name, "config": config})

    _save_templates(data)
    return {"ok": True}


@app.delete("/api/templates")
async def api_delete_template(request: Request):
    """删除一个预设模板."""
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"error": "bad request"}, status_code=400)

    ttype = body.get("type", "")
    name = body.get("name", "").strip()
    data = _load_templates()
    key = f"{ttype}_templates"
    if key in data:
        data[key] = [t for t in data[key] if t.get("name") != name]
    _save_templates(data)
    return {"ok": True}


@app.post("/api/restart_all_bots")
async def api_restart_all_bots():
    """重启所有正在运行的 Bot 进程."""
    rooms = _list_rooms_from_disk()
    count = 0
    for r in rooms:
        if r["status"] == "running":
            await restart_room_async(r["room_id"])
            count += 1
    _save_room_states()
    logger.info("restarted %d bots", count)
    return {"ok": True, "count": count}


# ══════════════════════════════════════════════════════════════
#  通用机器人配置 API
# ══════════════════════════════════════════════════════════════


@app.get("/api/general_config")
async def api_get_general_config():
    """返回机器人全局配置."""
    from app.config import load_config, config_to_dict
    try:
        cfg = load_config(_CONFIG_YAML_PATH)
        return config_to_dict(cfg)
    except Exception as exc:
        logger.warning("general config load failed: %s", exc)
        return {"error": str(exc)}


@app.post("/api/general_config")
async def api_save_general_config(request: Request):
    """保存机器人全局配置到 config.yaml."""
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"error": "bad request"}, status_code=400)

    from app.config import update_config_from_dict
    ok = update_config_from_dict(body, _CONFIG_YAML_PATH)
    return {"ok": ok}


# ══════════════════════════════════════════════════════════════
#  用户管理 API
# ══════════════════════════════════════════════════════════════


@app.get("/api/users")
async def api_list_users(request: Request):
    """列出所有用户（不包含密码哈希）. 管理员可看全部，普通用户只能看自己."""
    _, role, _ = _get_current_role(request)
    users_raw = _load_users()
    if role == "user":
        # 普通用户只能看到自己的信息
        token = request.cookies.get("session", "")
        username, _, _ = _user_role(token)
        filtered = {}
        if username in users_raw:
            filtered[username] = users_raw[username]
        return {"users": filtered}
    # Strip password hashes from response
    safe = {}
    for uname, info in users_raw.items():
        safe[uname] = {
            "role": info.get("role", "user"),
            "allowed_rooms": info.get("allowed_rooms", []),
        }
    return {"users": safe}


@app.post("/api/users/update")
async def api_update_user(request: Request):
    """添加/修改用户（管理员或主播）."""
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"error": "bad request"}, status_code=400)
    username = body.get("username", "").strip()
    if not username:
        return JSONResponse({"error": "username required"}, status_code=400)

    users = _load_users()
    password = body.get("password", "")
    role = body.get("role", "user")
    rooms = body.get("rooms", body.get("allowed_rooms", []))

    if password:
        users[username] = {
            "password_hash": _hash_password(password),
            "role": role,
            "allowed_rooms": rooms,
        }
    elif username in users:
        # 不修改密码，只更新角色和房间
        users[username]["role"] = role
        users[username]["allowed_rooms"] = rooms
    else:
        return JSONResponse({"error": "user not found and no password provided"}, status_code=400)

    _save_users(users)
    return {"ok": True}


@app.delete("/api/users/{username}")
async def api_delete_user(username: str):
    """删除用户."""
    users = _load_users()
    users.pop(username, None)
    _save_users(users)
    return {"ok": True}


@app.post("/api/users/admin_password")
async def api_set_admin_password(request: Request):
    """设置管理员密码（同步到 auth 配置和当前环境变量）."""
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"error": "bad request"}, status_code=400)
    new_pass = body.get("password", "").strip()
    if len(new_pass) < 4:
        return JSONResponse({"error": "password too short"}, status_code=400)

    global AUTH_PASS
    users = _load_users()
    users["admin"] = {"password_hash": _hash_password(new_pass), "role": "admin", "allowed_rooms": []}
    _save_users(users)
    AUTH_PASS = new_pass  # 立即生效
    return {"ok": True}


# ── New Admin User Management API ──


@app.get("/api/admin/users")
async def api_admin_list_users():
    """管理员列出所有用户（完整信息，不含密码哈希）."""
    users_raw = _load_users()
    safe = {}
    for uname, info in users_raw.items():
        safe[uname] = {
            "role": info.get("role", "user"),
            "allowed_rooms": info.get("allowed_rooms", []),
        }
    return {"users": safe}


@app.post("/api/admin/users")
async def api_admin_create_user(request: Request):
    """管理员创建用户."""
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"error": "bad request"}, status_code=400)
    username = body.get("username", "").strip()
    password = body.get("password", "").strip()
    if not username or not password:
        return JSONResponse({"error": "username and password required"}, status_code=400)
    if len(password) < 4:
        return JSONResponse({"error": "password too short"}, status_code=400)

    users = _load_users()
    if username in users:
        return JSONResponse({"error": "user already exists"}, status_code=409)

    role = body.get("role", "user")
    allowed_rooms = body.get("allowed_rooms", [])
    users[username] = {
        "password_hash": _hash_password(password),
        "role": role if role in ("admin", "user") else "user",
        "allowed_rooms": allowed_rooms,
    }
    _save_users(users)
    return {"ok": True}


@app.put("/api/admin/users/{username}")
async def api_admin_update_user(username: str, request: Request):
    """管理员修改用户（角色、密码、授权房间）."""
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"error": "bad request"}, status_code=400)

    users = _load_users()
    if username not in users:
        return JSONResponse({"error": "user not found"}, status_code=404)

    password = body.get("password", "").strip()
    if password:
        if len(password) < 4:
            return JSONResponse({"error": "password too short"}, status_code=400)
        users[username]["password_hash"] = _hash_password(password)

    if "role" in body:
        role = body["role"]
        if role in ("admin", "user"):
            users[username]["role"] = role
    if "allowed_rooms" in body:
        users[username]["allowed_rooms"] = body["allowed_rooms"]

    _save_users(users)
    return {"ok": True}


@app.delete("/api/admin/users/{username}")
async def api_admin_delete_user(username: str):
    """管理员删除用户（不能删除自己）. """
    if username == "admin":
        return JSONResponse({"error": "cannot delete admin"}, status_code=400)
    users = _load_users()
    if username not in users:
        return JSONResponse({"error": "user not found"}, status_code=404)
    users.pop(username, None)
    _save_users(users)
    return {"ok": True}


# ── User Self-Service API ──


@app.post("/api/user/password")
async def api_user_change_password(request: Request):
    """用户修改自己的密码并可修改用户名。需要旧密码验证."""
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"error": "bad request"}, status_code=400)

    token = request.cookies.get("session", "")
    username, role, _ = _user_role(token)
    if not username:
        return JSONResponse({"error": "unauthorized"}, status_code=401)

    old_password = body.get("old_password", "")
    new_password = body.get("new_password", "").strip()
    new_username = body.get("new_username", "").strip()

    if not old_password or not new_password:
        return JSONResponse({"error": "old_password and new_password required"}, status_code=400)
    if len(new_password) < 4:
        return JSONResponse({"error": "password too short"}, status_code=400)

    users = _load_users()
    user_info = users.get(username)
    if not user_info:
        return JSONResponse({"error": "user not found"}, status_code=404)

    stored_hash = user_info.get("password_hash", "")
    if stored_hash and stored_hash != _hash_password(old_password):
        return JSONResponse({"error": "wrong password"}, status_code=403)

    # 允许修改用户名
    if new_username and new_username != username:
        if new_username in users:
            return JSONResponse({"error": "用户名已存在"}, status_code=400)
        # 迁移用户信息到新用户名
        users[new_username] = users.pop(username)
        users[new_username]["password_hash"] = _hash_password(new_password)
        users[new_username]["must_reset_password"] = False
        _save_users(users)
        # 更新当前session
        _SESSIONS[token] = (time.time() + _SESSION_TIMEOUT, new_username, role, body.get("allowed_rooms", []))
        return {"ok": True, "must_reset_password": False, "new_username": new_username}
    else:
        users[username]["password_hash"] = _hash_password(new_password)
        users[username]["must_reset_password"] = False
        _save_users(users)
        return {"ok": True, "must_reset_password": False}


# ══════════════════════════════════════════════════════════════
#  更新检查（自动选择国内可用的 GitHub 加速镜像）
# ══════════════════════════════════════════════════════════════

_UPDATE_REPO = "yujianke100/ayabot"
_UPDATE_ASSET = "Ayabot-latest.exe"
_GH_RELEASE_API = f"https://api.github.com/repos/{_UPDATE_REPO}/releases/latest"

# ── 线路候选 ──────────────────────────────────────────────
# 元数据（版本号）：国内优先、GitHub 直连垫底。
# 实测（2026-10）：gh-proxy.com 250ms 可用；hk.gh-proxy.com 1.2s 可用；
# gh-proxy.net / ghfast.top / ghproxy.net / gh.llkk.cc / ghfile.geekertao.top
# 对 api.github.com 返回 403 或 HTML 错误页，不能用于取版本号。
_META_SOURCES: tuple[tuple[str, str], ...] = (
    ("gh-proxy.com", "https://gh-proxy.com/"),
    ("hk.gh-proxy.com", "https://hk.gh-proxy.com/"),
    ("GitHub", ""),
)
# 安装包下载候选：国内线路在前，GitHub 直连垫底（仅作兜底展示）
# Gitee 走它自己的国内 CDN（foruda.gitee.com），实测约 2 MB/s，是最稳的一条。
_GITEE_REPO = "yujianke100/Ayabot"   # Gitee 上的仓库路径（owner/repo），需与密钥一致
_DOWNLOAD_SOURCES: tuple[tuple[str, str], ...] = (
    ("gh-proxy.com", "https://gh-proxy.com/"),
    ("hk.gh-proxy.com", "https://hk.gh-proxy.com/"),
    ("ghfast.top", "https://ghfast.top/"),
    ("ghproxy.net", "https://ghproxy.net/"),
    ("gh.llkk.cc", "https://gh.llkk.cc/"),
    ("ghfile.geekertao.top", "https://ghfile.geekertao.top/"),
    ("GitHub", ""),
)
# 取「最新版本号」的候选：用 releases/latest 的重定向，比 API 便宜也不吃限流。
# ghproxy.net 对 API 返回 403，但重定向路径可用，所以单独列一份。
_TAG_SOURCES: tuple[tuple[str, str], ...] = (
    ("gh-proxy.com", "https://gh-proxy.com/"),
    ("hk.gh-proxy.com", "https://hk.gh-proxy.com/"),
    ("ghproxy.net", "https://ghproxy.net/"),
    ("GitHub", ""),
)
# Gitee 的发行版 API（公开：无需 token，也不吃 GitHub 那 60 次/小时的限流）
# 注意：不能用 /releases/latest —— 那条会返回我们自己建的 `latest` 别名发行版
# （tag_name 字面就是 "latest"），拿不到真实版本号。改用列表接口再挑版本号最大的那个。
_GITEE_RELEASES_API = f"https://gitee.com/api/v5/repos/{_GITEE_REPO}/releases?per_page=20"
# 真实版本标签的形态（排除 latest 别名发行版）
_VERSION_TAG_RE = re.compile(r"^v?\d+(?:\.\d+)*$")

# ── 时间预算 ──────────────────────────────────────────────
# 国内直连 api.github.com / objects.githubusercontent.com 经常挂死到超时，
# 旧实现按顺序试（GitHub 先）会白等 8s，再等最慢的探测 10s，用户体感 10~18s。
# 现在：元数据并发抢答、探测到第一条可用线路后短暂宽限就收工。
_META_ATTEMPT_TIMEOUT = 5.0   # 单个元数据源超时
_META_BUDGET = 6.0            # 完整元数据抢答总预算
_META_STAGGER = 1.2           # GitHub 直连延迟起跑，给国内镜像让路
_TAG_BUDGET = 3.0             # 只取版本号的总预算（关键路径，短）
_META_EXTRA = 1.2             # 拿到版本号后，最多再花这么久等更新说明
_PROBE_TIMEOUT = 4.0          # 单条线路探测超时
_PROBE_BUDGET = 4.0           # 全部探测总预算
_PROBE_GRACE = 0.5            # 已有可用线路后，再收集候选的宽限时间
_UPDATE_CACHE_TTL = 600.0     # 结果缓存 10 分钟（静默检查直接复用）

# 排序优先级：国内镜像优先于 GitHub 直连。
# 即使某次直连比镜像快几十毫秒也不要推荐直连 —— 国内直连时通时不通，
# 用户点下去很可能转圈或断掉；镜像慢一点但稳。
_LANE_PRIORITY = {"GitHub": 1}

# 最近一次检查结果（进程内缓存）。静默检查每次启动/刷新都调一次接口，
# 没有缓存就会反复测速，既慢又浪费。
_UPDATE_CACHE: dict[str, Any] = {"ts": 0.0, "payload": None}


async def _race_json(session: aiohttp.ClientSession, api_path: str) -> Optional[dict]:
    """并发向各元数据源取同一个 GitHub API JSON，先到先得。

    浏览器直连 api.github.com 在国内经常失败或超时，所以这类请求一律由服务端
    经国内镜像代取。
    """
    async def attempt(name: str, prefix: str, delay: float) -> Optional[dict]:
        if delay > 0:
            await asyncio.sleep(delay)
        try:
            async with session.get(
                prefix + api_path,
                timeout=aiohttp.ClientTimeout(total=_META_ATTEMPT_TIMEOUT),
            ) as resp:
                if resp.status != 200:
                    return None
                raw = await resp.read()
            data = json.loads(raw)
            return data if isinstance(data, dict) else None
        except Exception:  # noqa: BLE001
            return None

    tasks = [
        asyncio.create_task(attempt(n, p, _META_STAGGER if not p else 0.0))
        for n, p in _META_SOURCES
    ]
    try:
        for fut in asyncio.as_completed(tasks, timeout=_META_BUDGET):
            try:
                data = await fut
            except Exception:  # noqa: BLE001
                continue
            if data is not None:
                return data
        return None
    except asyncio.TimeoutError:
        return None
    finally:
        for t in tasks:
            t.cancel()


def _release_urls(latest: str) -> dict[str, str]:
    tag = f"v{latest}" if not latest.startswith("v") else latest
    return {
        "page": f"https://github.com/{_UPDATE_REPO}/releases/tag/{tag}",
        "asset": f"https://github.com/{_UPDATE_REPO}/releases/download/{tag}/{_UPDATE_ASSET}",
        # Gitee 上一版一发行版，附件名固定；这里拼的是「版本无关」的 latest 别名地址
        "gitee": f"https://gitee.com/{_GITEE_REPO}/releases/download/latest/{_UPDATE_ASSET}",
        "gitee_tag": f"https://gitee.com/{_GITEE_REPO}/releases/download/{tag}/{_UPDATE_ASSET}",
    }


def _download_lanes(asset_url: str, version: str | None = None) -> list[tuple[str, str]]:
    """按「国内优先、GitHub 直连最后」排好的 (线路名, 完整地址) 列表。

    Gitee 用 latest 别名（固定地址，不怕版本号变化）；下面还会追加一条按 tag 拼的，
    以防 latest 别名没建成功但版本发行版在。
    """
    tag = f"v{version}" if version and not str(version).startswith("v") else str(version or "")
    lanes: list[tuple[str, str]] = [
        ("gitee", f"https://gitee.com/{_GITEE_REPO}/releases/download/latest/{_UPDATE_ASSET}"),
    ]
    if tag:
        lanes.append(
            ("gitee (tag)", f"https://gitee.com/{_GITEE_REPO}/releases/download/{tag}/{_UPDATE_ASSET}")
        )
    lanes += [(name, prefix + asset_url) for name, prefix in _DOWNLOAD_SOURCES]
    return lanes


async def _fetch_release_meta(
    session: aiohttp.ClientSession, name: str, prefix: str
) -> tuple[Optional[dict], str]:
    """从直连/镜像取 latest release 元数据。返回 (数据, 线路名)。"""
    url = prefix + _GH_RELEASE_API
    try:
        async with session.get(
            url, timeout=aiohttp.ClientTimeout(total=_META_ATTEMPT_TIMEOUT)
        ) as resp:
            if resp.status != 200:
                logger.debug("update meta %s -> HTTP %s", name, resp.status)
                return None, name
            raw = await resp.read()
        try:
            data = json.loads(raw)
        except Exception:  # noqa: BLE001
            # 有的加速站出错时返回 200 + HTML 页面，不能当成功
            logger.debug("update meta %s -> 非 JSON 响应", name)
            return None, name
        if not isinstance(data, dict) or not data.get("tag_name"):
            return None, name
        return data, name
    except Exception as exc:  # noqa: BLE001
        logger.debug("update meta %s failed: %s", name, exc)
        return None, name


async def _fetch_latest_tag(
    session: aiohttp.ClientSession, name: str, prefix: str
) -> tuple[Optional[str], str]:
    """只用一次重定向拿到最新版本号，不碰 api.github.com。

    `github.com/<repo>/releases/latest` 会 302 到 `/releases/tag/vX`。
    这条路径的好处：① 不吃 API 的 60 次/小时限流；② api.github.com 被墙/限流时
    github.com 往往还能通；③ 只要一个请求，比拉整份 release JSON 快得多。
    """
    url = prefix + f"https://github.com/{_UPDATE_REPO}/releases/latest"
    try:
        async with session.get(
            url, allow_redirects=False,
            timeout=aiohttp.ClientTimeout(total=_META_ATTEMPT_TIMEOUT),
        ) as resp:
            loc = resp.headers.get("Location") or ""
            body = b""
            if not loc and resp.status == 200:
                body = await resp.read()
    except Exception as exc:  # noqa: BLE001
        logger.debug("latest tag %s failed: %s", name, exc)
        return None, name
    text = loc or body.decode("utf-8", "replace")
    match = re.search(r"/tag/(v?[\d][\w.\-]*)", text)
    if not match:
        return None, name
    return match.group(1), name


async def _fetch_gitee_tag(session: aiohttp.ClientSession) -> tuple[Optional[str], str]:
    """从 Gitee 的发行版 API 取最新版本号（公开、免 token、不吃 GitHub 限流）。

    走列表接口而不是 /releases/latest：后者会返回我们自己维护的 `latest` 别名
    （tag_name 字面是 "latest"），不是真实版本号。列表里同时有别名和真实版本，
    所以按「版本号最大」挑，不看创建时间（重发旧版本时创建时间会更新）。
    """
    try:
        async with session.get(
            _GITEE_RELEASES_API, timeout=aiohttp.ClientTimeout(total=_META_ATTEMPT_TIMEOUT)
        ) as resp:
            if resp.status != 200:
                return None, "gitee"
            raw = await resp.read()
        data = json.loads(raw)
        if not isinstance(data, list):
            return None, "gitee"
        best: Optional[str] = None
        best_key: tuple[int, ...] = ()
        for rel in data:
            tag = str((rel or {}).get("tag_name") or "").strip()
            if not _is_version_tag(tag):
                continue
            key = _version_tuple(tag)
            if key > best_key:
                best, best_key = tag, key
        return best, "gitee"
    except Exception as exc:  # noqa: BLE001
        logger.debug("gitee tag failed: %s", exc)
        return None, "gitee"


async def _fetch_tag_race(
    session: aiohttp.ClientSession,
) -> tuple[Optional[str], str, int]:
    """并发问「最新版本号」，只走 releases/latest 重定向（便宜、不吃 API 限流）。

    版本号是最关键的一步：拿到它才能拼出下载地址、开始测速。
    所以这一步用最轻的请求、只等第一条结果，不依赖 api.github.com。
    GitHub 直连延迟 _META_STAGGER 起跑，国内镜像先说话。
    """
    started = time.time()

    async def attempt(name: str, prefix: str, delay: float):
        if delay > 0:
            await asyncio.sleep(delay)
        return await _fetch_latest_tag(session, name, prefix)

    tasks = [
        asyncio.create_task(attempt(n, p, _META_STAGGER if not p else 0.0))
        for n, p in _TAG_SOURCES
    ]
    tasks.append(asyncio.create_task(_fetch_gitee_tag(session)))
    try:
        for fut in asyncio.as_completed(tasks, timeout=_TAG_BUDGET):
            try:
                tag, name = await fut
            except Exception:  # noqa: BLE001
                continue
            if tag:
                return tag, name, int((time.time() - started) * 1000)
        return None, "", int((time.time() - started) * 1000)
    except asyncio.TimeoutError:
        return None, "", int((time.time() - started) * 1000)
    finally:
        for t in tasks:
            t.cancel()


async def _probe_url(
    session: aiohttp.ClientSession,
    name: str,
    url: str,
    expected_size: int = 0,
) -> dict[str, Any]:
    """探测下载地址是否可用（Range 只取 1 字节，省流量）。

    传了 expected_size 时会核对镜像返回的文件总长：加速站普遍做缓存，
    Release 资产被重新上传后镜像仍可能吐旧文件（实测 gh.llkk.cc 就这样），
    这种线路标 stale，不能推荐给用户。
    """
    started = time.time()
    try:
        async with session.get(
            url, timeout=aiohttp.ClientTimeout(total=_PROBE_TIMEOUT),
            headers={"Range": "bytes=0-0"},
        ) as resp:
            ok = resp.status < 400
            size = resp.headers.get("Content-Range") or resp.headers.get("Content-Length") or ""
        total = 0
        if "/" in size:
            tail = size.rsplit("/", 1)[-1].strip()
            total = int(tail) if tail.isdigit() else 0
        elif size.strip().isdigit():
            total = int(size.strip())
        stale = bool(expected_size and total and total != expected_size)
        return {
            "name": name,
            "url": url,
            "ok": ok,
            "status": resp.status,
            "ms": int((time.time() - started) * 1000),
            "size": size,
            "total_bytes": total,
            "stale": stale,
        }
    except Exception as exc:  # noqa: BLE001
        return {
            "name": name,
            "url": url,
            "ok": False,
            "stale": False,
            "error": str(exc)[:80],
            "ms": int((time.time() - started) * 1000),
        }


async def _probe_one(
    session: aiohttp.ClientSession,
    name: str,
    url: str,
    expected_size: int,
    delay: float,
) -> dict[str, Any]:
    """延迟起跑的探测（GitHub 直连作为兜底，不给国内镜像抢跑）。"""
    if delay > 0:
        await asyncio.sleep(delay)
    return await _probe_url(session, name, url, expected_size)


async def _probe_all(
    session: aiohttp.ClientSession, lanes: list[tuple[str, str]], expected_size: int = 0
) -> list[dict[str, Any]]:
    """并发探测全部下载线路，拿到第一条可用线路后再等一小段就收工。

    不这样做的话，某条线路挂死（国内直连 GitHub 常见）会把整个请求拖到超时，
    哪怕国内镜像 0.6s 就已经答复了。
    """
    tasks = {
        asyncio.create_task(
            _probe_one(session, name, url, expected_size,
                       _PROBE_GRACE if name == "GitHub" else 0.0)
        ): (name, url)
        for name, url in lanes
    }
    results: list[dict[str, Any]] = []
    pending = set(tasks)
    grace_until: Optional[float] = None
    hard_deadline = time.time() + _PROBE_BUDGET

    def _has_good() -> bool:
        return any(r["ok"] and not r.get("stale") for r in results)

    while pending:
        now = time.time()
        wait = hard_deadline - now
        if grace_until is not None:
            wait = min(wait, grace_until - now)
        if wait <= 0:
            break
        done, pending = await asyncio.wait(pending, timeout=wait, return_when=asyncio.FIRST_COMPLETED)
        for t in done:
            try:
                results.append(t.result())
            except Exception as exc:  # noqa: BLE001
                name, url = tasks[t]
                results.append({"name": name, "url": url, "ok": False,
                                "stale": False, "error": str(exc)[:80], "ms": 0})
        if _has_good() and grace_until is None:
            grace_until = time.time() + _PROBE_GRACE

    had_good = _has_good()
    for t in pending:
        t.cancel()
        name, url = tasks[t]
        results.append({
            "name": name, "url": url, "ok": False, "stale": False,
            # 已有可用线路就收工 → 这条只是「没来得及测」，不是「不通」
            "skipped": had_good,
            "error": "未测速（已有更快的可用线路）" if had_good else "超时",
            "ms": int((time.time() - (hard_deadline - _PROBE_BUDGET)) * 1000),
        })
    return results


def _version_tuple(text: str) -> tuple[int, ...]:
    parts: list[int] = []
    for chunk in str(text).lstrip("vV").split("."):
        digits = "".join(ch for ch in chunk if ch.isdigit())
        parts.append(int(digits) if digits else 0)
    return tuple(parts)


def _is_version_tag(tag: str) -> bool:
    """`v1.2.3` / `1.2.3` 这类真实版本标签。

    Gitee 上还有我们自己维护的 `latest` 别名发行版，它不是版本号，必须排除，
    否则会拿 "latest" 当版本号去拼下载地址。
    """
    return bool(_VERSION_TAG_RE.match(str(tag or "").strip()))


@app.get("/api/update/check")
async def api_update_check(force: int = 0):
    """检查更新，并探测国内加速镜像可用性。

    很多国内用户直连 api.github.com / objects.githubusercontent.com 会超时，
    因此由服务端（就在用户机器上跑）并发向国内镜像要版本号、并发探测下载线路，
    把能用的地址按速度排好返回，前端不需要用户自己猜哪个镜像能用。

    结果缓存 10 分钟：静默检查（每次打开/刷新页面都会跑）直接吃缓存，
    只有用户手动点「检查更新」才带 force=1 强制重新测速。
    服务启动后还会在后台预热一次，所以第一次打开页面通常也是秒回。
    """
    started_at = time.time()
    if not force:
        cached = _UPDATE_CACHE.get("payload")
        cache_age = time.time() - float(_UPDATE_CACHE.get("ts") or 0.0)
        if cached and cache_age < _UPDATE_CACHE_TTL:
            payload = dict(cached)
            payload["cached"] = True
            payload["cache_age"] = int(cache_age)
            payload["elapsed_ms"] = int((time.time() - started_at) * 1000)
            return payload

    payload = await _compute_update_payload()
    payload["cached"] = False
    payload["elapsed_ms"] = int((time.time() - started_at) * 1000)
    if payload.get("ok"):
        _UPDATE_CACHE["ts"] = time.time()
        _UPDATE_CACHE["payload"] = payload
    return payload


async def _warm_update_cache() -> None:
    """启动时后台预热更新检查结果（失败无所谓，用户点击时会再算一次）。"""
    try:
        await asyncio.sleep(5)
        if _UPDATE_CACHE.get("payload"):
            return
        payload = await _compute_update_payload()
        if payload.get("ok"):
            _UPDATE_CACHE["ts"] = time.time()
            _UPDATE_CACHE["payload"] = payload
            logger.info(
                "update cache warmed: latest=%s via %s in %sms",
                payload.get("latest"), payload.get("meta_source"), payload.get("meta_ms"),
            )
    except Exception as exc:  # noqa: BLE001
        logger.debug("warm update cache failed: %s", exc)


async def _compute_update_payload() -> dict:
    started_at = time.time()
    current = get_version_display()

    meta: Optional[dict] = None
    meta_source = ""
    meta_ms = 0
    async with aiohttp.ClientSession(
        headers={"User-Agent": "Ayabot-UpdateChecker", "Accept": "application/vnd.github+json"},
        trust_env=True,
    ) as session:
        # 关键路径只有两步：① 问版本号 ② 测下载线路。
        # 更新说明（changelog）是附赠信息，不能拖慢这两步，所以它单独跑、
        # 只给很短的时间窗，拿不到就空着，用户点「查看更新日志」时再经镜像取。
        latest = ""
        tag, tag_source, tag_ms = await _fetch_tag_race(session)
        meta_task = asyncio.create_task(_race_json(session, _GH_RELEASE_API))
        if tag:
            latest = tag.lstrip("vV")
            meta_source, meta_ms = tag_source, tag_ms
            urls = _release_urls(latest)
            probe_task = asyncio.create_task(
                _probe_all(session, _download_lanes(urls["asset"], latest))
            )
            try:
                meta = await asyncio.wait_for(meta_task, timeout=_META_EXTRA)
            except Exception:  # noqa: BLE001  超时或失败都不影响主流程
                meta = None
                meta_task.cancel()
            probes = await probe_task
        else:
            # 版本号拿不到时退回完整元数据（还能从 assets 里读到版本）
            meta = await meta_task
            if meta is None:
                cur_ver = get_version().lstrip("v")
                urls = _release_urls(cur_ver)
                probes = await _probe_all(session, _download_lanes(urls["asset"], cur_ver))
                return {
                    "ok": False,
                    "error": "无法获取版本信息（直连与镜像均失败）",
                    "current": current,
                    "meta_ms": tag_ms,
                    "elapsed_ms": int((time.time() - started_at) * 1000),
                    "downloads": sorted(probes, key=lambda p: (not p["ok"], p.get("ms", 9999))),
                }
            latest = str(meta.get("tag_name") or "").lstrip("vV")
            meta_source, meta_ms = tag_source or "GitHub", tag_ms
            urls = _release_urls(latest)
            probes = await _probe_all(session, _download_lanes(urls["asset"], latest))

        # 从 release 元数据里取资产真实大小，用来识别镜像缓存的旧文件
        expected_size = 0
        digest = ""
        for asset in (meta.get("assets") or []) if meta else []:
            if isinstance(asset, dict) and asset.get("name") == _UPDATE_ASSET:
                expected_size = int(asset.get("size") or 0)
                digest = str(asset.get("digest") or "")
                break

    if expected_size:
        # 元数据里的真实大小是最权威的判据（probes 可能是在 meta 到达前跑的，重算一遍）
        for p in probes:
            p["stale"] = bool(
                p.get("ok") and p.get("total_bytes")
                and p["total_bytes"] != expected_size
            )
    else:
        # 只拿到版本号（没拿到完整元数据）时，用各线路一致的文件大小当参照，
        # 这样仍然能发现「某条镜像还吐着旧文件」。
        sizes = [p["total_bytes"] for p in probes if p.get("ok") and p.get("total_bytes")]
        if sizes:
            expected_size = max(set(sizes), key=sizes.count)
            for p in probes:
                p["stale"] = bool(
                    p.get("ok") and p.get("total_bytes")
                    and p["total_bytes"] != expected_size
                )

    # 优先级：可用 → 非旧缓存 → 国内镜像优先于 GitHub 直连 → 延迟
    downloads = sorted(
        probes,
        key=lambda p: (
            not p["ok"],
            bool(p.get("stale")),
            _LANE_PRIORITY.get(p["name"], 0),
            p.get("ms", 9999),
        ),
    )
    recommended = next((d for d in downloads if d["ok"] and not d.get("stale")), None)
    if recommended is None:
        # 全部线路都拿不到新文件时，至少给出可用的（并保留 stale 标记提醒用户）
        recommended = next((d for d in downloads if d["ok"]), None)
    if recommended is None and meta_source:
        # 探测全部超时，但版本号是从某条镜像拿到的 —— 该镜像的下载地址通常也能用
        if meta_source == "gitee":
            rec_url = urls.get("gitee") or urls["asset"]
        else:
            rec_url = dict(_META_SOURCES).get(meta_source, "") + urls["asset"]
        recommended = {
            "name": meta_source,
            "url": rec_url,
            "ok": True,
            "untested": True,
            "stale": False,
            "ms": 0,
        }
        downloads.insert(0, recommended)

    safe_meta = meta or {}
    payload = {
        "ok": True,
        "current": current,
        "latest": "v" + latest,
        "has_update": _version_tuple(latest) > _version_tuple(current),
        "meta_source": meta_source,
        "page_url": urls["page"],
        "changelog": str(safe_meta.get("body") or ""),
        "published_at": safe_meta.get("published_at") or "",
        "expected_bytes": expected_size,
        "asset_digest": digest,
        "downloads": downloads,
        "recommended": recommended,
        "meta_ms": meta_ms,
        "elapsed_ms": int((time.time() - started_at) * 1000),
        "cached": False,
    }
    return payload


@app.get("/api/update/changelog")
async def api_update_changelog(version: str = ""):
    """取某个版本的更新说明，由服务端经国内镜像代取。

    浏览器直连 api.github.com 在国内经常失败，前端原来直接 fetch 它会转圈或报错。
    """
    ver = version.strip().lstrip("vV")
    headers = {"User-Agent": "Ayabot-UpdateChecker", "Accept": "application/vnd.github+json"}
    async with aiohttp.ClientSession(headers=headers, trust_env=True) as session:
        data: Optional[dict] = None
        if ver:
            data = await _race_json(
                session, f"https://api.github.com/repos/{_UPDATE_REPO}/releases/tags/v{ver}"
            )
        if data is None:
            data = await _race_json(session, _GH_RELEASE_API)
    if not data:
        return {"ok": False, "version": ver, "body": "", "error": "无法获取更新说明"}
    return {
        "ok": True,
        "version": ver or str(data.get("tag_name") or "").lstrip("vV"),
        "name": data.get("name") or "",
        "body": str(data.get("body") or ""),
        "published_at": data.get("published_at") or "",
    }


# ══════════════════════════════════════════════════════════════
#  多房间管理 API
# ══════════════════════════════════════════════════════════════

_ROOMS_BASE_DIR: str = "."  # 由 init_app 设置


async def _resolve_room_id(anchor_uid: int) -> int:
    """通过 B站 API 从主播 UID 查询直播间号."""
    url = f"https://api.live.bilibili.com/room/v1/Room/getRoomInfoOld?mid={anchor_uid}"
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
        "Referer": "https://live.bilibili.com/",
    }
    try:
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=10)) as sess:
            async with sess.get(url, headers=headers) as resp:
                if resp.content_type != "application/json":
                    raise ValueError(f"B站 API 返回非 JSON (content_type={resp.content_type}), 可能被风控")
                data = await resp.json()
        if data.get("code") == 0:
            room_id = data.get("data", {}).get("room_id") or data.get("data", {}).get("roomid")
            if room_id:
                return int(room_id)
        raise ValueError(f"B站 API 返回异常: {data}")
    except Exception as exc:
        raise ValueError(f"无法解析直播间号 (UID={anchor_uid}): {exc}") from exc


def _list_rooms_from_disk() -> list[dict[str, Any]]:
    """扫描 rooms/ 目录列出所有房间."""
    from app.config import DEFAULT_ROOMS_DIR
    base = Path(_ROOMS_BASE_DIR).resolve() / DEFAULT_ROOMS_DIR
    if not base.exists():
        return []
    rooms: list[dict[str, Any]] = []
    for d in sorted(base.iterdir()):
        if not d.is_dir():
            continue
        room_id = d.name
        cfg_path = d / "config.yaml"
        if not cfg_path.exists():
            continue
        # 读取关键信息
        try:
            import yaml
            cfg = yaml.safe_load(cfg_path.read_text(encoding="utf-8")) or {}
        except Exception:
            cfg = {}
        rooms.append({
            "room_id": room_id,
            "anchor_uid": cfg.get("anchor_uid", 0),
            "room_display_id": cfg.get("room_display_id", 0),
            "bot_name": cfg.get("web_ui", {}).get("bot_name", ""),
            "status": room_status(room_id),
            "port": cfg.get("web_ui", {}).get("port", 8000),
            "account_uid": cfg.get("account_uid", ""),
            "account_nick": "",
            "room_name": cfg.get("room_name", ""),
        })
    return rooms


@app.get("/api/bilibili/user_info")
async def api_bilibili_user_info(mid: int):
    """代理 B站 API（获取用户昵称），避免前端跨域问题."""
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
        "Referer": "https://www.bilibili.com/",
    }
    try:
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=8), headers=headers) as s:
            async with s.get(f"https://api.bilibili.com/x/web-interface/card?mid={mid}") as r:
                if r.status == 200:
                    j = await r.json()
                    if j.get("code") == 0:
                        name = j.get("data", {}).get("card", {}).get("name", "")
                        return {"code": 0, "name": name}
                    return {"code": j.get("code"), "name": ""}
                return {"code": -1, "name": "", "error": "http error"}
    except Exception as exc:
        return {"code": -1, "name": "", "error": str(exc)}


@app.get("/api/rooms")
async def api_list_rooms(request: Request):
    """列出所有房间及状态."""
    # 从 process_manager 查询状态
    rooms = _list_rooms_from_disk()
    # 补齐 account_nick
    accounts_map = {a["uid"]: a.get("nickname", "") for a in _list_accounts()}
    now = int(time.time())
    for r in rooms:
        if r.get("account_uid"):
            r["account_nick"] = accounts_map.get(str(r["account_uid"]), "")
        rid = r["room_id"]
        # B站凭证状态（needs_login → 前端引导重新扫码）
        auth_st = _read_room_json(rid, "auth_status.json")
        r["auth_status"] = auth_st.get("status", "ok")
        r["auth_reason"] = auth_st.get("reason", "")
        # 用户已经重新扫码（凭证文件比状态文件新）时不必再提示，等机器人自己恢复
        if r["auth_status"] == "needs_login" and r.get("account_uid"):
            try:
                cred_file = _get_account_dir(str(r["account_uid"])) / "credential.json"
                status_file = _room_data_file(rid, "auth_status.json")
                if cred_file.exists() and status_file.exists():
                    cred_mtime = int(cred_file.stat().st_mtime)
                    status_mtime = int(status_file.stat().st_mtime)
                    if cred_mtime > status_mtime + 5:
                        r["auth_status"] = "ok"
                        r["auth_reason"] = ""
            except Exception:  # noqa: BLE001
                pass
        # 心跳（进程活着但掉线时前端能显示细节）
        hb = _read_room_json(rid, "bot_status.json")
        r["heartbeat"] = hb
        if hb.get("ts"):
            r["heartbeat_age"] = now - int(hb["ts"])
        # 上次崩溃记录
        crash = _read_crash_info(rid)
        if crash:
            r["crash_info"] = crash
            r["recent_crash"] = (now - int(crash.get("ts") or 0)) < 900
        else:
            r["recent_crash"] = False
        if r.get("status") == "running" and r["auth_status"] == "needs_login":
            r["status_note"] = "运行中（等待重新登录）"
    # 根据用户角色过滤
    token = request.cookies.get("session", "")
    _, role, allowed = _user_role(token)
    if role in ("user", "streamer") and allowed:
        rooms = [r for r in rooms if r["room_id"] in allowed]
    return {"rooms": rooms}


@app.post("/api/rooms")
async def api_create_room(request: Request):
    """新建房间: 传入 anchor_uid, 可选 room_display_id / bot_name / port."""
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"error": "bad request"}, status_code=400)

    anchor_uid = body.get("anchor_uid")
    if not anchor_uid:
        return JSONResponse({"error": "anchor_uid is required"}, status_code=400)

    # 检查直播间号
    room_display_id = body.get("room_display_id")
    if not room_display_id:
        return JSONResponse({"error": "请填写直播间号（room_display_id）"}, status_code=400)

    room_id = str(room_display_id)
    from app.config import ensure_room_dirs, get_room_path
    room_dir = ensure_room_dirs(room_id, base_dir=_ROOMS_BASE_DIR)
    cfg_path = room_dir / "config.yaml"

    if cfg_path.exists():
        return JSONResponse({"error": f"房间 {room_id} 已存在"}, status_code=409)

    # 从模板复制一份配置：优先 config.example.yaml，其次任意可用的 config.yaml；
    # 都找不到时按内置默认值生成（绝不让「新建房间」卡在这里）
    import shutil
    from app.config import find_template_config, write_default_config

    src = find_template_config(_ROOMS_BASE_DIR)
    if src:
        shutil.copy2(str(src), str(cfg_path))
        logger.info("新建房间 %s：配置模板取自 %s", room_id, src)
    else:
        write_default_config(cfg_path)
        logger.warning("新建房间 %s：未找到任何配置模板，已按内置默认值生成", room_id)

    # 写入房间配置
    port = body.get("port", 8000)
    room_name = body.get("room_name", "")
    if not room_name:
        # 尝试从 B站 API 获取主播用户名
        try:
            headers = {
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
                "Referer": "https://www.bilibili.com/",
            }
            async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=8), headers=headers) as s:
                async with s.get(f"https://api.bilibili.com/x/web-interface/card?mid={anchor_uid}") as r:
                    if r.status == 200:
                        j = await r.json()
                        if j.get("code") == 0:
                            room_name = j.get("data", {}).get("card", {}).get("name", "")
        except Exception:
            pass
        if not room_name:
            room_name = str(anchor_uid)
    bot_name = f"ayabot{room_id[:4]}"
    from app.config import update_config_from_dict
    cfg_update = {
        "room_display_id": int(room_display_id),
        "anchor_uid": int(anchor_uid),
        "bot_name": bot_name,
        "room_name": room_name,
        "web_ui": {"port": int(port)},
    }
    update_config_from_dict(cfg_update, str(cfg_path))

    logger.info("room created: id=%s uid=%s port=%s", room_id, anchor_uid, port)
    return {"ok": True, "room_id": room_id, "room_display_id": room_display_id}


@app.post("/api/rooms/{room_id}/start")
async def api_start_room(room_id: str):
    """启动房间 Bot（自动选择同进程/子进程模式）。"""
    ok = await start_room_async(room_id)
    if not ok:
        return JSONResponse({"error": "启动失败，请检查配置"}, status_code=500)
    _mark_desired(room_id, True)
    _save_room_states()
    # 清除上次崩溃记录
    try:
        _crash_info_path(room_id).unlink(missing_ok=True)
    except Exception:  # noqa: BLE001
        pass
    _restart_attempts.pop(room_id, None)
    return {"ok": True, "status": "running"}


@app.post("/api/rooms/{room_id}/stop")
async def api_stop_room(room_id: str):
    """停止房间 Bot（同时清理同进程和子进程）。"""
    await stop_room_async(room_id)
    _mark_desired(room_id, False)
    _save_room_states()
    return {"ok": True, "status": "stopped"}


@app.post("/api/rooms/{room_id}/restart")
async def api_restart_room(room_id: str):
    """重启房间 Bot（自动选择同进程/子进程模式）。"""
    ok = await restart_room_async(room_id)
    if ok:
        _mark_desired(room_id, True)
    _save_room_states()
    return {"ok": ok, "status": "running" if ok else "stopped"}


@app.delete("/api/rooms/{room_id}")
async def api_delete_room(room_id: str):
    """删除房间（停止进程 + 删目录）."""
    import shutil
    from app.config import get_room_path

    clean_room(room_id)
    _save_room_states()

    # 删除目录
    room_dir = get_room_path(room_id, base_dir=_ROOMS_BASE_DIR)
    if room_dir.exists():
        shutil.rmtree(str(room_dir))
    logger.info("room deleted: %s", room_id)
    return {"ok": True}


@app.get("/api/rooms/{room_id}/config")
async def api_get_room_config(room_id: str):
    """获取房间配置."""
    from app.config import get_room_path
    cfg_path = get_room_path(room_id, base_dir=_ROOMS_BASE_DIR) / "config.yaml"
    if not cfg_path.exists():
        return JSONResponse({"error": "room not found"}, status_code=404)
    from app.config import load_config, config_to_dict
    try:
        cfg = load_config(str(cfg_path))
        return config_to_dict(cfg)
    except Exception as exc:
        return JSONResponse({"error": str(exc)}, status_code=500)


@app.post("/api/rooms/{room_id}/config")
async def api_save_room_config(room_id: str, request: Request):
    """保存房间配置."""
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"error": "bad request"}, status_code=400)
    from app.config import get_room_path
    cfg_path = get_room_path(room_id, base_dir=_ROOMS_BASE_DIR) / "config.yaml"
    if not cfg_path.exists():
        return JSONResponse({"error": "room not found"}, status_code=404)
    from app.config import update_config_from_dict
    ok = update_config_from_dict(body, str(cfg_path))
    return {"ok": ok}


@app.get("/api/rooms/{room_id}/config/export")
async def api_room_config_export(room_id: str):
    """导出房间配置为 JSON 下载。"""
    from app.config import get_room_path
    cfg_path = get_room_path(room_id, base_dir=_ROOMS_BASE_DIR) / "config.yaml"
    if not cfg_path.exists():
        return JSONResponse({"error": "room not found"}, status_code=404)
    try:
        from app.config import load_config, config_to_dict
        cfg = load_config(str(cfg_path))
        data = config_to_dict(cfg)
        return JSONResponse(data)
    except Exception as exc:
        return JSONResponse({"error": str(exc)}, status_code=500)


@app.post("/api/rooms/{room_id}/config/import")
async def api_room_config_import(room_id: str, request: Request):
    """导入 JSON 配置覆盖房间配置。"""
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"error": "bad request"}, status_code=400)
    from app.config import get_room_path
    cfg_path = get_room_path(room_id, base_dir=_ROOMS_BASE_DIR) / "config.yaml"
    if not cfg_path.exists():
        return JSONResponse({"error": "room not found"}, status_code=404)
    try:
        from app.config import update_config_from_dict
        ok = update_config_from_dict(body, str(cfg_path))
        return {"ok": ok}
    except Exception as exc:
        return JSONResponse({"error": str(exc)}, status_code=500)


# ══════════════════════════════════════════════════════════════
#  房间级 API 外部接口配置
# ══════════════════════════════════════════════════════════════


def _load_room_raw_config(room_id: str) -> dict:
    """加载房间的原始 config.yaml 内容。"""
    from app.config import get_room_path
    cfg_path = get_room_path(room_id, base_dir=_ROOMS_BASE_DIR) / "config.yaml"
    if not cfg_path.exists():
        return {}
    try:
        return yaml.safe_load(cfg_path.read_text(encoding="utf-8")) or {}
    except Exception:
        return {}


def _save_room_raw_config(room_id: str, raw: dict) -> bool:
    """保存 dict 到房间的 config.yaml。"""
    from app.config import get_room_path
    cfg_path = get_room_path(room_id, base_dir=_ROOMS_BASE_DIR) / "config.yaml"
    if not cfg_path.exists():
        return False
    try:
        cfg_path.write_text(
            yaml.dump(raw, default_flow_style=False, allow_unicode=True),
            encoding="utf-8",
        )
        return True
    except Exception:
        return False


@app.get("/api/rooms/{room_id}/api_config")
async def api_room_api_config(room_id: str, request: Request):
    """获取房间的 API 外部接口配置。"""
    raw = _load_room_raw_config(room_id)
    web_ui = raw.get("web_ui", {}) or {}
    api_enabled = bool(web_ui.get("api_enabled", False))
    api_token = str(web_ui.get("api_token", "") or "")

    # 构建 API 地址
    if _API_DOMAIN:
        base = _API_DOMAIN.rstrip("/")
    else:
        host = request.headers.get("host", f"{_HTTP_HOST}:{_HTTP_PORT}")
        scheme = request.headers.get("x-forwarded-proto", "http")
        base = f"{scheme}://{host}"
    api_url = f"{base}/api/external/user_stats?room_id={room_id}"

    return {
        "ok": True,
        "api_enabled": api_enabled,
        "has_key": bool(api_token),
        "full_key": api_token,
        "api_url": api_url,
    }


@app.post("/api/rooms/{room_id}/api_toggle")
async def api_room_api_toggle(room_id: str):
    """切换房间的 API 开关。开启时自动生成密钥（如无已有密钥）。"""
    import secrets as _secrets

    raw = _load_room_raw_config(room_id)
    if not raw:
        return JSONResponse({"error": "room not found"}, status_code=404)

    web_ui = raw.setdefault("web_ui", {})
    was_enabled = bool(web_ui.get("api_enabled", False))
    new_enabled = not was_enabled
    web_ui["api_enabled"] = new_enabled

    new_key = ""
    masked = ""
    if new_enabled:
        # 开启时：如果有旧 key 则保留，否则自动生成
        existing = str(web_ui.get("api_token", "") or "")
        if existing:
            new_key = existing
        else:
            new_key = _secrets.token_hex(32)
            web_ui["api_token"] = new_key
        t = new_key
        masked = t[:6] + "*" * (len(t) - 10) + t[-4:] if len(t) > 12 else "****"

    _save_room_raw_config(room_id, raw)
    logger.info("room %s API %s (token=%s)", room_id, "enabled" if new_enabled else "disabled", masked or "none")

    return {
        "ok": True,
        "api_enabled": new_enabled,
        "has_key": bool(new_key),
        "key_masked": masked,
        "message": "API 已开启" if new_enabled else "API 已关闭",
    }


@app.post("/api/rooms/{room_id}/api_regenerate")
async def api_room_api_regenerate(room_id: str):
    """重新生成房间的 API 密钥。"""
    import secrets as _secrets

    raw = _load_room_raw_config(room_id)
    if not raw:
        return JSONResponse({"error": "room not found"}, status_code=404)

    new_key = _secrets.token_hex(32)
    web_ui = raw.setdefault("web_ui", {})
    web_ui["api_token"] = new_key
    web_ui["api_enabled"] = True

    _save_room_raw_config(room_id, raw)
    t = new_key
    masked = t[:6] + "*" * (len(t) - 10) + t[-4:] if len(t) > 12 else "****"
    logger.info("room %s API key regenerated", room_id)

    return {
        "ok": True,
        "key_masked": masked,
        "full_key": new_key,
        "message": "新密钥已生成",
    }


@app.get("/api/llm_config/export")
async def api_llm_config_export():
    """导出 LLM 配置为 JSON 下载。"""
    return JSONResponse({
        "enabled": _LLM_CONFIG_DICT.get("enabled", False),
        "provider": _LLM_CONFIG_DICT.get("provider", "openai"),
        "api_key": _LLM_CONFIG_DICT.get("api_key", ""),
        "base_url": _LLM_CONFIG_DICT.get("base_url", ""),
        "model": _LLM_CONFIG_DICT.get("model", ""),
        "wake_word": _LLM_CONFIG_DICT.get("wake_word", "ayabot"),
        "temperature": _LLM_CONFIG_DICT.get("temperature", 0.7),
        "top_p": _LLM_CONFIG_DICT.get("top_p", 0.9),
        "max_tokens": _LLM_CONFIG_DICT.get("max_tokens", 150),
        "system_prompt": _LLM_CONFIG_DICT.get("system_prompt", ""),
        "context": _LLM_CONFIG_DICT.get("context", {}),
    })


@app.post("/api/llm_config/import")
async def api_llm_config_import(request: Request):
    """导入 JSON 覆盖 LLM 配置。"""
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"error": "bad request"}, status_code=400)
    for key in ("enabled", "provider", "api_key", "base_url", "model", "wake_word", "temperature", "top_p", "max_tokens", "system_prompt"):
        if key in body:
            _LLM_CONFIG_DICT[key] = body[key]
    if "context" in body and isinstance(body["context"], dict):
        _LLM_CONFIG_DICT.setdefault("context", {}).update(body["context"])
    # 回写 config.yaml
    try:
        cfg_path = Path(_CONFIG_YAML_PATH)
        raw = yaml.safe_load(cfg_path.read_text(encoding="utf-8")) or {}
        raw["llm"] = {k: _LLM_CONFIG_DICT.get(k) for k in ("enabled","provider","api_key","base_url","model","wake_word","temperature","top_p","max_tokens","system_prompt")}
        raw["llm"]["context"] = _LLM_CONFIG_DICT.get("context", {})
        cfg_path.write_text(yaml.dump(raw, default_flow_style=False, allow_unicode=True), encoding="utf-8")
    except Exception as exc:
        return JSONResponse({"error": f"save failed: {exc}"}, status_code=500)
    return {"ok": True}


# ══════════════════════════════════════════════════════════════
#  B站账号管理 API
# ══════════════════════════════════════════════════════════════

_ACCOUNTS_DIR: str = "accounts"


def _get_account_dir(uid: str) -> Path:
    return Path(_ROOMS_BASE_DIR).resolve() / _ACCOUNTS_DIR / str(uid)


def _list_accounts() -> list[dict[str, Any]]:
    """扫描 accounts/ 目录列出所有已登录 B站 账号."""
    base = Path(_ROOMS_BASE_DIR).resolve() / _ACCOUNTS_DIR
    if not base.exists():
        return []
    accounts: list[dict[str, Any]] = []
    for d in sorted(base.iterdir()):
        if not d.is_dir():
            continue
        uid = d.name
        cred_path = d / "credential.json"
        meta_path = d / "meta.yaml"
        meta = {}
        if meta_path.exists():
            try:
                meta = yaml.safe_load(meta_path.read_text(encoding="utf-8")) or {}
            except Exception:
                meta = {}
        has_cred = cred_path.exists()
        nick = meta.get("nickname", "") or meta.get("uname", "") or f"UID:{uid}"
        accounts.append({
            "uid": uid,
            "nickname": nick,
            "has_credential": has_cred,
            "linked_rooms": _get_account_rooms(uid),
        })
    return accounts


def _get_account_rooms(uid: str) -> list[dict[str, Any]]:
    """返回指定 B站 账号关联了哪些房间."""
    linked: list[dict[str, Any]] = []
    rooms_dir = Path(_ROOMS_BASE_DIR).resolve() / DEFAULT_ROOMS_DIR
    if not rooms_dir.exists():
        return linked
    for d in sorted(rooms_dir.iterdir()):
        if not d.is_dir():
            continue
        cfg_path = d / "config.yaml"
        if not cfg_path.exists():
            continue
        try:
            cfg = yaml.safe_load(cfg_path.read_text(encoding="utf-8")) or {}
        except Exception:
            continue
        account_uid = cfg.get("account_uid", "")
        if str(account_uid) == str(uid):
            linked.append({
                "room_id": d.name,
                "bot_name": cfg.get("web_ui", {}).get("bot_name", ""),
            })
    return linked


@app.post("/api/bili_accounts")
async def api_bili_login_account(request: Request):
    """生成 B站 二维码用于登录账号（保存到 accounts/<uid>/credential.json）."""
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"error": "bad request"}, status_code=400)

    account_uid = body.get("uid", "")
    # 不强制 UID — 如果没传，登录后自动从 credential 提取

    # 生成二维码
    try:
        from bilibili_api import login_v2  # noqa: PLC0415
    except Exception:
        return JSONResponse({"error": "bilibili_api not available"}, status_code=500)

    qr = login_v2.QrCodeLogin(platform=login_v2.QrCodeLoginChannel.WEB)
    await qr.generate_qrcode()
    qr_pic = qr.get_qrcode_picture()
    session_id = str(uuid.uuid4())

    # 直接使用 bilibili_api 生成的二维码图片
    import base64  # noqa: PLC0415

    img_b64 = base64.b64encode(qr_pic.content).decode("ascii")

    _BILI_LOGIN_SESSIONS[session_id] = {
        "qr": qr,
        "qrcode_key": qr._QrCodeLogin__qr_key,  # noqa: SLF001
        "created_at": time.time(),
        "state": "waiting",
        "target_uid": account_uid or "",
    }

    return {
        "ok": True,
        "session_id": session_id,
        "qr_image": f"data:image/png;base64,{img_b64}",
    }


@app.get("/api/bili_accounts")
async def api_list_accounts():
    """列出所有已登录的 B站 账号."""
    return {"accounts": _list_accounts()}


@app.post("/api/bili_accounts/save")
async def api_save_account_credential(request: Request):
    """保存扫码登录后的凭据到 accounts/<uid>/credential.json."""
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"ok": False, "error": "bad request"}, status_code=400)

    session_id = body.get("session_id", "")
    sess = _BILI_LOGIN_SESSIONS.get(session_id)
    if not sess:
        logger.warning("bili save: session not found: %s", session_id)
        return {"ok": False, "error": "session expired"}

    qr = sess["qr"]
    if not qr.has_done() and not sess.get("cred_cookies"):
        logger.warning("bili save: login not completed for session %s", session_id)
        return {"ok": False, "error": "login not completed"}

    target_uid = sess.get("target_uid", "")
    if not target_uid:
        # 如果没传 UID，登录后从 credential 获取
        target_uid = ""

    # 优先使用 status 轮询时当场解析好的完整凭据（B站 编码 URL 兼容）
    if sess.get("cred_cookies"):
        cookies = dict(sess["cred_cookies"])
    else:
        # 兜底：直接取库解析结果（旧版明文 URL 场景）
        try:
            credential = qr.get_credential()
        except Exception as exc:
            logger.warning("bili save: get credential failed: %s", exc)
            return {"ok": False, "error": f"get credential failed: {exc}"}
        cookies = credential.get_cookies()

    # 统一重建 credential（供 nav 兜底等后续使用）
    from bilibili_api import Credential as _Cred  # noqa: PLC0415

    credential = _Cred(
        sessdata=cookies.get("SESSDATA", ""),
        bili_jct=cookies.get("bili_jct", ""),
        buvid3=cookies.get("buvid3", "") or None,
        dedeuserid=cookies.get("DedeUserID", "") or None,
        ac_time_value=cookies.get("ac_time_value", ""),
    )

    dedeuserid = cookies.get("DedeUserID", "")

    # 如果没传 UID，使用登录后的 DedeUserID
    if not target_uid and dedeuserid:
        target_uid = dedeuserid

    # 兜底：B站 新接口格式变化导致 check_state() 解析不到 DedeUserID 时，
    # 用 SESSDATA 调 nav 接口恢复用户 UID（data.mid）
    if not target_uid and cookies.get("SESSDATA"):
        try:
            from bilibili_api.utils.network import API as _BILI_API, Api as _BILI_Api  # noqa: PLC0415
            nav = await _BILI_Api(**_BILI_API["info"]["valid"], credential=credential).result
            mid = str(nav.get("mid", "") or "")
            if mid and mid != "0":
                target_uid = mid
                logger.warning("bili save: recovered uid from nav: %s", mid[:6])
            else:
                logger.warning("bili save: nav returned no mid (isLogin=%s)", nav.get("isLogin"))
        except Exception as exc:
            logger.warning("bili save: nav fallback failed: %s", exc)

    if not target_uid:
        logger.warning("bili save: no target uid after fallback")
        return {"ok": False, "error": "no target uid (未能从登录结果获取 DedeUserID)"}

    # 保存到 accounts/<uid>/
    acc_dir = _get_account_dir(target_uid)
    acc_dir.mkdir(parents=True, exist_ok=True)

    cred_data = {
        "SESSDATA": cookies.get("SESSDATA", ""),
        "bili_jct": cookies.get("bili_jct", ""),
        "buvid3": cookies.get("buvid3", ""),
        "DedeUserID": dedeuserid,
        "ac_time_value": cookies.get("ac_time_value", ""),
    }
    cred_json = json.dumps(cred_data, ensure_ascii=False, indent=2)
    (acc_dir / "credential.json").write_text(cred_json, encoding="utf-8")
    logger.info("credential saved for account %s", target_uid)

    # 查询用户昵称
    nickname = ""
    try:
        headers = {
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
            "Referer": "https://www.bilibili.com/",
        }
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=10), headers=headers) as sess_aio:
            async with sess_aio.get(
                f"https://api.bilibili.com/x/web-interface/card?mid={dedeuserid}"
            ) as resp:
                info = await resp.json()
                if info.get("code") == 0:
                    nickname = info.get("data", {}).get("card", {}).get("name", "")
    except Exception:
        pass

    # 始终写入 meta.yaml（即使昵称获取失败也用 UID 兜底）
    (acc_dir / "meta.yaml").write_text(
        yaml.dump({"nickname": nickname or f"UID:{dedeuserid}", "uname": nickname or ""}, allow_unicode=True),
        encoding="utf-8",
    )

    _BILI_LOGIN_SESSIONS.pop(session_id, None)
    logger.info("bili account saved: uid=%s nickname=%s", dedeuserid, nickname)

    return {
        "ok": True,
        "uid": dedeuserid,
        "nickname": nickname,
    }


@app.get("/api/bili_accounts/status")
async def api_account_login_status(session_id: str):
    """查询账号二维码登录状态."""
    sess = _BILI_LOGIN_SESSIONS.get(session_id)
    if not sess:
        return {"state": "expired"}

    qr = sess["qr"]

    # 二维码硬超时：B站二维码有效期通常 180 秒，60 秒后已经不可靠
    import time as _time2
    elapsed = _time2.time() - sess.get("created_at", 0)
    QR_MAX_AGE = 60  # 60 秒后强制过期

    if elapsed >= QR_MAX_AGE:
        # 不删除 session，给前端留足够时间看到 "timeout"
        return {"state": "timeout"}

    try:
        # 如果此前已解析出完整凭据，直接返回 done
        if sess.get("cred_cookies"):
            return {"state": "done"}

        # 直接用 qrcode_key 轮询 B站 poll 接口（bilibili_api 的 Api 自带 buvid 指纹，
        # 避开 412 风控）。B站 新接口扫码成功后 url 只含 ticket、不再直接携带
        # SESSDATA 等，bilibili_api 17.4.x 的 check_state() 无法适配，
        # 这里自行轮询并在 code=0 时访问 crossDomain URL 收集登录 Cookie。
        from bilibili_api import login_v2 as _lv2  # noqa: PLC0415
        from bilibili_api.utils.network import Api as _BILI_Api  # noqa: PLC0415
        from bilibili_api import Credential as _Cred  # noqa: PLC0415

        _ev = (
            await _BILI_Api(credential=_Cred(), **_lv2.API["qrcode"]["web"]["get_events"])
            .update_params(**{"qrcode_key": sess["qrcode_key"]})
            .result
        )
        _code = _ev.get("code")
        if _code == 86101:  # 未扫码
            return {"state": "waiting"}
        if _code == 86090:  # 已扫码待确认
            return {"state": "scanned"}
        if _code == 86038:  # 过期
            return {"state": "timeout"}
        if _code == 0:  # 登录成功
            _raw_url = _ev.get("url", "")
            _cookies = {
                "SESSDATA": "", "bili_jct": "", "buvid3": "",
                "DedeUserID": "", "ac_time_value": _ev.get("refresh_token", ""),
            }
            # B站 新流程：登录成功后 url 只含 ticket（不再直接带 SESSDATA 等），
            # 需访问该 crossDomain URL，B站 通过 Set-Cookie 下发登录 Cookie。
            if _raw_url:
                try:
                    _headers = {
                        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
                        "Referer": "https://www.bilibili.com/",
                    }
                    async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15), headers=_headers) as _s:
                        async with _s.get(_raw_url) as _r:
                            await _r.read()  # 确保响应被消费，Set-Cookie 写入 cookie jar
                            for _ck in _s.cookie_jar:
                                if _ck.key in _cookies:
                                    _cookies[_ck.key] = _ck.value
                    logger.warning(
                        "bili status: crossDomain visited -> has_sess=%s has_jct=%s dede=%r",
                        bool(_cookies.get("SESSDATA")),
                        bool(_cookies.get("bili_jct")),
                        (_cookies.get("DedeUserID") or "")[:6],
                    )
                except Exception as exc:
                    logger.warning("bili status: crossDomain visit failed: %s", exc)
            sess["cred_cookies"] = _cookies
            logger.warning(
                "bili status: parsed ok has_sess=%s has_jct=%s dede=%r",
                bool(_cookies.get("SESSDATA")),
                bool(_cookies.get("bili_jct")),
                (_cookies.get("DedeUserID") or "")[:6],
            )
            return {"state": "done"}
        return {"state": "waiting"}
    except Exception as exc:
        logger.warning("account login status error: %s", exc)
        return {"state": "error", "message": str(exc)}


@app.delete("/api/bili_accounts/{uid}")
async def api_delete_account(uid: str):
    """删除 B站 账号（解除所有房间的关联）."""
    import shutil  # noqa: PLC0415

    # 先解除所有房间的关联
    rooms_dir = Path(_ROOMS_BASE_DIR).resolve() / DEFAULT_ROOMS_DIR
    if rooms_dir.exists():
        for d in rooms_dir.iterdir():
            if not d.is_dir():
                continue
            cfg_path = d / "config.yaml"
            if not cfg_path.exists():
                continue
            try:
                cfg = yaml.safe_load(cfg_path.read_text(encoding="utf-8")) or {}
            except Exception:
                continue
            if str(cfg.get("account_uid", "")) == str(uid):
                cfg.pop("account_uid", None)
                (d / "config.yaml").write_text(
                    yaml.dump(cfg, default_flow_style=False, allow_unicode=True),
                    encoding="utf-8",
                )
                logger.info("removed account %s from room %s", uid, d.name)

    # 删除账号目录
    acc_dir = _get_account_dir(uid)
    if acc_dir.exists():
        shutil.rmtree(str(acc_dir))

    logger.info("bili account deleted: %s", uid)
    return {"ok": True}


@app.post("/api/bili_accounts/{uid}/nickname")
async def api_update_account_nickname(uid: str, request: Request):
    """修改 B站 账号的显示名称."""
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"error": "bad request"}, status_code=400)
    nickname = body.get("nickname", "").strip()
    if not nickname:
        return JSONResponse({"error": "nickname required"}, status_code=400)
    meta_path = _get_account_dir(uid) / "meta.yaml"
    try:
        meta = yaml.safe_load(meta_path.read_text(encoding="utf-8")) if meta_path.exists() else {}
    except Exception:
        meta = {}
    meta["nickname"] = nickname
    meta_path.write_text(yaml.dump(meta, allow_unicode=True), encoding="utf-8")
    return {"ok": True, "nickname": nickname}


@app.post("/api/bili_accounts/{uid}/verify")
async def api_verify_account_credential(uid: str):
    """验证 B站 凭证是否仍然有效."""
    cred_path = _get_account_dir(uid) / "credential.json"
    if not cred_path.exists():
        return {"valid": False, "error": "no credential"}
    try:
        cred_data = json.loads(cred_path.read_text(encoding="utf-8"))
    except Exception:
        return {"valid": False, "error": "corrupted credential"}
    try:
        from bilibili_api import Credential  # noqa: PLC0415
        credential = Credential(
            sessdata=cred_data.get("SESSDATA", ""),
            bili_jct=cred_data.get("bili_jct", ""),
            buvid3=cred_data.get("buvid3", ""),
            dedeuserid=cred_data.get("DedeUserID", ""),
            ac_time_value=cred_data.get("ac_time_value", ""),
        )
        ok = await credential.check_valid()
        return {"valid": ok}
    except Exception as exc:
        return {"valid": False, "error": str(exc)}


# ══════════════════════════════════════════════════════════════
#  Per-Room 数据 API
# ══════════════════════════════════════════════════════════════

def _room_db_path(room_id: str) -> Path:
    """返回房间的 SQLite 数据库路径."""
    from app.config import get_room_path
    return get_room_path(room_id, base_dir=_ROOMS_BASE_DIR) / "data" / "bot.db"


@app.get("/api/rooms/{room_id}/log/export")
async def api_room_log_export(room_id: str):
    """导出 Bot 日志为文本文件。"""
    from app.config import get_room_path
    log_path = get_room_path(room_id, base_dir=_ROOMS_BASE_DIR) / "bot.log"
    if not log_path.exists():
        return JSONResponse({"error": "log not found"}, status_code=404)
    try:
        text = log_path.read_text(encoding="utf-8", errors="replace")
        return Response(
            content=text,
            media_type="text/plain",
            headers={"Content-Disposition": f'attachment; filename="bot_{room_id}.log"'},
        )
    except Exception as exc:
        return JSONResponse({"error": str(exc)}, status_code=500)


@app.post("/api/rooms/{room_id}/log/clear")
async def api_room_log_clear(room_id: str):
    """清空房间 Bot 日志文件。"""
    from app.config import get_room_path
    log_path = get_room_path(room_id, base_dir=_ROOMS_BASE_DIR) / "bot.log"
    try:
        if log_path.exists():
            log_path.write_text("", encoding="utf-8")
        return {"ok": True}
    except Exception as exc:
        return JSONResponse({"error": str(exc)}, status_code=500)


@app.get("/api/rooms/{room_id}/log")
async def api_room_log(room_id: str, request: Request, lines: int = 200):
    """返回房间 Bot 日志的最新 N 行。"""
    from app.config import get_room_path
    log_path = get_room_path(room_id, base_dir=_ROOMS_BASE_DIR) / "bot.log"
    if not log_path.exists():
        return {"lines": []}
    try:
        text = log_path.read_text(encoding="utf-8", errors="replace")
        all_lines = text.splitlines()
        tail = all_lines[-lines:] if len(all_lines) > lines else all_lines
        return {"lines": tail, "total": len(all_lines)}
    except Exception as exc:
        return JSONResponse({"error": str(exc)}, status_code=500)


@app.get("/api/rooms/{room_id}/ranking")
async def api_room_ranking(room_id: str, rStart: str = "", rEnd: str = "", rType: str = "all"):
    """获取指定房间的送礼排行."""
    db_path = _room_db_path(room_id)
    if not db_path.exists():
        return {"ranking": []}

    try:
        conn = sqlite3.connect(str(db_path))
        cur = conn.cursor()

        where_clauses = ["1=1"]
        params: list[Any] = []

        if rStart:
            where_clauses.append("date(ts, 'unixepoch', 'localtime') >= date(?)")
            params.append(rStart)
        if rEnd:
            where_clauses.append("date(ts, 'unixepoch', 'localtime') <= date(?)")
            params.append(rEnd)

        if rType == "gift":
            where_clauses.append("is_blind_box = 0")
        elif rType == "blindbox":
            where_clauses.append("is_blind_box = 1")

        where_sql = " AND ".join(where_clauses)
        if where_clauses:
            where_sql += " AND event_type = 'SEND_GIFT'"
        else:
            where_sql = "event_type = 'SEND_GIFT'"

        cur.execute(f"""
            SELECT uid, uname,
                   ROUND(SUM(CASE WHEN is_blind_box=1 THEN CAST(actual_value AS REAL) / 10.0 ELSE CAST(json_extract(raw_json, '$.total_coin') AS REAL) / 1000.0 END), 2) as total,
                   ROUND(SUM(CAST(profit_value AS REAL) / 10.0), 2) as total_profit
            FROM gift_events WHERE {where_sql}
            GROUP BY uid ORDER BY total DESC LIMIT 50
        """, params)
        rows = cur.fetchall()
        conn.close()

        ranking = [
            {"uid": r[0], "uname": r[1], "count": 0, "total": r[2] or 0, "total_profit": r[3] or 0}
            for r in rows
        ]
        return {"ranking": ranking}
    except Exception as exc:
        return {"error": str(exc)}


@app.get("/api/rooms/{room_id}/user_gifts")
async def api_room_user_gifts(room_id: str, uid: int = 0, date: str = "", gift_type: str = "all"):
    """获取指定房间某用户某天的送礼详情."""
    db_path = _room_db_path(room_id)
    if not db_path.exists() or not uid or not date:
        return []

    try:
        conn = sqlite3.connect(str(db_path))
        cur = conn.cursor()

        where_extra = ""
        if gift_type == "gift":
            where_extra = " AND is_blind_box = 0"
        elif gift_type == "blindbox":
            where_extra = " AND is_blind_box = 1"

        cur.execute(f"""
            SELECT uid, uname, gift_name, gift_num, actual_value, ts, is_blind_box, id, raw_json
            FROM gift_events
            WHERE uid = ? AND date(ts, 'unixepoch', 'localtime') = date(?) AND event_type = 'SEND_GIFT'{where_extra}
            ORDER BY ts
        """, (uid, date))
        rows = cur.fetchall()
        conn.close()

        import json as _json
        results = []
        # 合并字典：key = (batch_combo_id, gift_name) → merged entry
        merged = {}
        for r in rows:
            raw = {}
            if r[8]:
                try:
                    raw = _json.loads(r[8])
                except Exception:
                    raw = {}
            # 从 raw_json 解析实际价格、舰长等级、头像、礼物图标、batch_combo_id
            guard_level = 0
            avatar = ""
            gift_icon = ""
            actual_value = r[4]  # DB actual_value (for blindbox = item value)
            is_blind = bool(r[6])

            if not is_blind and raw:
                # 一般礼物：total_coin 单位是 1000=1元
                actual_value = round(int(raw.get("total_coin", 0) or 0) / 1000.0, 2)
            else:
                # 盲盒：DB actual_value 单位是角，/10 转元
                actual_value = round(actual_value / 10.0, 2)

            if raw:
                sender_info = raw.get("sender_uinfo", {}) or {}
                base = sender_info.get("base", {}) or {}
                avatar = base.get("face", "") or ""
                guard_info = sender_info.get("guard", {}) or None
                if guard_info:
                    guard_level = guard_info.get("level", 0) or 0
                medal = sender_info.get("medal", {}) or None
                if medal and not guard_level:
                    guard_level = medal.get("guard_level", 0) or 0
                gift_info = raw.get("gift_info", {}) or {}
                gift_icon = gift_info.get("img_basic", "") or gift_info.get("webp", "") or ""

            # 合并 key：batch_combo_id（短时间相同礼物合并）
            batch_key = r[8] and _json.loads(r[8]).get("batch_combo_id", "") or ""
            merge_key = (batch_key, r[2])

            if merge_key in merged:
                merged[merge_key]["gift_num"] += r[3]
                merged[merge_key]["actual_value"] += actual_value
            else:
                merged[merge_key] = {
                    "uid": r[0], "uname": r[1], "gift_name": r[2],
                    "gift_num": r[3], "actual_value": actual_value,
                    "ts": r[5], "is_blind_box": is_blind,
                    "id": r[7],
                    "guard_level": guard_level,
                    "avatar": avatar,
                    "gift_icon": gift_icon,
                }

        results = list(merged.values())
        return results
    except Exception:
        return []


@app.get("/api/rooms/{room_id}/guards")
async def api_room_guards(room_id: str, rStart: str = "", rEnd: str = "", limit: int = 200):
    """大航海（上舰）记录：列表 + 汇总."""
    db_path = _room_db_path(room_id)
    if not db_path.exists():
        return {"items": [], "totals": {"count": 0, "value": 0, "captain": 0, "commander": 0, "governor": 0}}
    try:
        from app.storage import StatsStore  # noqa: PLC0415

        store = StatsStore(str(db_path))
        try:
            items = store.list_guard_events(date_from=rStart, date_to=rEnd, limit=max(1, min(limit, 1000)))
            totals = store.get_guard_totals(date_from=rStart, date_to=rEnd)
        finally:
            store.close()
        return {"items": items, "totals": totals}
    except Exception as exc:  # noqa: BLE001
        logger.warning("room %s guards query failed: %s", room_id, exc)
        return JSONResponse({"error": str(exc)}, status_code=500)


@app.get("/api/rooms/{room_id}/user_dates")
async def api_room_user_dates(room_id: str, uid: int = 0):
    """获取指定房间某用户有送礼记录的所有日期."""
    db_path = _room_db_path(room_id)
    if not db_path.exists() or not uid:
        return []

    try:
        conn = sqlite3.connect(str(db_path))
        cur = conn.cursor()
        cur.execute(
            "SELECT DISTINCT date(ts, 'unixepoch', 'localtime') FROM gift_events WHERE uid = ? ORDER BY date(ts, 'unixepoch', 'localtime')",
            (uid,),
        )
        dates = [r[0] for r in cur.fetchall()]
        conn.close()
        return dates
    except Exception:
        return []


@app.get("/api/rooms/{room_id}/all_dates")
async def api_room_all_dates(room_id: str):
    """获取指定房间内所有用户有送礼记录的日期（去重）."""
    db_path = _room_db_path(room_id)
    if not db_path.exists():
        return []
    try:
        conn = sqlite3.connect(str(db_path))
        cur = conn.cursor()
        cur.execute(
            "SELECT DISTINCT date(ts, 'unixepoch', 'localtime') FROM gift_events ORDER BY date(ts, 'unixepoch', 'localtime')"
        )
        dates = [r[0] for r in cur.fetchall()]
        conn.close()
        return dates
    except Exception:
        return []


@app.get("/api/rooms/{room_id}/export_all")
async def api_room_export_all(
    room_id: str,
    date_from: str = "",
    date_to: str = "",
    gift_type: str = "all",
    sort: str = "ts",
    uid: int = 0,
):
    """
    导出指定房间在日期范围内的送礼明细（聚合排序版）。

    Args:
        date_from: 起始日期 YYYY-MM-DD（留空不限）
        date_to: 结束日期 YYYY-MM-DD（留空不限）
        gift_type: all|gift|blindbox
        sort: ts|uname|value — 按时间/用户名/价值排序
        uid: 指定用户 UID（0=所有人）
    """
    db_path = _room_db_path(room_id)
    if not db_path.exists():
        return []

    try:
        conn = sqlite3.connect(str(db_path))
        cur = conn.cursor()

        conditions = ["event_type = 'SEND_GIFT'"]
        params: list = []

        if date_from:
            conditions.append("date(ts, 'unixepoch', 'localtime') >= date(?)")
            params.append(date_from)
        if date_to:
            conditions.append("date(ts, 'unixepoch', 'localtime') <= date(?)")
            params.append(date_to)
        if gift_type == "gift":
            conditions.append("is_blind_box = 0")
        elif gift_type == "blindbox":
            conditions.append("is_blind_box = 1")
        if uid:
            conditions.append("uid = ?")
            params.append(uid)

        where = " AND ".join(conditions)

        cur.execute(f"""
            SELECT uid, uname, gift_name, gift_num, actual_value, ts, is_blind_box, id, raw_json
            FROM gift_events
            WHERE {where}
            ORDER BY ts ASC
        """, params)
        rows = cur.fetchall()

        # ══ 大航海兜底：用上舰记录 guard_events 反查每个 UID 的真实大航海等级 ══
        # 礼物事件 raw_json 的 sender_uinfo.guard / medal.guard_level 只有少数记录会携带，
        # 大量舰长/提督/总督送礼时该字段为空 → 被误判 guard_level=0，导出图鉴就只显示
        # 个别大航海徽章。guard_events 按 (uid,start_time) 去重的是权威上舰记录，用它兜底。
        guard_level_fallback: dict[int, int] = {}
        try:
            cur.execute(
                "SELECT uid, MAX(guard_level) AS lvl FROM guard_events WHERE guard_level > 0 GROUP BY uid"
            )
            for g_uid, g_lvl in cur.fetchall():
                guard_level_fallback[int(g_uid)] = int(g_lvl or 0)
        except Exception:
            guard_level_fallback = {}
        conn.close()

        import json as _json
        merged: dict[tuple, dict] = {}
        for r in rows:
            raw = {}
            if r[8]:
                try:
                    raw = _json.loads(r[8])
                except Exception:
                    raw = {}
            
            is_blind = bool(r[6])
            guard_level = 0
            avatar = ""
            gift_icon = ""
            actual_value = r[4]

            if not is_blind and raw:
                actual_value = round(int(raw.get("total_coin", 0) or 0) / 1000.0, 2)
            else:
                actual_value = round(actual_value / 10.0, 2)

            if raw:
                # ── 兼容两种归一化结构 ──
                # 旧协议 SEND_GIFT：字段嵌套在 sender_uinfo.base / .guard / .medal 里
                sender_info = raw.get("sender_uinfo", {}) or {}
                base = sender_info.get("base", {}) or {}
                avatar = base.get("face", "") or raw.get("face", "") or ""
                guard_info = sender_info.get("guard", {}) or None
                if guard_info:
                    guard_level = guard_info.get("level", 0) or 0
                # 新协议 SEND_GIFT_V2：guard_level / medal_info 在顶层
                if not guard_level and raw.get("guard_level"):
                    guard_level = int(raw.get("guard_level") or 0)
                medal = sender_info.get("medal", {}) or None
                if medal and not guard_level:
                    guard_level = medal.get("guard_level", 0) or 0
                if not guard_level:
                    medal2 = raw.get("medal_info", {}) or {}
                    guard_level = int(medal2.get("guard_level", 0) or 0)
                gift_info = raw.get("gift_info", {}) or {}
                gift_icon = gift_info.get("img_basic", "") or gift_info.get("webp", "") or ""

            # 事件 payload 里没带大航海信息 → 用上舰记录兜底
            if not guard_level:
                guard_level = guard_level_fallback.get(int(r[0]), 0)

            batch_key = r[8] and _json.loads(r[8]).get("batch_combo_id", "") or ""
            merge_key = (r[0], batch_key, r[2])  # (uid, batch_combo_id, gift_name)

            if merge_key in merged:
                merged[merge_key]["gift_num"] += r[3]
                merged[merge_key]["actual_value"] += actual_value
            else:
                merged[merge_key] = {
                    "uid": r[0], "uname": r[1], "gift_name": r[2],
                    "gift_num": r[3], "actual_value": actual_value,
                    "ts": r[5], "is_blind_box": is_blind,
                    "id": r[7],
                    "guard_level": guard_level,
                    "avatar": avatar,
                    "gift_icon": gift_icon,
                }

        results = list(merged.values())

        # 排序
        if sort == "uname":
            results.sort(key=lambda x: (x["uname"] or "", x["ts"] or 0))
        elif sort == "value":
            results.sort(key=lambda x: -(x["actual_value"] or 0))
        else:  # ts
            results.sort(key=lambda x: x["ts"] or 0)

        return results
    except Exception:
        return []


@app.post("/api/rooms/{room_id}/delete_old")
async def api_room_delete_old(room_id: str, request: Request):
    """删除指定房间的旧数据. data_type: 'gift' | 'danmaku' | 'all'."""
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"error": "bad request"}, status_code=400)

    date_str = body.get("date", "")
    data_type = body.get("type", "gift")
    if not date_str:
        return JSONResponse({"error": "date required"}, status_code=400)

    db_path = _room_db_path(room_id)
    if not db_path.exists():
        return {"deleted_gifts": 0, "deleted_danmaku": 0}

    try:
        conn = sqlite3.connect(str(db_path))
        cur = conn.cursor()
        result = {"deleted_gifts": 0, "deleted_danmaku": 0}
        if data_type in ("gift", "all"):
            cur.execute("DELETE FROM gift_events WHERE date(ts, 'unixepoch') <= date(?)", (date_str,))
            result["deleted_gifts"] = cur.rowcount
        if data_type in ("danmaku", "all"):
            cur.execute("DELETE FROM danmaku_log WHERE date(ts, 'unixepoch', 'localtime') <= date(?)", (date_str,))
            result["deleted_danmaku"] = cur.rowcount
        conn.commit()
        conn.close()
        # 清理无数据的月度汇总
        if result["deleted_gifts"]:
            _clean_orphan_monthly_stats(db_path)
        return result
    except Exception as exc:
        return JSONResponse({"error": str(exc)}, status_code=500)


def _clean_orphan_monthly_stats(db_path: Path) -> None:
    """删除已无 gift_events 数据的月度汇总行."""
    try:
        conn = sqlite3.connect(str(db_path))
        cur = conn.cursor()
        cur.execute("DELETE FROM monthly_blindbox_stats WHERE month NOT IN (SELECT DISTINCT month FROM gift_events)")
        cur.execute("DELETE FROM monthly_gift_stats WHERE month NOT IN (SELECT DISTINCT month FROM gift_events)")
        conn.commit()
        conn.close()
    except Exception:
        pass


# ══════════════════════════════════════════════════════════════
#  Danmaku Log API
# ══════════════════════════════════════════════════════════════


@app.get("/api/danmaku_log")
async def api_get_danmaku_log(room_id: str = "", limit: int = 50, offset: int = 0, date_from: str = "", date_to: str = "", asc: int = 1, keyword: str = "", gap_sec: int = 14400, start_ts: str = "", end_ts: str = "", uid: str = "", uname: str = ""):
    try:
        db_path = _room_db_path(room_id) if room_id else Path(_DB_PATH)
        if not db_path.exists():
            return {"rows": [], "total": 0}
        from app.storage import StatsStore
        store = StatsStore(str(db_path))
        rows = store.get_danmaku_log(limit=limit, offset=offset, date_from=date_from, date_to=date_to, asc=bool(asc), keyword=keyword, start_ts=start_ts, end_ts=end_ts, uid=uid, uname=uname)
        total = store.get_danmaku_log_count(date_from=date_from, date_to=date_to, keyword=keyword, start_ts=start_ts, end_ts=end_ts, uid=uid, uname=uname)
        # 录像/场次划分：按相邻弹幕时间间隔 >= gap_sec 切分为多段（一段=一场直播/一个录像）
        try:
            ts_list = store.get_danmaku_ts_list(date_from=date_from, date_to=date_to, keyword=keyword, start_ts=start_ts, end_ts=end_ts, uid=uid, uname=uname)
            sessions = []
            for ts in ts_list:
                if not sessions or ts - sessions[-1]["end"] >= max(1, gap_sec):
                    sessions.append({"start": ts, "end": ts})
                else:
                    sessions[-1]["end"] = ts
            def _sess_of(ts):
                # 线性查找（会话数通常很少）
                idx = 0
                for s in sessions:
                    if s["start"] <= ts <= s["end"]:
                        return idx, s
                    idx += 1
                # 兜底：找最近 不大于 ts 的 end
                best = None; bi = 0
                for i, s in enumerate(sessions):
                    if s["start"] <= ts:
                        best = s; bi = i
                return bi, best
            for r in rows:
                ts = r.get("ts")
                idx, s = _sess_of(ts)
                r["sess"] = idx + 1
                r["sess_start"] = s["start"]
                r["rel"] = max(0, ts - s["start"])
        except Exception as exc:
            logger.exception("danmaku session split failed")
        store.close()
        return {"rows": rows, "total": total}
    except Exception as exc:
        logger.exception("danmaku_log get failed")
        return JSONResponse({"error": str(exc)}, status_code=500)


@app.get("/api/danmaku_users")
async def api_get_danmaku_users(room_id: str = "", date_from: str = "", date_to: str = "", keyword: str = "", start_ts: str = "", end_ts: str = "", uid: str = "", uname: str = ""):
    """返回弹幕对应的去重用户列表（按发言次数降序），供前端用户筛选下拉使用。"""
    try:
        db_path = _room_db_path(room_id) if room_id else Path(_DB_PATH)
        if not db_path.exists():
            return {"users": []}
        from app.storage import StatsStore
        store = StatsStore(str(db_path))
        users = store.get_danmaku_users(date_from=date_from, date_to=date_to, keyword=keyword, start_ts=start_ts, end_ts=end_ts, uid=uid, uname=uname)
        store.close()
        return {"users": users}
    except Exception as exc:
        logger.exception("danmaku_users get failed")
        return JSONResponse({"error": str(exc)}, status_code=500)


@app.get("/api/danmaku_stats")
async def api_get_danmaku_stats(room_id: str = "", date_from: str = "", date_to: str = "", keyword: str = "", start_ts: str = "", end_ts: str = "", uid: str = "", uname: str = ""):
    """返回弹幕统计：总条数 / 去重用户数 / 发言TOP10 / 逐小时分布。"""
    try:
        db_path = _room_db_path(room_id) if room_id else Path(_DB_PATH)
        if not db_path.exists():
            return {"stats": None}
        from app.storage import StatsStore
        store = StatsStore(str(db_path))
        stats = store.get_danmaku_stats(date_from=date_from, date_to=date_to, keyword=keyword, start_ts=start_ts, end_ts=end_ts, uid=uid, uname=uname)
        store.close()
        return {"stats": stats}
    except Exception as exc:
        logger.exception("danmaku_stats get failed")
        return JSONResponse({"error": str(exc)}, status_code=500)


@app.get("/api/danmaku_sessions")
async def api_get_danmaku_sessions(room_id: str = "", date_from: str = "", date_to: str = "", keyword: str = "", start_ts: str = "", end_ts: str = "", uid: str = "", uname: str = "", gap_sec: int = 14400):
    """返回筛选集合下按相邻时间间隔切分的直播场次列表，供前端「按场次查看」下拉使用。"""
    try:
        db_path = _room_db_path(room_id) if room_id else Path(_DB_PATH)
        if not db_path.exists():
            return {"sessions": []}
        from app.storage import StatsStore
        store = StatsStore(str(db_path))
        sessions = store.get_danmaku_sessions(date_from=date_from, date_to=date_to, keyword=keyword, start_ts=start_ts, end_ts=end_ts, uid=uid, uname=uname, gap_sec=gap_sec)
        store.close()
        return {"sessions": sessions}
    except Exception as exc:
        logger.exception("danmaku_sessions get failed")
        return JSONResponse({"error": str(exc)}, status_code=500)


@app.get("/api/rooms/{room_id}/danmaku/dates")
async def api_room_danmaku_dates(room_id: str):
    """返回有弹幕记录的日期列表。"""
    db_path = _room_db_path(room_id)
    if not db_path.exists():
        return []
    try:
        from app.storage import StatsStore
        store = StatsStore(str(db_path))
        dates = store.get_danmaku_dates()
        store.close()
        return dates
    except Exception as exc:
        return JSONResponse({"error": str(exc)}, status_code=500)


@app.get("/api/rooms/{room_id}/danmaku/export")
async def api_room_danmaku_export_dates(room_id: str, date_from: str = "", date_to: str = "", asc: int = 1):
    """按日期范围导出弹幕为 CSV。"""
    import csv, io
    db_path = _room_db_path(room_id)
    if not db_path.exists():
        return JSONResponse({"error": "no data"}, status_code=404)
    try:
        from app.storage import StatsStore
        store = StatsStore(str(db_path))
        rows = store.get_danmaku_log(limit=100000, offset=0, date_from=date_from, date_to=date_to, asc=bool(asc))
        store.close()
        buf = io.StringIO()
        w = csv.writer(buf)
        w.writerow(["时间", "用户", "UID", "内容"])
        for r in rows:
            ts = datetime.datetime.fromtimestamp(r["ts"]).strftime("%Y-%m-%d %H:%M:%S") if r.get("ts") else ""
            w.writerow([ts, r.get("uname",""), r.get("uid",""), r.get("content","")])
        fname = f"danmaku_{room_id}"
        if date_from or date_to:
            fname += f"_{date_from or ''}_{date_to or ''}"
        fname += ".csv"
        return Response(
            content=buf.getvalue(),
            media_type="text/csv",
            headers={"Content-Disposition": f'attachment; filename="{fname}"'},
        )
    except Exception as exc:
        return JSONResponse({"error": str(exc)}, status_code=500)


@app.delete("/api/rooms/{room_id}/danmaku/clear")
async def api_room_danmaku_clear_dates(room_id: str, date_from: str = "", date_to: str = ""):
    """按日期范围删除弹幕记录。"""
    db_path = _room_db_path(room_id)
    if not db_path.exists():
        return {"deleted": 0}
    try:
        from app.storage import StatsStore
        store = StatsStore(str(db_path))
        count = store.clear_danmaku_log(date_from=date_from, date_to=date_to)
        store.close()
        return {"deleted": count}
    except Exception as exc:
        return JSONResponse({"error": str(exc)}, status_code=500)


# ══════════════════════════════════════════════════════════════
#  外部 API — 供 AstrBot 插件等第三方查询（Token 认证）
# ══════════════════════════════════════════════════════════════


def _verify_api_token(request: Request) -> bool:
    """验证外部 API Token（支持全局和按房间两种模式）。"""
    token = request.query_params.get("token", "") or request.headers.get("Authorization", "").replace("Bearer ", "")

    # 1. 先检查全局 token
    if _API_TOKEN and token == _API_TOKEN:
        return True

    # 2. 如果传了 room_id，检查该房间的 token
    room_id = request.query_params.get("room_id", "")
    if room_id:
        raw = _load_room_raw_config(room_id)
        web_ui = raw.get("web_ui", {}) or {}
        if web_ui.get("api_enabled") and web_ui.get("api_token") == token:
            return True

    return False


@app.get("/api/external/user_stats")
async def api_external_user_stats(
    request: Request,
    room_id: str = "",
    uid: int = 0,
    period: str = "all",
):
    """
    外部查询接口：获取用户指定时间范围的礼物/盲盒统计。
    
    Args:
        room_id: 房间号（多房间模式必填）
        uid: B站 UID
        period: 时间范围 today|week|month|all
    
    需要 Token 认证：?token=xxx 或 Authorization: Bearer xxx
    """
    if not _verify_api_token(request):
        return JSONResponse({"error": "unauthorized"}, status_code=401)

    if not uid:
        return JSONResponse({"error": "uid is required"}, status_code=400)

    # 确定数据库路径
    if room_id:
        db_path = _room_db_path(room_id)
    else:
        db_path = Path(_DB_PATH)

    if not db_path.exists():
        return JSONResponse({"error": "room data not found"}, status_code=404)

    try:
        now = datetime.datetime.now()
        ts_now = int(now.timestamp())

        if period == "today":
            start_ts = int(now.replace(hour=0, minute=0, second=0, microsecond=0).timestamp())
            end_ts = int(now.replace(hour=23, minute=59, second=59, microsecond=999999).timestamp())
        elif period == "week":
            # 周一为每周第一天
            weekday = now.weekday()
            monday = now - datetime.timedelta(days=weekday)
            start_ts = int(monday.replace(hour=0, minute=0, second=0, microsecond=0).timestamp())
            end_ts = ts_now
        elif period == "month":
            start_ts = int(now.replace(day=1, hour=0, minute=0, second=0, microsecond=0).timestamp())
            end_ts = ts_now
        else:  # all
            start_ts = 0
            end_ts = ts_now

        conn = sqlite3.connect(str(db_path))
        conn.row_factory = sqlite3.Row

        # 通用礼物统计（含盲盒）- 普通礼物的价值从 raw_json.total_coin 提取
        gift_rows = conn.execute(
            """
            SELECT
                COUNT(1) as total_events,
                COALESCE(SUM(gift_num), 0) as total_gift_count,
                COALESCE(SUM(CASE WHEN is_blind_box=0 THEN CAST(json_extract(raw_json, '$.total_coin') AS INTEGER) / 100 ELSE actual_value END), 0) as total_value
            FROM gift_events
            WHERE uid = ? AND ts >= ? AND ts <= ?
            """,
            (uid, start_ts, end_ts),
        ).fetchone()

        # 盲盒统计
        blind_rows = conn.execute(
            """
            SELECT
                COALESCE(SUM(gift_num), 0) as blind_count,
                COALESCE(SUM(blind_box_cost), 0) as blind_cost,
                COALESCE(SUM(actual_value), 0) as blind_actual,
                COALESCE(SUM(profit_value), 0) as blind_profit
            FROM gift_events
            WHERE uid = ? AND ts >= ? AND ts <= ? AND is_blind_box = 1
            """,
            (uid, start_ts, end_ts),
        ).fetchone()

        # 按礼物名称分组统计（普通礼物从 raw_json 提取 total_coin 作为价值，gift_info.img_basic 作为图标）
        gift_detail_rows = conn.execute(
            """
            SELECT g.gift_name,
                   COALESCE(SUM(g.gift_num), 0) as total_num,
                   COALESCE(SUM(CAST(json_extract(g.raw_json, '$.total_coin') AS INTEGER)), 0) / 100 as total_value,
                   COALESCE(
                       (SELECT json_extract(sub.raw_json, '$.gift_info.img_basic')
                        FROM gift_events sub
                        WHERE sub.uid = g.uid AND sub.gift_name = g.gift_name
                          AND sub.is_blind_box = 0 AND sub.ts >= ? AND sub.ts <= ?
                          AND json_extract(sub.raw_json, '$.gift_info.img_basic') IS NOT NULL
                          AND json_extract(sub.raw_json, '$.gift_info.img_basic') != ''
                        ORDER BY sub.ts DESC LIMIT 1),
                   ''
                   ) as gift_icon
            FROM gift_events g
            WHERE g.uid = ? AND g.ts >= ? AND g.ts <= ? AND g.is_blind_box = 0
            GROUP BY g.gift_name
            ORDER BY total_num DESC
            """,
            (start_ts, end_ts, uid, start_ts, end_ts),
        ).fetchall()

        # 盲盒明细（从 raw_json 提取盲盒名称）
        blind_detail_rows = conn.execute(
            """
            SELECT
                json_extract(raw_json, '$.blind_gift.original_gift_name') as box_name,
                json_extract(raw_json, '$.blind_gift.gift_name') as box_gift_name,
                gift_name as item_name,
                COALESCE(SUM(gift_num), 0) as total_num,
                COALESCE(SUM(blind_box_cost), 0) as total_cost,
                COALESCE(SUM(profit_value), 0) as total_profit,
                COALESCE(
                    (SELECT json_extract(sub2.raw_json, '$.gift_info.img_basic')
                     FROM gift_events sub2
                     WHERE sub2.uid = g.uid AND sub2.gift_name = g.gift_name
                       AND sub2.is_blind_box = 1 AND sub2.ts >= ? AND sub2.ts <= ?
                       AND json_extract(sub2.raw_json, '$.gift_info.img_basic') IS NOT NULL
                       AND json_extract(sub2.raw_json, '$.gift_info.img_basic') != ''
                     ORDER BY sub2.ts DESC LIMIT 1),
                    ''
                ) as item_icon
            FROM gift_events g
            WHERE g.uid = ? AND g.ts >= ? AND g.ts <= ? AND g.is_blind_box = 1
            GROUP BY box_name, item_name
            ORDER BY box_name, total_num DESC
            """,
            (start_ts, end_ts, uid, start_ts, end_ts),
        ).fetchall()

        # 弹幕数统计
        danmaku_count = 0
        try:
            dm_row = conn.execute(
                "SELECT COUNT(*) as cnt FROM danmaku_log WHERE uid = ? AND ts >= ? AND ts <= ?",
                (uid, start_ts, end_ts),
            ).fetchone()
            if dm_row:
                danmaku_count = int(dm_row["cnt"])
        except Exception:
            pass  # danmaku_log 表可能不存在

        # 获取用户信息（uname + avatar + guard_level）
        user_row = conn.execute(
            """
            SELECT uname,
                   COALESCE(
                       json_extract(raw_json, '$.sender_uinfo.base.face'),
                       json_extract(raw_json, '$.face'),
                       ''
                   ) as avatar,
                   COALESCE(
                       json_extract(raw_json, '$.sender_uinfo.guard.level'),
                       json_extract(raw_json, '$.sender_uinfo.medal.guard_level'),
                       0
                   ) as guard_level
            FROM gift_events WHERE uid = ? AND raw_json IS NOT NULL AND raw_json != ''
            ORDER BY
                CASE
                    WHEN json_extract(raw_json, '$.sender_uinfo.guard.level') IS NOT NULL AND json_extract(raw_json, '$.sender_uinfo.guard.level') > 0 THEN 0
                    WHEN json_extract(raw_json, '$.sender_uinfo.medal.guard_level') IS NOT NULL AND json_extract(raw_json, '$.sender_uinfo.medal.guard_level') > 0 THEN 1
                    ELSE 2
                END,
                ts DESC
            LIMIT 1
            """,
            (uid,),
        ).fetchone()

        conn.close()

        uname = user_row["uname"] if user_row else f"UID:{uid}"
        avatar = user_row["avatar"] if user_row and user_row["avatar"] else ""
        guard_level = int(user_row["guard_level"]) if user_row and user_row["guard_level"] else 0

        # DB 存储单位是 电池（金瓜子÷100），直接使用
        def _to_battery(v: int) -> int:
            return int(v)

        # 构建礼物名称明细
        gift_details = []
        for r in gift_detail_rows:
            gift_details.append({
                "name": r["gift_name"],
                "count": int(r["total_num"]),
                "value": _to_battery(r["total_value"]),
                "icon": r["gift_icon"] or "",
            })

        blind_details = []
        box_groups: dict[str, dict] = {}
        for r in blind_detail_rows:
            box_name = r["box_name"] or "未知盲盒"
            if box_name not in box_groups:
                box_groups[box_name] = {"items": [], "total_count": 0, "total_cost": 0, "total_profit": 0}
            g = box_groups[box_name]
            g["items"].append({
                "name": r["item_name"],
                "count": int(r["total_num"]),
                "cost": _to_battery(r["total_cost"]),
                "profit": _to_battery(r["total_profit"]),
                "icon": r["item_icon"] or "",
            })
            g["total_count"] += int(r["total_num"])
            g["total_cost"] += int(r["total_cost"])
            g["total_profit"] += int(r["total_profit"])
        for box_name, g in box_groups.items():
            blind_details.append({
                "box_name": box_name,
                "count": g["total_count"],
                "cost": g["total_cost"],
                "profit": g["total_profit"],
                "items": g["items"],
            })

        return {
            "ok": True,
            "uid": uid,
            "uname": uname,
            "avatar": avatar,
            "guard_level": guard_level,
            "period": period,
            "danmaku_count": danmaku_count,
            "gift": {
                "total_events": int(gift_rows["total_events"]),
                "total_gift_count": int(gift_rows["total_gift_count"]),
                "total_value": _to_battery(gift_rows["total_value"]),
                "details": gift_details,
            },
            "blindbox": {
                "count": int(blind_rows["blind_count"]),
                "cost": _to_battery(blind_rows["blind_cost"]),
                "actual": _to_battery(blind_rows["blind_actual"]),
                "profit": _to_battery(blind_rows["blind_profit"]),
                "details": blind_details,
            },
        }
    except Exception as exc:
        logger.exception("external user_stats failed")
        return JSONResponse({"error": str(exc)}, status_code=500)


@app.get("/api/external/api_token")
async def api_external_get_token(request: Request):
    """获取当前 API Key 配置状态和接口地址。"""
    global _API_DOMAIN

    # 优先使用配置的域名，否则自动检测
    if _API_DOMAIN:
        base = _API_DOMAIN.rstrip("/")
    else:
        host = request.headers.get("host", f"{_HTTP_HOST}:{_HTTP_PORT}")
        scheme = request.headers.get("x-forwarded-proto", "http")
        base = f"{scheme}://{host}"
    api_url = f"{base}/api/external/user_stats"

    if _API_TOKEN:
        masked = _API_TOKEN[:4] + "*" * min(len(_API_TOKEN) - 4, 8) + _API_TOKEN[-2:] if len(_API_TOKEN) > 8 else "****"
    else:
        masked = ""
    return {
        "ok": True,
        "has_key": bool(_API_TOKEN),
        "key_masked": masked,
        "api_url": api_url,
        "api_domain": _API_DOMAIN,
    }


@app.post("/api/external/api_token")
async def api_external_generate_key(request: Request):
    """随机生成一个强 API Key 并保存到配置文件。"""
    global _API_TOKEN
    import secrets as _secrets

    # 生成 32 字节随机 hex 密钥（64 位强随机串）
    new_key = _secrets.token_hex(32)

    # 更新内存
    _API_TOKEN = new_key

    # 保存到 config.yaml
    try:
        cfg_path = Path(_CONFIG_YAML_PATH)
        raw = yaml.safe_load(cfg_path.read_text(encoding="utf-8")) or {}
        web_ui = raw.setdefault("web_ui", {})
        web_ui["api_token"] = new_key
        cfg_path.write_text(
            yaml.dump(raw, default_flow_style=False, allow_unicode=True),
            encoding="utf-8",
        )
        logger.info("api_token saved to %s", cfg_path)
    except Exception as exc:
        logger.warning("failed to save api_token: %s", exc)
        return JSONResponse({"error": f"保存失败: {exc}"}, status_code=500)

    masked = new_key[:6] + "*" * (len(new_key) - 10) + new_key[-4:] if len(new_key) > 12 else "****"
    return {
        "ok": True,
        "message": "新 API Key 已生成并生效",
        "key_masked": masked,
        "full_key": new_key,
    }


@app.post("/api/external/clear_key")
async def api_external_clear_key():
    """清空 API Key（禁用外部查询）。"""
    global _API_TOKEN

    _API_TOKEN = ""
    try:
        cfg_path = Path(_CONFIG_YAML_PATH)
        raw = yaml.safe_load(cfg_path.read_text(encoding="utf-8")) or {}
        web_ui = raw.setdefault("web_ui", {})
        web_ui["api_token"] = ""
        cfg_path.write_text(
            yaml.dump(raw, default_flow_style=False, allow_unicode=True),
            encoding="utf-8",
        )
        logger.info("api_token cleared")
    except Exception as exc:
        logger.warning("failed to clear api_token: %s", exc)
        return JSONResponse({"error": f"清空失败: {exc}"}, status_code=500)

    return {"ok": True, "message": "API Key 已清空，外部查询已禁用"}


@app.get("/api/external/ranking")
async def api_external_ranking(
    request: Request,
    room_id: str = "",
    period: str = "all",
    gift_type: str = "all",
    limit: int = 20,
):
    """
    外部查询接口：获取房间的送礼排行。
    
    Args:
        room_id: 房间号
        period: today|week|month|all
        gift_type: all|gift|blindbox
        limit: 返回条数（默认20，最大100）
    
    需要 Token 认证：?token=xxx
    """
    if not _verify_api_token(request):
        return JSONResponse({"error": "unauthorized"}, status_code=401)
    if not room_id:
        return JSONResponse({"error": "room_id is required"}, status_code=400)

    db_path = _room_db_path(room_id)
    if not db_path.exists():
        return JSONResponse({"error": "room data not found"}, status_code=404)

    try:
        now = datetime.datetime.now()
        ts_now = int(now.timestamp())
        if period == "today":
            start_ts = int(now.replace(hour=0, minute=0, second=0, microsecond=0).timestamp())
            end_ts = ts_now
        elif period == "week":
            weekday = now.weekday()
            monday = now - datetime.timedelta(days=weekday)
            start_ts = int(monday.replace(hour=0, minute=0, second=0, microsecond=0).timestamp())
            end_ts = ts_now
        elif period == "month":
            start_ts = int(now.replace(day=1, hour=0, minute=0, second=0, microsecond=0).timestamp())
            end_ts = ts_now
        else:
            start_ts = 0
            end_ts = ts_now

        limit = min(max(limit, 1), 100)

        conn = sqlite3.connect(str(db_path))
        cur = conn.cursor()

        where = "ts >= ? AND ts <= ?"
        params: list = [start_ts, end_ts]
        if gift_type == "gift":
            where += " AND is_blind_box = 0"
        elif gift_type == "blindbox":
            where += " AND is_blind_box = 1"

        cur.execute(f"""
            SELECT uid, uname,
                   COALESCE(SUM(gift_num), 0) as total_count,
                   COALESCE(SUM(CASE WHEN is_blind_box=0 THEN CAST(json_extract(raw_json, '$.total_coin') AS INTEGER) / 100 ELSE actual_value END), 0) as total_value,
                   COALESCE(SUM(profit_value), 0) as total_profit
            FROM gift_events
            WHERE {where}
            GROUP BY uid
            ORDER BY total_value DESC
            LIMIT ?
        """, params + [limit])
        rows = cur.fetchall()
        conn.close()

        ranking = []
        for r in rows:
            ranking.append({
                "uid": int(r[0]),
                "uname": str(r[1]),
                "count": int(r[2]),
                "value": int(r[3]),
                "profit": int(r[4]),
            })
        return {"ok": True, "ranking": ranking, "total": len(ranking)}
    except Exception as exc:
        logger.exception("external ranking failed")
        return JSONResponse({"error": str(exc)}, status_code=500)


@app.get("/api/external/room_stats")
async def api_external_room_stats(
    request: Request,
    room_id: str = "",
    period: str = "all",
):
    """
    外部查询接口：获取房间整体统计数据。
    
    Args:
        room_id: 房间号
        period: today|week|month|all
    
    需要 Token 认证：?token=xxx
    """
    if not _verify_api_token(request):
        return JSONResponse({"error": "unauthorized"}, status_code=401)
    if not room_id:
        return JSONResponse({"error": "room_id is required"}, status_code=400)

    db_path = _room_db_path(room_id)
    if not db_path.exists():
        return JSONResponse({"error": "room data not found"}, status_code=404)

    try:
        now = datetime.datetime.now()
        ts_now = int(now.timestamp())
        if period == "today":
            start_ts = int(now.replace(hour=0, minute=0, second=0, microsecond=0).timestamp())
            end_ts = ts_now
        elif period == "week":
            weekday = now.weekday()
            monday = now - datetime.timedelta(days=weekday)
            start_ts = int(monday.replace(hour=0, minute=0, second=0, microsecond=0).timestamp())
            end_ts = ts_now
        elif period == "month":
            start_ts = int(now.replace(day=1, hour=0, minute=0, second=0, microsecond=0).timestamp())
            end_ts = ts_now
        else:
            start_ts = 0
            end_ts = ts_now

        conn = sqlite3.connect(str(db_path))
        conn.row_factory = sqlite3.Row

        # 总览
        overview = conn.execute("""
            SELECT
                COUNT(DISTINCT uid) as total_users,
                COUNT(1) as total_events,
                COALESCE(SUM(gift_num), 0) as total_gifts,
                COALESCE(SUM(CASE WHEN is_blind_box=0 THEN CAST(json_extract(raw_json, '$.total_coin') AS INTEGER) / 100 ELSE actual_value END), 0) as total_value,
                COALESCE(SUM(CASE WHEN is_blind_box=1 THEN 1 ELSE 0 END), 0) as blind_users,
                COALESCE(SUM(CASE WHEN is_blind_box=1 THEN gift_num ELSE 0 END), 0) as blind_count,
                COALESCE(SUM(CASE WHEN is_blind_box=1 THEN blind_box_cost ELSE 0 END), 0) as blind_cost,
                COALESCE(SUM(CASE WHEN is_blind_box=1 THEN profit_value ELSE 0 END), 0) as blind_profit
            FROM gift_events
            WHERE ts >= ? AND ts <= ?
        """, (start_ts, end_ts)).fetchone()

        conn.close()

        return {
            "ok": True,
            "period": period,
            "overview": {
                "total_users": int(overview["total_users"]),
                "total_events": int(overview["total_events"]),
                "total_gifts": int(overview["total_gifts"]),
                "total_value": int(overview["total_value"]),
                "blind_users": int(overview["blind_users"]),
                "blind_count": int(overview["blind_count"]),
                "blind_cost": int(overview["blind_cost"]),
                "blind_profit": int(overview["blind_profit"]),
            },
        }
    except Exception as exc:
        logger.exception("external room_stats failed")
        return JSONResponse({"error": str(exc)}, status_code=500)


@app.post("/api/external/api_domain")
async def api_external_save_domain(request: Request):
    """保存 API 外部域名到配置文件并更新内存。"""
    global _API_DOMAIN
    try:
        body = await request.json()
    except Exception:
        return JSONResponse({"error": "bad request"}, status_code=400)

    domain = str(body.get("domain", "")).strip().rstrip("/")
    _API_DOMAIN = domain

    try:
        cfg_path = Path(_CONFIG_YAML_PATH)
        raw = yaml.safe_load(cfg_path.read_text(encoding="utf-8")) or {}
        web_ui = raw.setdefault("web_ui", {})
        web_ui["api_domain"] = domain
        cfg_path.write_text(
            yaml.dump(raw, default_flow_style=False, allow_unicode=True),
            encoding="utf-8",
        )
        logger.info("api_domain saved: %s", domain or "(empty, auto-detect)")
    except Exception as exc:
        logger.warning("failed to save api_domain: %s", exc)
        return JSONResponse({"error": f"保存失败: {exc}"}, status_code=500)

    return {"ok": True, "message": "外部域名已保存，即时生效", "api_domain": domain}


@app.post("/api/external/restart")
async def api_external_restart():
    """重启 WebUI 服务（让配置完全生效）。"""
    import sys as _sys
    import os as _os
    logger.info("WebUI restart requested via external API config")

    # 异步启动重启：先返回响应，再退出进程（由启动脚本自动重启）
    async def _delayed_restart():
        await asyncio.sleep(1)
        _os.execl(_sys.executable, _sys.executable, *[_sys.argv[0]])

    asyncio.create_task(_delayed_restart())
    return {"ok": True, "message": "正在重启 WebUI..."}


# ══════════════════════════════════════════════════════════════
#  HTML
# ══════════════════════════════════════════════════════════════════

INDEX_HTML = r"""<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Ayabot 直播间机器人</title>
<link rel="icon" href="/favicon.ico" sizes="any">
<link rel="icon" type="image/png" sizes="192x192" href="/icon-192.png">
<link rel="apple-touch-icon" href="/icon-192.png">
<meta name="theme-color" content="#2563eb">
<script src="https://cdn.tailwindcss.com"></script>
<script src="https://unpkg.com/vue@3/dist/vue.global.prod.js"></script>
<script src="https://cdn.jsdelivr.net/npm/chart.js@4"></script>
<script src="https://unpkg.com/modern-screenshot@4.7.0/dist/index.js"></script>
<script>
// ── 夜间模式：页面加载前立即应用，避免闪烁 ──
(function () {
  try {
    if (localStorage.getItem('ayabot_dark') === '1') {
      document.documentElement.classList.add('dark');
    }
  } catch (e) { /* 无痕模式忽略 */ }
})();
</script>
<style>
#app { background: linear-gradient(160deg, #f8fafc 0%, #eef2ff 40%, #f0f9ff 100%); min-height: 100vh; }
/* ── 礼物卡片（毛玻璃 + 主题色渐变）── */
.bili-card {
    border-radius: 12px;
    padding: 10px 14px;
    display: flex;
    align-items: center;
    gap: 12px;
    color: #fff;
    font-family: "Microsoft YaHei", "PingFang SC", sans-serif;
    box-shadow: 0 3px 10px rgba(0,0,0,0.15);
    margin-bottom: 8px;
    position: relative;
    min-height: 56px;
    border: 1px solid rgba(255,255,255,0.08);
}
/* 毛玻璃：顶部高光 */
.bili-card::after {
    content: '';
    position: absolute;
    top: 0; left: 0; right: 0;
    height: 48%;
    border-radius: 12px 12px 0 0;
    background: linear-gradient(180deg, rgba(255,255,255,0.10) 0%, transparent 100%);
    pointer-events: none;
}
.bili-card > * { position: relative; z-index: 1; }

/* ── 身份底色（半透明主题色 + 毛玻璃质感）── */
.bg-default { background: linear-gradient(135deg, #374151 0%, #1f2937 100%); }
.bg-captain { background: linear-gradient(135deg, #1e3a5f 0%, #1a2d4a 100%); }
.bg-commander { background: linear-gradient(135deg, #3b1f6e 0%, #2d1550 100%); }
.bg-governor { background: linear-gradient(135deg, #5c3a0e 0%, #3d2608 100%); }

.avatar-wrap {
    position: relative;
    width: 52px;
    height: 52px;
    flex-shrink: 0;
    display: flex;
    align-items: center;
    justify-content: center;
}
.avatar-wrap img.face {
    width: 44px; height: 44px;
    border-radius: 50%;
    border: 2px solid rgba(255,255,255,0.85);
    object-fit: cover;
    display: block;
    max-width: none !important;
    position: relative;
    z-index: 1;
}
.avatar-wrap img.frame-img {
    position: absolute;
    width: 60px; height: 60px;
    top: -4px; left: -4px;
    pointer-events: none;
    z-index: 2;
    max-width: none !important;
}

/* ── 多列布局（水平可滚动，居中）── */
.capture-grid {
    display: flex;
    gap: 16px;
    align-items: flex-start;
}
.capture-col {
    min-width: 0;
    flex-shrink: 0;
}
.capture-inner {
    display: inline-block;
    margin: 0 auto;
    text-align: left;
}
#capture {
    text-align: center;
}

.gift-icon {
    width: 38px; height: 38px;
    flex-shrink: 0;
    object-fit: contain;
    border-radius: 6px;
}
.gift-icon.mini {
    width: 16px; height: 16px;
    border-radius: 4px;
    flex-shrink: 0;
}
.gift-value {
    background: rgba(255,255,255,0.2);
    border-radius: 8px;
    padding: 1px 8px;
    font-size: 11px;
    font-weight: 600;
    white-space: nowrap;
    display: inline-block;
    line-height: 1.5;
    vertical-align: middle;
}
.gift-time {
    font-size: 10px;
    color: rgba(255,255,255,0.65);
    white-space: nowrap;
    display: inline-block;
    vertical-align: middle;
}

/* ═══════ 精美导出卡片：日间浅色主题（跟随页面主题切换）═══════ */
/* 默认 .bili-card 是深色设计；html 非 .dark 时切换为浅色玻璃风（截图克隆同样生效） */
html:not(.dark) .bili-card {
    color: #334155;
    border: 1px solid rgba(148,163,184,0.22);
    box-shadow: 0 3px 12px rgba(56,48,130,0.10), 0 1px 4px rgba(148,163,184,0.08);
}
html:not(.dark) .bili-card::after {
    background: linear-gradient(180deg, rgba(255,255,255,0.55) 0%, transparent 100%);
}
/* 身份底色 → 日间浅色柔和渐变 */
html:not(.dark) .bg-default { background: linear-gradient(135deg, #eef2f7 0%, #f8fafc 100%); }
html:not(.dark) .bg-captain { background: linear-gradient(135deg, #dbeafe 0%, #eff6ff 100%); }
html:not(.dark) .bg-commander { background: linear-gradient(135deg, #ede9fe 0%, #f5f3ff 100%); }
html:not(.dark) .bg-governor { background: linear-gradient(135deg, #fef3c7 0%, #fefce8 100%); }
/* 卡片内文字/边框工具类 → 日间深色 */
html:not(.dark) .bili-card .text-white\/80 { color: rgba(51,65,85,0.82) !important; }
html:not(.dark) .bili-card .text-white\/50 { color: rgba(51,65,85,0.5) !important; }
html:not(.dark) .bili-card .border-white\/10 { border-color: rgba(148,163,184,0.25) !important; }
/* 头像白边 → 浅灰边 */
html:not(.dark) .avatar-wrap img.face { border: 2px solid rgba(255,255,255,0.95); box-shadow: 0 0 0 1px rgba(148,163,184,0.25); }
/* gift-time 时间文字深色化 */
html:not(.dark) .bili-card .gift-time,
html:not(.dark) .gift-time { color: rgba(100,116,139,0.7) !important; }
/* 礼物总额徽章金色在浅色卡上加深描边，保持可读 */
html:not(.dark) .bili-card .gift-value { box-shadow: 0 1px 2px rgba(180,140,20,0.18); }

/* ═────── 全局现代化覆盖（浅色极简玻璃拟态）─────── */
#app input[class*="border"], #app textarea[class*="border"], #app select[class*="border"] {
    border-radius: 0.75rem !important;
    border-color: rgba(226,232,240,1) !important;
    box-shadow: 0 1px 2px rgba(148,163,184,0.08) !important;
    transition: border-color .15s ease, box-shadow .15s ease;
    background-color: rgba(255,255,255,0.7) !important;
}
#app input[class*="border"]:focus, #app textarea[class*="border"]:focus, #app select[class*="border"]:focus {
    border-color: #818cf8 !important;
    box-shadow: 0 0 0 3px rgba(129,140,248,0.15) !important;
    outline: none;
}
#app button[class*="bg-green"], #app button[class*="bg-blue"], #app button[class*="bg-red"],
#app button[class*="bg-indigo"], #app button[class*="bg-gray"], #app button[class*="bg-slate"] {
    border-radius: 0.75rem !important;
    font-weight: 500;
}
#app div[class*="bg-white"][class*="rounded"], #app div[class*="border rounded-lg"] { border-radius: 1rem !important; }
#app .bg-white.shadow { box-shadow: 0 4px 16px rgba(99,102,241,0.08) !important; }
#app div[class*="fixed"][class*="bg-black"] { backdrop-filter: blur(6px); }
#app .bg-white.rounded-xl.shadow-sm {
    background-color: rgba(255,255,255,0.72) !important;
    backdrop-filter: blur(12px);
    -webkit-backdrop-filter: blur(12px);
    border: 1px solid rgba(255,255,255,0.9);
    box-shadow: 0 8px 24px rgba(56,48,130,0.08), 0 2px 6px rgba(148,163,184,0.06) !important;
}
#app .bg-gray-50.rounded-lg {
    background-color: rgba(248,250,252,0.7) !important;
    backdrop-filter: blur(8px);
    border-radius: 1rem !important;
    border-color: rgba(226,232,240,0.8) !important;
}
#app button[class*="bg-blue-500"] { background-image: linear-gradient(to right, #6366f1, #0ea5e9) !important; background-color: transparent !important; }
#app button[class*="bg-green-500"] { background-image: linear-gradient(to right, #10b981, #14b8a6) !important; background-color: transparent !important; box-shadow: 0 4px 12px rgba(16,185,129,0.25) !important; }
#app button[class*="bg-gray-200"] { background-color: rgba(226,232,240,0.8) !important; }
#app h2, #app h3 { letter-spacing: -0.01em; }

/* 房间子页面精致化 */
.gb-tabs { background: rgba(255,255,255,0.5); backdrop-filter: blur(10px); -webkit-backdrop-filter: blur(10px); border: 1px solid rgba(255,255,255,0.9); }
.gb-tab { transition: all .18s ease; font-weight: 500; }
.gb-tab:not(.active):hover { background: rgba(226,232,240,0.5); color: #4338ca; }
.gb-tab.active { background-image: linear-gradient(120deg, #6366f1, #0ea5e9); color: #fff !important; box-shadow: 0 4px 12px rgba(99,102,241,0.35); }
.gb-table { border-collapse: separate; border-spacing: 0; }
.gb-table thead th { background: rgba(238,242,255,0.85) !important; backdrop-filter: blur(6px); font-weight: 600; color: #475569; letter-spacing: 0.01em; position: sticky; top: 0; z-index: 5; }
.gb-table thead th:first-child { border-top-left-radius: 0.75rem; }
.gb-table thead th:last-child { border-top-right-radius: 0.75rem; }
.gb-table tbody tr { transition: background-color .15s ease; }
.gb-table tbody tr:nth-child(even) { background: rgba(248,250,252,0.5); }
.gb-table tbody tr:hover { background: rgba(238,242,255,0.7); }
.gb-table tbody tr:last-child td:first-child { border-bottom-left-radius: 0.75rem; }
.gb-table tbody tr:last-child td:last-child { border-bottom-right-radius: 0.75rem; }
.rank-medal { display: inline-flex; align-items: center; justify-content: center; width: 1.5rem; height: 1.5rem; border-radius: 9999px; font-weight: 700; font-size: 0.75rem; color: #fff; }
.rank-1 { background: linear-gradient(135deg, #f6b73c, #e8a020); box-shadow: 0 2px 6px rgba(245,158,11,0.4); }
.rank-2 { background: linear-gradient(135deg, #cbd5e1, #94a3b8); box-shadow: 0 2px 6px rgba(148,163,184,0.4); }
.rank-3 { background: linear-gradient(135deg, #f0a18a, #d97a4f); box-shadow: 0 2px 6px rgba(217,122,79,0.4); }
.rank-plain { display: inline-flex; align-items: center; justify-content: center; min-width: 1.5rem; padding: 0 0.25rem; height: 1.5rem; border-radius: 9999px; background: rgba(226,232,240,0.6); color: #64748b; font-weight: 600; font-size: 0.75rem; }
.gb-card-title { position: relative; padding-left: 0.85rem; }
.gb-card-title::before { content: ''; position: absolute; left: 0; top: 50%; transform: translateY(-50%); width: 4px; height: 1.1em; border-radius: 2px; background-image: linear-gradient(180deg, #6366f1, #0ea5e9); }

/* 房间列表卡片（现代玻璃卡片） */
.room-card {
    backdrop-filter: blur(14px);
    -webkit-backdrop-filter: blur(14px);
    border: 1px solid rgba(255,255,255,0.9);
    box-shadow: 0 2px 8px rgba(148,163,184,0.08);
    border-radius: 1.25rem !important;
    transition: transform .18s ease, box-shadow .18s ease, border-color .18s ease;
}
.room-card.running { background: linear-gradient(135deg, rgba(240,253,244,0.8), rgba(236,254,255,0.6)); border-color: rgba(134,239,172,0.6); }
.room-card.stopped { background: rgba(255,255,255,0.6); }
.room-card:hover {
    transform: translateY(-2px);
    box-shadow: 0 12px 28px rgba(56,48,130,0.12), 0 4px 10px rgba(148,163,184,0.10);
    border-color: rgba(129,140,248,0.5);
}
.room-card .status-dot { box-shadow: 0 0 0 3px rgba(34,197,94,0.18); }
.room-card .room-name { letter-spacing: -0.01em; }
.room-card .status-badge {
    display: inline-flex; align-items: center;
    padding: 2px 10px; border-radius: 9999px;
    font-size: 11px; font-weight: 600; letter-spacing: 0.01em;
}
.room-card .status-badge.on { background: rgba(220,252,231,0.9); color: #15803d; }
.room-card .status-badge.off { background: rgba(241,245,249,0.9); color: #64748b; }
.btn-soft { transition: all .16s ease; backdrop-filter: blur(6px); }
.btn-soft:hover { transform: translateY(-1px); box-shadow: 0 4px 10px rgba(148,163,184,0.18); }

/* 新建房间表单（玻璃卡片） */
.create-form {
    background: linear-gradient(135deg, rgba(248,250,252,0.75), rgba(255,255,255,0.5));
    backdrop-filter: blur(12px);
    -webkit-backdrop-filter: blur(12px);
    border: 1px solid rgba(226,232,240,0.9);
    border-radius: 1.25rem !important;
    box-shadow: inset 0 1px 0 rgba(255,255,255,0.8);
}
html.dark .create-form {
    background: linear-gradient(135deg, rgba(30,41,59,0.6), rgba(15,23,42,0.5));
    border-color: rgba(71,85,105,0.3);
}
html.dark .create-form input, html.dark .create-form select {
    background-color: rgba(15,23,42,0.6) !important;
    border-color: rgba(71,85,105,0.5) !important;
    color: #e2e8f0 !important;
}

/* 主页面标题（柔和渐变衬底，不挤压 emoji） */
.page-title { display: inline-flex; align-items: center; gap: 0.4rem; padding: 0.35rem 0.85rem; border-radius: 0.75rem; background: linear-gradient(120deg, rgba(99,102,241,0.10), rgba(14,165,233,0.06)); border: 1px solid rgba(129,140,248,0.18); font-weight: 700; letter-spacing: -0.01em; color: #334155; }
html.dark .page-title { color: #e2e8f0; background: linear-gradient(120deg, rgba(99,102,241,0.22), rgba(14,165,233,0.10)); border-color: rgba(129,140,248,0.25); }

/* 夜间模式房间卡片 */
html.dark .room-card.running { background: linear-gradient(135deg, rgba(20,83,45,0.4), rgba(8,51,68,0.4)); border-color: rgba(74,222,128,0.25); }
html.dark .room-card.stopped { background: rgba(30,41,59,0.5); }
html.dark .room-card .room-name { color: #e2e8f0; }
html.dark .room-card .status-badge.on { background: rgba(22,101,52,0.5); color: #86efac; }
html.dark .room-card .status-badge.off { background: rgba(51,65,85,0.6); color: #94a3b8; }
html.dark .btn-soft { background-color: rgba(30,41,59,0.6) !important; border-color: rgba(71,85,105,0.3); }
html.dark .btn-soft.bg-green-50 { background-color: rgba(22,101,52,0.35) !important; color: #86efac; }
html.dark .btn-soft.bg-yellow-50 { background-color: rgba(113,63,18,0.35) !important; color: #fcd34d; }
html.dark .btn-soft.bg-red-50 { background-color: rgba(136,19,55,0.3) !important; color: #fca5a5; }

/* 夜间模式（.dark 触发） */
html.dark body { background-color: #0b1120; }
html.dark #app { background: linear-gradient(160deg, #0b1120 0%, #0f1b33 45%, #0a1428 100%); }
html.dark .from-slate-50 { --tw-gradient-from: #0f172a; --tw-gradient-to: #1e293b; }
html.dark .via-white { --tw-gradient-stops: var(--tw-gradient-from), #111c2e, var(--tw-gradient-to); }
html.dark .to-indigo-50\/70 { --tw-gradient-to: rgba(49,46,129,0.5); }
html.dark .bg-slate-50 { background-color: #0f172a; }
html.dark .text-slate-800 { color: #e2e8f0; }
html.dark .text-slate-500, html.dark .text-slate-400, html.dark .text-gray-500,
html.dark .text-gray-400, html.dark .text-gray-600, html.dark .text-gray-300 { color: #94a3b8; }
html.dark .text-gray-700, html.dark .text-gray-800 { color: #e2e8f0; }
html.dark .bg-indigo-200\/40 { background-color: rgba(67,56,202,0.25); }
html.dark .bg-sky-200\/40 { background-color: rgba(14,116,144,0.25); }
html.dark .bg-white\/70, html.dark .bg-white\/60, html.dark .bg-white {
    background-color: rgba(30,41,59,0.55) !important;
    backdrop-filter: blur(14px);
    -webkit-backdrop-filter: blur(14px);
}
html.dark .bg-white.rounded-xl.shadow-sm { background-color: rgba(30,41,59,0.55) !important; border-color: rgba(100,116,139,0.25); box-shadow: 0 8px 24px rgba(0,0,0,0.35) !important; }
html.dark .bg-gray-50.rounded-lg { background-color: rgba(30,41,59,0.6) !important; border-color: rgba(100,116,139,0.2) !important; }
html.dark .bg-gray-50 { background-color: rgba(30,41,59,0.7) !important; }
html.dark header { background-color: rgba(15,23,42,0.7) !important; border-color: rgba(71,85,105,0.3) !important; box-shadow: 0 4px 20px rgba(0,0,0,0.4) !important; }
html.dark input[class*="border"], html.dark textarea[class*="border"], html.dark select[class*="border"] {
    background-color: rgba(15,23,42,0.6) !important; border-color: rgba(71,85,105,0.5) !important; color: #e2e8f0 !important;
}
html.dark input::placeholder, html.dark textarea::placeholder { color: #64748b !important; }
html.dark .gb-table thead th { background-color: rgba(30,41,59,0.9) !important; color: #cbd5e1 !important; }
html.dark .gb-table tbody tr:nth-child(even) { background: rgba(30,41,59,0.35); }
html.dark .gb-table tbody tr:hover { background: rgba(67,56,202,0.18) !important; }
html.dark .border-t { border-color: rgba(71,85,105,0.2) !important; }
html.dark .gb-tabs { background: rgba(30,41,59,0.6); border-color: rgba(71,85,105,0.3); }
html.dark .gb-tab:not(.active) { color: #94a3b8; }
html.dark .gb-tab:not(.active):hover { background: rgba(71,85,105,0.3); color: #e0e7ff; }
html.dark div[class*="fixed"][class*="bg-black"] { background-color: rgba(0,0,0,0.6); }
html.dark #app div[class*="bg-white"][class*="rounded"] { background-color: #1e293b !important; color: #e2e8f0; }
html.dark .bg-gray-900 { background-color: #0b1220 !important; border: 1px solid #1e293b; }
html.dark button[class*="bg-red-50"], html.dark button[class*="bg-amber-50"],
html.dark div[class*="bg-red-50"], html.dark div[class*="bg-amber-50"], html.dark div[class*="bg-yellow-50"] {
    background-color: rgba(30,41,59,0.6) !important; border-color: rgba(71,85,105,0.25) !important;
}
html.dark .text-red-500 { color: #f87171 !important; }
html.dark .text-red-600 { color: #fca5a5 !important; }
html.dark .text-amber-700, html.dark .text-yellow-700 { color: #fbbf24 !important; }
html.dark .text-green-600 { color: #4ade80 !important; }

/* ═────── 弹窗精致化（玻璃拟态卡片，共享覆盖全部 12 处弹窗）────── */
.bg-white.rounded-xl.shadow-lg {
    border-radius: 1.25rem !important;
    border: 1px solid rgba(255,255,255,0.9) !important;
    background-color: rgba(255,255,255,0.82) !important;
    backdrop-filter: blur(20px) saturate(140%);
    -webkit-backdrop-filter: blur(20px) saturate(140%);
    box-shadow: 0 20px 50px rgba(56,48,130,0.18), 0 4px 16px rgba(148,163,184,0.10) !important;
    animation: modalPop .18s ease-out;
}
@keyframes modalPop {
    from { opacity: 0; transform: translateY(8px) scale(.98); }
    to   { opacity: 1; transform: translateY(0) scale(1); }
}
/* 弹窗顶/底分隔线柔和 */
.bg-white.rounded-xl.shadow-lg .border-b { border-color: rgba(148,163,184,0.18) !important; }
.bg-white.rounded-xl.shadow-lg .border-t { border-color: rgba(148,163,184,0.18) !important; }
/* 弹窗内条目块（bg-gray-50）统一浅玻璃 */
.bg-white.rounded-xl.shadow-lg .bg-gray-50 { background-color: rgba(248,250,252,0.65) !important; border-radius: 0.85rem !important; border-color: rgba(226,232,240,0.7) !important; }
/* 弹窗滚动条美化 */
.bg-white.rounded-xl.shadow-lg ::-webkit-scrollbar { width: 8px; height: 8px; }
.bg-white.rounded-xl.shadow-lg ::-webkit-scrollbar-thumb { background: rgba(148,163,184,0.35); border-radius: 9999px; }
.bg-white.rounded-xl.shadow-lg ::-webkit-scrollbar-thumb:hover { background: rgba(99,102,241,0.5); }
.bg-white.rounded-xl.shadow-lg ::-webkit-scrollbar-track { background: transparent; }
/* 弹窗内按钮统一圆角 */
.bg-white.rounded-xl.shadow-lg button { border-radius: 0.6rem !important; }
/* 弹窗标题区字间距 */
.bg-white.rounded-xl.shadow-lg h3 { letter-spacing: -0.01em; }
/* 夜间模式弹窗玻璃 */
html.dark .bg-white.rounded-xl.shadow-lg {
    background-color: rgba(17,24,39,0.85) !important;
    border-color: rgba(71,85,105,0.35) !important;
    box-shadow: 0 20px 50px rgba(0,0,0,0.55) !important;
}
html.dark .bg-white.rounded-xl.shadow-lg .bg-gray-50 { background-color: rgba(30,41,59,0.5) !important; border-color: rgba(71,85,105,0.25) !important; }
html.dark .bg-white.rounded-xl.shadow-lg input[class*="border"], html.dark .bg-white.rounded-xl.shadow-lg select[class*="border"], html.dark .bg-white.rounded-xl.shadow-lg textarea[class*="border"] {
    background-color: rgba(15,23,42,0.6) !important; border-color: rgba(71,85,105,0.5) !important; color: #e2e8f0 !important;
}
/* 精美导出日期选择 日历弹窗（Teleport 到 body，.cal-pop）夜间适配 */
html.dark .cal-pop { background-color: #101a2c !important; border-color: rgba(71,85,105,0.4) !important; box-shadow: 0 20px 50px rgba(0,0,0,0.6) !important; }
html.dark .cal-pop .text-sm.font-bold { color: #e2e8f0 !important; }
html.dark .cal-pop button[class*="hover:bg-gray-100"] { color: #cbd5e1 !important; }
html.dark .cal-pop .bg-blue-50 { background-color: rgba(59,130,246,0.18) !important; color: #93c5fd !important; }
html.dark .cal-pop .bg-gray-50 { background-color: rgba(51,65,85,0.45) !important; color: #cbd5e1 !important; border-color: rgba(71,85,105,0.3) !important; }
html.dark .cal-pop .bg-green-50 { background-color: rgba(22,101,52,0.35) !important; color: #86efac !important; }
html.dark .cal-pop .text-gray-400 { color: #94a3b8 !important; }
html.dark .cal-pop .text-gray-300 { color: #64748b !important; }
html.dark .cal-pop .bg-blue-100 { background-color: rgba(30,58,138,0.4) !important; color: #bfdbfe !important; }
html.dark .cal-pop .bg-blue-100:hover { background-color: rgba(30,58,138,0.6) !important; }
html.dark .cal-pop .bg-blue-500 { background-color: #2563eb !important; color: #fff !important; }
html.dark .cal-pop .bg-blue-500:hover { background-color: #2563eb !important; }
/* ── 弹幕记录工具区分组卡片（dm-toolbar）夜间适配 ── */
html.dark .dm-toolbar { background-color: rgba(30,41,59,0.6) !important; border-color: rgba(71,85,105,0.3) !important; }
html.dark .dm-toolbar .divide-y > * + * { border-color: rgba(71,85,105,0.25) !important; }
/* ── 帮助页（使用指南）夜间适配 ── */
html.dark .help-page { background-color: rgba(30,41,59,0.55) !important; border-color: rgba(100,116,139,0.25); box-shadow: 0 8px 24px rgba(0,0,0,0.35) !important; }
html.dark .help-page .from-pink-50, html.dark .help-page .from-sky-50 { background-image: linear-gradient(120deg, rgba(244,114,182,0.12), rgba(56,189,248,0.10)) !important; border-color: rgba(244,114,182,0.3) !important; }
html.dark .help-page .text-gray-800 { color: #e2e8f0 !important; }
html.dark .help-page .text-gray-500 { color: #94a3b8 !important; }
html.dark .help-page .text-gray-600 { color: #cbd5e1 !important; }
html.dark .help-page .text-gray-400 { color: #94a3b8 !important; }
html.dark .help-page .bg-blue-50 { background-color: rgba(59,130,246,0.15) !important; border-color: rgba(59,130,246,0.3) !important; }
html.dark .help-page .text-blue-700 { color: #93c5fd !important; }
html.dark .help-page .text-blue-600, html.dark .help-page .text-blue-500 { color: #93c5fd !important; }
html.dark .help-page code.bg-indigo-50 { background-color: rgba(99,102,241,0.22) !important; color: #c7d2fe !important; }
html.dark .help-page .border-slate-100 { border-color: rgba(71,85,105,0.25) !important; }
html.dark .help-page .text-slate-700 { color: #e2e8f0 !important; }
html.dark .help-page .hover\:bg-blue-100:hover { background-color: rgba(59,130,246,0.22) !important; }
html.dark .dm-toolbar-row { border-color: rgba(71,85,105,0.25) !important; }
html.dark .dm-toolbar .dm-toolbar-label { color: #94a3b8 !important; }
html.dark .dm-toolbar .text-xs.text-gray-400 { color: #94a3b8 !important; }
html.dark .dm-toolbar div[class*="border-l"] { border-color: rgba(71,85,105,0.3) !important; }
html.dark .dm-toolbar label { color: #cbd5e1 !important; }
/* 工具区通用控件（按钮/输入/下拉）夜间配色 */
html.dark .dm-toolbar input[class*="border"], html.dark .dm-toolbar select[class*="border"], html.dark .dm-toolbar button[class*="border"] {
    background-color: rgba(15,23,42,0.7) !important; border-color: rgba(71,85,105,0.45) !important; color: #e2e8f0 !important;
}
html.dark .dm-toolbar button[class*="border"]:hover { background-color: rgba(51,65,85,0.6) !important; }
html.dark .dm-toolbar input::placeholder { color: #64748b !important; }
/* 下拉框文字与背景强对比（日间/夜间），修复“颜色和字体几乎一样看不清” */
.dm-toolbar select[class*="border"] { color: #1e293b !important; background-color: #ffffff !important; }
.dm-toolbar select[class*="border"] option { color: #1e293b; background-color: #ffffff; }
html.dark .dm-toolbar select[class*="border"] { color: #f1f5f9 !important; background-color: #1e293b !important; }
html.dark .dm-toolbar select[class*="border"] option { color: #f1f5f9; background-color: #1e293b; }
/* ── 弹幕记录整体美化（日间玻璃拟态） ── */
/* 工具区分组标签：渐变胶囊 + 柔光 */
.dm-toolbar-label {
    display: inline-flex; align-items: center; justify-content: center;
    height: 1.6rem; width: 3.4rem; flex: 0 0 3.4rem;
    border-radius: 0.55rem; font-weight: 600; color: #ffffff !important;
    font-size: 0.75rem; letter-spacing: 0.02em;
    background-image: linear-gradient(135deg, #6366f1, #8b5cf6);
    box-shadow: 0 2px 8px rgba(99,102,241,0.28);
    margin: 0.25rem 0; line-height: 1.6rem;
}
/* 工具区行间距与包裹负边距对齐 */
.dm-toolbar-row { align-items: center !important; }
/* 工具区容器精致玻璃 */
.dm-toolbar {
    background: linear-gradient(180deg, rgba(255,255,255,0.75), rgba(248,250,252,0.55)) !important;
    backdrop-filter: blur(10px); -webkit-backdrop-filter: blur(10px);
    border: 1px solid rgba(226,232,240,0.9) !important;
    box-shadow: 0 4px 16px rgba(148,163,184,0.08);
    position: relative; z-index: 20; isolation: isolate;
}
/* 弹幕表格容器玻璃卡片 */
.dm-table-wrap { border-radius: 0.9rem; border: 1px solid rgba(226,232,240,0.9); overflow: hidden; background: rgba(255,255,255,0.6); }
.dm-table-wrap .gb-table tbody tr { box-shadow: inset 0 -1px 0 rgba(226,232,240,0.5); }
/* 录像/场次徽章 */
.dm-sess-badge {
    display: inline-flex; align-items: center; gap: 3px;
    padding: 2px 8px; border-radius: 9999px; font-weight: 700; font-size: 10px;
    background: linear-gradient(135deg, #ede9fe, #e0f2fe); color: #7c3aed;
    border: 1px solid rgba(216,180,254,0.5);
}
.dm-rel-time { color: #7c3aed; font-family: ui-monospace, SFMono-Regular, Menlo, monospace; }
/* 弹幕统计面板 */
.dm-stats-card {
    border-radius: 0.75rem; border: 1px solid rgba(226,232,240,0.5);
    background: rgba(255,255,255,0.6);
}
/* 分页胶囊按钮 */
.dm-page-btn {
    border-radius: 9999px !important; padding: 4px 14px !important;
    transition: all .15s ease;
}
/* 夜间：弹幕记录美化覆盖 */
html.dark .dm-toolbar {
    background: linear-gradient(180deg, rgba(30,41,59,0.68), rgba(15,23,42,0.55)) !important;
    border-color: rgba(71,85,105,0.35) !important;
    box-shadow: 0 4px 16px rgba(0,0,0,0.25);
}
html.dark .dm-toolbar-label {
    background-image: linear-gradient(135deg, #6366f1, #7c3aed);
    box-shadow: 0 2px 10px rgba(99,102,241,0.4);
}
html.dark .dm-table-wrap { background: rgba(15,23,42,0.45); border-color: rgba(71,85,105,0.3); }
html.dark .dm-table-wrap .gb-table tbody tr { box-shadow: inset 0 -1px 0 rgba(71,85,105,0.2); }
html.dark .dm-stats-card { background: rgba(15,23,42,0.5); border-color: rgba(71,85,105,0.3); }
html.dark .dm-stats-card .bg-gray-100 { background-color: rgba(30,41,59,0.8) !important; }
/* ── 可搜索场次选择器面板 ── */
.dm-sess-picker .dm-sess-trigger { min-width: 11rem; text-align: left; }
.dm-sess-picker .dm-sess-trigger .text-gray-800 { color: #1e293b; }
html.dark .dm-sess-picker .dm-sess-trigger { color: #f1f5f9 !important; background-color: #1e293b !important; border-color: rgba(71,85,105,0.45) !important; }
html.dark .dm-sess-picker .dm-sess-trigger .text-gray-400 { color: #94a3b8 !important; }
html.dark .dm-sess-picker .dm-sess-trigger .text-gray-800 { color: #f1f5f9 !important; }
.dm-sess-picker .absolute { z-index: 60; }
html.dark .dm-sess-picker .absolute { background-color: #1e293b !important; border-color: rgba(71,85,105,0.35) !important; }
html.dark .dm-sess-picker .absolute .border-gray-100 { border-color: rgba(71,85,105,0.25) !important; }
html.dark .dm-sess-picker .absolute .border-b,
html.dark .dm-sess-picker .absolute .border-t { border-color: rgba(71,85,105,0.25) !important; }
html.dark .dm-sess-picker .absolute .bg-white { background-color: #1e293b !important; }
html.dark .dm-sess-picker .absolute input[class*="border"] { background-color: #0f172a !important; border-color: rgba(71,85,105,0.5) !important; color: #e2e8f0 !important; }
html.dark .dm-sess-picker .absolute input::placeholder { color: #64748b !important; }
html.dark .dm-sess-picker .absolute .hover\:bg-blue-50:hover { background-color: rgba(99,102,241,0.18) !important; }
html.dark .dm-sess-picker .absolute .text-gray-700 { color: #e2e8f0 !important; }
html.dark .dm-sess-picker .absolute .bg-blue-50 { background-color: rgba(99,102,241,0.22) !important; }
html.dark .dm-sess-picker .absolute .text-blue-700 { color: #a5b4fc !important; }
html.dark .dm-sess-picker .absolute .max-h-64::-webkit-scrollbar-thumb { background: rgba(71,85,105,0.4); }
/* 追加 end */
html.dark .dm-sess-badge { background: rgba(124,58,237,0.25); color: #c4b5fd; border-color: rgba(167,139,250,0.4); }
html.dark .dm-rel-time { color: #c4b5fd; }
/* 弹窗遮罩统一毛玻璃 */
div[class*="fixed inset-0 bg-black/40"] { backdrop-filter: blur(6px); -webkit-backdrop-filter: blur(6px); }

/* ── 全局细滚动条（统一柔和） ── */
::-webkit-scrollbar { width: 8px; height: 8px; }
::-webkit-scrollbar-thumb { background: rgba(148,163,184,0.3); border-radius: 9999px; }
::-webkit-scrollbar-thumb:hover { background: rgba(99,102,241,0.5); }
::-webkit-scrollbar-track { background: transparent; }
</style>
</head>
<body class="bg-gray-100 p-2 sm:p-4">
<div id="app" class="max-w-6xl mx-auto" style="min-height:80vh;"><!-- 初始白屏防止闪烁 -->

<!-- ══════ 登录页 ══════ -->
<div v-if="!loggedIn" class="min-h-screen flex items-center justify-center px-4 py-10 bg-gradient-to-br from-slate-50 via-white to-indigo-50/70 relative overflow-hidden">
    <!-- 夜间模式切换（登录页右上角） -->
    <button @click="toggleTheme"
            class="absolute top-4 right-4 z-20 flex items-center gap-1.5 px-3 py-2 rounded-xl text-sm font-medium transition backdrop-blur border"
            :class="isDark ? 'bg-slate-800/80 text-amber-300 border-slate-700 hover:bg-slate-700' : 'bg-white/70 text-slate-600 border-slate-200 hover:bg-slate-100'"
            :title="isDark ? '切换到日间模式' : '切换到夜间模式'">
        <span class="text-base leading-none">{{ isDark ? '🌙' : '☀️' }}</span>
        <span class="hidden sm:inline">{{ isDark ? '夜间' : '日间' }}</span>
    </button>
    <!-- 背景装饰光斑 -->
    <div class="pointer-events-none absolute -top-24 -left-24 w-96 h-96 rounded-full bg-indigo-200/40 blur-3xl"></div>
    <div class="pointer-events-none absolute -bottom-32 -right-16 w-[28rem] h-[28rem] rounded-full bg-sky-200/40 blur-3xl"></div>
    <div v-if="false" class="pointer-events-none absolute top-1/3 right-1/4 w-40 h-40 rounded-full bg-violet-200/30 blur-2xl"></div>

    <div class="relative w-full max-w-md">
        <div class="bg-white/70 backdrop-blur-xl p-8 sm:p-10 rounded-3xl shadow-2xl shadow-indigo-100/60 border border-white/60 ring-1 ring-slate-900/5">
            <div class="flex items-center justify-center gap-3 mb-8">
                <div class="w-12 h-12 rounded-2xl bg-gradient-to-br from-indigo-500 to-sky-400 flex items-center justify-center shadow-lg shadow-indigo-200/60">
                    <img src="/icon-192.png" alt="" class="w-8 h-8 rounded-lg">
                </div>
                <div>
                    <h1 class="text-2xl font-bold text-slate-800 tracking-tight">Ayabot 管理后台</h1>
                    <p class="text-xs text-slate-400 mt-0.5">Bilibili 直播间机器人控制台</p>
                </div>
            </div>
            <div class="space-y-4">
                <div>
                    <label class="text-xs text-slate-500 font-medium mb-1.5 block">账号</label>
                    <input v-model="loginUser" placeholder="请输入账号" class="w-full px-4 py-3 rounded-xl bg-white/70 border border-slate-200 focus:border-indigo-400 focus:ring-2 focus:ring-indigo-100 outline-none transition text-sm placeholder:text-slate-300 shadow-sm" @keyup.enter="doLogin">
                </div>
                <div>
                    <label class="text-xs text-slate-500 font-medium mb-1.5 block">密码</label>
                    <input v-model="loginPass" type="password" placeholder="请输入密码" class="w-full px-4 py-3 rounded-xl bg-white/70 border border-slate-200 focus:border-indigo-400 focus:ring-2 focus:ring-indigo-100 outline-none transition text-sm placeholder:text-slate-300 shadow-sm" @keyup.enter="doLogin">
                </div>
                <div v-if="loginErr" class="text-red-500 text-sm bg-red-50 rounded-xl px-4 py-2.5 border border-red-100">{{ loginErr }}</div>
                <button @click="doLogin" class="w-full py-3 rounded-xl bg-gradient-to-r from-indigo-500 to-sky-500 hover:from-indigo-600 hover:to-sky-600 text-white font-semibold shadow-lg shadow-indigo-200/60 transition hover:shadow-indigo-300/60 active:scale-[0.99]">登 录</button>
                <div class="text-xs text-center text-amber-700 bg-amber-50 rounded-xl p-3 border border-amber-100 leading-relaxed">
                    初始账号: <strong>ayabot</strong> · 密码: <strong>123456</strong><br>
                    <span class="text-slate-400">（首次登录请修改密码）</span>
                </div>
            </div>
            <div class="mt-6 pt-5 border-t border-slate-100 text-center">
                <p class="text-xs text-slate-400">
                    <a href="https://github.com/yujianke100/ayabot" target="_blank" class="text-indigo-500 hover:underline">⭐ GitHub</a>
                    <span class="mx-1">·</span>
                    <span class="text-rose-500 font-bold">完全免费</span> · 开源
                    <span class="block mt-1">Ayabot __AYABOT_VERSION__</span>
                </p>
            </div>
        </div>
    </div>
</div>

<!-- ══════ 主界面 ══════ -->
<div v-if="loggedIn">
<header class="sticky top-3 z-40 mb-5 rounded-2xl bg-white/70 backdrop-blur-xl border border-white/70 shadow-lg shadow-indigo-100/40 px-3 sm:px-5 py-3 flex flex-wrap items-center gap-2">
    <h1 class="text-base sm:text-lg font-bold text-transparent bg-clip-text bg-gradient-to-r from-indigo-600 to-sky-500 flex-shrink-0 flex items-center gap-2"><img src="/icon-192.png" alt="Ayabot" class="w-6 h-6 rounded-lg shadow-sm flex-shrink-0">Ayabot</h1>
    <div class="flex-1 min-w-0"></div>
    <div class="flex items-center gap-1 bg-white/60 rounded-xl p-1 border border-slate-100 shadow-sm text-xs sm:text-sm sm:order-none order-last w-full sm:w-auto mt-1.5 sm:mt-0">
        <button @click="tab='rooms'" :class="tab==='rooms'?'bg-gradient-to-r from-indigo-500 to-sky-500 text-white shadow':''" class="whitespace-nowrap px-3 py-1.5 rounded-lg transition">🏠 房间管理</button>
        <button v-if="userRole === 'admin'" @click="tab='global'" :class="tab==='global'?'bg-gradient-to-r from-indigo-500 to-sky-500 text-white shadow':''" class="whitespace-nowrap px-3 py-1.5 rounded-lg transition">⚙️ 全局配置</button>
        <button v-if="userRole === 'admin'" @click="tab='users'" :class="tab==='users'?'bg-gradient-to-r from-indigo-500 to-sky-500 text-white shadow':''" class="whitespace-nowrap px-3 py-1.5 rounded-lg transition">👥 用户管理</button>
        <button @click="tab='help'"  :class="tab==='help' ?'bg-gradient-to-r from-indigo-500 to-sky-500 text-white shadow':''" class="whitespace-nowrap px-3 py-1.5 rounded-lg transition">帮助</button>
    </div>
    <!-- 夜间模式切换 -->
    <button @click="toggleTheme"
            class="flex-shrink-0 flex items-center gap-1.5 px-2.5 py-1.5 rounded-xl text-xs font-medium transition border border-slate-200/60"
            :class="isDark ? 'bg-slate-700 text-amber-300 hover:bg-slate-600' : 'bg-white/70 text-slate-600 hover:bg-slate-100'"
            :title="isDark ? '切换到日间模式' : '切换到夜间模式'">
        <span class="text-sm leading-none">{{ isDark ? '🌙' : '☀️' }}</span>
        <span class="hidden sm:inline">{{ isDark ? '夜间' : '日间' }}</span>
    </button>
    <!-- 新版本提醒（启动静默检查到更新，管理员可见） -->
    <button v-if="updateNotice && userRole === 'admin'" @click="openUpdateNotice()"
            class="flex-shrink-0 flex items-center gap-1 bg-amber-50/80 hover:bg-amber-100 border border-amber-200
                   text-amber-700 px-2.5 py-1.5 rounded-xl text-xs whitespace-nowrap mr-1 backdrop-blur"
            :title="'发现新版本 ' + updateNotice + '，点击查看'">
        <span class="relative flex h-2 w-2">
            <span class="animate-ping absolute inline-flex h-full w-full rounded-full bg-amber-400 opacity-75"></span>
            <span class="relative inline-flex rounded-full h-2 w-2 bg-amber-500"></span>
        </span>
        <span class="hidden sm:inline">新版本 {{ updateNotice }}</span>
        <span class="sm:hidden">🎁</span>
    </button>
    <div class="relative flex-shrink-0">
        <button @click="showUserMenu = !showUserMenu" class="text-slate-600 hover:text-slate-900 border border-slate-100 bg-white/70 rounded-xl px-3 py-1.5 text-xs whitespace-nowrap shadow-sm transition hover:shadow">
            👤 {{ loginUser }} ▾
        </button>
        <div v-if="showUserMenu" class="absolute right-0 top-full mt-2 bg-white/95 backdrop-blur border border-slate-100 rounded-2xl shadow-xl w-48 text-sm overflow-hidden z-[100] @click.stop" @click.stop>
            <div class="px-4 py-3 border-b border-slate-50 text-xs text-slate-400 font-medium truncate">{{ loginUser }}</div>
            <button @click="openChangePwd(); showUserMenu=false" class="block w-full text-left px-4 py-2.5 hover:bg-indigo-50/50 border-b border-slate-50 transition">🔑 修改密码</button>
            <button @click="doLogout" class="block w-full text-left px-4 py-2.5 hover:bg-red-50/50 text-red-500 transition">退出登录</button>
        </div>
    </div>
</header>

<style></style>

<!-- ══════ 修改密码弹窗 ══════ -->
<div v-if="showChangePwd" class="fixed inset-0 bg-black/40 flex items-center justify-center z-50" :style="mustResetPwd ? 'backdrop-filter:blur(4px);' : ''" @mousedown.self="mustResetPwd || (showChangePwd = false)">
    <div class="bg-white p-6 rounded-xl shadow-lg w-80" @click.stop>
        <h3 class="font-bold text-lg mb-4">🔑 {{ mustResetPwd ? '⚠️ 首次登录请重置密码' : '修改密码' }}</h3>
        <div class="space-y-3">
            <label class="text-xs text-gray-500 block">用户名
                <input type="text" v-model="changePwdNewUser" placeholder="用户名" class="border p-2 rounded w-full text-sm" :disabled="changingPwd">
                <span class="text-gray-400" v-if="mustResetPwd">可修改为你想要的用户名</span>
            </label>
            <input type="password" id="inpOldPwd" v-model="changePwdOld" placeholder="当前密码" class="border p-2 rounded w-full text-sm" :disabled="mustResetPwd || changingPwd">
            <input type="password" id="inpNewPwd" v-model="changePwdNew" placeholder="新密码（至少4位）" class="border p-2 rounded w-full text-sm" :disabled="changingPwd">
            <input type="password" id="inpCfmPwd" v-model="changePwdConfirm" placeholder="再次输入新密码" class="border p-2 rounded w-full text-sm" :disabled="changingPwd" @keyup.enter="doChangePwd">
            <div v-if="changePwdMsg" class="text-sm" :class="changePwdOk ? 'text-green-600' : 'text-red-500'">{{ changePwdMsg }}</div>
            <div class="flex gap-2">
                <button @click="doChangePwd" :disabled="changingPwd" class="bg-blue-500 hover:bg-blue-600 text-white px-4 py-2 rounded text-sm flex-1" :class="{'opacity-50 cursor-not-allowed': changingPwd}">确认</button>
                <button v-if="!mustResetPwd" @click="showChangePwd = false" :disabled="changingPwd" class="bg-gray-200 hover:bg-gray-300 px-4 py-2 rounded text-sm" :class="{'opacity-50 cursor-not-allowed': changingPwd}">取消</button>
            </div>
        </div>
    </div>
</div>

<!-- ══════ 房间管理 ══════ -->
<div v-if="tab==='rooms'" class="max-w-5xl mx-auto">

    <!-- ── 房间列表 ── -->
    <div v-if="!selectedRoom">
        <div class="bg-white p-4 sm:p-6 rounded-xl shadow-sm space-y-4">
            <div class="flex items-center justify-between flex-wrap gap-2">
                <h2 class="page-title">🏠 房间管理</h2>
                <button v-show="userRole === 'admin'" @click="toggleCreateRoom"
                        class="bg-gradient-to-r from-emerald-500 to-teal-500 hover:from-emerald-600 hover:to-teal-600 text-white px-3 sm:px-4 py-2 rounded-xl text-xs sm:text-sm shadow-md shadow-emerald-200/50 transition active:scale-[0.98]">
                    {{ showCreateRoom ? '取消' : '➕ 新建房间' }}
                </button>
            </div>

            <!-- 新建表单 -->
            <div v-if="showCreateRoom" class="create-form rounded-2xl p-4 sm:p-5 space-y-3">
                <h3 class="text-sm font-bold text-slate-700">➕ 新建直播间</h3>
                <div class="grid grid-cols-1 sm:grid-cols-2 gap-4">
                    <label class="text-xs text-gray-500 leading-relaxed">主播 UID
                        <input type="number" v-model.number="newRoomUid" placeholder="B站 主播 UID"
                               class="border p-2 rounded-xl w-full text-sm mt-1.5 bg-white/70 focus:border-indigo-400 focus:ring-2 focus:ring-indigo-100 outline-none transition">
                        <span v-if="newRoomAnchorName" class="text-[11px] mt-1 inline-block" :class="newRoomAnchorName.startsWith('(') ? 'text-yellow-500' : 'text-green-600'">
                            👤 {{ newRoomAnchorName }}
                        </span>
                    </label>
                    <label class="text-xs text-gray-500 leading-relaxed">直播间名称
                        <input type="text" v-model="newRoomName" placeholder="留空则使用主播用户名" class="border p-2 rounded-xl w-full text-sm mt-1.5 bg-white/70 focus:border-indigo-400 focus:ring-2 focus:ring-indigo-100 outline-none transition">
                    </label>
                    <label class="text-xs text-gray-500 leading-relaxed">直播间号
                        <input type="number" v-model.number="newRoomDisplayId" placeholder="B站 直播间号，如 1946287911"
                               class="border p-2 rounded-xl w-full text-sm mt-1.5 bg-white/70 focus:border-indigo-400 focus:ring-2 focus:ring-indigo-100 outline-none transition">
                    </label>
                    <label class="text-xs text-gray-500 leading-relaxed">关联 B站 账号
                        <select v-model="newRoomAccount" class="border p-2 rounded-xl w-full text-sm mt-1.5 bg-white/70 focus:border-indigo-400 focus:ring-2 focus:ring-indigo-100 outline-none transition">
                            <option value="">暂不关联</option>
                            <option v-for="a in accounts" :key="a.uid" :value="a.uid">{{ a.nickname || 'UID:'+a.uid }}</option>
                        </select>
                    </label>
                    <label class="text-xs text-gray-500 leading-relaxed">AI回复模板
                        <select v-model="newRoomLlmTemplate" class="border p-2 rounded-xl w-full text-sm mt-1.5 bg-white/70 focus:border-indigo-400 focus:ring-2 focus:ring-indigo-100 outline-none transition">
                            <option value="">默认（无模板）</option>
                            <option v-for="t in llmTemplates" :key="t.name" :value="t.name">{{ t.name }}</option>
                        </select>
                    </label>
                    <label class="text-xs text-gray-500 leading-relaxed">机器人配置模板
                        <select v-model="newRoomBotTemplate" class="border p-2 rounded-xl w-full text-sm mt-1.5 bg-white/70 focus:border-indigo-400 focus:ring-2 focus:ring-indigo-100 outline-none transition">
                            <option value="">默认（无模板）</option>
                            <option v-for="t in botTemplates" :key="t.name" :value="t.name">{{ t.name }}</option>
                        </select>
                    </label>
                </div>
                <div class="flex gap-3 items-center pt-1">
                    <button @click="createRoom" :disabled="creatingRoom"
                            class="bg-gradient-to-r from-blue-500 to-sky-500 hover:from-blue-600 hover:to-sky-600 text-white px-5 py-2 rounded-xl text-sm shadow-md shadow-blue-200/60 transition active:scale-[0.98]">
                        {{ creatingRoom ? '创建中...' : '创建' }}
                    </button>
                    <div v-if="createRoomMsg" class="text-sm" :class="createRoomOk ? 'text-green-600' : 'text-red-500'">
                        {{ createRoomMsg }}
                    </div>
                </div>
            </div>

            <!-- 房间卡片列表 -->
            <div v-if="!rooms || rooms.length === 0" class="text-sm text-gray-400 text-center py-8">
                <template v-if="userRole === 'admin'">暂无房间。点击「新建房间」添加。</template>
                <template v-else>暂无可用房间。</template>
            </div>
            <div v-for="r in rooms" :key="r.room_id"
                 class="room-card rounded-2xl p-4 flex flex-col sm:flex-row sm:items-center sm:justify-between gap-3 cursor-pointer transition"
                 :class="r.status==='running' ? 'running' : 'stopped'"
                 @click="selectRoom(r)">
                <div class="flex-1 min-w-0">
                    <div class="flex items-center gap-2 flex-wrap">
                        <span class="w-2 h-2 rounded-full inline-block shrink-0 status-dot"
                              :class="r.status==='running' ? 'bg-green-500' : 'bg-gray-400'"></span>
                        <span class="font-bold text-sm text-slate-700 room-name">{{ r.room_name || ('#'+r.room_id) }}</span>
                        <span v-if="r.room_name" class="text-xs text-gray-400">#{{ r.room_id }}</span>
                        <span class="text-xs text-gray-400 ml-1 break-all">UID: {{ r.anchor_uid }}</span>
                    </div>
                    <div class="text-xs text-gray-500 mt-1.5 flex gap-2 flex-wrap items-center">
                        <span class="status-badge" :class="r.status === 'running' ? 'on' : 'off'">{{ r.status === 'running' ? '🟢 运行中' : '⏹️ 已停止' }}</span>
                        <span v-if="r.account_nick">账号: {{ r.account_nick }}</span>
                        <span v-if="r.auth_status === 'needs_login'"
                              class="px-2.5 py-0.5 rounded-full bg-red-100 text-red-600 font-medium text-[11px]">
                            ⚠️ 登录已失效，需重新扫码
                        </span>
                        <span v-else-if="r.recent_crash"
                              class="px-2.5 py-0.5 rounded-full bg-yellow-100 text-yellow-700 text-[11px]">
                            ⚠️ 刚发生异常退出（已自动恢复）
                        </span>
                    </div>
                </div>
                <div class="flex gap-2 items-center flex-wrap sm:flex-nowrap shrink-0" @click.stop>
                    <button v-if="r.status !== 'running'"
                            @click="startRoom(r.room_id)"
                            :disabled="startingRooms.has(r.room_id)"
                            class="btn-soft bg-green-50 hover:bg-green-100 text-green-700 disabled:bg-green-50 disabled:text-green-300 px-4 py-2 sm:py-1 rounded-lg text-xs whitespace-nowrap font-medium"
                            v-show="userRole === 'admin'">{{ startingRooms.has(r.room_id) ? '启动中...' : '▶ 启动' }}</button>
                    <button v-if="r.status === 'running'"
                            @click="stopRoom(r.room_id)"
                            class="btn-soft bg-yellow-50 hover:bg-yellow-100 text-yellow-700 px-4 py-2 sm:py-1 rounded-lg text-xs whitespace-nowrap font-medium"
                            v-show="userRole === 'admin'">⏹ 停止</button>
                    <button @click="deleteRoom(r.room_id, r.room_id)"
                            class="btn-soft bg-red-50 hover:bg-red-100 text-red-500 px-4 py-2 sm:py-1 rounded-lg text-xs font-medium whitespace-nowrap"
                            v-show="userRole === 'admin'">🗑 删除</button>
                </div>
            </div>
        </div>
    </div>

    <!-- ── 房间详情 ── -->
    <div v-else>
        <div class="mb-3 sm:mb-4">
            <button @click="goBackRoomList()"
                    class="text-blue-500 hover:text-blue-700 text-sm inline-flex items-center gap-1 px-2 py-2 -ml-2 rounded-lg active:bg-blue-50">&larr; 返回房间列表</button>
        </div>

        <!-- 登录失效引导（凭证不可用时引导重新扫码，而不是报错） -->
        <div v-if="selectedRoom && selectedRoom.auth_status === 'needs_login'"
             class="bg-red-50 border border-red-200 rounded-xl p-4 mb-4 flex items-start gap-3">
            <div class="text-2xl">⚠️</div>
            <div class="flex-1">
                <div class="font-bold text-red-700 text-sm">B站 登录凭证已失效，机器人需要重新登录才能发弹幕/统计礼物</div>
                <div class="text-xs text-red-600 mt-1">
                    {{ selectedRoom.auth_reason || 'Cookie 已过期或被踢下线' }}
                </div>
                <div class="text-xs text-gray-600 mt-1">
                    机器人进程保持运行中，扫码登录成功后会自动恢复，无需重启房间。
                </div>
            </div>
            <button @click="goRelogin()"
                    class="bg-red-600 hover:bg-red-700 text-white px-3 py-1.5 rounded text-xs whitespace-nowrap">
                📱 去扫码登录
            </button>
        </div>

        <!-- 异常退出提示（自动守护已恢复） -->
        <div v-if="selectedRoom && selectedRoom.recent_crash"
             class="bg-yellow-50 border border-yellow-200 rounded-xl p-3 mb-4 text-xs text-yellow-800">
            ⚠️ 机器人刚刚异常退出（{{ selectedRoom.crash_info?.reason }}<span v-if="selectedRoom.crash_info?.exit_code !== null && selectedRoom.crash_info?.exit_code !== undefined">，退出码 {{ selectedRoom.crash_info.exit_code }}</span>），守护进程已自动重启。
        </div>

        <!-- 房间信息头（手机竖排，避免标题被按钮挤成竖排文字） -->
        <div class="bg-white p-4 rounded-xl shadow-sm mb-4 flex flex-col sm:flex-row sm:items-center sm:justify-between gap-3">
            <div class="min-w-0">
                <h2 class="text-lg font-bold flex items-center flex-wrap gap-1">
                    📺
                    <template v-if="editingRoomName">
                        <input type="text" v-model="roomNameEdit" class="border p-1 rounded text-sm w-32 sm:w-40" @keyup.enter="saveRoomName" @keyup.escape="editingRoomName=false">
                        <button @click="saveRoomName" class="text-blue-500 text-xs px-2 py-1">保存</button>
                        <button @click="editingRoomName=false" class="text-gray-400 text-xs px-2 py-1">取消</button>
                    </template>
                    <template v-else>
                        <span class="break-all">{{ selectedRoom.room_name || ('房间 #'+selectedRoom.room_id) }}</span>
                        <button v-show="userRole === 'admin'" @click="startEditRoomName" class="text-gray-400 hover:text-blue-500 text-sm px-1.5 py-1" title="改房间名">✏️</button>
                    </template>
                </h2>
                <div class="text-xs text-gray-500 mt-1 break-all">
                    主播 UID: {{ selectedRoom.anchor_uid }}
                    | 状态: {{ selectedRoom.status === 'running' ? '🟢 运行中' : '⏹️ 已停止' }}
                </div>
            </div>
            <div class="flex items-center gap-2 flex-wrap shrink-0" v-show="userRole === 'admin'">
                <span class="text-xs text-gray-500 whitespace-nowrap">B站账号:</span>
                <select v-model="selectedRoomAccount" class="border p-1.5 rounded text-sm flex-1 sm:flex-none min-w-0 max-w-[150px] sm:max-w-none">
                    <option value="">不关联</option>
                    <option v-for="a in accounts" :key="a.uid" :value="a.uid">{{ a.nickname || 'UID:'+a.uid }}</option>
                </select>
                <button @click="assignAccountToRoom" class="bg-blue-500 hover:bg-blue-600 text-white px-3 py-2 sm:py-1 rounded text-xs whitespace-nowrap">保存</button>
                <button @click="assignAccountAndRestart" class="bg-green-600 hover:bg-green-700 text-white px-3 py-2 sm:py-1 rounded text-xs whitespace-nowrap" :disabled="accountRestarting">{{ accountRestarting ? '重启中...' : '保存并重启' }}</button>
                <span v-if="accountAssignMsg" class="text-xs" :class="accountAssignOk ? 'text-green-600' : 'text-red-500'">{{ accountAssignMsg }}</span>
            </div>
        </div>

        <!-- 子导航：手机横向滚动，不折成竖排文字 -->
        <div class="flex gap-1 mb-4 text-sm bg-white rounded-xl shadow-sm p-1 overflow-x-auto no-scrollbar gb-tabs">
            <button v-for="st in roomSubTabs" :key="st.key"
                    @click="selectRoomSubTab(st.key)"
                    class="gb-tab px-3 sm:px-4 py-2 rounded-lg transition whitespace-nowrap shrink-0"
                    :class="roomSubTab === st.key ? 'bg-blue-500 text-white active' : 'text-gray-600 hover:bg-gray-100'">
                {{ st.label }}
            </button>
        </div>

        <!-- 送礼排行 -->
        <div v-if="roomSubTab==='ranking'" class="grid grid-cols-1 gap-6">
            <div class="bg-white p-4 sm:p-6 rounded-xl shadow-sm">
                <div class="grid grid-cols-2 sm:flex sm:flex-wrap gap-2 mb-3">
                    <input type="date" v-model="rStart" class="border p-2 rounded text-sm w-full sm:flex-1 sm:min-w-0">
                    <input type="date" v-model="rEnd"   class="border p-2 rounded text-sm w-full sm:flex-1 sm:min-w-0">
                    <select v-model="rType" class="border p-2 rounded text-sm w-full sm:w-auto">
                        <option value="all">全部</option>
                        <option value="gift">一般礼物</option>
                        <option value="blindbox">盲盒</option>
                    </select>
                    <button @click="loadRanking" class="bg-blue-500 hover:bg-blue-600 text-white px-4 py-2 rounded text-sm w-full sm:w-auto">查询</button>
                </div>
                <div v-if="errRanking" class="text-red-500 text-sm mb-2">{{ errRanking }}</div>
                <div class="overflow-y-auto max-h-[520px]" v-if="ranking.length">
                    <div class="overflow-x-auto">
                    <table class="w-full text-xs sm:text-sm gb-table">
                        <thead><tr class="bg-gray-50 sticky top-0"><th class="p-2 text-left">#</th><th class="p-2 text-left">用户</th><th class="p-2 text-right">价值</th><th class="p-2 text-right">利润</th></tr></thead>
                        <tbody>
                            <tr v-for="(u,i) in ranking" :key="u.uid"
                                class="border-t hover:bg-blue-50 cursor-pointer transition"
                                @click="gotoExport(u.uid, u.uname)">
                                <td class="p-2">
                                    <span class="rank-plain" :class="{'rank-1': i===0, 'rank-2': i===1, 'rank-3': i===2}">{{ i+1 }}</span>
                                </td>
                                <td class="p-2 font-medium text-gray-700">{{ u.uname }}</td>
                                <td class="p-2 text-right font-semibold text-gray-800">{{ Number(u.total_val).toFixed(1) }}</td>
                                <td class="p-2 text-right font-semibold" :class="Number(u.total_profit)>=0?'text-red-500':'text-green-500'">{{ Number(u.total_profit).toFixed(1) }}</td>
                            </tr>
                        </tbody>
                    </table>
                    </div>
                </div>
                <div v-else-if="!errRanking" class="text-gray-400 text-center py-8">暂无数据</div>
            </div>
            <div class="bg-white p-4 rounded-xl shadow-sm flex flex-col min-h-[300px]">
                <canvas id="chartRank" class="flex-1 min-h-0"></canvas>
            </div>

            <!-- 大航海（上舰）记录 -->
            <div class="bg-white p-4 sm:p-6 rounded-xl shadow-sm">
                <div class="flex items-center justify-between mb-3 flex-wrap gap-2">
                    <h3 class="font-bold text-sm gb-card-title">🚢 上舰记录
                        <span v-if="guardTotals" class="font-normal text-xs text-gray-400 ml-1">
                            共 {{ guardTotals.count }} 次 · 舰长 {{ guardTotals.captain }} / 提督 {{ guardTotals.commander }} / 总督 {{ guardTotals.governor }}
                            · 价值 {{ guardTotals.value }} 电池
                        </span>
                    </h3>
                    <button @click="loadGuards" class="text-xs text-blue-500 hover:underline">刷新</button>
                </div>
                <div v-if="guardItems.length" class="overflow-y-auto max-h-[360px]">
                    <table class="w-full text-xs sm:text-sm gb-table">
                        <thead><tr class="bg-gray-50 sticky top-0">
                            <th class="p-2 text-left">时间</th><th class="p-2 text-left">用户</th>
                            <th class="p-2 text-left">等级</th><th class="p-2 text-right">月数</th>
                            <th class="p-2 text-right">价值(电池)</th>
                        </tr></thead>
                        <tbody>
                            <tr v-for="g in guardItems" :key="g.uid + '-' + g.start_time" class="border-t">
                                <td class="p-2 text-gray-500 whitespace-nowrap">{{ fmtGuardTime(g.ts) }}</td>
                                <td class="p-2 font-medium text-gray-700">{{ g.uname }}</td>
                                <td class="p-2">
                                    <span class="px-2 py-0.5 rounded-full text-[10px] font-bold shadow-sm"
                                          :class="g.guard_level === 1 ? 'bg-amber-100 text-amber-700'
                                                : g.guard_level === 2 ? 'bg-purple-100 text-purple-700'
                                                : 'bg-blue-100 text-blue-700'">{{ g.guard_name || '大航海' }}</span>
                                </td>
                                <td class="p-2 text-right">{{ g.months }}</td>
                                <td class="p-2 text-right font-semibold text-gray-800">{{ g.value }}</td>
                            </tr>
                        </tbody>
                    </table>
                </div>
                <div v-else class="text-gray-400 text-center py-6 text-xs">
                    还没有上舰记录（开通后会出现在这里）
                </div>
            </div>
        </div>

        <!-- 精美导出 -->
        <div v-if="roomSubTab==='export'" class="flex flex-col items-center w-full">
            <!-- 模式切换 -->
            <div class="bg-white p-4 rounded-xl shadow-sm w-full max-w-3xl mb-4 space-y-3">
                <div class="flex flex-wrap gap-3 items-end">
                    <label class="text-xs text-gray-500 flex items-center gap-1.5 h-[38px]">
                        <input type="checkbox" v-model="eModeAll" @change="onModeChange" class="w-4 h-4">
                        <span>所有人</span>
                    </label>
                    <label class="text-xs text-gray-500 flex-[2] min-w-[100px]">
                        <span :class="eModeAll ? 'text-gray-300' : ''">UID</span>
                        <input type="number" v-model.number="eUid" :disabled="eModeAll"
                               class="border p-2 rounded w-full text-sm mt-0.5"
                               :class="eModeAll ? 'bg-gray-100 text-gray-300' : ''"
                               @input="onUidInput">
                    </label>
                    <label class="text-xs text-gray-500 flex-[2] min-w-[140px]">
                        日期
                        <div class="relative">
                            <input type="text" readonly :value="eDateLabel" placeholder="点击选择日期"
                                   class="border p-2 rounded w-full text-sm mt-0.5 cursor-pointer bg-white"
                                   @click="toggleCalendar($event)">
                            <Teleport to="body">
                            <div v-if="showCalendar" @click.stop class="cal-pop bg-white rounded-xl shadow-lg p-3 w-[320px]" :style="{position:'fixed', top:(calPos.top)+'px', left:(calPos.left)+'px', zIndex:2147483000}">
                                <div class="flex justify-between items-center mb-2">
                                    <button @click="calMonth--" type="button" class="px-2 py-1 hover:bg-gray-100 rounded text-sm">&lt;</button>
                                    <span class="text-sm font-bold">{{ calYear }}年{{ calMonth+1 }}月</span>
                                    <button @click="calMonth++" type="button" class="px-2 py-1 hover:bg-gray-100 rounded text-sm">&gt;</button>
                                </div>
                                <div class="flex gap-1 mb-2">
                                    <button @click="selectAllDatesInRange" type="button" class="text-[10px] px-2 py-1 bg-blue-50 text-blue-600 rounded hover:bg-blue-100">全选当月</button>
                                    <button @click="clearSelectedDates" type="button" class="text-[10px] px-2 py-1 bg-gray-50 text-gray-500 rounded hover:bg-gray-100">清除</button>
                                    <button v-if="eSelectedDates.length>=1" @click="applyMultiDateExport" type="button" class="text-[10px] px-2 py-1 bg-green-50 text-green-600 rounded hover:bg-green-100 font-semibold ml-auto">
                                        确定（{{ eSelectedDates.length }}天）
                                    </button>
                                </div>
                                <div class="grid grid-cols-7 gap-1 text-center text-xs mb-1">
                                    <div class="text-gray-400 font-medium">日</div>
                                    <div class="text-gray-400 font-medium">一</div>
                                    <div class="text-gray-400 font-medium">二</div>
                                    <div class="text-gray-400 font-medium">三</div>
                                    <div class="text-gray-400 font-medium">四</div>
                                    <div class="text-gray-400 font-medium">五</div>
                                    <div class="text-gray-400 font-medium">六</div>
                                </div>
                                <div class="grid grid-cols-7 gap-1">
                                    <template v-for="(day,i) in calDays" :key="i">
                                        <div v-if="!day" class="h-8"></div>
                                        <button v-else type="button"
                                                :disabled="!day.hasData"
                                                @click="toggleDate(day.ymd)"
                                                class="h-8 rounded text-xs transition relative"
                                                :class="day.hasData
                                                    ? (eSelectedSet.has(day.ymd) ? 'bg-blue-500 text-white' : 'bg-blue-100 text-blue-700 hover:bg-blue-200 cursor-pointer')
                                                    : 'text-gray-300 cursor-not-allowed'">
                                            {{ day.d }}
                                        </button>
                                    </template>
                                </div>
                                <div class="text-[10px] text-gray-400 mt-2 text-center">蓝色 = 有数据，深蓝 = 已选中</div>
                            </div>
                            </Teleport>
                        </div>
                    </label>
                    <select v-model="eType" class="border p-2 rounded text-sm h-[38px]">
                        <option value="all">全部</option>
                        <option value="gift">仅一般礼物</option>
                        <option value="blindbox">仅盲盒</option>
                    </select>
                    <label class="text-xs text-gray-500">
                        排序
                        <select @change="onSortChange($event)" class="border p-2 rounded text-sm h-[34px] mt-0.5">
                            <option value="uname">按用户</option>
                            <option value="value">按价值</option>
                            <option value="ts" :disabled="eMergeGifts">按时间</option>
                        </select>
                    </label>
                    <button @click="loadExport()" :disabled="loadingExport"
                            class="bg-green-500 hover:bg-green-600 disabled:bg-green-300 text-white px-5 py-2 rounded text-sm h-[38px] transition">
                        {{ loadingExport ? '⏳ 加载中...' : '生成' }}</button>
                </div>
                <div class="flex flex-wrap gap-4 items-end">
                    <label class="text-xs text-gray-500 flex items-center gap-1.5 h-[38px]">
                        <input type="checkbox" v-model="eMergeGifts" class="w-4 h-4">
                        <span>合并相同礼物</span>
                    </label>
                    <label class="text-xs text-gray-500 flex items-center gap-1.5 h-[38px]">
                        <input type="checkbox" v-model="eMergeUser" class="w-4 h-4">
                        <span>按用户合并</span>
                    </label>
                    <label class="text-xs text-gray-500 flex items-center gap-1.5 h-[38px]">
                        <input type="checkbox" v-model="eShowPrice" class="w-4 h-4">
                        <span>显示金额</span>
                    </label>
                    <label class="text-xs text-gray-500">每列行数
                        <input type="number" v-model.number="ePerCol" min="1" max="50" class="border p-2 rounded text-sm mt-0.5 w-20">
                    </label>
                    <label class="text-xs text-gray-500 flex-1 min-w-[200px]">
                        单列宽度 <span class="text-sm font-mono ml-1">{{ eColWidth }}px</span>
                        <input type="range" v-model.number="eColWidth" min="200" max="600" step="10" class="w-full mt-1">
                    </label>
                </div>
            </div>
            <div v-if="errExport" class="text-red-500 text-sm mb-2">{{ errExport }}</div>

            <div v-if="exportList.length" class="text-center mb-4">
                <button @click="captureExport" :disabled="exporting"
                        class="bg-purple-600 hover:bg-purple-700 disabled:bg-purple-300 text-white px-6 py-2.5 rounded-lg text-sm font-semibold shadow-md transition">
                    {{ exporting ? '⏳ 导出中...' : '📷 导出 PNG' }}
                </button>
                <p class="text-xs text-gray-400 mt-2">所见即所得，完整捕获全部内容（不受滚动/遮挡影响）</p>
            </div>

            <!-- 精美数据展示区（水平可滚动，居中） -->
            <div id="capture" v-if="exportList.length" class="w-full overflow-x-auto">
                <div class="capture-inner">

                <div class="capture-grid" :style="{ minWidth: exportCols.length * (eColWidth + 16) + 'px' }">
                    <div v-for="(col,cidx) in exportCols" :key="cidx" class="capture-col" :style="{ minWidth: eColWidth + 'px', maxWidth: eColWidth + 'px' }">
                        <div v-for="(item,idx2) in col" :key="item.id"
                             class="bili-card"
                             :class="cardBgClass(item.guard_level)">
                            <div class="avatar-wrap">
                                <!-- 舰长头像框 — 仅舰长有 -->
                                <img v-if="item.guard_level === 3"
                                     :src="proxyImg('https://i0.hdslb.com/bfs/live/80f732943cc3367029df65e267960d56736a82ee.png')"
                                     class="frame-img"
                                     @error="$event.target.style.display='none'">
                                <img :src="proxyImg(item.avatar)" class="face"
                                     @error="$event.target.src='data:image/svg+xml,<svg xmlns=%22http://www.w3.org/2000/svg%22 viewBox=%220 0 44 44%22><rect width=%2244%22 height=%2244%22 fill=%22%23ccc%22 rx=%2222%22/></svg>'">
                            </div>
                            <div class="flex-1 min-w-0">
                                <div class="font-bold text-sm truncate">
                                    {{ item.uname }}
                                    <span v-if="item.guard_level" class="inline-block text-[9px] font-bold px-[5px] py-[1px] rounded-full ml-1 align-middle"
                                          :class="guardBadgeClass(item.guard_level)">{{ guardLabel(item.guard_level) }}</span>
                                </div>
                                <!-- 按用户合并：列出该用户的每一个礼物（多行）全部显示 -->
                                <div v-if="eMergeUser && item._gifts && item._gifts.length" class="mt-1 space-y-1">
                                    <div class="flex items-center gap-1 font-semibold text-[11px]">
                                        <span>礼物清单</span>
                                        <span class="gift-value" v-if="eShowPrice" style="margin-left:auto; background:rgba(255,215,0,0.28)">总额 ¥{{ Number(item.actual_value).toFixed(1) }}</span>
                                    </div>
                                    <div v-for="(g, gi) in item._gifts" :key="gi"
                                         class="flex items-center gap-1.5 text-xs">
                                        <img v-if="g.gift_icon" :src="proxyImg(g.gift_icon)" class="gift-icon mini"
                                             @error="$event.target.style.display='none'">
                                        <span class="text-white/80 truncate flex-1">{{ g.gift_name }} × {{ g.gift_num }}</span>
                                        <span class="gift-value" v-if="eShowPrice && g.actual_value">¥{{ Number(g.actual_value).toFixed(1) }}</span>
                                    </div>
                                    <div v-if="item._gift_total" class="text-[10px] text-white/50 pt-0.5 border-t border-white/10">
                                        共 {{ item._gifts.length }} 种礼物 · {{ item._gift_total }} 件
                                    </div>
                                </div>
                                <!-- 普通模式：单条礼物 -->
                                <div v-else class="flex items-center gap-1.5 mt-0.5 flex-wrap">
                                    <span class="text-xs text-white/80">投喂了 {{ item.gift_name }} × {{ item.gift_num }}</span>
                                    <span class="gift-value" v-if="eShowPrice && item.actual_value">¥{{ Number(item.actual_value).toFixed(1) }}</span>
                                    <span class="gift-time" v-if="item.ts && !eMergeGifts">{{ fmtDateTime(item.ts, eSelectedDates.length > 1) }}</span>
                                </div>
                            </div>
                            <img v-if="item.gift_icon && !eMergeUser" :src="proxyImg(item.gift_icon)" class="gift-icon"
                                 @error="$event.target.style.display='none'">
                        </div>
                    </div>
                </div>
            </div>
        </div>
            <div v-else-if="!errExport" class="text-gray-400 mt-20">输入 UID 和日期后点击"生成"</div>
        </div>

        <!-- AI 回复 -->
        <div v-if="roomSubTab==='llm'" class="max-w-full sm:max-w-2xl mx-auto">
            <div class="bg-white p-4 sm:p-6 rounded-xl shadow-sm space-y-4">
                <h2 class="text-lg font-bold">🤖 AI 回复设置</h2>
                <p class="text-xs text-gray-400 mb-2">用户发送 <code class="bg-gray-100 px-1 rounded">#{{ llmWakeWord || 'ayabot' }} &lt;聊天内容&gt;</code> 时调用 LLM API 自动回复。</p>
                <div class="flex flex-wrap gap-1 mb-3 text-xs">
                    <span class="text-gray-500 mr-1">当前触发模式：</span>
                    <span class="bg-blue-50 px-2 py-0.5 rounded">#唤醒词</span>
                    <span v-if="roomConfig?.features?.llm_bare_trigger" class="bg-green-50 px-2 py-0.5 rounded">唤醒词开头</span>
                    <span v-if="roomConfig?.features?.llm_bare_trigger && roomConfig?.features?.llm_keyword_trigger" class="bg-purple-50 px-2 py-0.5 rounded">含唤醒词触发</span>
                    <span v-if="!roomConfig?.features?.llm_bare_trigger && !roomConfig?.features?.llm_keyword_trigger" class="text-gray-400">仅 #唤醒词</span>
                </div>

                <label class="flex items-center gap-2 text-sm">
                    <input type="checkbox" v-model="llmEnabled" class="w-4 h-4">
                    启用 AI 回复
                </label>

                <div class="grid grid-cols-1 sm:grid-cols-2 gap-4">
                    <label class="text-xs text-gray-500">接口格式
                        <select v-model="llmProvider" class="border p-2 rounded w-full text-sm mt-1">
                            <option value="openai">OpenAI 格式</option>
                            <option value="anthropic">Anthropic 格式</option>
                        </select>
                    </label>
                    <label class="text-xs text-gray-500">模型
                        <input type="text" v-model="llmModel" placeholder="gpt-4o-mini" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                    <label class="text-xs text-gray-500">唤醒词
                        <div class="flex items-center mt-1">
                            <span class="bg-gray-200 px-2 py-[7px] rounded-l text-sm font-mono text-gray-500">#</span>
                            <input type="text" v-model="llmWakeWord" placeholder="ayabot" class="border p-2 rounded-r w-full text-sm flex-1">
                        </div>
                        <span class="text-xs text-gray-400">用户发送 <code>#{{ llmWakeWord || 'ayabot' }} &lt;聊天内容&gt;</code> 触发</span>
                    </label>
                    <label class="text-xs text-gray-500">温度 (temperature)
                        <input type="number" v-model="llmTemp" step="0.1" min="0" max="2" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                    <label class="text-xs text-gray-500">Top P
                        <input type="number" v-model="llmTopP" step="0.05" min="0" max="1" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                    <label class="text-xs text-gray-500">最大 Token
                        <input type="number" v-model.number="llmMaxTokens" min="1" max="2000" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                </div>

                <label class="text-xs text-gray-500">API Key
                    <input type="password" v-model="llmApiKey" placeholder="sk-..." class="border p-2 rounded w-full text-sm mt-1">
                </label>

                <!-- 没有 API Key 也能用：魔搭每日免费额度（默认就显示，别让人以为必须先买 Key） -->
                <div class="rounded-lg border border-amber-200 bg-amber-50 p-3 text-[11px] leading-relaxed text-amber-900">
                    <div class="flex items-start gap-1.5">
                        <span class="shrink-0">💡</span>
                        <div class="flex-1 min-w-0">
                            <div class="font-semibold">没有 API Key？可以用魔搭 ModelScope 的每日免费额度</div>
                            <div class="mt-1 text-amber-800">
                                手机号注册即送 <b>2000 次/天</b> 的 API 调用（部分模型 500 次/天），
                                直播聊天机器人日常够用，超出后才会开始计费。
                            </div>
                            <div class="mt-2 flex flex-wrap items-center gap-1.5">
                                <button type="button" @click="applyModelScope"
                                        class="px-2 py-1 rounded bg-amber-500 hover:bg-amber-600 text-white font-medium cursor-pointer">
                                    一键填入魔搭配置
                                </button>
                                <a href="https://modelscope.cn/my/myaccesstoken" target="_blank"
                                   class="px-2 py-1 rounded bg-white border border-amber-300 hover:bg-amber-100">
                                    去领 API Key ↗
                                </a>
                                <span class="text-amber-700">（Base URL 我帮你填好，你只要粘贴 Key）</span>
                            </div>
                            <div v-if="msPicked" class="mt-1.5 text-emerald-700">
                                已填好接口格式和 Base URL（模型名保留你原来的；没填过的话我给的是 Qwen/Qwen2.5-7B-Instruct）。
                                把领到的 Key 粘到上面的输入框，再点下面的「保存」。
                            </div>
                            <div class="mt-2">
                                <span class="text-amber-700 cursor-pointer hover:underline"
                                      @click="showMsTip = !showMsTip">
                                    {{ showMsTip ? '收起详细说明 ▴' : '详细说明（Base URL / 模型名 / 其他免费额度）▾' }}
                                </span>
                            </div>
                            <div v-if="showMsTip" class="mt-1.5 space-y-0.5 text-amber-800">
                                <div>Base URL：<code class="bg-white px-1 rounded">https://api-inference.modelscope.cn/v1</code></div>
                                <div>模型名：填魔搭的模型 ID，例如 <code class="bg-white px-1 rounded">Qwen/Qwen2.5-7B-Instruct</code></div>
                                <div>接口格式保持 <b>OpenAI 格式</b>；Anthropic 格式魔搭用不了。</div>
                                <div class="pt-1 text-amber-700">
                                    其他可选：智谱 GLM-4-Flash（免费）、硅基流动、DeepSeek（按量计费很便宜）。
                                    额度与规则以各家官网为准。
                                </div>
                            </div>
                        </div>
                    </div>
                </div>

                <label class="text-xs text-gray-500">Base URL
                    <input type="url" v-model="llmBaseUrl" placeholder="https://api.openai.com/v1" class="border p-2 rounded w-full text-sm mt-1">
                </label>

                <label class="text-xs text-gray-500">人设（System Prompt）
                    <textarea v-model="llmPrompt" rows="3" class="border p-2 rounded w-full text-sm mt-1" placeholder="你是ayabot，一个可爱温柔的虚拟主播助手。所有回复必须控制在40字以内。"></textarea>
                </label>

                <hr class="my-2">
                <h3 class="text-sm font-bold">🧠 对话上下文</h3>

                <label class="flex items-center gap-2 text-sm">
                    <input type="checkbox" v-model="ctxEnabled" class="w-4 h-4">
                    开启上下文记忆
                </label>

                <div v-if="ctxEnabled" class="grid grid-cols-1 sm:grid-cols-2 gap-4">
                    <label class="text-xs text-gray-500">隔离方式
                        <select v-model="ctxMode" class="border p-2 rounded w-full text-sm mt-1">
                            <option value="isolated">按用户隔离</option>
                            <option value="merged">所有用户合并</option>
                        </select>
                    </label>
                    <label class="text-xs text-gray-500">记录内容
                        <select v-model="ctxContent" class="border p-2 rounded w-full text-sm mt-1">
                            <option value="llm_only">仅 #{{ llmWakeWord }} 对话</option>
                            <option value="all">所有弹幕消息</option>
                        </select>
                    </label>
                </div>

                <label v-if="ctxEnabled" class="text-xs text-gray-500">保留条数
                    <input type="number" v-model.number="ctxMaxMsg" min="1" max="50" class="border p-2 rounded w-full text-sm mt-1">
                </label>

                <div class="flex items-center gap-4 flex-wrap">
                    <button @click="saveLlmConfig" class="bg-blue-500 hover:bg-blue-600 text-white px-6 py-2 rounded text-sm">保存</button>
                    <button @click="downloadJson('/api/llm_config/export', 'llm_config.json')" class="bg-green-500 hover:bg-green-600 text-white px-3 py-2 rounded text-sm text-xs">📤 导出</button>
                    <button @click="importJsonFile('选择 AI 配置 JSON','/api/llm_config/import', afterImportLlm)" class="bg-orange-500 hover:bg-orange-600 text-white px-3 py-2 rounded text-sm text-xs">📥 导入</button>
                    <span v-if="llmSaveMsg" class="text-sm" :class="llmSaveOk ? 'text-green-600' : 'text-red-500'">{{ llmSaveMsg }}</span>
                    <span v-if="llmSaveOk" class="text-xs text-green-600">✅ 即时生效，无需重启</span>
                    <select v-model="applyLlmTemplate" class="border p-1 rounded text-xs">
                        <option value="">套用AI模板...</option>
                        <option v-for="t in llmTemplates" :key="t.name" :value="t.name">{{ t.name }}</option>
                    </select>
                    <button v-if="applyLlmTemplate" @click="applyTemplateToLlm" class="bg-purple-500 hover:bg-purple-600 text-white px-3 py-1.5 rounded text-xs">应用</button>
                </div>

                <hr class="my-2">
                <h3 class="text-sm font-bold">测试</h3>
                <div class="flex gap-2">
                    <input type="text" v-model="llmTestText" placeholder="输入测试消息" class="border p-2 rounded flex-1 text-sm"
                           @keyup.enter="testLlm">
                    <button @click="testLlm" class="bg-green-500 hover:bg-green-600 text-white px-4 py-2 rounded text-sm">测试</button>
                </div>
                <div v-if="llmTestResp" class="text-sm bg-gray-50 p-3 rounded">{{ llmTestResp }}</div>
            </div>
        </div>

        <!-- 机器人配置 -->
        <div v-if="roomSubTab==='config'" class="max-w-full sm:max-w-2xl mx-auto">
            <div v-if="roomConfig" class="bg-white p-4 sm:p-6 rounded-xl shadow-sm space-y-4">
                <h2 class="text-lg font-bold">⚙️ 机器人配置</h2>
                <p class="text-xs text-gray-500">配置保存后需重启对应房间服务才能生效。</p>

                <div class="grid grid-cols-1 sm:grid-cols-2 gap-4">
                    <label class="text-xs text-gray-500">主播 UID
                        <input type="number" v-model.number="roomConfig.anchor_uid" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                </div>

                <hr>
                <h3 class="text-sm font-bold cursor-pointer select-none hover:text-blue-600" @click="toggleSection('rateLimit')">
                    <span v-if="configSections.rateLimit">▼</span><span v-else>▶</span> 🚦 限流 / 冷却
                </h3>
                <div v-show="configSections.rateLimit" class="grid grid-cols-1 sm:grid-cols-2 gap-4">
                    <label class="text-xs text-gray-500">欢迎同用户间隔（秒）
                        <input type="number" v-model.number="roomConfig.cooldown.welcome_user_seconds" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                    <label class="text-xs text-gray-500">感谢同用户间隔（秒）
                        <input type="number" v-model.number="roomConfig.cooldown.thanks_user_seconds" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                    <label class="text-xs text-gray-500">弹幕发送间隔(秒)
                        <input type="number" v-model="roomConfig.rate_limit.send_interval_seconds" step="0.1" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                    <label class="text-xs text-gray-500">重试次数
                        <input type="number" v-model.number="roomConfig.rate_limit.retry_count" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                    <label class="text-xs text-gray-500">队列上限
                        <input type="number" v-model.number="roomConfig.rate_limit.max_queue_size" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                    <label class="text-xs text-gray-500">回复延迟(秒)
                        <input type="number" v-model="roomConfig.rate_limit.reply_delay_seconds" step="0.1" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                </div>

                <hr>
                <h3 class="text-sm font-bold cursor-pointer select-none hover:text-blue-600" @click="toggleSection('features')">
                    <span v-if="configSections.features">▼</span><span v-else>▶</span> 🎛️ 功能开关
                </h3>
                <div v-show="configSections.features">
                <div class="grid grid-cols-1 sm:grid-cols-2 gap-2 text-sm">
                    <label class="flex items-center gap-2"><input type="checkbox" v-model="roomConfig.features.welcome_enabled" class="w-4 h-4"> 欢迎</label>
                    <label class="flex items-center gap-2"><input type="checkbox" v-model="roomConfig.features.guard_welcome_enabled" class="w-4 h-4"> 大航海欢迎</label>
                    <label class="flex items-center gap-2"><input type="checkbox" v-model="roomConfig.features.thanks_enabled" class="w-4 h-4"> 感谢</label>
                    <div class="flex items-center gap-1 text-[11px] text-gray-400 col-span-2 sm:col-span-2">大航海欢迎：仅舰长/提督/总督进房时用专属模板欢迎，与「欢迎」相互独立，可只开大航海欢迎</div>

                    <label class="flex items-center gap-2"><input type="checkbox" v-model="roomConfig.features.blindbox_enabled" class="w-4 h-4"> 盲盒统计</label>
                    <label class="flex items-center gap-2"><input type="checkbox" v-model="roomConfig.features.guard_thanks_enabled" class="w-4 h-4"> 大航海感谢</label>
                    <label class="flex items-center gap-2"><input type="checkbox" v-model="roomConfig.features.like_thanks_enabled" class="w-4 h-4"> 点赞感谢</label>
                    <label class="flex items-center gap-2"><input type="checkbox" v-model="roomConfig.features.share_thanks_enabled" class="w-4 h-4"> 转发感谢</label>
                    <label class="flex items-center gap-2"><input type="checkbox" v-model="roomConfig.features.follow_thanks_enabled" class="w-4 h-4"> 关注感谢</label>

                    <label class="flex items-center gap-2"><input type="checkbox" v-model="roomConfig.features.connected_message_enabled" class="w-4 h-4"> 连接消息</label>
                    <label class="flex items-center gap-2"><input type="checkbox" v-model="roomConfig.features.danmaku_log_enabled" class="w-4 h-4"> 弹幕记录</label>
                    <label class="flex items-center gap-2"><input type="checkbox" v-model="roomConfig.features.allow_bare_commands" class="w-4 h-4"> 免#指令</label>
                    <label class="flex items-center gap-2"><input type="checkbox" v-model="roomConfig.features.llm_bare_trigger" class="w-4 h-4"> AI免#前缀唤醒</label>
                    <label class="flex items-center gap-2" v-if="roomConfig.features.llm_bare_trigger"><input type="checkbox" v-model="roomConfig.features.llm_keyword_trigger" class="w-4 h-4"> 包含关键词触发AI</label>
                    <label class="flex items-center gap-2"><input type="checkbox" v-model="roomConfig.features.use_chinese_numbers_global" class="w-4 h-4"> 全局大写数字（反屏蔽）</label>
                    <label class="flex items-center gap-2"><input type="checkbox" v-model="roomConfig.features.pk_report_enabled" class="w-4 h-4"> ⚔️ PK汇报</label>
                    <label class="flex items-center gap-2"><input type="checkbox" v-model="roomConfig.features.run_when_not_live" class="w-4 h-4"> 未开播也运行</label>
                    <div class="flex items-center gap-1 text-[11px] text-gray-400 col-span-2 sm:col-span-2">未开播也运行：未开播时也保持弹幕连接并正常发送消息（测试用，开启后永不断连）</div>
                </div>
                <div class="text-xs text-gray-400 mb-2">免#指令：开启后可不带 # 使用指令（签到、今日盲盒等） | AI免#：弹幕开头匹配唤醒词即触发AI | 包含关键词：弹幕含唤醒词即触发AI（需AI免#前缀唤醒）</div>
                <div v-if="roomConfig.features.danmaku_log_enabled" class="grid grid-cols-1 sm:grid-cols-2 gap-4">
                    <label class="text-xs text-gray-500">弹幕总条数上限
                        <input type="number" v-model.number="roomConfig.features.danmaku_log_max_entries" min="100" max="100000" class="border p-2 rounded w-full text-sm mt-1">
                        <span class="text-gray-400 text-[10px]">数据库保留的总条数，超出时自动删除最旧记录，不是单日上限</span>
                    </label>
                    <label class="text-xs text-gray-500">
                        保留天数
                        <input type="number" v-model.number="roomConfig.features.danmaku_retention_days" min="1" max="365" class="border p-2 rounded w-full text-sm mt-1">
                        <span class="text-gray-400 text-[10px]">关闭弹幕记录时此配置不生效，且不会主动删除旧数据</span>
                    </label>
                </div>
                <div v-else class="text-xs text-gray-400 ml-1 mb-2">弹幕记录关闭时，保留天数不生效，已有数据保留不删除。</div>
                <hr class="my-3">
                <h4 class="text-xs font-bold text-gray-600 mb-2">📦 数据保留</h4>
                <div class="grid grid-cols-1 sm:grid-cols-2 gap-4">
                    <label class="text-xs text-gray-500">礼物保留天数
                        <input type="number" v-model.number="roomConfig.features.gift_retention_days" min="0" max="3650" class="border p-2 rounded w-full text-sm mt-1">
                        <span class="text-gray-400 text-[10px]">0=永久保存，默认733天(~2年)，机器人启动时自动清理过期数据</span>
                    </label>
                    <label class="text-xs text-gray-500">日志级别
                        <select v-model="roomConfig.runtime.log_level" class="border p-2 rounded w-full text-sm mt-1">
                            <option value="DEBUG">DEBUG</option>
                            <option value="INFO">INFO</option>
                            <option value="WARNING">WARNING</option>
                            <option value="ERROR">ERROR</option>
                        </select>
                        <span class="text-xs text-gray-400">保存后重启机器人生效</span>
                    </label>
                </div>
                </div>

                <hr>
                <h3 class="text-sm font-bold cursor-pointer select-none hover:text-blue-600" @click="toggleSection('filter')">
                    <span v-if="configSections.filter">▼</span><span v-else>▶</span> 🚫 弹幕过滤
                </h3>
                <div v-show="configSections.filter" class="space-y-3">
                    <div class="border rounded p-3 bg-gray-50 flex items-center justify-between">
                        <div>
                            <span class="text-xs font-bold text-gray-600">🚫 UID 黑名单</span>
                            <span class="text-xs text-gray-400 ml-2">{{ (roomConfig.features.uid_blacklist||[]).length }} 条规则</span>
                        </div>
                        <button @click="openUidBlacklistModal" class="bg-blue-50 hover:bg-blue-100 text-blue-600 px-2.5 py-1 rounded text-xs font-medium">✏️ 编辑</button>
                    </div>
                    <div class="border rounded p-3 bg-gray-50 flex items-center justify-between">
                        <div>
                            <span class="text-xs font-bold text-gray-600">🔤 关键词屏蔽</span>
                            <span class="text-xs text-gray-400 ml-2">{{ (roomConfig.features.keyword_filter||[]).length }} 条规则</span>
                        </div>
                        <button @click="openKeywordFilterModal" class="bg-blue-50 hover:bg-blue-100 text-blue-600 px-2.5 py-1 rounded text-xs font-medium">✏️ 编辑</button>
                    </div>
                </div>

                <hr>
                <h3 class="text-sm font-bold cursor-pointer select-none hover:text-blue-600" @click="toggleSection('templates')">
                    <span v-if="configSections.templates">▼</span><span v-else>▶</span> 📝 回复模板
                </h3>
                <div v-show="configSections.templates" class="space-y-3">
                    <label class="text-xs text-gray-500 block">欢迎模板
                        <input type="text" v-model="roomConfig.features.welcome_template" placeholder="欢迎{uname}来到直播间" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                    <div class="border rounded p-3 bg-gray-50 flex items-center justify-between">
                        <span class="text-xs text-gray-500">📋 多模板（随机+时段）共 {{ ((roomConfig?.features?.welcome_templates_list||[]).length) }} 条</span>
                        <button @click="openWelcomeTplModal" class="bg-blue-50 hover:bg-blue-100 text-blue-600 px-2.5 py-1 rounded text-xs font-medium">✏️ 编辑</button>
                    </div>
                    <label class="text-xs text-gray-500 block">感谢模板
                        <input type="text" v-model="roomConfig.features.thanks_template" placeholder="感谢{uname}的{gift_name}x{gift_num}!" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                    <div class="border rounded p-3 bg-gray-50 space-y-2">
                        <h4 class="text-xs font-bold text-gray-600">🏆 荣耀等级欢迎</h4>
                        <label class="flex items-center gap-2 text-xs"><input type="checkbox" v-model="roomConfig.features.honor_welcome_enabled" class="w-4 h-4"> 启用</label>
                        <label class="text-xs text-gray-500">最低勋章等级
                            <input type="number" v-model.number="roomConfig.features.honor_welcome_min_level" min="1" max="40" class="border p-2 rounded w-full text-sm mt-1">
                            <span class="text-[10px] text-gray-400">粉丝勋章等级 ≥ 此值时触发荣耀欢迎</span>
                        </label>
                        <label class="text-xs text-gray-500">单模板（多模板为空时使用）
                            <input type="text" v-model="roomConfig.features.honor_welcome_template" placeholder="欢迎荣耀{uname}进入直播间~" class="border p-2 rounded w-full text-sm mt-1">
                        </label>
                        <div class="flex items-center justify-between">
                            <span class="text-xs text-gray-500">📋 多模板共 {{ ((roomConfig?.features?.honor_welcome_templates_list||[]).length) }} 条</span>
                            <button @click="openHonorWelcomeTplModal" class="bg-blue-50 hover:bg-blue-100 text-blue-600 px-2.5 py-1 rounded text-xs font-medium">✏️ 编辑</button>
                        </div>
                    </div>
                    <label class="text-xs text-gray-500 block">大航海 - 舰长
                        <input type="text" v-model="roomConfig.features.guard_thanks_template_captain" placeholder="感谢{uname}上舰！" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                    <label class="text-xs text-gray-500 block">大航海 - 提督
                        <input type="text" v-model="roomConfig.features.guard_thanks_template_commander" placeholder="感谢{uname}支持！" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                    <label class="text-xs text-gray-500 block">大航海 - 总督
                        <input type="text" v-model="roomConfig.features.guard_thanks_template_governor" placeholder="感谢{uname}支持！" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                    <label class="text-xs text-gray-500 block">大航海 - 默认
                        <input type="text" v-model="roomConfig.features.guard_thanks_template_default" placeholder="感谢{uname}开通大航海！" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                    <div v-if="roomConfig.features.like_thanks_enabled" class="border rounded p-3 bg-gray-50 mt-2">
                        <h4 class="text-xs font-bold text-gray-600">👍 点赞感谢</h4>
                        <label class="text-xs text-gray-500 block">模板
                            <input type="text" v-model="roomConfig.features.like_thanks_template" placeholder="感谢 {uname} 的点赞~" class="border p-2 rounded w-full text-sm mt-1">
                            <span class="text-gray-400 text-[10px]">支持占位符: {uname}用户名</span>
                        </label>
                    </div>
                    <div v-if="roomConfig.features.share_thanks_enabled" class="border rounded p-3 bg-gray-50 space-y-2 mt-2">
                        <h4 class="text-xs font-bold text-gray-600">🔁 转发感谢</h4>
                        <label class="text-xs text-gray-500 block">模板
                            <input type="text" v-model="roomConfig.features.share_thanks_template" placeholder="感谢分享直播间~" class="border p-2 rounded w-full text-sm mt-1">
                            <span class="text-gray-400 text-[10px]">B站不提供分享者信息，无法使用 {uname}</span>
                        </label>
                    </div>
                    <div v-if="roomConfig.features.follow_thanks_enabled" class="border rounded p-3 bg-gray-50 space-y-2 mt-2">
                        <h4 class="text-xs font-bold text-gray-600">❤️ 关注感谢</h4>
                        <label class="text-xs text-gray-500 block">模板
                            <input type="text" v-model="roomConfig.features.follow_thanks_template" placeholder="感谢 {uname} 的关注~" class="border p-2 rounded w-full text-sm mt-1">
                            <span class="text-gray-400 text-[10px]">支持占位符: {uname}用户名</span>
                        </label>
                    </div>
                    <h4 class="text-xs font-bold text-gray-600 mt-2">🛳️ 大航海欢迎（仅舰长/提督/总督，优先级高于默认欢迎模板）</h4>
                    <div class="border rounded p-3 bg-gray-50 flex items-center justify-between">
                        <label class="flex items-center gap-2 text-xs text-gray-600"><input type="checkbox" v-model="roomConfig.features.guard_welcome_enabled" class="w-4 h-4"> 开启大航海欢迎</label>
                        <button @click="openGuardWelcomeTplModal" class="bg-blue-50 hover:bg-blue-100 text-blue-600 px-2.5 py-1 rounded text-xs font-medium">✏️ 编辑模板</button>
                    </div>
                    <label class="text-xs text-gray-500 block">连接消息
                        <input type="text" v-model="roomConfig.features.connected_message" placeholder="来了喵~" class="border p-2 rounded w-full text-sm mt-1">
                    </label>

                    <h4 class="text-xs font-bold text-gray-600 mt-2">📦 盲盒统计（支持 {count} {cost} {profit} 占位符）</h4>
                    <p class="text-[10px] text-gray-400">修改盲盒指令的回复文本。如发送失败可尝试开启「数字转中文」或使用简短表述。</p>
                    <label class="flex items-center gap-2 text-xs mb-2">
                        <input type="checkbox" v-model="roomConfig.features.use_chinese_numbers" class="w-4 h-4" :disabled="roomConfig.features.use_chinese_numbers_global"> 盲盒数字转中文
                        <span v-if="roomConfig.features.use_chinese_numbers_global" class="text-gray-400 text-[10px]">（全局已开启，无需单独设置）</span>
                    </label>
                    <div class="border rounded p-3 bg-gray-50 space-y-2 mb-2">
                        <label class="flex items-center gap-2 text-xs">
                            <input type="checkbox" v-model="roomConfig.features.blindbox_glassheart_enabled" class="w-4 h-4"> 💔 玻璃心模式（亏损时隐藏真实收益）
                        </label>
                        <label v-if="roomConfig.features.blindbox_glassheart_enabled" class="text-xs text-gray-500 block">亏损回复
                            <input type="text" v-model="roomConfig.features.blindbox_glassheart_reply" placeholder="服务器繁忙，请稍后重试" class="border p-2 rounded w-full text-sm mt-1">
                        </label>
                    </div>
                    <label class="text-xs text-gray-500 block">#本月盲盒 有数据
                        <input type="text" v-model="roomConfig.features.blindbox_result_monthly" placeholder="本月盲盒共{count}个，花费{cost}，收益{profit}" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                    <label class="text-xs text-gray-500 block">#今日盲盒 有数据
                        <input type="text" v-model="roomConfig.features.blindbox_result_today" placeholder="今日盲盒共{count}个，花费{cost}，收益{profit}" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                    <label class="text-xs text-gray-500 block">有送礼无盲盒
                        <input type="text" v-model="roomConfig.features.blindbox_no_blindbox" placeholder="无盲盒记录" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                    <label class="text-xs text-gray-500 block">无任何送礼记录
                        <input type="text" v-model="roomConfig.features.blindbox_no_gift" placeholder="无送礼记录" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                </div>

                <hr>
                <h3 class="text-sm font-bold cursor-pointer select-none hover:text-blue-600" @click="toggleSection('periodic')">
                    <span v-if="configSections.periodic">▼</span><span v-else>▶</span> ⏰ 定时消息
                </h3>
                <div v-show="configSections.periodic" class="space-y-3">
                    <label class="flex items-center gap-2 text-sm">
                        <input type="checkbox" v-model="roomConfig.features.periodic_message_enabled" class="w-4 h-4">
                        启用定时消息（仅在开播时发送）
                    </label>
                    <div class="grid grid-cols-1 sm:grid-cols-2 gap-4">
                        <label class="text-xs text-gray-500">间隔（秒）
                            <input type="number" v-model.number="roomConfig.features.periodic_message_interval_seconds" min="30" max="86400" class="border p-2 rounded w-full text-sm mt-1">
                            <span class="text-xs text-gray-400">默认 600 秒（10 分钟）</span>
                        </label>
                    </div>
                    <div class="border rounded p-3 bg-gray-50 flex items-center justify-between">
                        <span class="text-xs text-gray-500">📋 多模板（随机+时段）共 {{ ((roomConfig?.features?.periodic_messages_list||[]).length) }} 条</span>
                        <button @click="openPeriodicTplModal" class="bg-blue-50 hover:bg-blue-100 text-blue-600 px-2.5 py-1 rounded text-xs font-medium">✏️ 编辑</button>
                    </div>
                    <label class="text-xs text-gray-500 block">旧版单模板（降级）
                        <input type="text" v-model="roomConfig.features.periodic_message_template" placeholder="欢迎关注直播间~点个关注不迷路！" class="border p-2 rounded w-full text-sm mt-1">
                        <span class="text-xs text-gray-400">新版多模板填空时使用此项</span>
                    </label>
                </div>

                <hr>
                <h3 class="text-sm font-bold cursor-pointer select-none hover:text-blue-600" @click="toggleSection('uidWelcome')">
                    <span v-if="configSections.uidWelcome">▼</span><span v-else>▶</span> 👤 UID特定欢迎模板
                </h3>
                <div v-show="configSections.uidWelcome">
                <p class="text-xs text-gray-500">为特定UID的用户设置专属欢迎词（优先级高于默认和大航海欢迎）。</p>
                <div class="border rounded p-3 bg-gray-50 flex items-center justify-between">
                    <span class="text-xs text-gray-500">共 {{ (roomConfig.features.welcome_templates_for_uids_entries||[]).length }} 条配置</span>
                    <button @click="openUidWelcomeModal" class="bg-blue-50 hover:bg-blue-100 text-blue-600 px-2.5 py-1 rounded text-xs font-medium">✏️ 编辑</button>
                </div>
                </div>

                <!-- UID欢迎模板编辑弹窗 -->
                <div v-if="showUidWelcomeModal" class="fixed inset-0 bg-black/40 flex items-center justify-center z-50">
                    <div class="bg-white rounded-xl shadow-lg w-full max-w-lg mx-4 max-h-[80vh] flex flex-col" @click.stop>
                        <div class="p-4 border-b flex items-center justify-between">
                            <h3 class="font-bold text-lg">👤 UID特定欢迎模板</h3>
                            <button @click="closeUidWelcomeModal" class="text-gray-400 hover:text-gray-600 text-xl">✕</button>
                        </div>
                        <div class="p-4 overflow-y-auto flex-1 space-y-3">
                            <div v-for="(wt, wti) in uidWelcomeEditEntries" :key="wti" class="border rounded p-3 bg-gray-50 space-y-2">
                                <div class="flex items-center justify-between">
                                    <span class="text-xs font-bold">#{{ wti+1 }}</span>
                                    <button @click="uidWelcomeEditEntries.splice(wti, 1)" class="bg-red-50 hover:bg-red-100 text-red-500 px-2 py-0.5 rounded text-xs font-medium">删除</button>
                                </div>
                                <div class="grid grid-cols-1 sm:grid-cols-2 gap-2">
                                    <label class="text-xs text-gray-500">UID
                                        <input type="number" v-model.number="wt.uid" class="border p-1 rounded w-full text-sm mt-1" placeholder="用户UID">
                                    </label>
                                    <label class="text-xs text-gray-500">欢迎模板
                                        <input type="text" v-model="wt.template" class="border p-1 rounded w-full text-sm mt-1" placeholder="欢迎{uname}！">
                                    </label>
                                </div>
                                <label class="flex items-center gap-1 text-xs text-gray-500 mt-1">
                                    <input type="checkbox" v-model="wt.allDay" class="w-3.5 h-3.5" @change="wt.time_start=0; wt.time_end=23">
                                    全天生效
                                </label>
                                <div v-if="!wt.allDay" class="grid grid-cols-2 gap-2">
                                    <label class="text-xs text-gray-500">起始小时
                                        <input type="number" v-model.number="wt.time_start" min="0" max="23" class="border p-1 rounded w-full text-sm mt-1">
                                    </label>
                                    <label class="text-xs text-gray-500">结束小时
                                        <input type="number" v-model.number="wt.time_end" min="0" max="23" class="border p-1 rounded w-full text-sm mt-1">
                                    </label>
                                </div>
                            </div>
                            <button @click="uidWelcomeEditEntries.push({uid: 0, template: '', time_start: 0, time_end: 23, allDay: true})" class="bg-blue-50 hover:bg-blue-100 text-blue-600 px-3 py-1 rounded text-xs font-medium">➕ 添加</button>
                        </div>
                        <div class="p-4 border-t flex items-center gap-2 justify-end">
                            <button @click="closeUidWelcomeModal" class="bg-gray-200 hover:bg-gray-300 px-4 py-2 rounded text-sm">取消</button>
                            <button @click="saveUidWelcomeModal" class="bg-blue-500 hover:bg-blue-600 text-white px-4 py-2 rounded text-sm">保存</button>
                        </div>
                    </div>
                </div>

                <hr>
                <h3 class="text-sm font-bold">🔑 关键词回复</h3>
                <p class="text-xs text-gray-500">设置弹幕关键词自动回复。支持包含、精确匹配。</p>
                <div class="border rounded p-3 bg-gray-50 space-y-2">
                    <label class="flex items-center gap-2 text-xs">
                        <input type="checkbox" v-model="roomConfig.keyword_reply.enabled" class="w-4 h-4"> 启用
                    </label>
                    <label class="text-xs text-gray-500">冷却时间(秒)
                        <input type="number" v-model.number="roomConfig.keyword_reply.cooldown" class="border p-2 rounded w-full text-sm mt-1">
                    </label>
                    <div class="flex items-center justify-between pt-1">
                        <span class="text-xs text-gray-500">共 {{ (roomConfig.keyword_reply.rules||[]).length }} 条规则</span>
                        <button @click="openKeywordModal" class="bg-blue-50 hover:bg-blue-100 text-blue-600 px-2.5 py-1 rounded text-xs font-medium">✏️ 编辑</button>
                    </div>
                </div>

                <!-- 关键词回复编辑弹窗 -->
                <div v-if="showKeywordModal" class="fixed inset-0 bg-black/40 flex items-center justify-center z-50">
                    <div class="bg-white rounded-xl shadow-lg w-full max-w-xl mx-4 max-h-[80vh] flex flex-col" @click.stop>
                        <div class="p-4 border-b flex items-center justify-between">
                            <h3 class="font-bold text-lg">🔑 关键词规则</h3>
                            <button @click="closeKeywordModal" class="text-gray-400 hover:text-gray-600 text-xl">✕</button>
                        </div>
                        <div class="p-4 overflow-y-auto flex-1 space-y-3">
                            <div v-for="(rule, ri) in keywordEditRules" :key="ri" class="border rounded p-3 bg-gray-50 space-y-2">
                                <div class="flex items-center justify-between">
                                    <span class="text-xs font-bold">规则 #{{ ri+1 }}</span>
                                    <button @click="keywordEditRules.splice(ri, 1)" class="bg-red-50 hover:bg-red-100 text-red-500 px-2 py-0.5 rounded text-xs font-medium">删除</button>
                                </div>
                                <label class="text-xs text-gray-500">触发关键词（逗号分隔）
                                    <input type="text" v-model="rule.keywordsStr" class="border p-1 rounded w-full text-sm mt-1" placeholder="价格,多少钱">
                                </label>
                                <label class="text-xs text-gray-500">回复内容
                                    <textarea v-model="rule.reply" class="border p-1 rounded w-full text-sm mt-1" rows="2"></textarea>
                                </label>
                                <label class="text-xs text-gray-500">匹配模式
                                    <select v-model="rule.match_mode" class="border p-1 rounded text-sm">
                                        <option value="contains">包含</option>
                                        <option value="exact">精确</option>
                                    </select>
                                </label>
                                <label class="text-xs text-gray-500">限制UID（逗号分隔，留空=全部用户）
                                    <input type="text" v-model="rule.allowedUidsStr" class="border p-1 rounded w-full text-sm mt-1" placeholder="12345, 67890">
                                </label>
                                <label class="flex items-center gap-1 text-xs text-gray-500 mt-1">
                                    <input type="checkbox" v-model="rule.allDay" class="w-3.5 h-3.5" @change="rule.time_start=0; rule.time_end=23">
                                    全天生效
                                </label>
                                <div v-if="!rule.allDay" class="grid grid-cols-2 gap-2">
                                    <label class="text-xs text-gray-500">起始小时
                                        <input type="number" v-model.number="rule.time_start" min="0" max="23" class="border p-1 rounded w-full text-sm mt-1">
                                    </label>
                                    <label class="text-xs text-gray-500">结束小时
                                        <input type="number" v-model.number="rule.time_end" min="0" max="23" class="border p-1 rounded w-full text-sm mt-1">
                                    </label>
                                </div>
                            </div>
                            <button @click="keywordEditRules.push({keywordsStr: '', reply: '', match_mode: 'contains', allowedUidsStr: '', time_start: 0, time_end: 23, allDay: true})" class="bg-blue-50 hover:bg-blue-100 text-blue-600 px-3 py-1 rounded text-xs font-medium">➕ 添加规则</button>
                        </div>
                        <div class="p-4 border-t flex items-center gap-2 justify-end">
                            <button @click="closeKeywordModal" class="bg-gray-200 hover:bg-gray-300 px-4 py-2 rounded text-sm">取消</button>
                            <button @click="saveKeywordModal" class="bg-blue-500 hover:bg-blue-600 text-white px-4 py-2 rounded text-sm">保存</button>
                        </div>
                    </div>
                </div>

                <!-- ── 欢迎模板多模板编辑弹窗 ── -->
                <div v-if="showWelcomeTplModal" class="fixed inset-0 bg-black/40 flex items-center justify-center z-50">
                    <div class="bg-white rounded-xl shadow-lg w-full max-w-lg mx-4 max-h-[80vh] flex flex-col" @click.stop>
                        <div class="p-4 border-b flex items-center justify-between">
                            <h3 class="font-bold text-lg">📝 欢迎多模板</h3>
                            <button @click="showWelcomeTplModal = false" class="text-gray-400 hover:text-gray-600 text-xl">✕</button>
                        </div>
                        <div class="p-4 overflow-y-auto flex-1 space-y-3">
                            <p class="text-xs text-gray-500">每条模板可设置生效时段，机器人每次随机选一条当前时段生效的发送。</p>
                            <div v-for="(t, ti) in welcomeTplEntries" :key="ti" class="border rounded p-3 bg-gray-50 space-y-2">
                                <div class="flex items-center justify-between">
                                    <span class="text-xs font-bold">模板 #{{ ti+1 }}</span>
                                    <button @click="welcomeTplEntries.splice(ti, 1)" class="bg-red-50 hover:bg-red-100 text-red-500 px-2 py-0.5 rounded text-xs font-medium">删除</button>
                                </div>
                                <label class="text-xs text-gray-500">内容（支持 {uname}）
                                    <input type="text" v-model="t.text" class="border p-1 rounded w-full text-sm mt-1" placeholder="欢迎 {uname} 来到直播间喵~">
                                </label>
                                <label class="flex items-center gap-1 text-xs text-gray-500 mt-1">
                                    <input type="checkbox" v-model="t.allDay" class="w-3.5 h-3.5" @change="t.time_start=0; t.time_end=23">
                                    全天生效
                                </label>
                                <div v-if="!t.allDay" class="grid grid-cols-2 gap-2">
                                    <label class="text-xs text-gray-500">起始小时
                                        <input type="number" v-model.number="t.time_start" min="0" max="23" class="border p-1 rounded w-full text-sm mt-1">
                                    </label>
                                    <label class="text-xs text-gray-500">结束小时
                                        <input type="number" v-model.number="t.time_end" min="0" max="23" class="border p-1 rounded w-full text-sm mt-1">
                                    </label>
                                </div>
                                <p class="text-[10px] text-gray-400">起始≤结束=当天时段，起始>结束=跨天（如 22~6 是深夜到凌晨）</p>
                            </div>
                            <button @click="welcomeTplEntries.push({text: '', time_start: 0, time_end: 23})" class="bg-blue-50 hover:bg-blue-100 text-blue-600 px-3 py-1 rounded text-xs font-medium">➕ 添加模板</button>
                        </div>
                        <div class="p-4 border-t flex items-center gap-2 justify-end">
                            <button @click="showWelcomeTplModal = false" class="bg-gray-200 hover:bg-gray-300 px-4 py-2 rounded text-sm">取消</button>
                            <button @click="saveWelcomeTplModal" class="bg-blue-500 hover:bg-blue-600 text-white px-4 py-2 rounded text-sm">保存</button>
                        </div>
                    </div>
                </div>

                <!-- ── UID 黑名单编辑弹窗 ── -->
                <div v-if="showUidBlacklistModal" class="fixed inset-0 bg-black/40 flex items-center justify-center z-50">
                    <div class="bg-white rounded-xl shadow-lg w-full max-w-lg mx-4 max-h-[80vh] flex flex-col" @click.stop>
                        <div class="p-4 border-b flex items-center justify-between">
                            <h3 class="font-bold text-lg">🚫 UID 黑名单</h3>
                            <button @click="closeUidBlacklistModal" class="text-gray-400 hover:text-gray-600 text-xl">✕</button>
                        </div>
                        <div class="p-4 overflow-y-auto flex-1 space-y-3">
                            <p class="text-xs text-gray-500">无视指定 UID 的所有弹幕（不影响送礼记录）。UID为空时保存自动清理。</p>
                            <div v-for="(r, ri) in uidBlacklistEdit" :key="ri" class="border rounded p-3 bg-gray-50 space-y-2">
                                <div class="flex items-center justify-between">
                                    <span class="text-xs font-bold">#{{ ri+1 }}</span>
                                    <button @click="uidBlacklistEdit.splice(ri,1)" class="bg-red-50 hover:bg-red-100 text-red-500 px-2 py-0.5 rounded text-xs font-medium">删除</button>
                                </div>
                                <label class="text-xs text-gray-500">UID<input type="number" v-model.number="r.uid" class="border p-1 rounded w-full text-sm mt-1"></label>
                                <label class="flex items-center gap-1 text-xs text-gray-500 mt-1"><input type="checkbox" v-model="r.allDay" class="w-3.5 h-3.5" @change="if(r.allDay){r.time_start=0;r.time_end=23}"> 全天生效</label>
                                <div v-if="!r.allDay" class="grid grid-cols-2 gap-2">
                                    <label class="text-xs text-gray-500">起始<input type="number" v-model.number="r.time_start" min="0" max="23" class="border p-1 rounded w-full text-sm"></label>
                                    <label class="text-xs text-gray-500">结束<input type="number" v-model.number="r.time_end" min="0" max="23" class="border p-1 rounded w-full text-sm"></label>
                                </div>
                            </div>
                            <button @click="uidBlacklistEdit.push({uid:0,time_start:0,time_end:23,allDay:true})" class="bg-blue-50 hover:bg-blue-100 text-blue-600 px-3 py-1 rounded text-xs font-medium">➕ 添加 UID</button>
                        </div>
                        <div class="p-4 border-t flex items-center gap-2 justify-end">
                            <button @click="closeUidBlacklistModal" class="bg-gray-200 hover:bg-gray-300 px-4 py-2 rounded text-sm">取消</button>
                            <button @click="saveUidBlacklistModal" class="bg-blue-500 hover:bg-blue-600 text-white px-4 py-2 rounded text-sm">保存</button>
                        </div>
                    </div>
                </div>

                <!-- ── 关键词屏蔽编辑弹窗 ── -->
                <div v-if="showKeywordFilterModal" class="fixed inset-0 bg-black/40 flex items-center justify-center z-50">
                    <div class="bg-white rounded-xl shadow-lg w-full max-w-lg mx-4 max-h-[80vh] flex flex-col" @click.stop>
                        <div class="p-4 border-b flex items-center justify-between">
                            <h3 class="font-bold text-lg">🔤 关键词屏蔽</h3>
                            <button @click="closeKeywordFilterModal" class="text-gray-400 hover:text-gray-600 text-xl">✕</button>
                        </div>
                        <div class="p-4 overflow-y-auto flex-1 space-y-3">
                            <p class="text-xs text-gray-500">限制机器人发送包含指定关键词的弹幕。空关键词条目保存时自动清理。</p>
                            <div v-for="(r, ri) in keywordFilterEdit" :key="ri" class="border rounded p-3 bg-gray-50 space-y-2">
                                <div class="flex items-center justify-between">
                                    <span class="text-xs font-bold">#{{ ri+1 }}</span>
                                    <button @click="keywordFilterEdit.splice(ri,1)" class="bg-red-50 hover:bg-red-100 text-red-500 px-2 py-0.5 rounded text-xs font-medium">删除</button>
                                </div>
                                <label class="text-xs text-gray-500">关键词<input type="text" v-model="r.keyword" class="border p-1 rounded w-full text-sm mt-1" placeholder="输入关键词"></label>
                                <div class="grid grid-cols-2 gap-2">
                                    <label class="text-xs text-gray-500">匹配<select v-model="r.match_mode" class="border p-1 rounded w-full text-sm mt-1"><option value="contains">包含</option><option value="exact">精确</option></select></label>
                                    <label class="text-xs text-gray-500">动作<select v-model="r.action" class="border p-1 rounded w-full text-sm mt-1"><option value="block">拦截不发送</option><option value="censor">关键词变*</option></select></label>
                                </div>
                                <label class="flex items-center gap-1 text-xs text-gray-500 mt-1"><input type="checkbox" v-model="r.allDay" class="w-3.5 h-3.5" @change="if(r.allDay){r.time_start=0;r.time_end=23}"> 全天生效</label>
                                <div v-if="!r.allDay" class="grid grid-cols-2 gap-2">
                                    <label class="text-xs text-gray-500">起始<input type="number" v-model.number="r.time_start" min="0" max="23" class="border p-1 rounded w-full text-sm"></label>
                                    <label class="text-xs text-gray-500">结束<input type="number" v-model.number="r.time_end" min="0" max="23" class="border p-1 rounded w-full text-sm"></label>
                                </div>
                                <p v-if="r.match_mode==='exact' && r.action==='censor'" class="text-[10px] text-yellow-600">精确+变*不会生效</p>
                            </div>
                            <button @click="keywordFilterEdit.push({keyword:'',match_mode:'contains',action:'block',allDay:true,time_start:0,time_end:23})" class="bg-blue-50 hover:bg-blue-100 text-blue-600 px-3 py-1 rounded text-xs font-medium">➕ 添加规则</button>
                        </div>
                        <div class="p-4 border-t flex items-center gap-2 justify-end">
                            <button @click="closeKeywordFilterModal" class="bg-gray-200 hover:bg-gray-300 px-4 py-2 rounded text-sm">取消</button>
                            <button @click="saveKeywordFilterModal" class="bg-blue-500 hover:bg-blue-600 text-white px-4 py-2 rounded text-sm">保存</button>
                        </div>
                    </div>
                </div>

                <!-- ── 荣耀等级欢迎多模板编辑弹窗 ── -->
                <div v-if="showHonorWelcomeTplModal" class="fixed inset-0 bg-black/40 flex items-center justify-center z-50">
                    <div class="bg-white rounded-xl shadow-lg w-full max-w-lg mx-4 max-h-[80vh] flex flex-col" @click.stop>
                        <div class="p-4 border-b flex items-center justify-between">
                            <h3 class="font-bold text-lg">🏆 荣耀等级欢迎多模板</h3>
                            <button @click="showHonorWelcomeTplModal = false" class="text-gray-400 hover:text-gray-600 text-xl">✕</button>
                        </div>
                        <div class="p-4 overflow-y-auto flex-1 space-y-3">
                            <p class="text-xs text-gray-500">每条模板可设置生效时段，机器人每次随机选一条当前时段生效的发送。</p>
                            <div v-for="(t, ti) in honorWelcomeTplEntries" :key="ti" class="border rounded p-3 bg-gray-50 space-y-2">
                                <div class="flex items-center justify-between">
                                    <span class="text-xs font-bold">模板 #{{ ti+1 }}</span>
                                    <button @click="honorWelcomeTplEntries.splice(ti, 1)" class="bg-red-50 hover:bg-red-100 text-red-500 px-2 py-0.5 rounded text-xs font-medium">删除</button>
                                </div>
                                <label class="text-xs text-gray-500">内容（支持 {uname}）
                                    <input type="text" v-model="t.text" class="border p-1 rounded w-full text-sm mt-1" placeholder="欢迎荣耀{uname}进入直播间~">
                                </label>
                                <label class="flex items-center gap-1 text-xs text-gray-500 mt-1">
                                    <input type="checkbox" v-model="t.allDay" class="w-3.5 h-3.5" @change="t.time_start=0; t.time_end=23"> 全天生效
                                </label>
                                <div v-if="!t.allDay" class="grid grid-cols-2 gap-2">
                                    <label class="text-xs text-gray-500">起始小时<input type="number" v-model.number="t.time_start" min="0" max="23" class="border p-1 rounded w-full text-sm mt-1"></label>
                                    <label class="text-xs text-gray-500">结束小时<input type="number" v-model.number="t.time_end" min="0" max="23" class="border p-1 rounded w-full text-sm mt-1"></label>
                                </div>
                            </div>
                            <button @click="honorWelcomeTplEntries.push({text: '', time_start: 0, time_end: 23})" class="bg-blue-50 hover:bg-blue-100 text-blue-600 px-3 py-1 rounded text-xs font-medium">➕ 添加模板</button>
                        </div>
                        <div class="p-4 border-t flex items-center gap-2 justify-end">
                            <button @click="showHonorWelcomeTplModal = false" class="bg-gray-200 hover:bg-gray-300 px-4 py-2 rounded text-sm">取消</button>
                            <button @click="saveHonorWelcomeTplModal" class="bg-blue-500 hover:bg-blue-600 text-white px-4 py-2 rounded text-sm">保存</button>
                        </div>
                    </div>
                </div>

                <!-- ── 大航海欢迎多模板编辑弹窗 ── -->
                <div v-if="showGuardWelcomeTplModal" class="fixed inset-0 bg-black/40 flex items-center justify-center z-50">
                    <div class="bg-white rounded-xl shadow-lg w-full max-w-lg mx-4 max-h-[80vh] flex flex-col" @click.stop>
                        <div class="p-4 border-b flex items-center justify-between">
                            <h3 class="font-bold text-lg">🛳️ 大航海欢迎多模板</h3>
                            <button @click="showGuardWelcomeTplModal = false" class="text-gray-400 hover:text-gray-600 text-xl">✕</button>
                        </div>
                        <div class="p-4 overflow-y-auto flex-1 space-y-4">
                            <p class="text-xs text-gray-500">每个等级可配置多条模板，支持时段，随机选择。</p>
                            <div v-for="(level, lk) in {'captain':'舰长','commander':'提督','governor':'总督'}" :key="lk" class="border rounded p-3 bg-gray-100">
                                <h4 class="text-xs font-bold mb-2">{{ level }} <span class="text-gray-400">({{ lk }})</span></h4>
                                <div v-for="(t, ti) in (guardWelcomeTplEntries[lk]||[])" :key="ti" class="border-t border-gray-200 pt-2 mt-2 space-y-1">
                                    <div class="flex items-center justify-between">
                                        <span class="text-[10px] text-gray-400">#{{ ti+1 }}</span>
                                        <button @click="guardWelcomeTplEntries[lk].splice(ti, 1)" class="text-red-400 text-[10px] underline">删除</button>
                                    </div>
                                    <label class="text-xs text-gray-500">内容
                                        <input type="text" v-model="t.text" class="border p-1 rounded w-full text-sm mt-1" :placeholder="'欢迎'+level+'{uname}~'">
                                    </label>
                                    <label class="flex items-center gap-1 text-[10px] text-gray-500 mt-1">
                                        <input type="checkbox" v-model="t.allDay" class="w-3 h-3" @change="t.time_start=0; t.time_end=23">
                                        全天生效
                                    </label>
                                    <div v-if="!t.allDay" class="grid grid-cols-2 gap-2">
                                        <label class="text-xs text-gray-500">起始
                                            <input type="number" v-model.number="t.time_start" min="0" max="23" class="border p-1 rounded w-full text-sm">
                                        </label>
                                        <label class="text-xs text-gray-500">结束
                                            <input type="number" v-model.number="t.time_end" min="0" max="23" class="border p-1 rounded w-full text-sm">
                                        </label>
                                    </div>
                                </div>
                                <button @click="addGuardTpl(lk)" class="bg-blue-50 hover:bg-blue-100 text-blue-600 px-2.5 py-1 rounded text-[11px] font-medium mt-1">➕ 添加{{ level }}模板</button>
                            </div>
                        </div>
                        <div class="p-4 border-t flex items-center gap-2 justify-end">
                            <button @click="showGuardWelcomeTplModal = false" class="bg-gray-200 hover:bg-gray-300 px-4 py-2 rounded text-sm">取消</button>
                            <button @click="saveGuardWelcomeTplModal" class="bg-blue-500 hover:bg-blue-600 text-white px-4 py-2 rounded text-sm">保存</button>
                        </div>
                    </div>
                </div>

                <!-- ── 定时消息多模板编辑弹窗 ── -->
                <div v-if="showPeriodicTplModal" class="fixed inset-0 bg-black/40 flex items-center justify-center z-50">
                    <div class="bg-white rounded-xl shadow-lg w-full max-w-lg mx-4 max-h-[80vh] flex flex-col" @click.stop>
                        <div class="p-4 border-b flex items-center justify-between">
                            <h3 class="font-bold text-lg">⏰ 定时消息多模板</h3>
                            <button @click="showPeriodicTplModal = false" class="text-gray-400 hover:text-gray-600 text-xl">✕</button>
                        </div>
                        <div class="p-4 overflow-y-auto flex-1 space-y-3">
                            <p class="text-xs text-gray-500">每条消息可设置生效时段，机器人每次随机选一条当前时段生效的发送。</p>
                            <div v-for="(t, ti) in periodicTplEntries" :key="ti" class="border rounded p-3 bg-gray-50 space-y-2">
                                <div class="flex items-center justify-between">
                                    <span class="text-xs font-bold">消息 #{{ ti+1 }}</span>
                                    <button @click="periodicTplEntries.splice(ti, 1)" class="bg-red-50 hover:bg-red-100 text-red-500 px-2 py-0.5 rounded text-xs font-medium">删除</button>
                                </div>
                                <label class="text-xs text-gray-500">内容
                                    <input type="text" v-model="t.text" class="border p-1 rounded w-full text-sm mt-1" placeholder="点个关注不迷路喵~">
                                </label>
                                <label class="flex items-center gap-1 text-xs text-gray-500 mt-1">
                                    <input type="checkbox" v-model="t.allDay" class="w-3.5 h-3.5" @change="t.time_start=0; t.time_end=23">
                                    全天生效
                                </label>
                                <div v-if="!t.allDay" class="grid grid-cols-2 gap-2">
                                    <label class="text-xs text-gray-500">起始小时
                                        <input type="number" v-model.number="t.time_start" min="0" max="23" class="border p-1 rounded w-full text-sm mt-1">
                                    </label>
                                    <label class="text-xs text-gray-500">结束小时
                                        <input type="number" v-model.number="t.time_end" min="0" max="23" class="border p-1 rounded w-full text-sm mt-1">
                                    </label>
                                </div>
                                <p class="text-[10px] text-gray-400">起始≤结束=当天，起始>结束=跨天（如 22~6）</p>
                            </div>
                            <button @click="periodicTplEntries.push({text: '', time_start: 0, time_end: 23})" class="bg-blue-50 hover:bg-blue-100 text-blue-600 px-3 py-1 rounded text-xs font-medium">➕ 添加消息</button>
                        </div>
                        <div class="p-4 border-t flex items-center gap-2 justify-end">
                            <button @click="showPeriodicTplModal = false" class="bg-gray-200 hover:bg-gray-300 px-4 py-2 rounded text-sm">取消</button>
                            <button @click="savePeriodicTplModal" class="bg-blue-500 hover:bg-blue-600 text-white px-4 py-2 rounded text-sm">保存</button>
                        </div>
                    </div>
                </div>

                <!-- ── 签文多文本编辑弹窗 ── -->
                <div v-if="showFortuneTplModal" class="fixed inset-0 bg-black/40 flex items-center justify-center z-50">
                    <div class="bg-white rounded-xl shadow-lg w-full max-w-lg mx-4 max-h-[80vh] flex flex-col" @click.stop>
                        <div class="p-4 border-b flex items-center justify-between">
                            <h3 class="font-bold text-lg">🎴 签文编辑</h3>
                            <button @click="showFortuneTplModal = false" class="text-gray-400 hover:text-gray-600 text-xl">✕</button>
                        </div>
                        <div class="p-4 overflow-y-auto flex-1 space-y-4">
                            <p class="text-xs text-gray-500">每个类型可添加多条签文，抽签时随机选一条使用。留空则使用默认签文。</p>
                            <div v-for="(ft, fti) in fortuneTypes" :key="ft.key" class="border rounded p-3 bg-gray-50">
                                <h4 class="text-xs font-bold mb-1">{{ ft.label }}</h4>
                                <div v-for="(txt, txi) in (fortuneTplEntries[ft.key]||[])" :key="txi" class="flex items-center gap-2 mb-1">
                                    <input type="text" v-model="fortuneTplEntries[ft.key][txi]" class="border p-1 rounded w-full text-sm" :placeholder="ft.placeholder">
                                    <button @click="fortuneTplEntries[ft.key].splice(txi, 1)" class="bg-red-50 hover:bg-red-100 text-red-500 px-2 py-0.5 rounded text-xs font-medium shrink-0">删</button>
                                </div>
                                <button @click="addFortuneText(ft.key)" class="text-blue-500 text-[10px] underline mt-1">➕ 添加{{ ft.label }}签文</button>
                            </div>
                        </div>
                        <div class="p-4 border-t flex items-center gap-2 justify-end">
                            <button @click="showFortuneTplModal = false" class="bg-gray-200 hover:bg-gray-300 px-4 py-2 rounded text-sm">取消</button>
                            <button @click="saveFortuneTplModal" class="bg-blue-500 hover:bg-blue-600 text-white px-4 py-2 rounded text-sm">保存</button>
                        </div>
                    </div>
                </div>

                <hr>
                <h3 class="text-sm font-bold">🎴 自定义签文</h3>
                <p class="text-xs text-gray-500">修改 #抽签 命令的签文内容。每个类型可填多条，随机选。留空用默认。</p>
                <div class="border rounded p-3 bg-gray-50 flex items-center justify-between">
                    <span class="text-xs text-gray-500">📋 全部签文共 {{ fortuneTotalEntries }} 条</span>
                    <button @click="openFortuneTplModal" class="bg-blue-50 hover:bg-blue-100 text-blue-600 px-2.5 py-1 rounded text-xs font-medium">✏️ 编辑</button>
                </div>

                <div class="flex items-center gap-4 mt-4 flex-wrap">
                    <button @click="saveRoomConfig" class="bg-blue-500 hover:bg-blue-600 text-white px-6 py-2 rounded text-sm">保存</button>
                    <button @click="exportRoomConfig()" class="bg-green-500 hover:bg-green-600 text-white px-4 py-2 rounded text-sm">📤 导出配置</button>
                    <button @click="importRoomConfig()" class="bg-orange-500 hover:bg-orange-600 text-white px-4 py-2 rounded text-sm">📥 导入配置</button>
                    <select v-model="applyBotTemplate" class="border p-1 rounded text-xs">
                        <option value="">套用模板...</option>
                        <option v-for="t in botTemplates" :key="t.name" :value="t.name">{{ t.name }}</option>
                    </select>
                    <button v-if="applyBotTemplate" @click="applyTemplateToBot" class="bg-purple-500 hover:bg-purple-600 text-white px-2.5 py-1 rounded text-xs">应用</button>
                    <span v-if="roomSaveMsg" class="text-sm" :class="roomSaveOk ? 'text-green-600' : 'text-red-500'">{{ roomSaveMsg }}</span>
                    <span v-if="roomSaveOk" class="text-xs text-yellow-600">💡 更改配置后需重启机器人才能生效</span>
                    <span v-if="applyTemplateMsg" class="text-xs" :class="applyTemplateOk ? 'text-green-600' : 'text-red-500'">{{ applyTemplateMsg }}</span>
                </div>
                <div class="flex items-center gap-3 mt-2 flex-wrap">
                    <button v-if="selectedRoom" @click="restartSingleBot(selectedRoom.room_id)" class="bg-yellow-500 hover:bg-yellow-600 text-white px-3 py-2 rounded text-sm text-xs">🔄 重启此机器人</button>
                    <button @click="editRoomConfig(selectedRoom?.room_id)" class="bg-gray-200 hover:bg-gray-300 text-gray-700 px-3 py-2 rounded text-sm text-xs">🔄 刷新</button>
                </div>
            </div>
        </div>

        <!-- 数据管理 -->
        <div v-if="roomSubTab==='manage'" class="max-w-full sm:max-w-lg mx-auto space-y-4">
            <!-- API 外部接口配置 -->
            <div class="bg-white p-4 sm:p-6 rounded-xl shadow-sm" :class="{'opacity-60': !roomApiEnabled}">
                <div class="flex items-center justify-between mb-3">
                    <h2 class="text-lg font-bold">🔌 API 外部接口</h2>
                    <!-- 开关 -->
                    <label class="relative inline-flex items-center cursor-pointer">
                        <input type="checkbox" class="sr-only peer" :checked="roomApiEnabled" @change="toggleRoomApi">
                        <div class="w-11 h-6 bg-gray-200 peer-focus:outline-none peer-focus:ring-2 peer-focus:ring-blue-300 rounded-full peer peer-checked:after:translate-x-full rtl:peer-checked:after:-translate-x-full peer-checked:after:border-white after:content-[''] after:absolute after:top-[2px] after:start-[2px] after:bg-white after:border-gray-300 after:border after:rounded-full after:h-5 after:w-5 after:transition-all peer-checked:bg-blue-600"></div>
                        <span class="ms-3 text-sm font-medium" :class="roomApiEnabled ? 'text-green-600' : 'text-gray-400'">{{ roomApiEnabled ? '已开启' : '已关闭' }}</span>
                    </label>
                </div>
                <p class="text-xs text-gray-500 mb-3">
                    供 AstrBot 插件等第三方服务按房间查询礼物/盲盒数据。
                    <a href="https://github.com/yujianke100/Ayabot-astrbot-plugin" target="_blank" class="text-blue-500 hover:underline">查看插件</a>
                </p>

                <template v-if="roomApiEnabled">
                    <!-- API 地址 -->
                    <label class="text-xs text-gray-500 mt-3 block">API 地址
                        <div class="flex items-center mt-1">
                            <input type="text" :value="roomApiUrl" readonly class="border p-2 rounded-l w-full text-sm bg-gray-50 font-mono text-xs" @click="copyText(roomApiUrl, 'apiMsg')">
                            <button @click="copyText(roomApiUrl, 'apiMsg')" class="bg-gray-200 hover:bg-gray-300 px-3 py-2 rounded-r text-sm border-l-0" title="复制">📋</button>
                        </div>
                        <span class="text-xs text-gray-400">将以上地址和下方密钥填入插件配置</span>
                    </label>

                    <!-- 密钥 -->
                    <label class="text-xs text-gray-500 mt-3 block">API 密钥
                        <div class="flex items-center mt-1">
                            <input type="text" :value="roomApiFullKey" readonly class="border p-2 rounded-l w-full text-sm bg-gray-50 font-mono text-xs select-all">
                            <button @click="copyText(roomApiFullKey, 'apiMsg')" class="bg-gray-200 hover:bg-gray-300 px-3 py-2 rounded-r text-sm border-l-0" title="复制">📋</button>
                        </div>
                        <span class="text-xs text-gray-400">点击 📋 复制密钥</span>
                    </label>

                    <!-- 操作按钮 -->
                    <div class="flex items-center gap-2 mt-3">
                        <button @click="regenerateRoomApiKey" class="bg-blue-500 hover:bg-blue-600 text-white px-4 py-2 rounded text-sm" :disabled="roomApiBusy">
                            {{ roomApiBusy ? '处理中...' : '🔄 重新生成密钥' }}
                        </button>
                    </div>
                </template>

                <template v-else>
                    <div class="py-6 text-center text-gray-400 text-sm">API 接口已关闭，开启后即可查看地址和密钥</div>
                </template>

                <div v-if="apiMsg" class="mt-2 text-sm" :class="apiMsgOk ? 'text-green-600' : 'text-red-500'">{{ apiMsg }}</div>
            </div>

            <!-- 数据删除 -->
            <div class="bg-white p-4 sm:p-6 rounded-xl shadow-sm">
                <h2 class="text-lg font-bold mb-4 text-red-600">⚠️ 数据管理</h2>
                <p class="text-sm text-gray-500 mb-4">注意：删除操作不可恢复。礼物数据保留天数在「机器人配置 → 数据保留」中设置。</p>
                <div class="flex items-end gap-2">
                    <label class="text-xs text-gray-500 flex-1">日期<input type="date" v-model="delDate" class="border p-2 rounded w-full text-sm mt-1"></label>
                    <button @click="confirmDelete('gift')" class="bg-red-500 hover:bg-red-600 text-white px-3 py-2 rounded text-sm h-[38px]">删除送礼</button>
                    <button @click="confirmDelete('danmaku')" class="bg-red-500 hover:bg-red-600 text-white px-3 py-2 rounded text-sm h-[38px]">删除弹幕</button>
                </div>
                <div v-if="delResult" class="mt-4 text-sm">{{ delResult }}</div>
            </div>
        </div>

        <!-- Bot 日志 -->
        <div v-if="roomSubTab==='log'" class="max-w-full sm:max-w-4xl mx-auto">
            <div class="bg-white p-4 sm:p-6 rounded-xl shadow-sm space-y-4">
                <div class="flex flex-col sm:flex-row sm:items-center sm:justify-between gap-2">
                    <h2 class="text-lg font-bold whitespace-nowrap">📋 Bot 日志</h2>
                    <div class="flex items-center gap-2 flex-wrap">
                        <span class="text-xs text-gray-400 w-full sm:w-auto sm:mr-1">日志级别在「机器人配置」中修改，重启后生效</span>
                        <button @click="clearBotLog" class="bg-red-500 hover:bg-red-600 text-white px-3 py-2 rounded text-sm whitespace-nowrap">清空</button>
                        <button @click="downloadUrl('/api/rooms/'+selectedRoom.room_id+'/log/export', 'bot_'+selectedRoom.room_id+'.log')" class="bg-green-500 hover:bg-green-600 text-white px-3 py-2 rounded text-sm whitespace-nowrap">📤 导出</button>
                        <button @click="loadBotLog" class="bg-blue-500 hover:bg-blue-600 text-white px-4 py-2 rounded text-sm whitespace-nowrap">刷新</button>
                    </div>
                </div>
                <div ref="logContainer" class="bg-gray-900 text-green-300 p-4 rounded text-xs font-mono max-h-[600px] overflow-y-auto whitespace-pre-wrap" v-html="botLogContent"></div>
                <div v-if="!botLogContent" class="text-gray-400 text-center py-4">暂无日志或日志文件不存在</div>
            </div>
        </div>

        <!-- 弹幕记录 -->
        <div v-if="roomSubTab==='danmaku'" class="max-w-full sm:max-w-4xl mx-auto">
            <div class="bg-white p-4 sm:p-6 rounded-xl shadow-sm space-y-4">
                <div class="flex items-center justify-between">
                    <h2 class="gb-card-title text-lg font-bold">💬 弹幕记录</h2>
                    <div class="flex items-center gap-2">
                        <button @click="dmExportSelected" class="bg-green-500 hover:bg-green-600 text-white px-3 py-2 rounded text-sm">📤 导出CSV</button>
                        <button @click="clearDanmakuLog" class="bg-red-500 hover:bg-red-600 text-white px-3 py-2 rounded text-sm">清空</button>
                        <button @click="loadDanmakuLog" class="bg-blue-500 hover:bg-blue-600 text-white px-4 py-2 rounded text-sm">刷新</button>
                    </div>
                </div>

                <!-- 工具区：时间范围 / 搜索 / 用户 / 场次 分组排列 -->
                <div class="relative">
                    <div class="dm-toolbar rounded-xl border border-gray-200 bg-gray-50/60 divide-y divide-gray-100">
                        <!-- 时间范围 + 排序 -->
                        <div class="dm-toolbar-row flex items-start gap-3 px-3 py-2 flex-wrap">
                            <span class="dm-toolbar-label w-16 shrink-0 text-xs text-gray-400 leading-8">时间范围</span>
                            <div class="flex items-center gap-2 flex-wrap">
                                <button @click="dmToggleCal($event)" class="border px-3 py-2 rounded text-sm bg-white hover:bg-gray-50">
                                    {{ dmSelectedDates.size ? '已选 '+dmSelectedDates.size+' 天' : '点击选择日期' }}
                                    <span v-if="dmDateFrom && dmDateTo && dmDateFrom !== dmDateTo" class="text-gray-400 ml-1">({{ dmDateFrom }} ~ {{ dmDateTo }})</span>
                                    <span v-else-if="dmDateFrom" class="text-gray-400 ml-1">({{ dmDateFrom }})</span>
                                </button>
                                <button @click="dmAsc = !dmAsc; loadDanmakuLog()" class="border px-3 py-2 rounded text-sm bg-white hover:bg-gray-50" :title="dmAsc ? '旧到新' : '新到旧'">
                                    {{ dmAsc ? '📅 旧→新' : '📅 新→旧' }}
                                </button>
                            </div>
                            <span class="text-xs text-gray-400 self-center ml-auto">{{ dmDates.length }} 天有数据，点击日期可多选</span>
                        </div>
                        <!-- 搜索 + 录像 -->
                        <div class="dm-toolbar-row flex items-start gap-3 px-3 py-2 flex-wrap">
                            <span class="dm-toolbar-label w-16 shrink-0 text-xs text-gray-400 leading-8">搜索</span>
                            <div class="flex items-center gap-2 flex-wrap">
                                <div class="flex items-center gap-1">
                                    <input type="text" v-model="dmKeyword" placeholder="🔍 搜索用户名/内容"
                                           class="border p-2 rounded text-sm w-52 bg-white focus:outline-none focus:ring-2 focus:ring-blue-300"
                                           @keyup.enter="dmSearch" @keyup.esc="clearDmSearch">
                                    <button @click="dmSearch" class="bg-blue-500 hover:bg-blue-600 text-white px-3 py-2 rounded text-sm whitespace-nowrap">搜索</button>
                                    <button v-if="dmSearchActive" @click="clearDmSearch" class="px-2 py-2 rounded text-sm text-gray-500 hover:bg-gray-100" title="清除搜索">✕</button>
                                </div>
                                <div class="flex items-center gap-2 pl-2 border-l border-gray-200">
                                    <span class="text-xs text-gray-400">相邻弹幕间隔更大</span>
                                    <select v-model="dmGap" @change="restartSessions" class="border px-2 py-2 rounded text-sm bg-white focus:outline-none focus:ring-2 focus:ring-blue-300" title="两条相邻弹幕间隔超过该时长即视为新的一场录像">
                                        <option v-for="o in dmGapOptions" :key="o.v" :value="o.v">{{ o.label }}</option>
                                    </select>
                                    <span class="text-xs text-gray-400">算新录像</span>
                                    <label class="flex items-center gap-1 text-sm text-gray-600 cursor-pointer select-none" title="显示/隐藏弹幕对应的录像时间列">
                                        <input type="checkbox" v-model="dmShowRec" class="accent-purple-600"> 显示弹幕对应的录像时间
                                    </label>
                                </div>
                            </div>
                        </div>
                        <!-- 用户筛选 + 统计 -->
                        <div class="dm-toolbar-row flex items-start gap-3 px-3 py-2 flex-wrap">
                            <span class="dm-toolbar-label w-16 shrink-0 text-xs text-gray-400 leading-8">用户</span>
                            <div class="flex items-center gap-2 flex-wrap">
                                <select v-model="dmUserFilter" @change="dmUidFilter=''; danmakuOffset=0; dmSessionIdx=-1; loadDanmakuLog(); loadDanmakuUsers(); loadDanmakuSessions(); if(dmShowStats) loadDanmakuStats();"
                                        class="border px-2 py-2 rounded text-sm bg-white focus:outline-none focus:ring-2 focus:ring-blue-300 max-w-[200px]" title="按用户名筛选(模糊)">
                                    <option value="">全部用户</option>
                                    <option v-for="u in dmUsers" :key="u.uid" :value="u.uname">{{ u.uname }} ({{ u.count }})</option>
                                </select>
                                <input type="text" v-model="dmUidFilter" placeholder="UID 精确筛选"
                                       class="border px-2 py-2 rounded text-sm bg-white w-36 focus:outline-none focus:ring-2 focus:ring-blue-300"
                                       @keyup.enter="dmUserFilter=''; danmakuOffset=0; dmSessionIdx=-1; loadDanmakuLog(); loadDanmakuSessions(); if(dmShowStats) loadDanmakuStats()">
                                <button v-if="dmUserFilter || dmUidFilter" @click="clearDmFilters" class="px-2 py-1.5 rounded text-xs text-gray-500 hover:bg-gray-100" title="清除用户/UID筛选">✕</button>
                                <button @click="dmShowStats = !dmShowStats; if(dmShowStats) loadDanmakuStats()"
                                        class="border px-3 py-2 rounded text-sm bg-white hover:bg-gray-50"
                                        :class="dmShowStats ? 'ring-2 ring-blue-300 bg-blue-50 text-blue-700' : ''">📊 弹幕统计</button>
                            </div>
                        </div>
                        <!-- 直播场次 -->
                        <div class="dm-toolbar-row flex items-start gap-3 px-3 py-2 flex-wrap">
                            <span class="dm-toolbar-label w-16 shrink-0 text-xs text-gray-400 leading-8">场次</span>
                            <div class="flex items-center gap-2 flex-wrap">
                                <div class="relative dm-sess-picker">
                                    <button @click.prevent="dmToggleSessionPanel"
                                            class="dm-sess-trigger border px-2 py-2 rounded text-sm bg-white focus:outline-none focus:ring-2 focus:ring-blue-300 whitespace-nowrap"
                                            title="搜索并选择某一场直播查看其弹幕,替代按日期选择">
                                        <span v-if="dmSessionIdx < 0" class="text-gray-400">全部(按日期)</span>
                                        <span v-else class="text-gray-800">{{ dmSessCurLabel }}</span>
                                        <span class="text-gray-400 ml-1">▾</span>
                                    </button>
                                    <!-- 可搜索场次列表面板 -->
                                    <div v-if="dmShowSessionPanel"
                                         class="absolute top-full left-0 mt-1 w-80 bg-white border rounded-xl shadow-lg z-50 flex flex-col"
                                         @click.stop>
                                        <div class="p-2 border-b border-gray-100">
                                            <input v-model="dmSessionQuery" type="text" placeholder="🔍 搜索日期/时间段/条数…"
                                                   class="w-full border p-2 rounded-lg text-sm bg-white focus:outline-none focus:ring-2 focus:ring-blue-300"
                                                   @keyup.esc="dmShowSessionPanel=false">
                                        </div>
                                        <div class="max-h-64 overflow-y-auto py-1">
                                            <button v-for="(s,i) in dmSessionFiltered" :key="s.start"
                                                    @click="dmPickSession(i)"
                                                    class="w-full text-left px-3 py-2 hover:bg-blue-50 text-sm transition-colors"
                                                    :class="i === dmSessionIdx ? 'bg-blue-50 text-blue-700' : 'text-gray-700'">
                                                <div class="flex items-center justify-between">
                                                    <span class="font-medium">场次{{ i+1 }}</span>
                                                    <span class="text-xs text-gray-400">{{ dmSessionLabel(s) }}</span>
                                                </div>
                                                <div class="flex items-center justify-between mt-0.5">
                                                    <span class="text-xs text-purple-600 font-mono">{{ s.count }} 条</span>
                                                    <span v-if="i === dmSessionIdx" class="text-blue-600 text-xs">✓ 已选</span>
                                                </div>
                                            </button>
                                            <div v-if="!dmSessionFiltered.length" class="px-3 py-6 text-center text-sm text-gray-400">没有匹配的场次</div>
                                        </div>
                                        <div class="p-2 border-t border-gray-100">
                                            <button @click="dmPickSession(-1)" class="w-full text-center text-sm text-gray-500 hover:text-blue-600 py-1">↺ 全部(按日期)</button>
                                        </div>
                                    </div>
                                </div>
                                <button v-if="dmSessionIdx >= 0" @click="dmSessionIdx=-1; danmakuOffset=0; loadDanmakuLog(); loadDanmakuSessions(changed=true)" class="px-2 py-1.5 rounded text-xs text-gray-500 hover:bg-gray-100" title="清除场次筛选,回到按日期">✕</button>
                                <button @click="loadDanmakuSessions(true)" class="border px-3 py-2 rounded text-sm bg-white hover:bg-gray-50" title="重新加载直播场次列表">⟳ 刷新场次</button>
                            </div>
                        </div>
                    </div>
                    <Teleport to="body">
                    <div v-if="dmShowCal" @click.stop class="cal-pop bg-white rounded-xl shadow-lg p-3 w-[320px]" :style="{position:'fixed', top:(dmCalPos.top)+'px', left:(dmCalPos.left)+'px', zIndex:2147483000}">
                        <div class="flex justify-between items-center mb-2">
                            <button @click="dmCalMonth--" type="button" class="px-2 py-1 hover:bg-gray-100 rounded text-sm">&lt;</button>
                            <span class="text-sm font-bold">{{ dmCalYear }}年{{ dmCalMonth+1 }}月</span>
                            <button @click="dmCalMonth++" type="button" class="px-2 py-1 hover:bg-gray-100 rounded text-sm">&gt;</button>
                        </div>
                        <div class="flex gap-1 mb-2">
                            <button @click="dmSelectAllMonth" type="button" class="text-[10px] px-2 py-1 bg-blue-50 text-blue-600 rounded hover:bg-blue-100">全选当月</button>
                            <button @click="dmClearDates" type="button" class="text-[10px] px-2 py-1 bg-gray-50 text-gray-500 rounded hover:bg-gray-100">清除</button>
                            <button v-if="dmSelectedDates.size>=1" @click="dmCalOk" type="button" class="text-[10px] px-2 py-1 bg-green-50 text-green-600 rounded hover:bg-green-100 font-semibold ml-auto">
                                确定（{{ dmSelectedDates.size }}天）
                            </button>
                        </div>
                        <div class="grid grid-cols-7 gap-1 text-center text-xs mb-1">
                            <div class="text-gray-400 font-medium">日</div><div class="text-gray-400 font-medium">一</div><div class="text-gray-400 font-medium">二</div><div class="text-gray-400 font-medium">三</div><div class="text-gray-400 font-medium">四</div><div class="text-gray-400 font-medium">五</div><div class="text-gray-400 font-medium">六</div>
                        </div>
                        <div class="grid grid-cols-7 gap-1">
                            <template v-for="(day,i) in dmCalDays" :key="i">
                                <div v-if="!day" class="h-8"></div>
                                <button v-else type="button" :disabled="!day.hasData" @click="dmToggleDate(day.ymd)"
                                        class="h-8 rounded text-xs transition relative"
                                        :class="day.hasData
                                            ? (day.selected ? 'bg-blue-500 text-white' : 'bg-blue-100 text-blue-700 hover:bg-blue-200 cursor-pointer')
                                            : 'text-gray-300 cursor-not-allowed'">
                                    {{ day.d }}
                                </button>
                            </template>
                        </div>
                        <div class="text-[10px] text-gray-400 mt-2 text-center">蓝色 = 有数据，深蓝 = 已选中</div>
                    </div>
                    </Teleport>
                </div>

                <div v-if="danmakuErr" class="text-red-500 text-sm">{{ danmakuErr }}</div>

                <!-- 弹幕统计面板 -->
                <div v-if="dmShowStats && dmStats" class="dm-stats-card mb-3 p-4">
                    <div class="gb-card-title text-sm font-bold text-blue-800 mb-3">📊 弹幕统计</div>
                    <div class="grid grid-cols-2 sm:grid-cols-4 gap-2 text-center mb-3">
                        <div class="bg-white rounded-xl p-3 shadow-sm">
                            <div class="text-xl font-bold text-blue-700">{{ dmStats.total }}</div>
                            <div class="text-[10px] text-gray-400 mt-0.5">弹幕总数</div>
                        </div>
                        <div class="bg-white rounded-xl p-3 shadow-sm">
                            <div class="text-xl font-bold text-blue-700">{{ dmStats.distinct_users }}</div>
                            <div class="text-[10px] text-gray-400 mt-0.5">发言用户数</div>
                        </div>
                        <div class="bg-white rounded-xl p-3 shadow-sm">
                            <div class="text-xl font-bold text-purple-600">{{ dmStats.top_users.length }}</div>
                            <div class="text-[10px] text-gray-400 mt-0.5">活跃TOP</div>
                        </div>
                        <div class="bg-white rounded-xl p-3 shadow-sm">
                            <div class="text-xl font-bold text-amber-600">{{ dmStats.hours.length }}</div>
                            <div class="text-[10px] text-gray-400 mt-0.5">活跃小时段</div>
                        </div>
                    </div>
                    <div class="grid grid-cols-1 sm:grid-cols-2 gap-3 text-xs">
                        <div>
                            <div class="font-semibold text-gray-700 mb-1.5">🏆 发言最活跃 TOP{{ Math.min(5, dmStats.top_users.length) }} 用户</div>
                            <div class="space-y-1">
                                <div v-for="(u,i) in dmStats.top_users.slice(0,5)" :key="u.uid"
                                     class="flex items-center justify-between bg-white rounded-lg px-2.5 py-1.5 shadow-sm">
                                    <span class="text-gray-700"><b class="text-amber-500">{{ i+1 }}.</b> {{ u.uname }}</span>
                                    <span class="text-gray-500 font-medium">{{ u.count }} 条</span>
                                </div>
                            </div>
                        </div>
                        <div>
                            <div class="font-semibold text-gray-700 mb-1.5">🕐 逐小时活跃分布</div>
                            <div class="space-y-1.5">
                                <div v-for="h in dmStats.hours" :key="h.hour" class="flex items-center gap-2">
                                    <span class="w-10 text-gray-500 text-right">{{ String(h.hour).padStart(2,'0') }}:00</span>
                                    <div class="flex-1 bg-gray-100 rounded-full h-2.5 overflow-hidden">
                                        <div class="h-full bg-gradient-to-r from-blue-500 to-purple-500 rounded-full" :style="'width:'+ barPct(h.count) + '%'"></div>
                                    </div>
                                    <span class="text-gray-400 w-8 text-left">{{ h.count }}</span>
                                </div>
                            </div>
                        </div>
                    </div>
                </div>

                <!-- 弹幕表格 -->
                <div v-if="danmakuRows.length" class="overflow-x-auto">
                    <div v-if="dmSearchActive" class="flex items-center gap-2 mb-3 text-xs bg-blue-50 text-blue-700 px-3 py-2 rounded-lg">
                        <span>🔎 正在搜索「{{ dmSearchActive }}」</span>
                        <span class="text-blue-400">匹配 {{ danmakuTotal }} 条</span>
                        <button @click="clearDmSearch" class="ml-auto hover:underline">清除搜索</button>
                    </div>
                    <div class="dm-table-wrap">
                        <table class="gb-table w-full text-sm">
                            <thead><tr><th v-if="dmShowRec" class="p-2 text-left">录像时间</th><th class="p-2 text-left">时间</th><th class="p-2 text-left">用户</th><th class="p-2 text-left">UID</th><th class="p-2 text-left">内容</th></tr></thead>
                            <tbody>
                                <tr v-for="(r,ri) in danmakuRows" :key="r.id" class="align-top"
                                    :class="{'bg-purple-50/60': ri>0 && dmShowRec && danmakuRows[ri-1].sess !== r.sess}">
                                    <td v-if="dmShowRec" class="p-2 whitespace-nowrap">
                                        <span v-if="ri===0 || danmakuRows[ri-1].sess !== r.sess" class="dm-sess-badge mb-1">🎬 第 {{ r.sess }} 场</span>
                                        <div class="text-xs dm-rel-time">{{ fmtRelTime(r.rel) }}</div>
                                    </td>
                                    <td class="p-2 whitespace-nowrap text-xs text-gray-500">{{ fmtDanmakuTime(r.ts) }}</td>
                                    <td class="p-2 font-medium whitespace-nowrap" v-html="highlightDanmaku(r.uname)"></td>
                                    <td class="p-2 text-xs text-gray-400 whitespace-nowrap">{{ r.uid }}</td>
                                    <td class="p-2 whitespace-pre-wrap break-words min-w-[200px] max-w-xl" v-html="highlightDanmaku(r.content)"></td>
                                </tr>
                            </tbody>
                        </table>
                    </div>
                    <div class="flex items-center justify-between mt-4 text-sm">
                        <div class="text-gray-500">共 {{ danmakuTotal }} 条</div>
                        <div class="flex gap-2 items-center">
                            <button @click="danmakuOffset = Math.max(0, danmakuOffset - danmakuLimit)"
                                    :disabled="danmakuOffset === 0"
                                    class="dm-page-btn px-3 py-1 rounded border text-sm"
                                    :class="danmakuOffset === 0 ? 'text-gray-300 cursor-not-allowed' : 'hover:bg-gray-100'">上一页</button>
                            <span class="text-gray-500">第 {{ danmakuPage }} 页</span>
                            <button @click="danmakuOffset += danmakuLimit"
                                    :disabled="danmakuOffset + danmakuLimit >= danmakuTotal"
                                    class="dm-page-btn px-3 py-1 rounded border text-sm"
                                    :class="danmakuOffset + danmakuLimit >= danmakuTotal ? 'text-gray-300 cursor-not-allowed' : 'hover:bg-gray-100'">下一页</button>
                        </div>
                    </div>
                </div>
                <div v-else-if="!danmakuErr" class="text-gray-400 text-center py-8">暂无弹幕记录</div>
            </div>
        </div>
    </div>
</div>

<!-- ══════ B站账号管理（已合并到 用户管理） ══════ -->

<!-- ══════ 全局配置 ══════ -->
<div v-if="tab==='global'" class="max-w-3xl mx-auto">
    <div class="bg-white p-6 rounded-xl shadow-sm space-y-4">
        <h2 class="page-title">⚙️ 全局配置</h2>
        <div class="text-sm space-y-2">
            <div class="flex items-center gap-2">
                <span class="text-gray-500">Web 端口:</span>
                <span class="font-mono font-bold">{{ cfgPort }}</span>
            </div>
            <div class="flex items-center gap-2">
                <span class="text-gray-500">监听地址:</span>
                <span class="font-mono">{{ cfgHost }}</span>
            </div>
        </div>
        <div class="bg-yellow-50 border border-yellow-200 rounded p-3 text-xs text-yellow-700">
            💡 端口和监听地址通过 <code class="bg-yellow-100 px-1 rounded">config.yaml</code> 或环境变量
            <code class="bg-yellow-100 px-1 rounded">AYABOT_PORT</code> 配置，修改后需重启服务生效。
        </div>
    </div>

    <!-- ══════ 预设模板 ══════ -->
    <div class="bg-white p-6 rounded-xl shadow-sm space-y-4 mt-4">
        <div class="flex items-center justify-between">
            <h2 class="page-title">📋 预设模板</h2>
            <div class="flex gap-2">
                <button @click="showAddTemplate = 'llm'" class="bg-blue-500 hover:bg-blue-600 text-white px-3 py-1.5 rounded text-xs">➕ AI模板</button>
                <button @click="showAddTemplate = 'bot'" class="bg-green-500 hover:bg-green-600 text-white px-3 py-1.5 rounded text-xs">➕ 机器人模板</button>
            </div>
        </div>
        <p class="text-xs text-gray-500">新建直播间时可选择预设模板快速配置。</p>

        <!-- AI模板列表 -->
        <div>
            <h3 class="text-sm font-bold mb-2">🤖 AI回复模板</h3>
            <div v-if="llmTemplates.length === 0" class="text-xs text-gray-400 py-2">暂无模板</div>
            <div v-for="(t, ti) in llmTemplates" :key="ti" class="border rounded p-3 flex items-center justify-between mb-2">
                <div>
                    <span class="font-bold text-sm">{{ t.name }}</span>
                    <span class="text-xs text-gray-400 ml-2">{{ t.config.model || t.config.provider || '' }}</span>
                </div>
                <button @click="deleteTemplate('llm', t.name)" class="bg-red-50 hover:bg-red-100 text-red-500 px-3 py-1 rounded text-xs font-medium">删除</button>
            </div>
        </div>

        <!-- 机器人模板列表 -->
        <div>
            <h3 class="text-sm font-bold mb-2">🤖 机器人配置模板</h3>
            <div v-if="botTemplates.length === 0" class="text-xs text-gray-400 py-2">暂无模板</div>
            <div v-for="(t, ti) in botTemplates" :key="ti" class="border rounded p-3 flex items-center justify-between mb-2">
                <div>
                    <span class="font-bold text-sm">{{ t.name }}</span>
                    <span class="text-xs text-gray-400 ml-2">{{ Object.keys(t.config).length }} 项配置</span>
                </div>
                <button @click="deleteTemplate('bot', t.name)" class="bg-red-50 hover:bg-red-100 text-red-500 px-3 py-1 rounded text-xs font-medium">删除</button>
            </div>
        </div>

        <!-- 添加模板弹窗 -->
        <div v-if="showAddTemplate" class="fixed inset-0 bg-black/40 flex items-center justify-center z-50">
            <div class="bg-white rounded-xl shadow-lg w-full max-w-lg mx-4" @click.stop>
                <div class="p-4 border-b flex items-center justify-between">
                    <h3 class="font-bold text-lg">📋 {{ showAddTemplate === 'llm' ? 'AI回复模板' : '机器人配置模板' }}</h3>
                    <button @click="showAddTemplate = null" class="text-gray-400 hover:text-gray-600 text-xl">✕</button>
                </div>
                <div class="p-4 space-y-3">
                    <label class="text-xs text-gray-500 block">模板名称
                        <input type="text" v-model="templateFormName" class="border p-2 rounded w-full text-sm mt-1" placeholder="例如：标准AI配置">
                    </label>
                    <div class="text-xs text-gray-500">
                        从已有房间导入配置：
                        <select v-model="templateFormImportRoom" class="border p-2 rounded w-full text-sm mt-1">
                            <option value="">请选择房间...</option>
                            <option v-for="r in rooms" :key="r.room_id" :value="r.room_id">#{{ r.room_id }} {{ r.room_name || '' }}</option>
                        </select>
                    </div>
                    <button @click="saveTemplate" :disabled="savingTemplate"
                            class="bg-blue-500 hover:bg-blue-600 text-white px-4 py-2 rounded text-sm">
                        {{ savingTemplate ? '保存中...' : '保存模板' }}
                    </button>
                    <div v-if="templateFormMsg" class="text-sm" :class="templateFormOk ? 'text-green-600' : 'text-red-500'">{{ templateFormMsg }}</div>
                </div>
            </div>
        </div>
    </div>

    <!-- ══════ 全局控制 ══════ -->
    <div class="bg-white p-6 rounded-xl shadow-sm space-y-4 mt-4">
        <h2 class="page-title">🔄 全局控制</h2>
        <div class="flex flex-wrap gap-3 items-center">
            <button @click="restartAllBots" :disabled="restartingAll"
                    class="bg-yellow-500 hover:bg-yellow-600 text-white px-5 py-2 rounded text-sm">
                {{ restartingAll ? '重启中...' : '🔄 重启所有机器人' }}
            </button>
            <span v-if="restartAllMsg" class="text-sm" :class="restartAllOk ? 'text-green-600' : 'text-red-500'">{{ restartAllMsg }}</span>
        </div>
    </div>
</div>

<!-- ══════ 用户管理 ══════ -->
<div v-if="tab==='users'" class="max-w-full sm:max-w-3xl mx-auto px-2 sm:px-0">
    <div class="bg-white p-4 sm:p-6 rounded-xl shadow-sm space-y-4">
        <div class="flex items-center justify-between">
            <h2 class="page-title">👥 用户管理</h2>
            <button @click="openAddUser" class="bg-gradient-to-r from-emerald-500 to-teal-500 hover:from-emerald-600 hover:to-teal-600 text-white px-4 py-2 rounded-xl text-sm shadow-md shadow-emerald-200/50 transition active:scale-[0.98]">➕ 添加用户</button>
        </div>

        <div v-if="showUserForm" class="border rounded-lg p-4 bg-gray-50 space-y-3">
            <h3 class="text-sm font-bold">{{ editingUser ? '编辑用户' : '添加用户' }}</h3>
            <div class="grid grid-cols-2 gap-3">
                <label class="text-xs text-gray-500">用户名
                    <input type="text" v-model="userFormUsername" :disabled="!!editingUser" class="border p-2 rounded w-full text-sm mt-1">
                </label>
                <label class="text-xs text-gray-500">密码 <span v-if="editingUser" class="text-gray-400">(留空不修改)</span>
                    <input type="password" v-model="userFormPassword" :placeholder="editingUser ? '留空不修改' : ''" class="border p-2 rounded w-full text-sm mt-1">
                </label>
                <label class="text-xs text-gray-500">角色
                    <select v-model="userFormRole" class="border p-2 rounded w-full text-sm mt-1">
                        <option value="user">普通用户</option>
                        <option value="admin">管理员</option>
                    </select>
                </label>
            </div>
            <label class="text-xs text-gray-500">授权直播间</label>
            <div v-if="userFormRole === 'user'" class="relative">
                <button @click="showUserRoomDropdown = !showUserRoomDropdown"
                        class="border rounded w-full text-sm p-2 text-left bg-white flex items-center justify-between">
                    <span v-if="userFormRooms.length === 0" class="text-gray-400">选择房间...</span>
                    <span v-else class="text-gray-700">{{ userFormRooms.length }} 个房间已选</span>
                    <span class="text-gray-400">▼</span>
                </button>
                <div v-if="showUserRoomDropdown" class="absolute z-50 mt-1 bg-white border rounded shadow-lg w-full max-h-48 overflow-y-auto">
                    <div v-for="r in allRooms" :key="r.room_id"
                         class="flex items-center gap-2 px-3 py-2 hover:bg-gray-50 cursor-pointer text-sm"
                         @click="toggleUserRoom(r.room_id)">
                        <input type="checkbox" :checked="userFormRooms.includes(r.room_id)" class="w-3.5 h-3.5">
                        <span>{{ r.room_name || ('#'+r.room_id) }}</span>
                    </div>
                    <div v-if="!allRooms.length" class="text-xs text-gray-400 px-3 py-2">暂无房间</div>
                </div>
            </div>
            <div v-if="userFormRole !== 'user'" class="text-xs text-gray-400 mt-1">管理员可查看所有直播间</div>
            <div class="flex gap-2 mt-2">
                <button @click="saveUserForm" :disabled="savingUserForm"
                        class="bg-blue-500 hover:bg-blue-600 text-white px-4 py-2 rounded text-sm">
                    {{ savingUserForm ? '保存中...' : (editingUser ? '保存' : '添加') }}
                </button>
                <button @click="showUserForm = false; editingUser = null" class="bg-gray-200 hover:bg-gray-300 px-4 py-2 rounded text-sm">取消</button>
            </div>
            <div v-if="userFormMsg" class="text-sm" :class="userFormOk ? 'text-green-600' : 'text-red-500'">{{ userFormMsg }}</div>
        </div>

        <div v-if="adminUsers.length === 0" class="text-sm text-gray-400 text-center py-8">暂无用户</div>
        <div v-for="u in adminUsers" :key="u.username"
             class="border rounded-lg p-4 flex items-center justify-between">
            <div>
                <div class="font-bold text-sm">
                    {{ u.username }}
                    <span class="text-xs ml-2 px-2 py-0.5 rounded"
                          :class="u.role === 'admin' ? 'bg-red-100 text-red-600' : 'bg-blue-100 text-blue-600'">{{ u.role === 'admin' ? '管理员' : '普通用户' }}</span>
                </div>
                <div class="text-xs text-gray-500 mt-1">
                    授权房间: {{ u.role === 'admin' ? '全部直播间' : (u.allowed_rooms?.length ? u.allowed_rooms.join(', ') : '无') }}
                </div>
            </div>
            <div class="flex gap-2">
                <button @click="editUser(u)" class="bg-blue-50 hover:bg-blue-100 text-blue-600 px-3 py-1.5 rounded text-xs font-medium">编辑</button>
                <button v-if="u.username !== loginUser" @click="deleteUser(u.username)" class="bg-red-50 hover:bg-red-100 text-red-500 px-3 py-1.5 rounded text-xs font-medium">删除</button>
            </div>
        </div>
    </div>

    <!-- ── B站账号（合并到用户管理） ── -->
    <div class="bg-white p-4 sm:p-6 rounded-xl shadow-sm space-y-4 mt-4">
        <div class="flex items-center justify-between">
            <h2 class="text-lg font-bold">🤖 B站账号</h2>
            <button @click="toggleNewAccount"
                    class="bg-blue-500 hover:bg-blue-600 text-white px-4 py-2 rounded text-sm">
                {{ showNewAccount ? '取消' : '📱 扫码登录' }}
            </button>
        </div>

        <div v-if="showNewAccount" class="border rounded-lg p-4 bg-gray-50 space-y-3">
            <h3 class="text-sm font-bold">扫码登录 B站 账号</h3>
            <p class="text-xs text-gray-500">用 B站 App 扫描二维码即可登录，系统自动识别账号。</p>
            <button @click="startAccountLogin" :disabled="accountLoggingIn"
                    class="bg-blue-500 hover:bg-blue-600 text-white px-4 py-2 rounded text-sm">
                {{ accountLoggingIn ? '请稍候...' : '生成二维码' }}
            </button>
            <div v-if="accountQrImage" class="flex flex-col items-center space-y-2">
                <img :src="accountQrImage" class="border-2 border-gray-200 rounded-lg" style="width:180px;height:180px">
                <div class="flex items-center gap-2">
                    <span class="inline-block w-3 h-3 rounded-full bg-green-400 animate-pulse"></span>
                    <span class="text-sm">请用 B站 App 扫码</span>
                </div>
                <div v-if="accountQrState === 'scanned'" class="text-yellow-600 text-sm">已扫码，请在手机上确认</div>
                <div v-if="accountQrState === 'done'" class="text-green-600 text-sm font-bold">✅ 登录成功，即将返回...</div>
                <div v-if="accountQrState === 'timeout' || accountQrState === 'expired'" class="text-red-500 text-sm">⏰ 二维码已过期</div>
                <div v-if="accountQrState === 'error'" class="text-red-500 text-sm">{{ accountQrError }}</div>
                <div v-if="accountQrState === 'waiting' || accountQrState === 'scanned' || accountQrState === 'timeout' || accountQrState === 'expired'" class="flex gap-2 justify-center">
                    <button @click="refreshQrCode" class="bg-blue-500 hover:bg-blue-600 text-white px-4 py-1.5 rounded text-sm">🔄 刷新二维码</button>
                </div>
            </div>
        </div>

        <div v-if="!accounts || accounts.length === 0" class="text-sm text-gray-400 text-center py-8">暂无已登录的 B站 账号。</div>
        <div v-if="accounts && accounts.length > 1" class="flex justify-end">
            <button @click="verifyAllAccounts" :disabled="verifyingAll" class="bg-blue-50 hover:bg-blue-100 text-blue-600 px-3 py-1.5 rounded text-xs font-medium">
                {{ verifyingAll ? (`验证中 ${verifyQueue.length + 1}/${accounts.length}...`) : '🔍 一键检测所有' }}
            </button>
        </div>
        <div v-for="a in accounts" :key="a.uid" class="border rounded-lg p-4 flex items-center justify-between">
            <div>
                <div class="font-bold text-sm">
                    <template v-if="editingNickname === a.uid">
                        <input type="text" v-model="a.editNick" class="border p-1 rounded text-sm w-32" @keyup.enter="saveNickname(a)">
                        <button @click="saveNickname(a)" class="text-blue-500 text-xs ml-1">保存</button>
                        <button @click="editingNickname = null" class="text-gray-400 text-xs ml-1">取消</button>
                    </template>
                    <template v-else>
                        <span @click="startEditNickname(a)" class="cursor-pointer hover:text-blue-600">{{ a.nickname || '未命名' }}</span>
                        <button @click="startEditNickname(a)" class="text-gray-400 hover:text-blue-500 text-xs ml-1">✏️</button>
                    </template>
                </div>
                <div class="text-xs text-gray-500 mt-1">UID: {{ a.uid }}</div>
                <div v-if="a.linked_rooms && a.linked_rooms.length" class="text-xs text-gray-400 mt-1">
                    关联房间: <span v-for="(lr, li) in a.linked_rooms" :key="lr.room_id">{{ lr.room_id }}<span v-if="li < a.linked_rooms.length-1">, </span></span>
                </div>
                <div v-else class="text-xs text-gray-400 mt-1">未关联房间（可在房间详情设置中绑定）</div>
            </div>
            <div class="flex gap-2 items-center">
                <button @click="verifyAccount(a.uid)" :disabled="a.verifying" class="bg-gray-100 hover:bg-gray-200 px-2.5 py-1.5 rounded text-xs font-medium" :class="{'text-green-600':a.credential_ok===true,'text-red-500':a.credential_ok===false,'text-gray-600':!a.credential_ok}">
                    {{ a.verifying ? '验证中...' : (a.credential_ok === true ? '✅ 有效' : (a.credential_ok === false ? '❌ 失效' : '验证')) }}
                </button>
                <button @click="deleteAccount(a.uid, a.nickname)" class="bg-red-50 hover:bg-red-100 text-red-500 px-2.5 py-1.5 rounded text-xs font-medium">删除</button>
            </div>
        </div>
    </div>
</div>
<div v-if="tab==='help'" class="max-w-3xl mx-auto">
    <div class="help-page bg-white p-6 rounded-xl shadow-sm space-y-6 text-sm leading-relaxed">
        <h2 class="page-title">📖 使用指南</h2>
        <!-- 官网入口：放在最显眼的位置（下载、功能说明、常见问题都在上面） -->
        <a href="https://ayabot.jianke-yu.online" target="_blank" rel="noopener"
           class="flex items-center gap-3 bg-gradient-to-r from-pink-50 to-sky-50 border border-pink-200 rounded-lg p-3 hover:border-pink-300 transition no-underline">
            <span class="text-2xl shrink-0">🌐</span>
            <span class="flex-1 min-w-0">
                <span class="block font-bold text-[13px] sm:text-sm text-gray-800 break-words">原作者官网 · ayabot.jianke-yu.online</span>
                <span class="block text-xs text-gray-500 mt-0.5">最新版下载（国内线路自动测速）、功能说明、常见问题</span>
            </span>
            <span class="hidden sm:inline text-xs text-blue-500 whitespace-nowrap shrink-0">打开 ↗</span>
        </a>
        <!-- 本版本链接：与官网卡片同样式 -->
        <a href="https://github.com/MildewD/Ayabot-Enhanced" target="_blank" rel="noopener"
           class="flex items-center gap-3 bg-gradient-to-r from-pink-50 to-sky-50 border border-pink-200 rounded-lg p-3 hover:border-pink-300 transition no-underline">
            <span class="text-2xl shrink-0">🌐</span>
            <span class="flex-1 min-w-0">
                <span class="block font-bold text-[13px] sm:text-sm text-gray-800 break-words">本版本 · github.com/MildewD/Ayabot-Enhanced</span>
                <span class="block text-xs text-gray-500 mt-0.5">本版本源码、功能说明、常见问题</span>
            </span>
            <span class="hidden sm:inline text-xs text-blue-500 whitespace-nowrap shrink-0">打开 ↗</span>
        </a>
        <div class="bg-blue-50 border border-blue-200 rounded-lg p-4 space-y-3">
            <h3 class="font-bold text-blue-700">🚀 快速开始</h3>
            <ol class="list-decimal pl-4 space-y-2 text-xs">
                <li><strong class="text-blue-600">登录 B站 账号</strong> — 进入「用户管理」→「B站账号」→「扫码登录」，用 B站 App 扫描二维码完成登录。机器人需要通过你的账号发送弹幕。</li>
                <li><strong class="text-blue-600">新建直播间</strong> — 进入「房间管理」→「新建房间」，填写主播 UID 和直播间号，关联上一步登录的 B站 账号。</li>
                <li><strong class="text-blue-600">配置并启动</strong> — 创建后在房间详情中按需配置功能开关、回复模板、AI 回复等，然后点击「启动」按钮。</li>
                <li><strong class="text-blue-600">创建主播账号（可选）</strong> — 如果是帮别人部署，可在「用户管理」中新建「普通用户」账号并授权指定房间，对方登录后仅可查看/导出自己房间的数据。</li>
            </ol>
        </div>
        <div>
            <h3 class="font-bold text-slate-700 mb-2 flex items-center gap-1.5"><span class="gb-card-title">🎯 弹幕命令</span></h3>
            <div class="rounded-xl border border-slate-100 bg-white/40 overflow-hidden">
            <table class="w-full text-xs border-collapse gb-table">
                <thead><tr><th class="p-2 text-left">命令</th><th class="p-2 text-left">说明</th></tr></thead>
                <tbody>
                    <tr><td class="p-2"><code class="px-1.5 py-0.5 rounded bg-indigo-50 text-indigo-700 font-semibold">#签到</code></td><td class="p-2 text-gray-600">每日签到（直播场次连续签到）</td></tr>
                    <tr><td class="p-2"><code class="px-1.5 py-0.5 rounded bg-indigo-50 text-indigo-700 font-semibold">#抽签</code></td><td class="p-2 text-gray-600">今日运势抽签（支持自定义签文）</td></tr>
                    <tr><td class="p-2"><code class="px-1.5 py-0.5 rounded bg-indigo-50 text-indigo-700 font-semibold">#今日盲盒:用户名</code></td><td class="p-2 text-gray-600">今日盲盒统计，不加用户名查自己</td></tr>
                    <tr><td class="p-2"><code class="px-1.5 py-0.5 rounded bg-indigo-50 text-indigo-700 font-semibold">#本月盲盒:用户名</code></td><td class="p-2 text-gray-600">本月盲盒统计，不加用户名查自己</td></tr>
                    <tr><td class="p-2"><code class="px-1.5 py-0.5 rounded bg-indigo-50 text-indigo-700 font-semibold">#&lt;唤醒词&gt; &lt;聊天&gt;</code></td><td class="p-2 text-gray-600">AI 智能回复</td></tr>
                    <tr><td class="p-2"><code class="px-1.5 py-0.5 rounded bg-indigo-50 text-indigo-700 font-semibold">#帮助</code></td><td class="p-2 text-gray-600">显示所有命令</td></tr>
                    <tr><td class="p-2"><code class="px-1.5 py-0.5 rounded bg-indigo-50 text-indigo-700 font-semibold">#PK已结束</code></td><td class="p-2 text-gray-600">手动复位 PK 状态（主播/房管）</td></tr>
                </tbody>
            </table>
            </div>
            <p class="text-xs text-gray-400 mt-2">开启「免#指令」后可不带 # 前缀触发指令。
            开启「AI免#前缀唤醒」后弹幕以唤醒词开头即触发 AI。</p>
            <p class="text-xs text-gray-400 mt-2">
            ⚔️ <strong class="text-gray-500">PK 状态播报</strong>：开启「PK 汇报」后，进入/PK 开始 → 机器人自动播报对手信息；PK <strong class="text-gray-500">主动停止</strong>（主播手动结束，无完整结算数据）→ 机器人同步复位 PK 状态并只播报一句「#PK已结束」；PK <strong class="text-gray-500">自然结算</strong> → 机器人播报输赢与双方比分。</p>
        </div>
    </div>
</div>

                <!-- ── 检查更新弹窗 ── -->
                <div v-if="showUpdateModal" class="fixed inset-0 bg-black/40 flex items-center justify-center z-50">
                    <div class="bg-white rounded-xl shadow-lg w-full max-w-sm mx-4 p-6 text-center space-y-4" @click.stop>
                        <div v-if="updateChecking" class="py-8">
                            <p class="text-gray-500">正在检查更新...</p>
                            <p class="text-[11px] text-gray-400 mt-1">并发测速国内线路，通常 1 秒内完成</p>
                        </div>
                        <div v-else-if="updateError" class="py-4">
                            <p class="text-red-500 text-lg mb-2">❌ 检查失败</p>
                            <p class="text-xs text-gray-500">{{ updateError }}</p>
                        </div>
                        <div v-else-if="updateData">
                            <p class="text-4xl mb-3">{{ updateData.hasUpdate ? '📢' : '✅' }}</p>
                            <p class="text-lg font-bold mb-2">
                                {{ updateData.hasUpdate ? '发现新版本！' : '已是最新版本' }}
                            </p>
                            <p class="text-sm text-gray-600">
                                当前版本：<span class="font-mono">{{ updateData.current }}</span>
                            </p>
                            <p v-if="updateData.hasUpdate" class="text-sm text-gray-600">
                                最新版本：<span class="font-mono font-bold text-green-600">{{ updateData.latest }}</span>
                            </p>
                            <div v-if="updateData.hasUpdate" class="pt-3 space-y-2">
                                <a v-if="updateData.recommended" :href="updateData.recommended.url" target="_blank"
                                   class="block w-full bg-green-500 hover:bg-green-600 text-white px-4 py-2 rounded text-sm">
                                   📥 下载 {{ updateData.latest }}
                                   <span class="text-xs opacity-80">
                                       （{{ updateData.recommended.name === 'GitHub' ? 'GitHub 直连' : '国内镜像 ' + updateData.recommended.name }}{{ updateData.recommended.stale ? '，该线路缓存未更新' : '' }}）
                                   </span>
                                </a>
                                <div v-if="updateData.downloads && updateData.downloads.length > 1" class="text-left">
                                    <p class="text-[11px] text-gray-400 mb-1">
                                        其他线路（已自动测速，✅ 可用 / ⏱ 未测速 / ❌ 不通）：
                                    </p>
                                    <div class="space-y-1 max-h-56 overflow-y-auto">
                                        <a v-for="d in updateData.downloads" :key="d.name" :href="d.url" target="_blank"
                                           class="flex items-center justify-between gap-2 text-xs px-2 py-1 rounded hover:bg-gray-50"
                                           :class="d.ok && !d.stale ? 'text-gray-600' : 'text-gray-400'">
                                            <span>{{ d.ok ? (d.stale ? '⚠️' : '✅') : (d.skipped ? '⏱' : '❌') }} {{ d.name === 'GitHub' ? 'GitHub 直连' : d.name }}<span v-if="d.stale" class="text-[10px] text-amber-600 ml-1">缓存旧版</span></span>
                                            <span class="font-mono text-[10px]">{{ d.ok ? d.ms + 'ms' : (d.skipped ? '未测速' : (d.status || '超时')) }}</span>
                                        </a>
                                    </div>
                                </div>
                                <a :href="updateData.url" target="_blank"
                                   class="block w-full bg-blue-50 hover:bg-blue-100 text-blue-600 px-4 py-2 rounded text-sm">
                                   📄 查看 Release 页面
                                </a>
                            </div>
                            <div class="pt-3">
                                <button @click="viewChangelog"
                                        class="w-full bg-purple-50 hover:bg-purple-100 text-purple-600 font-medium px-4 py-2 rounded text-sm">
                                    📝 查看更新日志
                                </button>
                            </div>
                            <p v-if="updateData" class="text-[10px] text-gray-400">
                                线路 {{ updateData.metaSource || '未知' }} ·
                                <template v-if="updateData.cached">缓存结果（{{ updateData.cacheAge }} 秒前测的）</template>
                                <template v-else>耗时 {{ (updateData.elapsedMs / 1000).toFixed(1) }}s</template>
                            </p>
                        </div>
                        <div class="pt-2">
                            <button v-if="updateData && updateData.hasUpdate" @click="ignoreUpdate"
                                    class="text-xs text-gray-400 hover:text-gray-600 underline mr-4">忽略此版本</button>
                            <button @click="showUpdateModal = false" class="text-gray-400 hover:text-gray-600 text-sm">关闭</button>
                        </div>
                    </div>
                </div>

                <!-- 更新日志弹窗 -->
                <div v-if="showChangelog" class="fixed inset-0 bg-black/40 flex items-center justify-center z-50">
                    <div class="bg-white rounded-xl shadow-lg w-full max-w-lg mx-4 max-h-[70vh] flex flex-col" @click.stop>
                        <div class="p-4 border-b flex items-center justify-between shrink-0">
                            <h3 class="font-bold text-lg">📝 更新日志</h3>
                            <button @click="showChangelog = false" class="text-gray-400 hover:text-gray-600 text-xl">✕</button>
                        </div>
                        <div class="p-4 overflow-y-auto flex-1 text-sm leading-relaxed whitespace-pre-wrap"
                             v-html="renderMarkdown(changelogContent)">
                        </div>
                    </div>
                </div>

</div><!-- /loggedIn -->
</div>

<script>
const {createApp, ref, computed, watch, nextTick} = Vue;
createApp({
    setup() {
        const loggedIn = ref(document.cookie.includes('session='));
        const loginUser = ref('');
        const loginPass = ref('');
        const loginErr = ref('');
        const tab = ref('rooms');
        const userRole = ref('');
        const mustResetPwd = ref(false);

        // 夜间模式（与 <html>.dark 同步）
        const isDark = ref(false);
        function initTheme() {
            try {
                isDark.value = localStorage.getItem('ayabot_dark') === '1';
            } catch (e) { /* 无痕 */ }
        }
        function toggleTheme() {
            isDark.value = !isDark.value;
            document.documentElement.classList.toggle('dark', isDark.value);
            try {
                localStorage.setItem('ayabot_dark', isDark.value ? '1' : '0');
            } catch (e) { /* 无痕 */ }
        }
        initTheme();
        // 让当前渲染状态与 <html> 保持同步（防页面硬刷新后 Vue 状态与 class 脱节）
        document.documentElement.classList.toggle('dark', isDark.value);

        // 修改密码
        const showChangePwd = ref(false);
        const changePwdOld = ref('');
        const changePwdNew = ref('');
        const changePwdConfirm = ref('');
        const changePwdNewUser = ref('');
        const changePwdMsg = ref('');
        const changePwdOk = ref(false);
        const changingPwd = ref(false);

        // 用户菜单
        const showUserMenu = ref(false);

        // 管理员用户管理
        const adminUsers = ref([]);
        const showUserForm = ref(false);
        const editingUser = ref(null);
        const userFormUsername = ref('');
        const userFormPassword = ref('');
        const userFormRole = ref('user');
        const userFormRooms = ref([]);
        const showUserRoomDropdown = ref(false);
        const savingUserForm = ref(false);
        const userFormMsg = ref('');
        const userFormOk = ref(false);

        // Room detail
        const selectedRoom = ref(null);
        const roomSubTab = ref('ranking');
        const roomSubTabs = computed(() => {
            const tabs = [
                {key: 'ranking', label: '送礼排行'},
                {key: 'export', label: '精美导出'},
                {key: 'danmaku', label: '弹幕记录'},
            ];
            if (userRole.value === 'admin') {
                tabs.push(
                    {key: 'llm', label: 'AI回复'},
                    {key: 'config', label: '机器人配置'},
                    {key: 'manage', label: '数据管理'},
                    {key: 'log', label: '📋 日志'},
                );
            }
            return tabs;
        });
        const newRoomAccount = ref('');
        const selectedRoomAccount = ref('');
        const accountAssignMsg = ref('');
        const accountAssignOk = ref(false);
        const accountRestarting = ref(false);

        // Accounts management
        const accounts = ref([]);
        const showNewAccount = ref(false);
        const newAccountUid = ref(0);
        const accountLoggingIn = ref(false);
        const accountQrImage = ref('');
        const accountQrState = ref('idle');
        const accountQrError = ref('');
        const accountSessionId = ref('');
        let accountsPollTimer = null;

        // Ranking
        const rStart = ref(new Date().toISOString().slice(0,10));
        const rEnd   = ref(new Date().toISOString().slice(0,10));
        const rType  = ref('all');
        const ranking = ref([]);
        const errRanking = ref('');
        // 上舰（大航海）记录
        const guardItems = ref([]);
        const guardTotals = ref(null);
        function fmtGuardTime(ts) {
            if (!ts) return '';
            const d = new Date(ts * 1000);
            return d.toLocaleString('zh-CN', {month:'2-digit', day:'2-digit', hour:'2-digit', minute:'2-digit'});
        }
        async function loadGuards() {
            const roomId = selectedRoom.value?.room_id;
            if (!roomId) return;
            try {
                const params = new URLSearchParams();
                if (rStart.value) params.set('rStart', rStart.value);
                if (rEnd.value) params.set('rEnd', rEnd.value);
                const res = await fetch(`/api/rooms/${roomId}/guards?${params}`, {credentials: 'include'});
                if (!res.ok) return;
                const data = await res.json();
                guardItems.value = data.items || [];
                guardTotals.value = data.totals || null;
            } catch(e) { /* ignore */ }
        }

        // Export
        const eModeAll = ref(false);  // true=所有人模式
        const eUid = ref(0);
        const eName = ref('');
        const eDate = ref(new Date().toISOString().slice(0,10));
        const eSelectedDates = ref([new Date().toISOString().slice(0,10)]);  // 数组保证响应式
        const eSelectedSet = Vue.computed(() => new Set(eSelectedDates.value));
        const eDateLabel = Vue.computed(() => {
            const arr = eSelectedDates.value.slice().sort();
            if (arr.length > 1) {
                return arr[0] + ' ~ ' + arr[arr.length-1] + ` (${arr.length}天)`;
            }
            if (arr.length === 1) return arr[0];
            return '请选择日期';
        });
        const eAllUserDates = ref([]);
        const eType = ref('all');
        const eSort = ref('uname');
        const eMergeGifts = ref(false);
        const eMergeUser = ref(false);
        const ePerCol = ref(6);
        const eColWidth = ref(340);
        const eShowPrice = ref(true);
        const exportList = ref([]);
        const exporting = ref(false);
        const loadingExport = ref(false);
        const exportDates = ref([]);
        const errExport = ref('');

        // 日历状态
        const showCalendar = ref(false);
        const calYear = ref(new Date().getFullYear());
        const calMonth = ref(new Date().getMonth());
        const exportDatesSet = ref(new Set());
        // 日历弹窗定位：Teleport 到 body 后需用视口坐标 (fixed)。点击输入框时记录其位置
        const calPos = ref({ top: 0, left: 0 });
        const toggleCalendar = (ev) => {
          showCalendar.value = !showCalendar.value;
          if (showCalendar.value && ev && ev.currentTarget) {
            const r = ev.currentTarget.getBoundingClientRect();
            calPos.value = { top: r.bottom + 4, left: r.left };
          }
        };

        // 日历天数计算
        const calDays = Vue.computed(() => {
            const year = calYear.value;
            const month = calMonth.value;
            const firstDay = new Date(year, month, 1).getDay();
            const daysInMonth = new Date(year, month + 1, 0).getDate();
            const cells = [];
            for (let i = 0; i < firstDay; i++) cells.push(null);
            for (let d = 1; d <= daysInMonth; d++) {
                const ymd = `${year}-${String(month+1).padStart(2,'0')}-${String(d).padStart(2,'0')}`;
                cells.push({ d, ymd, hasData: exportDatesSet.value.has(ymd) });
            }
            return cells;
        });

        // 手动分列计算
        const exportCols = Vue.computed(() => {
            let items = exportList.value;
            const perCol = Math.max(1, ePerCol.value);
            if (!items.length) return [];

            // 排序（按当前选中的排序规则）
            const s = eSort.value;
            const merge = eMergeGifts.value;
            // 非合并 或 按用户/按时间：先排序再合并
            if (s === 'uname') {
                items = [...items].sort((a, b) => {
                    const g = (b.guard_level || 0) - (a.guard_level || 0);
                    if (g) return g;
                    const n = (a.uname || '').localeCompare(b.uname || '');
                    if (n) return n;
                    return (b.actual_value || 0) - (a.actual_value || 0);
                });
            } else if (s === 'value' && !merge) {
                items = [...items].sort((a, b) => {
                    const v = (b.actual_value || 0) - (a.actual_value || 0);
                    if (v) return v;
                    const g = (b.guard_level || 0) - (a.guard_level || 0);
                    if (g) return g;
                    return (a.uname || '').localeCompare(b.uname || '');
                });
            } else if (s === 'ts' && !merge) {
                items = [...items].sort((a, b) => (a.ts || 0) - (b.ts || 0));
            }

            // 合并相同礼物模式
            if (merge) {
                const merged = new Map();
                for (const item of items) {
                    const key = item.uid + '|' + item.gift_name;
                    if (merged.has(key)) {
                        const existing = merged.get(key);
                        existing.gift_num += item.gift_num;
                        existing.actual_value += item.actual_value;
                        existing.ts = Math.max(existing.ts, item.ts);
                    } else {
                        merged.set(key, { ...item, id: key });
                    }
                }
                items = [...merged.values()];
                // 合并后按价值排序（按合并总价）
                if (s === 'value') {
                    items.sort((a, b) => {
                        const v = (b.actual_value || 0) - (a.actual_value || 0);
                        if (v) return v;
                        const g = (b.guard_level || 0) - (a.guard_level || 0);
                        if (g) return g;
                        return (a.uname || '').localeCompare(b.uname || '');
                    });
                }
            }

            // ══ 按用户合并：同一用户所有礼物整合成一张卡片 ══
            if (eMergeUser.value) {
                const byUser = new Map();
                for (const item of items) {
                    const k = item.uid;
                    if (!byUser.has(k)) {
                        byUser.set(k, {
                            ...item,
                            _gifts: [{
                                gift_name: item.gift_name,
                                gift_num: item.gift_num || 0,
                                actual_value: item.actual_value || 0,
                                gift_icon: item.gift_icon || '',
                            }],
                            _gift_total: item.gift_num || 0,
                        });
                    } else {
                        const ex = byUser.get(k);
                        // 同一礼物名在聚合卡片内再累加一次
                        const dup = ex._gifts.find(g => g.gift_name === item.gift_name);
                        if (dup) {
                            dup.gift_num += (item.gift_num || 0);
                            dup.actual_value += (item.actual_value || 0);
                        } else {
                            ex._gifts.push({
                                gift_name: item.gift_name,
                                gift_num: item.gift_num || 0,
                                actual_value: item.actual_value || 0,
                                gift_icon: item.gift_icon || '',
                            });
                        }
                        ex._gift_total += (item.gift_num || 0);
                        ex.ts = Math.max(ex.ts, item.ts);
                    }
                }
                items = [...byUser.values()].map(u => {
                    const tv = u._gifts.reduce((s, g) => s + (g.actual_value || 0), 0);
                    return { ...u, actual_value: tv, _gift_total: u._gift_total, _gifts: u._gifts };
                });
                // 排序：大航海优先，再按总价值/时间
                items.sort((a, b) => {
                    const g = (b.guard_level || 0) - (a.guard_level || 0);
                    if (g) return g;
                    if (s === 'ts') return (a.ts || 0) - (b.ts || 0);
                    return (b.actual_value || 0) - (a.actual_value || 0);
                });
            }

            const cols = [];
            for (let i = 0; i < items.length; i += perCol) {
                cols.push(items.slice(i, i + perCol));
            }
            return cols;
        });

        // Manage
        const delDate = ref('');
        const delResult = ref('');

        // Room API config
        const roomApiEnabled = ref(false);
        const roomApiUrl = ref('');
        const roomApiFullKey = ref('');
        const roomApiBusy = ref(false);
        const apiMsg = ref('');
        const apiMsgOk = ref(false);

        // Danmaku Log
        const danmakuRows = ref([]);
        const danmakuErr = ref('');
        const danmakuOffset = ref(0);
        const danmakuLimit = ref(50);
        const danmakuTotal = ref(0);
        const danmakuPage = Vue.computed(() => Math.floor(danmakuOffset.value / danmakuLimit.value) + 1);
        // Danmaku date calendar
        const dmDates = ref([]);
        const dmDatesSet = ref(new Set());
        const dmCalYear = ref(new Date().getFullYear());
        const dmCalMonth = ref(new Date().getMonth());
        const dmSelectedDates = ref(new Set());
        const dmShowCal = ref(false);
        const dmCalPos = ref({ top: 0, left: 0 }); // 日历弹窗定位（Teleport fixed）
        const dmDateFrom = ref('');
        const dmDateTo = ref('');
        const dmAsc = ref(false);
        const dmKeyword = ref('');
        const dmSearchActive = ref('');
        const dmSearchCount = ref(0);
        const dmGap = ref(14400);   // 录像划分间隔阈值(秒)，相邻弹幕间隔≥该值视为新录像；默认4小时
        const dmShowRec = ref(true); // 是否显示「录像」列
        const dmGapOptions = [
            { v: 3600, label: '1 小时' },
            { v: 7200, label: '2 小时' },
            { v: 14400, label: '4 小时(默认)' },
            { v: 28800, label: '8 小时' },
            { v: 43200, label: '12 小时' },
        ];
        // 用户名 / UID 筛选 + 弹幕统计
        const dmUsers = ref([]);            // 去重用户列表(从 /api/danmaku_users 加载)
        const dmUserFilter = ref('');        // 选中的用户名(模糊筛选)
        const dmUidFilter = ref('');         // 精确 UID 筛选输入
        const dmUserBusy = ref(false);       // 用户下拉加载中
        const dmStats = ref(null);           // 统计结果
        const dmShowStats = ref(false);      // 统计面板显隐
        const dmSessions = ref([]);          // 直播场次列表(从 /api/danmaku_sessions 加载)
        const dmSessionIdx = ref(-1);        // 选中的场次索引(-1=不按场次,按日期)
        const dmShowSessionPanel = ref(false); // 可搜索场次面板开关
        const dmSessionQuery = ref('');        // 场次面板搜索词
        const dmCalDays = Vue.computed(() => {
            const y = dmCalYear.value, m = dmCalMonth.value;
            const fd = new Date(y, m, 1).getDay();
            const dim = new Date(y, m + 1, 0).getDate();
            const cells = [];
            for (let i = 0; i < fd; i++) cells.push(null);
            for (let d = 1; d <= dim; d++) {
                const ymd = `${y}-${String(m+1).padStart(2,'0')}-${String(d).padStart(2,'0')}`;
                cells.push({ d, ymd, hasData: dmDatesSet.value.has(ymd), selected: dmSelectedDates.value.has(ymd) });
            }
            return cells;
        });

        // Room Management
        const rooms = ref([]);
        const showCreateRoom = ref(false);
        const newRoomUid = ref(0);
        const newRoomName = ref('');
        const newRoomAnchorName = ref('');  // 自动获取的主播用户名
        const newRoomPort = ref(8001);
        const newRoomDisplayId = ref(0);
        const creatingRoom = ref(false);
        const createRoomMsg = ref('');
        const createRoomOk = ref(false);
        const editingRoom = ref(null);
        const roomConfig = ref(null);
        const roomSaveMsg = ref('');
        const roomSaveOk = ref(false);
        const editingRoomName = ref(false);
        const roomNameEdit = ref('');

        // ── 检查更新 ──
        const showUpdateModal = ref(false);
        const updateChecking = ref(false);
        const updateError = ref('');
        const updateData = ref(null);
        // 启动时静默检查到的更新（管理员才提示；可忽略某个版本）
        const silentUpdate = ref(null);
        const updateNotice = ref('');   // 非空 = 有未忽略的新版本，值是版本号
        const showChangelog = ref(false);
        const changelogContent = ref('');
        async function viewChangelog() {
            showChangelog.value = true;
            if (!changelogContent.value) {
                // 要看的版本：优先弹窗里查到的最新版，否则当前版本
                const target = ((updateData.value && updateData.value.latest) ||
                                (silentUpdate.value && silentUpdate.value.latest) || '').replace(/^v/i, '');
                const curEl = document.querySelector('[data-ayabot-version]');
                const current = (curEl ? curEl.getAttribute('data-ayabot-version') : '0').replace(/^v/i, '');
                const ver = target || current;
                changelogContent.value = '*正在加载…*';
                try {
                    // 服务端经国内镜像代取（浏览器直连 api.github.com 在国内常失败）
                    const r = await fetch(`/api/update/changelog?version=${encodeURIComponent(ver)}`, {
                        credentials: 'include',
                        signal: AbortSignal.timeout(15000),
                    });
                    const j = await r.json();
                    if (j.ok && j.body) {
                        changelogContent.value = j.body;
                    } else {
                        changelogContent.value = '*无法加载更新日志*';
                    }
                } catch(e) {
                    changelogContent.value = '*加载失败: ' + e.message + '*';
                }
            }
        }
        function renderMarkdown(text) {
            if (!text) return '';
            return text
                // 标题
                .replace(/^#### (.*$)/gm, '<h4 class="font-bold text-sm mt-3 mb-1">$1</h4>')
                .replace(/^### (.*$)/gm, '<h3 class="font-bold text-base mt-3 mb-1">$1</h3>')
                .replace(/^## (.*$)/gm, '<h2 class="font-bold text-lg mt-4 mb-1">$1</h2>')
                .replace(/^# (.*$)/gm, '<h1 class="font-bold text-xl mt-4 mb-1">$1</h1>')
                // 粗体
                .replace(/\*\*(.*?)\*\*/g, '<strong>$1</strong>')
                // 行内代码
                .replace(/`([^`]+)`/g, '<code class="bg-gray-100 px-1 rounded text-xs font-mono">$1</code>')
                // 无序列表
                .replace(/^- (.*$)/gm, '<li class="ml-4 list-disc">$1</li>')
                // 链接
                .replace(/\[([^\]]+)\]\(([^)]+)\)/g, '<a href="$2" target="_blank" class="text-blue-500 hover:underline">$1</a>')
                // 换行
                .replace(/\n\n/g, '</p><p class="my-2">')
                .replace(/\n/g, '<br>');
        }
        function toUpdateData(j) {
            return {
                hasUpdate: !!j.has_update,
                current: j.current,
                latest: j.latest,
                url: j.page_url || 'https://github.com/yujianke100/ayabot/releases',
                changelogUrl: j.page_url || 'https://github.com/yujianke100/ayabot/releases',
                downloads: j.downloads || [],
                recommended: j.recommended || null,
                metaSource: j.meta_source || '',
                changelog: j.changelog || '',
                elapsedMs: j.elapsed_ms || 0,
                cached: !!j.cached,
                cacheAge: j.cache_age || 0,
            };
        }
        async function checkUpdate() {
            showUpdateModal.value = true;
            updateChecking.value = true;
            updateError.value = '';
            updateData.value = null;
            try {
                // 先取服务端缓存（通常秒回），有就先显示
                const r = await fetch('/api/update/check', {
                    credentials: 'include',
                    signal: AbortSignal.timeout(20000)
                });
                if (!r.ok) throw new Error(`HTTP ${r.status}`);
                const j = await r.json();
                if (!j.ok) throw new Error(j.error || '无法获取版本信息');
                updateData.value = toUpdateData(j);
                updateChecking.value = false;
                // 手动检查过就同步提示状态（有更新 → 亮红点；已验证最新 → 清掉）
                if (j.has_update) {
                    updateNotice.value = j.latest;
                } else {
                    updateNotice.value = '';
                }
                // 缓存超过 2 分钟，再向国内镜像实测一次（界面已经先显示了，慢了也无感）
                if (j.cached && (j.cache_age || 0) > 120) {
                    fetch('/api/update/check?force=1', {
                        credentials: 'include',
                        signal: AbortSignal.timeout(20000)
                    }).then(r2 => (r2.ok ? r2.json() : null)).then(j2 => {
                        if (j2 && j2.ok) {
                            updateData.value = toUpdateData(j2);
                            updateNotice.value = j2.has_update ? j2.latest : '';
                        }
                    }).catch(() => {});
                }
            } catch(e) {
                updateChecking.value = false;
                // 兜底：老版本/离线环境仍直接问 GitHub
                try {
                    const r2 = await fetch('https://api.github.com/repos/yujianke100/ayabot/releases/latest', {
                        signal: AbortSignal.timeout(8000)
                    });
                    if (!r2.ok) throw new Error(`HTTP ${r2.status}`);
                    const j2 = await r2.json();
                    const latest = (j2.tag_name || '').replace(/^v/i, '');
                    const verEl = document.querySelector('[data-ayabot-version]');
                    const current = (verEl ? verEl.getAttribute('data-ayabot-version') : '0').replace(/^v/i, '');
                    const asset = `https://github.com/yujianke100/ayabot/releases/download/v${latest}/Ayabot-latest.exe`;
                    updateData.value = {
                        hasUpdate: latest.localeCompare(current, undefined, {numeric: true}) > 0,
                        current: 'v' + current,
                        latest: 'v' + latest,
                        url: j2.html_url || 'https://github.com/yujianke100/ayabot/releases',
                        changelogUrl: 'https://github.com/yujianke100/ayabot/releases/tag/v' + latest,
                        downloads: [{name: 'GitHub', url: asset, ok: true}],
                        recommended: {name: 'GitHub', url: asset, ok: true},
                        metaSource: 'GitHub（前端直连）',
                        changelog: j2.body || '',
                    };
                } catch(e2) {
                    updateError.value = (e.message || '') + ' / ' + (e2.message || '网络错误');
                }
            } finally {
                updateChecking.value = false;
            }
        }

        // ── 启动静默检查更新（不打断操作，只在导航栏亮一个提示） ──
        function _ignoredVersion() {
            try { return localStorage.getItem('ayabot_ignored_version') || ''; } catch(e) { return ''; }
        }
        async function silentCheckUpdate() {
            if (userRole.value !== 'admin') return;   // 只有管理员能更新，普通用户不打扰
            try {
                // 不带 force：服务端 10 分钟内的结果直接复用，打开/刷新页面几乎立刻有结果
                const r = await fetch('/api/update/check', {
                    credentials: 'include',
                    signal: AbortSignal.timeout(20000),
                });
                if (!r.ok) return;
                const j = await r.json();
                if (!j.ok || !j.has_update) return;
                if (j.latest && j.latest === _ignoredVersion()) return;
                silentUpdate.value = toUpdateData(j);
                updateNotice.value = j.latest;
            } catch(e) {
                // 网络不通就静默失败，绝不弹错误打断用户
            }
        }
        function openUpdateNotice() {
            if (silentUpdate.value) {
                // 用启动时已探测好的结果，点开即显示（不再等一遍测速）
                updateError.value = '';
                updateData.value = silentUpdate.value;
                showUpdateModal.value = true;
                return;
            }
            checkUpdate();
        }
        function ignoreUpdate() {
            const ver = (updateData.value && updateData.value.latest) || updateNotice.value || '';
            try { localStorage.setItem('ayabot_ignored_version', ver); } catch(e) { /* 无痕模式忽略 */ }
            silentUpdate.value = null;
            updateNotice.value = '';
            showUpdateModal.value = false;
        }

        // 模板管理
        const llmTemplates = ref([]);
        const botTemplates = ref([]);
        const showAddTemplate = ref(null);  // 'llm' | 'bot' | null
        const templateFormName = ref('');
        const templateFormImportRoom = ref('');
        const savingTemplate = ref(false);
        const templateFormMsg = ref('');
        const templateFormOk = ref(false);
        const newRoomLlmTemplate = ref('');
        const newRoomBotTemplate = ref('');
        // 输入 UID 时自动查询主播用户名（通过后端代理，避免跨域）
        watch(newRoomUid, async (val) => {
            if (!val || val < 1000) { newRoomAnchorName.value = ''; return; }
            newRoomAnchorName.value = '查询中...';
            try {
                const r = await fetch(`/api/bilibili/user_info?mid=${val}`, {credentials: 'include'});
                if (!r.ok) { newRoomAnchorName.value = '(查询失败)'; return; }
                const j = await r.json();
                newRoomAnchorName.value = (j.code === 0 && j.name) ? j.name : '(未找到)';
            } catch(e) { newRoomAnchorName.value = '(查询失败)'; }
        });
        const restartingAll = ref(false);
        const startingRooms = ref(new Set());
        const restartAllMsg = ref('');
        const restartAllOk = ref(false);
        const applyLlmTemplate = ref('');
        const applyBotTemplate = ref('');
        const applyTemplateMsg = ref('');
        const applyTemplateOk = ref(false);

        // 配置区折叠状态（默认全部收起，accordion 模式：开一个关其他）
        const configSections = ref({
            rateLimit: false,
            features: true,
            filter: false,
            templates: false,
            periodic: false,
            uidWelcome: false,
        });
        function toggleSection(key) {
            const next = !configSections.value[key];
            // 收起所有
            for (const k in configSections.value) configSections.value[k] = false;
            // 只打开点击的那个
            configSections.value[key] = next;
        }

        // LLM Config
        const llmEnabled = ref(false);
        const llmProvider = ref('openai');
        const llmApiKey = ref('');
        const llmApiKeyReal = ref('');  // 真实的 API key（不掩码）
        const showMsTip = ref(false);   // 魔搭免费额度提示：详细说明是否展开
        const msPicked = ref(false);    // 点过「一键填入魔搭配置」
        const MS_BASE_URL = 'https://api-inference.modelscope.cn/v1';
        const MS_MODEL = 'Qwen/Qwen2.5-7B-Instruct';
        const llmBaseUrl = ref('');
        const llmModel = ref('');
        // 一键把接口格式 / Base URL 填成魔搭的（用户只需要粘贴自己领的 Key）
        // 模型名只在没填的时候才补默认值，避免覆盖用户已经配好能用的模型
        function applyModelScope() {
            llmProvider.value = 'openai';       // 魔搭走 OpenAI 兼容接口
            llmBaseUrl.value = MS_BASE_URL;
            if (!llmModel.value) {
                llmModel.value = MS_MODEL;
            }
            msPicked.value = true;
        }
        const llmWakeWord = ref('ayabot');
        const llmTemp = ref(0.7);
        const llmTopP = ref(0.9);
        const llmMaxTokens = ref(150);
        const llmPrompt = ref('');
        const llmSaveMsg = ref('');
        const llmSaveOk = ref(false);
        const llmTestText = ref('');
        const llmTestResp = ref('');

        // LLM Context Config
        const ctxEnabled = ref(true);
        const ctxMode = ref('isolated');
        const ctxContent = ref('llm_only');
        const ctxMaxMsg = ref(10);

        // General Config
        const cfgHost = ref('0.0.0.0');
        const cfgPort = ref(19810);
        const cfgRoomId = ref(0);
        const cfgAnchorUid = ref(0);
        const cfgWelcomeCd = ref(600);
        const cfgThanksCd = ref(10);
        const cfgSendInterval = ref(1.2);
        const cfgRetry = ref(2);
        const cfgMaxQueue = ref(50);
        const cfgReplyDelay = ref(1.0);
        const cfgWelcomeOn = ref(true);
        const cfgThanksOn = ref(true);
        const cfgBlindboxOn = ref(true);
        const cfgGuardOn = ref(true);
        const cfgConnectedMsg = ref(false);
        const cfgWelcomeTmpl = ref('');
        const cfgThanksTmpl = ref('');
        const cfgGuardCaptain = ref('');
        const cfgGuardCommander = ref('');
        const cfgGuardGovernor = ref('');
        const cfgGuardDefault = ref('');
        const cfgConnMsg = ref('');
        const cfgPeriodicOn = ref(true);
        const cfgPeriodicInterval = ref(600);
        const cfgPeriodicTmpl = ref('');
        const cfgSaveMsg = ref('');
        const cfgSaveOk = ref(false);
        const restartMsg = ref('');
        const restartOk = ref(false);

        // B站 登录
        let biliPollTimer = null;
        const biliLoginState = ref('idle');
        const biliQrImage = ref('');
        const biliLoginError = ref('');
        const biliSessionId = ref('');

        let chartInst = null;

        // ── Auth ──
        async function doLogin() {
            loginErr.value = '';
            try {
                const res = await fetch('/api/login', {
                    method: 'POST',
                    headers: {'Content-Type':'application/json'},
                    body: JSON.stringify({username: loginUser.value, password: loginPass.value})
                });
                if (!res.ok) { loginErr.value = '账号或密码错误'; return; }
                const data = await res.json();
                loggedIn.value = true;
                userRole.value = data.role || '';
                if (!loginUser.value && data.username) loginUser.value = data.username;
                if (data.must_reset_password) {
                    mustResetPwd.value = true;
                    showChangePwd.value = true;
                    changePwdNewUser.value = loginUser.value;
                    changePwdOld.value = loginPass.value; // 默认密码即登录密码
                    changePwdNew.value = '';
                    changePwdConfirm.value = '';
                    changePwdMsg.value = '⚠️ 首次登录请先修改默认密码';
                    changePwdOk.value = false;
                    return;
                }
                await loadLlmConfig();
                await loadGeneralConfig();
                await loadRooms();
                await loadAccounts();
                await loadUsers();
                await loadTemplates();
                // 房间状态/凭证失效需要实时反映（守护进程会自动重启/等待登录）
                if (!window.__roomStatusTimer) {
                    window.__roomStatusTimer = setInterval(() => {
                        if (loggedIn.value) loadRooms();
                    }, 15000);
                }
                // 进去后静默查一次更新：有新版本就在导航栏亮提示，不弹窗打断
                if (!window.__updateTimer) {
                    window.__updateTimer = setTimeout(() => { silentCheckUpdate(); }, 4000);
                }
            } catch(e) { loginErr.value = '登录失败: ' + e.message; }
        }
        function doLogout() {
            document.cookie = 'session=;max-age=0';
            loggedIn.value = false;
            tab.value = 'rooms';
            userRole.value = '';
            showUserMenu.value = false;
        }

        // ── Helpers ──
        function proxyImg(url) {
            if (!url) return '';
            if (url.startsWith('data:') || url.startsWith('blob:')) return url;
            if (url.startsWith('/api/')) return url;
            return '/api/proxy_image?url=' + encodeURIComponent(url);
        }
        function fmtTime(ts) {
            if (!ts) return '';
            const d = new Date(ts * 1000);
            return d.toLocaleTimeString('zh-CN', {hour:'2-digit',minute:'2-digit'});
        }
        function cardBgClass(guardLevel) {
            if (guardLevel === 3) return 'bg-captain';
            if (guardLevel === 2) return 'bg-commander';
            if (guardLevel === 1) return 'bg-governor';
            return 'bg-default';
        }
        function guardLabel(guardLevel) {
            if (guardLevel === 3) return '舰长';
            if (guardLevel === 2) return '提督';
            if (guardLevel === 1) return '总督';
            return '';
        }
        function guardBadgeClass(guardLevel) {
            if (guardLevel === 3) return 'bg-blue-500';
            if (guardLevel === 2) return 'bg-purple-600';
            if (guardLevel === 1) return 'bg-amber-500';
            return '';
        }

        // ── Room Detail ──
        function selectRoom(r) {
            selectedRoom.value = r;
            roomSubTab.value = 'ranking';
            selectedRoomAccount.value = r.account_uid || '';
            // 清除上一个房间的查询状态
            _clearRoomState();
            // 加载房间 API 配置
            loadRoomApiConfig();
            // 上舰记录自动加载（排行仍需点「查询」）
            loadGuards();
        }
        function goBackRoomList() {
            selectedRoom.value = null;
            roomSubTab.value = 'ranking';
            _clearRoomState();
        }
        function _clearRoomState() {
            ranking.value = [];
            errRanking.value = '';
            guardItems.value = [];
            guardTotals.value = null;
            exportList.value = [];
            exportDates.value = [];
            exportDatesSet.value = new Set();
            errExport.value = '';
            eModeAll.value = false;
            eUid.value = 0;
            eName.value = '';
            eDate.value = new Date().toISOString().slice(0,10);
            eSelectedDates.value = [new Date().toISOString().slice(0,10)];
            eAllUserDates.value = [];
            eType.value = 'all';
            eSort.value = 'uname';
            eMergeGifts.value = false;
            ePerCol.value = 6;
            eColWidth.value = 340;
            exporting.value = false;
            showCalendar.value = false;
            roomConfig.value = null;
        }
        function startEditRoomName() {
            roomNameEdit.value = selectedRoom.value?.room_name || '';
            editingRoomName.value = true;
        }
        async function saveRoomName() {
            const name = roomNameEdit.value?.trim() || '';
            const rid = selectedRoom.value?.room_id;
            if (!rid) return;
            editingRoomName.value = false;
            try {
                const res = await fetch(`/api/rooms/${rid}/config`, {
                    method: 'POST', headers: {'Content-Type':'application/json'}, credentials: 'include',
                    body: JSON.stringify({room_name: name}),
                });
                const data = await res.json();
                if (data.ok) {
                    selectedRoom.value.room_name = name;
                    await loadRooms();
                }
            } catch(e) { /* ignore */ }
        }
        function exportRoomConfig() {
            const rid = selectedRoom.value?.room_id;
            if (!rid) return;
            downloadJson('/api/rooms/'+rid+'/config/export', 'room_'+rid+'_config.json');
        }
        function importRoomConfig() {
            const rid = selectedRoom.value?.room_id;
            if (!rid) return;
            importJsonFile('选择机器人配置 JSON','/api/rooms/'+rid+'/config/import',()=>editRoomConfig(rid));
        }
        async function afterImportLlm() {
            // 导入全局 LLM 配置后，如果在房间内还需同步写入房间配置
            if (selectedRoom.value?.room_id) {
                try {
                    const r = await fetch('/api/llm_config/export', {credentials:'include'});
                    const d = await r.json();
                    await fetch('/api/rooms/'+selectedRoom.value.room_id+'/config', {
                        method:'POST', headers:{'Content-Type':'application/json'},
                        credentials:'include', body:JSON.stringify({llm:d}),
                    });
                } catch(e) { /* best-effort */ }
            }
            editRoomConfig(selectedRoom?.value?.room_id);
            setTimeout(loadLlmConfig, 300);
        }
        async function selectRoomSubTab(key) {
            roomSubTab.value = key;
            if ((key === 'config' || key === 'llm') && selectedRoom.value) {
                editRoomConfig(selectedRoom.value.room_id);
            }
            if (key === 'llm') {
                // AI 页面启动后等待 roomConfig 加载完毕再刷新 LLM 表单
                setTimeout(() => loadLlmConfig(), 100);
            }
            if (key === 'danmaku') {
                danmakuOffset.value = 0;
                dmSelectedDates.value = new Set();
                await loadDmDates();
                loadDanmakuLog();
                loadDanmakuSessions();
                loadDanmakuUsers();
            }
            if (key === 'export') {
                loadUserDates();
            }
            if (key === 'ranking') {
                loadGuards();
            }
        }
        function toggleCreateRoom() { showCreateRoom.value = !showCreateRoom.value; }
        function toggleNewAccount() { showNewAccount.value = !showNewAccount.value; }
        // 登录失效时的一键恢复：跳到「用户管理 → B站账号」并直接开二维码
        async function goRelogin() {
            tab.value = 'users';
            showNewAccount.value = true;
            accountQrState.value = 'idle';
            accountQrError.value = '';
            window.scrollTo({ top: 0, behavior: 'smooth' });
            await startAccountLogin();
        }
        async function assignAccountToRoom() {
            const rid = selectedRoom.value?.room_id;
            if (!rid) return;
            accountAssignMsg.value = '';
            try {
                const res = await fetch(`/api/rooms/${rid}/config`, {
                    method: 'POST',
                    headers: {'Content-Type':'application/json'},
                    credentials: 'include',
                    body: JSON.stringify({account_uid: selectedRoomAccount.value || ''}),
                });
                const data = await res.json();
                if (data.ok) {
                    accountAssignMsg.value = '✅ 已保存';
                    accountAssignOk.value = true;
                    selectedRoom.value.account_uid = selectedRoomAccount.value;
                    await loadRooms();
                    await loadAccounts();
                } else {
                    accountAssignMsg.value = '❌ 保存失败';
                    accountAssignOk.value = false;
                }
            } catch(e) {
                accountAssignMsg.value = '❌ 保存失败';
                accountAssignOk.value = false;
            }
        }
        async function assignAccountAndRestart() {
            const rid = selectedRoom.value?.room_id;
            if (!rid) return;
            accountAssignMsg.value = '';
            accountRestarting.value = true;
            try {
                // 先保存账号
                const res = await fetch(`/api/rooms/${rid}/config`, {
                    method: 'POST',
                    headers: {'Content-Type':'application/json'},
                    credentials: 'include',
                    body: JSON.stringify({account_uid: selectedRoomAccount.value || ''}),
                });
                const data = await res.json();
                if (!data.ok) throw new Error('保存失败');
                // 再重启 bot
                const restartRes = await fetch(`/api/rooms/${rid}/restart`, {
                    method: 'POST', credentials: 'include',
                });
                if (!restartRes.ok) throw new Error('重启失败');
                accountAssignMsg.value = '✅ 已保存并重启';
                accountAssignOk.value = true;
                selectedRoom.value.account_uid = selectedRoomAccount.value;
                selectedRoom.value.status = 'running';
                await loadRooms();
                await loadAccounts();
            } catch(e) {
                accountAssignMsg.value = '❌ ' + e.message;
                accountAssignOk.value = false;
            } finally {
                accountRestarting.value = false;
            }
        }

        // ── Accounts Management ──
        async function loadAccounts() {
            try {
                const res = await fetch('/api/bili_accounts', {credentials: 'include'});
                if (res.status === 401) { loggedIn.value = false; return; }
                if (!res.ok) return;
                const data = await res.json();
                accounts.value = data.accounts || [];
            } catch(e) { /* ignore */ }
        }
        async function startAccountLogin() {
            accountLoggingIn.value = true;
            accountQrState.value = 'loading';
            accountQrError.value = '';
            if (accountsPollTimer) { clearInterval(accountsPollTimer); accountsPollTimer = null; }
            accountQrImage.value = '';
            try {
                const res = await fetch('/api/bili_accounts', {
                    method: 'POST',
                    headers: {'Content-Type':'application/json'},
                    credentials: 'include',
                    body: JSON.stringify({}),
                });
                if (!res.ok) throw new Error('请求失败');
                const data = await res.json();
                if (!data.ok) throw new Error(data.error || '生成二维码失败');
                accountQrImage.value = data.qr_image;
                accountSessionId.value = data.session_id;
                accountQrState.value = 'waiting';
                accountsPollTimer = setInterval(pollAccountLogin, 2000);
            } catch(e) {
                accountQrError.value = e.message;
                accountQrState.value = 'error';
            } finally {
                accountLoggingIn.value = false;
            }
        }
        function refreshQrCode() {
            // 停止旧轮询，重新生成二维码
            if (accountsPollTimer) { clearInterval(accountsPollTimer); accountsPollTimer = null; }
            accountSessionId.value = '';
            accountQrImage.value = '';
            accountQrState.value = 'idle';
            accountQrError.value = '';
            startAccountLogin();
        }
        async function pollAccountLogin() {
            if (!accountSessionId.value) return;
            try {
                const res = await fetch('/api/bili_accounts/status?session_id=' + accountSessionId.value, {
                    credentials: 'include',
                });
                if (!res.ok) return;
                const data = await res.json();
                if (data.state === 'done') {
                    accountQrState.value = 'done';
                    if (accountsPollTimer) { clearInterval(accountsPollTimer); accountsPollTimer = null; }
                    const saved = await saveAccountLogin();
                    if (!saved) {
                        // 保存失败：停留在错误状态，不关闭面板
                        return;
                    }
                    // 登录成功，自动关闭二维码面板
                    setTimeout(() => {
                        showNewAccount.value = false;
                        accountQrState.value = 'idle';
                        accountQrImage.value = '';
                        accountSessionId.value = '';
                    }, 1500);
                } else if (data.state === 'scanned') {
                    accountQrState.value = 'scanned';
                } else if (data.state === 'timeout') {
                    accountQrState.value = 'timeout';
                    if (accountsPollTimer) { clearInterval(accountsPollTimer); accountsPollTimer = null; }
                } else if (data.state === 'error') {
                    accountQrError.value = data.message || '登录失败';
                    accountQrState.value = 'error';
                    if (accountsPollTimer) { clearInterval(accountsPollTimer); accountsPollTimer = null; }
                }
                // 不处理 'waiting' - 保持当前状态
            } catch(e) { /* ignore */ }
        }
        async function saveAccountLogin() {
            let ok = false;
            try {
                const res = await fetch('/api/bili_accounts/save', {
                    method: 'POST',
                    headers: {'Content-Type':'application/json'},
                    credentials: 'include',
                    body: JSON.stringify({session_id: accountSessionId.value}),
                });
                const data = await res.json().catch(() => ({}));
                if (data.ok) {
                    ok = true;
                } else {
                    accountQrError.value = data.error || '保存凭据失败';
                }
            } catch(e) {
                accountQrError.value = '保存失败: ' + e.message;
            }
            if (!ok) {
                accountQrState.value = 'error';
            }
            await loadAccounts();
            // 扫码成功：机器人会自动拾取新凭证，刷新房间状态让提示消失
            await loadRooms();
            return ok;
        }
        async function refreshAccount(uid) {
            // 目前没有单独的刷新 API，重新加载列表
            await loadAccounts();
        }
        async function deleteAccount(uid, nickname) {
            if (!confirm(`⚠️ 确定删除 B站账号「${nickname || uid}」（${uid}）？`)) return;
            try {
                const res = await fetch(`/api/bili_accounts/${uid}`, {
                    method: 'DELETE', credentials: 'include',
                });
                if (!res.ok) throw new Error((await res.text()).slice(0,80));
                await loadAccounts();
            } catch(e) { alert('删除失败: ' + e.message); }
        }
        const editingNickname = ref(null);
        function startEditNickname(a) {
            a.editNick = a.nickname || '';
            editingNickname.value = a.uid;
        }
        async function saveNickname(a) {
            const nick = a.editNick?.trim();
            if (!nick) return;
            try {
                const res = await fetch(`/api/bili_accounts/${a.uid}/nickname`, {
                    method: 'POST',
                    headers: {'Content-Type':'application/json'},
                    credentials: 'include',
                    body: JSON.stringify({nickname: nick}),
                });
                if (!res.ok) throw new Error((await res.text()).slice(0,80));
                a.nickname = nick;
                editingNickname.value = null;
            } catch(e) { alert('修改失败: ' + e.message); }
        }
        // ── 验证队列（串行执行，避免并发卡顿） ──
        const verifyQueue = ref([]);
        const verifyingAll = ref(false);
        let _verifyProcessing = false;
        async function _processVerifyQueue() {
            if (_verifyProcessing || verifyQueue.value.length === 0) return;
            _verifyProcessing = true;
            while (verifyQueue.value.length > 0) {
                const uid = verifyQueue.value.shift();
                const acct = accounts.value.find(a => a.uid === uid);
                if (!acct) continue;
                acct.verifying = true;
                try {
                    const res = await fetch(`/api/bili_accounts/${uid}/verify`, {
                        method: 'POST', credentials: 'include',
                    });
                    const data = await res.json();
                    acct.credential_ok = data.valid;
                } catch(e) { acct.credential_ok = false; }
                finally { acct.verifying = false; }
            }
            verifyingAll.value = false;
            _verifyProcessing = false;
        }
        async function verifyAccount(uid) {
            const acct = accounts.value.find(a => a.uid === uid);
            if (!acct || acct.verifying) return;
            if (verifyQueue.value.includes(uid)) return;
            verifyQueue.value.push(uid);
            _processVerifyQueue();
        }
        async function verifyAllAccounts() {
            if (!accounts.value.length) return;
            verifyingAll.value = true;
            for (const a of accounts.value) {
                if (!a.verifying && !verifyQueue.value.includes(a.uid)) {
                    verifyQueue.value.push(a.uid);
                }
            }
            _processVerifyQueue();
        }

        // ── Ranking ──
        async function loadRanking() {
            errRanking.value = '';
            ranking.value = [];
            const roomId = selectedRoom.value?.room_id;
            if (!roomId) return;
            // 日期校验：确保 start <= end
            if (rStart.value && rEnd.value && rStart.value > rEnd.value) {
                errRanking.value = '起始日期不能晚于终止日期';
                return;
            }
            try {
                const res = await fetch(`/api/rooms/${roomId}/ranking?rStart=${rStart.value}&rEnd=${rEnd.value}&rType=${rType.value}`);
                if (!res.ok) { const txt = await res.text(); throw new Error(txt.slice(0,80)); }
                const data = await res.json();
                ranking.value = (data.ranking || []).map(u => ({
                    uid: u.uid, uname: u.uname, total_val: u.total,
                    total_profit: u.total_profit || 0
                }));
            } catch(e) { errRanking.value = '加载失败: ' + e.message; }
            await nextTick();
            updateChart();
            loadGuards();
        }
        function updateChart() {
            const canvas = document.getElementById('chartRank');
            if (!canvas) return;
            if (chartInst) chartInst.destroy();
            if (!ranking.value.length) return;
            chartInst = new Chart(canvas, {
                type: 'bar',
                data: {
                    labels: ranking.value.map(u=>u.uname),
                    datasets: [{
                        label: '送礼价值',
                        data: ranking.value.map(u=>Number(u.total_val)),
                        backgroundColor: 'rgba(59,130,246,0.6)',
                        borderRadius: 4
                    }]
                },
                options: { responsive: true, maintainAspectRatio: false, plugins: { legend: { display: false } } }
            });
        }

        // ── Export ──
        async function loadUserDates() {
            const roomId = selectedRoom.value?.room_id;
            if (!roomId) return;

            if (eModeAll.value) {
                // 加载所有人有数据的日期
                try {
                    const res = await fetch(`/api/rooms/${roomId}/all_dates`);
                    if (!res.ok) return;
                    const arr = await res.json();
                    eAllUserDates.value = arr;
                    exportDatesSet.value = new Set(arr);
                } catch(e) { /* ignore */ }
                return;
            }

            if (!eUid.value) return;
            try {
                const res = await fetch(`/api/rooms/${roomId}/user_dates?uid=${eUid.value}`);
                if (!res.ok) return;
                const arr = await res.json();
                exportDates.value = arr;
                exportDatesSet.value = new Set(arr);
            } catch(e) { /* ignore */ }
        }
        function onModeChange() {
            showCalendar.value = false;
            exportList.value = [];
            errExport.value = '';
            eSelectedDates.value = eModeAll.value ? [] : [new Date().toISOString().slice(0,10)];
            eDate.value = new Date().toISOString().slice(0,10);
            loadUserDates();
        }
        function onUidInput() {
            showCalendar.value = false;
            exportList.value = [];
            errExport.value = '';
            loadUserDates();
        }
        // 排序辅助函数（已迁移到 exportCols computed 中）
        // 保留空函数供 watch 调用时安全
        function onSortChange($event) {
            eSort.value = $event.target.value;
        }
        function toggleDate(ymd) {
            // 多选模式（单用户和所有人模式都可以多选）
            const arr = eSelectedDates.value.slice();
            const idx = arr.indexOf(ymd);
            if (idx >= 0) {
                arr.splice(idx, 1);
            } else {
                arr.push(ymd);
            }
            eSelectedDates.value = arr;
        }
        function selectAllDatesInRange() {
            const arr = eSelectedDates.value.slice();
            calDays.value.forEach(day => {
                if (day && day.hasData && arr.indexOf(day.ymd) === -1) arr.push(day.ymd);
            });
            eSelectedDates.value = arr;
        }
        function clearSelectedDates() {
            eSelectedDates.value = [];
        }
        async function applyMultiDateExport() {
            showCalendar.value = false;
            await loadExport();
        }
        function pickDate(ymd) {
            eDate.value = ymd;
            eSelectedDates.value = [ymd];
            showCalendar.value = false;
            loadExport();
        }
        async function loadExport() {
            errExport.value = '';
            exportList.value = [];
            loadingExport.value = true;
            const roomId = selectedRoom.value?.room_id;
            if (!roomId) { loadingExport.value = false; return; }

            if (eModeAll.value) {
                // 所有人模式
                const sel = eSelectedDates.value.slice().sort();
                let dateFrom = '', dateTo = '';
                if (sel.length === 1) {
                    dateFrom = sel[0];
                    dateTo = sel[0];
                } else if (sel.length > 1) {
                    dateFrom = sel[0];
                    dateTo = sel[sel.length-1];
                } else {
                    errExport.value = '请至少选择一个日期';
                    loadingExport.value = false;
                    return;
                }
                try {
                    const params = new URLSearchParams({ gift_type: eType.value, sort: eSort.value });
                    if (dateFrom) params.set('date_from', dateFrom);
                    if (dateTo) params.set('date_to', dateTo);
                    const res = await fetch(`/api/rooms/${roomId}/export_all?${params}`);
                    if (!res.ok) { const txt = await res.text(); errExport.value = '请求失败: ' + txt.slice(0,80); loadingExport.value = false; return; }
                    const data = await res.json();
                    exportList.value = (data || []).map((item, idx) => ({
                        ...item,
                        id: item.id || idx,
                        gift_num: item.gift_num || 0,
                        price: item.actual_value || 0,
                        ts: typeof item.ts === 'number' ? item.ts : 0,
                        avatar: item.avatar || '',
                        guard_level: item.guard_level || 0,
                        gift_icon: item.gift_icon || '',
                    }));
                    if (!exportList.value.length) {
                        errExport.value = '所选日期范围内无送礼记录';
                    }
                } catch(e) { errExport.value = '加载失败: ' + e.message; }
                loadingExport.value = false;
                return;
            }

            // 单用户模式（同样支持多选日期）
            if (!eUid.value) { errExport.value = '请填写 UID'; loadingExport.value = false; return; }
            const sel2 = eSelectedDates.value.slice().sort();
            let dateFrom2 = '', dateTo2 = '';
            if (sel2.length === 1) {
                dateFrom2 = sel2[0];
                dateTo2 = sel2[0];
            } else if (sel2.length > 1) {
                dateFrom2 = sel2[0];
                dateTo2 = sel2[sel2.length-1];
            } else {
                errExport.value = '请至少选择一个日期';
                loadingExport.value = false;
                return;
            }
            try {
                const params = new URLSearchParams({ gift_type: eType.value, sort: eSort.value, uid: eUid.value });
                if (dateFrom2) params.set('date_from', dateFrom2);
                if (dateTo2) params.set('date_to', dateTo2);
                const res = await fetch(`/api/rooms/${roomId}/export_all?${params}`);
                if (!res.ok) { const txt = await res.text(); errExport.value = '请求失败: ' + txt.slice(0,80); loadingExport.value = false; return; }
                const data = await res.json();
                exportList.value = (data || []).map((item, idx) => ({
                    ...item,
                    id: item.id || idx,
                    gift_num: item.gift_num || 0,
                    price: item.actual_value || 0,
                    ts: typeof item.ts === 'number' ? item.ts : 0,
                    avatar: item.avatar || '',
                    guard_level: item.guard_level || 0,
                    gift_icon: item.gift_icon || '',
                }));
                if (exportList.value.length) {
                    eName.value = exportList.value[0].uname || '';
                } else {
                    errExport.value = '该用户所选日期范围内无送礼记录';
                }
            } catch(e) { errExport.value = '加载失败: ' + e.message; }
            loadingExport.value = false;
        }
        async function captureExport() {
            exporting.value = true;
            const el = document.getElementById('capture');
            if (!el) { exporting.value = false; return; }
            if (typeof window.modernScreenshot === 'undefined') { alert('截图库加载中，请稍后重试'); exporting.value = false; return; }
            // 0. 先确保原 DOM 所有图片已加载完成
            const origImgs = Array.from(el.querySelectorAll('img'));
            await Promise.all(origImgs.map(img => {
                if (img.complete && img.naturalWidth > 0) return Promise.resolve();
                return new Promise(resolve => { img.onload = resolve; img.onerror = resolve; });
            }));
            // 多等一帧让浏览器完成布局
            await new Promise(r => requestAnimationFrame(r));

            // 1. 【精准测量】在克隆前拿到原 DOM 真实内容尺寸
            const innerGrid = el.querySelector('.capture-grid') || el.querySelector('.capture-inner') || el;
            const targetWidth = innerGrid.scrollWidth;
            const targetHeight = el.scrollHeight;

            // 2. 离屏克隆
            const clone = el.cloneNode(true);

            // 3. 在挂载前给所有 img 补上 crossorigin，确保 Canvas 可读
            clone.querySelectorAll('img').forEach(img => {
                // 如果是已通过 proxy 加载的本地图片，不需要 crossorigin
                const src = img.getAttribute('src') || '';
                if (src.startsWith('/api/proxy_image')) {
                    // 跳过已缓存的本地代理图片
                } else {
                    img.setAttribute('crossorigin', 'anonymous');
                }
            });

            // 4. 锁定克隆节点宽高
            clone.style.width = targetWidth + 'px';
            clone.style.minWidth = targetWidth + 'px';
            clone.style.maxWidth = targetWidth + 'px';
            clone.style.overflow = 'visible';
            clone.style.overflowX = 'visible';
            clone.style.maxHeight = 'none';

            // 5. 挂载到离屏容器
            const container = document.createElement('div');
            container.style.position = 'fixed';
            container.style.left = '-9999px';
            container.style.top = '0';
            container.style.zIndex = '-1000';
            container.style.pointerEvents = 'none';
            container.className = document.body.className;
            container.appendChild(clone);
            document.body.appendChild(container);

            // 6. 等待克隆中的所有图片完全加载
            await Promise.all(Array.from(clone.querySelectorAll('img')).map(img => {
                // 强制重新加载（克隆后浏览器可能用缓存，但 crossorigin 变化需要重载）
                if (img.complete && img.naturalWidth > 0) return Promise.resolve();
                return new Promise(resolve => {
                    let done = false;
                    img.onload = () => { if (!done) { done = true; resolve(); } };
                    img.onerror = () => { if (!done) { done = true; resolve(); } };
                    // 超时保护：5秒后无论如何继续
                    setTimeout(() => { if (!done) { done = true; resolve(); } }, 5000);
                });
            }));

            // 7. 等两帧完成布局重排与字体/图片渲染
            await new Promise(r => requestAnimationFrame(r));
            await new Promise(r => requestAnimationFrame(r));
            // 额外加 200ms 确保 modernScreenshot 内部也完成
            await new Promise(r => setTimeout(r, 200));

            try {
                const dataUrl = await window.modernScreenshot.domToPng(clone, {
                    scale: 2,
                    backgroundColor: null,
                    width: targetWidth,
                    height: targetHeight,
                    features: {
                        router: false,
                    },
                });
                const link = document.createElement('a');
                const dateStr = eDateLabel.value || eDate.value;
                const namePart = eModeAll.value ? '所有人' : (eName.value || eUid.value);
                link.download = `${namePart}_${dateStr}_礼物明细.png`;
                link.href = dataUrl;
                link.click();
            } catch(e) {
                alert('导出失败: ' + e.message);
            } finally {
                exporting.value = false;
                if (container.parentNode) container.parentNode.removeChild(container);
            }
        }
        function fmtDateTime(ts, showDate) {
            if (!ts) return '';
            const d = new Date(ts * 1000);
            if (showDate) {
                const mo = String(d.getMonth()+1).padStart(2,'0');
                const dd = String(d.getDate()).padStart(2,'0');
                return `${mo}-${dd} ${d.toLocaleTimeString('zh-CN', {hour:'2-digit',minute:'2-digit'})}`;
            }
            return d.toLocaleTimeString('zh-CN', {hour:'2-digit',minute:'2-digit'});
        }
        function gotoExport(uid, uname) {
            eModeAll.value = false;
            eUid.value = uid;
            eName.value = uname || '';
            roomSubTab.value = 'export';
            showCalendar.value = false;
            const today = new Date().toISOString().slice(0,10);
            eSelectedDates.value = [today];
            eDate.value = today;
            exportDates.value = [];
            exportList.value = [];
            errExport.value = '';
            loadUserDates();
        }

        // ── Delete ──
        async function confirmDelete(type) {
            if (!delDate.value) { delResult.value = '请选择日期'; return; }
            const label = type === 'gift' ? '送礼' : '弹幕';
            if (!confirm(`确定删除 ${delDate.value} 之前的所有${label}记录？此操作不可恢复！`)) return;
            const roomId = selectedRoom.value?.room_id;
            if (!roomId) return;
            try {
                const res = await fetch(`/api/rooms/${roomId}/delete_old`, {
                    method: 'POST',
                    headers: {'Content-Type':'application/json'},
                    body: JSON.stringify({date: delDate.value, type: type})
                });
                if (!res.ok) throw new Error((await res.text()).slice(0,80));
                const data = await res.json();
                const parts = [];
                if (data.deleted_gifts > 0) parts.push(`${data.deleted_gifts} 条送礼`);
                if (data.deleted_danmaku > 0) parts.push(`${data.deleted_danmaku} 条弹幕`);
                delResult.value = parts.length ? `已删除 ${parts.join('、')}` : '没有需要删除的数据';
            } catch(e) { delResult.value = '删除失败: ' + e.message; }
        }

        // ── 房间 API 配置 ──
        async function loadRoomApiConfig() {
            const rid = selectedRoom.value?.room_id;
            if (!rid) return;
            try {
                const res = await fetch(`/api/rooms/${rid}/api_config`);
                if (!res.ok) return;
                const data = await res.json();
                roomApiEnabled.value = data.api_enabled;
                roomApiUrl.value = data.api_url || '';
                roomApiFullKey.value = data.full_key || '';
            } catch(e) {}
        }

        async function toggleRoomApi() {
            const rid = selectedRoom.value?.room_id;
            if (!rid) return;
            roomApiBusy.value = true;
            apiMsg.value = '';
            apiMsgOk.value = false;
            try {
                const res = await fetch(`/api/rooms/${rid}/api_toggle`, { method: 'POST' });
                const data = await res.json();
                if (data.ok) {
                    roomApiEnabled.value = data.api_enabled;
                    apiMsg.value = data.message;
                    apiMsgOk.value = true;
                    // 如果开启了且没完整密钥，刷新配置
                    if (data.api_enabled && !roomApiFullKey.value) {
                        await loadRoomApiConfig();
                    }
                } else {
                    apiMsg.value = data.error || '操作失败';
                    apiMsgOk.value = false;
                }
            } catch(e) {
                apiMsg.value = '操作失败: ' + e.message;
            } finally {
                roomApiBusy.value = false;
            }
        }

        async function regenerateRoomApiKey() {
            const rid = selectedRoom.value?.room_id;
            if (!rid) return;
            roomApiBusy.value = true;
            apiMsg.value = '';
            apiMsgOk.value = false;
            try {
                const res = await fetch(`/api/rooms/${rid}/api_regenerate`, { method: 'POST' });
                const data = await res.json();
                if (data.ok) {
                    roomApiEnabled.value = true;
                    roomApiFullKey.value = data.full_key;
                    apiMsg.value = data.message;
                    apiMsgOk.value = true;
                } else {
                    apiMsg.value = data.error || '生成失败';
                }
            } catch(e) {
                apiMsg.value = '生成失败: ' + e.message;
            } finally {
                roomApiBusy.value = false;
            }
        }

        function copyText(text, msgRef) {
            if (!text) return;
            const target = msgRef || 'apiMsg';
            navigator.clipboard.writeText(text).then(() => {
                if (target === 'apiMsg') { apiMsg.value = '✅ 已复制到剪贴板'; apiMsgOk.value = true; }
                setTimeout(() => { if (target === 'apiMsg') apiMsg.value = ''; }, 2000);
            }).catch(() => {
                const ta = document.createElement('textarea');
                ta.value = text;
                document.body.appendChild(ta);
                ta.select();
                document.execCommand('copy');
                document.body.removeChild(ta);
                if (target === 'apiMsg') { apiMsg.value = '✅ 已复制到剪贴板'; apiMsgOk.value = true; }
                setTimeout(() => { if (target === 'apiMsg') apiMsg.value = ''; }, 2000);
            });
        }

        // ── Bot Log ──
        const botLogContent = ref('');
        const logLevel = ref('INFO');
        const logContainer = ref(null);
        async function loadBotLog() {
            if (!selectedRoom.value?.room_id) return;
            try {
                const res = await fetch(`/api/rooms/${selectedRoom.value.room_id}/log?lines=500`, {credentials: 'include'});
                if (!res.ok) return;
                const data = await res.json();
                if (data.error) { botLogContent.value = '加载失败: ' + data.error; return; }
                const lines = data.lines || [];
                botLogContent.value = lines.map(l => {
                    return l
                        .replace(/ERROR/g, '<span class="text-red-400">ERROR</span>')
                        .replace(/WARNING/g, '<span class="text-yellow-400">WARNING</span>')
                        .replace(/INFO/g, '<span class="text-green-300">INFO</span>')
                        .replace(/DEBUG/g, '<span class="text-gray-500">DEBUG</span>');
                }).join('\n');
                setTimeout(() => { if (logContainer.value) logContainer.value.scrollTop = logContainer.value.scrollHeight; }, 50);
            } catch(e) { botLogContent.value = '加载失败: ' + e.message; }
        }

        async function clearBotLog() {
            if (!selectedRoom.value?.room_id) return;
            if (!confirm('确定清空 Bot 日志？')) return;
            try {
                await fetch(`/api/rooms/${selectedRoom.value.room_id}/log/clear`, {method:'POST', credentials:'include'});
                botLogContent.value = '';
            } catch(e) { /* ignore */ }
        }

        // ── Danmaku Log ──
        async function loadDmDates() {
            const rid = selectedRoom.value?.room_id;
            if (!rid) return;
            try {
                const r = await fetch(`/api/rooms/${rid}/danmaku/dates`, {credentials:'include'});
                if (!r.ok) return;
                dmDates.value = await r.json();
                dmDatesSet.value = new Set(dmDates.value);
                // 默认仅显示最新一天（dmDates 为升序，最后一项即最新）；未选日期时才默认
                if (dmSelectedDates.value.size === 0 && dmDates.value.length) {
                    dmSelectedDates.value = new Set([dmDates.value[dmDates.value.length-1]]);
                }
            } catch(e) { /* ignore */ }
        }
        function dmToggleDate(ymd) {
            const s = new Set(dmSelectedDates.value);
            if (s.has(ymd)) s.delete(ymd); else s.add(ymd);
            dmSelectedDates.value = s;
        }
        // 日历弹窗开合并记录触发点视口坐标（Teleport 到 body 后需用 fixed 定位）
        function dmToggleCal(ev) {
            dmShowCal.value = !dmShowCal.value;
            if (dmShowCal.value && ev && ev.currentTarget) {
                const r = ev.currentTarget.getBoundingClientRect();
                dmCalPos.value = { top: r.bottom + 4, left: r.left };
            }
        }
        // 全选当月有数据的日期
        function dmSelectAllMonth() {
            const s = new Set(dmSelectedDates.value);
            const y = dmCalYear.value, m = dmCalMonth.value;
            const ymd = (d) => `${y}-${String(m+1).padStart(2,'0')}-${String(d).padStart(2,'0')}`;
            for (let d = 1; d <= new Date(y, m + 1, 0).getDate(); d++) {
                const k = ymd(d);
                if (dmDatesSet.value.has(k)) s.add(k);
            }
            dmSelectedDates.value = s;
        }
        // 清除所有选中日期
        function dmClearDates() {
            dmSelectedDates.value = new Set();
        }
        // 确定：关闭日历并按选中日期加载
        function dmCalOk() {
            dmShowCal.value = false;
            danmakuOffset.value = 0;
            dmSessionIdx.value = -1;
            loadDanmakuLog();
            loadDanmakuSessions();
        }
        async function loadDanmakuLog() {
            danmakuErr.value = '';
            const roomId = selectedRoom.value?.room_id;
            if (!roomId) return;
            // build date params
            const sel = Array.from(dmSelectedDates.value).sort();
            let df = '', dt = '';
            if (sel.length) { df = sel[0]; dt = sel[sel.length-1]; }
            dmDateFrom.value = df; dmDateTo.value = dt;
            // 场次查看模式：选中的场次用其精确时间戳范围过滤，替代日期参数
            let st = '', en = '';
            let tsdf = df, tsdt = dt;
            if (dmSessionIdx.value >= 0) {
                const s = dmSessions.value[dmSessionIdx.value];
                if (s) { st = String(s.start); en = String(s.end); }
            }
            const kw = dmSearchActive.value ? encodeURIComponent(dmSearchActive.value) : '';
            const url = `/api/danmaku_log?room_id=${roomId}&limit=${danmakuLimit.value}&offset=${danmakuOffset.value}&date_from=${tsdf}&date_to=${tsdt}&asc=${dmAsc.value ? 1 : 0}&keyword=${kw}&gap_sec=${dmGap.value}&start_ts=${st}&end_ts=${en}&uid=${dmUidFilter.value ? encodeURIComponent(dmUidFilter.value) : ''}&uname=${dmUserFilter.value ? encodeURIComponent(dmUserFilter.value) : ''}`;
            try {
                const res = await fetch(url, {credentials: 'include'});
                if (res.status === 401) { loggedIn.value = false; return; }
                if (!res.ok) throw new Error((await res.text()).slice(0,80));
                const data = await res.json();
                danmakuRows.value = data.rows || [];
                danmakuTotal.value = data.total || 0;
            } catch(e) { danmakuErr.value = '加载失败: ' + e.message; }
        }
        // 弹幕搜索：从第一页开始按关键词过滤
        function dmSearch() {
            const kw = dmKeyword.value.trim();
            if (!kw && !dmSearchActive.value) return;
            if (kw === dmSearchActive.value) return;
            dmSearchActive.value = kw || '';
            danmakuOffset.value = 0;
            loadDanmakuLog();
        }
        function clearDmSearch() {
            if (!dmSearchActive.value) return;
            dmSearchActive.value = '';
            dmKeyword.value = '';
            danmakuOffset.value = 0;
            loadDanmakuLog();
        }
        // —— 场次查看：直接选某一场直播看弹幕 ——
        function dmSessionLabel(s) {
            if (!s) return '';
            const z = (n) => String(n).padStart(2, '0');
            const d = new Date((s.start + (s.utc ? 0 : 0)) * 1000);
            return `${d.getFullYear()}-${z(d.getMonth()+1)}-${z(d.getDate())} ${z(d.getHours())}:${z(d.getMinutes())}`;
        }
        function dmSessionChanged() {
            danmakuOffset.value = 0;
            loadDanmakuLog();
            if (dmShowStats.value) loadDanmakuStats();
        }
        // 可搜索场次：按查询词过滤（匹配 场次号/日期时间/条数）
        const dmSessionFiltered = computed(() => {
            const q = (dmSessionQuery.value || '').trim().toLowerCase();
            if (!q) return dmSessions.value;
            return dmSessions.value.filter((s, i) => {
                const label = dmSessionLabel(s).toLowerCase();
                return ('场次' + (i + 1)).toLowerCase().includes(q)
                    || label.includes(q)
                    || String(s.count).includes(q);
            });
        });
        // 触发按钮上当前场次的展示标签
        const dmSessCurLabel = computed(() => {
            if (dmSessionIdx.value < 0) return '';
            const s = dmSessions.value[dmSessionIdx.value];
            return s ? `场次${dmSessionIdx.value + 1} · ${dmSessionLabel(s)} · ${s.count}条` : '';
        });
        function dmToggleSessionPanel() {
            dmShowSessionPanel.value = !dmShowSessionPanel.value;
            if (dmShowSessionPanel.value) dmSessionQuery.value = '';
        }
        // 从面板选中某场(-1=全部) 或点搜索框外关闭时共用
        function dmPickSession(i) {
            dmShowSessionPanel.value = false;
            dmSessionQuery.value = '';
            if (i === dmSessionIdx.value) return;
            dmSessionIdx.value = i;
            dmSessionChanged();
        }
        async function loadDanmakuSessions() {
            const roomId = selectedRoom.value?.room_id;
            if (!roomId) return;
            const df = dmDateFrom.value, dt = dmDateTo.value;
            const kw = dmSearchActive.value ? encodeURIComponent(dmSearchActive.value) : '';
            const uid = dmUidFilter.value ? encodeURIComponent(dmUidFilter.value) : '';
            const uname = dmUserFilter.value ? encodeURIComponent(dmUserFilter.value) : '';
            try {
                const res = await fetch(`/api/danmaku_sessions?room_id=${roomId}&date_from=${df}&date_to=${dt}&keyword=${kw}&gap_sec=${dmGap.value}&uid=${uid}&uname=${uname}`, {credentials: 'include'});
                if (!res.ok) return;
                const data = await res.json();
                dmSessions.value = data.sessions || [];
                if (dmSessionIdx.value >= dmSessions.value.length) dmSessionIdx.value = -1;
            } catch(e) { dmSessions.value = []; }
        }
        // 加载去重用户列表(供用户筛选下拉)，随日期/关键词变化刷新
        async function loadDanmakuUsers() {
            const roomId = selectedRoom.value?.room_id;
            if (!roomId) return;
            const df = dmDateFrom.value, dt = dmDateTo.value;
            const kw = dmSearchActive.value ? encodeURIComponent(dmSearchActive.value) : '';
            const {st, en} = dmSessionTs();
            try {
                const res = await fetch(`/api/danmaku_users?room_id=${roomId}&date_from=${df}&date_to=${dt}&keyword=${kw}&start_ts=${st}&end_ts=${en}`, {credentials: 'include'});
                if (!res.ok) return;
                const data = await res.json();
                dmUsers.value = data.users || [];
            } catch(e) { dmUsers.value = []; }
        }
        // 取当前选中场次的 ts 范围（未选时为空）
        function dmSessionTs() {
            if (dmSessionIdx.value >= 0) {
                const s = dmSessions.value[dmSessionIdx.value];
                if (s) return { st: String(s.start), en: String(s.end) };
            }
            return { st: '', en: '' };
        }
        // 加载弹幕统计
        async function loadDanmakuStats() {
            const roomId = selectedRoom.value?.room_id;
            if (!roomId) return;
            const df = dmDateFrom.value, dt = dmDateTo.value;
            const kw = dmSearchActive.value ? encodeURIComponent(dmSearchActive.value) : '';
            const uid = dmUidFilter.value ? encodeURIComponent(dmUidFilter.value) : '';
            const uname = dmUserFilter.value ? encodeURIComponent(dmUserFilter.value) : '';
            const {st, en} = dmSessionTs();
            try {
                const res = await fetch(`/api/danmaku_stats?room_id=${roomId}&date_from=${df}&date_to=${dt}&keyword=${kw}&start_ts=${st}&end_ts=${en}&uid=${uid}&uname=${uname}`, {credentials: 'include'});
                if (!res.ok) return;
                const data = await res.json();
                dmStats.value = data.stats || null;
            } catch(e) { dmStats.value = null; }
        }
        // 统计条形图百分比(相对最多的小时段，撑满 100%)
        function barPct(c) {
            const hours = (dmStats.value && dmStats.value.hours) || [];
            const max = hours.reduce((a,h) => Math.max(a, h.count), 1) || 1;
            return Math.min(100, Math.round((c / max) * 100));
        }
        // 清空用户名/UID 筛选
        function clearDmFilters() {
            dmUserFilter.value = '';
            dmUidFilter.value = '';
            danmakuOffset.value = 0;
            loadDanmakuLog();
            loadDanmakuUsers();
            if (dmShowStats.value) loadDanmakuStats();
        }
        // 弹幕高亮: 用 <mark> 包裹关键词 (v-html), 转义 HTML 防止注入
        function highlightDanmaku(text) {
            if (text == null) return '';
            const safe = String(text).replace(/[&<>"']/g, m => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[m]));
            const kw = dmSearchActive.value;
            if (!kw) return safe;
            let re;
            try { re = new RegExp(`(${kw.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')})`, 'gi'); }
            catch { return safe; }
            return safe.replace(re, '<mark style="background:#fde68a;color:#92400e;border-radius:2px;padding:0 1px">$1</mark>');
        }
        // 录像相对播放时间: 秒 -> H:MM:SS (不足1小时只显示 MM:SS)
        function fmtRelTime(rel) {
            if (rel == null || rel < 0) return '';
            rel = Math.floor(rel);
            const h = Math.floor(rel / 3600);
            const m = Math.floor((rel % 3600) / 60);
            const s = rel % 60;
            const mm = String(m).padStart(2, '0');
            const ss = String(s).padStart(2, '0');
            return h > 0 ? `${h}:${mm}:${ss}` : `${mm}:${ss}`;
        }
        // 录像划分间隔阈值改变: 重置到第一页重载
        function restartSessions() {
            danmakuOffset.value = 0;
            loadDanmakuLog();
        }
        async function dmExportSelected() {
            const rid = selectedRoom.value?.room_id;
            if (!rid || !dmSelectedDates.value.size) { alert('请先选择日期'); return; }
            const sel = Array.from(dmSelectedDates.value).sort();
            const a = dmAsc.value ? 1 : 0;
            await downloadUrl(`/api/rooms/${rid}/danmaku/export?date_from=${sel[0]}&date_to=${sel[sel.length-1]}&asc=${a}`, `danmaku_${rid}_${sel[0]}_${sel[sel.length-1]}.csv`);
        }
        async function clearDanmakuLog() {
            const rid = selectedRoom.value?.room_id;
            if (!rid) return;
            const sel = Array.from(dmSelectedDates.value).sort();
            const label = sel.length ? `所选 ${sel.length} 天的弹幕记录` : '所有弹幕记录';
            if (!confirm(`确定清空${label}？此操作不可恢复！`)) return;
            danmakuErr.value = '';
            try {
                let url = `/api/rooms/${rid}/danmaku/clear`;
                if (sel.length) url += `?date_from=${sel[0]}&date_to=${sel[sel.length-1]}`;
                const res = await fetch(url, {method: 'DELETE', credentials: 'include'});
                if (res.status === 401) { loggedIn.value = false; return; }
                if (!res.ok) throw new Error((await res.text()).slice(0,80));
                const data = await res.json();
                danmakuRows.value = [];
                danmakuOffset.value = 0;
                danmakuTotal.value = 0;
                dmSelectedDates.value = new Set();
                await loadDmDates();
                loadDanmakuLog();
            } catch(e) { danmakuErr.value = '清空失败: ' + e.message; }
        }
        function fmtDanmakuTime(ts) {
            if (!ts) return '';
            const d = new Date(ts * 1000);
            return d.toLocaleString('zh-CN', {month:'2-digit',day:'2-digit',hour:'2-digit',minute:'2-digit',second:'2-digit'});
        }
        // 翻页时自动重新加载弹幕
        Vue.watch([danmakuOffset, danmakuLimit], () => {
            if (selectedRoom.value?.room_id) loadDanmakuLog();
        });

        // 切换到数据管理标签时刷新房间 API 配置
        Vue.watch(roomSubTab, (val) => {
            if (val === 'manage' && selectedRoom.value) {
                loadRoomApiConfig();
            }
        });

        // ── LLM Config ──
        async function loadLlmConfig() {
            // 如果当前在房间详情中，从房间配置加载 LLM 设置
            if (selectedRoom.value) {
                // roomConfig 可能尚未加载，直接取房间配置
                let llm = roomConfig.value?.llm;
                if (!llm) {
                    try {
                        const res = await fetch(`/api/rooms/${selectedRoom.value.room_id}/config`, {credentials: 'include'});
                        if (res.ok) {
                            const data = await res.json();
                            if (data && !data.error) llm = data.llm;
                        }
                    } catch(e) { /* fallback to global */ }
                }
                // 编辑房间配置时确保 roomConfig 有 llm 字段
                if (llm && !roomConfig.value?.llm && roomConfig.value) {
                    roomConfig.value.llm = JSON.parse(JSON.stringify(llm));
                }
                if (llm) {
                    llmEnabled.value = llm.enabled ?? false;
                    llmProvider.value = llm.provider || 'openai';
                    llmBaseUrl.value = llm.base_url || '';
                    llmModel.value = llm.model || '';
                    llmWakeWord.value = llm.wake_word || 'ayabot';
                    llmTemp.value = llm.temperature ?? 0.7;
                    llmTopP.value = llm.top_p ?? 0.9;
                    llmMaxTokens.value = llm.max_tokens ?? 150;
                    llmPrompt.value = llm.system_prompt || '';
                    llmApiKeyReal.value = llm.api_key || '';
                    llmApiKey.value = llm.api_key ? '********' : '';
                    if (llm.context) {
                        ctxEnabled.value = llm.context.enabled ?? true;
                        ctxMode.value = llm.context.mode || 'isolated';
                        ctxContent.value = llm.context.content || 'llm_only';
                        ctxMaxMsg.value = llm.context.max_messages ?? 10;
                    }
                    return;
                }
            }
            try {
                const res = await fetch('/api/llm_config', {credentials: 'include'});
                if (res.status === 401) { loggedIn.value = false; return; }
                if (!res.ok) return;
                const data = await res.json();
                llmEnabled.value = data.enabled;
                llmProvider.value = data.provider;
                llmBaseUrl.value = data.base_url;
                llmModel.value = data.model;
                llmWakeWord.value = data.wake_word || 'ayabot';
                llmTemp.value = data.temperature ?? 0.7;
                llmTopP.value = data.top_p ?? 0.9;
                llmMaxTokens.value = data.max_tokens ?? 150;
                llmPrompt.value = data.system_prompt;
                llmApiKeyReal.value = data.api_key || '';
                if (data.has_api_key) {
                    llmApiKey.value = '********';
                }
                if (data.context) {
                    ctxEnabled.value = data.context.enabled;
                    ctxMode.value = data.context.mode;
                    ctxContent.value = data.context.content;
                    ctxMaxMsg.value = data.context.max_messages;
                }
            } catch(e) { /* ignore */ }
        }
        async function saveLlmConfig() {
            llmSaveMsg.value = '';
            const body = {
                enabled: llmEnabled.value,
                provider: llmProvider.value,
                base_url: llmBaseUrl.value,
                model: llmModel.value,
                wake_word: llmWakeWord.value,
                temperature: llmTemp.value,
                top_p: llmTopP.value,
                max_tokens: llmMaxTokens.value,
                system_prompt: llmPrompt.value,
                context: {
                    enabled: ctxEnabled.value,
                    mode: ctxMode.value,
                    content: ctxContent.value,
                    max_messages: ctxMaxMsg.value,
                },
            };
            if (llmApiKey.value && llmApiKey.value !== '********') {
                body.api_key = llmApiKey.value;
            }
            // 如果在房间内，同时保存到房间配置
            if (selectedRoom.value) {
                try {
                    const roomBody = JSON.parse(JSON.stringify(roomConfig.value || {}));
                    roomBody.llm = JSON.parse(JSON.stringify(body));
                    const res2 = await fetch(`/api/rooms/${selectedRoom.value.room_id}/config`, {
                        method: 'POST', headers: {'Content-Type':'application/json'},
                        credentials: 'include', body: JSON.stringify(roomBody),
                    });
                    if (res2.ok) {
                        // 更新内存中的 roomConfig
                        if (roomConfig.value) roomConfig.value.llm = JSON.parse(JSON.stringify(body));
                    }
                } catch(e) { /* room save best-effort */ }
            }
            try {
                const res = await fetch('/api/llm_config', {
                    method: 'POST',
                    headers: {'Content-Type':'application/json'},
                    credentials: 'include',
                    body: JSON.stringify(body),
                });
                if (res.status === 401) {
                    loggedIn.value = false;
                    llmSaveMsg.value = '会话已过期，请重新登录';
                    llmSaveOk.value = false;
                    return;
                }
                if (!res.ok) throw new Error((await res.text()).slice(0,80));
                const data = await res.json();
                if (data.ok) {
                    llmSaveMsg.value = '已保存';
                    llmSaveOk.value = true;
                    await loadLlmConfig();
                } else {
                    llmSaveMsg.value = data.error || '保存失败';
                    llmSaveOk.value = false;
                }
            } catch(e) {
                llmSaveMsg.value = '保存失败: ' + e.message;
                llmSaveOk.value = false;
            }
        }
        async function testLlm() {
            llmTestResp.value = '';
            if (!llmTestText.value) return;
            try {
                const res = await fetch('/api/llm_test', {
                    method: 'POST',
                    headers: {'Content-Type':'application/json'},
                    credentials: 'include',
                    body: JSON.stringify({text: llmTestText.value}),
                });
                if (res.status === 401) { loggedIn.value = false; return; }
                if (!res.ok) { llmTestResp.value = '测试失败'; return; }
                const data = await res.json();
                llmTestResp.value = data.reply || '(无回复)';
            } catch(e) {
                llmTestResp.value = '测试失败: ' + e.message;
            }
        }

        // 自动加载配置
        loadLlmConfig();
        loadGeneralConfig();
        loadRooms();
        loadAccounts();

        // ── 动态标题 ──
        document.title = 'Ayabot 直播间机器人';

        // ── General Config ──
        async function loadGeneralConfig() {
            try {
                const res = await fetch('/api/general_config', {credentials: 'include'});
                if (res.status === 401) { loggedIn.value = false; return; }
                if (!res.ok) return;
                const data = await res.json();
                if (data.error) return;
                cfgHost.value = data.web_ui?.host || '0.0.0.0';
                cfgPort.value = data.web_ui?.port || 19810;
                cfgRoomId.value = data.room_display_id || 0;
                cfgAnchorUid.value = data.anchor_uid || 0;
                cfgWelcomeCd.value = data.cooldown?.welcome_user_seconds ?? 600;
                cfgThanksCd.value = data.cooldown?.thanks_user_seconds ?? 10;
                cfgSendInterval.value = data.rate_limit?.send_interval_seconds ?? 1.2;
                cfgRetry.value = data.rate_limit?.retry_count ?? 2;
                cfgMaxQueue.value = data.rate_limit?.max_queue_size ?? 50;
                cfgReplyDelay.value = data.rate_limit?.reply_delay_seconds ?? 1.0;
                cfgWelcomeOn.value = data.features?.welcome_enabled ?? true;
                cfgThanksOn.value = data.features?.thanks_enabled ?? true;
                cfgBlindboxOn.value = data.features?.blindbox_enabled ?? true;
                cfgGuardOn.value = data.features?.guard_thanks_enabled ?? true;
                cfgConnectedMsg.value = data.features?.connected_message_enabled ?? false;
                cfgWelcomeTmpl.value = data.features?.welcome_template || '';
                cfgThanksTmpl.value = data.features?.thanks_template || '';
                cfgGuardCaptain.value = data.features?.guard_thanks_template_captain || '';
                cfgGuardCommander.value = data.features?.guard_thanks_template_commander || '';
                cfgGuardGovernor.value = data.features?.guard_thanks_template_governor || '';
                cfgGuardDefault.value = data.features?.guard_thanks_template_default || '';
                cfgConnMsg.value = data.features?.connected_message || '';
                cfgPeriodicOn.value = data.features?.periodic_message_enabled ?? true;
                cfgPeriodicInterval.value = data.features?.periodic_message_interval_seconds ?? 600;
                cfgPeriodicTmpl.value = data.features?.periodic_message_template || '';
            } catch(e) { /* ignore */ }
        }
        async function saveGeneralConfig() {
            cfgSaveMsg.value = '';
            try {
                const res = await fetch('/api/general_config', {
                    method: 'POST',
                    headers: {'Content-Type':'application/json'},
                    credentials: 'include',
                    body: JSON.stringify({
                        web_ui: {
                            host: cfgHost.value,
                            port: cfgPort.value,
                        },
                        cooldown: {
                            welcome_user_seconds: cfgWelcomeCd.value,
                            thanks_user_seconds: cfgThanksCd.value,
                        },
                        rate_limit: {
                            send_interval_seconds: cfgSendInterval.value,
                            retry_count: cfgRetry.value,
                            max_queue_size: cfgMaxQueue.value,
                            reply_delay_seconds: cfgReplyDelay.value,
                        },
                        features: {
                            welcome_enabled: cfgWelcomeOn.value,
                            welcome_template: cfgWelcomeTmpl.value,
                            thanks_enabled: cfgThanksOn.value,
                            thanks_template: cfgThanksTmpl.value,
                            blindbox_enabled: cfgBlindboxOn.value,
                            guard_thanks_enabled: cfgGuardOn.value,
                            guard_thanks_template_captain: cfgGuardCaptain.value,
                            guard_thanks_template_commander: cfgGuardCommander.value,
                            guard_thanks_template_governor: cfgGuardGovernor.value,
                            guard_thanks_template_default: cfgGuardDefault.value,
                            connected_message: cfgConnMsg.value,
                            connected_message_enabled: cfgConnectedMsg.value,
                            periodic_message_enabled: cfgPeriodicOn.value,
                            periodic_message_interval_seconds: cfgPeriodicInterval.value,
                            periodic_message_template: cfgPeriodicTmpl.value,
                        },
                    }),
                });
                if (res.status === 401) { loggedIn.value = false; return; }
                if (!res.ok) throw new Error((await res.text()).slice(0,80));
                const data = await res.json();
                if (data.ok) {
                    cfgSaveMsg.value = '已保存（重启后生效）';
                    cfgSaveOk.value = true;
                } else {
                    cfgSaveMsg.value = '保存失败';
                    cfgSaveOk.value = false;
                }
            } catch(e) {
                cfgSaveMsg.value = '保存失败: ' + e.message;
                cfgSaveOk.value = false;
            }
        }

        // ── Room Management ──
        async function loadRooms() {
            try {
                const res = await fetch('/api/rooms', {credentials: 'include'});
                if (res.status === 401) { loggedIn.value = false; return; }
                if (!res.ok) return;
                const data = await res.json();
                rooms.value = data.rooms || [];
                allRooms.value = data.rooms || [];
                // 同步当前打开的详情页（凭证状态/心跳/崩溃信息需要实时反映）
                if (selectedRoom.value) {
                    const fresh = (data.rooms || []).find(x => x.room_id === selectedRoom.value.room_id);
                    if (fresh) Object.assign(selectedRoom.value, fresh);
                }
            } catch(e) { /* ignore */ }
        }
        async function createRoom() {
            if (!newRoomUid.value) { createRoomMsg.value = '请填写主播 UID'; createRoomOk.value = false; return; }
            if (!newRoomDisplayId.value) { createRoomMsg.value = '请填写直播间号'; createRoomOk.value = false; return; }
            creatingRoom.value = true;
            createRoomMsg.value = '';
            try {
                const body = {
                    anchor_uid: newRoomUid.value,
                };
                if (newRoomName.value) {
                    body.room_name = newRoomName.value;
                } else if (newRoomAnchorName.value && !newRoomAnchorName.value.startsWith('(') && newRoomAnchorName.value !== '查询中...') {
                    body.room_name = newRoomAnchorName.value;
                }
                if (newRoomPort.value && newRoomPort.value !== 8001) body.port = newRoomPort.value;
                if (newRoomDisplayId.value) body.room_display_id = newRoomDisplayId.value;
                const res = await fetch('/api/rooms', {
                    method: 'POST',
                    headers: {'Content-Type':'application/json'},
                    credentials: 'include',
                    body: JSON.stringify(body),
                });
                if (res.status === 401) { loggedIn.value = false; return; }
                const data = await res.json();
                if (data.ok) {
                    createRoomMsg.value = `✅ 房间 ${data.room_id} 创建成功！`;
                    createRoomOk.value = true;
                    showCreateRoom.value = false;
                    // 关联 B站 账号
                    if (newRoomAccount.value) {
                        try {
                            await fetch(`/api/rooms/${data.room_id}/config`, {
                                method: 'POST',
                                headers: {'Content-Type':'application/json'},
                                credentials: 'include',
                                body: JSON.stringify({account_uid: newRoomAccount.value}),
                            });
                        } catch(e) { /* ignore */ }
                    }
                    // 应用预设模板
                    if (newRoomLlmTemplate.value || newRoomBotTemplate.value) {
                        const tplRes = await fetch('/api/templates', {credentials: 'include'});
                        const tplData = await tplRes.json();
                        const body = {};
                        if (newRoomLlmTemplate.value) {
                            const tpl = (tplData.llm_templates || []).find(t => t.name === newRoomLlmTemplate.value);
                            if (tpl) body.llm = tpl.config;
                        }
                        if (newRoomBotTemplate.value) {
                            const tpl = (tplData.bot_templates || []).find(t => t.name === newRoomBotTemplate.value);
                            if (tpl) body.features = tpl.config;
                        }
                        if (Object.keys(body).length) {
                            await fetch(`/api/rooms/${data.room_id}/config`, {
                                method: 'POST',
                                headers: {'Content-Type':'application/json'},
                                credentials: 'include',
                                body: JSON.stringify(body),
                            });
                        }
                    }
                    newRoomUid.value = 0;
                    newRoomName.value = '';
                    newRoomPort.value = 8001;
                    newRoomDisplayId.value = 0;
                    newRoomAccount.value = '';
                    newRoomLlmTemplate.value = '';
                    newRoomBotTemplate.value = '';
                    await loadRooms();
                } else {
                    createRoomMsg.value = '❌ ' + (data.error || '创建失败');
                    createRoomOk.value = false;
                }
            } catch(e) {
                createRoomMsg.value = '❌ 创建失败: ' + e.message;
                createRoomOk.value = false;
            } finally {
                creatingRoom.value = false;
            }
        }
        async function startRoom(roomId) {
            if (startingRooms.value.has(roomId)) return;
            if (!confirm(`确定启动房间 ${roomId}？`)) return;
            startingRooms.value = new Set([...startingRooms.value, roomId]);
            try {
                const res = await fetch(`/api/rooms/${roomId}/start`, {
                    method: 'POST', credentials: 'include',
                });
                if (!res.ok) throw new Error((await res.text()).slice(0,80));
                await loadRooms();
            } catch(e) { alert('启动失败: ' + e.message); }
            finally {
                const s = new Set(startingRooms.value);
                s.delete(roomId);
                startingRooms.value = s;
            }
        }
        async function stopRoom(roomId) {
            if (!confirm(`确定停止房间 ${roomId}？`)) return;
            try {
                const res = await fetch(`/api/rooms/${roomId}/stop`, {
                    method: 'POST', credentials: 'include',
                });
                if (!res.ok) throw new Error((await res.text()).slice(0,80));
                await loadRooms();
            } catch(e) { alert('停止失败: ' + e.message); }
        }
        async function deleteRoom(roomId, name) {
            if (!confirm(`⚠️ 确定删除房间「${name || roomId}」（${roomId}）？\n这将停止服务并删除所有数据！`)) return;
            try {
                const res = await fetch(`/api/rooms/${roomId}`, {
                    method: 'DELETE', credentials: 'include',
                });
                if (!res.ok) throw new Error((await res.text()).slice(0,80));
                editingRoom.value = null;
                roomConfig.value = null;
                await loadRooms();
            } catch(e) { alert('删除失败: ' + e.message); }
        }
        async function editRoomConfig(roomId) {
            editingRoom.value = roomId;
            roomConfig.value = null;
            roomSaveMsg.value = '';
            try {
                const res = await fetch(`/api/rooms/${roomId}/config`, {credentials: 'include'});
                if (res.status === 401) { loggedIn.value = false; return; }
                if (!res.ok) throw new Error((await res.text()).slice(0,80));
                const data = await res.json();
                if (data.error) throw new Error(data.error);
                roomConfig.value = data;
                // 确保 keyword_reply 存在（优先从 features 读取，兼容旧格式）
                const kr = data.keyword_reply || data.features?.keyword_reply;
                if (kr) {
                    roomConfig.value.keyword_reply = JSON.parse(JSON.stringify(kr));
                    roomConfig.value.keyword_reply.rules = (kr.rules || []).map(r => ({
                        ...r,
                        keywordsStr: (r.keywords || []).join(", "),
                        allowedUidsStr: (r.allowed_uids || []).join(", "),
                    }));
                } else {
                    roomConfig.value.keyword_reply = {enabled: false, cooldown: 30, rules: []};
                }
                if (!roomConfig.value.custom_fortunes) {
                    roomConfig.value.custom_fortunes = {daiji: "", zhongji: "", xiaoji: "", moji: "", xiong: "", daxiong: ""};
                }
                if (!roomConfig.value.features) roomConfig.value.features = {};
                // 转换 UID 欢迎模板 dict → entries 数组
                const wtfu = roomConfig.value.features.welcome_templates_for_uids || {};
                roomConfig.value.features.welcome_templates_for_uids_entries = Object.entries(wtfu).map(([uid, tmpl]) => ({uid: Number(uid), template: tmpl}));
                // 确保大航海欢迎模板存在
                if (!roomConfig.value.features.guard_welcome_templates) {
                    roomConfig.value.features.guard_welcome_templates = {captain: "", commander: "", governor: ""};
                }
            } catch(e) { alert('加载配置失败: ' + e.message); }
        }
        async function saveRoomConfig() {
            if (!roomConfig.value || !editingRoom.value) return;
            roomSaveMsg.value = '';
            const body = JSON.parse(JSON.stringify(roomConfig.value));
            if (body.keyword_reply && body.keyword_reply.rules) {
                body.keyword_reply.rules = body.keyword_reply.rules.map(r => ({
                    ...r,
                    keywords: r.keywordsStr ? r.keywordsStr.split(/[,，]\s*/).filter(Boolean) : [],
                    keywordsStr: undefined,
                    allowed_uids: r.allowedUidsStr ? r.allowedUidsStr.split(/[,，]\s*/).map(s => Number(s.trim())).filter(n => !isNaN(n)) : null,
                    allowedUidsStr: undefined,
                }));
            }
            // 转换 UID 欢迎 entries → dict
            if (body.features && body.features.welcome_templates_for_uids_entries) {
                const wtfu = {};
                for (const entry of body.features.welcome_templates_for_uids_entries) {
                    if (entry.uid && entry.template) wtfu[entry.uid] = entry.template;
                }
                body.features.welcome_templates_for_uids = Object.keys(wtfu).length ? wtfu : null;
                delete body.features.welcome_templates_for_uids_entries;
            }
            try {
                const res = await fetch(`/api/rooms/${editingRoom.value}/config`, {
                    method: 'POST',
                    headers: {'Content-Type':'application/json'},
                    credentials: 'include',
                    body: JSON.stringify(body),
                });
                if (res.status === 401) { loggedIn.value = false; return; }
                if (!res.ok) throw new Error((await res.text()).slice(0,80));
                const data = await res.json();
                if (data.ok) {
                    roomSaveMsg.value = '✅ 已保存';
                    roomSaveOk.value = true;
                    await loadRooms();
                } else {
                    roomSaveMsg.value = '❌ 保存失败';
                    roomSaveOk.value = false;
                }
            } catch(e) {
                roomSaveMsg.value = '❌ ' + e.message;
                roomSaveOk.value = false;
            }
        }

        // ── B站 扫码登录 ──
        async function startBiliLogin() {
            biliLoginState.value = 'loading';
            biliLoginError.value = '';
            if (biliPollTimer) { clearInterval(biliPollTimer); biliPollTimer = null; }
            try {
                const res = await fetch('/api/bili_login/start', {
                    method: 'POST', credentials: 'include',
                });
                if (!res.ok) throw new Error('请求失败');
                const data = await res.json();
                if (!data.ok) throw new Error(data.error || '生成二维码失败');
                biliQrImage.value = data.qr_image;
                biliSessionId.value = data.session_id;
                biliLoginState.value = 'waiting';
                // 开始轮询
                biliPollTimer = setInterval(pollBiliLogin, 2000);
            } catch(e) {
                biliLoginError.value = e.message;
                biliLoginState.value = 'error';
            }
        }
        async function pollBiliLogin() {
            if (!biliSessionId.value) return;
            try {
                const res = await fetch('/api/bili_login/status?session_id=' + biliSessionId.value, {
                    credentials: 'include',
                });
                if (!res.ok) return;
                const data = await res.json();
                if (data.state === 'done') {
                    biliLoginState.value = 'done';
                    if (biliPollTimer) { clearInterval(biliPollTimer); biliPollTimer = null; }
                } else if (data.state === 'scanned') {
                    biliLoginState.value = 'scanned';
                } else if (data.state === 'timeout') {
                    biliLoginState.value = 'timeout';
                    if (biliPollTimer) { clearInterval(biliPollTimer); biliPollTimer = null; }
                } else if (data.state === 'error') {
                    biliLoginError.value = data.message || '登录失败';
                    biliLoginState.value = 'error';
                    if (biliPollTimer) { clearInterval(biliPollTimer); biliPollTimer = null; }
                }
            } catch(e) { /* ignore */ }
        }
        async function saveBiliLogin() {
            biliLoginState.value = 'saving';
            try {
                const res = await fetch('/api/bili_login/save', {
                    method: 'POST',
                    credentials: 'include',
                    headers: {'Content-Type':'application/json'},
                    body: JSON.stringify({session_id: biliSessionId.value}),
                });
                if (!res.ok) throw new Error('保存失败');
                const data = await res.json();
                if (data.ok) {
                    // 服务正在重启，自动登出
                    setTimeout(() => { loggedIn.value = false; }, 2000);
                } else {
                    biliLoginError.value = data.error || '保存失败';
                    biliLoginState.value = 'error';
                }
            } catch(e) {
                biliLoginError.value = '保存失败: ' + e.message;
                biliLoginState.value = 'error';
            }
        }

        // ── Download helper ──
        async function downloadUrl(url, filename) {
            try {
                const res = await fetch(url, {credentials: 'include'});
                if (!res.ok) { const txt = await res.text(); throw new Error(txt.slice(0,80)); }
                const blob = await res.blob();
                const a = document.createElement('a');
                a.href = URL.createObjectURL(blob);
                a.download = filename;
                a.click();
                URL.revokeObjectURL(a.href);
            } catch(e) { alert('下载失败: ' + e.message); }
        }
        async function downloadJson(url, filename) {
            try {
                const res = await fetch(url, {credentials: 'include'});
                if (!res.ok) { const txt = await res.text(); throw new Error(txt.slice(0,80)); }
                const data = await res.json();
                const blob = new Blob([JSON.stringify(data, null, 2)], {type:'application/json'});
                const a = document.createElement('a');
                a.href = URL.createObjectURL(blob);
                a.download = filename;
                a.click();
                URL.revokeObjectURL(a.href);
            } catch(e) { alert('导出失败: ' + e.message); }
        }
        function importJsonFile(promptLabel, apiUrl, onSuccess) {
            const input = document.createElement('input');
            input.type = 'file';
            input.accept = '.json,application/json';
            input.onchange = async () => {
                const file = input.files[0];
                if (!file) return;
                try {
                    const text = await file.text();
                    const data = JSON.parse(text);
                    const res = await fetch(apiUrl, {
                        method: 'POST', headers: {'Content-Type':'application/json'},
                        credentials: 'include', body: JSON.stringify(data),
                    });
                    if (!res.ok) throw new Error((await res.text()).slice(0,80));
                    const ret = await res.json();
                    if (ret.ok === false) throw new Error(ret.error || '导入失败');
                    alert('✅ 导入成功');
                    if (onSuccess) onSuccess();
                } catch(e) { alert('❌ 导入失败: ' + e.message); }
            };
            input.click();
        }

        // ── Restart ──
        async function restartService() {
            restartMsg.value = '';
            restartOk.value = false;
            try {
                const res = await fetch('/api/restart', {
                    method: 'POST',
                    credentials: 'include',
                });
                if (res.status === 401) { loggedIn.value = false; return; }
                const data = await res.json();
                if (data.ok) {
                    restartMsg.value = '服务正在重启...';
                    restartOk.value = true;
                    // 重启后自动登出（web 也重启了）
                    setTimeout(() => { loggedIn.value = false; }, 2000);
                } else {
                    restartMsg.value = data.error || '重启失败';
                    restartOk.value = false;
                }
            } catch(e) {
                restartMsg.value = '重启失败: ' + e.message;
                restartOk.value = false;
            }
        }

        // ── Change Password ──
        function openChangePwd() {
            showUserMenu.value = false;
            showChangePwd.value = true;
            changePwdOld.value = '';
            changePwdNew.value = '';
            changePwdConfirm.value = '';
            changePwdNewUser.value = loginUser.value;
            changePwdMsg.value = '';
            changePwdOk.value = false;
            changingPwd.value = false;
        }
        async function doChangePwd() {
            // 从 DOM 读取（id 选择器最可靠）
            const oldPwd = (document.getElementById('inpOldPwd')?.value || '').trim();
            const newPwd = (document.getElementById('inpNewPwd')?.value || '').trim();
            const confirmPwd = (document.getElementById('inpCfmPwd')?.value || '').trim();
            if (!oldPwd || !newPwd) { changePwdMsg.value = '请填写当前密码和新密码'; changePwdOk.value = false; return; }
            if (newPwd.length < 4) { changePwdMsg.value = '密码至少4位'; changePwdOk.value = false; return; }
            if (newPwd !== confirmPwd) {
                changePwdMsg.value = '两次输入的密码不一致';
                changePwdOk.value = false;
                return;
            }
            if (!changePwdNewUser.value) { changePwdMsg.value = '请输入用户名'; changePwdOk.value = false; return; }
            changePwdMsg.value = '';
            changingPwd.value = true;
            try {
                const body = {old_password: oldPwd, new_password: newPwd};
                if (changePwdNewUser.value !== loginUser.value) {
                    body.new_username = changePwdNewUser.value;
                }
                const res = await fetch('/api/user/password', {
                    method: 'POST',
                    headers: {'Content-Type':'application/json'},
                    credentials: 'include',
                    body: JSON.stringify(body),
                });
                const data = await res.json();
                if (data.ok) {
                    changePwdMsg.value = '✅ 密码已修改';
                    changePwdOk.value = true;
                    if (data.new_username) {
                        loginUser.value = data.new_username;
                    }
                    if (mustResetPwd.value) {
                        mustResetPwd.value = false;
                        changePwdMsg.value = '✅ 密码已修改，即将进入管理后台...';
                        setTimeout(() => {
                            showChangePwd.value = false;
                            loadLlmConfig();
                            loadGeneralConfig();
                            loadRooms();
                            loadAccounts();
                            loadUsers();
                            loadTemplates();
                        }, 1000);
                    } else {
                        setTimeout(() => { showChangePwd.value = false; }, 1500);
                    }
                } else {
                    changePwdMsg.value = '❌ ' + (data.error || '修改失败');
                    changePwdOk.value = false;
                    changingPwd.value = false;
                }
            } catch(e) {
                changePwdMsg.value = '❌ ' + e.message;
                changePwdOk.value = false;
                changingPwd.value = false;
            }
        }

        // ── Admin User Management ──
        async function loadAdminUsers() {
            try {
                const res = await fetch('/api/admin/users', {credentials: 'include'});
                if (res.status === 401) { loggedIn.value = false; return; }
                if (!res.ok) return;
                const data = await res.json();
                const users = data.users || {};
                const list = [];
                for (const [uname, info] of Object.entries(users)) {
                    list.push({username: uname, ...info});
                }
                adminUsers.value = list;
            } catch(e) { /* ignore */ }
        }
        function openAddUser() {
            editingUser.value = null;
            userFormUsername.value = '';
            userFormPassword.value = '';
            userFormRole.value = 'user';
            userFormRooms.value = [];
            showUserForm.value = true;
            userFormMsg.value = '';
            showUserRoomDropdown.value = false;
        }
        function editUser(u) {
            editingUser.value = u;
            userFormUsername.value = u.username;
            userFormPassword.value = '';
            userFormRole.value = u.role || 'user';
            userFormRooms.value = [...(u.allowed_rooms || [])];
            showUserForm.value = true;
            userFormMsg.value = '';
            showUserRoomDropdown.value = false;
        }
        function toggleUserRoom(roomId) {
            const idx = userFormRooms.value.indexOf(roomId);
            if (idx >= 0) userFormRooms.value.splice(idx, 1);
            else userFormRooms.value.push(roomId);
        }
        async function saveUserForm() {
            if (!userFormUsername.value) { userFormMsg.value = '请填写用户名'; userFormOk.value = false; return; }
            if (!editingUser.value && !userFormPassword.value) { userFormMsg.value = '请填写密码'; userFormOk.value = false; return; }
            savingUserForm.value = true;
            userFormMsg.value = '';
            try {
                let res;
                if (editingUser.value) {
                    const body = {role: userFormRole.value, allowed_rooms: userFormRooms.value};
                    if (userFormPassword.value) body.password = userFormPassword.value;
                    res = await fetch(`/api/admin/users/${editingUser.value.username}`, {
                        method: 'PUT',
                        headers: {'Content-Type':'application/json'},
                        credentials: 'include',
                        body: JSON.stringify(body),
                    });
                } else {
                    res = await fetch('/api/admin/users', {
                        method: 'POST',
                        headers: {'Content-Type':'application/json'},
                        credentials: 'include',
                        body: JSON.stringify({
                            username: userFormUsername.value,
                            password: userFormPassword.value,
                            role: userFormRole.value,
                            allowed_rooms: userFormRooms.value,
                        }),
                    });
                }
                const data = await res.json();
                if (data.ok) {
                    userFormMsg.value = '✅ 保存成功';
                    userFormOk.value = true;
                    showUserForm.value = false;
                    editingUser.value = null;
                    await loadAdminUsers();
                } else {
                    userFormMsg.value = '❌ ' + (data.error || '保存失败');
                    userFormOk.value = false;
                }
            } catch(e) {
                userFormMsg.value = '❌ ' + e.message;
                userFormOk.value = false;
            } finally {
                savingUserForm.value = false;
            }
        }
        async function deleteUser(username) {
            if (!confirm(`确定删除用户「${username}」？`)) return;
            try {
                const res = await fetch(`/api/admin/users/${username}`, {
                    method: 'DELETE', credentials: 'include',
                });
                if (!res.ok) throw new Error((await res.text()).slice(0,80));
                await loadAdminUsers();
            } catch(e) { alert('删除失败: ' + e.message); }
        }

        // ── User Management (legacy, kept for backward compat) ──
        const streamers = ref([]);
        const allRooms = ref([]);
        const showStreamerForm = ref(null); // null | 'add' | 'edit'
        const editStreamerUser = ref('');
        const editStreamerPass = ref('');
        const editStreamerRooms = ref([]);
        const savingStreamer = ref(false);
        const streamerMsg = ref('');
        const streamerOk = ref(false);
        const showRoomDropdown = ref(false);
        const adminPass = ref('');
        const adminPassMsg = ref('');
        const adminPassOk = ref(false);
        async function loadUsers() {
            try {
                const res = await fetch('/api/users', {credentials: 'include'});
                if (!res.ok) return;
                const data = await res.json();
                const users = data.users || {};
                const list = [];
                for (const [uname, info] of Object.entries(users)) {
                    if (info.role === 'streamer' || info.role === 'user') {
                        list.push({username: uname, ...info, rooms: info.allowed_rooms || info.rooms || []});
                    }
                }
                streamers.value = list;
                // Also load admin users for the admin tab
                if (userRole.value === 'admin') {
                    loadAdminUsers();
                }
            } catch(e) { /* ignore */ }
        }
        function toggleStreamerRoom(roomId) {
            const idx = editStreamerRooms.value.indexOf(roomId);
            if (idx >= 0) editStreamerRooms.value.splice(idx, 1);
            else editStreamerRooms.value.push(roomId);
        }
        function editStreamer(s) {
            editStreamerUser.value = s.username;
            editStreamerPass.value = '';
            editStreamerRooms.value = [...(s.rooms || [])];
            showStreamerForm.value = 'edit';
        }
        async function saveStreamer() {
            if (!editStreamerUser.value) { streamerMsg.value = '请填写用户名'; streamerOk.value = false; return; }
            if (showStreamerForm.value === 'add' && !editStreamerPass.value) { streamerMsg.value = '请填写密码'; streamerOk.value = false; return; }
            savingStreamer.value = true;
            streamerMsg.value = '';
            try {
                const body = {
                    username: editStreamerUser.value,
                    role: 'streamer',
                    rooms: editStreamerRooms.value,
                };
                if (showStreamerForm.value === 'add' || editStreamerPass.value) {
                    body.password = editStreamerPass.value;
                }
                const res = await fetch('/api/users/update', {
                    method: 'POST', headers: {'Content-Type':'application/json'}, credentials: 'include',
                    body: JSON.stringify(body),
                });
                const data = await res.json();
                if (data.ok) {
                    streamerMsg.value = '✅ 保存成功';
                    streamerOk.value = true;
                    showStreamerForm.value = null;
                    editStreamerUser.value = ''; editStreamerPass.value = ''; editStreamerRooms.value = [];
                    await loadUsers();
                } else { streamerMsg.value = '❌ 保存失败'; streamerOk.value = false; }
            } catch(e) { streamerMsg.value = '❌ ' + e.message; streamerOk.value = false; }
            finally { savingStreamer.value = false; }
        }
        async function deleteStreamer(username) {
            if (!confirm(`确定删除主播账号「${username}」？`)) return;
            try {
                const res = await fetch(`/api/users/${username}`, {method: 'DELETE', credentials: 'include'});
                if (!res.ok) throw new Error('删除失败');
                await loadUsers();
            } catch(e) { alert(e.message); }
        }
        async function saveAdminPass() {
            if (!adminPass.value || adminPass.value.length < 4) { adminPassMsg.value = '密码至少4位'; adminPassOk.value = false; return; }
            adminPassMsg.value = '';
            try {
                const res = await fetch('/api/users/admin_password', {
                    method: 'POST', headers: {'Content-Type':'application/json'}, credentials: 'include',
                    body: JSON.stringify({password: adminPass.value}),
                });
                const data = await res.json();
                if (data.ok) {
                    adminPassMsg.value = '✅ 密码已更新';
                    adminPassOk.value = true;
                    adminPass.value = '';
                } else { adminPassMsg.value = '❌ 保存失败'; adminPassOk.value = false; }
            } catch(e) { adminPassMsg.value = '❌ ' + e.message; adminPassOk.value = false; }
        }

        function addKeywordRule() {
            if (!roomConfig.value.keyword_reply.rules) roomConfig.value.keyword_reply.rules = [];
            roomConfig.value.keyword_reply.rules.push({keywords: [], keywordsStr: "", reply: "", match_mode: "contains", allowedUidsStr: ""});
        }
        function removeKeywordRule(idx) {
            roomConfig.value.keyword_reply.rules.splice(idx, 1);
        }
        // ── UID欢迎模板弹窗 ──
        const showUidWelcomeModal = ref(false);
        const uidWelcomeEditEntries = ref([]);
        function openUidWelcomeModal() {
            const raw = roomConfig.value.features.welcome_templates_for_uids_entries || [];
            uidWelcomeEditEntries.value = raw.map(e => {
                const entry = JSON.parse(JSON.stringify(e));
                entry.allDay = (entry.time_start === 0 && entry.time_end === 23);
                return entry;
            });
            showUidWelcomeModal.value = true;
        }
        function closeUidWelcomeModal() {
            showUidWelcomeModal.value = false;
            uidWelcomeEditEntries.value = [];
        }
        function saveUidWelcomeModal() {
            roomConfig.value.features.welcome_templates_for_uids_entries =
                JSON.parse(JSON.stringify(uidWelcomeEditEntries.value.map(e => ({
                    uid: e.uid, template: e.template,
                    time_start: e.time_start || 0, time_end: e.time_end || 23,
                }))));
            closeUidWelcomeModal();
        }
        function addUidWelcomeTemplate() {
            if (!roomConfig.value.features.welcome_templates_for_uids_entries) roomConfig.value.features.welcome_templates_for_uids_entries = [];
            roomConfig.value.features.welcome_templates_for_uids_entries.push({uid: 0, template: ""});
        }
        function removeUidWelcomeTemplate(idx) {
            roomConfig.value.features.welcome_templates_for_uids_entries.splice(idx, 1);
        }
        // ── 关键词回复弹窗 ──
        const showKeywordModal = ref(false);
        const keywordEditRules = ref([]);
        function openKeywordModal() {
            keywordEditRules.value = JSON.parse(JSON.stringify((roomConfig.value.keyword_reply.rules || []).map(r => ({
                ...r,
                keywordsStr: r.keywordsStr || (r.keywords || []).join(", "),
                allowedUidsStr: r.allowedUidsStr || (r.allowed_uids || []).join(", "),
                time_start: r.time_start || 0,
                time_end: r.time_end || 23,
                allDay: (r.time_start === 0 && r.time_end === 23),
            }))));
            showKeywordModal.value = true;
        }
        function closeKeywordModal() {
            showKeywordModal.value = false;
            keywordEditRules.value = [];
        }
        function saveKeywordModal() {
            roomConfig.value.keyword_reply.rules = JSON.parse(JSON.stringify(keywordEditRules.value.map(r => ({
                ...r,
                time_start: r.time_start || 0,
                time_end: r.time_end || 23,
            }))));
            closeKeywordModal();
        }

        // ── 荣耀等级欢迎多模板弹窗 ──
        const showHonorWelcomeTplModal = ref(false);
        const honorWelcomeTplEntries = ref([]);
        function openHonorWelcomeTplModal() {
            honorWelcomeTplEntries.value = JSON.parse(JSON.stringify(roomConfig.value.features.honor_welcome_templates_list || []));
            honorWelcomeTplEntries.value.forEach(e => { if (e.time_start === 0 && e.time_end === 23) e.allDay = true; else e.allDay = false; });
            showHonorWelcomeTplModal.value = true;
        }
        function saveHonorWelcomeTplModal() {
            const valid = honorWelcomeTplEntries.value.filter(e => e.text && e.text.trim());
            roomConfig.value.features.honor_welcome_templates_list = valid.length ? valid.map(e => ({text: e.text, time_start: e.time_start || 0, time_end: e.time_end || 23})) : null;
            showHonorWelcomeTplModal.value = false;
        }

        // ── UID 黑名单弹窗 ──
        const showUidBlacklistModal = ref(false);
        const uidBlacklistEdit = ref([]);
        function openUidBlacklistModal() {
            uidBlacklistEdit.value = JSON.parse(JSON.stringify(roomConfig.value.features.uid_blacklist || []));
            uidBlacklistEdit.value.forEach(e => { if (e.time_start === 0 && e.time_end === 23) e.allDay = true; else e.allDay = false; });
            showUidBlacklistModal.value = true;
        }
        function closeUidBlacklistModal() {
            showUidBlacklistModal.value = false;
            uidBlacklistEdit.value = [];
        }
        function saveUidBlacklistModal() {
            const valid = uidBlacklistEdit.value.filter(e => e.uid && e.uid > 0);
            roomConfig.value.features.uid_blacklist = valid.length ? JSON.parse(JSON.stringify(valid.map(e => ({uid: e.uid, time_start: e.time_start || 0, time_end: e.time_end || 23})))) : null;
            closeUidBlacklistModal();
        }

        // ── 关键词屏蔽弹窗 ──
        const showKeywordFilterModal = ref(false);
        const keywordFilterEdit = ref([]);
        function openKeywordFilterModal() {
            keywordFilterEdit.value = JSON.parse(JSON.stringify(roomConfig.value.features.keyword_filter || []));
            keywordFilterEdit.value.forEach(e => { if (e.time_start === 0 && e.time_end === 23) e.allDay = true; else e.allDay = false; });
            showKeywordFilterModal.value = true;
        }
        function closeKeywordFilterModal() {
            showKeywordFilterModal.value = false;
            keywordFilterEdit.value = [];
        }
        function saveKeywordFilterModal() {
            const valid = keywordFilterEdit.value.filter(e => e.keyword && e.keyword.trim());
            roomConfig.value.features.keyword_filter = valid.length ? JSON.parse(JSON.stringify(valid.map(e => ({keyword: e.keyword.trim(), match_mode: e.match_mode, action: e.action, time_start: e.time_start || 0, time_end: e.time_end || 23})))) : null;
            closeKeywordFilterModal();
        }

        // ── 欢迎多模板弹窗 ──
        const showWelcomeTplModal = ref(false);
        const welcomeTplEntries = ref([]);
        function openWelcomeTplModal() {
            welcomeTplEntries.value = JSON.parse(JSON.stringify(roomConfig.value.features.welcome_templates_list || []));
            // 补齐 allDay 字段
            welcomeTplEntries.value.forEach(e => { if (e.time_start === 0 && e.time_end === 23) e.allDay = true; else e.allDay = false; });
            showWelcomeTplModal.value = true;
        }
        function saveWelcomeTplModal() {
            const valid = welcomeTplEntries.value.filter(e => e.text && e.text.trim());
            roomConfig.value.features.welcome_templates_list = valid.length ? valid.map(e => ({text: e.text, time_start: e.time_start || 0, time_end: e.time_end || 23})) : null;
            showWelcomeTplModal.value = false;
        }
        // ── 大航海欢迎多模板弹窗 ──
        const showGuardWelcomeTplModal = ref(false);
        const guardWelcomeTplEntries = ref({captain: [], commander: [], governor: []});
        function openGuardWelcomeTplModal() {
            const src = roomConfig.value.features.guard_welcome_templates_list || {};
            function load(lk) {
                const arr = JSON.parse(JSON.stringify(src[lk] || []));
                arr.forEach(e => { if (e.time_start === 0 && e.time_end === 23) e.allDay = true; else e.allDay = false; });
                return arr;
            }
            guardWelcomeTplEntries.value = {
                captain: load('captain'),
                commander: load('commander'),
                governor: load('governor'),
            };
            showGuardWelcomeTplModal.value = true;
        }
        function saveGuardWelcomeTplModal() {
            function save(lk) {
                return (guardWelcomeTplEntries.value[lk] || []).filter(e => e.text && e.text.trim()).map(e => ({text: e.text, time_start: e.time_start || 0, time_end: e.time_end || 23}));
            }
            const out = {};
            for (const lk of ['captain', 'commander', 'governor']) {
                const valid = save(lk);
                if (valid.length) out[lk] = valid;
            }
            roomConfig.value.features.guard_welcome_templates_list = Object.keys(out).length ? out : null;
            showGuardWelcomeTplModal.value = false;
        }
        function addGuardTpl(level) {
            if (!guardWelcomeTplEntries.value[level]) guardWelcomeTplEntries.value[level] = [];
            guardWelcomeTplEntries.value[level].push({text: '', time_start: 0, time_end: 23, allDay: true});
        }
        // ── 定时消息多模板弹窗 ──
        const showPeriodicTplModal = ref(false);
        const periodicTplEntries = ref([]);
        function openPeriodicTplModal() {
            periodicTplEntries.value = JSON.parse(JSON.stringify(roomConfig.value.features.periodic_messages_list || []));
            periodicTplEntries.value.forEach(e => { if (e.time_start === 0 && e.time_end === 23) e.allDay = true; else e.allDay = false; });
            showPeriodicTplModal.value = true;
        }
        function savePeriodicTplModal() {
            const valid = periodicTplEntries.value.filter(e => e.text && e.text.trim());
            roomConfig.value.features.periodic_messages_list = valid.length ? valid.map(e => ({text: e.text, time_start: e.time_start || 0, time_end: e.time_end || 23})) : null;
            showPeriodicTplModal.value = false;
        }
        // ── 签文多文本弹窗 ──
        const showFortuneTplModal = ref(false);
        const fortuneTypes = [
            {key: 'daiji', label: '大吉', placeholder: '今天运气爆棚！'},
            {key: 'zhongji', label: '中吉', placeholder: '运势不错~'},
            {key: 'xiaoji', label: '小吉', placeholder: '平稳的一天~'},
            {key: 'moji', label: '末吉', placeholder: '平淡是福~'},
            {key: 'xiong', label: '凶', placeholder: '今天低调行事~'},
            {key: 'daxiong', label: '大凶', placeholder: '吃顿好的安慰自己~'},
        ];
        const fortuneTplEntries = ref({daiji: [], zhongji: [], xiaoji: [], moji: [], xiong: [], daxiong: []});
        function openFortuneTplModal() {
            const src = roomConfig.value.custom_fortunes || {};
            const out = {};
            for (const ft of fortuneTypes) {
                const val = src[ft.key];
                if (Array.isArray(val)) {
                    out[ft.key] = JSON.parse(JSON.stringify(val));
                } else if (typeof val === 'string' && val) {
                    out[ft.key] = [val];
                } else {
                    out[ft.key] = [];
                }
            }
            fortuneTplEntries.value = out;
            showFortuneTplModal.value = true;
        }
        function saveFortuneTplModal() {
            const out = {};
            for (const ft of fortuneTypes) {
                const arr = (fortuneTplEntries.value[ft.key] || []).filter(t => t && t.trim());
                if (arr.length) {
                    out[ft.key] = arr;
                }
            }
            roomConfig.value.custom_fortunes = Object.keys(out).length ? out : {};
            showFortuneTplModal.value = false;
        }
        function addFortuneText(key) {
            if (!fortuneTplEntries.value[key]) fortuneTplEntries.value[key] = [];
            fortuneTplEntries.value[key].push('');
        }
        // ── 计算属性: 统计条数 ──
        const guardWelcomeTotal = computed(() => {
            const gwl = roomConfig.value.features.guard_welcome_templates_list || {};
            return (gwl.captain||[]).length + (gwl.commander||[]).length + (gwl.governor||[]).length;
        });
        const fortuneTotalEntries = computed(() => {
            const cf = roomConfig.value.custom_fortunes || {};
            return Object.values(cf).reduce((sum, arr) => sum + (Array.isArray(arr) ? arr.length : (arr ? 1 : 0)), 0);
        });

        // ── 预设模板管理 ──
        async function loadTemplates() {
            try {
                const res = await fetch('/api/templates', {credentials: 'include'});
                if (res.status === 401) { loggedIn.value = false; return; }
                if (!res.ok) return;
                const data = await res.json();
                llmTemplates.value = data.llm_templates || [];
                botTemplates.value = data.bot_templates || [];
            } catch(e) { /* ignore */ }
        }
        async function saveTemplate() {
            if (!templateFormName.value) { templateFormMsg.value = '请输入模板名称'; templateFormOk.value = false; return; }
            if (!templateFormImportRoom.value) { templateFormMsg.value = '请选择要导入的房间'; templateFormOk.value = false; return; }
            const ttype = showAddTemplate.value;
            if (!ttype) return;
            savingTemplate.value = true;
            templateFormMsg.value = '';
            try {
                // 从房间导入配置
                const configRes = await fetch(`/api/rooms/${templateFormImportRoom.value}/config`, {credentials: 'include'});
                if (!configRes.ok) {
                    const errText = await configRes.text().catch(() => '');
                    throw new Error('读取房间配置失败: ' + (errText || configRes.status));
                }
                const roomCfg = await configRes.json();
                let config = {};
                if (ttype === 'llm') {
                    // AI 配置是全局的（存于 _LLM_CONFIG_DICT），使用当前表单值
                    config = {
                        enabled: llmEnabled.value,
                        provider: llmProvider.value,
                        base_url: llmBaseUrl.value,
                        model: llmModel.value,
                        wake_word: llmWakeWord.value,
                        temperature: llmTemp.value,
                        top_p: llmTopP.value,
                        max_tokens: llmMaxTokens.value,
                        system_prompt: llmPrompt.value,
                        context: {
                            enabled: ctxEnabled.value,
                            mode: ctxMode.value,
                            content: ctxContent.value,
                            max_messages: ctxMaxMsg.value,
                        },
                    };
                    // API key：表单里如果是掩码则用真实值
                    if (llmApiKey.value && llmApiKey.value !== '********') {
                        config.api_key = llmApiKey.value;
                    } else if (llmApiKeyReal.value) {
                        config.api_key = llmApiKeyReal.value;
                    }
                } else {
                    config = roomCfg.features || {};
                }
                const res = await fetch('/api/templates', {
                    method: 'POST',
                    headers: {'Content-Type':'application/json'},
                    credentials: 'include',
                    body: JSON.stringify({type: ttype, name: templateFormName.value, config}),
                });
                if (!res.ok) throw new Error('保存失败');
                templateFormMsg.value = '✅ 模板已保存';
                templateFormOk.value = true;
                showAddTemplate.value = null;
                templateFormName.value = '';
                templateFormImportRoom.value = '';
                await loadTemplates();
            } catch(e) {
                templateFormMsg.value = '❌ ' + e.message;
                templateFormOk.value = false;
            } finally { savingTemplate.value = false; }
        }
        async function deleteTemplate(ttype, name) {
            try {
                await fetch('/api/templates', {
                    method: 'DELETE',
                    headers: {'Content-Type':'application/json'},
                    credentials: 'include',
                    body: JSON.stringify({type: ttype, name}),
                });
                await loadTemplates();
            } catch(e) { /* ignore */ }
        }
        async function restartAllBots() {
            restartingAll.value = true;
            restartAllMsg.value = '';
            try {
                const res = await fetch('/api/restart_all_bots', {method: 'POST', credentials: 'include'});
                const data = await res.json();
                if (data.ok) {
                    restartAllMsg.value = `✅ 已触发 ${data.count} 个机器人重启`;
                    restartAllOk.value = true;
                } else {
                    restartAllMsg.value = '❌ 重启失败';
                    restartAllOk.value = false;
                }
            } catch(e) {
                restartAllMsg.value = '❌ ' + e.message;
                restartAllOk.value = false;
            } finally { restartingAll.value = false; }
        }
        async function restartSingleBot(roomId) {
            try {
                await fetch(`/api/rooms/${roomId}/restart`, {method: 'POST', credentials: 'include'});
                roomSaveMsg.value = '✅ 已触发重启';
                roomSaveOk.value = true;
                setTimeout(() => { roomSaveMsg.value = ''; }, 3000);
            } catch(e) { /* ignore */ }
        }
        // ── 套用模板 ──
        async function applyTemplateToLlm() {
            const tpl = llmTemplates.value.find(t => t.name === applyLlmTemplate.value);
            if (!tpl) return;
            const c = tpl.config;
            llmEnabled.value = c.enabled ?? false;
            llmProvider.value = c.provider || 'openai';
            if (c.api_key) llmApiKey.value = c.api_key;
            llmBaseUrl.value = c.base_url || '';
            llmModel.value = c.model || '';
            llmWakeWord.value = c.wake_word || 'ayabot';
            llmTemp.value = c.temperature ?? 0.7;
            llmTopP.value = c.top_p ?? 0.9;
            llmMaxTokens.value = c.max_tokens ?? 150;
            llmPrompt.value = c.system_prompt || '';
            if (c.context) {
                ctxEnabled.value = c.context.enabled ?? true;
                ctxMode.value = c.context.mode || 'isolated';
                ctxContent.value = c.context.content || 'llm_only';
                ctxMaxMsg.value = c.context.max_messages ?? 10;
            }
            applyLlmTemplate.value = '';
            llmSaveMsg.value = '✅ 已套用模板，请点击保存生效';
            llmSaveOk.value = true;
        }
        async function applyTemplateToBot() {
            const tpl = botTemplates.value.find(t => t.name === applyBotTemplate.value);
            if (!tpl || !roomConfig.value) return;
            const c = tpl.config;
            // 套用到 roomConfig（注意先转成 entries 格式）
            for (const key of Object.keys(c)) {
                if (key === 'welcome_templates_for_uids') {
                    roomConfig.value.features.welcome_templates_for_uids_entries = Object.entries(c[key] || {}).map(([uid, tmpl]) => ({uid: Number(uid), template: tmpl}));
                } else {
                    roomConfig.value.features[key] = c[key];
                }
            }
            applyBotTemplate.value = '';
            applyTemplateMsg.value = '✅ 已套用模板，请点击保存';
            applyTemplateOk.value = true;
            setTimeout(() => { applyTemplateMsg.value = ''; }, 5000);
        }

        return {showUpdateModal, updateChecking, updateError, updateData, checkUpdate, viewChangelog, showChangelog, changelogContent, renderMarkdown,
                updateNotice, openUpdateNotice, ignoreUpdate, silentCheckUpdate,
                loggedIn, loginUser, loginPass, loginErr, doLogin, doLogout,
                isDark, toggleTheme,
                tab, userRole,
                showUserMenu, showChangePwd, changePwdOld, changePwdNew, changePwdNewUser, changePwdMsg, changePwdOk, changingPwd,
                mustResetPwd,
                openChangePwd, doChangePwd,
                adminUsers, showUserForm, editingUser, userFormUsername, userFormPassword,
                userFormRole, userFormRooms, showUserRoomDropdown, savingUserForm, userFormMsg, userFormOk,
                openAddUser, editUser, saveUserForm, deleteUser, toggleUserRoom,
                rStart, rEnd, rType, ranking, errRanking, loadRanking,
                guardItems, guardTotals, loadGuards, fmtGuardTime,
                eUid, eName, eDate, eType, ePerCol, eColWidth, exportList, exportDates, exportCols, errExport, loadingExport,
                loadExport, gotoExport, loadUserDates, onUidInput, onModeChange,
                toggleDate, selectAllDatesInRange, clearSelectedDates, applyMultiDateExport,
                pickDate, captureExport, eModeAll, eSelectedDates, eSelectedSet,
                eMergeGifts, eMergeUser, eShowPrice, exporting, startingRooms, fmtDateTime,
                showCalendar, calYear, calMonth, calDays, exportDatesSet, calPos, toggleCalendar,
                proxyImg, fmtTime, cardBgClass, guardLabel, guardBadgeClass,
                delDate, delResult, confirmDelete,
                roomApiEnabled, roomApiUrl, roomApiFullKey, roomApiBusy,
                apiMsg, apiMsgOk, loadRoomApiConfig, toggleRoomApi, regenerateRoomApiKey, copyText,
                danmakuRows, danmakuErr, danmakuOffset, danmakuLimit, danmakuTotal, danmakuPage,
                loadDanmakuLog, clearDanmakuLog, fmtDanmakuTime, loadDmDates, dmToggleDate, dmToggleCal, dmSelectAllMonth, dmClearDates, dmCalOk, dmCalPos, dmExportSelected, dmCalDays, dmCalYear, dmCalMonth, dmShowCal, dmSelectedDates, dmDates, dmDatesSet, dmAsc,
                dmKeyword, dmSearchActive, dmSearch, clearDmSearch, highlightDanmaku,
                dmGap, dmShowRec, dmGapOptions, fmtRelTime, restartSessions,
                dmUsers, dmUserFilter, dmUidFilter, dmUserBusy, dmStats, dmShowStats,
                dmSessions, dmSessionIdx, dmSessionLabel, dmSessionChanged, loadDanmakuSessions, dmSessionTs,
                dmShowSessionPanel, dmSessionQuery, dmSessionFiltered, dmSessCurLabel,
                dmToggleSessionPanel, dmPickSession,
                loadDanmakuUsers, loadDanmakuStats, clearDmFilters, barPct,
                llmEnabled, llmProvider, llmApiKey, llmBaseUrl, llmModel, llmPrompt,
                showMsTip, msPicked, applyModelScope,
                llmWakeWord, llmTemp, llmTopP, llmMaxTokens,
                llmSaveMsg, llmSaveOk, llmTestText, llmTestResp,
                ctxEnabled, ctxMode, ctxContent, ctxMaxMsg,
                saveLlmConfig, testLlm, loadLlmConfig,
                cfgRoomId, cfgAnchorUid, cfgWelcomeCd, cfgThanksCd,
                cfgSendInterval, cfgRetry, cfgMaxQueue, cfgReplyDelay,
                cfgWelcomeOn, cfgThanksOn, cfgBlindboxOn, cfgGuardOn, cfgConnectedMsg,
                cfgWelcomeTmpl, cfgThanksTmpl, cfgGuardCaptain, cfgGuardCommander, cfgGuardGovernor, cfgGuardDefault, cfgConnMsg,
                cfgPeriodicOn, cfgPeriodicInterval, cfgPeriodicTmpl,
                cfgHost, cfgPort,
                cfgSaveMsg, cfgSaveOk, loadGeneralConfig,
                restartMsg, restartOk, restartService,
                selectedRoom, roomSubTab, roomSubTabs, newRoomAccount, selectedRoomAccount,
                selectRoom, goBackRoomList, assignAccountToRoom, toggleCreateRoom, toggleNewAccount, goRelogin, downloadUrl, downloadJson, importJsonFile, exportRoomConfig, importRoomConfig, afterImportLlm,
                selectRoomSubTab, accountAssignMsg, accountAssignOk, accountRestarting, assignAccountAndRestart,
                onSortChange,
                startEditRoomName, saveRoomName, editingRoomName, roomNameEdit,
                rooms, showCreateRoom, newRoomUid, newRoomName, newRoomAnchorName, newRoomPort, newRoomDisplayId,
                creatingRoom, createRoomMsg, createRoomOk, createRoom,
                startRoom, stopRoom, deleteRoom, editRoomConfig, saveRoomConfig, editingRoom, roomConfig,
                roomSaveMsg, roomSaveOk,
                accounts, showNewAccount, newAccountUid, accountLoggingIn, accountQrImage,
                accountQrState, accountQrError, startAccountLogin, refreshAccount, deleteAccount,
                loadAccounts, loadRooms, refreshQrCode,
                editingNickname, startEditNickname, saveNickname, verifyAccount,
                verifyQueue, verifyingAll, verifyAllAccounts,
                streamers, allRooms, showStreamerForm, editStreamerUser, editStreamerPass,
                editStreamerRooms, savingStreamer, streamerMsg, streamerOk,
                loadUsers, saveStreamer, editStreamer, deleteStreamer, toggleStreamerRoom, showRoomDropdown,
                addUidWelcomeTemplate, removeUidWelcomeTemplate,
                loadBotLog, clearBotLog, botLogContent, logLevel, logContainer,
                showUidWelcomeModal, uidWelcomeEditEntries, openUidWelcomeModal, closeUidWelcomeModal, saveUidWelcomeModal,
                showKeywordModal, keywordEditRules, openKeywordModal, closeKeywordModal, saveKeywordModal,
                showWelcomeTplModal, welcomeTplEntries, openWelcomeTplModal, saveWelcomeTplModal,
                showGuardWelcomeTplModal, guardWelcomeTplEntries, openGuardWelcomeTplModal, saveGuardWelcomeTplModal, addGuardTpl,
                showHonorWelcomeTplModal, honorWelcomeTplEntries, openHonorWelcomeTplModal, saveHonorWelcomeTplModal,
                showUidBlacklistModal, uidBlacklistEdit, openUidBlacklistModal, closeUidBlacklistModal, saveUidBlacklistModal,
                showKeywordFilterModal, keywordFilterEdit, openKeywordFilterModal, closeKeywordFilterModal, saveKeywordFilterModal,
                showPeriodicTplModal, periodicTplEntries, openPeriodicTplModal, savePeriodicTplModal,
                showFortuneTplModal, fortuneTypes, fortuneTplEntries, openFortuneTplModal, saveFortuneTplModal, addFortuneText,
                guardWelcomeTotal, fortuneTotalEntries,
                llmTemplates, botTemplates, showAddTemplate, templateFormName, templateFormImportRoom,
                savingTemplate, templateFormMsg, templateFormOk, newRoomLlmTemplate, newRoomBotTemplate,
                restartingAll, restartAllMsg, restartAllOk,
                loadTemplates, saveTemplate, deleteTemplate, restartAllBots, restartSingleBot,
                applyLlmTemplate, applyBotTemplate, applyTemplateMsg, applyTemplateOk,
                applyTemplateToLlm, applyTemplateToBot,
                configSections, toggleSection};
    }
}).mount('#app');
</script>
</body>
</html>
"""

# 注入版本号（从 VERSION 文件读取，一处修改全局同步）
INDEX_HTML = INDEX_HTML.replace("__AYABOT_VERSION__", _APP_VERSION)


@app.get("/", response_class=HTMLResponse)
async def index():
    return INDEX_HTML


@app.get("/favicon.ico")
async def favicon():
    """站点图标 = 软件图标（figs/favicon.ico，随 exe 一起打包）。"""
    for name, media in (("favicon.ico", "image/x-icon"), ("icon-web.png", "image/png"),
                        ("icon.png", "image/png")):
        path = _figs_path(name)
        if path is not None and path.exists():
            return FastResponse(content=path.read_bytes(), media_type=media,
                                headers={"Cache-Control": "public, max-age=86400"})
    return Response(status_code=204)


@app.get("/icon-192.png")
async def web_icon_192():
    """导航栏 / iOS 添加到主屏用的图标。"""
    for name in ("icon-web.png", "icon.png"):
        path = _figs_path(name)
        if path is not None and path.exists():
            return FastResponse(content=path.read_bytes(), media_type="image/png",
                                headers={"Cache-Control": "public, max-age=86400"})
    return Response(status_code=204)


# ── 打赏二维码 ──


def _figs_path(name: str) -> Path:
    """在 PyInstaller 冻结模式和正常模式下查找 figs/ 目录下的文件。"""
    if getattr(sys, 'frozen', False) and hasattr(sys, '_MEIPASS'):
        p = Path(sys._MEIPASS) / "figs" / name
        if p.exists():
            return p
    p = Path(__file__).resolve().parent.parent.parent / "figs" / name
    return p


@app.get("/figs/alipay.jpg")
async def alipay_qr():
    p = _figs_path("alipay.jpg")
    if p.exists():
        return FastResponse(content=p.read_bytes(), media_type="image/jpeg")
    return Response(status_code=404)


@app.get("/figs/wechat.png")
async def wechat_qr():
    p = _figs_path("wechat.png")
    if p.exists():
        return FastResponse(content=p.read_bytes(), media_type="image/png")
    return Response(status_code=404)


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO)
    uvicorn.run(app, host="0.0.0.0", port=8000)
