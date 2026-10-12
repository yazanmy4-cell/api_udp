import asyncio
import os
import time
import json
from typing import Dict, Any, Optional, Callable
from aiohttp import web

BR_PHASE_SECONDS = 15 * 60
COOLDOWN_SECONDS = 3 * 60
MAX_MATCHES_PER_ACCOUNT = 200
MAX_EXP_TARGET = 50000


class BotState:
    def __init__(self):
        self.accounts: Dict[str, Dict[str, Any]] = {}
        self.account_workers: Dict[str, asyncio.Task] = {}
        self.account_credentials: Dict[str, Dict] = {}
        self.refresh_callbacks: Dict[str, Callable] = {}
        self.logs: list = []
        self._loop: Optional[asyncio.AbstractEventLoop] = None
        self.exp_targets_ref: Dict[str, int] = {}
        self.start_exp_ref: Dict[str, int] = {}
        self.exp_limit_reached_ref: set = set()
        self.account_start_ref: Dict[str, float] = {}
        self.session_matches_ref: Dict[str, int] = {}
        self.generated_accounts: list = []
        self.max_exp_target: int = MAX_EXP_TARGET
        self.auto_cycle_tasks: Dict[str, asyncio.Task] = {}
        self.auto_cycle_phase: Dict[str, str] = {}

    def bind_loop(self):
        self._loop = asyncio.get_running_loop()

    def register_account(self, uid, nickname, region, level, exp, likes=0):
        uid = str(uid)
        existing = self.accounts.get(uid, {})
        self.accounts[uid] = {
            "uid": uid,
            "nickname": nickname or existing.get("nickname") or f"Player_{uid}",
            "region": region or existing.get("region") or "ME",
            "level": int(level) if level else existing.get("level", 1),
            "exp": int(exp) if exp else existing.get("exp", 0),
            "likes": int(likes) if likes else existing.get("likes", 0),
            "status": existing.get("status", "CONNECTING"),
            "active_matches": existing.get("active_matches", 0),
            "matches_played": existing.get("matches_played", 0),
            "phase": existing.get("phase", "IDLE"),
        }

    def update_status(self, uid, status, active_matches=None):
        uid = str(uid)
        if uid in self.accounts:
            self.accounts[uid]["status"] = status
            if active_matches is not None:
                self.accounts[uid]["active_matches"] = int(active_matches)

    def update_exp(self, uid, exp, level=None):
        uid = str(uid)
        if uid in self.accounts:
            self.accounts[uid]["exp"] = int(exp)
            if level is not None:
                self.accounts[uid]["level"] = int(level)

    def increment_match(self, uid):
        uid = str(uid)
        if uid in self.accounts:
            self.accounts[uid]["active_matches"] = self.accounts[uid].get("active_matches", 0) + 1
            self.accounts[uid]["matches_played"] = self.accounts[uid].get("matches_played", 0) + 1

    def log(self, message, level="info"):
        self.logs.append({"t": time.time(), "level": level, "msg": str(message)})
        self.logs = self.logs[-500:]


bot_state = BotState()


async def api_status(request: web.Request):
    out = []
    now = time.time()
    for uid, acc in bot_state.accounts.items():
        creds = bot_state.account_credentials.get(uid, {}) or {}
        worker = bot_state.account_workers.get(uid)
        running = bool(worker and not worker.done())
        started_at = float(bot_state.account_start_ref.get(uid, 0) or 0)
        elapsed = int(max(0, now - started_at)) if started_at else 0
        target = int(bot_state.exp_targets_ref.get(uid, 0) or 0)
        exp = int(acc.get("exp", 0))
        start_exp = int(bot_state.start_exp_ref.get(uid, exp))
        gain = max(0, exp - start_exp)
        eta = 0
        rate = 0
        if elapsed > 5 and gain > 0 and target > gain:
            rate_sec = gain / elapsed
            rate = int(rate_sec * 3600)
            eta = int((target - gain) / rate_sec) if rate_sec else 0
        out.append({
            "uid": uid,
            "nickname": acc.get("nickname", f"Player_{uid}"),
            "region": acc.get("region", "ME"),
            "level": int(acc.get("level", 1)),
            "exp": exp,
            "exp_start": start_exp,
            "exp_gain": gain,
            "target": target,
            "remaining": max(0, target - gain) if target else 0,
            "likes": int(acc.get("likes", 0)),
            "status": acc.get("status", "OFFLINE"),
            "phase": bot_state.auto_cycle_phase.get(uid, "IDLE"),
            "matches_played": int(acc.get("matches_played", 0)),
            "session_matches": int(bot_state.session_matches_ref.get(uid, 0)),
            "running": running,
            "elapsed_seconds": elapsed,
            "rate_per_hour": rate,
            "eta_seconds": eta,
            "auth_type": creds.get("auth_type", ""),
        })
    return web.json_response({"ok": True, "count": len(out), "server_time": now, "accounts": out})


async def api_start(request: web.Request):
    data = await request.json()
    uid_in = str(data.get("uid", "")).strip()
    password_in = str(data.get("password", "")).strip()
    token = str(data.get("token", "")).strip()
    if not token and not (uid_in and password_in):
        return web.json_response({"ok": False, "error": "Provide token OR uid+password"}, status=400)
    try:
        target = int(data.get("target", MAX_EXP_TARGET))
    except Exception:
        target = MAX_EXP_TARGET
    target = max(1, min(MAX_EXP_TARGET, target))
    payload = {"type": "token", "token": token} if token else {"type": "guest", "uid": uid_in, "password": password_in}
    login_handler = bot_state.refresh_callbacks.get("on_account_login_only")
    if not login_handler:
        return web.json_response({"ok": False, "error": "Backend not ready"}, status=500)
    try:
        await login_handler(payload)
    except Exception as e:
        return web.json_response({"ok": False, "error": f"Login failed: {e}"}, status=500)
    uid = None
    deadline = time.time() + 90
    while time.time() < deadline:
        for k, creds in list(bot_state.account_credentials.items()):
            if token and creds.get("auth_type") == "token" and creds.get("auth_token") == token:
                uid = str(creds.get("account_id"))
                break
            if uid_in and creds.get("auth_type") == "guest" and str(creds.get("auth_uid")) == uid_in:
                uid = str(creds.get("account_id"))
                break
        if uid and uid in bot_state.accounts:
            break
        await asyncio.sleep(0.5)
    if not uid:
        return web.json_response({"ok": False, "error": "Login timeout"}, status=502)
    setter = bot_state.refresh_callbacks.get("on_set_target")
    if setter:
        await setter(uid, target)
    starter = bot_state.refresh_callbacks.get("on_start_account")
    if starter:
        await starter(uid)
    return web.json_response({"ok": True, "uid": uid, "target": target})


async def api_stop(request: web.Request):
    data = await request.json()
    uid = str(data.get("uid", "")).strip()
    if not uid:
        return web.json_response({"ok": False, "error": "Missing uid"}, status=400)
    t = bot_state.auto_cycle_tasks.pop(uid, None)
    if t and not t.done():
        t.cancel()
    handler = bot_state.refresh_callbacks.get("on_stop_account")
    if handler:
        try:
            await handler(uid)
        except Exception as e:
            return web.json_response({"ok": False, "error": str(e)}, status=500)
    return web.json_response({"ok": True, "uid": uid})


async def api_delete(request: web.Request):
    data = await request.json()
    uid = str(data.get("uid", "")).strip()
    if not uid:
        return web.json_response({"ok": False, "error": "Missing uid"}, status=400)
    t = bot_state.auto_cycle_tasks.pop(uid, None)
    if t and not t.done():
        t.cancel()
    handler = bot_state.refresh_callbacks.get("on_delete_account")
    if handler:
        try:
            await handler(uid)
        except Exception as e:
            return web.json_response({"ok": False, "error": str(e)}, status=500)
    return web.json_response({"ok": True, "uid": uid})


async def api_lvl_cycle(request: web.Request):
    accounts_list = []
    target = MAX_EXP_TARGET
    if request.method == "GET":
        accs_param = request.query.get("accounts", "").strip()
        if accs_param:
            for pair in accs_param.split(","):
                pair = pair.strip()
                if not pair:
                    continue
                if ":" in pair:
                    u, p = pair.split(":", 1)
                    accounts_list.append((u.strip(), p.strip()))
        try:
            target = int(request.query.get("target", MAX_EXP_TARGET))
        except Exception:
            target = MAX_EXP_TARGET
    else:
        try:
            data = await request.json()
        except Exception:
            data = {}
        for item in data.get("accounts", []):
            u = str(item.get("uid", "")).strip()
            p = str(item.get("password", "")).strip()
            if u and p:
                accounts_list.append((u, p))
        try:
            target = int(data.get("target", MAX_EXP_TARGET))
        except Exception:
            target = MAX_EXP_TARGET
    if not accounts_list:
        return web.json_response({"ok": False, "error": "No accounts provided"}, status=400)
    target = max(1, min(MAX_EXP_TARGET, target))
    started = []
    for u, p in accounts_list:
        task = asyncio.create_task(_auto_cycle_one(u, p, target))
        bot_state.auto_cycle_tasks[u] = task
        started.append(u)
    return web.json_response({
        "ok": True,
        "accounts_queued": started,
        "target": target,
        "cycle": {
            "br_phase_seconds": BR_PHASE_SECONDS,
            "cooldown_seconds": COOLDOWN_SECONDS,
            "max_matches_per_account": MAX_MATCHES_PER_ACCOUNT
        }
    })


async def _auto_cycle_one(auth_uid: str, auth_pass: str, target: int):
    login_handler = bot_state.refresh_callbacks.get("on_account_login_only")
    starter = bot_state.refresh_callbacks.get("on_start_account")
    stopper = bot_state.refresh_callbacks.get("on_stop_account")
    setter = bot_state.refresh_callbacks.get("on_set_target")
    refresher = bot_state.refresh_callbacks.get("on_refresh_profile")
    round_num = 0
    while True:
        round_num += 1
        try:
            await login_handler({"type": "guest", "uid": auth_uid, "password": auth_pass})
        except Exception as e:
            bot_state.log(f"[CYCLE] login fail {auth_uid}: {e}")
            await asyncio.sleep(30)
            continue
        real_uid = None
        deadline = time.time() + 60
        while time.time() < deadline:
            for k, creds in list(bot_state.account_credentials.items()):
                if creds.get("auth_type") == "guest" and str(creds.get("auth_uid")) == auth_uid:
                    real_uid = str(creds.get("account_id"))
                    break
            if real_uid:
                break
            await asyncio.sleep(0.5)
        if not real_uid:
            bot_state.log(f"[CYCLE] no real_uid for {auth_uid}")
            await asyncio.sleep(20)
            continue
        bot_state.auto_cycle_phase[real_uid] = "BR"
        if setter:
            try:
                await setter(real_uid, target)
            except Exception:
                pass
        if starter:
            try:
                await starter(real_uid)
            except Exception as e:
                bot_state.log(f"[CYCLE] start fail {real_uid}: {e}")
                await asyncio.sleep(10)
                continue
        bot_state.log(f"[CYCLE] {real_uid} round {round_num} - BR phase")
        await asyncio.sleep(BR_PHASE_SECONDS)
        if stopper:
            try:
                await stopper(real_uid)
            except Exception:
                pass
        bot_state.auto_cycle_phase[real_uid] = "COOLDOWN"
        bot_state.log(f"[CYCLE] {real_uid} cooldown")
        await asyncio.sleep(COOLDOWN_SECONDS)
        try:
            creds = bot_state.account_credentials.get(real_uid)
            if creds and refresher:
                await refresher(creds)
        except Exception:
            pass
        try:
            await login_handler({"type": "guest", "uid": auth_uid, "password": auth_pass})
        except Exception as e:
            bot_state.log(f"[CYCLE] re-login fail {real_uid}: {e}")
            await asyncio.sleep(30)
            continue
        new_uid = None
        deadline = time.time() + 60
        while time.time() < deadline:
            for k, creds in list(bot_state.account_credentials.items()):
                if creds.get("auth_type") == "guest" and str(creds.get("auth_uid")) == auth_uid:
                    new_uid = str(creds.get("account_id"))
                    break
            if new_uid:
                break
            await asyncio.sleep(0.5)
        if not new_uid:
            bot_state.log(f"[CYCLE] re-login timeout {auth_uid}")
            await asyncio.sleep(20)
            continue
        real_uid = new_uid
        bot_state.auto_cycle_phase[real_uid] = "LW"
        if setter:
            try:
                await setter(real_uid, target)
            except Exception:
                pass
        try:
            creds = bot_state.account_credentials.get(real_uid)
            if creds:
                creds["force_lw"] = True
                if not creds.get("level") or int(creds.get("level", 1)) < 3:
                    creds["level"] = 3
                if real_uid in bot_state.accounts:
                    bot_state.accounts[real_uid]["level"] = 3
        except Exception:
            pass
        if starter:
            try:
                await starter(real_uid)
            except Exception as e:
                bot_state.log(f"[CYCLE] LW start fail {real_uid}: {e}")
        bot_state.log(f"[CYCLE] {real_uid} round {round_num} - LW phase")
        while True:
            await asyncio.sleep(30)
            acc = bot_state.accounts.get(real_uid)
            if not acc:
                break
            played = int(acc.get("matches_played", 0))
            if played >= MAX_MATCHES_PER_ACCOUNT:
                bot_state.log(f"[CYCLE] {real_uid} reached {played} matches")
                break
            w = bot_state.account_workers.get(real_uid)
            if not w or w.done():
                bot_state.log(f"[CYCLE] {real_uid} worker stopped")
                break
        if stopper:
            try:
                await stopper(real_uid)
            except Exception:
                pass
        bot_state.auto_cycle_phase[real_uid] = "RESTART"
        await asyncio.sleep(5)


async def api_logs(request: web.Request):
    return web.json_response({"ok": True, "logs": bot_state.logs[-200:]})


async def api_health(request: web.Request):
    return web.json_response({
        "ok": True,
        "service": "yazan-level-api",
        "accounts": len(bot_state.accounts),
        "workers": sum(1 for t in bot_state.account_workers.values() if t and not t.done()),
        "cycles": sum(1 for t in bot_state.auto_cycle_tasks.values() if t and not t.done()),
        "time": time.time()
    })


async def root(request: web.Request):
    return web.json_response({
        "service": "YAZAN LEVEL API",
        "endpoints": {
            "GET /status": "all accounts",
            "POST /start": "{uid,password,target}",
            "POST /stop": "{uid}",
            "POST /delete": "{uid}",
            "POST /lvl": "{accounts:[{uid,password}],target}",
            "GET /lvl": "?accounts=uid1:pass1,uid2:pass2&target=50000",
            "GET /logs": "last 200 logs",
            "GET /health": "health"
        }
    })


async def start_api_server(host="0.0.0.0", port=8080):
    app = web.Application()
    app.router.add_get("/", root)
    app.router.add_get("/status", api_status)
    app.router.add_post("/start", api_start)
    app.router.add_post("/stop", api_stop)
    app.router.add_post("/delete", api_delete)
    app.router.add_post("/lvl", api_lvl_cycle)
    app.router.add_get("/lvl", api_lvl_cycle)
    app.router.add_get("/logs", api_logs)
    app.router.add_get("/health", api_health)
    runner = web.AppRunner(app)
    await runner.setup()
    site = web.TCPSite(runner, host, port)
    await site.start()
    print(f"YAZAN LEVEL API on http://{host}:{port}")
    return runner