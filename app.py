import sys
import os
os.environ['PYTHONUNBUFFERED'] = '1'
os.environ.setdefault('PROTOCOL_BUFFERS_PYTHON_IMPLEMENTATION', 'python')
try:
    sys.stdout.reconfigure(line_buffering=True)
    sys.stderr.reconfigure(line_buffering=True)
except Exception:
    pass

if sys.platform == "win32":
    try:
        if hasattr(sys.stdout, 'reconfigure'):
            sys.stdout.reconfigure(encoding='utf-8', errors='replace')
        if hasattr(sys.stderr, 'reconfigure'):
            sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except Exception:
        pass

import asyncio
import httpx
import random
import json
import socket
import struct
import time
import uuid
import itertools
import math
import string as _string
from datetime import datetime
from typing import Dict, List, Optional, Tuple, Any

from google_play_scraper import app as play_scraper
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad
from protobuf_decoder.protobuf_decoder import Parser
from message_ids import MESSAGE_ID_TO_NAME
import thunderFF_pb2

try:
    from ReqAddBoT import send_friend_request_async
    _HAS_ADDFRIEND = True
except Exception:
    _HAS_ADDFRIEND = False
    send_friend_request_async = None

try:
    import gen as _gen_module
    _HAS_GEN = True
except Exception:
    _HAS_GEN = False
    _gen_module = None

from api_server import bot_state, start_api_server

WEB_PORT = int(os.getenv("WEB_PORT", os.getenv("PORT", "8080")))
START_MATCH_INTERVAL = 3.0
NEW_MATCH_DELAY = 3.0
MAX_MATCH_DURATION = 800
MATCH_IDLE_TIMEOUT = 8.0
MAX_CONCURRENT_MATCHES = 1
MODE_SWITCH_LEVEL = 3
PRIORITY_REGIONS = ["BD", "IND", "SG", "TH", "PH", "VN", "MY", "ID", "HK", "TW"]

LW_START_INTERVAL = 3.0
LW_NEW_MATCH_DELAY = 3.0
LW_MAX_MATCH_DURATION = 700
LW_MATCH_IDLE_TIMEOUT = 8.0
LW_RECONNECT_DELAY = 1.0
LW_MAX_PARSE_FAILS = 5.0
LW_TOKEN_TTL = 1200

MIN_UID_LENGTH = 8

INFO_API = "http://de26.spaceify.eu:26080/info?uid="
INFO_TIMEOUT = 10.0


def _pb_varint(n):
    if n < 0:
        n = (1 << 64) + n
    out = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        if n:
            b |= 0x80
        out.append(b)
        if not n:
            break
    return bytes(out)


def _pb_tag(f, w):
    return _pb_varint((f << 3) | w)


def _pb_field(f, v):
    if isinstance(v, bool):
        v = int(v)
    if isinstance(v, int):
        return _pb_tag(f, 0) + _pb_varint(v)
    if isinstance(v, str):
        d = v.encode('utf-8')
        return _pb_tag(f, 2) + _pb_varint(len(d)) + d
    if isinstance(v, (bytes, bytearray)):
        d = bytes(v)
        return _pb_tag(f, 2) + _pb_varint(len(d)) + d
    return b""


def is_valid_account_id(acc_id) -> bool:
    try:
        s = str(acc_id).strip()
        if not s or s == "0":
            return False
        if not s.isdigit():
            return False
        if len(s) < MIN_UID_LENGTH:
            return False
        if int(s) == 0:
            return False
        return True
    except Exception:
        return False


def _generate_new_device() -> dict:
    device_list = [
        ("samsung", "sm-g998b", "adreno (tm) 660", "android os 12 / api-31"),
        ("xiaomi", "2201122g", "adreno (tm) 730", "android os 13 / api-33"),
        ("realme", "rmx3700", "mali-g710", "android os 14 / api-34"),
        ("oneplus", "cph2451", "adreno (tm) 740", "android os 13 / api-33"),
        ("oppo", "cph2611", "adreno (tm) 720", "android os 14 / api-34"),
        ("vivo", "v2203", "mali-g710", "android os 12 / api-31"),
        ("poco", "m2102j20sg", "adreno (tm) 660", "android os 13 / api-33"),
    ]
    brand, model, gpu, os_ver = random.choice(device_list)
    return {
        "unique_device_id": f"google|{str(uuid.uuid4())}",
        "brand": brand,
        "model": model,
        "gpu_renderer": gpu,
        "system_software": os_ver,
        "screen_width": random.choice([1080, 1440, 720, 1280]),
        "screen_height": random.choice([2400, 3200, 1600, 2400]),
        "screen_dpi": str(random.randint(300, 420)),
        "memory": random.randint(2800, 6500),
        "processor_details": f"arm64 fp asimd aes vmh | {random.randint(2200, 3200)} | {random.randint(6, 12)}",
        "client_ip": f"{random.randint(103, 223)}.{random.randint(10, 250)}.{random.randint(10, 250)}.{random.randint(10, 250)}"
    }


def get_device_for_account(account_identifier: str) -> dict:
    return _generate_new_device()


CLOUDFLARE_PRIMARY_DNS = "1.1.1.1"
CLOUDFLARE_SECONDARY_DNS = "1.0.0.1"
_DNS_CACHE: Dict[str, Tuple[str, float]] = {}
_DNS_CACHE_TTL = 300.0


async def resolve_host_cloudflare(hostname: str) -> str:
    if not hostname:
        return hostname
    parts = hostname.split('.')
    if len(parts) == 4 and all(p.isdigit() and 0 <= int(p) <= 255 for p in parts):
        return hostname

    now = time.time()
    if hostname in _DNS_CACHE:
        ip, exp = _DNS_CACHE[hostname]
        if now < exp:
            return ip

    def _query_cloudflare(server_ip: str) -> Optional[str]:
        s = None
        try:
            tx_id = random.randint(1000, 65535)
            header = struct.pack(">hhhhhh", tx_id, 0x0100, 1, 0, 0, 0)
            qname = b"".join(bytes([len(part)]) + part.encode('ascii') for part in hostname.split('.')) + b"\x00"
            query_pkt = header + qname + struct.pack(">hh", 1, 1)
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            s.settimeout(1.2)
            s.sendto(query_pkt, (server_ip, 53))
            resp, _ = s.recvfrom(1024)
            if len(resp) >= 12:
                ancount = struct.unpack(">h", resp[6:8])[0]
                if ancount > 0:
                    offset = 12 + len(qname) + 4
                    for _ in range(ancount):
                        if offset >= len(resp):
                            break
                        if (resp[offset] & 0xc0) == 0xc0:
                            offset += 2
                        else:
                            while offset < len(resp) and resp[offset] != 0:
                                offset += 1 + resp[offset]
                            offset += 1
                        if offset + 10 > len(resp):
                            break
                        rtype, rclass, ttl, rdlen = struct.unpack(">hhih", resp[offset:offset+10])
                        offset += 10
                        if rtype == 1 and rdlen == 4 and offset + 4 <= len(resp):
                            return socket.inet_ntoa(resp[offset:offset+4])
                        offset += rdlen
        except Exception:
            pass
        finally:
            if s:
                try:
                    s.close()
                except Exception:
                    pass
        return None

    loop = asyncio.get_running_loop()
    ip = await loop.run_in_executor(None, _query_cloudflare, CLOUDFLARE_PRIMARY_DNS)
    if not ip:
        ip = await loop.run_in_executor(None, _query_cloudflare, CLOUDFLARE_SECONDARY_DNS)
    if not ip:
        try:
            ip_info = await loop.getaddrinfo(hostname, None, family=socket.AF_INET)
            if ip_info:
                ip = ip_info[0][4][0]
        except Exception:
            ip = hostname

    if ip:
        _DNS_CACHE[hostname] = (ip, now + _DNS_CACHE_TTL)
    return ip or hostname


def optimize_tcp_socket(sock: socket.socket):
    try:
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)
        if hasattr(socket, "sio_keepalive_vals") and os.name == 'nt':
            try:
                sock.ioctl(socket.sio_keepalive_vals, (1, 10000, 2000))
            except Exception:
                pass
        elif hasattr(socket, "tcp_keepidle"):
            try:
                sock.setsockopt(socket.IPPROTO_TCP, socket.tcp_keepidle, 10)
                if hasattr(socket, "tcp_keepintvl"):
                    sock.setsockopt(socket.IPPROTO_TCP, socket.tcp_keepintvl, 2)
                if hasattr(socket, "tcp_keepcnt"):
                    sock.setsockopt(socket.IPPROTO_TCP, socket.tcp_keepcnt, 5)
            except Exception:
                pass
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 131072)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, 131072)
    except Exception:
        pass


async def safe_close_writer(writer):
    if not writer:
        return
    try:
        if not writer.is_closing():
            writer.close()
        await asyncio.wait_for(writer.wait_closed(), timeout=1.5)
    except Exception:
        pass


def optimize_udp_socket(sock: socket.socket):
    try:
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 131072)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, 131072)
        if hasattr(socket, 'sio_udp_connreset') and os.name == 'nt':
            try:
                sock.ioctl(socket.sio_udp_connreset, False)
            except Exception:
                pass
    except Exception:
        pass


client = httpx.AsyncClient(
    verify=False,
    timeout=15.0,
    limits=httpx.Limits(max_connections=300, max_keepalive_connections=150)
)
_LOGIN_SEMAPHORE = asyncio.Semaphore(4)

headers = {
    'user-agent': 'unityplayer/2018.4.12f1 (unitywebrequest/1.0, libcurl/8.5.0-dev)',
    'connection': 'keep-alive',
    'accept-encoding': 'gzip',
    'content-type': 'application/x-www-form-urlencoded',
    'expect': '100-continue',
    'x-unity-version': '2018.4.12f1',
    'x-ga-sv': '1789535859',
    'x-ga': 'v1 1',
    'releaseversion': 'ob55'
}

AES_KEY = b'Yg&tc%DEuh6%Zc^8'
AES_IV = b'6oyZDr22E3ychjM%'

CRC7_TABLE = bytes([
    0, 9, 18, 27, 36, 45, 54, 63, 72, 65, 90, 83, 108, 101, 126, 119,
    25, 16, 11, 2, 61, 52, 47, 38, 81, 88, 67, 74, 117, 124, 103, 110,
    50, 59, 32, 41, 22, 31, 4, 13, 122, 115, 104, 97, 94, 87, 76, 69,
    43, 34, 57, 48, 15, 6, 29, 20, 99, 106, 113, 120, 71, 78, 85, 92,
    100, 109, 118, 127, 64, 73, 82, 91, 44, 37, 62, 55, 8, 1, 26, 19,
    125, 116, 111, 102, 89, 80, 75, 66, 53, 60, 39, 46, 17, 24, 3, 10,
    86, 95, 68, 77, 114, 123, 96, 105, 30, 23, 12, 5, 58, 51, 40, 33,
    79, 70, 93, 84, 107, 98, 121, 112, 7, 14, 21, 28, 35, 42, 49, 56,
    65, 72, 83, 90, 101, 108, 119, 126, 9, 0, 27, 18, 45, 36, 63, 54,
    88, 81, 74, 67, 124, 117, 110, 103, 16, 25, 2, 11, 52, 61, 38, 47,
    115, 122, 97, 104, 87, 94, 69, 76, 59, 50, 41, 32, 31, 22, 13, 4,
    106, 99, 120, 113, 78, 71, 92, 85, 34, 43, 48, 57, 6, 15, 20, 29,
    37, 44, 55, 62, 1, 8, 19, 26, 109, 100, 127, 118, 73, 64, 91, 82,
    60, 53, 46, 39, 24, 17, 10, 3, 116, 125, 102, 111, 80, 89, 66, 75,
    23, 30, 5, 12, 51, 58, 33, 40, 95, 86, 77, 68, 123, 114, 105, 96,
    14, 7, 28, 21, 42, 35, 56, 49, 70, 79, 84, 93, 98, 107, 112, 121,
])

_DELTA = 0x9E3779B9
_ROUNDS = 16
_FIELD_SIZES = {0: 1, 1: 2, 2: 2, 3: 1, 4: 2}
_FIELD_NAMES = {0: "sendoption", 1: "cmd", 2: "orderid", 3: "flags", 4: "length"}


def log(msg):
    print(msg, flush=True)
    try:
        bot_state.log(msg)
    except Exception:
        pass


def get_proto_field(d, key, default=None):
    if not d or not isinstance(d, dict):
        return default
    if key in d:
        val = d[key].get('data')
        return val if val is not None else default
    if str(key) in d:
        val = d[str(key)].get('data')
        return val if val is not None else default
    return default


_match_counters: Dict[str, int] = {}
_match_counter_lock = asyncio.Lock()


async def _inc_match(uid: str) -> int:
    async with _match_counter_lock:
        _match_counters[uid] = _match_counters.get(uid, 0) + 1
        return _match_counters[uid]


async def _dec_match(uid: str) -> int:
    async with _match_counter_lock:
        if uid in _match_counters and _match_counters[uid] > 0:
            _match_counters[uid] -= 1
        return _match_counters.get(uid, 0)


async def _get_match_count(uid: str) -> int:
    async with _match_counter_lock:
        return _match_counters.get(uid, 0)


async def aes_encrypt(payload, key, iv):
    cipher = AES.new(key, AES.MODE_CBC, iv)
    return cipher.encrypt(pad(payload, AES.block_size))


async def get_playstore_version():
    loop = asyncio.get_event_loop()
    try:
        result = await loop.run_in_executor(
            None,
            lambda: play_scraper('com.dts.freefireth', lang='hi', country='id')
        )
        return result.get("version")
    except Exception:
        return "1.132.8"


async def version_config():
    app_version = await get_playstore_version()
    api_url = (
        "https://version.ggwhitehawk.com/live/ver.php"
        f"?version={app_version}"
        "&lang=hi&device=android&channel=android"
        "&appstore=googleplay&region=me"
        "&whitelist_version=1.3.0&whitelist_sp_version=1.0.0"
    )
    try:
        response = await client.get(api_url)
        response.raise_for_status()
        data = response.json()
        server_url = data.get("server_url")
        remote_version = data.get("remote_version")
        latest_release_version = data.get("latest_release_version")
        if not server_url or not remote_version or not latest_release_version:
            return None
        return latest_release_version, remote_version, server_url
    except Exception:
        return None


async def fetch_external_info(uid: str) -> Optional[Dict]:
    try:
        url = f"{INFO_API}{uid}"
        r = await client.get(url, timeout=INFO_TIMEOUT)
        if r.status_code == 200:
            return r.json()
    except Exception as e:
        log(f"[-] info api error for {uid}: {e}")
    return None


async def get_access_token(uid, password):
    url = "https://100067.connect.garena.com/oauth/guest/token/grant"
    hdrs = {
        "host": "100067.connect.garena.com",
        "user-agent": "dalvik/2.1.0 (linux; u; android 12; sm-g998b build/sp1a.210812.016)",
        "content-type": "application/x-www-form-urlencoded",
        "accept-encoding": "gzip, deflate, br",
        "connection": "close"
    }
    data = {
        "uid": uid,
        "password": password,
        "response_type": "token",
        "client_type": "2",
        "client_secret": "2ee44819e9b4598845141067b281621874d0d5d7af9d8f7e00c1e54715b7d1e3",
        "client_id": "100067"
    }
    for attempt in range(5):
        try:
            response = await client.post(url, headers=hdrs, data=data)
            if response.status_code == 200:
                response_data = response.json()
                open_id = response_data.get("open_id")
                access_token = response_data.get("access_token")
                platform = response_data.get("platform", 4)
                if open_id and access_token:
                    return open_id, access_token, platform
            if response.status_code == 429:
                await asyncio.sleep(1)
                continue
        except Exception:
            pass
        await asyncio.sleep(0.5)
    return None


async def parse_results(parsed_results):
    result_dict = {}
    for result in parsed_results:
        field_data = {"wire_type": result.wire_type}
        if result.wire_type == "varint":
            field_data["data"] = result.data
        elif result.wire_type == "string":
            field_data["data"] = result.data
        elif result.wire_type == "bytes":
            field_data["data"] = result.data
        elif result.wire_type == "length_delimited":
            if hasattr(result.data, "results"):
                field_data["data"] = await parse_results(result.data.results)
            elif isinstance(result.data, list):
                field_data["data"] = await parse_results(result.data)
            else:
                field_data["data"] = str(result.data)
        result_dict[str(result.field)] = field_data
    return result_dict


async def decode_protobuf(data):
    parsed_results = Parser().parse(data)
    parsed_results_dict = await parse_results(parsed_results)
    return json.dumps(parsed_results_dict)


async def build_majorlogin_payload(open_id, access_token, platform, client_version, device_info, verr=None):
    try:
        if verr is None:
            verr = client_version

        proto = thunderFF_pb2.MajorLoginReq()
        proto.event_time = str(datetime.now())[:-7]
        proto.game_name = "free fire"
        proto.platform_id = 1
        proto.client_version = str(verr)
        proto.client_version_code = "2019121229"
        proto.system_software = "android os 15 / api-35 (ap3a.240905.015.a2/185014)"
        proto.system_hardware = "handheld"
        proto.device_type = "handheld"
        proto.screen_width = 1600
        proto.screen_height = 719
        proto.screen_dpi = "234"
        proto.processor_details = "arm64 fp asimd aes | 1820 | 8"
        proto.memory = 2798
        proto.gpu_renderer = "mali-g57"
        proto.gpu_version = "opengl es 3.2 v1.r49p1-04eac0.2848c17a2fd4e9340e06555168eaa3c9"
        proto.unique_device_id = "google|f744e396-5694-4e65-995d-97a958f2bd1f"
        proto.client_ip = "197.0.137.129"
        proto.language = "pt-br"
        proto.open_id = str(open_id)
        proto.open_id_type = "4"
        proto.login_open_id_type = 4
        proto.access_token = str(access_token)
        proto.login_by = 2
        proto.platform_sdk_id = 1
        proto.origin_platform_type = "4"
        proto.primary_platform_type = "4"
        proto.reg_avatar = 1
        proto.channel_type = 3
        proto.telecom_operator = "tuntel"
        proto.network_operator_a = "tuntel"
        proto.network_type = "wifi"
        proto.network_type_a = "wifi"
        proto.cpu_type = 2
        proto.cpu_architecture = "64"
        proto.graphics_api = "opengles2"
        proto.supported_astc_bitset = 8191
        proto.client_using_version = "7428b253defc164018c604a1ebbfebdf"
        proto.loading_time = 15078
        proto.release_channel = "android"
        proto.extra_info = "kqshtx3+qombrr1wkvawewlcpqjbfjki+pphqoqg8+0yv+uos7guffjhmq/e7u6han6fl77r7c3vmn3p8ubkgn+nfycqcgwbmwgbzomx2gj84c+p"
        proto.android_engine_init_flag = 111207
        proto.if_push = 1
        proto.is_vpn = 0

        memory_available = proto.memory_available
        memory_available.version = 55
        memory_available.hidden_value = 81

        proto.external_storage_total = 49973
        proto.external_storage_available = 11338
        proto.internal_storage_total = 854
        proto.internal_storage_available = 11466
        proto.game_disk_storage_total = 49973
        proto.game_disk_storage_available = 11466
        proto.external_sdcard_total_storage = 49973
        proto.external_sdcard_avail_storage = 11466

        proto.library_path = "/data/app/~~lhfxtccbupg2qvjmsurtzw==/com.dts.freefireth-n3achphnxpdxjd80uiibww==/lib/arm64"
        proto.library_token = "b8e0cd5e295eee42f5860d3c86e483dd|/data/app/~~lhfxtccbupg2qvjmsurtzw==/com.dts.freefireth-n3achphnxpdxjd80uiibww==/base.apk"

        base_payload = proto.SerializeToString()

        extra = b""
        extra += _pb_field(96, '{"cur_rate":[90,60,120],"support_etc2":false}')
        extra += _pb_field(97, 1)
        extra += _pb_field(99, "4")
        extra += _pb_field(100, "4")
        extra += _pb_field(102, b"\x17]enwu\x0er5")
        extra += _pb_field(104, 52882)
        extra += _pb_field(105, 1)
        extra += _pb_field(106, "https://dl.ak.freefiremobile.com/live/abhotupdates/|https://core-ak.freefiremobile.com/live/abhotupdates/|6b2078db9d22dd98f8e9386a39af8462")
        extra += _pb_field(107, "c8e41b7a93f02d56e1a94c7b8203f5d1")

        full_payload = base_payload + extra
        return await aes_encrypt(full_payload, AES_KEY, AES_IV)
    except Exception:
        return None


async def send_majorlogin(data, release_version, server_url):
    try:
        url = f"{server_url}majorlogin" if server_url.endswith('/') else f"{server_url}/majorlogin"
        req_headers = headers.copy()
        req_headers["releaseversion"] = str(release_version)
        response = await client.post(url, headers=req_headers, data=data)
        if response.status_code != 200:
            return None
        response_content = response.content
        if len(response_content) < 40:
            return None

        res_proto = thunderFF_pb2.MajorLoginRes()
        try:
            res_proto.ParseFromString(response_content)
        except Exception:
            pass

        dict_res = {}
        try:
            parsed = Parser().parse(response_content.hex())
            dict_res = await parse_results(parsed)
        except Exception:
            pass

        key_val = get_proto_field(dict_res, 22)
        iv_val = get_proto_field(dict_res, 23)

        if not key_val:
            key_val = res_proto.aes_ak
        if not iv_val:
            iv_val = res_proto.iv_i

        if isinstance(key_val, str):
            try:
                key_val = bytes.fromhex(key_val)
            except Exception:
                pass
        if isinstance(iv_val, str):
            try:
                iv_val = bytes.fromhex(iv_val)
            except Exception:
                pass

        if not key_val or not iv_val:
            for offset in range(min(128, len(response_content))):
                try:
                    candidate = thunderFF_pb2.MajorLoginRes()
                    candidate.ParseFromString(response_content[offset:])
                    if candidate.region and candidate.token:
                        res_proto = candidate
                        break
                except Exception:
                    pass
            try:
                parsed = Parser().parse(response_content.hex())
                dict_res = await parse_results(parsed)
                kv = get_proto_field(dict_res, 22)
                ivv = get_proto_field(dict_res, 23)
                if isinstance(kv, str):
                    try:
                        kv = bytes.fromhex(kv)
                    except Exception:
                        pass
                if isinstance(ivv, str):
                    try:
                        ivv = bytes.fromhex(ivv)
                    except Exception:
                        pass
                if kv:
                    key_val = kv
                if ivv:
                    iv_val = ivv
            except Exception:
                pass

        if key_val:
            try:
                res_proto.aes_ak = key_val
            except Exception:
                pass
        if iv_val:
            try:
                res_proto.iv_i = iv_val
            except Exception:
                pass

        return res_proto
    except Exception as e:
        log(f"[-] send_majorlogin error: {e}")
        return None


async def send_getlogin(data, base_url, token, release_version):
    try:
        url = f"{base_url.rstrip('/')}/getlogindata"
        req_headers = headers.copy()
        req_headers["releaseversion"] = release_version
        req_headers['authorization'] = f"bearer {token}"
        req_headers['host'] = "clientbp.ppmainecoonghj.com"
        response = await client.post(url, headers=req_headers, data=data)
        if response.status_code != 200:
            return None
        response_content = response.content

        res_proto = thunderFF_pb2.GetLoginDataRes()
        try:
            res_proto.ParseFromString(response_content)
        except Exception:
            pass

        def _extract_addr(raw_bytes, field_no):
            try:
                pos = 0
                n = len(raw_bytes)
                def read_varint(buf, p):
                    res = 0
                    sh = 0
                    while p < len(buf):
                        b = buf[p]
                        p += 1
                        res |= (b & 0x7f) << sh
                        if not (b & 0x80):
                            break
                        sh += 7
                    return res, p

                fields = {}
                while pos < n:
                    try:
                        key, pos = read_varint(raw_bytes, pos)
                    except Exception:
                        break
                    fn = key >> 3
                    wt = key & 0x07
                    try:
                        if wt == 0:
                            val, pos = read_varint(raw_bytes, pos)
                        elif wt == 2:
                            ln, pos = read_varint(raw_bytes, pos)
                            val = raw_bytes[pos:pos + ln]
                            pos += ln
                        elif wt == 5:
                            val = raw_bytes[pos:pos + 4]
                            pos += 4
                        elif wt == 1:
                            val = raw_bytes[pos:pos + 8]
                            pos += 8
                        else:
                            break
                    except Exception:
                        break
                    fields.setdefault(fn, []).append(val)

                if field_no in fields:
                    v = fields[field_no][0]
                    if isinstance(v, bytes):
                        try:
                            return v.decode('utf-8', 'ignore')
                        except Exception:
                            return None
                    return str(v)
            except Exception:
                return None

        try:
            for offset in range(0, min(80, len(response_content))):
                fa = _extract_addr(response_content[offset:], 14)
                ia = _extract_addr(response_content[offset:], 32)
                if fa and ":" in fa and ia and ":" in ia:
                    res_proto.functional_addrs = fa
                    res_proto.informational_addrs = ia
                    break
        except Exception:
            pass

        dict_res = {}
        try:
            parsed = Parser().parse(response_content.hex())
            dict_res = await parse_results(parsed)
        except Exception:
            pass

        return res_proto, dict_res
    except Exception as e:
        log(f"[-] send_getlogin error: {e}")
        return None


async def build_tcp_startup_packet(account_id, token, server_time, key, iv, region="me", typ='online'):
    uid_hex = f"{int(account_id):016x}"
    timestamp_hex = f"{int(server_time):08x}"
    encode_token = token.encode()
    encrypted_packet = AES.new(key, AES.MODE_CBC, iv).encrypt(pad(encode_token, 16)).hex()
    encrypted_packet_length = f"{len(encrypted_packet) // 2:08x}"
    if typ == 'online':
        return f"9015{uid_hex}{timestamp_hex}00000000{encrypted_packet_length}{encrypted_packet}"
    else:
        return f"9015{uid_hex}{timestamp_hex}{encrypted_packet_length}{encrypted_packet}"


async def send_keep_alive(region="me"):
    try:
        reg = str(region).upper() if region else "me"
        ka_hex = "0219" if reg == "me" else ("0214" if reg == "ind" else "0215")
        return bytes.fromhex(ka_hex)
    except Exception:
        return bytes.fromhex("0219")


async def start_game_battle_royale(region, client_version, writer, key, iv):
    packet = bytes.fromhex("080112800a0a010110013a110a044944433110aa011a064555524f50453a100a044944433210311a064555524f504540014a0801090a0b1219202758016291090a8001303838463832424630324139363736373032303130313030303030303030303030303136303030313030313530303032323246393745454530463030303030303436373632353134303030303030303030303030303030303030303030303030303030303030303030303030303066663030303030303030636163666131366410241afb02735d5e571400024a775d45414d1a041b1c001f11010449715f4243481a001e1d071c1703004b1a4066785c524570735c51486775421b5c5a4c07504042685a63610816054e19025e75196001477c015165406370195f5547404e4550640103020f1304064863754268676c755f65576e40467e5f0a417a4701026d675d6e73670b1108495a4c6a0b78470b740065645e525a057258425f584a447d4e6759440c11044e7c596d7f4b625f7d04055a47505c4e1d6b5b4107447d7201057d7f0f14084e430457674f7e517d72015172415d027473577c4d615f79535256780911030f4d5e027a797f614165067806505d53777750475e75064257076500460817014e741e7e5078487e7a7c465e7669767153497064605a7376677773550d160148037e18675966787f4c42607a645f577e7b441b460776026b18685d0b110205490060020f70676175654674706671797f41067346677c4e06585e780f15074c57047b40517075415f6364027259674b5b0166407f7340600407770a22047a5d5c52300b3a0a167305067162727516134208312e3133302e3232480350015ae90403626253513635686e556f4e36416456324b796f566c636f477776484f624e56526c4d727073504b4f43654177616848494176795556497273743752737149734a7a786b3247525268377a2f637664626d504f6a73552f79626d38547a4c69586d2f474351696d494b53486833447955726f39515152756c34545350626d6d624b7949565937545671577059455372323646572f59624578507338514f706d317372785455736c30796a434144444d4f34616a654b615753366361496c554b4963797a494e396d52516f715277687939797257476d337a644345337a6a61436f492f5a585233656f65365a42647a64677654636b6b665733356e4d4c6a6a565072564b6433523172756174394e50514150724a5546627859696c4c5a3859707336654d5447666b6649793574666a526c314d4648706b51774c6373374439656378566c41636f374e664f6d2b30654756466c4434744478706771385533595973587645384842502f70666c767a737138316a32524f4d7857437556445442492f684735625462773166456e4249725162762b636144775147696f74554e316d4c4b77734379456f4766706746614251457645672b736a764c4c78704743334c304a5344532f74526169504354553344374e6249306547516651622f5a466f4c36455630775a324d6f583932414c572f5049752f56634663584e70596b356f7966326151416a536971486a2f363276354843644f525551303578754e6171795251625653704654303137655237675255636b4966366c6f447476342b514e4a4670766d74757077707774396a5a5974437a4b56743657726d6e36785837706658456251555434684f3758a201050803108703a201050804108103a20105080510c001a20105081d10cc01a2010408161078a20105080e10af01a201020815")
    proto = thunderFF_pb2.StartMatch()
    proto.ParseFromString(packet)
    if hasattr(proto.main, 'region_list') and len(proto.main.region_list) > 0:
        proto.main.region_list[0].region = region
        if len(proto.main.region_list) > 1:
            proto.main.region_list[1].region = region
    if hasattr(proto.main, 'client_version'):
        proto.main.client_version.remote_version = client_version
    packet = proto.SerializeToString()
    encrypted_packet = (await aes_encrypt(packet, key, iv)).hex()
    packet_length = len(encrypted_packet) // 2
    hex_length = hex(packet_length)[2:]
    hex_length = hex_length if len(hex_length) > 1 else "0" + hex_length
    reg = str(region).upper() if region else "me"
    reg_prefix = "031900" if reg == "me" else ("031900" if reg == "ind" else "031900")
    final_packet = reg_prefix + "0" * (6 - len(hex_length)) + hex_length + encrypted_packet
    writer.write(bytes.fromhex(final_packet))
    await writer.drain()
    log(f"[br] match search sent ({packet_length} bytes) | region: {reg}")


async def start_game_lone_wolf(region, client_version, writer, key, iv):
    packet = bytes.fromhex("080112800a0a010b102b3a110a044944433110aa011a064555524f50453a100a044944433210311a064555524f504540014a0801090a0b1219202758016291090a8001303838463832424630324139363736373032303130313030303030303030303030303136303030313030313530303032323246393745454530463030303030303436373632353134303030303030303030303030303030303030303030303030303030303030303030303030303066663030303030303030636163666131366410241afb02735d5e571400024a775d45414d1a041b1c001f11010449715f4243481a001e1d071c1703004b1a4066785c524570735c51486775421b5c5a4c07504042685a63610816054e19025e75196001477c015165406370195f5547404e4550640103020f1304064863754268676c755f65576e40467e5f0a417a4701026d675d6e73670b1108495a4c6a0b78470b740065645e525a057258425f584a447d4e6759440c11044e7c596d7f4b625f7d04055a47505c4e1d6b5b4107447d7201057d7f0f14084e430457674f7e517d72015172415d027473577c4d615f79535256780911030f4d5e027a797f614165067806505d53777750475e75064257076500460817014e741e7e5078487e7a7c465e7669767153497064605a7376677773550d160148037e18675966787f4c42607a645f577e7b441b460776026b18685d0b110205490060020f70676175654674706671797f41067346677c4e06585e780f15074c57047b40517075415f6364027259674b5b0166407f7340600407770a22047a5d5c52300b3a0a167305067162727516134208312e3133302e3232480350015ae90403626253513635686e556f4e36416456324b796f566c636f477776484f624e56526c4d727073504b4f43654177616848494176795556497273743752737149734a7a786b3247525268377a2f637664626d504f6a73552f79626d38547a4c69586d2f474351696d494b53486833447955726f39515152756c34545350626d6d624b7949565937545671577059455372323646572f59624578507338514f706d317372785455736c30796a434144444d4f34616a654b615753366361496c554b4963797a494e396d52516f715277687939797257476d337a644345337a6a61436f492f5a585233656f65365a42647a64677654636b6b665733356e4d4c6a6a565072564b6433523172756174394e50514150724a5546627859696c4c5a3859707336654d5447666b6649793574666a526c314d4648706b51774c6373374439656378566c41636f374e664f6d2b30654756466c4434744478706771385533595973587645384842502f70666c767a737138316a32524f4d7857437556445442492f684735625462773166456e4249725162762b636144775147696f74554e316d4c4b77734379456f4766706746614251457645672b736a764c4c78704743334c304a5344532f74526169504354553344374e6249306547516651622f5a466f4c36455630775a324d6f583932414c572f5049752f56634663584e70596b356f7966326151416a536971486a2f363276354843644f525551303578754e6171795251625653704654303137655237675255636b4966366c6f447476342b514e4a4670766d74757077707774396a5a5974437a4b56743657726d6e36785837706658456251555434684f3758a201050803108703a201050804108103a20105080510c001a20105081d10cc01a2010408161078a20105080e10af01a201020815")
    proto = thunderFF_pb2.StartMatch()
    proto.ParseFromString(packet)
    if hasattr(proto.main, 'region_list') and len(proto.main.region_list) > 0:
        proto.main.region_list[0].region = region
        if len(proto.main.region_list) > 1:
            proto.main.region_list[1].region = region
    if hasattr(proto.main, 'client_version'):
        proto.main.client_version.remote_version = client_version
    packet = proto.SerializeToString()
    encrypted_packet = (await aes_encrypt(packet, key, iv)).hex()
    packet_length = len(encrypted_packet) // 2
    hex_length = hex(packet_length)[2:]
    hex_length = hex_length if len(hex_length) > 1 else "0" + hex_length
    reg = str(region).upper() if region else "me"
    reg_prefix = "031400" if reg == "me" else ("031400" if reg == "ind" else "031500")
    final_packet = reg_prefix + "0" * (6 - len(hex_length)) + hex_length + encrypted_packet
    writer.write(bytes.fromhex(final_packet))
    await writer.drain()
    log(f"[lw] match search sent ({packet_length} bytes) | region: {reg}")


async def has_ssan_zig(n):
    z = (n << 1) & 0xffffffffffffffff
    out = bytearray()
    while z >= 0x80:
        out.append((z & 0x7f) | 0x80)
        z >>= 7
    out.append(z)
    return bytes(out)


async def uleb_encode(n):
    out = bytearray()
    while True:
        b = n & 0x7f
        n >>= 7
        if n:
            b |= 0x80
        out.append(b)
        if not n:
            break
    return bytes(out)


async def tea_enc(v0, v1, k0, k1, k2, k3):
    s = 0
    for _ in range(_ROUNDS):
        s = (s + _DELTA) & 0xffffffff
        v0 = (v0 + (((((v1 << 4) & 0xffffffff) + k0) & 0xffffffff ^
                      ((v1 + s) & 0xffffffff) ^
                      (((v1 >> 5) + k1) & 0xffffffff)))) & 0xffffffff
        v1 = (v1 + (((((v0 << 4) & 0xffffffff) + k2) & 0xffffffff ^
                      ((v0 + s) & 0xffffffff) ^
                      (((v0 >> 5) + k3) & 0xffffffff)))) & 0xffffffff
    return v0, v1


async def tea_dec(v0, v1, k0, k1, k2, k3):
    s = (_DELTA * _ROUNDS) & 0xffffffff
    for _ in range(_ROUNDS):
        v1 = (v1 - (((((v0 << 4) & 0xffffffff) + k2) & 0xffffffff ^
                      ((v0 + s) & 0xffffffff) ^
                      (((v0 >> 5) + k3) & 0xffffffff)))) & 0xffffffff
        v0 = (v0 - (((((v1 << 4) & 0xffffffff) + k0) & 0xffffffff ^
                      ((v1 + s) & 0xffffffff) ^
                      (((v1 >> 5) + k1) & 0xffffffff)))) & 0xffffffff
        s = (s - _DELTA) & 0xffffffff
    return v0, v1


async def tea_cbc_encrypt(padded, key_bytes):
    k0, k1, k2, k3 = (struct.unpack_from("<i", key_bytes, o)[0] for o in (0, 4, 8, 12))
    out = bytearray(len(padded))
    prev_cipher = bytearray(8)
    prev_intermediate = bytearray(8)
    for i in range(0, len(padded), 8):
        xored = bytearray(8)
        for j in range(8):
            xored[j] = padded[i + j] ^ prev_cipher[j]
        e0, e1 = await tea_enc(
            struct.unpack_from("<i", xored, 0)[0],
            struct.unpack_from("<i", xored, 4)[0],
            k0, k1, k2, k3,
        )
        enc = bytearray(8)
        struct.pack_into("<i", enc, 0, e0)
        struct.pack_into("<i", enc, 4, e1)
        for j in range(8):
            out[i + j] = enc[j] ^ prev_intermediate[j]
        prev_cipher[:] = out[i:i + 8]
        prev_intermediate[:] = xored
    return bytes(out)


async def build_padded(content):
    pad_len = (8 - (len(content) + 10) % 8) % 8
    return bytes([pad_len, 0, 0]) + b"\x00" * pad_len + content + b"\x00" * 7


async def encode_header(layout, send_option, cmd, order_id, flags, length, k, v80):
    out = bytearray()
    for code in layout:
        value = {0: send_option, 1: cmd, 2: order_id, 3: flags, 4: length}[code]
        if _FIELD_SIZES[code] == 1:
            out.append((value & 0xff) ^ k)
        else:
            v = ((value & 0xffff) ^ v80) & 0xffff
            out.append(v & 0xff)
            out.append((v >> 8) & 0xff)
    return bytes(out)


async def crc7_buff(crc, buf):
    c = crc & 0x7f
    for b in buf:
        c = CRC7_TABLE[((2 * (c & 0xff)) ^ (b & 0xff)) & 0xff] & 0x7f
    return c & 0x7f


async def sv_frame(msg_key, layout, send_option, cmd, order_id, flags, content, key, encrypted=True):
    k = key[0]
    v80 = ((k << 8) | k) & 0xffff
    body = await tea_cbc_encrypt(await build_padded(content), key) if encrypted else content
    hdr = bytearray([msg_key, 0]) + await encode_header(layout, send_option, cmd, order_id, flags, len(body), k, v80)
    packet = bytearray(hdr + body)
    packet[1] = await crc7_buff(0, bytes(packet[2:])) & 0x7f
    return bytes(packet)


async def build_match_startup_packets(token, udp_key, match_code, account_id, block_val,
                                      server_ip="", region="me", client_version="1.132.8",
                                      client_version_code="2019121229", access_token="",
                                      mode_id=1, map_id=1):
    token = token.strip()
    udp_key = bytes.fromhex(udp_key)
    match_code = [int(ch) for ch in str(match_code).strip()]

    thunder_jwt = token[:660] if len(token) > 660 else token
    sharma_jwt = token[660:] if len(token) > 660 else ""
    encoded_thunder_jwt = thunder_jwt.encode() if isinstance(thunder_jwt, str) else thunder_jwt
    encoded_sharma_jwt = sharma_jwt.encode() if isinstance(sharma_jwt, str) else sharma_jwt

    garena420 = await has_ssan_zig(len(encoded_thunder_jwt)) + encoded_thunder_jwt
    reg = str(region).upper() if region else "me"

    csoversea_block = bytes.fromhex(
        "ca0163736f7665727365612e7374726f6e67686f6c642e66726565666972656d6f62696c652e636f6d"
        "3b302e302e302e303b33342e3132362e37362e34353b33342e38372e3137372e31343b33342e38372e"
        "3137302e3233303b33352e3138352e3138332e35370000000000000100000000000000000000000001"
        "00000800000100000000000100a8a2d7bebd8d8bdf110200"
    )

    mid = bytes.fromhex('0000000001000102030101') + await has_ssan_zig(len(reg)) + reg.encode()
    mid += bytes.fromhex('0001030003000004')
    mid += await has_ssan_zig(len(client_version)) + client_version.encode()
    mid += await has_ssan_zig(len(client_version_code)) + client_version_code.encode()
    mid += csoversea_block

    clean_ip = server_ip.split(':')[0] if server_ip else "0.0.0.0"
    mid += await has_ssan_zig(len(clean_ip)) + clean_ip.encode()

    clean_acc_tok = access_token.strip() if access_token else ""
    if clean_acc_tok:
        mid += await has_ssan_zig(len(clean_acc_tok)) + clean_acc_tok.encode()

    mid += await has_ssan_zig(len(encoded_sharma_jwt)) + encoded_sharma_jwt

    tg_garena420 = (
        await uleb_encode(int(account_id)) +
        await uleb_encode(int(block_val)) +
        await uleb_encode(1) +
        await uleb_encode(int(mode_id)) +
        await uleb_encode(int(block_val)) +
        await uleb_encode(int(map_id)) +
        mid
    )

    process = await sv_frame(0x5e, match_code, 2, 447, 0, 1, garena420, udp_key)
    loading = await sv_frame(0x5a, match_code, 2, 448, 1, 1, tg_garena420, udp_key)
    return process.hex(), loading.hex()


async def produce_xor_key(secret_key):
    k = secret_key[0] if secret_key and len(secret_key) > 0 else 10
    return k, ((k << 8) | k) & 0xffff


async def parse_layout(layout):
    if isinstance(layout, str):
        return [int(ch) for ch in layout.strip()]
    return list(layout)


async def tea_cbc_decrypt(body, key_bytes):
    k0, k1, k2, k3 = (struct.unpack_from("<i", key_bytes, o)[0] for o in (0, 4, 8, 12))
    out = bytearray(len(body))
    prev_intermediate = bytearray(8)
    prev_cipher = bytearray(8)
    xored = bytearray(8)
    dec = bytearray(8)
    for i in range(0, len(body), 8):
        for j in range(8):
            xored[j] = body[i + j] ^ prev_intermediate[j]
        d0, d1 = await tea_dec(
            struct.unpack_from("<i", xored, 0)[0],
            struct.unpack_from("<i", xored, 4)[0],
            k0, k1, k2, k3
        )
        struct.pack_into("<i", dec, 0, d0)
        struct.pack_into("<i", dec, 4, d1)
        for j in range(8):
            out[i + j] = dec[j] ^ prev_cipher[j]
        prev_cipher[:] = body[i:i + 8]
        prev_intermediate[:] = dec
    return bytes(out)


async def build_hello_packet(text, key, layout):
    data = text.encode("utf-8")
    if len(data) > 25:
        raise ValueError(f"text is too long ({len(data)} bytes)")
    content = b"\x10\x00\x00\x00" + data + b"\x00" * (29 - 4 - len(data))
    k, v80 = await produce_xor_key(key)
    layout = await parse_layout(layout)
    padded = await build_padded(content)
    enc_body = await tea_cbc_encrypt(padded, key)
    header_bytes = await encode_header(layout, 1, 1, 0, 1, len(enc_body), k, v80)
    packet = bytearray([0x63, 0x00]) + header_bytes + enc_body
    packet[1] = await crc7_buff(0, packet[2:]) & 0x7f
    return bytes(packet).hex()


async def classify(frame):
    cmd = frame["cmd"]
    msg_name = MESSAGE_ID_TO_NAME.get(cmd, f"unknown_{cmd}")
    if msg_name == "udp_hello":
        return "hello"
    if msg_name == "udp_ack":
        return "ack"
    if msg_name == "udp_ping":
        return "ping"
    if msg_name == "rudp_join_match":
        return "join_match"
    if msg_name.startswith("rudp_"):
        return msg_name
    if msg_name.startswith("udp_"):
        return msg_name
    return "data"


async def build_packet(msg_key, layout, send_option, cmd, order_id, flags, content, key, encrypted=True):
    k = key[0]
    v80 = ((k << 8) | k) & 0xffff
    body = await tea_cbc_encrypt(await build_padded(content), key) if encrypted else content
    hdr = bytearray([msg_key, 0])
    for code in layout:
        value = {0: send_option, 1: cmd, 2: order_id, 3: flags, 4: len(body)}[code]
        if _FIELD_SIZES[code] == 1:
            hdr.append((value & 0xff) ^ k)
        else:
            v = ((value & 0xffff) ^ v80) & 0xffff
            hdr.append(v & 0xff)
            hdr.append((v >> 8) & 0xff)
    packet = bytearray(hdr + body)
    packet[1] = await crc7_buff(0, bytes(packet[2:])) & 0x7f
    return bytes(packet)


async def layouts_from_mask(mask):
    ru = [int(c) for c in str(mask).strip()]
    nr = [c for c in ru if c != 2]
    return ru, nr


async def reply_for(frame, key, mask, ack_key=0x68, ping_key=0x6d, hello_key=0x5b, ack_style="short"):
    ru, nr = await layouts_from_mask(mask)
    typ = await classify(frame)
    if typ == "hello":
        if ack_style == "echo":
            content = frame["content"] if frame["content"] else b"\x10\x00\x00\x00"
            return typ, await build_packet(hello_key, nr, 1, 1, None, 1, content, key)
        return typ, await build_packet(ack_key, nr, 0, 2, None, 1, b"\x01\x00", key)
    if typ == "ack":
        content = frame["content"] if frame["content"] else b"\x01\x00"
        return typ, await build_packet(ack_key, nr, 0, 2, None, 1, content, key)
    if typ == "ping":
        c = frame["content"]
        counter = c[:4] if len(c) >= 4 else c
        return typ, await build_packet(ping_key, nr, 0, 3, None, 0, counter + b"\x00\x00\x00", key, encrypted=False)
    if typ == "join_match":
        return typ, await build_packet(ack_key, nr, 0, 2, None, 1, b"\x02\x00", key)
    return typ, None


async def keepalive_ping(sock, ip, port, key_bytes, mask, stop_event):
    nr = (await layouts_from_mask(mask))[1]
    ping_keys = [0x66, 0x6d, 0x69, 0x6c, 0x6b, 0x6e, 0x6f, 0x70]
    loop = asyncio.get_event_loop()
    i = 0
    while not stop_event.is_set():
        pk = ping_keys[i % len(ping_keys)]
        counter = int(time.time() * 1000) & 0xffffffff
        pkt = await build_packet(pk, nr, 0, 3, None, 0, struct.pack("<i", counter) + b"\x00\x00\x00", key_bytes, encrypted=False)
        try:
            await loop.sock_sendto(sock, pkt, (ip, port))
        except Exception:
            pass
        i += 1
        try:
            await asyncio.wait_for(stop_event.wait(), timeout=3.0)
        except asyncio.TimeoutError:
            pass


async def try_header(buf, layout, k, v80):
    off = 2
    out = {}
    for code in layout:
        size = _FIELD_SIZES[code]
        if off + size > len(buf):
            return None
        out[_FIELD_NAMES[code]] = (buf[off] ^ k) if size == 1 else ((buf[off] | (buf[off + 1] << 8)) ^ v80) & 0xffff
        off += size
    out["headerlen"] = off
    return out


async def oicq_unpad(padded):
    if not padded or len(padded) < 8:
        return None
    if not all(padded[-1 - i] == 0 for i in range(7)):
        return None
    pad_len = padded[0] & 0x07
    s = 3 + pad_len
    e = len(padded) - 7
    return padded[s:e] if s < e else b""


async def decode_packet(packet, key, mask=None):
    data = bytes(packet) if isinstance(packet, bytes) else bytes.fromhex(packet)
    if len(data) < 8:
        return None
    k = key[0]
    v80 = ((k << 8) | k) & 0xffff
    crc_ok = (data[1] & 0x7f) == await crc7_buff(0, data[2:])
    candidates = []
    if mask:
        ru, nr = await layouts_from_mask(mask)
        layouts = [("rudp", ru), ("nonrudp", nr)]
    else:
        layouts = [("rudp", list(p)) for p in itertools.permutations([0, 1, 2, 3, 4])]
        layouts += [("nonrudp", list(p)) for p in itertools.permutations([0, 1, 3, 4])]
    for kind, layout in layouts:
        f = await try_header(data, layout, k, v80)
        if not f:
            continue
        if f["flags"] > 7 or f["sendoption"] > 7:
            continue
        if f["length"] != len(data) - f["headerlen"]:
            continue
        body = data[f["headerlen"]:f["headerlen"] + f["length"]]
        content = None
        padded = None
        if f["flags"] & 1:
            if len(body) < 8 or len(body) % 8 != 0:
                continue
            padded = await tea_cbc_decrypt(body, key)
            content = await oicq_unpad(padded)
            if content is None:
                continue
        else:
            content = body
        score = (1 if crc_ok else 0) + (1 if content is not None else 0)
        candidates.append({
            "kind": kind, "layout": layout, "headerlen": f["headerlen"],
            "msgkey": data[0], "cmd": f["cmd"], "flags": f["flags"],
            "sendoption": f["sendoption"], "orderid": f.get("orderid"),
            "length": f["length"], "content": content, "crcok": crc_ok,
            "padded": padded, "score": score, "total": len(data),
        })
    if not candidates:
        return None
    candidates.sort(key=lambda c: (c["kind"] == "rudp" or c["kind"] == "nonrudp", c["score"]), reverse=True)
    return candidates[0]


async def read_varints_full(b):
    out, i = [], 0
    while i < len(b):
        n, shift = 0, 0
        while i < len(b):
            byte = b[i]; i += 1
            n |= (byte & 0x7f) << shift
            if not byte & 0x80:
                break
            shift += 7
        out.append(n)
    return out


async def play_game(server_ip_port, thunder, sharma, udp_key, match_code,
                    account_id, player_region, client_version, key, iv,
                    match_index: int):
    match_start_time = time.time()
    ping_task = None
    sock = None
    ping_stop = asyncio.Event()
    uid_str = str(account_id)
    completed_cleanly = False

    try:
        ip, port = server_ip_port.split(":")
        port = int(port)
        resolved_ip = await resolve_host_cloudflare(ip)

        loop = asyncio.get_event_loop()
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            sock.bind(('0.0.0.0', 0))
        except Exception:
            pass
        optimize_udp_socket(sock)
        sock.setblocking(False)

        udp_key_bytes = bytes.fromhex(udp_key)
        hello_packet = await build_hello_packet(f"{account_id}_2585", udp_key_bytes, match_code)
        await loop.sock_sendto(sock, bytes.fromhex(hello_packet), (resolved_ip, port))

        ack_state = "waiting_for_hello_reply"
        thunder_sent = False
        sharma_sent = False
        join_match_received = False
        local_closed = False
        send_lock = asyncio.Lock()

        ping_task = asyncio.create_task(
            keepalive_ping(sock, resolved_ip, port, udp_key_bytes, match_code, ping_stop)
        )

        last_activity = time.time()
        max_idle_before_hello_resend = 7.0

        async def send_thunder_sharma_inline():
            nonlocal ack_state, thunder_sent, sharma_sent
            if thunder_sent:
                return
            async with send_lock:
                if thunder_sent:
                    return
                try:
                    await loop.sock_sendto(sock, bytes.fromhex(thunder), (resolved_ip, port))
                    thunder_sent = True
                    await asyncio.sleep(0.3)
                    prepare_ack = await build_packet(
                        0x68, (await layouts_from_mask(match_code))[1],
                        0, 2, None, 1, b"\x01\x00", udp_key_bytes
                    )
                    await loop.sock_sendto(sock, prepare_ack, (resolved_ip, port))
                    await asyncio.sleep(0.4)
                    await loop.sock_sendto(sock, bytes.fromhex(sharma), (resolved_ip, port))
                    sharma_sent = True
                    ack_state = "thunder_sharma_sent"
                    log(f"[match #{match_index}] startup delivered")
                except Exception as e:
                    log(f"[match #{match_index}] startup send failed: {e}")

        while not local_closed:
            elapsed = time.time() - match_start_time
            if elapsed > LW_MAX_MATCH_DURATION:
                completed_cleanly = True
                break

            try:
                response, server_addr = await asyncio.wait_for(
                    loop.sock_recvfrom(sock, 65535), timeout=0.5
                )
                if response:
                    last_activity = time.time()
                    frame = await decode_packet(response, udp_key_bytes, match_code)
                    if frame:
                        ptype = await classify(frame)

                        if frame['cmd'] in [103, 107]:
                            log(f"[*] match #{match_index} finished")
                            completed_cleanly = True
                            local_closed = True
                            continue

                        if ptype in ["ack", "ping", "hello", "join_match"]:
                            if ptype == "hello" and ack_state == "waiting_for_hello_reply":
                                typ, reply = await reply_for(
                                    frame, udp_key_bytes, match_code, ack_style="short"
                                )
                                if reply:
                                    await loop.sock_sendto(sock, reply, server_addr)
                                ack_state = "ack_sent_waiting"
                            elif ptype == "ack":
                                if ack_state == "waiting_for_hello_reply":
                                    typ, reply = await reply_for(frame, udp_key_bytes, match_code)
                                    if reply:
                                        await loop.sock_sendto(sock, reply, server_addr)
                                    ack_state = "ready_to_send_thunder"
                                elif ack_state == "ack_sent_waiting":
                                    ack_state = "ready_to_send_thunder"
                                else:
                                    typ, reply = await reply_for(frame, udp_key_bytes, match_code)
                                    if reply:
                                        await loop.sock_sendto(sock, reply, server_addr)
                            elif ptype == "ping":
                                typ, reply = await reply_for(frame, udp_key_bytes, match_code)
                                if reply:
                                    await loop.sock_sendto(sock, reply, server_addr)
                            elif ptype == "join_match" and not join_match_received:
                                typ, reply = await reply_for(frame, udp_key_bytes, match_code)
                                if reply:
                                    await loop.sock_sendto(sock, reply, server_addr)
                                    join_match_received = True

            except asyncio.TimeoutError:
                if ack_state == "ready_to_send_thunder" and not thunder_sent:
                    await send_thunder_sharma_inline()
                elif ack_state == "waiting_for_hello_reply":
                    if (time.time() - last_activity) > max_idle_before_hello_resend:
                        try:
                            pkt = await build_hello_packet(
                                f"{account_id}_2585", udp_key_bytes, match_code
                            )
                            await loop.sock_sendto(sock, bytes.fromhex(pkt), (resolved_ip, port))
                        except Exception:
                            pass
                        last_activity = time.time()
                    if (time.time() - match_start_time) > 25.0:
                        break
                elif ack_state == "thunder_sharma_sent":
                    idle_time = time.time() - last_activity
                    if idle_time > LW_MATCH_IDLE_TIMEOUT:
                        completed_cleanly = True
                        break

            except BlockingIOError:
                await asyncio.sleep(0.05)
            except OSError:
                await asyncio.sleep(0.5)
                continue
            except Exception:
                await asyncio.sleep(0.5)
                continue

            if ack_state == "ready_to_send_thunder" and not thunder_sent:
                await send_thunder_sharma_inline()

        return f"match #{match_index} finished"

    except Exception as e:
        log(f"[match #{match_index}] session error: {e}")
        return f"match #{match_index} error"

    finally:
        ping_stop.set()
        if ping_task:
            ping_task.cancel()
            try:
                await ping_task
            except asyncio.CancelledError:
                pass
        if sock:
            try:
                sock.close()
            except Exception:
                pass
        await _dec_match(uid_str)


async def lw_fast_flow(addrs, tcp_online_starter, account_region, client_version,
                        key, iv, account_id="", account_data=None, max_reconnects=10):
    reconnects = 0
    ip, port = addrs.split(":")
    play_matches: List[asyncio.Task] = []
    no_response_count = 0
    search_attempts = 0
    last_start_time = 0.0
    uid_str = str(account_id)
    parse_fail_count = 0

    current_token = tcp_online_starter
    current_key = key
    current_iv = iv
    current_account_data = account_data

    try:
        if current_account_data:
            bot_state.register_account(
                uid_str,
                current_account_data.get("nickname", f"player_{uid_str}"),
                current_account_data.get("region", "me"),
                current_account_data.get("level", 1),
                current_account_data.get("exp", 0),
                current_account_data.get("likes", 0),
            )
            bot_state.update_status(uid_str, "running")
            bot_state.account_start_ref[uid_str] = time.time()
            bot_state.start_exp_ref[uid_str] = int(current_account_data.get("exp", 0))
            bot_state.session_matches_ref[uid_str] = 0
            bot_state.exp_limit_reached_ref.discard(uid_str)
    except Exception:
        pass

    while True:
        writer = None
        gateway_ping_task = None
        try:
            resolved_ip = await resolve_host_cloudflare(ip)
            reader, writer = await asyncio.open_connection(resolved_ip, int(port))

            raw_sock = writer.get_extra_info('socket')
            if raw_sock:
                optimize_tcp_socket(raw_sock)

            writer.write(bytes.fromhex(current_token))
            await writer.drain()

            try:
                init_ka = await send_keep_alive(account_region)
                if init_ka and writer and not writer.is_closing():
                    writer.write(init_ka)
                    await asyncio.wait_for(writer.drain(), timeout=3)
            except Exception:
                pass

            async def func_gateway_keepalive():
                ka_bytes = await send_keep_alive(account_region)
                while True:
                    await asyncio.sleep(5)
                    try:
                        if writer and not writer.is_closing():
                            writer.write(ka_bytes)
                            await writer.drain()
                    except Exception:
                        break

            gateway_ping_task = asyncio.create_task(func_gateway_keepalive())

            log(f"[+] tcp gateway connected (lw) | uid: {uid_str}")
            reconnects = 0
            no_response_count = 0
            last_start_time = 0.0
            parse_fail_count = 0

            async def send_start_match():
                nonlocal search_attempts, last_start_time
                search_attempts += 1
                try:
                    await asyncio.sleep(random.uniform(0.3, 0.6))
                    log(f"[lw] uid {uid_str} -> lw match #{search_attempts}")
                    await start_game_lone_wolf(
                        account_region, client_version, writer,
                        current_key, current_iv
                    )
                except Exception as e:
                    log(f"[!] startmatch notice: {e}")
                last_start_time = asyncio.get_running_loop().time()

            await send_start_match()

            while True:
                play_matches[:] = [m for m in play_matches if not m.done()]

                now = asyncio.get_running_loop().time()
                if len(play_matches) == 0 and (now - last_start_time >= LW_START_INTERVAL):
                    await send_start_match()

                try:
                    data = await asyncio.wait_for(reader.read(8192), timeout=0.5)
                except asyncio.TimeoutError:
                    no_response_count += 1
                    if no_response_count > 80:
                        raise ConnectionError("idle")
                    continue

                if not data:
                    raise ConnectionError("connection closed by server")

                hex_data = data.hex()
                packet_length = len(data)
                no_response_count = 0

                if hex_data.startswith("0300") and 10 < packet_length < 30:
                    log(f"[*] queue confirmed (lw) | uid: {uid_str}")
                    continue

                if hex_data.startswith("0300") and packet_length >= 300:
                    log(f"[+] match found udp {account_id}...")
                    try:
                        res = json.loads(await decode_protobuf(hex_data[10:]))
                        token = None
                        udp_key = None
                        match_code = None
                        server_ip_port = None
                        match_account_id = None
                        block_val = None

                        if '42' in res and 'data' in res['42']:
                            match_code = res['42']['data']
                        if '5' in res and 'data' in res['5']:
                            res_field5 = res['5']['data']
                            server_ip_port = res_field5.get('2', {}).get('data')
                            udp_key = res_field5.get('3', {}).get('data')
                            token = res_field5.get('4', {}).get('data')
                            if '42' in res_field5:
                                match_code = res_field5['42']['data']
                        if '1' in res and 'data' in res['1']:
                            match_account_id = res['1']['data']
                        if '5' in res and 'data' in res['5']:
                            block_val = res['5']['data'].get('1', {}).get('data')

                        effective_acc_id = match_account_id or account_id or "me_bot"

                        if token and udp_key and match_code and server_ip_port:
                            acc_tok = current_account_data.get('access_token', '') if current_account_data else ""

                            mode_id, map_id = 43, 11

                            thunder, sharma = await build_match_startup_packets(
                                token, udp_key, match_code, effective_acc_id, block_val or 0,
                                server_ip=server_ip_port,
                                region=account_region,
                                client_version=client_version,
                                access_token=acc_tok,
                                mode_id=mode_id,
                                map_id=map_id
                            )

                            match_index = await _inc_match(uid_str)
                            log(f"[+] match #{match_index} [lw] injected -> {server_ip_port}")

                            try:
                                bot_state.increment_match(uid_str)
                                bot_state.session_matches_ref[uid_str] = \
                                    bot_state.session_matches_ref.get(uid_str, 0) + 1
                                bot_state.update_status(uid_str, "in_match")
                            except Exception:
                                pass

                            if gateway_ping_task:
                                gateway_ping_task.cancel()
                            await safe_close_writer(writer)
                            writer = None

                            new_match = asyncio.create_task(
                                play_game(
                                    server_ip_port,
                                    thunder,
                                    sharma,
                                    udp_key,
                                    match_code,
                                    effective_acc_id,
                                    "me",
                                    client_version,
                                    current_key,
                                    current_iv,
                                    match_index=match_index
                                )
                            )
                            play_matches.append(new_match)

                            await asyncio.sleep(LW_NEW_MATCH_DELAY)

                            try:
                                await refresh_account_profile(current_account_data)
                            except Exception:
                                pass

                            try:
                                new_exp = int(current_account_data.get("exp", 0))
                                new_lvl = int(current_account_data.get("level", 1))
                                bot_state.update_exp(uid_str, new_exp, new_lvl)

                                target = int(bot_state.exp_targets_ref.get(uid_str, 0) or 0)
                                start_exp = int(bot_state.start_exp_ref.get(uid_str, new_exp))
                                if target > 0 and (new_exp - start_exp) >= target:
                                    bot_state.exp_limit_reached_ref.add(uid_str)
                                    bot_state.update_status(uid_str, "completed")
                                    log(f"[+] uid {uid_str} reached exp target ({new_exp - start_exp}/{target})")
                            except Exception:
                                pass

                            if uid_str in bot_state.exp_limit_reached_ref:
                                log(f"[+] uid {uid_str} completed. stopping lw worker.")
                                bot_state.update_status(uid_str, "completed")
                                return

                            break
                        else:
                            parse_fail_count += 1
                            if parse_fail_count >= LW_MAX_PARSE_FAILS:
                                parse_fail_count = 0
                            await asyncio.sleep(LW_RECONNECT_DELAY)
                            break

                    except Exception as e:
                        log(f"[!] match packet notice: {e}")
                        parse_fail_count += 1
                        if parse_fail_count >= LW_MAX_PARSE_FAILS:
                            parse_fail_count = 0
                        await asyncio.sleep(LW_RECONNECT_DELAY)
                        break

                if 30 <= packet_length <= 40:
                    continue

        except asyncio.CancelledError:
            if gateway_ping_task:
                gateway_ping_task.cancel()
            raise
        except Exception as e:
            if gateway_ping_task:
                gateway_ping_task.cancel()
            play_matches[:] = [m for m in play_matches if not m.done()]
            await safe_close_writer(writer)

            if "cache expired" in str(e):
                break

            reconnects += 1
            if reconnects > max_reconnects:
                reconnects = 0
                await asyncio.sleep(3)
                continue

            await asyncio.sleep(min(reconnects, 2))
        finally:
            if gateway_ping_task:
                gateway_ping_task.cancel()
            if writer:
                await safe_close_writer(writer)


async def functional_lone_wolf(addrs, starter_packet, account_region, client_version,
                                key, iv, account_id="", account_data=None,
                                max_reconnects=10):
    cur_lvl = 1
    force_lw = False
    try:
        if account_data:
            v = account_data.get("level", 0)
            if v:
                cur_lvl = max(1, int(v))
            force_lw = bool(account_data.get("force_lw"))
    except Exception:
        cur_lvl = 1

    cur_mode = "lone_wolf" if (cur_lvl >= MODE_SWITCH_LEVEL or force_lw) else "br"
    log(f"[*] mode selected: {cur_mode} | lvl {cur_lvl}")

    if cur_mode == "lone_wolf":
        await lw_fast_flow(
            addrs, starter_packet, account_region, client_version,
            key, iv, account_id=account_id, account_data=account_data,
            max_reconnects=max_reconnects
        )
        return

    reconnects = 0
    ip, port = addrs.split(":")
    play_matches: List[asyncio.Task] = []
    no_response_count = 0
    search_attempts = 0
    last_start_time = 0.0
    uid_str = str(account_id)

    current_token = starter_packet
    current_key = key
    current_iv = iv
    current_account_data = account_data

    try:
        if current_account_data:
            bot_state.register_account(
                uid_str,
                current_account_data.get("nickname", f"player_{uid_str}"),
                current_account_data.get("region", "me"),
                current_account_data.get("level", 1),
                current_account_data.get("exp", 0),
                current_account_data.get("likes", 0),
            )
            bot_state.update_status(uid_str, "running")
            bot_state.account_start_ref[uid_str] = time.time()
            bot_state.start_exp_ref[uid_str] = int(current_account_data.get("exp", 0))
            bot_state.session_matches_ref[uid_str] = 0
            bot_state.exp_limit_reached_ref.discard(uid_str)
    except Exception:
        pass

    try:
        while True:
            writer = None
            gateway_ping_task = None
            try:
                resolved_ip = await resolve_host_cloudflare(ip)
                reader, writer = await asyncio.open_connection(resolved_ip, int(port))

                raw_sock = writer.get_extra_info('socket')
                if raw_sock:
                    optimize_tcp_socket(raw_sock)

                writer.write(bytes.fromhex(current_token))
                await writer.drain()

                try:
                    init_ka = await send_keep_alive(account_region)
                    if init_ka and writer and not writer.is_closing():
                        writer.write(init_ka)
                        await asyncio.wait_for(writer.drain(), timeout=3)
                except Exception:
                    pass

                async def func_gateway_keepalive():
                    ka_bytes = await send_keep_alive(account_region)
                    while True:
                        await asyncio.sleep(5)
                        try:
                            if writer and not writer.is_closing():
                                writer.write(ka_bytes)
                                await writer.drain()
                        except Exception:
                            break

                gateway_ping_task = asyncio.create_task(func_gateway_keepalive())

                log(f"[+] tcp gateway connected | uid: {uid_str}")
                reconnects = 0
                no_response_count = 0
                last_start_time = 0.0

                async def send_start_match():
                    nonlocal search_attempts, last_start_time
                    search_attempts += 1
                    current_region = "me"
                    cur_mode, cur_lvl = ("br", 1)
                    try:
                        if current_account_data:
                            cur_lvl = max(1, int(current_account_data.get("level", 1) or 1))
                            cur_mode = "lone_wolf" if cur_lvl >= MODE_SWITCH_LEVEL else "br"
                    except Exception:
                        pass
                    try:
                        await asyncio.sleep(random.uniform(0.2, 0.4))
                        log(f"[br] uid {uid_str} | lvl {cur_lvl} -> br match #{search_attempts}")
                        await start_game_battle_royale(
                            current_region, client_version, writer,
                            current_key, current_iv
                        )
                    except Exception as e:
                        log(f"[!] startmatch notice: {e}")
                    last_start_time = asyncio.get_running_loop().time()

                await send_start_match()

                while True:
                    play_matches[:] = [m for m in play_matches if not m.done()]

                    now = asyncio.get_running_loop().time()
                    if len(play_matches) == 0 and (now - last_start_time >= START_MATCH_INTERVAL):
                        await send_start_match()

                    try:
                        data = await asyncio.wait_for(reader.read(8192), timeout=0.5)
                    except asyncio.TimeoutError:
                        no_response_count += 1
                        if no_response_count > 60:
                            no_response_count = 0
                        continue

                    if not data:
                        raise ConnectionError("connection closed by server")

                    hex_data = data.hex()
                    packet_length = len(data)
                    no_response_count = 0

                    if hex_data.startswith("0300") and 10 < packet_length < 30:
                        log(f"[*] queue confirmed (br) | uid: {uid_str}")
                        continue

                    if hex_data.startswith("0300") and packet_length >= 300:
                        log(f"[+] match found (br) | uid: {uid_str}")

                        try:
                            res = json.loads(await decode_protobuf(hex_data[10:]))
                            token = None
                            udp_key = None
                            match_code = None
                            server_ip_port = None
                            match_account_id = None
                            block_val = None

                            if '42' in res and 'data' in res['42']:
                                match_code = res['42']['data']
                            if '5' in res and 'data' in res['5']:
                                res_field5 = res['5']['data']
                                server_ip_port = res_field5.get('2', {}).get('data')
                                udp_key = res_field5.get('3', {}).get('data')
                                token = res_field5.get('4', {}).get('data')
                                if '42' in res_field5:
                                    match_code = res_field5['42']['data']
                            if '1' in res and 'data' in res['1']:
                                match_account_id = res['1']['data']
                            if '5' in res and 'data' in res['5']:
                                block_val = res['5']['data'].get('1', {}).get('data')

                            effective_acc_id = match_account_id or account_id or "me_bot"

                            if token and udp_key and match_code and server_ip_port:
                                acc_tok = current_account_data.get('access_token', '') if current_account_data else ""

                                mode_id, map_id = 1, 1

                                thunder, sharma = await build_match_startup_packets(
                                    token, udp_key, match_code, effective_acc_id, block_val or 0,
                                    server_ip=server_ip_port,
                                    region=account_region,
                                    client_version=client_version,
                                    access_token=acc_tok,
                                    mode_id=mode_id,
                                    map_id=map_id
                                )

                                match_index = await _inc_match(uid_str)
                                log(f"[+] match #{match_index} [br] injected -> {server_ip_port}")

                                try:
                                    bot_state.increment_match(uid_str)
                                    bot_state.session_matches_ref[uid_str] = \
                                        bot_state.session_matches_ref.get(uid_str, 0) + 1
                                    bot_state.update_status(uid_str, "in_match")
                                except Exception:
                                    pass

                                new_match = asyncio.create_task(
                                    play_game(
                                        server_ip_port,
                                        thunder,
                                        sharma,
                                        udp_key,
                                        match_code,
                                        effective_acc_id,
                                        "me",
                                        client_version,
                                        current_key,
                                        current_iv,
                                        match_index=match_index
                                    )
                                )
                                play_matches.append(new_match)

                                async def drain_gateway_reader():
                                    while not new_match.done():
                                        try:
                                            data_gw = await asyncio.wait_for(reader.read(4096), timeout=1.0)
                                            if not data_gw:
                                                break
                                        except asyncio.TimeoutError:
                                            continue
                                        except Exception:
                                            break

                                drain_task = asyncio.create_task(drain_gateway_reader())

                                try:
                                    await new_match
                                except Exception as e:
                                    log(f"[match #{match_index}] error: {e}")
                                finally:
                                    drain_task.cancel()
                                    try:
                                        await drain_task
                                    except asyncio.CancelledError:
                                        pass

                                play_matches[:] = [m for m in play_matches if not m.done()]

                                try:
                                    await refresh_account_profile(current_account_data)
                                except Exception:
                                    pass

                                try:
                                    new_exp = int(current_account_data.get("exp", 0))
                                    new_lvl = int(current_account_data.get("level", 1))
                                    bot_state.update_exp(uid_str, new_exp, new_lvl)

                                    target = int(bot_state.exp_targets_ref.get(uid_str, 0) or 0)
                                    start_exp = int(bot_state.start_exp_ref.get(uid_str, new_exp))
                                    if target > 0 and (new_exp - start_exp) >= target:
                                        bot_state.exp_limit_reached_ref.add(uid_str)
                                        bot_state.update_status(uid_str, "completed")
                                        log(f"[+] uid {uid_str} reached exp target ({new_exp - start_exp}/{target})")
                                except Exception:
                                    pass

                                if uid_str in bot_state.exp_limit_reached_ref:
                                    log(f"[+] uid {uid_str} completed. stopping worker.")
                                    bot_state.update_status(uid_str, "completed")
                                    if gateway_ping_task:
                                        gateway_ping_task.cancel()
                                    await safe_close_writer(writer)
                                    writer = None
                                    return

                                if gateway_ping_task:
                                    gateway_ping_task.cancel()
                                await safe_close_writer(writer)
                                writer = None
                                break

                            else:
                                continue

                        except Exception as e:
                            log(f"[!] match packet notice: {e}")
                            continue

                    if 30 <= packet_length <= 40:
                        continue

            except asyncio.CancelledError:
                if gateway_ping_task:
                    gateway_ping_task.cancel()
                raise
            except Exception as e:
                if gateway_ping_task:
                    gateway_ping_task.cancel()
                play_matches[:] = [m for m in play_matches if not m.done()]
                await safe_close_writer(writer)

                if "cache expired" in str(e):
                    break

                reconnects += 1
                if reconnects > max_reconnects:
                    reconnects = 0
                    break

                await asyncio.sleep(min(reconnects * 0.5, 2.0))
            finally:
                if gateway_ping_task:
                    gateway_ping_task.cancel()
                if writer:
                    await safe_close_writer(writer)

    except asyncio.CancelledError:
        raise
    finally:
        for m in play_matches:
            if not m.done():
                m.cancel()
        try:
            bot_state.update_status(uid_str, "offline")
        except Exception:
            pass


async def informational(addrs, starter_packet, key, iv, region="me", account_id="", max_reconnects=3):
    reconnects = 0
    ip, port = addrs.split(":")
    while True:
        writer = None
        ping_task = None
        try:
            resolved_ip = await resolve_host_cloudflare(ip)
            reader, writer = await asyncio.open_connection(resolved_ip, int(port))

            raw_sock = writer.get_extra_info('socket')
            if raw_sock:
                optimize_tcp_socket(raw_sock)

            writer.write(bytes.fromhex(starter_packet))
            await writer.drain()
            reconnects = 0

            try:
                init_ka = await send_keep_alive(region)
                if init_ka and writer and not writer.is_closing():
                    writer.write(init_ka)
                    await asyncio.wait_for(writer.drain(), timeout=3)
            except Exception:
                pass

            async def info_keepalive():
                ka_bytes = await send_keep_alive(region)
                while True:
                    await asyncio.sleep(5)
                    try:
                        if writer and not writer.is_closing():
                            writer.write(ka_bytes)
                            await writer.drain()
                    except Exception:
                        break

            ping_task = asyncio.create_task(info_keepalive())

            while True:
                try:
                    data = await asyncio.wait_for(reader.read(8192), timeout=1.0)
                except asyncio.TimeoutError:
                    continue

                if not data:
                    raise ConnectionError("connection closed")
        except asyncio.CancelledError:
            if ping_task:
                ping_task.cancel()
            await safe_close_writer(writer)
            raise
        except Exception:
            if ping_task:
                ping_task.cancel()
            await safe_close_writer(writer)
            reconnects += 1
            if reconnects > max_reconnects:
                await asyncio.sleep(3)
                reconnects = 0
            else:
                await asyncio.sleep(1)


async def refresh_account_profile(account_data: Dict):
    try:
        if not account_data:
            return

        uid = account_data.get('account_id')
        if not uid:
            return

        info = await fetch_external_info(str(uid))
        if not info:
            return

        basic = info.get('basicinfo', {}) or info.get('basicInfo', {}) or {}

        level = int(basic.get('level', 0) or 0)
        exp = int(basic.get('exp', 0) or 0)
        nickname = basic.get('nickname', '') or ''
        region = basic.get('region', '') or ''
        likes = int(basic.get('liked', 0) or 0)

        if level <= 0:
            level = 1

        account_data['level'] = level
        account_data['exp'] = exp
        if nickname:
            account_data['nickname'] = nickname
        if region:
            account_data['region'] = region
        account_data['likes'] = likes

        try:
            uid_str = str(account_data.get('account_id'))
            bot_state.update_exp(uid_str, exp, level)
            if uid_str in bot_state.accounts:
                bot_state.accounts[uid_str]['likes'] = likes
                if nickname:
                    bot_state.accounts[uid_str]['nickname'] = nickname
        except Exception:
            pass
    except Exception:
        pass


async def process_account_uid_pass(uid: str, password: str) -> Optional[Dict]:
    log(f"[*] logging in uid: {uid}")

    try:
        async with _LOGIN_SEMAPHORE:
            verconfig_res = await version_config()
            if verconfig_res is None:
                return None
            release_version, client_version, server_url = verconfig_res

            tokengrant_response = await get_access_token(uid, password)
            if tokengrant_response is None:
                log(f"[-] oauth failed for uid {uid}")
                return None
            open_id, access_token, platform = tokengrant_response

            device_info = get_device_for_account(uid)

            login_payload_data = await build_majorlogin_payload(open_id, access_token, platform, client_version, device_info)
            if login_payload_data is None:
                return None

            majorlogin_response = await send_majorlogin(login_payload_data, release_version, server_url)
            if majorlogin_response is None:
                log(f"[-] majorlogin failed for {uid}")
                return None

            getlogin_result = await send_getlogin(
                login_payload_data,
                majorlogin_response.url,
                majorlogin_response.token,
                release_version
            )

            if getlogin_result is None:
                log(f"[-] getlogindata failed for {uid}")
                return None

            res_proto, dict_res = getlogin_result

        acc_id = str(majorlogin_response.account_id)

        if not is_valid_account_id(acc_id):
            log(f"[-] invalid account_id '{acc_id}' for uid {uid} -> retry login")
            for retry in range(5):
                await asyncio.sleep(2)
                try:
                    tokengrant_response = await get_access_token(uid, password)
                    if tokengrant_response is None:
                        continue
                    open_id, access_token, platform = tokengrant_response
                    device_info = get_device_for_account(uid)
                    login_payload_data = await build_majorlogin_payload(
                        open_id, access_token, platform, client_version, device_info
                    )
                    if login_payload_data is None:
                        continue
                    majorlogin_response = await send_majorlogin(
                        login_payload_data, release_version, server_url
                    )
                    if majorlogin_response is None:
                        continue
                    new_acc_id = str(majorlogin_response.account_id)
                    if is_valid_account_id(new_acc_id):
                        acc_id = new_acc_id
                        log(f"[+] retry ok | uid {acc_id}")
                        break
                except Exception as e:
                    log(f"[-] retry {retry+1} error: {e}")
            else:
                log(f"[-] login failed after 5 retries for uid {uid}")
                return None

        info = await fetch_external_info(acc_id)
        if info:
            basic = info.get('basicinfo', {}) or info.get('basicInfo', {}) or {}
            level = int(basic.get('level', 0) or 1)
            exp = int(basic.get('exp', 0) or 0)
            nickname = basic.get('nickname', '') or f"player_{acc_id}"
            region = basic.get('region', '') or "me"
            likes = int(basic.get('liked', 0) or 0)
        else:
            level = 0
            try:
                level = int(get_proto_field(dict_res, 6, 0) or 0)
            except Exception:
                level = 0
            if level <= 0:
                try:
                    level = int(get_proto_field(dict_res, 5, 0) or 0)
                except Exception:
                    level = 0
            if level <= 0:
                level = 1
            exp = 0
            try:
                exp = int(get_proto_field(dict_res, 7, 0) or 0)
            except Exception:
                exp = 0
            nickname = get_proto_field(dict_res, 4, f"player_{acc_id}")
            region = majorlogin_response.region or get_proto_field(dict_res, 3, "me")
            likes = 0

        if exp < 0:
            exp = 0

        func_addr = res_proto.functional_addrs
        info_addr = res_proto.informational_addrs

        if not isinstance(func_addr, str) or not func_addr or ":" not in func_addr:
            func_addr = None
        if not isinstance(info_addr, str) or not info_addr or ":" not in info_addr:
            info_addr = None

        key_val = majorlogin_response.aes_ak
        iv_val = majorlogin_response.iv_i

        if not isinstance(key_val, (bytes, bytearray)) or len(key_val) < 16:
            key_val = AES_KEY
        if not isinstance(iv_val, (bytes, bytearray)) or len(iv_val) < 16:
            iv_val = AES_IV

        account_data = {
            'account_id': majorlogin_response.account_id,
            'nickname': nickname,
            'region': region,
            'level': level,
            'exp': exp,
            'likes': likes,
            'open_id': open_id,
            'access_token': access_token,
            'platform': str(platform),
            'token': majorlogin_response.token,
            'server_time': majorlogin_response.server_time,
            'aes_ak': key_val,
            'iv_i': iv_val,
            'functional_addrs': func_addr,
            'informational_addrs': info_addr,
            'release_version': release_version,
            'client_version': client_version,
            'server_url': majorlogin_response.url,
            'login_payload_data': login_payload_data,
            'auth_type': 'guest',
            'auth_uid': uid,
            'auth_password': password
        }
        log(f"[+] login ok | uid {acc_id} | {nickname} | lvl {level}")
        return account_data
    except Exception as e:
        log(f"[-] process_account_uid_pass error: {e}")
        return None


async def process_account_token(access_token: str) -> Optional[Dict]:
    log("[*] logging in with access token")

    try:
        async with _LOGIN_SEMAPHORE:
            verconfig_res = await version_config()
            if verconfig_res is None:
                return None
            release_version, client_version, server_url = verconfig_res

            url = f"https://100067.connect.garena.com/oauth/token/inspect?token={access_token}"
            hdrs = {
                "accept-encoding": "gzip, deflate, br",
                "connection": "close",
                "content-type": "application/x-www-form-urlencoded",
                "host": "100067.connect.garena.com",
                "user-agent": "garenamsdk/4.0.19p4(g011a ;android 9;en;us;)"
            }
            resp = await client.get(url, headers=hdrs, timeout=10.0)
            if resp.status_code != 200:
                return None
            data = resp.json()

            if 'error' in data:
                return None

            open_id = data.get('open_id')
            platform = data.get('platform', 4)

            if not open_id:
                return None

            device_info = get_device_for_account(open_id)

            login_payload_data = await build_majorlogin_payload(open_id, access_token, str(platform), client_version, device_info)
            if not login_payload_data:
                return None

            majorlogin_response = await send_majorlogin(login_payload_data, release_version, server_url)
            if majorlogin_response is None:
                return None

            getlogin_result = await send_getlogin(
                login_payload_data,
                majorlogin_response.url,
                majorlogin_response.token,
                release_version
            )
            if getlogin_result is None:
                return None

            res_proto, dict_res = getlogin_result

        acc_id = str(majorlogin_response.account_id)

        if not is_valid_account_id(acc_id):
            log(f"[-] invalid account_id '{acc_id}' from token -> retry")
            for retry in range(5):
                await asyncio.sleep(2)
                try:
                    login_payload_data = await build_majorlogin_payload(
                        open_id, access_token, str(platform), client_version, device_info
                    )
                    if login_payload_data is None:
                        continue
                    majorlogin_response = await send_majorlogin(
                        login_payload_data, release_version, server_url
                    )
                    if majorlogin_response is None:
                        continue
                    new_acc_id = str(majorlogin_response.account_id)
                    if is_valid_account_id(new_acc_id):
                        acc_id = new_acc_id
                        log(f"[+] retry ok | uid {acc_id}")
                        break
                except Exception as e:
                    log(f"[-] retry {retry+1} error: {e}")
            else:
                log(f"[-] token login failed after 5 retries")
                return None

        info = await fetch_external_info(acc_id)
        if info:
            basic = info.get('basicinfo', {}) or info.get('basicInfo', {}) or {}
            level = int(basic.get('level', 0) or 1)
            exp = int(basic.get('exp', 0) or 0)
            nickname = basic.get('nickname', '') or f"player_{acc_id}"
            region = basic.get('region', '') or "me"
            likes = int(basic.get('liked', 0) or 0)
        else:
            level = 1
            exp = 0
            nickname = f"player_{acc_id}"
            region = "me"
            likes = 0

        account_data = {
            'account_id': majorlogin_response.account_id,
            'nickname': nickname,
            'region': region,
            'level': level,
            'exp': exp,
            'likes': likes,
            'open_id': open_id,
            'access_token': access_token,
            'platform': str(platform),
            'token': majorlogin_response.token,
            'server_time': majorlogin_response.server_time,
            'aes_ak': majorlogin_response.aes_ak,
            'iv_i': majorlogin_response.iv_i,
            'functional_addrs': get_proto_field(dict_res, 14),
            'informational_addrs': get_proto_field(dict_res, 32),
            'release_version': release_version,
            'client_version': client_version,
            'server_url': majorlogin_response.url,
            'login_payload_data': login_payload_data,
            'auth_type': 'token',
            'auth_token': access_token
        }
        log(f"[+] login ok (token) | uid {acc_id} | {nickname} | lvl {level}")
        return account_data
    except Exception as e:
        log(f"[-] process_account_token error: {e}")
        return None


async def run_account_worker(account_data: Dict, label: str):
    acc_id = str(account_data['account_id']).strip()

    if not is_valid_account_id(acc_id):
        log(f"[!] invalid account_id '{acc_id}' for {label} -> refusing to start")
        bot_state.update_status(acc_id, "error")
        return

    informational_task = None
    exp_task = None
    functional_task = None
    try:
        reg = account_data.get('region', 'me')
        func_addr = account_data.get('functional_addrs')
        info_addr = account_data.get('informational_addrs')

        if not func_addr or not isinstance(func_addr, str) or ":" not in func_addr:
            log(f"[!] no functional_addrs for {acc_id} - worker idle")
            bot_state.update_status(acc_id, "error")
            while True:
                await asyncio.sleep(60)
            return

        tcp_packet_online = await build_tcp_startup_packet(
            account_data['account_id'],
            account_data['token'],
            account_data['server_time'],
            account_data['aes_ak'],
            account_data['iv_i'],
            region=reg,
            typ='online'
        )

        tcp_packet_chat = await build_tcp_startup_packet(
            account_data['account_id'],
            account_data['token'],
            account_data['server_time'],
            account_data['aes_ak'],
            account_data['iv_i'],
            region=reg,
            typ='chat'
        )

        if info_addr and isinstance(info_addr, str) and ":" in info_addr:
            informational_task = asyncio.create_task(
                informational(
                    info_addr,
                    tcp_packet_chat,
                    account_data['aes_ak'],
                    account_data['iv_i'],
                    region=reg
                )
            )

        async def exp_refresher():
            while True:
                await asyncio.sleep(60 + random.uniform(-10.0, 10.0))
                try:
                    await refresh_account_profile(account_data)
                except Exception:
                    pass

        exp_task = asyncio.create_task(exp_refresher())

        functional_task = asyncio.create_task(
            functional_lone_wolf(
                func_addr,
                tcp_packet_online,
                account_data['region'],
                account_data['client_version'],
                account_data['aes_ak'],
                account_data['iv_i'],
                account_id=acc_id,
                account_data=account_data
            )
        )

        await functional_task

    except asyncio.CancelledError:
        raise
    except Exception as e:
        log(f"run_account_worker error for {label}: {e}")
    finally:
        for t in (informational_task, exp_task, functional_task):
            if t and not t.done():
                t.cancel()
        for t in (informational_task, exp_task, functional_task):
            if t:
                try:
                    await t
                except (asyncio.CancelledError, Exception):
                    pass
        try:
            bot_state.update_status(acc_id, "offline")
        except Exception:
            pass


async def cb_login_only(payload: Dict):
    try:
        if payload.get("type") == "token":
            account_data = await process_account_token(payload["token"])
        else:
            account_data = await process_account_uid_pass(payload["uid"], payload["password"])

        if not account_data:
            raise RuntimeError("login failed")

        uid = str(account_data["account_id"]).strip()

        if not is_valid_account_id(uid):
            raise RuntimeError(f"invalid account_id returned: {uid}")

        ok = bot_state.register_account(
            uid,
            account_data.get("nickname", f"player_{uid}"),
            account_data.get("region", "me"),
            account_data.get("level", 1),
            account_data.get("exp", 0),
            account_data.get("likes", 0),
        )
        if not ok:
            raise RuntimeError(f"register_account rejected uid: {uid}")

        bot_state.account_credentials[uid] = account_data
        bot_state.accounts[uid]["status"] = "ready"
        log(f"[api] registered uid {uid} - ready")
        return uid
    except Exception as e:
        log(f"[api] login_only error: {e}")
        raise


async def cb_relogin(old_uid: str, auth_uid: str, auth_password: str):
    try:
        log(f"[relogin] invalid uid '{old_uid}' -> re-login for auth_uid={auth_uid}")

        try:
            bot_state.accounts.pop(old_uid, None)
            bot_state.account_credentials.pop(old_uid, None)
            bot_state.exp_targets_ref.pop(old_uid, None)
            bot_state.start_exp_ref.pop(old_uid, None)
            bot_state.session_matches_ref.pop(old_uid, None)
            bot_state.account_start_ref.pop(old_uid, None)
            bot_state.exp_limit_reached_ref.discard(old_uid)
            t = bot_state.account_workers.pop(old_uid, None)
            if t and not t.done():
                t.cancel()
        except Exception:
            pass

        new_data = None
        for attempt in range(5):
            try:
                new_data = await process_account_uid_pass(auth_uid, auth_password)
                if new_data:
                    new_uid = str(new_data.get("account_id", "")).strip()
                    if is_valid_account_id(new_uid):
                        log(f"[relogin] ok -> new uid = {new_uid}")
                        break
                    log(f"[relogin] attempt {attempt+1}: invalid uid '{new_uid}' -> retry")
                    new_data = None
            except Exception as e:
                log(f"[relogin] attempt {attempt+1} error: {e}")
            await asyncio.sleep(3)

        if not new_data:
            log(f"[relogin] failed after 5 attempts for {auth_uid}")
            return None

        new_uid = str(new_data.get("account_id", "")).strip()

        ok = bot_state.register_account(
            new_uid,
            new_data.get("nickname", f"player_{new_uid}"),
            new_data.get("region", "me"),
            new_data.get("level", 1),
            new_data.get("exp", 0),
            new_data.get("likes", 0),
        )
        if not ok:
            log(f"[relogin] register_account rejected {new_uid}")
            return None

        bot_state.account_credentials[new_uid] = new_data
        bot_state.accounts[new_uid]["status"] = "ready"
        log(f"[relogin] registered {new_uid} - ready")
        return new_uid

    except Exception as e:
        log(f"[relogin] error: {e}")
        return None


async def cb_set_target(uid: str, target: int):
    try:
        uid = str(uid)
        bot_state.exp_targets_ref[uid] = int(target)
        if uid in bot_state.accounts:
            bot_state.accounts[uid]["target"] = int(target)
        log(f"[api] target set for {uid}: {target}")
    except Exception as e:
        log(f"[api] set_target error: {e}")
        raise


async def cb_start_account(uid: str):
    try:
        uid = str(uid)
        if not is_valid_account_id(uid):
            raise RuntimeError(f"invalid uid: {uid}")
        creds = bot_state.account_credentials.get(uid)
        if not creds:
            raise RuntimeError(f"no credentials for {uid}")

        if uid in bot_state.account_workers:
            t = bot_state.account_workers[uid]
            if t and not t.done():
                log(f"[api] {uid} already running")
                return

        bot_state.account_start_ref[uid] = time.time()
        bot_state.start_exp_ref[uid] = int(creds.get("exp", 0))
        bot_state.session_matches_ref[uid] = 0
        bot_state.exp_limit_reached_ref.discard(uid)

        task = asyncio.create_task(run_account_worker(creds, uid))
        bot_state.account_workers[uid] = task
        bot_state.update_status(uid, "running")
        log(f"[api] started worker for {uid}")

        def _done(t, _uid=uid):
            try:
                bot_state.update_status(_uid, "offline")
                bot_state.account_workers.pop(_uid, None)
            except Exception:
                pass

        task.add_done_callback(_done)
    except Exception as e:
        log(f"[api] start_account error: {e}")
        raise


async def cb_stop_account(uid: str):
    try:
        uid = str(uid)
        t = bot_state.account_workers.get(uid)
        if t and not t.done():
            t.cancel()
            try:
                await t
            except (asyncio.CancelledError, Exception):
                pass
        bot_state.account_workers.pop(uid, None)
        bot_state.update_status(uid, "offline")
        log(f"[api] stopped worker for {uid}")
    except Exception as e:
        log(f"[api] stop_account error: {e}")
        raise


async def cb_halt_account(uid: str):
    await cb_stop_account(uid)


async def cb_delete_account(uid: str):
    try:
        uid = str(uid)
        await cb_stop_account(uid)
        bot_state.accounts.pop(uid, None)
        bot_state.account_credentials.pop(uid, None)
        bot_state.exp_targets_ref.pop(uid, None)
        bot_state.start_exp_ref.pop(uid, None)
        bot_state.session_matches_ref.pop(uid, None)
        bot_state.account_start_ref.pop(uid, None)
        bot_state.exp_limit_reached_ref.discard(uid)
        log(f"[api] deleted {uid}")
    except Exception as e:
        log(f"[api] delete_account error: {e}")
        raise


async def cb_add_friend(uid: str, target: str):
    try:
        uid = str(uid)
        target = str(target)
        if not _HAS_ADDFRIEND:
            return {"ok": False, "error": "reqaddbot not available"}
        creds = bot_state.account_credentials.get(uid)
        if not creds:
            return {"ok": False, "error": f"no credentials for {uid}"}
        if creds.get("auth_type") != "guest":
            return {"ok": False, "error": "only uid+password accounts supported"}
        auth_uid = str(creds.get("auth_uid", ""))
        auth_password = str(creds.get("auth_password", ""))
        if not auth_uid or not auth_password:
            return {"ok": False, "error": "missing stored uid/password"}
        res = await send_friend_request_async(auth_uid, auth_password, target)
        return res if res else {"ok": False, "error": "no response"}
    except Exception as e:
        return {"ok": False, "error": str(e)}


def _make_random_name(prefix):
    if not prefix:
        prefix = "bot"
    prefix = prefix[:7]
    suffix = "".join(random.choices(_string.ascii_letters, k=5))
    return f"{prefix}-{suffix}"


def _make_random_pw():
    return "".join(random.choices(_string.ascii_letters + _string.digits, k=15))


async def cb_generate_accounts(name: str, region: str, count: int, threads: int):
    if not _HAS_GEN:
        return []
    try:
        generated = []
        loop = asyncio.get_event_loop()
        for _ in range(count):
            n = _make_random_name(name) if name else _make_random_name("")
            try:
                acc = await loop.run_in_executor(
                    None,
                    _gen_module.create_account,
                    region, n, 0
                )
            except Exception:
                acc = None
            if not acc:
                continue
            generated.append(acc)
            try:
                bot_state.generated_accounts.append({
                    "uid": str(acc.get("uid", "")),
                    "account_id": str(acc.get("account_id", "")),
                    "name": acc.get("name", n),
                    "password": acc.get("password", ""),
                    "region": acc.get("region", region),
                    "date_created": acc.get("date_created", ""),
                })
            except Exception:
                pass
        return generated
    except Exception as e:
        log(f"[gen] error: {e}")
        return []


async def cb_gen_start(uid: str):
    uid = str(uid)
    try:
        found = None
        for a in (getattr(bot_state, "generated_accounts", []) or []):
            if str(a.get("uid")) == uid:
                found = a
                break
        if not found:
            raise RuntimeError(f"no generated account with uid {uid}")
        credentials = await process_account_uid_pass(str(found["uid"]), str(found["password"]))
        if not credentials:
            raise RuntimeError("login failed")
        uid_real = str(credentials["account_id"])
        if not is_valid_account_id(uid_real):
            raise RuntimeError(f"invalid account_id: {uid_real}")
        bot_state.register_account(
            uid_real,
            credentials.get("nickname", f"player_{uid_real}"),
            credentials.get("region", "me"),
            credentials.get("level", 1),
            credentials.get("exp", 0),
            credentials.get("likes", 0),
        )
        bot_state.account_credentials[uid_real] = credentials
        bot_state.accounts[uid_real]["status"] = "ready"
        bot_state.account_start_ref[uid_real] = time.time()
        bot_state.start_exp_ref[uid_real] = int(credentials.get("exp", 0))
        bot_state.session_matches_ref[uid_real] = 0
        bot_state.exp_limit_reached_ref.discard(uid_real)

        task = asyncio.create_task(run_account_worker(credentials, uid_real))
        bot_state.account_workers[uid_real] = task
        bot_state.update_status(uid_real, "running")

        def _done(t, _uid=uid_real):
            try:
                bot_state.update_status(_uid, "offline")
                bot_state.account_workers.pop(_uid, None)
            except Exception:
                pass
        task.add_done_callback(_done)
        log(f"[gen] started {uid_real}")
    except Exception as e:
        log(f"[gen] start error: {e}")
        raise


async def cb_gen_import(uid: str):
    uid = str(uid)
    try:
        found = None
        for a in (getattr(bot_state, "generated_accounts", []) or []):
            if str(a.get("uid")) == uid:
                found = a
                break
        if not found:
            raise RuntimeError(f"no generated account with uid {uid}")
        credentials = await process_account_uid_pass(str(found["uid"]), str(found["password"]))
        if not credentials:
            raise RuntimeError("login failed")
        uid_real = str(credentials["account_id"])
        if not is_valid_account_id(uid_real):
            raise RuntimeError(f"invalid account_id: {uid_real}")
        bot_state.register_account(
            uid_real,
            credentials.get("nickname", f"player_{uid_real}"),
            credentials.get("region", "me"),
            credentials.get("level", 1),
            credentials.get("exp", 0),
            credentials.get("likes", 0),
        )
        bot_state.account_credentials[uid_real] = credentials
        bot_state.accounts[uid_real]["status"] = "ready"
        log(f"[gen] imported {uid_real}")
    except Exception as e:
        log(f"[gen] import error: {e}")
        raise


async def cb_refresh_profile(account_data: Dict):
    try:
        await refresh_account_profile(account_data)
    except Exception:
        pass


async def _auto_cycle_one(auth_uid: str, auth_pass: str, target: int):
    login_handler = bot_state.refresh_callbacks.get("on_account_login_only")
    starter = bot_state.refresh_callbacks.get("on_start_account")
    stopper = bot_state.refresh_callbacks.get("on_stop_account")
    setter = bot_state.refresh_callbacks.get("on_set_target")
    refresher = bot_state.refresh_callbacks.get("on_refresh_profile")

    round_num = 0
    real_uid = None

    while True:
        round_num += 1

        try:
            result = await login_handler({"type": "guest", "uid": auth_uid, "password": auth_pass})
            if not result:
                bot_state.log(f"[cycle] login returned empty for {auth_uid}")
                await asyncio.sleep(15)
                continue
            real_uid = str(result).strip()
            if not real_uid:
                bot_state.log(f"[cycle] login returned empty uid for {auth_uid}")
                await asyncio.sleep(15)
                continue
            bot_state.log(f"[cycle] login ok -> real_uid={real_uid}")
        except Exception as e:
            bot_state.log(f"[cycle] login fail {auth_uid}: {e}")
            await asyncio.sleep(15)
            continue

        if setter:
            try:
                await setter(real_uid, target)
            except Exception:
                pass

        bot_state.auto_cycle_phase[real_uid] = "br"
        if starter:
            try:
                await starter(real_uid)
            except Exception as e:
                bot_state.log(f"[cycle] start fail {real_uid}: {e}")
                await asyncio.sleep(10)
                continue

        bot_state.log(f"[cycle] {real_uid} round {round_num} - br phase")
        await asyncio.sleep(BR_PHASE_SECONDS)

        if stopper:
            try:
                await stopper(real_uid)
            except Exception:
                pass

        bot_state.auto_cycle_phase[real_uid] = "cooldown"
        bot_state.log(f"[cycle] {real_uid} cooldown")
        await asyncio.sleep(COOLDOWN_SECONDS)

        try:
            creds = bot_state.account_credentials.get(real_uid)
            if creds and refresher:
                await refresher(creds)
        except Exception:
            pass

        try:
            result = await login_handler({"type": "guest", "uid": auth_uid, "password": auth_pass})
            if not result:
                bot_state.log(f"[cycle] re-login empty for {auth_uid}")
                await asyncio.sleep(15)
                continue
            real_uid = str(result).strip()
            if not real_uid:
                bot_state.log(f"[cycle] re-login empty uid")
                await asyncio.sleep(15)
                continue
            bot_state.log(f"[cycle] re-login ok -> {real_uid}")
        except Exception as e:
            bot_state.log(f"[cycle] re-login fail: {e}")
            await asyncio.sleep(15)
            continue

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

        if setter:
            try:
                await setter(real_uid, target)
            except Exception:
                pass

        bot_state.auto_cycle_phase[real_uid] = "lw"
        if starter:
            try:
                await starter(real_uid)
            except Exception as e:
                bot_state.log(f"[cycle] lw start fail {real_uid}: {e}")

        bot_state.log(f"[cycle] {real_uid} round {round_num} - lw phase (continuous)")

        while True:
            await asyncio.sleep(30)

            if real_uid in bot_state.exp_limit_reached_ref:
                bot_state.log(f"[cycle] {real_uid} reached exp target")
                break

            w = bot_state.account_workers.get(real_uid)
            if not w or w.done():
                bot_state.log(f"[cycle] {real_uid} worker stopped")
                break

            if asyncio.current_task().cancelled():
                break

        if real_uid in bot_state.exp_limit_reached_ref:
            bot_state.log(f"[cycle] {real_uid} completed - stopping cycle")
            if stopper:
                try:
                    await stopper(real_uid)
                except Exception:
                    pass
            bot_state.auto_cycle_phase[real_uid] = "completed"
            return

        if stopper:
            try:
                await stopper(real_uid)
            except Exception:
                pass

        bot_state.auto_cycle_phase[real_uid] = "restart"
        await asyncio.sleep(5)


async def main():
    bot_state.bind_loop()

    bot_state.refresh_callbacks["on_account_login_only"] = cb_login_only
    bot_state.refresh_callbacks["on_relogin"] = cb_relogin
    bot_state.refresh_callbacks["on_set_target"] = cb_set_target
    bot_state.refresh_callbacks["on_start_account"] = cb_start_account
    bot_state.refresh_callbacks["on_stop_account"] = cb_stop_account
    bot_state.refresh_callbacks["on_halt_account"] = cb_halt_account
    bot_state.refresh_callbacks["on_delete_account"] = cb_delete_account
    bot_state.refresh_callbacks["on_add_friend"] = cb_add_friend
    bot_state.refresh_callbacks["on_generate_accounts"] = cb_generate_accounts
    bot_state.refresh_callbacks["on_gen_start"] = cb_gen_start
    bot_state.refresh_callbacks["on_gen_import"] = cb_gen_import
    bot_state.refresh_callbacks["on_refresh_profile"] = cb_refresh_profile

    runner = await start_api_server(host="0.0.0.0", port=WEB_PORT)
    log(f"[api] yazan level ready on port {WEB_PORT}")

    try:
        while True:
            await asyncio.sleep(3600)
    except asyncio.CancelledError:
        pass
    finally:
        try:
            await runner.cleanup()
        except Exception:
            pass


if __name__ == "__main__":
    import traceback
    try:
        if sys.platform == "win32":
            try:
                asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())
            except Exception:
                pass
        print(">>> starting yazan level...")
        asyncio.run(main())
    except KeyboardInterrupt:
        print("\n>>> stopped by user.")
    except Exception:
        print("\n" + "=" * 60)
        print("[fatal error]")
        print("=" * 60)
        traceback.print_exc()
    finally:
        try:
            input("\n>>> press enter to exit...")
        except Exception:
            pass
