"""
ربات دستیار هوشمند — «هوشی» 🧠
+ پنل مدیریت گروه حرفه‌ای
+ حذف خودکار فحش + اخطار + بن خودکار
+ لیست بن دکمه‌ای (بدون /unban)
"""

import email.utils
import os
import re
import json
import random
import asyncio
import logging
import tempfile
import time
from pathlib import Path
from collections import OrderedDict, deque
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo
from typing import Optional

import httpx
import edge_tts
from groq import Groq
from telegram import (
    Update, ReplyKeyboardMarkup, KeyboardButton,
    InlineKeyboardMarkup, InlineKeyboardButton, BotCommand, ChatPermissions,
    BotCommandScopeDefault, BotCommandScopeChat
)
from telegram.ext import (
    Application, CommandHandler, MessageHandler,
    CallbackQueryHandler, ContextTypes, filters
)
from telegram.constants import ChatAction, ChatType

# ═══════════════════════════════════════════════════════════════
# پیکربندی
# ═══════════════════════════════════════════════════════════════

# مقادیر محرمانه را از متغیرهای محیطی بخوانید؛ آن‌ها را داخل کد ننویسید.
# قبل از اجرا، TELEGRAM_BOT_TOKEN و GROQ_API_KEY را تنظیم کنید.
BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
GROQ_KEY = os.getenv("GROQ_API_KEY", "").strip()
ADMIN_ID = int(os.getenv("BOT_ADMIN_ID", "8116162145"))

if not BOT_TOKEN:
    raise RuntimeError("متغیر محیطی TELEGRAM_BOT_TOKEN تنظیم نشده است.")
if not GROQ_KEY:
    raise RuntimeError("متغیر محیطی GROQ_API_KEY تنظیم نشده است.")

BOT_NAME = "هوشی"
BOT_USERNAME = "YourBotUsername"

logging.basicConfig(
    format="%(asctime)s | %(levelname)-8s | %(name)s | %(message)s",
    level=logging.INFO,
)
log = logging.getLogger("hooshi-bot")

ai = Groq(
    api_key=GROQ_KEY,
    http_client=httpx.Client(
        http2=False,
        headers={"User-Agent": "curl/8.23.0", "Accept": "*/*"},
        timeout=30.0,
        trust_env=True,
    ),
)

DATA_FILE = Path.home() / "bot_data.json"

# ⚡ تنظیمات
AI_MODEL = "openai/gpt-oss-20b"
MAX_TOKENS = 300
TTS_RATE = "+10%"
TTS_VOICE = "fa-IR-FaridNeural"

MAX_HISTORY_ITEMS = 15
HISTORY_TTL_MINUTES = 120
MAX_BUTTONS = 30
MAX_BUTTON_ITEMS = 20
MAX_VOICE_BYTES = 20 * 1024 * 1024

DEFAULT_MAX_WARNINGS = 3
try:
    BOT_TIMEZONE = ZoneInfo("Asia/Tehran")
except Exception:
    # در بعضی نصب‌های Termux دیتابیس منطقه‌های زمانی موجود نیست.
    # ایران در حال حاضر از UTC+03:30 استفاده می‌کند.
    BOT_TIMEZONE = timezone(timedelta(hours=3, minutes=30))


PERSIAN_WEEKDAYS = {
    "شنبه": 0, "یکشنبه": 1, "يکشنبه": 1, "دوشنبه": 2,
    "سهشنبه": 3, "سه شنبه": 3, "چهارشنبه": 4, "پنجشنبه": 5, "جمعه": 6,
}


def normalize_persian_digits(value: str) -> str:
    table = str.maketrans("۰۱۲۳۴۵۶۷۸۹٠١٢٣٤٥٦٧٨٩", "01234567890123456789")
    return value.translate(table).replace("：", ":").replace("\u200c", "").strip()


def jalali_to_gregorian(jy: int, jm: int, jd: int):
    """تبدیل تاریخ شمسی به میلادی بدون نیاز به کتابخانهٔ اضافی."""
    if not (1 <= jm <= 12 and 1 <= jd <= (31 if jm <= 6 else 30)):
        raise ValueError("تاریخ شمسی نامعتبر است")
    jy += 1595
    days = -355668 + 365 * jy + (jy // 33) * 8 + ((jy % 33 + 3) // 4) + jd
    days += (jm - 1) * 31 if jm <= 7 else (jm - 7) * 30 + 186
    gy = 400 * (days // 146097)
    days %= 146097
    if days > 36524:
        gy += 100 * ((days - 1) // 36524)
        days = (days - 1) % 36524
        if days >= 365:
            days += 1
    gy += 4 * (days // 1461)
    days %= 1461
    if days > 365:
        gy += (days - 1) // 365
        days = (days - 1) % 365
    gd = days + 1
    leap = (gy % 4 == 0 and gy % 100 != 0) or gy % 400 == 0
    month_days = [31, 29 if leap else 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
    gm = 1
    while gm <= 12 and gd > month_days[gm - 1]:
        gd -= month_days[gm - 1]
        gm += 1
    return gy, gm, gd


def gregorian_to_jalali(gy: int, gm: int, gd: int):
    g_month_days = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
    gy2 = gy + 1 if gm > 2 else gy
    days = 355666 + 365 * gy + (gy2 + 3) // 4 - (gy2 + 99) // 100 + (gy2 + 399) // 400
    days += g_month_days[gm - 1] + gd
    if gm > 2 and ((gy % 4 == 0 and gy % 100 != 0) or gy % 400 == 0):
        days += 1
    jy = -1595 + 33 * (days // 12053)
    days %= 12053
    jy += 4 * (days // 1461)
    days %= 1461
    if days > 365:
        jy += (days - 1) // 365
        days = (days - 1) % 365
    if days < 186:
        jm = 1 + days // 31
        jd = 1 + days % 31
    else:
        jm = 7 + (days - 186) // 30
        jd = 1 + (days - 186) % 30
    return jy, jm, jd


def parse_group_unlock_target(user_text: str, now: datetime) -> datetime:
    """ورودی ساعت، امروز/فردا، روز هفته یا تاریخ شمسی کامل را به زمان ایران تبدیل می‌کند."""
    value = normalize_persian_digits(user_text)
    value = value.replace("،", " ").replace("ساعت", " ").replace("تاریخ", " ")
    time_match = re.search(r"(?<!\d)([01]?\d|2[0-3]):([0-5]\d)(?!\d)", value)
    if not time_match:
        raise ValueError("ساعت را به شکل 10:34 وارد کن.")
    hour, minute = map(int, time_match.groups())
    remainder = (value[:time_match.start()] + " " + value[time_match.end():]).strip()
    remainder = re.sub(r"[\-،,]", " ", remainder)
    remainder = re.sub(r"\s+", " ", remainder).strip()

    date_match = re.search(r"(?<!\d)(\d{4})[/-](\d{1,2})[/-](\d{1,2})(?!\d)", remainder)
    if date_match:
        jy, jm, jd = map(int, date_match.groups())
        gy, gm, gd = jalali_to_gregorian(jy, jm, jd)
        if gregorian_to_jalali(gy, gm, gd) != (jy, jm, jd):
            raise ValueError("تاریخ شمسی معتبر نیست؛ روز و ماه را بررسی کن.")
        try:
            target_date = datetime(gy, gm, gd, tzinfo=now.tzinfo).date()
        except ValueError as exc:
            raise ValueError("تاریخ واردشده معتبر نیست.") from exc
        target = datetime.combine(target_date, datetime.min.time(), tzinfo=now.tzinfo).replace(hour=hour, minute=minute)
        if target <= now:
            raise ValueError("این تاریخ و ساعت گذشته است؛ تاریخ یا ساعت آینده را وارد کن.")
        return target

    low = remainder.replace(" ", "")
    # «امشب 10:42» یعنی 22:42؛ اگر کاربر 22:42 نوشته باشد همان ساعت حفظ می‌شود.
    is_tonight = "امشب" in low or "شب" in low
    if is_tonight and hour < 12:
        hour += 12

    if "امشب" in low:
        target = now.replace(hour=hour, minute=minute, second=0, microsecond=0)
        if target <= now:
            raise ValueError("ساعت امشب گذشته است؛ برای زمان آینده تاریخ یا ساعت دیگری وارد کن.")
        return target

    if "امروز" in low:
        target = now.replace(hour=hour, minute=minute, second=0, microsecond=0)
        if target <= now:
            raise ValueError("این ساعت امروز گذشته است؛ «فردا 10:34» یا تاریخ کامل را وارد کن.")
        return target
    if "فردا" in low:
        return (now + timedelta(days=1)).replace(hour=hour, minute=minute, second=0, microsecond=0)

    weekday = None
    # نام‌های بلندتر اول بررسی شوند تا مثلاً «دوشنبه» به اشتباه «شنبه» تشخیص داده نشود.
    for name, index in sorted(PERSIAN_WEEKDAYS.items(), key=lambda item: len(item[0].replace(" ", "")), reverse=True):
        if name.replace(" ", "") in low:
            weekday = index
            break
    if weekday is not None:
        today_index = (now.weekday() + 2) % 7  # شنبه=۰ ... جمعه=۶
        delta = (weekday - today_index) % 7
        target = (now + timedelta(days=delta)).replace(hour=hour, minute=minute, second=0, microsecond=0)
        if target <= now:
            target += timedelta(days=7)
        return target

    # فقط ساعت وارد شده: امروز اگر نگذشته باشد، وگرنه فردا.
    target = now.replace(hour=hour, minute=minute, second=0, microsecond=0)
    if target <= now:
        target += timedelta(days=1)
    return target


async def get_internet_utc_now() -> datetime:
    """ساعت UTC را از هدر Date یک پاسخ اینترنتی می‌گیرد؛ در صورت خطا ساعت دستگاه."""
    try:
        async with httpx.AsyncClient(timeout=5.0, follow_redirects=True) as client:
            response = await client.head("https://www.google.com/generate_204")
            date_header = response.headers.get("date")
            if date_header:
                parsed = email.utils.parsedate_to_datetime(date_header)
                if parsed.tzinfo is None:
                    parsed = parsed.replace(tzinfo=timezone.utc)
                return parsed.astimezone(timezone.utc)
    except Exception as exc:
        log.warning("گرفتن ساعت اینترنتی ناموفق بود؛ از ساعت دستگاه استفاده می‌شود: %r", exc)
    return datetime.now(timezone.utc)

CREATOR_STICKER = ""
CREATOR_REPLY = "ماهان، ۱۷ ساله، پسر ایرانی."

SLEEPY_REPLIES = (
    "😴 هوشی الان خوابه...",
    "💤 هوشی رفته یه چرت بزنه...",
)

GROQ_REFUSAL_PATTERNS = (
    "i'm sorry", "i cannot", "i can't",
    "cannot help", "can't help",
    "as an ai", "متأسفم", "نمی‌توانم",
)

# فهرست واژه‌ها و عبارت‌های رکیک؛ علاوه بر شکل عادی، نسخهٔ فشرده‌شده هم بررسی می‌شود
# تا فاصله‌گذاری، نیم‌فاصله و نشانه‌گذاری نتواند به‌سادگی فیلتر را دور بزند.
PROFANITY_KEYWORDS = (
    # فارسی و شکل‌های املایی رایج
    "کیر", "کص", "کسکش", "کوسکش", "کصکش", "کس کش", "کوس کش", "کص کش",
    "کون", "کونی", "کونده", "کونده", "کونکش", "کون کش", "کیرم", "کیرت", "کیرش",
    "کیرکش", "کیرخر", "کیرخور", "کصخل", "کسخل", "کصخُل", "سکس", "سیکتیر",
    "جنده", "جندگی", "جاکش", "جاکش", "گایید", "گاییده", "گاییدن", "گاییدمت",
    "گاییدم", "گاییدت", "گاینده", "گوه", "گوهخور", "دیوث", "حرومزاده", "حرامزاده",
    "مادرجنده", "مادر قهوه", "پدرسگ", "پدرسوخته", "بی ناموس", "بی‌ناموس", "بیناموس",
    "ناموس", "مادرت", "خواهرت", "تخم سگ", "تخم سگ", "عنتر", "لاشی", "هرزه",
    "پفیوز", "کثافت", "عوضی", "آشغال", "خفه شو", "دهنت", "دهنتو", "بکنمت", "بخورمت",
    "احمق", "اسکل", "اسکول", "خر", "گاو",
    # فینگلیش و انگلیسی
    "koskesh", "koskash", "koskesh", "koskes", "kosskesh", "kosekesh", "koni",
    "kir", "kیر", "koon", "kon", "jende", "jendeh", "jakesh", "gayid", "gaiid",
    "sex", "sexy", "fuck", "fucker", "fucking", "motherfucker", "mf", "shit", "bullshit",
    "bitch", "bitches", "asshole", "dick", "dickhead", "pussy", "cunt", "bastard",
    "whore", "slut", "nigga", "retard", "stfu", "wtf", "idiot", "moron", "dumbass",
    "xx",
)

PROFANITY_PATTERN = re.compile(
    r"(?<![\w])(" + "|".join(re.escape(k) for k in PROFANITY_KEYWORDS) + r")(?![\w])",
    re.IGNORECASE | re.UNICODE,
)

def normalize_profanity_text(value: str) -> str:
    value = (value or "").lower().translate(str.maketrans({"ي":"ی", "ى":"ی", "ك":"ک", "ۀ":"ه", "ة":"ه", "أ":"ا", "إ":"ا", "ؤ":"و", "ئ":"ی"}))
    # یکسان‌سازی اعداد/اعراب و حذف تمام جداکننده‌ها برای خنثی‌کردن نقطه، ستاره، @، #، $، %، &، +، _ و غیره
    value = re.sub(r"[\u064b-\u065f\u0670\u0640\u200c\u200d\ufeff]", "", value)
    value = re.sub(r"[^\w]", "", value, flags=re.UNICODE)
    return value

# ═══════════════════════════════════════════════════════════════
# حافظه
# ═══════════════════════════════════════════════════════════════

class ChatMemory:
    def __init__(self, max_users=500, ttl_minutes=HISTORY_TTL_MINUTES):
        self._data: "OrderedDict[int, tuple[datetime, list]]" = OrderedDict()
        self._ttl = timedelta(minutes=ttl_minutes)
        self._max_users = max_users

    def get(self, user_id: int) -> list:
        entry = self._data.get(user_id)
        if not entry:
            return []
        ts, history = entry
        if datetime.now() - ts > self._ttl:
            self._data.pop(user_id, None)
            return []
        return list(history)

    def set(self, user_id: int, history: list) -> None:
        self._data[user_id] = (datetime.now(), history[-MAX_HISTORY_ITEMS:])
        self._data.move_to_end(user_id)
        while len(self._data) > self._max_users:
            self._data.popitem(last=False)

    def clear(self, user_id: Optional[int] = None) -> None:
        if user_id is None:
            self._data.clear()
        else:
            self._data.pop(user_id, None)

    def count(self) -> int:
        return len(self._data)


memory = ChatMemory()
admin_states: dict[int, dict] = {}
_pending_captcha: dict[tuple[int, int], tuple[int, int]] = {}
_captcha_failures: dict[tuple[int, int], int] = {}
_captcha_message_ids: dict[tuple[int, int], int] = {}
_CAPTCHA_TIMEOUT_SECONDS = 10

# ضدفلود حافظه‌ای: پنجرهٔ زمانی و تشخیص پیام تکراری برای هر کاربر/گروه
_group_flood_windows: dict[tuple[int, int], deque] = {}
_group_recent_texts: dict[tuple[int, int], deque] = {}
_GROUP_FLOOD_WINDOW_SECONDS = 6.0
_GROUP_FLOOD_MAX_MESSAGES = 8
_GROUP_DUPLICATE_WINDOW_SECONDS = 20.0
_GROUP_DUPLICATE_MAX = 4
_GROUP_FLOOD_MUTE_SECONDS = 300
_GROUP_FLOOD_COOLDOWN: dict[tuple[int, int], float] = {}

# ═══════════════════════════════════════════════════════════════
# ذخیره‌سازی
# ═══════════════════════════════════════════════════════════════

def load_data() -> dict:
    if DATA_FILE.exists():
        try:
            d = json.loads(DATA_FILE.read_text(encoding="utf-8"))
            d.setdefault("rules", [])
            d.setdefault("buttons", [])
            d.setdefault("warnings", {})
            d.setdefault("group_warnings", {})
            d.setdefault("bans", [])
            d.setdefault("silence_until", 0)
            d.setdefault("bot_off", False)
            d.setdefault("admins", [])
            d.setdefault("groups", [])
            d.setdefault("active_groups", [])
            d.setdefault("group_settings", {})
            d.setdefault("group_bans", {})  # {chat_id: {user_id: name}}
            d.setdefault("group_history_messages", {})
            d.setdefault("group_message_counts", {})
            return d
        except (ValueError, OSError) as e:
            log.warning("خطا در خواندن دیتا: %r", e)
    return {
        "rules": [], "buttons": [],
        "warnings": {}, "group_warnings": {},
        "bans": [], "silence_until": 0,
        "bot_off": False, "admins": [],
        "groups": [], "active_groups": [],
        "group_settings": {},
        "group_bans": {},
        "group_history_messages": {},
        "group_message_counts": {},
    }


def save_data() -> None:
    tmp = DATA_FILE.with_suffix(".tmp")
    tmp.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
    tmp.replace(DATA_FILE)


data = load_data()

# ═══════════════════════════════════════════════════════════════
# امنیت / بن / مدیر
# ═══════════════════════════════════════════════════════════════

def is_banned(user_id: int) -> bool:
    return user_id in data["bans"]


def ban_user(user_id: int) -> None:
    if user_id not in data["bans"]:
        data["bans"].append(user_id)
        save_data()


def unban_user(user_id: int) -> None:
    if user_id in data["bans"]:
        data["bans"].remove(user_id)
        save_data()


def reset_warnings(user_id: int) -> None:
    if str(user_id) in data["warnings"]:
        del data["warnings"][str(user_id)]
        save_data()


def get_warnings(user_id: int) -> int:
    return int(data["warnings"].get(str(user_id), 0))


def add_warning(user_id: int) -> int:
    n = get_warnings(user_id) + 1
    data["warnings"][str(user_id)] = n
    save_data()
    return n


def contains_profanity(text: str) -> bool:
    if not text:
        return False
    normalized = normalize_profanity_text(text)
    if PROFANITY_PATTERN.search(normalized):
        return True
    # شکل فشرده، مانند «کوس کش»، «ک و س ک ش» یا واژه‌های جداشده با علائم
    compact = re.sub(r"[^\w]", "", normalized, flags=re.UNICODE)
    compact_keywords = tuple(re.sub(r"[^\w]", "", word, flags=re.UNICODE) for word in PROFANITY_KEYWORDS)
    compact_keywords += (
        "کسکش", "کوسکش", "کصکش", "کیرکش", "کیرمکس", "کونده",
        "جنده", "دیوث", "حرومزاده", "حرامزاده", "بیناموس",
        "گاییدمت", "گاییده", "گاییدن", "motherfucker", "asshole",
    )
    # حذف همه فاصله‌ها و علائم، برای شکل‌هایی مثل ک.س.ک.ش و ک س ک ش
    return any(word and word in compact for word in compact_keywords)


def is_groq_refusal(text: str) -> bool:
    if not text:
        return False
    low = text.lower().strip()
    return any(p in low for p in GROQ_REFUSAL_PATTERNS)


def is_admin_silenced() -> bool:
    return datetime.now().timestamp() < data.get("silence_until", 0)


def is_bot_off() -> bool:
    return bool(data.get("bot_off", False))


def is_primary_admin(user_id: int) -> bool:
    return user_id == ADMIN_ID


def is_any_admin(user_id: int) -> bool:
    return user_id == ADMIN_ID or user_id in data["admins"]


def add_admin(user_id: int) -> bool:
    if user_id == ADMIN_ID or user_id in data["admins"]:
        return False
    data["admins"].append(user_id)
    save_data()
    return True


def remove_admin(user_id: int) -> bool:
    if user_id in data["admins"]:
        data["admins"].remove(user_id)
        save_data()
        return True
    return False


# ─── گروه‌ها ─────────────────────────────────────────────────
def is_group_active(chat_id: int) -> bool:
    return chat_id in data["active_groups"]


def activate_group(chat_id: int) -> None:
    if chat_id not in data["active_groups"]:
        data["active_groups"].append(chat_id)
        save_data()


def deactivate_group(chat_id: int) -> None:
    if chat_id in data["active_groups"]:
        data["active_groups"].remove(chat_id)
        save_data()


# ─── تنظیمات گروه ────────────────────────────────────────────
def get_group_settings(chat_id: int) -> dict:
    key = str(chat_id)
    if key not in data["group_settings"]:
        data["group_settings"][key] = {
            "locked": False,
            "locked_until": 0,
            "silent_until": 0,
            "max_warnings": DEFAULT_MAX_WARNINGS,
            "media_locks": {"photo": False, "video": False, "voice": False, "gif": False, "document": False},
            "auto_delete_50": False,
            "hourly_delete": False,
            "welcome_enabled": True,
            "goodbye_enabled": True,
            "captcha_enabled": True,
            "welcome_template": "سلام و خوش اومدی #اسم جان! 🌹\n📅 تاریخ: #تاریخ\n🕒 ساعت: #ساعت\nامیدوارم توی گروه بهمون خوش بگذره ❤️",
            "goodbye_template": "خداحافظ #اسم عزیز! 👋\n📅 تاریخ: #تاریخ\n🕒 ساعت: #ساعت\nبه امید دیدار دوباره ❤️",
            "welcome_gif": "",
            "goodbye_gif": "",
        }
        save_data()
    settings = data["group_settings"][key]
    settings.setdefault("locked_until", 0)
    settings.setdefault("media_locks", {"photo": False, "video": False, "voice": False, "gif": False, "document": False})
    settings.setdefault("auto_delete_50", False)
    settings.setdefault("hourly_delete", False)
    settings.setdefault("welcome_enabled", True)
    settings.setdefault("goodbye_enabled", True)
    settings.setdefault("captcha_enabled", True)
    settings.setdefault("welcome_template", "سلام و خوش اومدی #اسم جان! 🌹\n📅 تاریخ: #تاریخ\n🕒 ساعت: #ساعت\nامیدوارم توی گروه بهمون خوش بگذره ❤️")
    settings.setdefault("goodbye_template", "خداحافظ #اسم عزیز! 👋\n📅 تاریخ: #تاریخ\n🕒 ساعت: #ساعت\nبه امید دیدار دوباره ❤️")
    settings.setdefault("welcome_gif", "")
    settings.setdefault("goodbye_gif", "")
    return settings


def update_group_settings(chat_id: int, **kwargs) -> None:
    key = str(chat_id)
    get_group_settings(chat_id)
    data["group_settings"][key].update(kwargs)
    save_data()


def is_group_locked(chat_id: int) -> bool:
    """Checks whether the lock is currently in effect without clearing persisted state.

    The scheduled unlock job must retain the expired lock record so it can restore
    Telegram permissions and announce the unlock. Clearing it here can make the
    scheduled job think there is nothing to do, leaving the real group permissions locked.
    """
    settings = get_group_settings(chat_id)
    if not settings.get("locked", False):
        return False
    until = float(settings.get("locked_until", 0) or 0)
    if until and datetime.now().timestamp() >= until:
        return False
    return True


def is_group_silent(chat_id: int) -> bool:
    return datetime.now().timestamp() < get_group_settings(chat_id).get("silent_until", 0)


def get_group_max_warnings(chat_id: int) -> int:
    return int(get_group_settings(chat_id).get("max_warnings", DEFAULT_MAX_WARNINGS))


# ─── اخطار گروه ──────────────────────────────────────────────
def get_group_warnings(chat_id: int, user_id: int) -> int:
    return int(data["group_warnings"].get(str(chat_id), {}).get(str(user_id), 0))


def add_group_warning(chat_id: int, user_id: int) -> int:
    key = str(chat_id)
    if key not in data["group_warnings"]:
        data["group_warnings"][key] = {}
    n = data["group_warnings"][key].get(str(user_id), 0) + 1
    data["group_warnings"][key][str(user_id)] = n
    save_data()
    return n


def reset_group_warnings(chat_id: int, user_id: int) -> None:
    key = str(chat_id)
    if key in data["group_warnings"] and str(user_id) in data["group_warnings"][key]:
        del data["group_warnings"][key][str(user_id)]
        save_data()


# ─── بن گروه ─────────────────────────────────────────────────
def add_group_ban(chat_id: int, user_id: int, name: str = "") -> None:
    key = str(chat_id)
    if key not in data["group_bans"]:
        data["group_bans"][key] = {}
    data["group_bans"][key][str(user_id)] = name or f"کاربر {user_id}"
    save_data()


def remove_group_ban(chat_id: int, user_id: int) -> None:
    key = str(chat_id)
    if key in data["group_bans"] and str(user_id) in data["group_bans"][key]:
        del data["group_bans"][key][str(user_id)]
        save_data()


def get_group_bans(chat_id: int) -> dict:
    return data["group_bans"].get(str(chat_id), {})


# ═══════════════════════════════════════════════════════════════
# کمکی‌ها
# ═══════════════════════════════════════════════════════════════

def is_admin(update: Update) -> bool:
    """بررسی دسترسی مدیر اصلی یا مدیران اضافه‌شده."""
    u = update.effective_user
    return bool(u and is_any_admin(u.id))


def main_keyboard(user_id: Optional[int] = None) -> ReplyKeyboardMarkup:
    rows = [[KeyboardButton("🏠 شروع")]]
    if user_id and is_any_admin(user_id):
        rows[0].append(KeyboardButton("👑 پنل مدیریت"))

    names = [b["name"] for b in data["buttons"][:MAX_BUTTONS]]
    for i in range(0, len(names), 2):
        rows.append([KeyboardButton(n) for n in names[i:i + 2]])
    return ReplyKeyboardMarkup(rows, resize_keyboard=True)


def admin_panel() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("📚 آموزش رفتار", callback_data="teach"),
         InlineKeyboardButton("🗑 حذف آموزش", callback_data="delete_rule")],
        [InlineKeyboardButton("➕ دکمهٔ جدید", callback_data="new_button"),
         InlineKeyboardButton("📋 فهرست دکمه‌ها", callback_data="list_buttons")],
        [InlineKeyboardButton("👥 مدیریت گروه‌ها", callback_data="manage_groups")],
        [InlineKeyboardButton("🧹 پاک‌کردن حافظه", callback_data="clear_memory")],
        [InlineKeyboardButton("📊 آمار", callback_data="stats"),
         InlineKeyboardButton("🚫 لیست بن‌ها", callback_data="list_bans")],
        [InlineKeyboardButton("👤 مدیران", callback_data="manage_admins"),
         InlineKeyboardButton("➕ افزودن مدیر", callback_data="add_admin")],
        [InlineKeyboardButton("🔕 سکوت ۱ ساعت", callback_data="silence_1h"),
         InlineKeyboardButton("🔔 لغو سکوت", callback_data="unsilence")],
    ])


def group_panel(chat_id: int) -> InlineKeyboardMarkup:
    s = get_group_settings(chat_id)
    locked = is_group_locked(chat_id)
    silent = is_group_silent(chat_id)
    max_w = get_group_max_warnings(chat_id)
    bans_count = len(get_group_bans(chat_id))
    ml = s.get("media_locks", {})
    auto50 = bool(s.get("auto_delete_50", False))
    hourly = bool(s.get("hourly_delete", False))
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🔒 قفل زمان‌دار / بازکردن", callback_data="g_lock_menu")],
        [InlineKeyboardButton(f"وضعیت گروه: {'🔒 بسته' if locked else '🔓 باز'}", callback_data="g_lock_menu")],
        [InlineKeyboardButton(f"🎬 فیلم: {'🔒 قفل' if ml.get('video') else '🔓 باز'}", callback_data="g_media_video"),
         InlineKeyboardButton(f"🖼 عکس: {'🔒 قفل' if ml.get('photo') else '🔓 باز'}", callback_data="g_media_photo")],
        [InlineKeyboardButton(f"🎙 ویس: {'🔒 قفل' if ml.get('voice') else '🔓 باز'}", callback_data="g_media_voice"),
         InlineKeyboardButton(f"🎞 گیف: {'🔒 قفل' if ml.get('gif') else '🔓 باز'}", callback_data="g_media_gif")],
        [InlineKeyboardButton(f"📄 سند/فایل: {'🔒 قفل' if ml.get('document') else '🔓 باز'}", callback_data="g_media_document")],
        [InlineKeyboardButton("🧹 حذف ۵۰ پیام اخیر", callback_data="g_delete_50")],
        [InlineKeyboardButton(f"🧹 خودکار هر ۵۰ پیام: {'روشن' if auto50 else 'خاموش'}", callback_data="g_auto_delete_50")],
        [InlineKeyboardButton(f"🕐 پاک‌سازی ساعتی: {'روشن' if hourly else 'خاموش'}", callback_data="g_hourly_delete")],
        [InlineKeyboardButton(f"{('🔇' if silent else '🔊')} سکوت گروه", callback_data="g_silent_menu")],
        [InlineKeyboardButton("⚠️ تنظیم تعداد اخطار", callback_data="g_warn_settings")],
        [InlineKeyboardButton(f"📌 تعداد اخطار فعلی: {max_w}", callback_data="g_show_warnings")],
        [InlineKeyboardButton(f"🚫 لیست بن‌ها ({bans_count})", callback_data="g_ban_list")],
        [InlineKeyboardButton("📊 آمار گروه", callback_data="g_stats")],
        [InlineKeyboardButton("👋 تنظیم خوشامد و خداحافظی", callback_data="g_greetings")],
    ])



def greetings_panel(chat_id: int) -> InlineKeyboardMarkup:
    s = get_group_settings(chat_id)
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(f"👋 خوشامد: {'روشن' if s.get('welcome_enabled', True) else 'خاموش'}", callback_data="g_toggle_welcome")],
        [InlineKeyboardButton(f"🚪 خداحافظی: {'روشن' if s.get('goodbye_enabled', True) else 'خاموش'}", callback_data="g_toggle_goodbye")],
        [InlineKeyboardButton(f"🤖 کپچا عضو جدید: {'روشن' if s.get('captcha_enabled', True) else 'خاموش'}", callback_data="g_toggle_captcha")],
        [InlineKeyboardButton("✏️ تنظیم متن خوشامد", callback_data="g_set_welcome_text")],
        [InlineKeyboardButton("✏️ تنظیم متن خداحافظی", callback_data="g_set_goodbye_text")],
        [InlineKeyboardButton("🎞 افزودن/تعویض گیف خوشامد", callback_data="g_set_welcome_gif")],
        [InlineKeyboardButton("🎞 افزودن/تعویض گیف خداحافظی", callback_data="g_set_goodbye_gif")],
        [InlineKeyboardButton("🗑 حذف گیف خوشامد", callback_data="g_clear_welcome_gif"), InlineKeyboardButton("🗑 حذف گیف خداحافظی", callback_data="g_clear_goodbye_gif")],
        [InlineKeyboardButton("👁 پیش‌نمایش خوشامد", callback_data="g_preview_welcome"), InlineKeyboardButton("👁 پیش‌نمایش خداحافظی", callback_data="g_preview_goodbye")],
        [InlineKeyboardButton("↩️ بازگشت به پنل گروه", callback_data="g_back")],
    ])


def render_greeting(template: str, user, now: datetime, member_count: Optional[int] = None) -> str:
    jy, jm, jd = gregorian_to_jalali(now.year, now.month, now.day)
    name = (getattr(user, "full_name", None) or getattr(user, "first_name", None) or "دوست عزیز")
    values = {
        "#اسم": name,
        "#نام": name,
        "#تاریخ": f"{jy:04d}/{jm:02d}/{jd:02d}",
        "#ساعت": now.strftime("%H:%M"),
        "#تعداد_اعضا": str(member_count) if member_count is not None else "نامشخص",
    }
    result = template or "سلام #اسم!"
    for key, value in values.items():
        result = result.replace(key, value)
    return result[:1024]


async def send_greeting(context, chat_id: int, user, kind: str, member_count: Optional[int] = None) -> None:
    settings = get_group_settings(chat_id)
    enabled_key = "welcome_enabled" if kind == "welcome" else "goodbye_enabled"
    if not settings.get(enabled_key, True):
        return
    template_key = "welcome_template" if kind == "welcome" else "goodbye_template"
    gif_key = "welcome_gif" if kind == "welcome" else "goodbye_gif"
    now = datetime.now(BOT_TIMEZONE)
    text = render_greeting(settings.get(template_key, ""), user, now, member_count)
    gif_id = settings.get(gif_key, "")
    try:
        if gif_id:
            await context.bot.send_animation(chat_id=chat_id, animation=gif_id, caption=text[:1024])
        else:
            await context.bot.send_message(chat_id=chat_id, text=text)
    except Exception as exc:
        log.warning("ارسال پیام %s در گروه %s ناموفق بود: %r", kind, chat_id, exc)
        # اگر گیف خراب/حذف شده باشد، متن خوشامد را همچنان ارسال کن.
        if gif_id:
            try:
                await context.bot.send_message(chat_id=chat_id, text=text)
            except Exception:
                pass


def group_lock_time_mode_menu() -> InlineKeyboardMarkup:
    """گزینه‌های واضح برای تعیین روز بازشدن گروه."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🕐 امروز (اگر نگذشته)", callback_data="g_lock_time_today")],
        [InlineKeyboardButton("🌙 امشب", callback_data="g_lock_time_tonight"),
         InlineKeyboardButton("📅 فردا", callback_data="g_lock_time_tomorrow")],
        [InlineKeyboardButton("🤖 تشخیص خودکار از روی ساعت", callback_data="g_lock_time_auto")],
        [InlineKeyboardButton("↩️ برگشت", callback_data="g_lock_menu")],
    ])


def group_lock_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🔒 قفل ۱ ساعت", callback_data="g_lock_1h"), InlineKeyboardButton("🔒 قفل ۶ ساعت", callback_data="g_lock_6h")],
        [InlineKeyboardButton("🔒 قفل ۲۴ ساعت", callback_data="g_lock_24h"), InlineKeyboardButton("🔒 قفل بدون زمان", callback_data="g_lock_forever")],
        [InlineKeyboardButton("⏰ قفل تا ساعت مشخص", callback_data="g_lock_at_time")],
        [InlineKeyboardButton("🔓 بازکردن گروه", callback_data="g_unlock")],
        [InlineKeyboardButton("↩️ بازگشت", callback_data="g_back")],
    ])


def silent_menu(chat_id: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🔇 ۱۰ دقیقه", callback_data="g_silent_10m"),
         InlineKeyboardButton("🔇 ۱ ساعت", callback_data="g_silent_1h")],
        [InlineKeyboardButton("🔇 ۶ ساعت", callback_data="g_silent_6h"),
         InlineKeyboardButton("🔇 ۱ روز", callback_data="g_silent_1d")],
        [InlineKeyboardButton("🔇 ۱ هفته", callback_data="g_silent_1w")],
        [InlineKeyboardButton("🔊 لغو سکوت", callback_data="g_unsilent")],
        [InlineKeyboardButton("↩️ بازگشت", callback_data="g_back")],
    ])


def warnings_settings_menu(chat_id: int) -> InlineKeyboardMarkup:
    current = get_group_max_warnings(chat_id)
    buttons = []
    for n in (1, 2, 3, 4, 5):
        mark = "✅ " if n == current else ""
        buttons.append([InlineKeyboardButton(f"{mark}{n} اخطار", callback_data=f"g_set_warn_{n}")])
    buttons.append([InlineKeyboardButton("↩️ بازگشت", callback_data="g_back")])
    return InlineKeyboardMarkup(buttons)


def ban_list_menu(chat_id: int) -> InlineKeyboardMarkup:
    """لیست بن‌شده‌های گروه — هر کی دکمه‌ش رو بزنی آنبن می‌شه."""
    bans = get_group_bans(chat_id)
    if not bans:
        return InlineKeyboardMarkup([
            [InlineKeyboardButton("✅ هیچ بن‌شده‌ای نیست", callback_data="g_back")]
        ])

    buttons = []
    for uid_str, name in bans.items():
        label = f"🔓 آنبن {name} ({uid_str})"[:60]
        buttons.append([InlineKeyboardButton(label, callback_data=f"g_unban_{uid_str}")])

    buttons.append([InlineKeyboardButton("↩️ بازگشت", callback_data="g_back")])
    return InlineKeyboardMarkup(buttons)


# ═══════════════════════════════════════════════════════════════
# قفل گروه، پاک‌سازی پیام‌ها و زمان‌بندی
# ═══════════════════════════════════════════════════════════════

MEDIA_PERMISSION_FIELDS = {
    "photo": ("can_send_photos",),
    "video": ("can_send_videos",),
    "voice": ("can_send_audios", "can_send_voice_notes"),
    "gif": ("can_send_other_messages",),
    "document": ("can_send_documents",),
}


def _permissions_kwargs(chat_id: int) -> dict:
    settings = get_group_settings(chat_id)
    locked = is_group_locked(chat_id)
    silenced = is_group_silent(chat_id)
    kwargs = {"can_send_messages": not (locked or silenced)}
    for field in ("can_send_audios", "can_send_documents", "can_send_photos", "can_send_videos",
                  "can_send_video_notes", "can_send_voice_notes", "can_send_polls",
                  "can_send_other_messages", "can_add_web_page_previews"):
        kwargs[field] = not (locked or silenced)
    if not locked and not silenced:
        locks = settings.get("media_locks", {})
        for media, fields in MEDIA_PERMISSION_FIELDS.items():
            if locks.get(media):
                for field in fields:
                    kwargs[field] = False
    return kwargs


async def apply_group_permissions(bot, chat_id: int) -> None:
    await bot.set_chat_permissions(chat_id, ChatPermissions(**_permissions_kwargs(chat_id)))


def _remove_jobs(job_queue, name: str) -> None:
    # JobQueue فقط وقتی نصبِ extra مربوطه وجود دارد.
    if job_queue is None:
        return
    for job in job_queue.get_jobs_by_name(name):
        job.schedule_removal()


def schedule_group_unlock(application, chat_id: int, until_timestamp: float) -> bool:
    """زمان‌بندی بازشدن گروه؛ زمان ذخیره‌شده بر مبنای timestamp است."""
    job_queue = application.job_queue
    if job_queue is None:
        return False
    job_name = f"unlock_{chat_id}"
    _remove_jobs(job_queue, job_name)
    delay = max(1, until_timestamp - datetime.now().timestamp())
    job_queue.run_once(unlock_group_job, when=delay, chat_id=chat_id, name=job_name)
    return True


async def unlock_group_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    chat_id = int(context.job.chat_id)
    settings = get_group_settings(chat_id)
    # اگر زمان قفل هنوز نرسیده، زمان‌بندی زودهنگام را نادیده بگیر.
    until = float(settings.get("locked_until", 0) or 0)
    now_ts = datetime.now().timestamp()
    if not settings.get("locked") or (until and now_ts < until):
        if settings.get("locked") and until:
            schedule_group_unlock(context.application, chat_id, until)
        return

    # اول تلاش می‌کنیم دسترسی‌های تلگرام را باز کنیم؛ فقط بعد از موفقیت،
    # وضعیت ذخیره‌شده را باز می‌کنیم تا خطای API باعث بازماندن قفل نشود.
    try:
        update_group_settings(chat_id, locked=False, locked_until=0)
        await apply_group_permissions(context.bot, chat_id)
        log.info("قفل گروه %s به‌صورت خودکار باز شد.", chat_id)
    except Exception:
        log.exception("بازکردن خودکار گروه %s ناموفق بود؛ برای تلاش مجدد قفل فعال می‌ماند.", chat_id)
        update_group_settings(chat_id, locked=True, locked_until=until or now_ts)
        # تلاش دوباره پس از 30 ثانیه
        if context.application.job_queue is not None:
            context.application.job_queue.run_once(
                unlock_group_job, when=30, chat_id=chat_id,
                name=f"unlock_retry_{chat_id}"
            )


async def check_expired_group_locks_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    """پشتیبان زمان‌بندی: بررسی قفل‌های منقضی‌شده پس از خواب/تأخیر JobQueue."""
    now_ts = datetime.now().timestamp()
    for key, settings in list(data.get("group_settings", {}).items()):
        if not settings.get("locked"):
            continue
        until = float(settings.get("locked_until", 0) or 0)
        if until and now_ts >= until:
            await unlock_group_job(
                type("JobContext", (), {
                    "job": type("Job", (), {"chat_id": int(key)})(),
                    "bot": context.bot,
                    "application": context.application,
                })()
            )


async def hourly_delete_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    chat_id = context.job.chat_id
    settings = get_group_settings(chat_id)
    if settings.get("hourly_delete"):
        await delete_recent_group_messages(context.bot, chat_id, 50)


async def delete_recent_group_messages(bot, chat_id: int, limit: int = 50) -> int:
    key = str(chat_id)
    ids = data.get("group_history_messages", {}).get(key, [])
    targets = ids[-max(1, min(limit, 100)) :]
    deleted = 0
    remaining = list(ids)
    for message_id in reversed(targets):
        try:
            await bot.delete_message(chat_id=chat_id, message_id=message_id)
            deleted += 1
        except Exception as e:
            log.debug("حذف پیام %s از %s ممکن نشد: %r", message_id, chat_id, e)
        if message_id in remaining:
            remaining.remove(message_id)
    data.setdefault("group_history_messages", {})[key] = remaining[-500:]
    save_data()
    return deleted


async def track_group_message(chat_id: int, message_id: int, context: ContextTypes.DEFAULT_TYPE) -> None:
    key = str(chat_id)
    history = data.setdefault("group_history_messages", {}).setdefault(key, [])
    history.append(message_id)
    data["group_history_messages"][key] = history[-500:]
    counts = data.setdefault("group_message_counts", {})
    counts[key] = int(counts.get(key, 0)) + 1
    settings = get_group_settings(chat_id)
    auto_delete = bool(settings.get("auto_delete_50")) and counts[key] >= 50
    if auto_delete:
        counts[key] = 0
    save_data()
    if auto_delete:
        await delete_recent_group_messages(context.bot, chat_id, 50)


# ═══════════════════════════════════════════════════════════════
# هوش مصنوعی
# ═══════════════════════════════════════════════════════════════

def build_system_prompt(user_id: int) -> str:
    is_admin_user = is_any_admin(user_id)
    rules_text = "\n".join(f"- {r['text']}" for r in data["rules"])

    if is_admin_user:
        base = (
            f"تو «{BOT_NAME}» هستی — یک دستیار فارسی‌زبان، صمیمی، بامزه.\n"
            f"با مدیرت (ماهان) مثل رفیق صمیمی حرف بزن.\n"
            "• احساسات داری و کرم می‌ریزی\n"
            "• ایموجی زیاد استفاده کن 😄🔥\n"
            f"• اسمت «{BOT_NAME}» هست.\n"
            f"• سازنده‌ات: «{CREATOR_REPLY}»\n"
        )
    else:
        base = (
            f"تو «{BOT_NAME}» هستی — یک دستیار فارسی‌زبان، مهربان.\n"
            f"• اسمت «{BOT_NAME}» هست.\n"
            f"• سازنده‌ات: «{CREATOR_REPLY}»\n"
            "• مودب و کمک‌کننده باش.\n"
        )

    if rules_text:
        base += "\nآموزش‌ها:\n" + rules_text

    return base


def ask_ai(user_id: int, text: str) -> Optional[str]:
    history = memory.get(user_id)
    history.append({"role": "user", "content": text})
    messages = [
        {"role": "system", "content": build_system_prompt(user_id)},
        *history
    ]

    try:
        result = ai.chat.completions.create(
            model=AI_MODEL,
            messages=messages,
            max_completion_tokens=MAX_TOKENS,
            temperature=0.8 if is_any_admin(user_id) else 0.7,
            timeout=25,
        )
        answer = (result.choices[0].message.content or "").strip()
    except Exception as e:
        log.exception("خطای AI: %r", e)
        return "فعلاً در پاسخ‌گویی مشکلی پیش آمده."

    if is_groq_refusal(answer):
        return None
    if not answer:
        return None

    history.append({"role": "assistant", "content": answer})
    memory.set(user_id, history)
    return answer


async def ai_detect_profanity(text: str) -> bool:
    prompt = (
        "فقط با «بله» یا «خیر» جواب بده.\n"
        "آیا این پیام حاوی فحش، توهین، تهمت یا کلمات رکیک است؟\n"
        f"پیام: «{text}»"
    )
    def run() -> str:
        result = ai.chat.completions.create(
            model=AI_MODEL,
            messages=[{"role": "user", "content": prompt}],
            max_completion_tokens=10,
            temperature=0,
            timeout=10,
        )
        return (result.choices[0].message.content or "").strip()

    try:
        answer = await asyncio.to_thread(run)
        return "بله" in answer or "yes" in answer.lower()
    except Exception as e:
        log.warning("خطا در تشخیص AI فحش: %r", e)
        return False


async def transcribe(path: str) -> str:
    def run() -> str:
        with open(path, "rb") as f:
            result = ai.audio.transcriptions.create(
                file=f,
                model="whisper-large-v3-turbo",
                language="fa",
                timeout=45,
                prompt="این یک پیام صوتی فارسی است. دقیق رونویسی کن.",
            )
        return (result.text or "").strip()
    return await asyncio.to_thread(run)


async def text_to_voice(text: str, out_path: str) -> None:
    communicate = edge_tts.Communicate(text, TTS_VOICE, rate=TTS_RATE)
    await communicate.save(out_path)


# ═══════════════════════════════════════════════════════════════
# ارسال متن + ویس
# ═══════════════════════════════════════════════════════════════

async def send_text_and_voice(
    message,
    context: ContextTypes.DEFAULT_TYPE,
    text: str,
    *,
    voice_too: bool = True,
) -> None:
    if not text:
        return
    await message.reply_text(text)
    if not voice_too:
        return
    try:
        await context.bot.send_chat_action(message.chat_id, ChatAction.RECORD_VOICE)
        with tempfile.TemporaryDirectory() as td:
            path = str(Path(td) / "reply.mp3")
            await text_to_voice(text, path)
            with open(path, "rb") as vf:
                await message.reply_voice(voice=vf)
    except Exception as e:
        log.warning("خطا در ساخت/ارسال ویس: %r", e)


# ═══════════════════════════════════════════════════════════════
# جواب‌های سریع مدیر
# ═══════════════════════════════════════════════════════════════

def get_admin_quick_reply(text: str) -> Optional[str]:
    low = text.lower().strip()

    if any(w in low for w in ("به تو چه", "بتوچه", "چیکار داری")):
        return random.choice([
            "هیچی جیگر، فضولی کردم! 😂",
            "به من چه؟ به تو هم چه! 😂",
        ])
    if any(w in low for w in ("چیه امروز", "چی کار کنیم", "چیکار کنیم")):
        return random.choice([
            "هیچی، گفتم ببینم تو چه نقشه‌ای داری؟ 😎",
            "چیزی تو سرت هست؟ من پایه‌ام! 🚀",
        ])
    if any(w in low for w in ("چطوری", "خوبی", "چه خبر")):
        return random.choice([
            "من که عالیم! تو چطوری جیگر؟ 😎",
            "خوبم، ممنون! تو چه خبر؟ 😄",
        ])
    if any(w in low for w in ("خسته ام", "خسته‌ام", "خستم")):
        return "خسته نباشی جیگر! یه چایی بخور. ☕❤️"
    if any(w in low for w in ("دوستت دارم", "عاشقتم")):
        return "منم دوسِت دارم جیگر! ❤️😄"

    return None


# ═══════════════════════════════════════════════════════════════
# دستورها
# ═══════════════════════════════════════════════════════════════

async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.message:
        return
    uid = update.effective_user.id if update.effective_user else None
    chat = update.effective_chat
    if not uid or not is_any_admin(uid):
        return

    if chat and chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        # در گروه فقط پنل اختصاصی /panel فعال است؛ /start پاسخی نمی‌دهد.
        return

    if is_bot_off() and not (uid and is_any_admin(uid)):
        await update.message.reply_text(random.choice(SLEEPY_REPLIES))
        return

    if uid and is_any_admin(uid):
        await update.message.reply_text(
            f"سلام جیگر! 😄 خسته نباشی، چیه امروز؟ 🚀",
            reply_markup=main_keyboard(uid),
        )
    else:
        await update.message.reply_text(
            f"سلام، بفرمایید، در خدمتم. 😊\n"
            f"من {BOT_NAME} هستم.",
            reply_markup=main_keyboard(uid),
        )


async def cmd_admin(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.message:
        return
    if update.effective_chat and update.effective_chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        return
    if not is_admin(update):
        return
    await update.message.reply_text("پنل مدیریت 👑", reply_markup=admin_panel())


async def cmd_group_panel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat = update.effective_chat
    user = update.effective_user
    if not chat or not user or not update.message:
        return

    if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
        return

    try:
        member = await context.bot.get_chat_member(chat.id, user.id)
        is_tg_admin = member.status in ("administrator", "creator")
    except Exception:
        is_tg_admin = False

    if not (is_tg_admin or is_any_admin(user.id)):
        return

    await update.message.reply_text(
        f"⚙️ <b>پنل مدیریت گروه</b>",
        parse_mode="HTML",
        reply_markup=group_panel(chat.id),
    )


async def cmd_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if update.effective_chat and update.effective_chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        user = update.effective_user
        if user and is_any_admin(user.id):
            admin_states.pop(user.id, None)
        return
    if not is_admin(update):
        return
    admin_states.pop(ADMIN_ID, None)
    if update.message:
        await update.message.reply_text("لغو شد.", reply_markup=main_keyboard(ADMIN_ID))


# ═══════════════════════════════════════════════════════════════
# کالبک پنل ادمین
# ═══════════════════════════════════════════════════════════════

async def admin_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    q = update.callback_query
    await q.answer()
    if not q.from_user or not is_primary_admin(q.from_user.id):
        await q.edit_message_text("اجازهٔ دسترسی نداری.")
        return

    action = q.data

    if action == "teach":
        admin_states[ADMIN_ID] = {"mode": "teach"}
        await q.message.reply_text("📚 قانون آموزشی را بفرست.")
    elif action == "clear_memory":
        memory.clear()
        await q.message.reply_text("🧹 حافظه پاک شد.")
    elif action == "stats":
        await q.message.reply_text(
            "📊 آمار ربات:\n"
            f"• قوانین: {len(data['rules'])}\n"
            f"• دکمه‌ها: {len(data['buttons'])}\n"
            f"• کاربران حافظه: {memory.count()}\n"
            f"• گروه‌های فعال: {len(data['active_groups'])}"
        )
    elif action == "list_bans":
        if not data["bans"]:
            await q.message.reply_text("هیچ کاربر بن‌شده‌ای نیست.")
        else:
            await q.message.reply_text(
                "🚫 لیست بن‌ها:\n" + "\n".join(f"• {u}" for u in data["bans"])
            )
    elif action == "manage_groups":
        if not data["active_groups"]:
            await q.message.reply_text("هیچ گروه فعالی وجود ندارد.")
        else:
            await q.message.reply_text(
                "🟢 گروه‌های فعال:\n" + "\n".join(f"• {cid}" for cid in data["active_groups"])
            )
    elif action == "delete_rule":
        if not data["rules"]:
            await q.message.reply_text("آموزشی برای حذف وجود ندارد.")
        else:
            data["rules"].clear()
            save_data()
            await q.message.reply_text("🗑 همهٔ آموزش‌ها حذف شدند.")
    elif action == "new_button":
        admin_states[ADMIN_ID] = {"mode": "new_button"}
        await q.message.reply_text("نام دکمه و پاسخ آن را با این قالب بفرست:\nنام دکمه | پاسخ دکمه")
    elif action == "list_buttons":
        if not data["buttons"]:
            await q.message.reply_text("هنوز دکمه‌ای ساخته نشده است.")
        else:
            lines = [f"• {item.get('name', 'بدون نام')}: {item.get('reply', 'بدون پاسخ')}" for item in data["buttons"]]
            await q.message.reply_text("📋 فهرست دکمه‌ها:\n" + "\n".join(lines))
    elif action == "manage_admins":
        admins = data.get("admins", [])
        await q.message.reply_text("👤 مدیران اضافه‌شده:\n" + ("\n".join(map(str, admins)) if admins else "هیچ مدیری اضافه نشده است."))
    elif action == "add_admin":
        admin_states[ADMIN_ID] = {"mode": "add_admin"}
        await q.message.reply_text("آیدی عددی تلگرامِ کاربر را بفرست.")
    elif action == "silence_1h":
        data["silence_until"] = (datetime.now() + timedelta(hours=1)).timestamp()
        save_data()
        await q.message.reply_text("🔕 هوشی برای یک ساعت در حالت سکوت قرار گرفت.")
    elif action == "unsilence":
        data["silence_until"] = 0
        save_data()
        await q.message.reply_text("🔔 سکوت هوشی لغو شد.")
    elif action == "back_to_panel":
        await q.edit_message_text("پنل مدیریت 👑", reply_markup=admin_panel())
    elif action == "cancel_flow":
        admin_states.pop(ADMIN_ID, None)
        await q.message.reply_text("لغو شد.")


# ═══════════════════════════════════════════════════════════════
# کالبک پنل گروه
# ═══════════════════════════════════════════════════════════════

async def group_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    q = update.callback_query
    if not q or not q.message:
        return
    user = q.from_user
    chat = q.message.chat

    try:
        member = await context.bot.get_chat_member(chat.id, user.id)
        is_tg_admin = member.status in ("administrator", "creator")
    except Exception:
        is_tg_admin = False

    if not (is_tg_admin or is_any_admin(user.id)):
        await q.answer("اجازه نداری.", show_alert=True)
        return

    action = q.data
    chat_id = chat.id

    if action == "g_greetings":
        await q.answer()
        await q.edit_message_text("👋 تنظیم خوشامدگویی و خداحافظی\nمتغیرها: #اسم ، #تاریخ ، #ساعت ، #تعداد_اعضا", reply_markup=greetings_panel(chat_id))
        return
    if action in ("g_toggle_welcome", "g_toggle_goodbye", "g_toggle_captcha"):
        settings = get_group_settings(chat_id)
        key = {"g_toggle_welcome": "welcome_enabled", "g_toggle_goodbye": "goodbye_enabled", "g_toggle_captcha": "captcha_enabled"}[action]
        update_group_settings(chat_id, **{key: not settings.get(key, True)})
        await q.answer("تنظیم ذخیره شد.")
        await q.edit_message_reply_markup(reply_markup=greetings_panel(chat_id))
        return
    if action in ("g_set_welcome_text", "g_set_goodbye_text", "g_set_welcome_gif", "g_set_goodbye_gif"):
        modes = {
            "g_set_welcome_text": "welcome_text", "g_set_goodbye_text": "goodbye_text",
            "g_set_welcome_gif": "welcome_gif", "g_set_goodbye_gif": "goodbye_gif",
        }
        mode = modes[action]
        admin_states[user.id] = {"mode": mode, "chat_id": chat_id}
        await q.answer()
        if mode.endswith("_text"):
            await q.message.reply_text("متن جدید را در خصوصی ربات بفرست. متغیرها: #اسم، #تاریخ، #ساعت، #تعداد_اعضا\nبرای لغو /cancel")
        else:
            await q.message.reply_text("گیف را در خصوصی ربات بفرست (به‌صورت GIF/Animation). برای لغو /cancel")
        return
    if action in ("g_clear_welcome_gif", "g_clear_goodbye_gif"):
        key = "welcome_gif" if action == "g_clear_welcome_gif" else "goodbye_gif"
        update_group_settings(chat_id, **{key: ""})
        await q.answer("گیف حذف شد.")
        await q.edit_message_reply_markup(reply_markup=greetings_panel(chat_id))
        return
    if action in ("g_preview_welcome", "g_preview_goodbye"):
        kind = "welcome" if action == "g_preview_welcome" else "goodbye"
        settings = get_group_settings(chat_id)
        template = settings.get(f"{kind}_template", "")
        preview_user = user
        text = render_greeting(template, preview_user, datetime.now(BOT_TIMEZONE), None)
        gif_id = settings.get(f"{kind}_gif", "")
        await q.answer("پیش‌نمایش ارسال شد.")
        try:
            if gif_id:
                await context.bot.send_animation(chat_id=chat_id, animation=gif_id, caption=text)
            else:
                await context.bot.send_message(chat_id=chat_id, text=text)
        except Exception as exc:
            log.warning("Greeting preview failed: %r", exc)
            await q.message.reply_text(text)
        return

    # ─── قفل زمان‌دار / قفل رسانه ─────────────────────
    if action in ("g_toggle_lock", "g_lock_menu"):
        await q.answer()
        await q.edit_message_reply_markup(reply_markup=group_lock_menu())
        return
    elif action == "g_lock_at_time":
        await q.answer()
        await q.edit_message_text(
            "⏰ **تنظیم قفل تا ساعت مشخص**\n\n"
            "اول مشخص کن منظورت کدام روز است؛ بعد ساعت را بفرست، مثلاً `1:26` یا `22:15`.\n"
            "اگر «تشخیص خودکار» را بزنی، هوشی خودش حساب می‌کند ساعت امروز باقی مانده یا باید برای فردا تنظیم شود.\n\n"
            "📌 ساعت بر اساس وقت ایران محاسبه می‌شود.",
            reply_markup=group_lock_time_mode_menu(),
            parse_mode="Markdown",
        )
        return
    elif action in ("g_lock_time_today", "g_lock_time_tonight", "g_lock_time_tomorrow", "g_lock_time_auto"):
        modes = {
            "g_lock_time_today": ("today", "امروز"),
            "g_lock_time_tonight": ("tonight", "امشب"),
            "g_lock_time_tomorrow": ("tomorrow", "فردا"),
            "g_lock_time_auto": ("auto", "تشخیص خودکار"),
        }
        mode, label = modes[action]
        admin_states[user.id] = {"mode": "group_lock_time", "chat_id": chat_id, "date_mode": mode}
        await q.answer("حالت " + label + " انتخاب شد")
        await q.edit_message_text(
            f"✅ حالت انتخاب شد: **{label}**\n\n"
            "حالا ساعت را به همین گروه بفرست؛ مثلاً `1:26` یا `22:15`.\n"
            "در حالت تشخیص خودکار، اگر ساعت امروز گذشته باشد، برای فردا تنظیم می‌شود.",
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("↩️ برگشت", callback_data="g_lock_menu")]]),
            parse_mode="Markdown",
        )
        return
    elif action in ("g_lock_1h", "g_lock_6h", "g_lock_24h", "g_lock_forever"):
        durations = {"g_lock_1h": 3600, "g_lock_6h": 21600, "g_lock_24h": 86400}
        seconds = durations.get(action, 0)
        until = datetime.now().timestamp() + seconds if seconds else 0
        update_group_settings(chat_id, locked=True, locked_until=until)
        activate_group(chat_id)
        try:
            await apply_group_permissions(context.bot, chat_id)
            if seconds:
                job_name = f"unlock_{chat_id}"
                job_queue = context.application.job_queue
                if job_queue is None:
                    update_group_settings(chat_id, locked=False, locked_until=0)
                    await apply_group_permissions(context.bot, chat_id)
                    await q.answer(
                        "برای قفل زمان‌دار این دستور را در ترموکس اجرا کن:\npip install -U 'python-telegram-bot[job-queue]'",
                        show_alert=True,
                    )
                    await q.edit_message_text("⚙️ پنل مدیریت گروه", reply_markup=group_panel(chat_id))
                    return
                _remove_jobs(job_queue, job_name)
                job_queue.run_once(
                    unlock_group_job, when=seconds, chat_id=chat_id, name=job_name
                )
                duration_text = {3600: "۱ ساعت", 21600: "۶ ساعت", 86400: "۲۴ ساعت"}[seconds]
            else:
                _remove_jobs(context.application.job_queue, f"unlock_{chat_id}")
        except Exception as e:
            log.warning("خطا در قفل گروه %s: %r", chat_id, e)
            await q.answer("تنظیم قفل ناموفق بود؛ دسترسی ربات را بررسی کن.", show_alert=True)
        else:
            await q.answer("قفل گروه تنظیم شد.")
        await q.edit_message_text("⚙️ پنل مدیریت گروه", reply_markup=group_panel(chat_id))
        return
    elif action == "g_unlock":
        _remove_jobs(context.application.job_queue, f"unlock_{chat_id}")
        update_group_settings(chat_id, locked=False, locked_until=0)
        try:
            await apply_group_permissions(context.bot, chat_id)
            await q.answer("گروه باز شد.")
        except Exception as e:
            await q.answer(f"خطا در بازکردن گروه: {e}", show_alert=True)
        await q.edit_message_text("⚙️ پنل مدیریت گروه", reply_markup=group_panel(chat_id))
        return
    elif action.startswith("g_media_"):
        media = action.replace("g_media_", "")
        if media not in MEDIA_PERMISSION_FIELDS:
            await q.answer("نوع رسانه نامعتبر است.", show_alert=True)
            return
        settings = get_group_settings(chat_id)
        locks = settings.setdefault("media_locks", {})
        locks[media] = not bool(locks.get(media, False))
        save_data()
        try:
            await apply_group_permissions(context.bot, chat_id)
            await q.answer(f"{media}: {'قفل شد' if locks[media] else 'باز شد'}", show_alert=True)
        except Exception as e:
            await q.answer(f"تنظیم مجوزها ناموفق بود: {e}", show_alert=True)
        await q.edit_message_reply_markup(reply_markup=group_panel(chat_id))
        return
    elif action == "g_delete_50":
        deleted = await delete_recent_group_messages(context.bot, chat_id, 50)
        await q.answer(f"{deleted} پیام حذف شد.", show_alert=True)
        return
    elif action == "g_auto_delete_50":
        settings = get_group_settings(chat_id)
        enabled = not bool(settings.get("auto_delete_50", False))
        update_group_settings(chat_id, auto_delete_50=enabled)
        await q.answer(f"پاک‌سازی خودکار هر ۵۰ پیام {'روشن' if enabled else 'خاموش'} شد.", show_alert=True)
        await q.edit_message_reply_markup(reply_markup=group_panel(chat_id))
        return
    elif action == "g_hourly_delete":
        settings = get_group_settings(chat_id)
        enabled = not bool(settings.get("hourly_delete", False))
        update_group_settings(chat_id, hourly_delete=enabled)
        job_name = f"hourly_delete_{chat_id}"
        job_queue = context.application.job_queue
        _remove_jobs(job_queue, job_name)
        if enabled and job_queue is None:
            update_group_settings(chat_id, hourly_delete=False)
            await q.answer(
                "برای پاک‌سازی ساعتی این دستور را در ترموکس اجرا کن:\npip install -U 'python-telegram-bot[job-queue]'",
                show_alert=True,
            )
            return
        if enabled:
            job_queue.run_repeating(
                hourly_delete_job, interval=3600, first=3600,
                chat_id=chat_id, name=job_name,
            )
        await q.answer(f"پاک‌سازی ساعتی {'روشن' if enabled else 'خاموش'} شد.", show_alert=True)
        await q.edit_message_reply_markup(reply_markup=group_panel(chat_id))
        return

    # ─── سکوت ───────────────────────────────────────
    elif action == "g_silent_menu":
        await q.answer()
        await q.edit_message_reply_markup(reply_markup=silent_menu(chat_id))

    elif action.startswith("g_silent_"):
        mins = {"10m": 10, "1h": 60, "6h": 360, "1d": 1440, "1w": 10080}
        key = action.replace("g_silent_", "")
        if key in mins:
            until = (datetime.now() + timedelta(minutes=mins[key])).timestamp()
            update_group_settings(chat_id, silent_until=until)
            try:
                await apply_group_permissions(context.bot, chat_id)
            except Exception:
                pass
            await q.answer(f"گروه ساکت شد ({key}).", show_alert=True)
            await q.edit_message_reply_markup(reply_markup=group_panel(chat_id))

    elif action == "g_unsilent":
        update_group_settings(chat_id, silent_until=0)
        try:
            await apply_group_permissions(context.bot, chat_id)
        except Exception:
            pass
        await q.answer("سکوت لغو شد.", show_alert=True)
        await q.edit_message_reply_markup(reply_markup=group_panel(chat_id))

    # ─── اخطار ──────────────────────────────────────
    elif action == "g_warn_settings":
        await q.answer()
        await q.edit_message_reply_markup(reply_markup=warnings_settings_menu(chat_id))

    elif action.startswith("g_set_warn_"):
        n = int(action.split("_")[-1])
        update_group_settings(chat_id, max_warnings=n)
        await q.answer(f"✅ تعداد اخطار: {n}", show_alert=True)
        await q.edit_message_reply_markup(reply_markup=warnings_settings_menu(chat_id))

    elif action == "g_show_warnings":
        max_w = get_group_max_warnings(chat_id)
        await q.answer(f"تعداد اخطار فعلی: {max_w}", show_alert=True)

    # ─── لیست بن (دکمه‌ای) ───────────────────────────
    elif action == "g_ban_list":
        await q.answer()
        bans = get_group_bans(chat_id)
        if not bans:
            await q.answer("هیچ کاربری بن نشده.", show_alert=True)
        else:
            await q.edit_message_text(
                f"🚫 <b>لیست بن‌شده‌ها ({len(bans)})</b>\n"
                f"━━━━━━━━━━━━\n"
                f"روی هر کاربر بزنی → آنبن می‌شه:",
                parse_mode="HTML",
                reply_markup=ban_list_menu(chat_id),
            )

    # ─── آنبن با دکمه ────────────────────────────────
    elif action.startswith("g_unban_"):
        try:
            target_uid = int(action.replace("g_unban_", ""))
        except ValueError:
            await q.answer("خطا در آیدی.", show_alert=True)
            return

        try:
            await context.bot.unban_chat_member(chat_id, target_uid)
            reset_group_warnings(chat_id, target_uid)
            remove_group_ban(chat_id, target_uid)
            await q.answer(f"✅ کاربر {target_uid} آنبن شد.", show_alert=True)
        except Exception as e:
            await q.answer(f"خطا: {e}", show_alert=True)

        # لیست رو دوباره نشون بده
        bans = get_group_bans(chat_id)
        if not bans:
            await q.edit_message_text("✅ لیست بن خالی شد.")
        else:
            await q.edit_message_text(
                f"🚫 <b>لیست بن‌شده‌ها ({len(bans)})</b>\n"
                f"━━━━━━━━━━━━\n"
                f"روی هر کاربر بزنی → آنبن می‌شه:",
                parse_mode="HTML",
                reply_markup=ban_list_menu(chat_id),
            )

    # ─── آمار ──────────────────────────────────────
    elif action == "g_stats":
        s = get_group_settings(chat_id)
        w = data["group_warnings"].get(str(chat_id), {})
        await q.answer(
            f"وضعیت: {'قفل' if s.get('locked') else 'باز'} | "
            f"سکوت: {'فعال' if is_group_silent(chat_id) else 'غیرفعال'} | "
            f"حداکثر اخطار: {s.get('max_warnings', DEFAULT_MAX_WARNINGS)} | "
            f"کاربران با اخطار: {len(w)} | بن‌شده‌ها: {len(get_group_bans(chat_id))}",
            show_alert=True,
        )

    # ─── بازگشت ─────────────────────────────────────
    elif action == "g_back":
        await q.answer()
        await q.edit_message_text("⚙️ <b>پنل مدیریت گروه</b>", parse_mode="HTML", reply_markup=group_panel(chat_id))


# ═══════════════════════════════════════════════════════════════
# دستورهای بن
# ═══════════════════════════════════════════════════════════════

async def cmd_ban_reply(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg = update.message
    chat = update.effective_chat
    user = update.effective_user
    if not msg or not chat or not user:
        return
    if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
        return

    try:
        member = await context.bot.get_chat_member(chat.id, user.id)
        if member.status not in ("administrator", "creator") and not is_any_admin(user.id):
            return
    except Exception:
        return

    if not msg.reply_to_message:
        return

    target = msg.reply_to_message.from_user
    if not target:
        return

    name = target.first_name or f"کاربر {target.id}"
    try:
        await context.bot.ban_chat_member(chat.id, target.id)
        add_group_ban(chat.id, target.id, name)
        log.info("کاربر %s در گروه %s توسط دستور /ban بن شد.", target.id, chat.id)
    except Exception as e:
        log.warning("خطا در دستور بن گروه: %r", e)


# ═══════════════════════════════════════════════════════════════
# منطق فحش + بن خودکار (گروه)
# ═══════════════════════════════════════════════════════════════

async def check_group_profanity(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
    chat_id: int,
    user_id: int,
    message,
    text: str,
) -> bool:
    if is_any_admin(user_id):
        return False

    try:
        member = await context.bot.get_chat_member(chat_id, user_id)
        if member.status in ("administrator", "creator"):
            return False
    except Exception:
        pass

    is_profane = contains_profanity(text)
    # برای اینکه پیام‌های عادی گروه به‌خاطر تماس AI معطل نشوند، تشخیص AI فقط
    # برای متن‌های مشکوک به ریشه‌های رکیک اجرا می‌شود؛ تطبیق واژه‌ای بالاتر فوری است.
    if not is_profane and len(text) >= 3:
        normalized = normalize_profanity_text(text)
        suspicious = re.search(r"(کص|کس|کیر|کون|گای|جند|دیوث|ناموس|fuck|fuk|dick|dik|puss|bitch|bich|asshole|motherf)", normalized, re.I)
        if suspicious:
            try:
                is_profane = await asyncio.wait_for(ai_detect_profanity(text), timeout=1.2)
            except asyncio.TimeoutError:
                is_profane = False

    if not is_profane:
        return False

    max_w = get_group_max_warnings(chat_id)
    n = add_group_warning(chat_id, user_id)

    try:
        await message.delete()
    except Exception as e:
        log.warning("خطا در حذف: %r", e)

    if n < max_w:
        try:
            await context.bot.send_message(
                chat_id,
                f"😏 اِ داش {message.from_user.first_name}، فکر کردی حواسم نیست چی نوشتی؟\n"
                f"⚠️ اخطار {n}/{max_w} گرفتی!\n"
                f"حواست به خودت باشه؛ ادامه بدی ممکنه بن بشی. با هوشی لج نکن داداش 😂"
            )
        except Exception:
            pass
    else:
        name = message.from_user.first_name or f"کاربر {user_id}"
        try:
            await context.bot.ban_chat_member(chat_id, user_id)
            add_group_ban(chat_id, user_id, name)
            await context.bot.send_message(
                chat_id,
                f"🚫 <b>{name}</b> بن شد!\n"
                f"دلیل: تکرار فحش ({n} اخطار)",
                parse_mode="HTML",
            )
        except Exception as e:
            log.warning("خطا در بن: %r", e)

    return True


# ═══════════════════════════════════════════════════════════════
# منطق فحش در چت خصوصی
# ═══════════════════════════════════════════════════════════════

async def _check_profanity_and_warn(
    message, context, user, text: str
) -> bool:
    if is_any_admin(user.id):
        return False

    is_profane = contains_profanity(text)
    if not is_profane and len(text) >= 3:
        is_profane = await ai_detect_profanity(text)

    if not is_profane:
        return False

    n = add_warning(user.id)
    if n >= DEFAULT_MAX_WARNINGS:
        ban_user(user.id)
        await message.reply_text("🚫 بن شدی.")
        return True
    await message.reply_text(f"⚠️ اخطار {n}/{DEFAULT_MAX_WARNINGS}")
    return True


# ═══════════════════════════════════════════════════════════════
# هندلر پیام
# ═══════════════════════════════════════════════════════════════

async def handle_message(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.message
    user = update.effective_user
    if not message or not user:
        return

    chat = update.effective_chat
    text = (message.text or "").strip()
    any_admin = is_any_admin(user.id)

    # رویداد ورود/خروج عضو؛ پیام سرویس تلگرام را با پیام عادی اشتباه نگیر.
    if chat and chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        if is_bot_off() and (message.new_chat_members or message.left_chat_member):
            return
        if message.new_chat_members:
            try:
                member_count = await context.bot.get_chat_member_count(chat.id)
            except Exception:
                member_count = None
            for joined_user in message.new_chat_members:
                if joined_user.is_bot:
                    continue
                settings = get_group_settings(chat.id)
                if settings.get("captcha_enabled", True):
                    try:
                        await context.bot.restrict_chat_member(
                            chat.id, joined_user.id,
                            permissions=ChatPermissions(can_send_messages=False, can_send_audios=False,
                                can_send_documents=False, can_send_photos=False, can_send_videos=False,
                                can_send_video_notes=False, can_send_voice_notes=False, can_send_polls=False,
                                can_send_other_messages=False, can_add_web_page_previews=False),
                        )
                        a = random.randint(1, 9)
                        b = random.randint(1, 9)
                        if random.choice((True, False)):
                            op, answer = "+", a + b
                        else:
                            if b > a:
                                a, b = b, a
                            op, answer = "−", a - b
                        _pending_captcha[(chat.id, joined_user.id)] = (member_count or 0, answer)
                        options = {answer}
                        while len(options) < 3:
                            options.add(max(0, answer + random.choice((-3, -2, -1, 1, 2, 3))))
                        buttons = [InlineKeyboardButton(str(v), callback_data=f"captcha_{chat.id}_{joined_user.id}_{v}") for v in sorted(options)]
                        random.shuffle(buttons)
                        kb = InlineKeyboardMarkup([buttons])
                        challenge_message = await context.bot.send_message(
                            chat.id,
                            f"🤖 خوش اومدی {joined_user.first_name}!\n"
                            f"برای اثبات اینکه ربات نیستی، این سؤال رو حل کن: {a} {op} {b} = ؟\n"
                            f"⏳ فقط {_CAPTCHA_TIMEOUT_SECONDS} ثانیه وقت داری؛ تا جواب درست ندی نمی‌تونی پیام بدی.",
                            reply_markup=kb,
                        )
                        _captcha_message_ids[(chat.id, joined_user.id)] = challenge_message.message_id
                        context.application.create_task(
                            _captcha_timeout(context, chat.id, joined_user.id, challenge_message.message_id)
                        )
                        continue
                    except Exception as exc:
                        log.warning("فعال‌سازی کپچا ناموفق بود: %r", exc)
                await send_greeting(context, chat.id, joined_user, "welcome", member_count)
            return
        if message.left_chat_member:
            left_user = message.left_chat_member
            if not left_user.is_bot:
                await send_greeting(context, chat.id, left_user, "goodbye")
            return

    # پاسخ به درخواست ساعت بازشدن گروه را پیش از پردازش عادی پیام می‌گیریم.
    state = admin_states.get(user.id) if is_any_admin(user.id) else None
    # حالت‌های پنل خصوصی نباید با پیام مدیر در گروه فعال شوند؛ فقط ورودی زمان
    # در همان گروهی که پنلش باز شده، به‌عنوان عملیات پنل پذیرفته می‌شود.
    if state and chat and chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        if state.get("mode") != "group_lock_time" or int(state.get("chat_id", 0)) != chat.id:
            state = None
    if state and state.get("mode") == "group_lock_time" and text and not text.startswith("/"):
        target_chat_id = int(state.get("chat_id", 0))
        now = (await get_internet_utc_now()).astimezone(BOT_TIMEZONE)
        try:
            date_mode = state.get("date_mode", "auto")
            time_input = text
            if date_mode == "today":
                time_input = "امروز " + text
            elif date_mode == "tonight":
                time_input = "امشب " + text
            elif date_mode == "tomorrow":
                time_input = "فردا " + text
            target = parse_group_unlock_target(time_input, now)
        except ValueError as exc:
            help_text = (
                f"❌ {exc}\n\n"
                "نمونه ساعت: `1:26` یا `22:15`\n"
                "می‌توانی از پنل «امروز»، «امشب»، «فردا» یا «تشخیص خودکار» را انتخاب کنی.\n"
                "در تشخیص خودکار، اگر ساعت امروز گذشته باشد، فردا در همان ساعت باز می‌شود."
            )
            if chat and chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
                try:
                    await context.bot.send_message(chat_id=user.id, text=help_text, parse_mode="Markdown")
                except Exception:
                    pass
            else:
                await message.reply_text(help_text, parse_mode="Markdown")
            return
        until = target.timestamp()
        if context.application.job_queue is None:
            if chat and chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
                await message.reply_text("❌ زمان‌بندی فعال نیست. در ترموکس اجرا کن:\npip install -U 'python-telegram-bot[job-queue]'")
            admin_states.pop(user.id, None)
            return
        try:
            update_group_settings(target_chat_id, locked=True, locked_until=until)
            activate_group(target_chat_id)
            await apply_group_permissions(context.bot, target_chat_id)
            if not schedule_group_unlock(context.application, target_chat_id, until):
                raise RuntimeError("JobQueue در دسترس نیست")
            admin_states.pop(user.id, None)
            jy, jm, jd = gregorian_to_jalali(target.year, target.month, target.day)
            weekday_names = ["دوشنبه", "سه‌شنبه", "چهارشنبه", "پنجشنبه", "جمعه", "شنبه", "یکشنبه"]
            weekday_name = weekday_names[target.weekday()]
            when_text = f"{weekday_name} {jy:04d}/{jm:02d}/{jd:02d} ساعت {target.strftime('%H:%M')} به وقت ایران"
            # اعلام زمان بازشدن را همیشه داخل همان گروه می‌فرستیم؛
            # حتی اگر مدیر ساعت را از پنل خصوصی تنظیم کرده باشد.
            announcement = (
                "🔒 قفل زمان‌دار گروه فعال شد.\n"
                f"⏰ زمان بازشدن خودکار: {when_text}\n"
                "تا آن زمان ارسال پیام برای اعضا محدود می‌ماند."
            )
            try:
                await context.bot.send_message(chat_id=target_chat_id, text=announcement)
            except Exception:
                log.exception("ارسال اعلام زمان بازشدن در گروه ناموفق بود")
            if chat and chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
                try:
                    await context.bot.send_message(
                        chat_id=user.id,
                        text=f"✅ زمان ثبت شد. اعلام زمان بازشدن هم در گروه ارسال شد.\nگروه در {when_text} خودکار باز می‌شود."
                    )
                except Exception:
                    pass
            else:
                await message.reply_text(f"✅ زمان ثبت شد. اعلام زمان بازشدن در گروه ارسال شد.\nگروه تا {when_text} بسته می‌ماند و خودکار باز می‌شود.")
        except Exception as e:
            update_group_settings(target_chat_id, locked=False, locked_until=0)
            try:
                await apply_group_permissions(context.bot, target_chat_id)
            except Exception:
                pass
            admin_states.pop(user.id, None)
            log.exception("تنظیم قفل تا ساعت مشخص شکست خورد")
            if chat and chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
                await message.reply_text("⚠️ نتوانستم قفل زمان‌دار را تنظیم کنم؛ گزارش خطا در لاگ ثبت شد.")
        return

    if chat and chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        await _handle_group_message(update, context, chat, user, text, message)
        return

    # دریافت پاسخ عملیات پنل فقط از مدیر اصلی
    state = admin_states.get(user.id) if is_any_admin(user.id) else None
    if chat and chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        state = None
    if state and ((text and not text.startswith("/")) or message.animation or message.document):
        mode = state.get("mode")
        target_chat_id = int(state.get("chat_id", 0) or 0)
        if mode in ("welcome_text", "goodbye_text"):
            if not target_chat_id:
                admin_states.pop(user.id, None)
                await message.reply_text("گروه هدف پیدا نشد؛ دوباره از پنل همان گروه اقدام کن.")
                return
            key = "welcome_template" if mode == "welcome_text" else "goodbye_template"
            update_group_settings(target_chat_id, **{key: text[:1024]})
            admin_states.pop(user.id, None)
            await message.reply_text("✅ متن ذخیره شد. متغیرها: #اسم، #تاریخ، #ساعت، #تعداد_اعضا")
            return
        if mode in ("welcome_gif", "goodbye_gif"):
            gif_file_id = None
            if message.animation:
                gif_file_id = message.animation.file_id
            elif message.document and (message.document.mime_type or "").lower() == "image/gif":
                gif_file_id = message.document.file_id
            if not gif_file_id:
                await message.reply_text("لطفاً خود GIF را به‌صورت Animation یا فایل با پسوند GIF بفرست؛ یا /cancel بزن.")
                return
            key = "welcome_gif" if mode == "welcome_gif" else "goodbye_gif"
            update_group_settings(target_chat_id, **{key: gif_file_id})
            admin_states.pop(user.id, None)
            await message.reply_text("✅ گیف ذخیره شد.")
            return
        if mode == "teach":
            data["rules"].append({"text": text})
            save_data()
            admin_states.pop(user.id, None)
            await message.reply_text("✅ آموزش ذخیره شد.")
            return
        if mode == "new_button":
            if "|" not in text:
                await message.reply_text("قالب درست: نام دکمه | پاسخ دکمه")
                return
            name, reply = (part.strip() for part in text.split("|", 1))
            if not name or not reply:
                await message.reply_text("نام و پاسخ هر دو لازم‌اند.")
                return
            data["buttons"].append({"name": name[:50], "reply": reply[:1000]})
            save_data()
            admin_states.pop(user.id, None)
            await message.reply_text("✅ دکمه ساخته شد. برای نمایش آن /start را بزن.")
            return
        if mode == "add_admin":
            try:
                new_id = int(text.strip())
                if new_id <= 0:
                    raise ValueError
            except ValueError:
                await message.reply_text("آیدی باید عدد صحیح مثبت باشد. دوباره بفرست یا /cancel بزن.")
                return
            if new_id == ADMIN_ID or new_id in data["admins"]:
                await message.reply_text("این کاربر از قبل مدیر است.")
            else:
                data["admins"].append(new_id)
                save_data()
                await message.reply_text(f"✅ مدیر {new_id} اضافه شد.")
            admin_states.pop(user.id, None)
            return

    if not any_admin and is_banned(user.id):
        await message.reply_text("🚫 بن شدی.")
        return

    if is_bot_off() and not any_admin:
        await message.reply_text(random.choice(SLEEPY_REPLIES))
        return

    if text == "🏠 شروع":
        await cmd_start(update, context)
        return
    if text == "👑 پنل مدیریت":
        await cmd_admin(update, context)
        return

    if any_admin and message.voice:
        handled = await _handle_admin_voice(message, context)
        if handled:
            return

    if message.voice:
        await _handle_user_voice(message, context, user)
        return

    if text and not text.startswith("/"):
        await _handle_user_text(message, context, user, text)


async def _group_member_is_admin(chat, user_id: int, context) -> bool:
    try:
        member = await context.bot.get_chat_member(chat.id, user_id)
        return member.status in ("administrator", "creator")
    except Exception:
        return is_any_admin(user_id)


async def _apply_group_antiflood(chat, user, message, context, text: str, sender_is_admin: bool) -> bool:
    """پیام‌های سیل‌آسا/تکراری را بی‌سروصدا حذف و در صورت امکان فرستنده را موقتاً محدود می‌کند."""
    if sender_is_admin or getattr(user, "is_bot", False):
        return False

    now = time.monotonic()
    key = (chat.id, user.id)
    window = _group_flood_windows.setdefault(key, deque())
    while window and now - window[0] > _GROUP_FLOOD_WINDOW_SECONDS:
        window.popleft()
    window.append(now)

    normalized = re.sub(r"\s+", " ", (text or "").lower()).strip()
    # برای رسانه‌های بدون متن نیز کلید ثابت استفاده می‌شود تا اسپم رسانه‌ای شناسایی شود.
    if not normalized:
        if message.photo:
            normalized = "[photo]"
        elif message.video:
            normalized = "[video]"
        elif message.animation:
            normalized = "[animation]"
        elif message.document:
            normalized = "[document]"
        elif message.voice:
            normalized = "[voice]"
        elif message.video_note:
            normalized = "[video_note]"
        elif message.sticker:
            normalized = "[sticker]"
        else:
            normalized = f"[media:{message.content_type}]"

    recent = _group_recent_texts.setdefault(key, deque())
    while recent and now - recent[0][0] > _GROUP_DUPLICATE_WINDOW_SECONDS:
        recent.popleft()
    recent.append((now, normalized[:500]))
    duplicate_count = sum(1 for _, value in recent if value == normalized[:500])
    flood = len(window) > _GROUP_FLOOD_MAX_MESSAGES or duplicate_count >= _GROUP_DUPLICATE_MAX

    # محدودسازی حافظه برای گروه‌های پررفت‌وآمد
    if len(_group_flood_windows) > 5000:
        for old_key in list(_group_flood_windows)[:1000]:
            _group_flood_windows.pop(old_key, None)
            _group_recent_texts.pop(old_key, None)
            _GROUP_FLOOD_COOLDOWN.pop(old_key, None)

    if not flood:
        return False

    try:
        await message.delete()
    except Exception as exc:
        log.debug("حذف پیام فلود ممکن نشد: %r", exc)

    # برای جلوگیری از درخواست‌های مکرر API، هر کاربر در هر گروه فقط هر ۵ دقیقه محدود می‌شود.
    cooldown_until = _GROUP_FLOOD_COOLDOWN.get(key, 0.0)
    if now >= cooldown_until:
        _GROUP_FLOOD_COOLDOWN[key] = now + _GROUP_FLOOD_MUTE_SECONDS
        try:
            until_date = datetime.now(timezone.utc) + timedelta(seconds=_GROUP_FLOOD_MUTE_SECONDS)
            await context.bot.restrict_chat_member(
                chat_id=chat.id,
                user_id=user.id,
                permissions=ChatPermissions(can_send_messages=False),
                until_date=until_date,
            )
            log.info("کاربر %s در گروه %s به‌دلیل فلود برای ۵ دقیقه محدود شد.", user.id, chat.id)
        except Exception as exc:
            log.warning("محدودسازی کاربر فلودر ممکن نشد: %r", exc)
    return True


async def _handle_group_message(update, context, chat, user, text: str, message) -> None:
    # در گروه هیچ پاسخ چتی تولید نمی‌شود. تنها پنل /panel و دکمه‌های آن کار می‌کنند.
    if message.message_id:
        await track_group_message(chat.id, message.message_id, context)

    # هنگام قفل گروه، پیام کاربران عادی حذف شود؛ هیچ پیام توضیحی ارسال نمی‌شود.
    if is_group_locked(chat.id) or is_group_silent(chat.id):
        sender_is_admin = await _group_member_is_admin(chat, user.id, context) or is_any_admin(user.id)
        if not sender_is_admin:
            try:
                await message.delete()
            except Exception:
                pass
            return

    sender_is_admin = await _group_member_is_admin(chat, user.id, context) or is_any_admin(user.id)

    # پیام عادی کاملاً بی‌پاسخ می‌ماند؛ فقط فحش کاربران عادی حذف و برای آن اخطار ثبت می‌شود.
    # تشخیص واژه‌ای سریع است و برای متن‌های مبهم، تشخیص AI نیز پشتیبان خواهد بود.
    if not sender_is_admin and text and await check_group_profanity(
        update, context, chat.id, user.id, message, text
    ):
        return

    await _apply_group_antiflood(chat, user, message, context, text, sender_is_admin)
    return


async def _handle_user_text(message, context, user, text: str) -> None:
    if await _check_profanity_and_warn(message, context, user, text):
        return

    for item in data.get("buttons", []):
        if text == item.get("name") and item.get("reply"):
            await message.reply_text(item["reply"])
            return

    if is_any_admin(user.id):
        quick = get_admin_quick_reply(text)
        if quick:
            await send_text_and_voice(message, context, quick)
            return

    if any(w in text.lower() for w in ("سازندت", "کی ساختت")):
        if CREATOR_STICKER:
            try:
                await message.reply_sticker(CREATOR_STICKER)
            except Exception:
                pass
        await send_text_and_voice(message, context, CREATOR_REPLY)
        return

    if any(w in text.lower() for w in ("اسمت چیه", "اسم تو")):
        await send_text_and_voice(message, context, f"اسم من {BOT_NAME} هست! 😊")
        return

    await context.bot.send_chat_action(message.chat_id, ChatAction.TYPING)
    answer = await asyncio.to_thread(ask_ai, user.id, text)

    if answer is None:
        fallback = "چی گفتی جیگر؟ نفهمیدم! 😅" if is_any_admin(user.id) else "ببخشید، نمی‌تونم پاسخ بدم."
        await send_text_and_voice(message, context, fallback)
        return

    await send_text_and_voice(message, context, answer)


async def _handle_admin_voice(message, context) -> bool:
    try:
        spoken = await _download_and_transcribe(context, message.voice.file_id)
    except Exception:
        await message.reply_text("در تشخیص مشکلی پیش آمد.")
        return True
    if not spoken:
        return False

    low = spoken.lower()
    if any(w in low for w in ("پنل", "مدیریت")):
        await message.reply_text("پنل 👑", reply_markup=admin_panel())
        return True
    return False


async def _handle_user_voice(message, context, user) -> None:
    try:
        await context.bot.send_chat_action(message.chat_id, ChatAction.TYPING)
        text = await _download_and_transcribe(context, message.voice.file_id)
    except Exception:
        await message.reply_text("نتونستم صدات رو تشخیص بدم.")
        return
    if not text:
        await message.reply_text("صدای واضحی نشنیدم.")
        return

    await message.reply_text(f"📝 متن پیام: {text}")

    if await _check_profanity_and_warn(message, context, user, text):
        return

    if is_any_admin(user.id):
        quick = get_admin_quick_reply(text)
        if quick:
            await send_text_and_voice(message, context, quick)
            return

    await context.bot.send_chat_action(message.chat_id, ChatAction.TYPING)
    answer = await asyncio.to_thread(ask_ai, user.id, text)

    if answer is None:
        fallback = "چی گفتی جیگر؟ نفهمیدم! 😅" if is_any_admin(user.id) else "ببخشید، نمی‌تونم پاسخ بدم."
        await send_text_and_voice(message, context, fallback)
        return

    await send_text_and_voice(message, context, answer)


async def _download_and_transcribe(context, file_id: str) -> str:
    with tempfile.TemporaryDirectory() as td:
        path = str(Path(td) / "voice.ogg")
        file = await context.bot.get_file(file_id)
        await file.download_to_drive(path)
        return await transcribe(path)


# ═══════════════════════════════════════════════════════════════
# خطا و راه‌اندازی
# ═══════════════════════════════════════════════════════════════

async def _remove_failed_captcha_user(context: ContextTypes.DEFAULT_TYPE, chat_id: int, user_id: int,
                                      message_id: Optional[int] = None, reason: str = "زمان کپچا تمام شد") -> None:
    """بار اول کاربر را بیرون می‌اندازد و اجازهٔ تلاش دوباره می‌دهد؛ بار دوم بن دائمی می‌کند."""
    key = (chat_id, user_id)
    if key not in _pending_captcha:
        return
    _pending_captcha.pop(key, None)
    _captcha_message_ids.pop(key, None)
    failures = _captcha_failures.get(key, 0) + 1
    _captcha_failures[key] = failures
    try:
        if message_id is not None:
            try:
                await context.bot.delete_message(chat_id, message_id)
            except Exception:
                pass
        await context.bot.ban_chat_member(chat_id, user_id)
        if failures >= 2:
            await context.bot.send_message(
                chat_id,
                f"🚫 کاربر {user_id} در تلاش دوم هم کپچا را رد نکرد؛ به‌عنوان ربات تشخیص داده شد و از گروه بن شد."
            )
            _captcha_failures.pop(key, None)
        else:
            await context.bot.unban_chat_member(chat_id, user_id, only_if_banned=True)
            await context.bot.send_message(
                chat_id,
                f"⏱️ {reason}. عضو از گروه بیرون انداخته شد؛ فقط یک بار دیگر می‌تواند وارد شود و کپچا را حل کند."
            )
    except Exception as exc:
        log.warning("حذف عضو ناموفق در کپچا: %r", exc)


async def _captcha_timeout(context: ContextTypes.DEFAULT_TYPE, chat_id: int, user_id: int, message_id: int) -> None:
    await asyncio.sleep(_CAPTCHA_TIMEOUT_SECONDS)
    if ((chat_id, user_id) in _pending_captcha
            and _captcha_message_ids.get((chat_id, user_id)) == message_id):
        await _remove_failed_captcha_user(
            context, chat_id, user_id, message_id, reason=f"در مهلت {_CAPTCHA_TIMEOUT_SECONDS} ثانیه‌ای پاسخ ندادی"
        )


async def captcha_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    q = update.callback_query
    if not q or not q.message:
        return
    match = re.fullmatch(r"captcha_(-?\d+)_(\d+)_(-?\d+)", q.data or "")
    if not match:
        await q.answer("این کپچا معتبر نیست.", show_alert=True)
        return
    chat_id, user_id, chosen = int(match.group(1)), int(match.group(2)), int(match.group(3))
    if q.from_user.id != user_id:
        await q.answer("این سؤال برای عضو جدید است 🙂", show_alert=True)
        return
    pending = _pending_captcha.get((chat_id, user_id))
    if pending is None:
        await q.answer("زمان کپچا تمام شده یا این سؤال دیگر معتبر نیست.", show_alert=True)
        return
    member_count, answer = pending
    if chosen != answer:
        await q.answer("جواب غلطه! این تلاش ناموفق حساب می‌شه.", show_alert=True)
        await _remove_failed_captcha_user(context, chat_id, user_id, q.message.message_id, reason="جواب کپچا اشتباه بود")
        return
    try:
        await context.bot.restrict_chat_member(
            chat_id, user_id,
            permissions=ChatPermissions(can_send_messages=True, can_send_audios=True,
                can_send_documents=True, can_send_photos=True, can_send_videos=True,
                can_send_video_notes=True, can_send_voice_notes=True, can_send_polls=True,
                can_send_other_messages=True, can_add_web_page_previews=True),
        )
        _pending_captcha.pop((chat_id, user_id), None)
        _captcha_message_ids.pop((chat_id, user_id), None)
        _captcha_failures.pop((chat_id, user_id), None)
        await q.answer("درسته! خوش اومدی 😎")
        try:
            await q.message.delete()
        except Exception:
            pass
        await send_greeting(context, chat_id, q.from_user, "welcome", member_count)
    except Exception as exc:
        log.warning("تأیید کپچا ناموفق بود: %r", exc)
        await q.answer("نتونستم تأییدت کنم؛ ادمین باید دسترسی ربات رو بررسی کنه.", show_alert=True)


async def error_handler(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    log.error("خطای تلگرام: %r", context.error, exc_info=context.error)


async def post_init(app: Application) -> None:
    # دستورات از فهرست عمومی پنهان‌اند؛ فقط مدیر اصلی در چت خصوصی فهرست می‌بیند.
    await app.bot.set_my_commands([], scope=BotCommandScopeDefault())
    try:
        await app.bot.set_my_commands([
            BotCommand("start", "🏠 شروع"),
            BotCommand("admin", "👑 پنل مدیریت"),
            BotCommand("panel", "⚙️ پنل گروه"),
            BotCommand("ban", "🚫 بن (ریپلای)"),
            BotCommand("cancel", "لغو عملیات"),
        ], scope=BotCommandScopeChat(chat_id=ADMIN_ID))
    except Exception as e:
        log.warning("تنظیم فهرست دستورات مدیر انجام نشد: %r", e)

    # بازیابی زمان‌بندی‌ها پس از راه‌اندازی مجدد
    if app.job_queue is None:
        log.warning("JobQueue در دسترس نیست؛ برای قابلیت‌های زمان‌دار اجرا کنید: pip install -U 'python-telegram-bot[job-queue]'")
        return
    for chat_id in list(data.get("active_groups", [])):
        settings = get_group_settings(int(chat_id))
        if settings.get("locked"):
            until = float(settings.get("locked_until", 0) or 0)
            if until and until > datetime.now().timestamp():
                app.job_queue.run_once(unlock_group_job, when=until - datetime.now().timestamp(),
                                       chat_id=int(chat_id), name=f"unlock_{chat_id}")
            elif until and until <= datetime.now().timestamp():
                # بعد از خاموش بودن ترموکس، قفل منقضی‌شده را هم باز کن و پیام بده.
                await unlock_group_job(
                    type("JobContext", (), {
                        "job": type("Job", (), {"chat_id": int(chat_id)})(),
                        "bot": app.bot,
                        "application": app,
                    })()
                )
        if settings.get("hourly_delete"):
            app.job_queue.run_repeating(hourly_delete_job, interval=3600, first=3600,
                                        chat_id=int(chat_id), name=f"hourly_delete_{chat_id}")
    # هر 30 ثانیه قفل‌های منقضی‌شده را هم بررسی کن؛ این کار پشتیبان JobQueue است.
    _remove_jobs(app.job_queue, "expired_group_lock_watchdog")
    app.job_queue.run_repeating(
        check_expired_group_locks_job, interval=30, first=10,
        name="expired_group_lock_watchdog"
    )
    log.info("ربات «%s» آماده است.", BOT_NAME)


def main() -> None:
    app = (
        Application.builder()
        .token(BOT_TOKEN)
        .connect_timeout(30)
        .read_timeout(30)
        .write_timeout(30)
        .pool_timeout(30)
        .get_updates_connect_timeout(30)
        .get_updates_read_timeout(30)
        .post_init(post_init)
        .build()
    )

    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(CommandHandler("admin", cmd_admin))
    app.add_handler(CommandHandler("panel", cmd_group_panel))
    app.add_handler(CommandHandler("cancel", cmd_cancel))
    app.add_handler(CommandHandler("ban", cmd_ban_reply))

    app.add_handler(CallbackQueryHandler(captcha_callback, pattern=r"^captcha_-?\d+_\d+_-?\d+$"))

    app.add_handler(CallbackQueryHandler(
        admin_callback,
        pattern="^(teach|delete_rule|new_button|list_buttons|manage_groups|clear_memory|stats|list_bans|manage_admins|add_admin|silence_1h|unsilence|back_to_panel|cancel_flow)$",
    ))

    app.add_handler(CallbackQueryHandler(
        group_callback,
        pattern="^(g_toggle_lock|g_lock_menu|g_lock_1h|g_lock_6h|g_lock_24h|g_lock_forever|g_lock_at_time|g_lock_time_(today|tonight|tomorrow|auto)|g_unlock|"
                "g_media_(photo|video|voice|gif|document)|g_delete_50|g_auto_delete_50|g_hourly_delete|"
                "g_silent_menu|g_silent_10m|g_silent_1h|g_silent_6h|g_silent_1d|g_silent_1w|"
                "g_unsilent|g_warn_settings|g_show_warnings|g_set_warn_[1-5]|g_ban_list|g_unban_\\d+|g_stats|g_back|"
                "g_greetings|g_toggle_welcome|g_toggle_goodbye|g_toggle_captcha|g_set_welcome_text|g_set_goodbye_text|"
                "g_set_welcome_gif|g_set_goodbye_gif|g_clear_welcome_gif|g_clear_goodbye_gif|"
                "g_preview_welcome|g_preview_goodbye)$",
    ))

    app.add_handler(MessageHandler(filters.ALL & ~filters.COMMAND, handle_message))
    app.add_error_handler(error_handler)

    log.info("ربات در حال اجرا...")
    app.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()