#!/usr/bin/env python3

import os
import sys
import asyncio
import logging
import json
import time
import random
import aiohttp
import websockets
import collections
import sqlite3
import traceback
from telethon import TelegramClient
from telethon.sessions import StringSession
from aiohttp import web
from typing import Set, Dict, Any, Optional, List, Tuple
from functools import lru_cache
from datetime import datetime, timedelta
from contextlib import asynccontextmanager

# === PARAMETERS TO EDIT ===
ULTRA_MIN_LIQ = 8
ULTRA_BUY_AMOUNT = 0.07
ULTRA_TP_X = 2.0
ULTRA_SL_X = 0.7
ULTRA_MIN_RISES = 2
ULTRA_AGE_MAX_S = 120

SCALPER_BUY_AMOUNT = 0.10
SCALPER_MIN_LIQ = 8
SCALPER_TP_X = 2.0
SCALPER_SL_X = 0.7
SCALPER_TRAIL = 0.2
SCALPER_MAX_POOLAGE = 20 * 60

COMMUNITY_BUY_AMOUNT = 0.04
COMM_HOLDER_THRESHOLD = 250
COMM_MAX_CONC = 0.10
COMM_TP1_MULT = 2.0
COMM_SL_PCT = 0.6
COMM_TRAIL = 0.4
COMM_HOLD_SECONDS = 2 * 24 * 60 * 60
COMM_MIN_SIGNALS = 2

ANTI_SNIPE_DELAY = 2
ML_MIN_SCORE = 60

# Performance settings
CACHE_TTL = 5  # seconds
MAX_CONCURRENT_REQUESTS = 10
API_RETRY_COUNT = 3
API_RETRY_DELAY = 1
CIRCUIT_BREAKER_THRESHOLD = 5
CIRCUIT_BREAKER_TIMEOUT = 60

# === ENV VARS ===
TELEGRAM_API_ID = int(os.environ["TELEGRAM_API_ID"])
TELEGRAM_API_HASH = os.environ["TELEGRAM_API_HASH"]
TELEGRAM_STRING_SESSION = os.environ["TELEGRAM_STRING_SESSION"]
TOXIBOT_USERNAME = os.environ.get("TOXIBOT_USERNAME", "@toxi_solana_bot")
HELIUS_API_KEY = os.environ.get("HELIUS_API_KEY", "")
# Use the exact RPC URL from your Helius dashboard
HELIUS_RPC_URL = os.environ.get("HELIUS_RPC_URL", "https://mainnet.helius-rpc.com/?api-key=0f2e5160-d95a-46d7-a0c4-9a71484ab3d8")
HELIUS_WS_URL = os.environ.get("HELIUS_WS_URL", "wss://mainnet.helius-rpc.com/?api-key=0f2e5160-d95a-46d7-a0c4-9a71484ab3d8")
WALLET_ADDRESS = os.environ.get("WALLET_ADDRESS", "")
BITQUERY_API_KEY = os.environ.get("BITQUERY_API_KEY", "")
PORT = int(os.environ.get("PORT", "8080"))

# Configure logging
sys.stdout.reconfigure(line_buffering=True)
sys.stderr.reconfigure(line_buffering=True)

# Database configuration - use volume for Railway
if os.environ.get('RAILWAY_ENVIRONMENT'):
    DB_PATH = '/data/toxibot.db'
    LOG_PATH = '/data/toxibot.log'
else:
    DB_PATH = 'toxibot.db'
    LOG_PATH = 'toxibot.log'

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s %(levelname)s %(message)s",
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler(LOG_PATH)
    ]
)
logger = logging.getLogger("toxibot")

# ---------------------
# GLOBAL STATE & STATS
# ---------------------
blacklisted_tokens: Set[str] = set()
blacklisted_devs: Set[str] = set()
positions: Dict[str, Dict[str, Any]] = {}
activity_log: collections.deque = collections.deque(maxlen=1000)

# Stats tracking
ultra_wins = 0
ultra_total = 0
ultra_pl = 0.0
scalper_wins = 0
scalper_total = 0
scalper_pl = 0.0
community_wins = 0
community_total = 0
community_pl = 0.0

# Performance tracking
api_failures: Dict[str, int] = collections.defaultdict(int)
api_circuit_breakers: Dict[str, float] = {}
price_cache: Dict[str, Tuple[float, float]] = {}
session_pool: Optional[aiohttp.ClientSession] = None

# Community voting
community_signal_votes = collections.defaultdict(lambda: {"sources": set(), "first_seen": time.time()})
community_token_queue = asyncio.Queue()
recent_rugdevs = set()

# Wallet tracking
current_wallet_balance = 0.0
daily_loss = 0.0
exposure = 0.0

# =====================================
# Database Functions
# =====================================
def init_database():
    """Initialize SQLite database for position persistence"""
    conn = sqlite3.connect(DB_PATH)
    cursor = conn.cursor()
    
    # Positions table
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS positions (
            token TEXT PRIMARY KEY,
            data JSON,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )
    ''')
    
    # Trades history table
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS trades (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            token TEXT,
            action TEXT,
            size REAL,
            price REAL,
            pl REAL,
            timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )
    ''')
    
    # Blacklist table
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS blacklist (
            address TEXT PRIMARY KEY,
            type TEXT,
            reason TEXT,
            timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )
    ''')
    
    conn.commit()
    conn.close()

def save_position(token: str, data: Dict[str, Any]):
    """Save position to database"""
    conn = sqlite3.connect(DB_PATH)
    cursor = conn.cursor()
    cursor.execute('''
        INSERT OR REPLACE INTO positions (token, data, updated_at)
        VALUES (?, ?, CURRENT_TIMESTAMP)
    ''', (token, json.dumps(data)))
    conn.commit()
    conn.close()

def load_positions():
    """Load all positions from database"""
    global positions
    conn = sqlite3.connect(DB_PATH)
    cursor = conn.cursor()
    cursor.execute('SELECT token, data FROM positions')
    for row in cursor.fetchall():
        positions[row[0]] = json.loads(row[1])
    conn.close()
    logger.info(f"Loaded {len(positions)} positions from database")

def record_trade(token: str, action: str, size: float, price: float, pl: float = 0.0):
    """Record trade in history"""
    conn = sqlite3.connect(DB_PATH)
    cursor = conn.cursor()
    cursor.execute('''
        INSERT INTO trades (token, action, size, price, pl)
        VALUES (?, ?, ?, ?, ?)
    ''', (token, action, size, price, pl))
    conn.commit()
    conn.close()

# =====================================
# HTTP Session Management
# =====================================
@asynccontextmanager
async def get_session():
    """Get or create aiohttp session with connection pooling"""
    global session_pool
    if session_pool is None or session_pool.closed:
        timeout = aiohttp.ClientTimeout(total=30)
        connector = aiohttp.TCPConnector(limit=MAX_CONCURRENT_REQUESTS)
        session_pool = aiohttp.ClientSession(timeout=timeout, connector=connector)
    try:
        yield session_pool
    except Exception as e:
        logger.error(f"Session error: {e}")
        raise

# =====================================
# Circuit Breaker Pattern
# =====================================
def is_circuit_broken(service: str) -> bool:
    """Check if circuit breaker is active for a service"""
    if service in api_circuit_breakers:
        if time.time() < api_circuit_breakers[service]:
            return True
        else:
            del api_circuit_breakers[service]
            api_failures[service] = 0
    return False

def trip_circuit_breaker(service: str):
    """Trip the circuit breaker for a service"""
    api_failures[service] += 1
    if api_failures[service] >= CIRCUIT_BREAKER_THRESHOLD:
        api_circuit_breakers[service] = time.time() + CIRCUIT_BREAKER_TIMEOUT
        logger.warning(f"Circuit breaker tripped for {service}")

# =====================================
# Retry Logic
# =====================================
async def retry_with_backoff(func, max_retries=API_RETRY_COUNT):
    """Execute function with exponential backoff retry"""
    for attempt in range(max_retries):
        try:
            return await func()
        except Exception as e:
            if attempt == max_retries - 1:
                raise
            wait_time = API_RETRY_DELAY * (2 ** attempt)
            logger.warning(f"Retry {attempt + 1}/{max_retries} after {wait_time}s: {e}")
            await asyncio.sleep(wait_time)

# =====================================
# Cache Management
# =====================================
def get_cached_price(token: str) -> Optional[float]:
    """Get cached price if still valid"""
    if token in price_cache:
        price, timestamp = price_cache[token]
        if time.time() - timestamp < CACHE_TTL:
            return price
    return None

def cache_price(token: str, price: float):
    """Cache token price"""
    price_cache[token] = (price, time.time())

# =====================================
# Helius RPC Functions (Using your paid API)
# =====================================
async def fetch_wallet_balance() -> Optional[float]:
    """Fetch SOL balance using Helius RPC"""
    if not WALLET_ADDRESS or is_circuit_broken("helius"):
        return None
    
    try:
        async with get_session() as session:
            async def _fetch():
                payload = {
                    "jsonrpc": "2.0",
                    "id": 1,
                    "method": "getBalance",
                    "params": [WALLET_ADDRESS]
                }
                async with session.post(HELIUS_RPC_URL, json=payload) as resp:
                    if resp.status != 200:
                        raise Exception(f"HTTP {resp.status}")
                    data = await resp.json()
                    if "result" in data and "value" in data["result"]:
                        return data["result"]["value"] / 1e9  # Convert lamports to SOL
                    return None
            
            return await retry_with_backoff(_fetch)
    except Exception as e:
        logger.error(f"Failed to fetch wallet balance: {e}")
        trip_circuit_breaker("helius")
        return None

async def get_priority_fee() -> int:
    """Get recommended priority fee using Helius API"""
    if is_circuit_broken("helius"):
        return 5000  # Default priority fee
    
    try:
        async with get_session() as session:
            url = f"https://api.helius.xyz/v0/priority-fee-estimate?api-key={HELIUS_API_KEY}"
            async with session.get(url) as resp:
                if resp.status == 200:
                    data = await resp.json()
                    return int(data.get("priorityFeeEstimate", 5000))
                return 5000
    except Exception:
        return 5000

# =====================================
# DexScreener API Functions (Primary price source)
# =====================================
async def fetch_token_price(token: str) -> Optional[float]:
    """Fetch token price from DexScreener (primary) with Jupiter fallback"""
    # Check cache first
    cached = get_cached_price(token)
    if cached:
        return cached
    
    # Try DexScreener first
    if not is_circuit_broken("dexscreener"):
        try:
            async with get_session() as session:
                url = f"https://api.dexscreener.com/latest/dex/tokens/{token}"
                async with session.get(url) as resp:
                    if resp.status == 200:
                        data = await resp.json()
                        if "pairs" in data and data["pairs"]:
                            # Find SOL pair
                            for pair in data["pairs"]:
                                if pair.get("quoteToken", {}).get("symbol") == "SOL":
                                    price = float(pair.get("priceUsd", 0))
                                    if price > 0:
                                        cache_price(token, price)
                                        return price
        except Exception as e:
            logger.error(f"DexScreener price error for {token}: {e}")
            trip_circuit_breaker("dexscreener")
    
    # Fallback to Jupiter
    if not is_circuit_broken("jupiter"):
        try:
            async with get_session() as session:
                url = f"https://price.jup.ag/v6/price?ids={token}"
                async with session.get(url) as resp:
                    if resp.status == 200:
                        data = await resp.json()
                        if "data" in data and token in data["data"]:
                            price = float(data["data"][token].get("price", 0))
                            if price > 0:
                                cache_price(token, price)
                                return price
        except Exception as e:
            logger.error(f"Jupiter price error for {token}: {e}")
            trip_circuit_breaker("jupiter")
    
    return None

async def fetch_liquidity_and_buyers(token: str) -> Dict[str, Any]:
    """Fetch liquidity and buyer data from DexScreener"""
    if is_circuit_broken("dexscreener"):
        return {"liq": 0, "buyers": 0}
    
    try:
        async with get_session() as session:
            url = f"https://api.dexscreener.com/latest/dex/tokens/{token}"
            async with session.get(url) as resp:
                if resp.status == 200:
                    data = await resp.json()
                    if "pairs" in data and data["pairs"]:
                        # Get the main SOL pair
                        for pair in data["pairs"]:
                            if pair.get("quoteToken", {}).get("symbol") == "SOL":
                                return {
                                    "liq": float(pair.get("liquidity", {}).get("usd", 0)) / 1000,  # Convert to K
                                    "buyers": int(pair.get("txns", {}).get("buys", 0))
                                }
                    return {"liq": 0, "buyers": 0}
    except Exception as e:
        logger.error(f"DexScreener liquidity error: {e}")
        trip_circuit_breaker("dexscreener")
    
    return {"liq": 0, "buyers": 0}

async def fetch_volumes(token: str) -> Dict[str, Any]:
    """Fetch volume data from DexScreener"""
    if is_circuit_broken("dexscreener"):
        return {"liq": 0, "vol_1h": 0, "vol_6h": 0, "base_liq": 0}
    
    try:
        async with get_session() as session:
            url = f"https://api.dexscreener.com/latest/dex/tokens/{token}"
            async with session.get(url) as resp:
                if resp.status == 200:
                    data = await resp.json()
                    if "pairs" in data and data["pairs"]:
                        for pair in data["pairs"]:
                            if pair.get("quoteToken", {}).get("symbol") == "SOL":
                                volume_h24 = float(pair.get("volume", {}).get("h24", 0))
                                return {
                                    "liq": float(pair.get("liquidity", {}).get("usd", 0)) / 1000,
                                    "vol_1h": volume_h24 / 24,  # Estimate
                                    "vol_6h": volume_h24 / 4,   # Estimate
                                    "base_liq": float(pair.get("liquidity", {}).get("base", 0))
                                }
    except Exception as e:
        logger.error(f"DexScreener volume error: {e}")
        trip_circuit_breaker("dexscreener")
    
    return {"liq": 0, "vol_1h": 0, "vol_6h": 0, "base_liq": 0}

async def fetch_pool_age(token: str) -> Optional[int]:
    """Fetch pool age from DexScreener"""
    if is_circuit_broken("dexscreener"):
        return None
    
    try:
        async with get_session() as session:
            url = f"https://api.dexscreener.com/latest/dex/tokens/{token}"
            async with session.get(url) as resp:
                if resp.status == 200:
                    data = await resp.json()
                    if "pairs" in data and data["pairs"]:
                        for pair in data["pairs"]:
                            if pair.get("quoteToken", {}).get("symbol") == "SOL":
                                created_at = pair.get("pairCreatedAt", 0) / 1000  # Convert ms to s
                                if created_at > 0:
                                    return int(time.time() - created_at)
    except Exception as e:
        logger.error(f"DexScreener pool age error: {e}")
        trip_circuit_breaker("dexscreener")
    
    return None

async def fetch_holders_and_conc(token: str) -> Dict[str, Any]:
    """Fetch holder data using Helius DAS API"""
    if is_circuit_broken("helius"):
        return {"holders": 0, "max_holder_pct": 100}
    
    try:
        async with get_session() as session:
            url = f"https://api.helius.xyz/v0/token-metadata?api-key={HELIUS_API_KEY}"
            payload = {"mintAccounts": [token]}
            
            async with session.post(url, json=payload) as resp:
                if resp.status == 200:
                    data = await resp.json()
                    # This is a simplified version - you'd need to implement
                    # proper holder analysis using getTokenAccounts
                    return {"holders": 100, "max_holder_pct": 10}  # Defaults
    except Exception as e:
        logger.error(f"Helius holder data error: {e}")
        trip_circuit_breaker("helius")
    
    return {"holders": 0, "max_holder_pct": 100}

# =====================================
# Utility Functions
# =====================================
def get_total_pl():
    return sum([pos.get("pl", 0) for pos in positions.values()]) + ultra_pl + scalper_pl + community_pl

def calc_winrate():
    total = ultra_total + scalper_total + community_total
    wins = ultra_wins + scalper_wins + community_wins
    return (100.0 * wins / total) if total else 0.0

def estimate_short_vs_long_volume(vol_1h: float, vol_6h: float) -> bool:
    """Estimate if short-term volume is increasing"""
    if vol_6h == 0:
        return False
    hourly_avg = vol_6h / 6
    return vol_1h > hourly_avg * 1.2  # 20% above average

# =====================================
# Data Feeds
# =====================================
async def pumpfun_newtoken_feed(callback):
    """WebSocket feed for new Pump.fun tokens"""
    uri = "wss://pumpportal.fun/api/data"
    retry_count = 0
    max_retries = 10
    
    while retry_count < max_retries:
        try:
            async with websockets.connect(uri) as ws:
                payload = {"method": "subscribeNewToken"}
                await ws.send(json.dumps(payload))
                retry_count = 0
                
                while True:
                    try:
                        msg = await asyncio.wait_for(ws.recv(), timeout=30)
                        data = json.loads(msg)
                        token = data.get("params", {}).get("mint")
                        if token:
                            await callback(token, "pumpfun")
                    except asyncio.TimeoutError:
                        logger.warning("Pump.fun WS timeout, sending ping")
                        await ws.ping()
        except Exception as e:
            retry_count += 1
            wait_time = min(60, 2 ** retry_count)
            logger.error(f"Pump.fun connection error (retry {retry_count}/{max_retries}): {e}")
            await asyncio.sleep(wait_time)

async def bitquery_trending_feed(callback):
    """Bitquery feed for trending tokens - excellent for scalping!"""
    if not BITQUERY_API_KEY:
        logger.warning("Bitquery feed not enabled (no API key).")
        return
    
    if BITQUERY_API_KEY == "disabled":
        logger.info("Bitquery feed disabled by user.")
        return
    
    url = "https://streaming.bitquery.io/graphql"
    query = """
    {
      Solana {
        DEXTrades(
            limit: 10, 
            orderBy: {descending: Block_Time}, 
            tradeAmountUsd: {gt: 100}
        ) {
          transaction { txFrom }
          baseCurrency { address }
          quoteCurrency { symbol }
          tradeAmount
          exchange { fullName }
          Block_Time
        }
      }
    }
    """
    
    payload = {"query": query}
    headers = {
        "Content-Type": "application/json",
        "Authorization": f"Bearer {BITQUERY_API_KEY}"
    }
    
    while True:
        if not is_circuit_broken("bitquery"):
            try:
                async with get_session() as session:  # Fixed: use context manager
                    async def _fetch():
                        async with session.post(url, json=payload, headers=headers) as resp:
                            if resp.status != 200:
                                text = await resp.text()
                                raise Exception(f"HTTP {resp.status}: {text}")
                            
                            data = await resp.json()
                            
                            # Defensive checks to avoid NoneType errors
                            trades = (data or {}).get("data", {}).get("Solana", {}).get("DEXTrades")
                            
                            if not trades or not isinstance(trades, list):
                                logger.error(f"Bitquery: Unexpected or missing DEXTrades: {data}")
                                return
                            
                            logger.info(f"Bitquery: Found {len(trades)} trending tokens")
                            
                            for trade in trades:
                                addr = (trade.get("baseCurrency") or {}).get("address", "")
                                if addr:
                                    logger.info(f"[Bitquery] Trending token: {addr}")
                                    await callback(addr, "bitquery")
                    
                    await retry_with_backoff(_fetch)
            except Exception as e:
                logger.error(f"Bitquery feed error: {e}")
                trip_circuit_breaker("bitquery")
        
        await asyncio.sleep(180)  # Check every 3 minutes

# =====================================
# Community Vote Aggregator
# =====================================
async def community_candidate_callback(token, src):
    """Aggregate community signals from multiple sources"""
    now = time.time()
    if src and token:
        rec = community_signal_votes[token]
        rec["sources"].add(src)
        if "first_seen" not in rec:
            rec["first_seen"] = now
        
        voted = len(rec["sources"])
        logger.info(f"[CommunityBot] {token} in {rec['sources']} ({voted}/{COMM_MIN_SIGNALS})")
        
        if voted >= COMM_MIN_SIGNALS:
            await community_token_queue.put(token)

# =====================================
# ToxiBot Client
# =====================================
class ToxiBotClient:
    def __init__(self, api_id, api_hash, session_id, username):
        self._client = TelegramClient(StringSession(session_id), api_id, api_hash, connection_retries=5)
        self.bot_username = username
        self.send_lock = asyncio.Lock()
    
    async def connect(self):
        await self._client.start()
        logger.info("Connected to ToxiBot (Telegram).")
    
    async def send_buy(self, mint: str, amount: float, price_limit=None):
        async with self.send_lock:
            cmd = f"/buy {mint} {amount}".strip()
            if price_limit:
                cmd += f" limit {price_limit:.7f}"
            logger.info(f"Sending to ToxiBot: {cmd}")
            try:
                return await self._client.send_message(self.bot_username, cmd)
            except Exception as e:
                logger.error(f"Failed to send buy command: {e}")
                raise
    
    async def send_sell(self, mint: str, perc: int = 100):
        async with self.send_lock:
            cmd = f"/sell {mint} {perc}%"
            logger.info(f"Sending to ToxiBot: {cmd}")
            try:
                return await self._client.send_message(self.bot_username, cmd)
            except Exception as e:
                logger.error(f"Failed to send sell command: {e}")
                raise

# =====================================
# Rugcheck Integration
# =====================================
async def rugcheck(token_addr: str) -> Dict[str, Any]:
    """Check token safety using Rugcheck API"""
    if is_circuit_broken("rugcheck"):
        return {}
    
    url = f"https://rugcheck.xyz/api/check/{token_addr}"
    
    try:
        async with get_session() as session:
            async def _fetch():
                async with session.get(url) as resp:
                    if resp.status != 200:
                        raise Exception(f"HTTP {resp.status}")
                    if resp.headers.get('content-type', '').startswith('application/json'):
                        data = await resp.json()
                    else:
                        logger.warning(f"Rugcheck returned HTML for {token_addr}")
                        data = {}
                    logger.info(f"Rugcheck {token_addr}: {data}")
                    return data
            
            return await retry_with_backoff(_fetch)
    except Exception as e:
        logger.error(f"Rugcheck error for {token_addr}: {e}")
        trip_circuit_breaker("rugcheck")
        return {}

def rug_gate(rug: Dict[str, Any]) -> Optional[str]:
    """Check if token passes rug safety checks"""
    if rug.get("label") != "Good":
        return "rugcheck not Good"
    
    if "bundled" in rug.get("supply_type", "").lower():
        if rug.get("mint"):
            blacklisted_tokens.add(rug["mint"])
        if rug.get("authority"):
            blacklisted_devs.add(rug["authority"])
        return "supply bundled"
    
    if rug.get("max_holder_pct", 0) > 25:
        return "too concentrated"
    
    return None

def is_blacklisted(token: str, dev: str = "") -> bool:
    """Check if token or developer is blacklisted"""
    return token in blacklisted_tokens or (dev and dev in blacklisted_devs)

def ml_score_token(meta: Dict[str, Any]) -> float:
    """Placeholder ML scoring - integrate your actual ML model here"""
    random.seed(meta.get("mint", random.random()))
    base_score = random.uniform(60, 90)
    
    if meta.get("liq", 0) > 50:
        base_score += 5
    if meta.get("holders", 0) > 500:
        base_score += 3
    if meta.get("vol_1h", 0) > 10000:
        base_score += 2
    
    return min(97, base_score)

# =====================================
# Trading Strategies
# =====================================
async def ultra_early_handler(token, toxibot):
    """Ultra-early discovery strategy for new tokens"""
    if is_blacklisted(token):
        return
    
    rug = await rugcheck(token)
    if rug_gate(rug):
        activity_log.append(f"[{datetime.now().strftime('%H:%M:%S')}] {token} UltraEarly: Rug gated.")
        return
    
    if token in positions:
        activity_log.append(f"[{datetime.now().strftime('%H:%M:%S')}] {token} UltraEarly: Already traded, skipping.")
        return
    
    # Monitor liquidity rises
    rises, last_liq, last_buyers = 0, 0, 0
    for i in range(3):
        stats = await fetch_liquidity_and_buyers(token)
        if stats['liq'] >= ULTRA_MIN_LIQ and stats['liq'] > last_liq:
            rises += 1
        last_liq, last_buyers = stats['liq'], stats['buyers']
        await asyncio.sleep(2)
    
    if rises < ULTRA_MIN_RISES:
        activity_log.append(f"[{datetime.now().strftime('%H:%M:%S')}] {token} UltraEarly: Liquidity not rapidly rising, skipping.")
        return
    
    entry_price = await fetch_token_price(token) or 0.01
    
    try:
        # Use anti-snipe delay
        await asyncio.sleep(ANTI_SNIPE_DELAY)
        
        await toxibot.send_buy(token, ULTRA_BUY_AMOUNT)
        
        global ultra_total
        ultra_total += 1
        
        positions[token] = {
            "src": "pumpfun",
            "buy_time": time.time(),
            "size": ULTRA_BUY_AMOUNT,
            "ml_score": ml_score_token({"mint": token, "liq": last_liq}),
            "entry_price": entry_price,
            "last_price": entry_price,
            "phase": "filled",
            "pl": 0.0,
            "local_high": entry_price,
            "hard_sl": entry_price * ULTRA_SL_X,
            "runner_trail": 0.3,
            "dev": rug.get("authority")
        }
        
        save_position(token, positions[token])
        record_trade(token, "BUY", ULTRA_BUY_AMOUNT, entry_price)
        activity_log.append(f"[{datetime.now().strftime('%H:%M:%S')}] {token} UltraEarly: BUY {ULTRA_BUY_AMOUNT} @ {entry_price:.5f}")
    except Exception as e:
        logger.error(f"Failed to execute UltraEarly buy: {e}")

async def scalper_handler(token, src, toxibot):
    """Scalper strategy for trending tokens"""
    if is_blacklisted(token):
        return
    
    if token in positions:
        activity_log.append(f"[{datetime.now().strftime('%H:%M:%S')}] {token} [Scalper] Already traded. Skipping.")
        return
    
    pool_stats = await fetch_volumes(token)
    pool_age = await fetch_pool_age(token) or 9999
    
    liq_ok = pool_stats["liq"] >= SCALPER_MIN_LIQ
    vol_ok = estimate_short_vs_long_volume(pool_stats["vol_1h"], pool_stats["vol_6h"])
    age_ok = 0 <= pool_age < SCALPER_MAX_POOLAGE
    
    if not (liq_ok and age_ok and vol_ok):
        activity_log.append(f"[{datetime.now().strftime('%H:%M:%S')}] {token} [Scalper] Entry FAIL: Liq:{liq_ok}, Age:{age_ok}, Vol:{vol_ok}")
        return
    
    rug = await rugcheck(token)
    if rug_gate(rug):
        activity_log.append(f"[{datetime.now().strftime('%H:%M:%S')}] {token} [Scalper] Rug gated.")
        return
    
    entry_price = await fetch_token_price(token) or 0.01
    limit_price = entry_price * 0.97  # 3% slippage limit
    
    try:
        # Get priority fee for faster execution
        priority_fee = await get_priority_fee()
        
        await toxibot.send_buy(token, SCALPER_BUY_AMOUNT, price_limit=limit_price)
        
        global scalper_total
        scalper_total += 1
        
        positions[token] = {
            "src": src,
            "buy_time": time.time(),
            "size": SCALPER_BUY_AMOUNT,
            "ml_score": ml_score_token({
                "mint": token,
                "liq": pool_stats["liq"],
                "vol_1h": pool_stats["vol_1h"]
            }),
            "entry_price": limit_price,
            "last_price": limit_price,
            "phase": "waiting_fill",
            "pl": 0.0,
            "local_high": limit_price,
            "hard_sl": limit_price * SCALPER_SL_X,
            "liq_ref": pool_stats["base_liq"],
            "dev": rug.get("authority"),
        }
        
        save_position(token, positions[token])
        record_trade(token, "BUY", SCALPER_BUY_AMOUNT, limit_price)
        activity_log.append(f"[{datetime.now().strftime('%H:%M:%S')}] {token} Scalper: limit-buy {SCALPER_BUY_AMOUNT} @ {limit_price:.5f}")
    except Exception as e:
        logger.error(f"Failed to execute Scalper buy: {e}")

async def community_trade_manager(toxibot):
    """Community consensus trading strategy"""
    while True:
        try:
            token = await community_token_queue.get()
            
            if is_blacklisted(token):
                continue
            
            rug = await rugcheck(token)
            dev = rug.get("authority")
            
            if rug_gate(rug) or (dev and dev in recent_rugdevs):
                activity_log.append(f"[{datetime.now().strftime('%H:%M:%S')}] {token} [Community] rejected: Ruggate or rugdev.")
                continue
            
            holders_data = await fetch_holders_and_conc(token)
            if holders_data["holders"] < COMM_HOLDER_THRESHOLD or holders_data["max_holder_pct"] > COMM_MAX_CONC:
                activity_log.append(f"[{datetime.now().strftime('%H:%M:%S')}] {token} [Community] fails holder/distribution screen.")
                continue
            
            if token in positions:
                activity_log.append(f"[{datetime.now().strftime('%H:%M:%S')}] {token} [Community] position open. No averaging down.")
                continue
            
            entry_price = await fetch_token_price(token) or 0.01
            
            try:
                await toxibot.send_buy(token, COMMUNITY_BUY_AMOUNT)
                
                global community_total
                community_total += 1
                
                now = time.time()
                positions[token] = {
                    "src": "community",
                    "buy_time": now,
                    "size": COMMUNITY_BUY_AMOUNT,
                    "ml_score": ml_score_token({
                        "mint": token,
                        "holders": holders_data["holders"]
                    }),
                    "entry_price": entry_price,
                    "last_price": entry_price,
                    "phase": "filled",
                    "pl": 0.0,
                    "local_high": entry_price,
                    "hard_sl": entry_price * COMM_SL_PCT,
                    "dev": dev,
                    "hold_until": now + COMM_HOLD_SECONDS
                }
                
                save_position(token, positions[token])
                record_trade(token, "BUY", COMMUNITY_BUY_AMOUNT, entry_price)
                activity_log.append(f"[{datetime.now().strftime('%H:%M:%S')}] {token} [Community] Buy {COMMUNITY_BUY_AMOUNT} @ {entry_price:.6f}")
            except Exception as e:
                logger.error(f"Failed to execute Community buy: {e}")
        except Exception as e:
            logger.error(f"Community trade manager error: {e}")
            await asyncio.sleep(5)

# =====================================
# Process Token
# =====================================
async def process_token(token, src):
    """Route token to appropriate strategy"""
    if src == "pumpfun":
        await ultra_early_handler(token, toxibot)
    elif src in ("bitquery",):  # Removed moralis
        await scalper_handler(token, src, toxibot)

# =====================================
# Position Management
# =====================================
async def update_position_prices_and_wallet():
    """Update position prices and handle exits"""
    global positions, current_wallet_balance, daily_loss, exposure
    
    while True:
        try:
            active_tokens = [token for token, pos in positions.items() if pos.get('size', 0) > 0]
            
            # Update prices in batches
            price_tasks = [fetch_token_price(token) for token in active_tokens]
            prices = await asyncio.gather(*price_tasks, return_exceptions=True)
            
            for token, price in zip(active_tokens, prices):
                if isinstance(price, Exception):
                    logger.warning(f"Price update failed for {token}: {price}")
                    continue
                
                if price and token in positions:
                    pos = positions[token]
                    pos['last_price'] = price
                    pos['local_high'] = max(pos.get("local_high", price), price)
                    pl = (price - pos['entry_price']) * pos['size']
                    pos['pl'] = pl
                    
                    # Handle position exit
                    await handle_position_exit(token, pos, price, toxibot)
            
            # Clean up closed positions
            to_remove = [k for k, v in positions.items() if v.get('size', 0) == 0]
            for k in to_remove:
                daily_loss += positions[k].get('pl', 0)
                del positions[k]
            
            # Update wallet balance
            bal = await fetch_wallet_balance()
            if bal:
                current_wallet_balance = bal
            
            # Calculate exposure
            exposure = sum(pos.get('size', 0) * pos.get('last_price', 0) for pos in positions.values())
            
            await asyncio.sleep(15)
        except Exception as e:
            logger.error(f"Position update error: {e}")
            await asyncio.sleep(30)

async def handle_position_exit(token: str, pos: Dict[str, Any], last_price: float, toxibot):
    """Handle position exit logic based on strategy"""
    try:
        buy_time = pos.get("buy_time", time.time())
        age = time.time() - buy_time
        entry_price = pos["entry_price"]
        src = pos.get("src", "")
        
        # Check if position should be sold
        should_sell = False
        sell_percent = 100
        reason = ""
        
        # Ultra-early strategy exits
        if src == "pumpfun":
            if age > ULTRA_AGE_MAX_S:
                should_sell = True
                reason = "age limit"
            elif last_price >= entry_price * ULTRA_TP_X:
                should_sell = True
                reason = "TP hit"
            elif last_price <= pos["hard_sl"]:
                should_sell = True
                reason = "SL hit"
        
        # Scalper strategy exits
        elif src in ("bitquery",):
            if last_price >= entry_price * SCALPER_TP_X:
                should_sell = True
                sell_percent = 50  # Take partial profits
                reason = "TP hit (partial)"
            elif last_price <= pos["hard_sl"]:
                should_sell = True
                reason = "SL hit"
            elif pos["local_high"] > entry_price * 1.5:
                # Trailing stop activated
                trail_stop = pos["local_high"] * (1 - SCALPER_TRAIL)
                if last_price <= trail_stop:
                    should_sell = True
                    reason = "trailing stop"
        
        # Community strategy exits
        elif src == "community":
            hold_until = pos.get("hold_until", 0)
            if time.time() >= hold_until:
                should_sell = True
                reason = "hold time expired"
            elif last_price >= entry_price * COMM_TP1_MULT:
                should_sell = True
                sell_percent = 50  # Take partial profits
                reason = "TP1 hit (partial)"
            elif last_price <= pos["hard_sl"]:
                should_sell = True
                reason = "SL hit"
        
        # Execute sell if needed
        if should_sell:
            try:
                await toxibot.send_sell(token, sell_percent)
                
                sold_size = pos["size"] * (sell_percent / 100)
                pl = (last_price - entry_price) * sold_size
                
                # Update stats
                if src == "pumpfun":
                    global ultra_wins, ultra_pl
                    if pl > 0:
                        ultra_wins += 1
                    ultra_pl += pl
                elif src in ("bitquery",):
                    global scalper_wins, scalper_pl
                    if pl > 0:
                        scalper_wins += 1
                    scalper_pl += pl
                elif src == "community":
                    global community_wins, community_pl
                    if pl > 0:
                        community_wins += 1
                    community_pl += pl
                
                # Update position
                if sell_percent == 100:
                    pos["size"] = 0
                else:
                    pos["size"] *= (1 - sell_percent / 100)
                
                # Record trade
                record_trade(token, "SELL", sold_size, last_price, pl)
                save_position(token, pos)
                
                activity_log.append(
                    f"[{datetime.now().strftime('%H:%M:%S')}] {token} "
                    f"Sold {sell_percent}% @ {last_price:.6f} ({reason}), "
                    f"P/L: {pl:+.3f} SOL"
                )
                
                # Track rug devs if significant loss
                if pl < -0.05 and pos.get("dev"):
                    recent_rugdevs.add(pos["dev"])
                
            except Exception as e:
                logger.error(f"Failed to execute sell for {token}: {e}")
    
    except Exception as e:
        logger.error(f"Position exit handler error for {token}: {e}")

# =====================================
# Dashboard HTML/JS (unchanged)
# =====================================
DASHBOARD_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>TOXIBOT v2 | TRON INTERFACE</title>
    <style>
        @import url('https://fonts.googleapis.com/css2?family=Orbitron:wght@400;700;900&family=Share+Tech+Mono&display=swap');
        
        * { margin: 0; padding: 0; box-sizing: border-box; }
        
        body { 
            background: #000; 
            color: #00ffff; 
            font-family: 'Orbitron', monospace; 
            overflow-x: hidden; 
            position: relative; 
        }
        
        body::before { 
            content: ""; 
            position: fixed; 
            top: 0; 
            left: 0; 
            width: 100%; 
            height: 100%;
            background-image: 
                linear-gradient(rgba(0, 255, 255, 0.1) 1px, transparent 1px),
                linear-gradient(90deg, rgba(0, 255, 255, 0.1) 1px, transparent 1px);
            background-size: 50px 50px; 
            z-index: -2; 
        }
        
        body::after { 
            content: ""; 
            position: fixed; 
            top: 0; 
            left: 0; 
            width: 100%; 
            height: 100%;
            background: repeating-linear-gradient(
                0deg, transparent, transparent 2px, rgba(0, 255, 255, 0.03) 2px, rgba(0, 255, 255, 0.03) 4px
            ); 
            pointer-events: none; 
            z-index: 1; 
        }
        
        .container { 
            max-width: 1400px; 
            margin: 0 auto; 
            padding: 20px; 
            position: relative; 
            z-index: 2; 
        }
        
        .header { 
            text-align: center; 
            margin-bottom: 30px; 
            position: relative; 
            padding: 30px 0; 
        }
        
        .header::before { 
            content: ""; 
            position: absolute; 
            top: 0; 
            left: -50%; 
            right: -50%; 
            height: 1px;
            background: linear-gradient(90deg, transparent, #00ffff, transparent); 
            animation: scan 3s linear infinite; 
        }
        
        @keyframes scan { 
            0% { transform: translateX(-100%); } 
            100% { transform: translateX(100%); } 
        }
        
        h1 { 
            font-size: 4em; 
            font-weight: 900; 
            text-transform: uppercase; 
            letter-spacing: 0.1em;
            text-shadow: 0 0 10px #00ffff, 0 0 20px #00ffff, 0 0 30px #00ffff, 0 0 40px #0088ff;
            animation: pulse-glow 2s ease-in-out infinite; 
        }
        
        @keyframes pulse-glow { 
            0%, 100% { opacity: 1; } 
            50% { opacity: 0.8; } 
        }
        
        .status-indicator { 
            display: inline-block; 
            padding: 10px 30px; 
            margin-top: 20px; 
            border: 2px solid #00ff00;
            background: rgba(0, 255, 0, 0.1); 
            font-weight: 700; 
            text-transform: uppercase; 
            position: relative; 
            overflow: hidden; 
        }
        
        .status-indicator.active { 
            color: #00ff00; 
            text-shadow: 0 0 10px #00ff00; 
        }
        
        .status-indicator.inactive { 
            border-color: #ff0066; 
            background: rgba(255, 0, 102, 0.1);
            color: #ff0066; 
            text-shadow: 0 0 10px #ff0066; 
        }
        
        .status-indicator::before { 
            content: ""; 
            position: absolute; 
            top: 0; 
            left: -100%; 
            width: 100%; 
            height: 100%;
            background: linear-gradient(90deg, transparent, rgba(255,255,255,0.2), transparent); 
            animation: sweep 3s linear infinite; 
        }
        
        @keyframes sweep { 
            0% { left: -100%; } 
            100% { left: 100%; } 
        }
        
        .metrics-grid { 
            display: grid; 
            grid-template-columns: repeat(auto-fit, minmax(250px, 1fr)); 
            gap: 20px; 
            margin-bottom: 30px; 
        }
        
        .metric-card { 
            background: rgba(0, 20, 40, 0.8); 
            border: 1px solid #00ffff; 
            padding: 20px; 
            position: relative; 
            overflow: hidden; 
            transition: all 0.3s ease; 
        }
        
        .metric-card::before { 
            content: ""; 
            position: absolute; 
            top: 0; 
            left: 0; 
            right: 0; 
            height: 2px;
            background: linear-gradient(90deg, transparent, #00ffff, transparent); 
            animation: slide 2s linear infinite; 
        }
        
        .metric-card:hover { 
            transform: translateY(-5px); 
            box-shadow: 0 10px 30px rgba(0,255,255,0.3); 
            border-color: #00ff00; 
        }
        
        .metric-label { 
            font-size: 0.9em; 
            color: #0088ff; 
            text-transform: uppercase; 
            letter-spacing: 0.1em; 
        }
        
        .metric-value { 
            font-size: 1.8em; 
            font-weight: 700; 
            margin-top: 10px; 
            font-family: 'Share Tech Mono', monospace; 
        }
        
        .metric-value.positive { color: #00ff00; }
        .metric-value.negative { color: #ff0066; }
        
        .bots-section {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(300px, 1fr));
            gap: 20px;
            margin-bottom: 30px;
        }
        
        .bot-card {
            background: rgba(0, 40, 80, 0.6);
            border: 2px solid #0088ff;
            padding: 20px;
            position: relative;
        }
        
        .bot-name {
            font-size: 1.2em;
            font-weight: 700;
            color: #00ffff;
            margin-bottom: 15px;
            text-transform: uppercase;
        }
        
        .bot-stats {
            display: flex;
            flex-direction: column;
            gap: 10px;
        }
        
        .stat-row {
            display: flex;
            justify-content: space-between;
            font-family: 'Share Tech Mono', monospace;
        }
        
        .stat-row span:first-child {
            color: #0088ff;
        }
        
        .stat-row span:last-child {
            color: #00ffff;
            font-weight: 700;
        }
        
        .positions-section {
            margin-bottom: 30px;
        }
        
        .section-title {
            font-size: 1.5em;
            font-weight: 700;
            color: #00ffff;
            margin-bottom: 20px;
            text-transform: uppercase;
            letter-spacing: 0.1em;
        }
        
        .positions-table {
            width: 100%;
            border-collapse: collapse;
            background: rgba(0, 20, 40, 0.6);
        }
        
        .positions-table th,
        .positions-table td {
            padding: 12px;
            text-align: left;
            border-bottom: 1px solid rgba(0, 255, 255, 0.2);
        }
        
        .positions-table th {
            background: rgba(0, 40, 80, 0.8);
            color: #0088ff;
            font-weight: 700;
            text-transform: uppercase;
            font-size: 0.9em;
        }
        
        .positions-table td {
            font-family: 'Share Tech Mono', monospace;
        }
        
        .positions-table tr:hover {
            background: rgba(0, 255, 255, 0.05);
        }
        
        .positive { color: #00ff00; }
        .negative { color: #ff0066; }
        
        /* Position alerts */
        .alert-profit {
            animation: blink-green 1s infinite;
        }
        
        .alert-loss {
            animation: blink-red 1s infinite;
        }
        
        .alert-old {
            animation: blink-yellow 1s infinite;
        }
        
        @keyframes blink-green {
            0%, 50% { background: rgba(0, 255, 0, 0.1); }
            51%, 100% { background: transparent; }
        }
        
        @keyframes blink-red {
            0%, 50% { background: rgba(255, 0, 102, 0.1); }
            51%, 100% { background: transparent; }
        }
        
        @keyframes blink-yellow {
            0%, 50% { background: rgba(255, 170, 0, 0.1); }
            51%, 100% { background: transparent; }
        }
        
        /* Quick stats bar */
        .quick-stats {
            display: flex;
            justify-content: space-around;
            padding: 15px;
            margin-bottom: 20px;
            background: rgba(0, 20, 40, 0.6);
            border: 1px solid #0088ff;
            font-family: 'Share Tech Mono', monospace;
        }
        
        .quick-stats span {
            color: #0088ff;
        }
        
        .quick-stats span span {
            color: #00ffff;
            font-weight: 700;
        }
        
        /* Connection status */
        .connection-status {
            position: absolute;
            top: 10px;
            right: 20px;
            font-size: 0.9em;
            font-family: 'Share Tech Mono', monospace;
        }
        
        .connection-status.connected {
            color: #00ff00;
        }
        
        .connection-status.disconnected {
            color: #ff0066;
            animation: pulse 1s infinite;
        }
        
        @keyframes pulse {
            0%, 100% { opacity: 1; }
            50% { opacity: 0.5; }
        }
        
        /* Log filters */
        .log-filters {
            display: flex;
            gap: 10px;
            margin-bottom: 10px;
        }
        
        .log-filters button {
            padding: 8px 16px;
            background: rgba(0, 40, 80, 0.8);
            border: 1px solid #0088ff;
            color: #00ffff;
            font-family: 'Orbitron', monospace;
            cursor: pointer;
            transition: all 0.3s ease;
            text-transform: uppercase;
            font-size: 0.8em;
        }
        
        .log-filters button:hover {
            background: rgba(0, 80, 160, 0.8);
            border-color: #00ffff;
            transform: translateY(-2px);
        }
        
        .log-filters button.active {
            background: rgba(0, 255, 255, 0.2);
            border-color: #00ff00;
        }
        
        .log-section {
            margin-top: 40px;
        }
        
        .log-container {
            background: rgba(0, 10, 20, 0.9);
            border: 1px solid #0088ff;
            padding: 20px;
            height: 400px;
            overflow-y: auto;
            font-family: 'Share Tech Mono', monospace;
            font-size: 0.9em;
        }
        
        .log-entry {
            margin-bottom: 8px;
            padding: 4px 8px;
            border-left: 3px solid #0088ff;
        }
        
        .log-entry.success {
            border-left-color: #00ff00;
            color: #00ff00;
        }
        
        .log-entry.error {
            border-left-color: #ff0066;
            color: #ff0066;
        }
        
        .log-entry.warning {
            border-left-color: #ffaa00;
            color: #ffaa00;
        }
        
        ::-webkit-scrollbar {
            width: 12px;
        }
        
        ::-webkit-scrollbar-track {
            background: rgba(0, 20, 40, 0.8);
            border: 1px solid #0088ff;
        }
        
        ::-webkit-scrollbar-thumb {
            background: #0088ff;
            border: 1px solid #00ffff;
        }
        
        ::-webkit-scrollbar-thumb:hover {
            background: #00ffff;
        }
    </style>
</head>
<body>
    <div class="container">
        <div class="header">
            <h1>TOXIBOT v2.0</h1>
            <div id="status" class="status-indicator active">SYSTEM ACTIVE</div>
            <div class="connection-status connected" id="connection-status">● Connected</div>
        </div>
        
        <div class="metrics-grid">
            <div class="metric-card">
                <div class="metric-label">Wallet Balance</div>
                <div class="metric-value positive" id="wallet">0.00 SOL</div>
            </div>
            <div class="metric-card">
                <div class="metric-label">Total P/L</div>
                <div class="metric-value" id="total-pl">+0.000</div>
            </div>
            <div class="metric-card">
                <div class="metric-label">Win Rate</div>
                <div class="metric-value" id="winrate">0.0%</div>
            </div>
            <div class="metric-card">
                <div class="metric-label">Active Positions</div>
                <div class="metric-value" id="positions-count">0</div>
            </div>
            <div class="metric-card">
                <div class="metric-label">Exposure</div>
                <div class="metric-value" id="exposure">0.000 SOL</div>
            </div>
            <div class="metric-card">
                <div class="metric-label">Daily Loss</div>
                <div class="metric-value negative" id="daily-loss">0.000 SOL</div>
            </div>
        </div>
        
        <div class="quick-stats">
            <span>🔥 Best Trade: <span id="best-trade">+0.000</span></span>
            <span>💀 Worst Trade: <span id="worst-trade">-0.000</span></span>
            <span>📊 Today's Trades: <span id="todays-trades">0</span></span>
            <span>⚡ Active Feeds: <span id="active-feeds">3</span></span>
        </div>
        
        <div class="bots-section">
            <div class="bot-card">
                <div class="bot-name">Ultra-Early Discovery</div>
                <div class="bot-stats">
                    <div class="stat-row">
                        <span>Trades</span>
                        <span id="ultra-trades">0/0</span>
                    </div>
                    <div class="stat-row">
                        <span>Win Rate</span>
                        <span id="ultra-winrate">0%</span>
                    </div>
                    <div class="stat-row">
                        <span>P/L</span>
                        <span id="ultra-pl">+0.000</span>
                    </div>
                </div>
            </div>
            
            <div class="bot-card">
                <div class="bot-name">2-Minute Scalper</div>
                <div class="bot-stats">
                    <div class="stat-row">
                        <span>Trades</span>
                        <span id="scalper-trades">0/0</span>
                    </div>
                    <div class="stat-row">
                        <span>Win Rate</span>
                        <span id="scalper-winrate">0%</span>
                    </div>
                    <div class="stat-row">
                        <span>P/L</span>
                        <span id="scalper-pl">+0.000</span>
                    </div>
                </div>
            </div>
            
            <div class="bot-card">
                <div class="bot-name">Community/Whale</div>
                <div class="bot-stats">
                    <div class="stat-row">
                        <span>Trades</span>
                        <span id="community-trades">0/0</span>
                    </div>
                    <div class="stat-row">
                        <span>Win Rate</span>
                        <span id="community-winrate">0%</span>
                    </div>
                    <div class="stat-row">
                        <span>P/L</span>
                        <span id="community-pl">+0.000</span>
                    </div>
                </div>
            </div>
        </div>
        
        <div class="positions-section">
            <h2 class="section-title">Active Positions</h2>
            <table class="positions-table">
                <thead>
                    <tr>
                        <th>Token</th>
                        <th>Source</th>
                        <th>Size</th>
                        <th>Entry</th>
                        <th>Current</th>
                        <th>P/L</th>
                        <th>P/L %</th>
                        <th>Phase</th>
                        <th>Age</th>
                    </tr>
                </thead>
                <tbody id="positions-tbody"></tbody>
            </table>
        </div>
        
        <div class="log-section">
            <h2 class="section-title">System Activity</h2>
            <div class="log-filters">
                <button class="active" onclick="filterLog('all')">All</button>
                <button onclick="filterLog('buys')">Buys</button>
                <button onclick="filterLog('sells')">Sells</button>
                <button onclick="filterLog('errors')">Errors</button>
                <button onclick="filterLog('skipped')">Skipped</button>
            </div>
            <div class="log-container" id="log-container"></div>
        </div>
    </div>
    
    <script>
        // Fix WebSocket URL for Railway deployment
        const wsProtocol = location.protocol === 'https:' ? 'wss:' : 'ws:';
        const wsUrl = `${wsProtocol}//${location.host}/ws`;
        console.log('Connecting to WebSocket:', wsUrl);
        const ws = new WebSocket(wsUrl);
        
        let lastUpdate = Date.now();
        let allLogs = [];
        let currentFilter = 'all';
        let bestTrade = 0;
        let worstTrade = 0;
        let todaysTrades = 0;
        
        ws.onopen = function() {
            console.log('WebSocket connected!');
            document.getElementById('connection-status').className = 'connection-status connected';
            document.getElementById('connection-status').textContent = '● Connected';
        };
        
        ws.onerror = function(error) {
            console.error('WebSocket error:', error);
            document.getElementById('connection-status').className = 'connection-status disconnected';
            document.getElementById('connection-status').textContent = '● Connection Error';
        };
        
        function formatNumber(num, decimals = 3) {
            return parseFloat(num || 0).toFixed(decimals);
        }
        
        function formatAge(seconds) {
            if (!seconds) return '';
            const d = Math.floor(seconds / 86400);
            const h = Math.floor((seconds % 86400) / 3600);
            const m = Math.floor((seconds % 3600) / 60);
            const s = Math.floor(seconds % 60);
            
            const parts = [];
            if (d) parts.push(`${d}d`);
            if (h) parts.push(`${h}h`);
            if (m) parts.push(`${m}m`);
            if (s && !d && !h) parts.push(`${s}s`);
            
            return parts.join(' ') || '0s';
        }
        
        function filterLog(filter) {
            currentFilter = filter;
            document.querySelectorAll('.log-filters button').forEach(btn => btn.classList.remove('active'));
            event.target.classList.add('active');
            updateLogDisplay();
        }
        
        function updateLogDisplay() {
            const logContainer = document.getElementById('log-container');
            let filtered = allLogs;
            
            if (currentFilter !== 'all') {
                filtered = allLogs.filter(entry => {
                    if (currentFilter === 'buys') return entry.includes('BUY');
                    if (currentFilter === 'sells') return entry.includes('Sold');
                    if (currentFilter === 'errors') return entry.includes('SL') || entry.includes('blacklist') || entry.includes('rejected');
                    if (currentFilter === 'skipped') return entry.includes('skipping') || entry.includes('FAIL');
                    return true;
                });
            }
            
            logContainer.innerHTML = filtered.map(entry => {
                let className = 'log-entry';
                if (entry.includes('BUY') || entry.includes('Sold')) className += ' success';
                else if (entry.includes('SL') || entry.includes('blacklist')) className += ' error';
                else if (entry.includes('skipping') || entry.includes('FAIL')) className += ' warning';
                return `<div class="${className}">${entry}</div>`;
            }).join('');
            logContainer.scrollTop = logContainer.scrollHeight;
        }
        
        // Connection status monitor
        setInterval(() => {
            const timeSinceUpdate = Date.now() - lastUpdate;
            const indicator = document.getElementById('connection-status');
            if (timeSinceUpdate > 5000) {
                indicator.className = 'connection-status disconnected';
                indicator.textContent = '● Disconnected';
            } else {
                indicator.className = 'connection-status connected';
                indicator.textContent = '● Connected';
            }
        }, 1000);
        
        ws.onmessage = function(event) {
            lastUpdate = Date.now();
            const data = JSON.parse(event.data);
            
            // Update status
            const statusEl = document.getElementById('status');
            const isActive = data.status && data.status.toLowerCase().includes('active');
            statusEl.className = `status-indicator ${isActive ? 'active' : 'inactive'}`;
            statusEl.textContent = isActive ? 'SYSTEM ACTIVE' : 'SYSTEM OFFLINE';
            
            // Update metrics
            document.getElementById('wallet').textContent = `${formatNumber(data.wallet_balance, 2)} SOL`;
            document.getElementById('total-pl').textContent = `${data.pl >= 0 ? '+' : ''}${formatNumber(data.pl)}`;
            document.getElementById('total-pl').className = `metric-value ${data.pl >= 0 ? 'positive' : 'negative'}`;
            document.getElementById('winrate').textContent = `${formatNumber(data.winrate, 1)}%`;
            document.getElementById('positions-count').textContent = Object.keys(data.positions || {}).length;
            document.getElementById('exposure').textContent = `${formatNumber(data.exposure)} SOL`;
            document.getElementById('daily-loss').textContent = `${formatNumber(data.daily_loss)} SOL`;
            
            // Update bot stats
            document.getElementById('ultra-trades').textContent = `${data.ultra_wins}/${data.ultra_total}`;
            document.getElementById('ultra-winrate').textContent = 
                `${data.ultra_total ? formatNumber(100 * data.ultra_wins / data.ultra_total, 1) : 0}%`;
            document.getElementById('ultra-pl').textContent = `${data.ultra_pl >= 0 ? '+' : ''}${formatNumber(data.ultra_pl)}`;
            document.getElementById('ultra-pl').className = data.ultra_pl >= 0 ? 'positive' : 'negative';
            
            document.getElementById('scalper-trades').textContent = `${data.scalper_wins}/${data.scalper_total}`;
            document.getElementById('scalper-winrate').textContent = 
                `${data.scalper_total ? formatNumber(100 * data.scalper_wins / data.scalper_total, 1) : 0}%`;
            document.getElementById('scalper-pl').textContent = `${data.scalper_pl >= 0 ? '+' : ''}${formatNumber(data.scalper_pl)}`;
            document.getElementById('scalper-pl').className = data.scalper_pl >= 0 ? 'positive' : 'negative';
            
            document.getElementById('community-trades').textContent = `${data.community_wins}/${data.community_total}`;
            document.getElementById('community-winrate').textContent = 
                `${data.community_total ? formatNumber(100 * data.community_wins / data.community_total, 1) : 0}%`;
            document.getElementById('community-pl').textContent = 
                `${data.community_pl >= 0 ? '+' : ''}${formatNumber(data.community_pl)}`;
            document.getElementById('community-pl').className = data.community_pl >= 0 ? 'positive' : 'negative';
            
            // Update quick stats
            todaysTrades = data.ultra_total + data.scalper_total + data.community_total;
            document.getElementById('todays-trades').textContent = todaysTrades;
            
            // Calculate best/worst trades from positions
            Object.values(data.positions || {}).forEach(pos => {
                const pl = pos.pl || 0;
                if (pl > bestTrade) bestTrade = pl;
                if (pl < worstTrade) worstTrade = pl;
            });
            
            document.getElementById('best-trade').textContent = `${bestTrade >= 0 ? '+' : ''}${formatNumber(bestTrade)}`;
            document.getElementById('best-trade').className = bestTrade >= 0 ? 'positive' : 'negative';
            document.getElementById('worst-trade').textContent = `${worstTrade >= 0 ? '+' : ''}${formatNumber(worstTrade)}`;
            document.getElementById('worst-trade').className = worstTrade >= 0 ? 'positive' : 'negative';
            
            // Update positions table with alerts
            const tbody = document.getElementById('positions-tbody');
            tbody.innerHTML = '';
            const now = Date.now() / 1000;
            
            Object.entries(data.positions || {}).forEach(([token, pos]) => {
                const entry = parseFloat(pos.entry_price || 0);
                const last = parseFloat(pos.last_price || entry);
                const size = parseFloat(pos.size || 0);
                const pl = (last - entry) * size;
                const plPct = entry ? 100 * (last - entry) / entry : 0;
                const age = now - (pos.buy_time || now);
                
                const row = tbody.insertRow();
                
                // Add alert classes
                if (plPct >= 50) row.classList.add('alert-profit');
                else if (plPct <= -20) row.classList.add('alert-loss');
                else if (age > 3600) row.classList.add('alert-old');
                
                row.innerHTML = `
                    <td style="color: #00ffff">${token.slice(0, 6)}...${token.slice(-4)}</td>
                    <td>${pos.src || ''}</td>
                    <td>${formatNumber(size)}</td>
                    <td>${formatNumber(entry, 6)}</td>
                    <td>${formatNumber(last, 6)}</td>
                    <td class="${pl >= 0 ? 'positive' : 'negative'}">${formatNumber(pl, 4)}</td>
                    <td class="${plPct >= 0 ? 'positive' : 'negative'}">${formatNumber(plPct, 2)}%</td>
                    <td>${pos.phase || ''}</td>
                    <td>${formatAge(age)}</td>
                `;
            });
            
            // Update activity log
            allLogs = data.log || [];
            updateLogDisplay();
        };
        
        ws.onclose = function() {
            setTimeout(() => { location.reload(); }, 5000);
        };
        
        // Keyboard shortcuts
        document.addEventListener('keydown', (e) => {
            if (e.key === 'r' && e.ctrlKey) {
                e.preventDefault();
                location.reload();
            }
            if (e.key === 'c' && e.ctrlKey) {
                e.preventDefault();
                allLogs = [];
                updateLogDisplay();
            }
        });
    </script>
</body>
</html>
"""

# =====================================
# Dashboard HTTP and WebSocket
# =====================================
async def html_handler(request):
    return web.Response(text=DASHBOARD_HTML, content_type="text/html")

async def ws_handler(request):
    ws = web.WebSocketResponse()
    await ws.prepare(request)
    logger.info("WebSocket client connected!")
    
    while True:
        try:
            data = {
                "status": "active",
                "wallet_balance": current_wallet_balance,
                "pl": get_total_pl(),
                "winrate": calc_winrate(),
                "positions": positions,
                "exposure": exposure,
                "daily_loss": daily_loss,
                "log": list(activity_log)[-40:],
                "ultra_wins": ultra_wins,
                "ultra_total": ultra_total,
                "ultra_pl": ultra_pl,
                "scalper_wins": scalper_wins,
                "scalper_total": scalper_total,
                "scalper_pl": scalper_pl,
                "community_wins": community_wins,
                "community_total": community_total,
                "community_pl": community_pl,
            }
            
            await ws.send_str(json.dumps(data))
            await asyncio.sleep(2)
        except Exception as e:
            logger.error(f"WS send error: {e}")
            break
    
    return ws

async def health_handler(request):
    """Health check endpoint for monitoring"""
    health_data = {
        "status": "healthy",
        "uptime": time.time() - startup_time,
        "active_positions": len(positions),
        "total_pl": get_total_pl(),
        "wallet_balance": current_wallet_balance,
        "circuit_breakers": list(api_circuit_breakers.keys())
    }
    return web.json_response(health_data)

async def run_dashboard_server():
    app = web.Application()
    app.router.add_get('/', html_handler)
    app.router.add_get('/ws', ws_handler)
    app.router.add_get('/health', health_handler)
    
    runner = web.AppRunner(app)
    await runner.setup()
    site = web.TCPSite(runner, port=PORT)
    await site.start()
    logger.info(f"Dashboard up at http://0.0.0.0:{PORT}")
    
    while True:
        await asyncio.sleep(3600)  # Keep running

# =====================================
# Main Bot Event Loop
# =====================================
async def bot_main():
    global toxibot
    
    # Initialize database
    init_database()
    load_positions()
    
    # Connect to ToxiBot
    toxibot = ToxiBotClient(
        TELEGRAM_API_ID,
        TELEGRAM_API_HASH,
        TELEGRAM_STRING_SESSION,
        TOXIBOT_USERNAME
    )
    await toxibot.connect()
    
    # Start all feeds and managers
    feeds = [
        # New token discovery
        pumpfun_newtoken_feed(lambda token, src: asyncio.create_task(process_token(token, src))),
        
        # Trending tokens (replaced Moralis with Bitquery)
        bitquery_trending_feed(lambda token, src: asyncio.create_task(process_token(token, src))),
        
        # Community consensus trading
        community_trade_manager(toxibot),
        
        # Position management
        update_position_prices_and_wallet()
    ]
    
    # Add community signal aggregation from Bitquery
    asyncio.create_task(bitquery_trending_feed(community_candidate_callback))
    
    await asyncio.gather(*feeds)

# =====================================
# Cleanup on Exit
# =====================================
async def cleanup():
    """Clean up resources on exit"""
    global session_pool
    
    logger.info("Shutting down...")
    
    # Close HTTP session
    if session_pool and not session_pool.closed:
        await session_pool.close()
    
    # Save final positions
    for token, pos in positions.items():
        save_position(token, pos)
    
    logger.info("Cleanup complete")

# =====================================
# Entry Point
# =====================================
startup_time = time.time()

async def main():
    # Set up signal handlers for graceful shutdown
    import signal
    signal.signal(signal.SIGINT, lambda s, f: asyncio.create_task(cleanup()))
    signal.signal(signal.SIGTERM, lambda s, f: asyncio.create_task(cleanup()))
    
    task_dashboard = asyncio.create_task(run_dashboard_server())
    task_bot = asyncio.create_task(bot_main())
    
    try:
        await asyncio.gather(task_dashboard, task_bot)
    except Exception as e:
        logger.error(f"Fatal error: {e}")
        await cleanup()

if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        logger.info("Interrupted by user")
    except Exception as e:
        logger.error(f"Unhandled exception: {e}")
        traceback.print_exc()
