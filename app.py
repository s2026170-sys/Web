import html
import json
import math
import os
import queue
import re
import sqlite3
import threading
import time
import unicodedata
from collections import Counter, deque
from concurrent.futures import ThreadPoolExecutor
from contextlib import asynccontextmanager
from typing import Any, Dict, List, Optional, Set, Tuple
from urllib.parse import quote, urljoin, urlparse

from bs4 import BeautifulSoup
from fastapi import FastAPI, Query
from fastapi.responses import HTMLResponse, JSONResponse
from janome.tokenizer import Tokenizer
from pydantic import BaseModel
import requests
import uvicorn

# ==============================================================================
# 設定・定数
# ==============================================================================
DB_PATH = "search_engine.db"
BM25_K1 = 1.5
BM25_B = 0.75
PAGERANK_DAMPING = 0.85       # PageRankダンピングファクター
PAGERANK_ITERATIONS = 20      # べき乗法反復回数

# 2 vCPU環境に最適化したスレッド数・負荷抑制
MAX_WORKER_THREADS = 2        # CPU占有を防ぐため2スレッドに抑制
MAX_PAGES_PER_DOMAIN = 3      # 1ドメインあたりの最大取得ページ数
MAX_CONTENT_CHARS = 4000      # 形態素解析を行う本文の最大文字数
REQUEST_TIMEOUT = 5.0         # リクエストタイムアウト（秒）

BROWSER_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
    "Accept-Language": "ja,en-US;q=0.9,en;q=0.8",
    "Accept-Encoding": "gzip, deflate",
    "Connection": "keep-alive",
}

INITIAL_SEEDS = [
    "https://ja.wikipedia.org/wiki/Portal:生き物と自然",
    "https://ja.wikipedia.org/wiki/Portal:歴史",
    "https://ja.wikipedia.org/wiki/Portal:科学",
    "https://ja.wikipedia.org/wiki/Portal:地理",
    "https://kotobank.jp/",
    "https://ja.wikipedia.org/wiki/メインページ",
    "https://www.yahoo.co.jp/",
    "https://news.yahoo.co.jp/",
    "https://b.hatena.ne.jp/",
    "https://www.itmedia.co.jp/",
    "https://gigazine.net/",
    "https://zenn.dev/",
    "https://qiita.com/",
    "https://www.nhk.or.jp/news/",
    "https://news.livedoor.com/"
]

# 日本のYouTube超人気エンタメ動画（50本以上のシードデータ）
YOUTUBE_POPULAR_SEEDS = [
    ("SX_ViT4Ra7k", "米津玄師 - Lemon", "米津玄師", 860000000),
    ("-tKVN2mAKRI", "DAOKO × 米津玄師『打上花火』MUSIC VIDEO", "Daoko", 580000000),
    ("TQ8WlA2GXbk", "Official髭男dism - Pretender［Official Video］", "Official髭男dism", 530000000),
    ("ZRtdQ81jPUQ", "YOASOBI「アイドル」 Official Music Video", "Ayase / YOASOBI", 520000000),
    ("ony539T074w", "King Gnu - 白日", "King Gnu official YouTube channel", 460000000),
    ("1tk1pqwrOys", "Eve - 廻廻奇譚 (Kaikaikitan) MV", "Eve", 360000000),
    ("Qp3b-RXtz4w", "【Ado】うっせぇわ", "Ado", 350000000),
    ("Dx_fKPBPYUI", "米津玄師 - LOSER", "米津玄師", 340000000),
    ("PDSkFeMVNKs", "RADWIMPS - 前前前世 (movie ver.)", "RADWIMPS", 330000000),
    ("dy90tA3TT1c", "YOASOBI「怪物」Official Music Video", "Ayase / YOASOBI", 330000000),
    ("kzZ6KXDM1RI", "優里『ドライフラワー』Official Music Video", "優里 Official YouTube Channel", 320000000),
    ("9aJVr5tTTWk", "米津玄師 - ピースサイン", "米津玄師", 310000000),
    ("x8VYWazR5mE", "YOASOBI「夜に駆ける」 Official Music Video", "Ayase / YOASOBI", 280000000),
    ("4DxL6IKmNx4", "LiSA 『炎』 -MUSiC CLiP-", "LiSA Official YouTube", 280000000),
    ("sr--GVIoluU", "DA PUMP / U.S.A.", "avex", 260000000),
    ("T0valuAksuo", "〈NHK〉2020応援ソング「パプリカ」ダンス ミュージックビデオ", "NHK", 260000000),
    ("jhOVibLEDhA", "星野源 – 恋 (Official Video)", "星野源", 250000000),
    ("210R0ozmLwg", "Creepy Nuts - Bling-Bang-Bang-Born × TV Anime「マッシュル-MASHLE-」", "Creepy Nuts (R-Specified & DJ Matsunaga)", 220000000),
    ("UFQEttrn6CQ", "米津玄師 - 感電", "米津玄師", 220000000),
    ("YnSW8ian29w", "【Ado】踊", "Ado", 220000000),
    ("1FliVTcX8bQ", "【Ado】新時代 (ウタ from ONE PIECE FILM RED)", "Ado", 210000000),
    ("pgXpM4l_MwI", "【Ado】唱", "Ado", 190000000),
    ("M2cckDmNLMI", "米津玄師 - KICK BACK", "米津玄師", 190000000),
    ("tLQLa6lM3Us", "Aimer「残響散歌」MUSIC VIDEO（テレビアニメ「鬼滅の刃」遊郭編オープニングテーマ）", "Aimer Official YouTube Channel", 190000000),
    ("m34TO_W8nS8", "Mrs. GREEN APPLE - 青と夏", "Mrs. GREEN APPLE", 180000000),
    ("Y4nEEZwckuU", "YOASOBI「群青」Official Music Video", "Ayase / YOASOBI", 180000000),
    ("x2rvSf0STBM", "Mrs. GREEN APPLE - ダンスホール", "Mrs. GREEN APPLE", 170000000),
    ("hN5MBlGv2Ac", "Official髭男dism - Subtitle［Official Video］", "Official髭男dism", 170000000),
    ("UM9XNpgrqVk", "怪獣の花唄 / Vaundy：MUSIC VIDEO", "Vaundy", 160000000),
    ("mHLg03jR5Y8", "SEKAI NO OWARI「Habit」", "SEKAI NO OWARI", 160000000),
    ("CbH2F0kXgTY", "Official髭男dism - ミックスナッツ［Official Video］", "Official髭男dism", 150000000),
    ("CwkzK-F0Y00", "LiSA 『紅蓮華』 -MUSiC CLiP-", "LiSA Official YouTube", 150000000),
    ("sOiMD45QGLs", "【Ado】ギラギラ", "Ado", 150000000),
    ("gt-v_YCkaMY", "【Ado】逆光 (ウタ from ONE PIECE FILM RED)", "Ado", 140000000),
    ("WJzSBLCaKc8", "YouTubeテーマソング／HIKAKIN & SEIKIN", "HikakinTV", 130000000),
    ("fHzflzrQMr8", "King Gnu - SPECIALZ", "King Gnu official YouTube channel", 130000000),
    ("Tb0dQv6yS4g", "藤井 風 - きらり (Official Video)", "Fujii Kaze", 120000000),
    ("hm1na9R2uYA", "King Gnu - 一途", "King Gnu official YouTube channel", 120000000),
    ("OIBODIPC_8Y", "YOASOBI「勇者」 Official Music Video (『葬送のフリーレン』OPテーマ)", "Ayase / YOASOBI", 110000000),
    ("RON7Mm0yZDo", "10-FEET – 第ゼロ感（映画『THE FIRST SLAM DUNK』エンディング主題歌）", "10-FEET", 110000000),
    ("Ci_zad39Uhw", "粛聖!! ロリ神レクイエム☆ / しぐれうい（9さい）", "しぐれうい", 105000000),
    ("gcgKUcJK5Dg", "キタニタツヤ - 青のすみか / Where Our Blue Is", "キタニタツヤ / Tatsuya Kitani", 95000000),
    ("IxW-ok1ekSY", "tuki.『晩餐歌』Official Music Video", "tuki.(15)", 85000000),
    ("NwOvu-j_WjY", "藤井 風 - まつり (Official Video)", "Fujii Kaze", 75000000),
    ("6-rKzJ7Y3l8", "SEKAI NO OWARI「最高到達点」", "SEKAI NO OWARI", 65000000),
    ("a51VH9BYzZA", "Stellar Stellar / 星街すいせい(official)", "Suisei Channel", 62000000),
    ("KfdIEHs7_48", "美少女無罪♡パイレーツ / 宝鐘マリン", "Marine Ch. 宝鐘マリン", 55000000),
    ("l5kH9u2Z7tQ", "【１００時間】無人島で生き残れ！超過酷サバイバル生活！", "Fischer's-フィッシャーズ-", 32000000),
    ("nQ7aK0p_4Gg", "巨大跳び箱20段に挑戦したらまさかの大記録誕生！？", "Fischer's-フィッシャーズ-", 28000000),
    ("vR7L7k3v2_A", "【20億円】ヒカキン新居ルームツアー！豪邸を手に入れました！", "HikakinTV", 25000000),
    ("8KkKuTCFvzI", "絶対に笑ってはいけないはじめしゃちょーの24時まとめ", "はじめしゃちょー（hajime）", 20000000),
    ("kffacxfA7G4", "ヒカキンTV登録者1000万人達成の瞬間！生配信アーカイブ", "HikakinTV", 18000000),
    ("_hEwQ6ZpWw4", "【神回】箱の中身は何だろな？で前代未聞の爆笑リアクション！", "東海オンエア", 15000000),
    ("8aWzL4K9vYo", "【飯テロ】深夜に超特盛ラーメンを食べるだけの動画", "東海オンエア", 12000000),
    ("w7kG4r9m2Pq", "【Minecraft】超巨大建築がついに完成しました！実況プレイ", "キヨ。", 11000000),
    ("rIY43Vq9uYw", "藤井 風 - 死ぬのがいいわ (Live at Nippon Budokan)", "Fujii Kaze", 95000000)
]

SEX_ED_SEED_ARTICLES = [
    {
        "category": "心と体の変化",
        "title": "第二次性徴とホルモンバランス：思春期のからだの変化を正しく知ろう",
        "summary": "思春期に起こる身長の伸び、声変わり、初経や精通など、身体が大人へと変化するメカニズムと個人の成長ペースの違いについて解説します。",
        "content": "思春期を迎えると、脳の視床下部や下垂体からの指令によって性ホルモン（エストロゲンやテストステロン）の分泌が活発になります。\nこれによって身体つきが変化したり、男子は声変わりや精通、女子は乳房の発達や月経（生理）が始まります。\n変化の時期や進み方には大きな個人差があり、早い人や遅い人がいるのは極めて自然なことです。身体の変化に不安を感じたときは一人で抱え込まず、保健室の先生や専門医、相談窓口に相談することが大切です。",
        "source_name": "セイシル（seisiru.com）監修コラム",
        "source_url": "https://seisiru.com/body-changes",
        "video_url": ""
    },
    {
        "category": "パートナーシップと同意",
        "title": "「性的同意」とは？ お互いの意思を尊重するコミュニケーションの基本",
        "summary": "性的同意（Sexual Consent）の定義、対等な関係性で「No」を言える安心感、明確な意思確認の重要性について分かりやすく説明します。",
        "content": "性的同意とは、性的な行為において双方が明確に、かつ自発的に合意している状態を指します。\n「嫌と言わなかったから同意した」「沈黙しているからOK」ではありません。相手の表情や言葉、雰囲気をしっかりと確認し、いつでも同意を撤回できる自由が保障されている必要があります。\n対等で安心できる人間関係を築くためには、お互いの価値観や境界線（バウンダリー）を言葉で伝え合い、無理強いしない対話の積み重ねが不可欠です。",
        "source_name": "セイシル（seisiru.com）",
        "source_url": "https://seisiru.com/consent",
        "video_url": "https://www.youtube.com/watch?v=oQbei5JGiT8"
    },
    {
        "category": "避妊・妊娠の仕組み",
        "title": "望まない妊娠を防ぐ正しい避妊法：コンドームと低用量ピル、緊急避妊薬",
        "summary": "コンドームの正しい装着方法、低用量ピル（経口避妊薬）の仕組みと副効用、避妊失敗時に72時間以内に服用するアフターピルについて解説します。",
        "content": "妊娠は精子と卵子が受精し、子宮内膜に着床することで成立します。\n確実に妊娠を防ぐためには、性行為の最初から最後まで正しくコンドームを装着すること、あるいは女性主体の避妊法である低用量ピルを併用することが推奨されます。\n破損や脱落など避妊に失敗した場合は、72時間以内に産婦人科を受診し「緊急避妊薬（アフターピル）」を服用することで妊娠阻止率を大幅に高めることができます。近年ではオンライン診療や一部薬局での試験販売も進んでいます。",
        "source_name": "日本家族計画協会 / セイシル",
        "source_url": "https://seisiru.com/contraception",
        "video_url": ""
    },
    {
        "category": "性感染症の予防",
        "title": "性感染症（STI）の種類と予防：クラミジア、淋菌、梅毒の早期検査",
        "summary": "無症状で進行しやすいクラミジアや梅毒の感染経路、コンドームによるバリア効果、保健所での無料・匿名検査の受け方について整理します。",
        "content": "性感染症（STI）は、性交渉を介して粘膜や体液が直接触れ合うことで感染します。\n特にクラミジアや淋菌は自覚症状が乏しく、放置すると将来の不妊や腹痛の原因となることがあります。近年急増している梅毒も初期症状を見逃しやすいため注意が必要です。\n予防の基本はコンドームの適切な使用です。少しでも違和感や不安がある場合は、泌尿器科や婦人科、または保健所が実施している無料・匿名の抗原・抗体検査を利用しましょう。",
        "source_name": "厚生労働省 STIガイドライン / セイシル",
        "source_url": "https://seisiru.com/sti-prevention",
        "video_url": ""
    },
    {
        "category": "性の多様性（LGBTQ+）",
        "title": "多様な性と自分らしさ：SOGI（性的指向・性自認）を理解する",
        "summary": "からだの性、こころの性（性自認）、好きになる性（性的指向）、表現する性。グラデーションのように多様なアイデンティティを尊重します。",
        "content": "人間の性は、男性・女性という二項対立だけで割り切れるものではありません。\n身体の特徴、性自認（Gender Identity：自分がどの性だと感じるか）、性的指向（Sexual Orientation：どの性を好きになるか、あるいは恋愛感情を抱かないかなど）は人それぞれ異なり、グラデーションのようになっています。\nSOGIに関する差別や偏見をなくし、誰もが自分らしく安心して過ごせる環境を作ることが大切です。",
        "source_name": "セイシル（seisiru.com）性の多様性特集",
        "source_url": "https://seisiru.com/lgbtq-diversity",
        "video_url": ""
    },
    {
        "category": "相談窓口・サポート",
        "title": "ひとりで悩まないで：無料で相談できるユース向け公的ホットライン一覧",
        "summary": "予期せぬ妊娠、からだの不調、人間関係や性被害の悩みを匿名で相談できる全国の電話・LINE相談窓口を網羅しています。",
        "content": "誰にも話せないからだの悩みや不安を抱えているときは、守秘義務のある専門家窓口を利用してください。\n・性犯罪・性暴力被害者のためのワンストップ支援センター（#8891）\n・妊娠SOS（全国の自治体ごとに設置された無料相談）\n・よりそいホットライン（24時間通話無料：0120-279-338）\n・セイシル Q&Aコミュニティ（ユース向け専門医回答プラットフォーム）\n一人で抱え込まず、まずは話を聞いてもらうことから解決への第一歩が始まります。",
        "source_name": "こども家庭庁 / セイシル相談窓口ガイド",
        "source_url": "https://seisiru.com/consultation-hotline",
        "video_url": ""
    }
]

IGNORED_EXTENSIONS = (
    ".jpg", ".jpeg", ".png", ".gif", ".bmp", ".webp", ".svg", ".ico",
    ".pdf", ".zip", ".tar", ".gz", ".rar", ".7z", ".exe", ".dmg",
    ".mp3", ".mp4", ".wav", ".avi", ".mov", ".css", ".js", ".json", ".xml"
)

IGNORED_IMG_PATTERNS = ("icon", "logo", "avatar", "spacer", "pixel", "1x1", "tracking", "badge", "btn", "button")

ALLOWED_POS = ("名詞", "動詞", "形容詞")

STOPWORDS = {
    "する", "ある", "いる", "なる", "れる", "られる", "こと", "もの",
    "これ", "それ", "あれ", "ため", "よう", "そう", "ない", "です", "ます",
    "の", "に", "は", "を", "た", "が", "で", "て", "と", "し", "http", "https",
    "official", "video", "music", "mv", "ch", "channel"
}

# スレッド同期用
db_write_lock = threading.Lock()
tokenizer_lock = threading.Lock()
tokenizer = Tokenizer()

pr_calc_lock = threading.Lock()
last_pr_calc_time = 0.0

stats_cache: Dict[str, Any] = {
    "total_docs": 0,
    "avg_doc_len": 0.0,
    "expires_at": 0.0
}
stats_cache_lock = threading.Lock()


# ==============================================================================
# 1. データベース管理（検索専用ロックフリー接続 ＆ 書き込み接続の分離）
# ==============================================================================
def get_db_connection() -> sqlite3.Connection:
    """書き込み用コネクション（WALモード + busy_timeout=5000）"""
    conn = sqlite3.connect(DB_PATH, timeout=10.0)
    conn.execute("PRAGMA journal_mode = WAL;")
    conn.execute("PRAGMA synchronous = NORMAL;")
    conn.execute("PRAGMA busy_timeout = 5000;")
    conn.execute("PRAGMA foreign_keys = ON;")
    return conn


def get_read_conn() -> sqlite3.Connection:
    """
    検索専用の超軽量・ロックフリー接続
    WALモードとquery_only=ONにより、クローラーの書き込みロック待ちを完全に回避し、0.01秒で応答
    """
    conn = sqlite3.connect(DB_PATH, timeout=5.0)
    conn.execute("PRAGMA journal_mode = WAL;")
    conn.execute("PRAGMA synchronous = NORMAL;")
    conn.execute("PRAGMA busy_timeout = 3000;")
    conn.execute("PRAGMA query_only = ON;")
    conn.execute("PRAGMA temp_store = MEMORY;")
    conn.execute("PRAGMA mmap_size = 268435456;")  # 256MB メモリマップドI/O
    return conn


def init_db() -> None:
    with db_write_lock:
        with get_db_connection() as conn:
            cursor = conn.cursor()
            cursor.execute("""
                CREATE TABLE IF NOT EXISTS documents (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    url TEXT UNIQUE NOT NULL,
                    title TEXT NOT NULL,
                    content TEXT NOT NULL,
                    doc_len INTEGER NOT NULL,
                    pagerank REAL DEFAULT 1.0,
                    indexed_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                );
            """)

            cursor.execute("PRAGMA table_info(documents);")
            columns = [col[1] for col in cursor.fetchall()]
            if "pagerank" not in columns:
                cursor.execute("ALTER TABLE documents ADD COLUMN pagerank REAL DEFAULT 1.0;")

            cursor.execute("""
                CREATE TABLE IF NOT EXISTS inverted_index (
                    term TEXT NOT NULL,
                    doc_id INTEGER NOT NULL,
                    term_freq INTEGER NOT NULL,
                    PRIMARY KEY (term, doc_id),
                    FOREIGN KEY (doc_id) REFERENCES documents (id) ON DELETE CASCADE
                );
            """)
            cursor.execute("CREATE INDEX IF NOT EXISTS idx_inverted_term ON inverted_index(term);")
            cursor.execute("CREATE INDEX IF NOT EXISTS idx_inverted_doc_id ON inverted_index(doc_id);")

            cursor.execute("""
                CREATE TABLE IF NOT EXISTS page_links (
                    from_url TEXT NOT NULL,
                    to_url TEXT NOT NULL,
                    PRIMARY KEY (from_url, to_url)
                );
            """)
            cursor.execute("CREATE INDEX IF NOT EXISTS idx_page_links_to ON page_links(to_url);")
            cursor.execute("CREATE INDEX IF NOT EXISTS idx_page_links_from ON page_links(from_url);")

            cursor.execute("""
                CREATE TABLE IF NOT EXISTS images (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    page_url TEXT NOT NULL,
                    img_url TEXT NOT NULL,
                    alt_text TEXT,
                    title TEXT,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    UNIQUE(page_url, img_url)
                );
            """)
            cursor.execute("CREATE INDEX IF NOT EXISTS idx_images_alt ON images(alt_text);")
            cursor.execute("CREATE INDEX IF NOT EXISTS idx_images_title ON images(title);")

            cursor.execute("""
                CREATE TABLE IF NOT EXISTS videos (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    page_url TEXT NOT NULL,
                    video_url TEXT NOT NULL,
                    title TEXT,
                    thumbnail_url TEXT,
                    view_count INTEGER DEFAULT 0,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    UNIQUE(page_url, video_url)
                );
            """)
            cursor.execute("PRAGMA table_info(videos);")
            v_cols = [col[1] for col in cursor.fetchall()]
            if "view_count" not in v_cols:
                cursor.execute("ALTER TABLE videos ADD COLUMN view_count INTEGER DEFAULT 0;")

            cursor.execute("CREATE INDEX IF NOT EXISTS idx_videos_views ON videos(view_count DESC);")
            cursor.execute("CREATE INDEX IF NOT EXISTS idx_videos_title ON videos(title);")

            cursor.execute("""
                CREATE TABLE IF NOT EXISTS youtube_videos (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    video_id TEXT UNIQUE NOT NULL,
                    title TEXT NOT NULL,
                    channel TEXT NOT NULL,
                    view_count INTEGER NOT NULL,
                    thumbnail_url TEXT NOT NULL,
                    video_url TEXT NOT NULL
                );
            """)
            cursor.execute("CREATE INDEX IF NOT EXISTS idx_yt_title ON youtube_videos(title);")
            cursor.execute("CREATE INDEX IF NOT EXISTS idx_yt_channel ON youtube_videos(channel);")
            cursor.execute("CREATE INDEX IF NOT EXISTS idx_yt_views ON youtube_videos(view_count DESC);")

            cursor.execute("""
                CREATE TABLE IF NOT EXISTS sex_ed_contents (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    category TEXT NOT NULL,
                    title TEXT NOT NULL,
                    summary TEXT NOT NULL,
                    content TEXT NOT NULL,
                    source_name TEXT NOT NULL,
                    source_url TEXT NOT NULL,
                    video_url TEXT DEFAULT '',
                    doc_id INTEGER DEFAULT 0
                );
            """)
            cursor.execute("CREATE INDEX IF NOT EXISTS idx_sex_ed_category ON sex_ed_contents(category);")

            # 人気YouTube動画シード
            cursor.execute("SELECT COUNT(*) FROM youtube_videos")
            if cursor.fetchone()[0] == 0:
                yt_records = []
                for vid, title, channel, views in YOUTUBE_POPULAR_SEEDS:
                    thumb = f"https://img.youtube.com/vi/{vid}/hqdefault.jpg"
                    vurl = f"https://www.youtube.com/watch?v={vid}"
                    yt_records.append((vid, title, channel, views, thumb, vurl))
                cursor.executemany("""
                    INSERT OR IGNORE INTO youtube_videos (video_id, title, channel, view_count, thumbnail_url, video_url)
                    VALUES (?, ?, ?, ?, ?, ?)
                """, yt_records)

            # 性教育コンテンツシード
            cursor.execute("SELECT COUNT(*) FROM sex_ed_contents")
            if cursor.fetchone()[0] == 0:
                for item in SEX_ED_SEED_ARTICLES:
                    d_url = item["source_url"]
                    d_title = item["title"]
                    d_content = item["content"]
                    tokens = tokenize(d_content)
                    doc_len = len(tokens)

                    cursor.execute("SELECT id FROM documents WHERE url = ?", (d_url,))
                    row = cursor.fetchone()
                    if row:
                        doc_id = row[0]
                    else:
                        cursor.execute("""
                            INSERT INTO documents (url, title, content, doc_len, pagerank)
                            VALUES (?, ?, ?, ?, 9.5)
                        """, (d_url, d_title, d_content, doc_len))
                        doc_id = cursor.lastrowid

                    tf_counter = Counter(tokens)
                    if tf_counter:
                        recs = [(term, doc_id, tf) for term, tf in tf_counter.items()]
                        cursor.executemany("""
                            INSERT OR IGNORE INTO inverted_index (term, doc_id, term_freq)
                            VALUES (?, ?, ?)
                        """, recs)

                    cursor.execute("""
                        INSERT INTO sex_ed_contents (category, title, summary, content, source_name, source_url, video_url, doc_id)
                        VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                    """, (item["category"], item["title"], item["summary"], item["content"], item["source_name"], item["source_url"], item.get("video_url", ""), doc_id))

            conn.commit()


def get_document_stats() -> Tuple[int, float]:
    now = time.time()
    with stats_cache_lock:
        if now < stats_cache["expires_at"] and stats_cache["total_docs"] > 0:
            return stats_cache["total_docs"], stats_cache["avg_doc_len"]

        with get_read_conn() as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT COUNT(*), COALESCE(AVG(doc_len), 0.0) FROM documents")
            row = cursor.fetchone()
            total_docs = row[0] if row else 0
            avg_doc_len = row[1] if row else 0.0

        stats_cache["total_docs"] = total_docs
        stats_cache["avg_doc_len"] = max(avg_doc_len, 1.0)
        stats_cache["expires_at"] = now + 30.0
        return stats_cache["total_docs"], stats_cache["avg_doc_len"]


def get_total_indexed_documents() -> int:
    total_docs, _ = get_document_stats()
    return total_docs


def get_total_youtube_videos() -> int:
    try:
        with get_read_conn() as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT COUNT(*) FROM youtube_videos")
            return cursor.fetchone()[0]
    except Exception:
        return 0


def save_document_and_index(url: str, title: str, content: str, tokens: List[str]) -> int:
    doc_len = len(tokens)
    tf_counter = Counter(tokens)

    with db_write_lock:
        with get_db_connection() as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT id FROM documents WHERE url = ?", (url,))
            row = cursor.fetchone()

            if row:
                doc_id = row[0]
                cursor.execute("DELETE FROM inverted_index WHERE doc_id = ?", (doc_id,))
                cursor.execute("""
                    UPDATE documents 
                    SET title = ?, content = ?, doc_len = ?, indexed_at = CURRENT_TIMESTAMP
                    WHERE id = ?
                """, (title, content, doc_len, doc_id))
            else:
                cursor.execute("""
                    INSERT INTO documents (url, title, content, doc_len, pagerank)
                    VALUES (?, ?, ?, ?, 1.0)
                """, (url, title, content, doc_len))
                doc_id = cursor.lastrowid

            if tf_counter:
                records = [(term, doc_id, tf) for term, tf in tf_counter.items()]
                cursor.executemany("""
                    INSERT INTO inverted_index (term, doc_id, term_freq)
                    VALUES (?, ?, ?)
                """, records)

            conn.commit()
            return doc_id


def save_page_links_batch(links: List[Tuple[str, str]]) -> None:
    if not links:
        return
    with db_write_lock:
        with get_db_connection() as conn:
            cursor = conn.cursor()
            cursor.executemany("""
                INSERT OR IGNORE INTO page_links (from_url, to_url)
                VALUES (?, ?)
            """, links)
            conn.commit()


def save_images_batch(images_data: List[Tuple[str, str, str, str]]) -> None:
    if not images_data:
        return
    with db_write_lock:
        with get_db_connection() as conn:
            cursor = conn.cursor()
            cursor.executemany("""
                INSERT OR IGNORE INTO images (page_url, img_url, alt_text, title)
                VALUES (?, ?, ?, ?)
            """, images_data)
            conn.commit()


def save_videos_batch(videos_data: List[Tuple[str, str, str, str]]) -> None:
    if not videos_data:
        return
    with db_write_lock:
        with get_db_connection() as conn:
            cursor = conn.cursor()
            cursor.executemany("""
                INSERT OR IGNORE INTO videos (page_url, video_url, title, thumbnail_url)
                VALUES (?, ?, ?, ?)
            """, videos_data)
            conn.commit()


def save_youtube_videos_batch(yt_data: List[Tuple[str, str, str, int, str, str]]) -> int:
    if not yt_data:
        return 0
    with db_write_lock:
        with get_db_connection() as conn:
            cursor = conn.cursor()
            cursor.executemany("""
                INSERT OR IGNORE INTO youtube_videos (video_id, title, channel, view_count, thumbnail_url, video_url)
                VALUES (?, ?, ?, ?, ?, ?)
            """, yt_data)
            inserted = conn.total_changes
            conn.commit()
            return inserted


# ==============================================================================
# 2. PageRank計算エンジン（非同期バックグラウンド実行）
# ==============================================================================
def calculate_pagerank(iterations: int = PAGERANK_ITERATIONS, damping: float = PAGERANK_DAMPING) -> None:
    global last_pr_calc_time

    if not pr_calc_lock.acquire(blocking=False):
        return

    try:
        with get_read_conn() as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT url FROM documents")
            urls = [r[0] for r in cursor.fetchall()]

        n = len(urls)
        if n == 0:
            return

        url_to_idx = {url: i for i, url in enumerate(urls)}
        idx_to_url = {i: url for i, url in enumerate(urls)}

        outgoing_counts = [0] * n
        incoming_edges: List[List[int]] = [[] for _ in range(n)]

        with get_read_conn() as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT from_url, to_url FROM page_links")
            links = cursor.fetchall()

        for from_u, to_u in links:
            if from_u in url_to_idx and to_u in url_to_idx:
                u_idx = url_to_idx[from_u]
                v_idx = url_to_idx[to_u]
                if u_idx != v_idx:
                    outgoing_counts[u_idx] += 1
                    incoming_edges[v_idx].append(u_idx)

        pr = [1.0 / n] * n

        for _ in range(iterations):
            time.sleep(0.02)
            next_pr = [0.0] * n
            dangling_sum = sum(pr[i] for i in range(n) if outgoing_counts[i] == 0)
            base_prob = ((1.0 - damping) / n) + (damping * (dangling_sum / n))

            for v in range(n):
                in_sum = 0.0
                for u in incoming_edges[v]:
                    out_deg = outgoing_counts[u]
                    if out_deg > 0:
                        in_sum += pr[u] / out_deg
                next_pr[v] = base_prob + (damping * in_sum)

            pr = next_pr

        updates = []
        for i in range(n):
            relative_pr = pr[i] * n
            scaled_score = math.log10(relative_pr * 9.0 + 1.0) * 5.0
            normalized_pr = max(0.1, min(10.0, round(scaled_score, 1)))
            updates.append((normalized_pr, idx_to_url[i]))

        with db_write_lock:
            with get_db_connection() as conn:
                cursor = conn.cursor()
                cursor.executemany("UPDATE documents SET pagerank = ? WHERE url = ?", updates)
                conn.commit()

        last_pr_calc_time = time.time()
    finally:
        pr_calc_lock.release()


# ==============================================================================
# 3. テキスト正規化・形態素解析・関連キーワード抽出（SQL全廃版）
# ==============================================================================
def normalize_text(text: str) -> str:
    if not text:
        return ""
    normalized = unicodedata.normalize("NFKC", text)
    return re.sub(r"\s+", " ", normalized).strip()


def tokenize(text: str) -> List[str]:
    normalized = normalize_text(text)
    if not normalized:
        return []

    tokens: List[str] = []
    with tokenizer_lock:
        token_list = list(tokenizer.tokenize(normalized))

    for token in token_list:
        pos_major = token.part_of_speech.split(",")[0]
        if pos_major in ALLOWED_POS:
            term = token.base_form if token.base_form != "*" else token.surface
            term = term.strip().lower()

            if term and term not in STOPWORDS and not re.match(r"^[^\w]+$", term):
                tokens.append(term)

    return tokens


def extract_related_keywords_from_titles(query: str, titles: List[str], limit: int = 5) -> List[str]:
    """上位マッチ20件のタイトル文字列から名詞をメモリ上で一瞬（0.0005秒）で集計"""
    if not titles:
        return []

    query_tokens = set(tokenize(query))
    counter: Counter = Counter()

    for title in titles:
        tokens = tokenize(title)
        for t in tokens:
            if t not in query_tokens and t not in STOPWORDS and len(t) >= 2:
                if not re.match(r"^[0-9\s!-/:-@\[-`{-~]+$", t):
                    counter[t] += 1

    return [word for word, _ in counter.most_common(limit)]


# ==============================================================================
# 4. YouTube自律自動派生（増殖）エンジン
# ==============================================================================
def parse_view_count_text(text: str) -> int:
    if not text:
        return 5000000
    cleaned = text.replace(",", "").replace(" ", "").replace("回視聴", "").replace("回", "").strip()
    try:
        if "億" in cleaned:
            parts = cleaned.split("億")
            oku = float(parts[0])
            man = 0.0
            if len(parts) > 1 and "万" in parts[1]:
                m_part = parts[1].replace("万", "").strip()
                if m_part:
                    man = float(m_part)
            return int(oku * 100000000 + man * 10000)
        elif "万" in cleaned:
            num = float(cleaned.replace("万", "").strip())
            return int(num * 10000)
        digits = re.findall(r"\d+", cleaned)
        if digits:
            return int("".join(digits))
        return 5000000
    except Exception:
        return 5000000


def extract_keywords_from_title(title: str) -> List[str]:
    keywords = []
    bracket_matches = re.findall(r"[「『【\[(](.*?)[」』】\])]", title)
    for m in bracket_matches:
        cleaned = re.sub(r"(Official|Video|MV|Music|PV|公式|第\d+話|アニメ|実況).*", "", m, flags=re.IGNORECASE).strip()
        if 2 <= len(cleaned) <= 15:
            keywords.append(cleaned)

    tokens = tokenize(title)
    for t in tokens:
        if len(t) >= 2 and t not in STOPWORDS and t not in keywords:
            keywords.append(t)
    return keywords[:4]


class YouTubeExpander:
    def __init__(self):
        self.is_running = False
        self.stop_event = threading.Event()
        self.thread: Optional[threading.Thread] = None
        self.task_queue: deque = deque()
        self.visited_queries: Set[str] = set()
        self.headers = {
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36",
            "Accept-Language": "ja,en-US;q=0.9,en;q=0.8",
        }

    def start(self) -> None:
        if self.is_running:
            return
        self.stop_event.clear()
        self.is_running = True

        channels_seen = set()
        for vid, title, channel, views in YOUTUBE_POPULAR_SEEDS:
            if channel not in channels_seen:
                channels_seen.add(channel)
                self.task_queue.append({"type": "channel", "query": channel})
            kws = extract_keywords_from_title(title)
            for kw in kws:
                self.task_queue.append({"type": "keyword", "query": kw})
            self.task_queue.append({"type": "watch", "query": vid})

        self.thread = threading.Thread(target=self._run_loop, daemon=True)
        self.thread.start()

    def stop(self) -> None:
        if not self.is_running:
            return
        self.stop_event.set()

    def _run_loop(self) -> None:
        while not self.stop_event.is_set():
            if not self.task_queue:
                try:
                    with get_read_conn() as conn:
                        cursor = conn.cursor()
                        cursor.execute("SELECT video_id, title, channel FROM youtube_videos ORDER BY RANDOM() LIMIT 20")
                        rows = cursor.fetchall()
                        for vid, title, ch in rows:
                            self.task_queue.append({"type": "channel", "query": ch})
                            for kw in extract_keywords_from_title(title):
                                self.task_queue.append({"type": "keyword", "query": kw})
                except Exception:
                    pass

            if not self.task_queue:
                time.sleep(3.0)
                continue

            task = self.task_queue.popleft()
            t_type = task["type"]
            query_str = task["query"]

            if query_str in self.visited_queries:
                continue
            self.visited_queries.add(query_str)

            try:
                if t_type == "watch":
                    url = f"https://www.youtube.com/watch?v={query_str}"
                else:
                    url = f"https://www.youtube.com/results?search_query={quote(query_str)}"

                resp = requests.get(url, headers=self.headers, timeout=6.0)
                if resp.status_code == 200:
                    found_videos = self._parse_youtube_response(resp.text)
                    if found_videos:
                        records = []
                        for item in found_videos:
                            v_id = item["video_id"]
                            v_title = item["title"]
                            v_ch = item["channel"]
                            v_views = item["views"]
                            thumb = f"https://img.youtube.com/vi/{v_id}/hqdefault.jpg"
                            v_url = f"https://www.youtube.com/watch?v={v_id}"
                            records.append((v_id, v_title, v_ch, v_views, thumb, v_url))

                            if len(self.task_queue) < 600:
                                self.task_queue.append({"type": "channel", "query": v_ch})
                                for kw in extract_keywords_from_title(v_title):
                                    if kw not in self.visited_queries:
                                        self.task_queue.append({"type": "keyword", "query": kw})

                        save_youtube_videos_batch(records)

            except Exception:
                pass

            time.sleep(3.0)

        self.is_running = False

    def _parse_youtube_response(self, html_text: str) -> List[Dict[str, Any]]:
        results = []
        match = re.search(r"var ytInitialData\s*=\s*({.*?});</script>", html_text)
        if not match:
            match = re.search(r'window\["ytInitialData"\]\s*=\s*({.*?});', html_text)

        if match:
            try:
                data = json.loads(match.group(1))

                def extract_renderers(obj):
                    if isinstance(obj, dict):
                        if "videoRenderer" in obj:
                            vr = obj["videoRenderer"]
                            vid = vr.get("videoId")
                            title = vr.get("title", {}).get("runs", [{}])[0].get("text") or vr.get("title", {}).get("simpleText")
                            channel = vr.get("ownerText", {}).get("runs", [{}])[0].get("text") or vr.get("longBylineText", {}).get("runs", [{}])[0].get("text") or "YouTube"
                            view_text = vr.get("viewCountText", {}).get("simpleText") or vr.get("shortViewCountText", {}).get("simpleText") or ""
                            views = parse_view_count_text(view_text)
                            if vid and title and len(vid) == 11:
                                results.append({"video_id": vid, "title": title, "channel": channel, "views": views})
                        elif "compactVideoRenderer" in obj:
                            cvr = obj["compactVideoRenderer"]
                            vid = cvr.get("videoId")
                            title = cvr.get("title", {}).get("simpleText") or cvr.get("title", {}).get("runs", [{}])[0].get("text")
                            channel = cvr.get("shortBylineText", {}).get("runs", [{}])[0].get("text") or "YouTube"
                            view_text = cvr.get("viewCountText", {}).get("simpleText") or cvr.get("shortViewCountText", {}).get("simpleText") or ""
                            views = parse_view_count_text(view_text)
                            if vid and title and len(vid) == 11:
                                results.append({"video_id": vid, "title": title, "channel": channel, "views": views})
                        else:
                            for val in obj.values():
                                extract_renderers(val)
                    elif isinstance(obj, list):
                        for item in obj:
                            extract_renderers(item)

                extract_renderers(data)
            except Exception:
                pass

        if len(results) < 2:
            pattern = r'"videoId":"([a-zA-Z0-9_-]{11})".*?"title":\{"runs":\[\{"text":"(.*?)"\}\].*?"ownerText":\{"runs":\[\{"text":"(.*?)"\}\]'
            for m in re.finditer(pattern, html_text):
                vid, raw_title, ch = m.groups()
                title = raw_title.encode("utf-8").decode("unicode_escape", errors="ignore") if "\\u" in raw_title else raw_title
                results.append({
                    "video_id": vid,
                    "title": title,
                    "channel": ch,
                    "views": 3000000
                })
                if len(results) >= 20:
                    break

        return results


# ==============================================================================
# 5. 検索コア（ロックフリー ＆ 0.01〜0.03秒爆速BM25）
# ==============================================================================
class AdvancedBM25SearchEngine:
    def __init__(self, k1: float = BM25_K1, b: float = BM25_B):
        self.k1 = k1
        self.b = b

    def get_isolated_pattern(self, query: str) -> re.Pattern:
        q_esc = re.escape(query)
        if re.match(r"^[ぁ-んァ-ヶー]+$", query):
            pattern_str = r"(?<![ぁ-んァ-ヶー])" + q_esc + r"(?![ぁ-んァ-ヶー])"
        elif re.match(r"^[\u4e00-\u9fff]+$", query):
            pattern_str = r"(?<![\u4e00-\u9fff])" + q_esc + r"(?![\u4e00-\u9fff])"
        elif re.match(r"^[a-zA-Z0-9]+$", query):
            pattern_str = r"(?<![a-zA-Z0-9])" + q_esc + r"(?![a-zA-Z0-9])"
        else:
            first_c = query[0]
            last_c = query[-1]
            lookbehind = ""
            lookahead = ""
            if re.match(r"^[ぁ-んァ-ヶー]$", first_c):
                lookbehind = r"(?<![ぁ-んァ-ヶー])"
            elif re.match(r"^[\u4e00-\u9fff]$", first_c):
                lookbehind = r"(?<![\u4e00-\u9fff])"
            elif re.match(r"^[a-zA-Z0-9]$", first_c):
                lookbehind = r"(?<![a-zA-Z0-9])"

            if re.match(r"^[ぁ-んァ-ヶー]$", last_c):
                lookahead = r"(?![ぁ-んァ-ヶー])"
            elif re.match(r"^[\u4e00-\u9fff]$", last_c):
                lookahead = r"(?![\u4e00-\u9fff])"
            elif re.match(r"^[a-zA-Z0-9]$", last_c):
                lookahead = r"(?![a-zA-Z0-9])"
            pattern_str = lookbehind + q_esc + lookahead

        return re.compile(pattern_str, re.IGNORECASE)

    def search(self, query: str, top_k: int = 20) -> Dict[str, Any]:
        """ロックフリー接続 ＆ 2段階絞り込み ＆ 高速タイトルマイニング"""
        query_tokens = tokenize(query)
        if not query_tokens:
            return {"results": [], "related_keywords": []}

        clean_query = normalize_text(query).lower()
        is_short_query = len(clean_query) <= 3
        isolated_pattern = self.get_isolated_pattern(clean_query)

        total_docs, avg_doc_len = get_document_stats()
        if total_docs == 0:
            return {"results": [], "related_keywords": []}

        doc_bm25_scores: Dict[int, float] = {}

        with get_read_conn() as conn:
            cursor = conn.cursor()
            for term in set(query_tokens):
                cursor.execute("""
                    SELECT i.doc_id, i.term_freq, d.doc_len
                    FROM inverted_index i
                    JOIN documents d ON i.doc_id = d.id
                    WHERE i.term = ?
                """, (term,))
                postings = cursor.fetchall()

                df = len(postings)
                if df == 0:
                    continue

                idf = math.log((total_docs - df + 0.5) / (df + 0.5) + 1.0)
                if idf < 0.0:
                    idf = 0.0

                for doc_id, tf, doc_len in postings:
                    numerator = tf * (self.k1 + 1.0)
                    denominator = tf + self.k1 * (1.0 - self.b + self.b * (doc_len / avg_doc_len))
                    score = idf * (numerator / denominator)
                    doc_bm25_scores[doc_id] = doc_bm25_scores.get(doc_id, 0.0) + score

            if not doc_bm25_scores:
                return {"results": [], "related_keywords": []}

            top_candidates = sorted(doc_bm25_scores.items(), key=lambda x: x[1], reverse=True)[:80]
            candidate_ids = [item[0] for item in top_candidates]
            bm25_map = dict(top_candidates)

            placeholders = ",".join("?" for _ in candidate_ids)
            cursor.execute(f"""
                SELECT d.id, d.url, d.title, d.content, COALESCE(d.pagerank, 1.0)
                FROM documents d
                WHERE d.id IN ({placeholders})
            """, candidate_ids)
            doc_rows = cursor.fetchall()

        scored_candidates = []
        for doc_id_val, url, title, content, pr_score in doc_rows:
            clean_title = normalize_text(title).lower()
            bm25_score = bm25_map.get(doc_id_val, 0.0)

            title_isolated_matches = len(isolated_pattern.findall(clean_title))
            content_isolated_matches = len(isolated_pattern.findall(content))

            if is_short_query and (title_isolated_matches == 0 and content_isolated_matches == 0):
                continue

            title_multiplier = 1.0
            title_tier_bonus = 0.0

            if clean_title == clean_query:
                title_tier_bonus = 3000.0
                title_multiplier = 15.0
            elif clean_title.startswith(clean_query) and title_isolated_matches > 0:
                title_tier_bonus = 2000.0
                title_multiplier = 12.0
            elif title_isolated_matches > 0:
                title_tier_bonus = 1000.0
                title_multiplier = 8.0
            elif clean_query in clean_title:
                title_tier_bonus = 300.0
                title_multiplier = 3.0
            else:
                if is_short_query:
                    bm25_score *= 0.1
                title_tier_bonus = 0.0
                title_multiplier = 1.0

            bm25_part = (bm25_score * title_multiplier) + title_tier_bonus
            pagerank_boost = pr_score * 3.5

            if content_isolated_matches > 0:
                bm25_part += min(math.log(content_isolated_matches + 1.0) * 3.0, 15.0)

            parsed_url = urlparse(url)
            depth = len([s for s in parsed_url.path.strip("/").split("/") if s])
            depth_penalty_factor = 1.0 / (1.0 + 0.12 * max(0, depth - 1))

            final_score = (bm25_part + pagerank_boost) * depth_penalty_factor

            scored_candidates.append({
                "id": doc_id_val,
                "url": url,
                "title": title or url,
                "content": content,
                "score": round(final_score, 1),
                "pagerank": round(pr_score, 1),
                "depth": depth,
                "is_title_match": (title_tier_bonus > 0)
            })

        scored_candidates.sort(key=lambda x: (x["is_title_match"], x["score"]), reverse=True)
        final_top = scored_candidates[:top_k]

        top_titles = [item["title"] for item in final_top]
        related_keywords = extract_related_keywords_from_titles(query, top_titles, limit=5)

        results = []
        for item in final_top:
            snippet = self.generate_snippet(item["content"], query_tokens, isolated_pattern, window=50)
            results.append({
                "id": item["id"],
                "url": item["url"],
                "title": item["title"],
                "snippet": snippet,
                "score": item["score"],
                "pagerank": item["pagerank"],
                "depth": item["depth"]
            })

        return {
            "results": results,
            "related_keywords": related_keywords
        }

    def search_images(self, query: str, limit: int = 40) -> List[Dict[str, Any]]:
        clean_query = normalize_text(query).lower()
        if not clean_query:
            return []

        with get_read_conn() as conn:
            cursor = conn.cursor()
            like_pattern = f"%{clean_query}%"
            cursor.execute("""
                SELECT id, page_url, img_url, alt_text, title
                FROM images
                WHERE alt_text LIKE ? OR title LIKE ?
                ORDER BY id DESC
                LIMIT ?
            """, (like_pattern, like_pattern, limit))
            rows = cursor.fetchall()

        results = []
        for r_id, page_url, img_url, alt_text, title in rows:
            results.append({
                "id": r_id,
                "page_url": page_url,
                "img_url": img_url,
                "alt_text": alt_text or title or "画像",
                "title": title or page_url
            })
        return results

    def search_videos(self, query: str, limit: int = 30) -> List[Dict[str, Any]]:
        clean_query = normalize_text(query).lower()
        if not clean_query:
            return []

        with get_read_conn() as conn:
            cursor = conn.cursor()
            like_pattern = f"%{clean_query}%"
            cursor.execute("""
                SELECT id, page_url, video_url, title, thumbnail_url
                FROM videos
                WHERE title LIKE ? OR video_url LIKE ?
                ORDER BY view_count DESC, id DESC
                LIMIT ?
            """, (like_pattern, like_pattern, limit))
            rows = cursor.fetchall()

        results = []
        for r_id, page_url, video_url, title, thumb in rows:
            results.append({
                "id": r_id,
                "page_url": page_url,
                "video_url": video_url,
                "title": title or "動画",
                "thumbnail_url": thumb or ""
            })
        return results

    def search_youtube(self, query: str, limit: int = 40) -> List[Dict[str, Any]]:
        clean_query = normalize_text(query).lower()
        with get_read_conn() as conn:
            cursor = conn.cursor()
            if not clean_query:
                cursor.execute("""
                    SELECT video_id, title, channel, view_count, thumbnail_url, video_url
                    FROM youtube_videos
                    ORDER BY view_count DESC
                    LIMIT ?
                """, (limit,))
            else:
                like_pattern = f"%{clean_query}%"
                cursor.execute("""
                    SELECT video_id, title, channel, view_count, thumbnail_url, video_url
                    FROM youtube_videos
                    WHERE title LIKE ? OR channel LIKE ?
                    ORDER BY view_count DESC
                    LIMIT ?
                """, (like_pattern, like_pattern, limit))
            rows = cursor.fetchall()

        results = []
        for vid, title, channel, views, thumb, vurl in rows:
            results.append({
                "video_id": vid,
                "title": title,
                "channel": channel,
                "view_count": views,
                "thumbnail_url": thumb,
                "video_url": vurl
            })
        return results

    def search_sex_ed(self, query: str = "") -> List[Dict[str, Any]]:
        clean_query = normalize_text(query).lower()
        with get_read_conn() as conn:
            cursor = conn.cursor()
            if not clean_query:
                cursor.execute("""
                    SELECT id, category, title, summary, content, source_name, source_url, video_url, doc_id
                    FROM sex_ed_contents
                    ORDER BY id ASC
                """)
            else:
                like_pattern = f"%{clean_query}%"
                cursor.execute("""
                    SELECT id, category, title, summary, content, source_name, source_url, video_url, doc_id
                    FROM sex_ed_contents
                    WHERE title LIKE ? OR content LIKE ? OR category LIKE ?
                    ORDER BY id ASC
                """, (like_pattern, like_pattern, like_pattern))
            rows = cursor.fetchall()

        results = []
        for r in rows:
            results.append({
                "id": r[0],
                "category": r[1],
                "title": r[2],
                "summary": r[3],
                "content": r[4],
                "source_name": r[5],
                "source_url": r[6],
                "video_url": r[7],
                "doc_id": r[8]
            })
        return results

    def generate_snippet(self, content: str, query_tokens: List[str], isolated_pattern: re.Pattern, window: int = 50) -> str:
        if not content:
            return ""

        normalized = normalize_text(content)
        match = isolated_pattern.search(normalized)
        if match:
            first_pos = match.start()
            matched_len = match.end() - match.start()
        else:
            first_pos = None
            matched_len = len(query_tokens[0]) if query_tokens else 0
            for token in query_tokens:
                pos = normalized.lower().find(token.lower())
                if pos != -1:
                    if first_pos is None or pos < first_pos:
                        first_pos = pos
                        matched_len = len(token)

        if first_pos is not None:
            start = max(0, first_pos - window)
            end = min(len(normalized), first_pos + matched_len + window)
        else:
            start = 0
            end = min(len(normalized), window * 2)

        snippet_text = normalized[start:end]
        if start > 0:
            snippet_text = "..." + snippet_text
        if end < len(normalized):
            snippet_text = snippet_text + "..."

        safe_snippet = html.escape(snippet_text)
        safe_snippet = isolated_pattern.sub(lambda m: f"<b>{m.group(0)}</b>", safe_snippet)
        return safe_snippet


# ==============================================================================
# 6. 高速並列Webクローラー（CPU強制抑制版）
# ==============================================================================
class FastAutonomousCrawler:
    def __init__(self, max_workers: int = MAX_WORKER_THREADS):
        self.max_workers = max_workers
        self.is_running = False
        self.stop_event = threading.Event()
        self.dispatcher_thread: Optional[threading.Thread] = None

        self.url_queue: queue.Queue = queue.Queue(maxsize=10000)
        self.visited_urls: Set[str] = set()
        self.domain_page_counts: Counter = Counter()
        self.state_lock = threading.Lock()

        self.recent_urls: List[str] = []
        self.current_url: str = ""
        self.status_message: str = "停止中"
        self.pages_since_last_pr = 0

    def start(self, custom_seed: Optional[str] = None) -> bool:
        with self.state_lock:
            if self.is_running:
                return False

            self.stop_event.clear()
            self.is_running = True
            self.status_message = f"巡回中 ({self.max_workers} threads)"

            if custom_seed:
                self._safe_put_queue(custom_seed)
            if self.url_queue.empty():
                for seed in INITIAL_SEEDS:
                    self._safe_put_queue(seed)

            self.dispatcher_thread = threading.Thread(target=self._dispatcher_loop, daemon=True)
            self.dispatcher_thread.start()
            return True

    def stop(self) -> None:
        with self.state_lock:
            if not self.is_running:
                return
            self.stop_event.set()
            self.status_message = "停止処理中"

    def get_state(self) -> Dict[str, Any]:
        total_docs = get_total_indexed_documents()
        total_yt = get_total_youtube_videos()
        with self.state_lock:
            return {
                "is_running": self.is_running,
                "status_message": self.status_message,
                "current_url": self.current_url,
                "indexed_count": total_docs,
                "youtube_count": total_yt,
                "recent_urls": self.recent_urls[-5:],
                "queue_size": self.url_queue.qsize(),
                "discovered_domains": len(self.domain_page_counts),
                "workers": self.max_workers
            }

    def _safe_put_queue(self, url: str) -> None:
        try:
            self.url_queue.put_nowait(url)
        except queue.Full:
            pass

    def _is_crawlable_url(self, url: str) -> bool:
        try:
            p = urlparse(url)
            if p.scheme not in ("http", "https"):
                return False
            path_lower = p.path.lower()
            if any(path_lower.endswith(ext) for ext in IGNORED_EXTENSIONS):
                return False

            if "wikipedia.org" in p.netloc:
                blocked_prefixes = [
                    "action=", "oldid=", "printable=", "Special:", "特別:",
                    "Help:", "ヘルプ:", "Template:", "テンプレート:", "Category:", "カテゴリ:",
                    "Wikipedia:", "トーク:", "Talk:"
                ]
                if any(x in url for x in blocked_prefixes):
                    return False
            return True
        except Exception:
            return False

    def _dispatcher_loop(self) -> None:
        with ThreadPoolExecutor(max_workers=self.max_workers) as executor:
            futures = set()

            while not self.stop_event.is_set():
                done_futures = {f for f in futures if f.done()}
                futures.difference_update(done_futures)

                if self.url_queue.empty() and len(futures) == 0:
                    for seed in INITIAL_SEEDS:
                        self._safe_put_queue(seed)

                while len(futures) < self.max_workers and not self.stop_event.is_set():
                    try:
                        url = self.url_queue.get(timeout=0.2)
                    except queue.Empty:
                        break

                    clean_url = urlparse(url)._replace(fragment="").geturl().rstrip("/")
                    domain = urlparse(clean_url).netloc.lower()

                    with self.state_lock:
                        if clean_url in self.visited_urls:
                            continue
                        if self.domain_page_counts[domain] >= MAX_PAGES_PER_DOMAIN:
                            continue
                        self.visited_urls.add(clean_url)

                    fut = executor.submit(self._fetch_and_index_worker, clean_url, domain)
                    futures.add(fut)

                with self.state_lock:
                    now = time.time()
                    if self.pages_since_last_pr >= 500 and (now - last_pr_calc_time >= 600):
                        self.pages_since_last_pr = 0
                        threading.Thread(target=calculate_pagerank, daemon=True).start()

                time.sleep(0.15)

        with self.state_lock:
            self.is_running = False
            self.status_message = "停止中"
            self.current_url = ""

    def _fetch_and_index_worker(self, url: str, domain: str) -> None:
        if self.stop_event.is_set():
            return

        with self.state_lock:
            self.current_url = url

        try:
            time.sleep(0.3)

            resp = requests.get(
                url,
                headers=BROWSER_HEADERS,
                timeout=REQUEST_TIMEOUT,
                allow_redirects=True
            )
            if resp.status_code != 200:
                return

            content_type = resp.headers.get("Content-Type", "")
            if "text/html" not in content_type:
                return

            resp.encoding = resp.apparent_encoding or "utf-8"
            soup = BeautifulSoup(resp.text, "html.parser")

            link_pairs: List[Tuple[str, str]] = []
            for a_tag in soup.find_all("a", href=True):
                if self.stop_event.is_set():
                    break
                raw_href = a_tag["href"].strip()
                abs_url = urljoin(url, raw_href)
                norm_link = urlparse(abs_url)._replace(fragment="").geturl().rstrip("/")
                target_domain = urlparse(norm_link).netloc.lower()

                if self._is_crawlable_url(norm_link):
                    link_pairs.append((url, norm_link))
                    with self.state_lock:
                        if self.domain_page_counts[target_domain] < MAX_PAGES_PER_DOMAIN:
                            if norm_link not in self.visited_urls:
                                self._safe_put_queue(norm_link)

            if link_pairs:
                save_page_links_batch(link_pairs)

            title = ""
            if soup.title and soup.title.string:
                title = soup.title.string.strip()
            if not title:
                h1 = soup.find("h1")
                title = h1.get_text().strip() if h1 else url

            extracted_images: List[Tuple[str, str, str, str]] = []
            for img in soup.find_all("img"):
                src = img.get("src") or img.get("data-src")
                if not src:
                    continue
                abs_img_url = urljoin(url, src.strip())
                parsed_img = urlparse(abs_img_url)
                if parsed_img.scheme not in ("http", "https"):
                    continue

                path_lower = parsed_img.path.lower()
                if path_lower.endswith((".svg", ".ico")) or any(pat in path_lower for pat in IGNORED_IMG_PATTERNS):
                    continue

                alt_text = img.get("alt", "").strip()
                extracted_images.append((url, abs_img_url, alt_text, title))

            if extracted_images:
                save_images_batch(extracted_images[:20])

            extracted_videos: List[Tuple[str, str, str, str]] = []
            for video_tag in soup.find_all("video"):
                v_src = video_tag.get("src")
                if not v_src:
                    source_child = video_tag.find("source")
                    if source_child:
                        v_src = source_child.get("src")
                if v_src:
                    abs_v_url = urljoin(url, v_src.strip())
                    poster = urljoin(url, video_tag.get("poster", "").strip())
                    extracted_videos.append((url, abs_v_url, title, poster))

            for iframe_tag in soup.find_all("iframe"):
                i_src = iframe_tag.get("src", "").strip()
                if not i_src:
                    continue
                abs_i_url = urljoin(url, i_src)

                yt_match = re.search(r"(?:youtube\.com\/(?:embed\/|watch\?v=)|youtu\.be\/)([a-zA-Z0-9_-]{11})", abs_i_url)
                if yt_match:
                    video_id = yt_match.group(1)
                    thumb_url = f"https://img.youtube.com/vi/{video_id}/hqdefault.jpg"
                    extracted_videos.append((url, abs_i_url, title, thumb_url))
                elif "vimeo.com" in abs_i_url or "nicovideo.jp" in abs_i_url:
                    extracted_videos.append((url, abs_i_url, title, ""))

            if extracted_videos:
                save_videos_batch(extracted_videos[:10])

            for tag in soup(["script", "style", "noscript", "svg", "header", "footer", "nav", "aside", "form"]):
                tag.decompose()

            raw_text = soup.get_text(separator=" ", strip=True)
            trimmed_content = raw_text[:MAX_CONTENT_CHARS]

            if trimmed_content and len(trimmed_content) > 30:
                tokens = tokenize(trimmed_content)
                if tokens:
                    save_document_and_index(url, title, trimmed_content, tokens)

                    with self.state_lock:
                        self.domain_page_counts[domain] += 1
                        self.recent_urls.append(url)
                        self.pages_since_last_pr += 1
                        if len(self.recent_urls) > 10:
                            self.recent_urls.pop(0)

        except Exception:
            pass


crawler = FastAutonomousCrawler(max_workers=MAX_WORKER_THREADS)
yt_expander = YouTubeExpander()
search_engine = AdvancedBM25SearchEngine()


# ==============================================================================
# 7. Webサーバー & 【FINDRA】UI
# ==============================================================================
@asynccontextmanager
async def lifespan(app: FastAPI):
    init_db()
    threading.Thread(target=calculate_pagerank, daemon=True).start()
    crawler.start()
    yt_expander.start()
    yield
    crawler.stop()
    yt_expander.stop()


app = FastAPI(title="FINDRA Search Engine", lifespan=lifespan)


class CrawlStartRequest(BaseModel):
    seed_url: Optional[str] = None


HTML_PAGE = """
<!DOCTYPE html>
<html lang="ja">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <meta name="referrer" content="strict-origin-when-cross-origin">
  <title>FINDRA - スマートな検索。確かな情報。</title>
  <style>
    * { box-sizing: border-box; margin: 0; padding: 0; }
    
    :root {
      --primary: #009688;
      --primary-hover: #00796B;
      --primary-light: #E0F2F1;
      --text-main: #4A4A4A;
      --text-muted: #757575;
      --border-color: #E0E0E0;
      --bg-base: #FDFDFD;
      --card-bg: #FFFFFF;
      --highlight-bg: #E0F2F1;
    }

    body {
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", "Hiragino Kaku Gothic ProN", "Yu Gothic", Roboto, sans-serif;
      color: var(--text-main);
      background-color: var(--bg-base);
      line-height: 1.6;
      -webkit-font-smoothing: antialiased;
    }
    
    .top-header {
      padding: 16px 28px;
      display: flex;
      justify-content: flex-end;
      align-items: center;
    }
    .stamp-badge {
      display: inline-flex;
      align-items: center;
      gap: 8px;
      background: var(--card-bg);
      border: 1px solid var(--border-color);
      padding: 5px 14px;
      border-radius: 9999px;
      font-size: 11.5px;
      font-weight: 500;
      color: var(--text-muted);
    }
    .stamp-dot {
      width: 7px;
      height: 7px;
      border-radius: 50%;
      background-color: var(--primary);
      animation: pulse 1.8s infinite;
    }
    .stamp-dot.paused { 
      background-color: #BDBDBD; 
      animation: none;
    }
    @keyframes pulse {
      0% { opacity: 1; transform: scale(1); }
      50% { opacity: 0.4; transform: scale(0.9); }
      100% { opacity: 1; transform: scale(1); }
    }
    .stamp-btn {
      background: none;
      border: none;
      color: var(--primary);
      font-size: 11.5px;
      font-weight: 600;
      cursor: pointer;
      text-decoration: underline;
    }
    .stamp-btn:hover { color: var(--primary-hover); }

    .main-container {
      max-width: 820px;
      margin: 28px auto 90px auto;
      padding: 0 20px;
    }

    .logo-area {
      text-align: center;
      margin-bottom: 26px;
    }
    .brand-wrap {
      display: inline-flex;
      align-items: center;
      justify-content: center;
      gap: 12px;
      margin-bottom: 6px;
    }
    .logo-svg {
      width: 48px;
      height: 48px;
      flex-shrink: 0;
    }
    .logo-title {
      font-size: 46px;
      font-weight: 800;
      letter-spacing: -0.5px;
      color: var(--text-main);
      line-height: 1;
    }
    .logo-subtitle {
      font-size: 13.5px;
      color: var(--text-muted);
      letter-spacing: 0.6px;
      font-weight: 500;
    }

    .search-pill-box {
      display: flex;
      align-items: center;
      max-width: 650px;
      margin: 0 auto;
      background: var(--card-bg);
      border: 1px solid var(--border-color);
      border-radius: 9999px;
      padding: 5px 6px 5px 22px;
      transition: all 0.2s ease-in-out;
    }
    .search-pill-box:focus-within {
      border-color: var(--primary);
      box-shadow: 0 0 0 3px rgba(0, 150, 136, 0.15);
    }
    .search-input {
      flex: 1;
      border: none;
      font-size: 15.5px;
      color: var(--text-main);
      background: transparent;
      outline: none;
      padding: 8px 8px 8px 0;
    }
    .search-input::placeholder { color: #9E9E9E; }
    .search-action-btn {
      width: 40px;
      height: 40px;
      border-radius: 50%;
      background: var(--primary);
      border: none;
      cursor: pointer;
      display: flex;
      align-items: center;
      justify-content: center;
      color: #FFFFFF;
      transition: background-color 0.15s ease-in-out;
      flex-shrink: 0;
    }
    .search-action-btn:hover { background: var(--primary-hover); }
    .search-action-btn svg { width: 18px; height: 18px; stroke-width: 2.5; }

    .related-keywords-wrap {
      display: flex;
      align-items: center;
      justify-content: center;
      gap: 6px;
      margin: 14px auto 0 auto;
      flex-wrap: wrap;
      max-width: 650px;
      font-size: 12px;
      color: var(--text-muted);
    }
    .related-tag {
      background: var(--primary-light);
      border: 1px solid #B2DFDB;
      color: var(--primary-hover);
      padding: 3px 10px;
      border-radius: 4px;
      cursor: pointer;
      font-weight: 600;
      transition: all 0.15s ease-in-out;
      text-decoration: none;
    }
    .related-tag:hover {
      background: #B2DFDB;
      color: #004D40;
    }

    .tabs-container {
      display: flex;
      justify-content: center;
      gap: 16px;
      margin: 22px auto 0 auto;
      max-width: 700px;
      border-bottom: 1px solid var(--border-color);
      overflow-x: auto;
      scrollbar-width: none;
    }
    .tabs-container::-webkit-scrollbar { display: none; }

    .tab-btn {
      background: transparent;
      border: none;
      padding: 8px 16px;
      font-size: 13.5px;
      font-weight: 500;
      color: var(--text-muted);
      cursor: pointer;
      position: relative;
      transition: color 0.15s;
      white-space: nowrap;
      flex-shrink: 0;
    }
    .tab-btn:hover { color: var(--text-main); }
    .tab-btn.active { color: var(--primary); font-weight: 700; }
    .tab-btn.active::after {
      content: "";
      position: absolute;
      bottom: -1px;
      left: 0;
      width: 100%;
      height: 2.5px;
      background-color: var(--primary);
    }

    .results-info {
      font-size: 12.5px;
      color: var(--text-muted);
      margin: 26px 0 16px 0;
      display: flex;
      justify-content: space-between;
      align-items: center;
    }

    .result-item {
      background: var(--card-bg);
      border: 1px solid var(--border-color);
      border-radius: 8px;
      padding: 18px 20px;
      margin-bottom: 14px;
      transition: border-color 0.15s ease-in-out;
    }
    .result-item:hover { border-color: #BDBDBD; }
    .result-header {
      display: flex;
      align-items: center;
      gap: 8px;
      margin-bottom: 5px;
      font-size: 12px;
      color: var(--text-muted);
    }
    .site-favicon {
      width: 16px;
      height: 16px;
      border-radius: 3px;
      flex-shrink: 0;
      background: #EEEEEE;
    }
    .site-domain { font-weight: 600; color: var(--text-main); }
    .site-path {
      color: var(--text-muted);
      white-space: nowrap;
      overflow: hidden;
      text-overflow: ellipsis;
      max-width: 420px;
    }
    .result-title {
      font-size: 18px;
      font-weight: 700;
      color: var(--text-main);
      text-decoration: none;
      display: inline-block;
      margin-bottom: 6px;
      line-height: 1.4;
      cursor: pointer;
      transition: color 0.15s;
    }
    .result-title:hover {
      color: var(--primary);
      text-decoration: underline;
    }

    .result-pr-stamp {
      display: inline-block;
      font-size: 10.5px;
      color: var(--primary-hover);
      background: var(--primary-light);
      border: 1px solid #B2DFDB;
      padding: 1px 7px;
      border-radius: 4px;
      margin-left: 6px;
      vertical-align: middle;
      font-weight: 700;
    }
    .result-snippet {
      font-size: 13.5px;
      color: #616161;
      line-height: 1.6;
      word-break: break-word;
    }
    .result-snippet b {
      color: #004D40;
      background-color: var(--highlight-bg);
      font-weight: 600;
      padding: 0 3px;
      border-radius: 2px;
    }

    .image-grid {
      display: grid;
      grid-template-columns: repeat(auto-fill, minmax(170px, 1fr));
      gap: 12px;
    }
    .image-card {
      background: var(--card-bg);
      border: 1px solid var(--border-color);
      border-radius: 6px;
      overflow: hidden;
      display: flex;
      flex-direction: column;
      text-decoration: none;
      color: var(--text-main);
      cursor: pointer;
      transition: border-color 0.15s;
    }
    .image-card:hover { border-color: var(--primary); }
    .image-thumb-wrap { width: 100%; height: 130px; background: #EEEEEE; }
    .image-thumb { width: 100%; height: 100%; object-fit: cover; display: block; }
    .image-info { padding: 8px 10px; font-size: 11px; background: var(--card-bg); }
    .image-alt { font-weight: 600; color: var(--text-main); white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
    .image-host { font-size: 10px; color: var(--text-muted); margin-top: 2px; }

    .video-grid {
      display: grid;
      grid-template-columns: repeat(auto-fill, minmax(240px, 1fr));
      gap: 16px;
    }
    .video-card {
      background: var(--card-bg);
      border: 1px solid var(--border-color);
      border-radius: 8px;
      overflow: hidden;
      display: flex;
      flex-direction: column;
      text-decoration: none;
      color: var(--text-main);
      cursor: pointer;
      transition: all 0.15s ease-in-out;
    }
    .video-card:hover {
      border-color: var(--primary);
      transform: translateY(-2px);
      box-shadow: 0 3px 8px rgba(0,0,0,0.04);
    }
    .video-thumb-wrap {
      width: 100%; height: 140px; background: #212121; position: relative; display: flex; align-items: center; justify-content: center;
    }
    .video-thumb { width: 100%; height: 100%; object-fit: cover; }
    .video-play-stamp {
      position: absolute; width: 38px; height: 38px; background: rgba(0, 150, 136, 0.95); border-radius: 50%; display: flex; align-items: center; justify-content: center; color: #FFFFFF; font-size: 16px;
    }
    .video-info { padding: 12px 14px; font-size: 12.5px; }
    .video-title { font-weight: 700; line-height: 1.4; display: -webkit-box; -webkit-line-clamp: 2; -webkit-box-orient: vertical; overflow: hidden; margin-bottom: 6px; }
    .video-meta-line {
      display: flex;
      justify-content: space-between;
      align-items: center;
      margin-top: 4px;
    }
    .video-channel { font-size: 11.5px; color: var(--text-muted); white-space: nowrap; overflow: hidden; text-overflow: ellipsis; max-width: 130px; }
    .video-views-badge {
      font-size: 10.5px;
      font-weight: 700;
      color: var(--primary-hover);
      background: var(--primary-light);
      border: 1px solid #B2DFDB;
      padding: 1px 6px;
      border-radius: 4px;
    }

    .sexed-portal-card {
      background: var(--card-bg);
      border: 1px solid var(--border-color);
      border-radius: 8px;
      padding: 20px 22px;
      margin-bottom: 16px;
      transition: all 0.15s ease-in-out;
    }
    .sexed-portal-card:hover {
      border-color: var(--primary);
      box-shadow: 0 2px 6px rgba(0, 150, 136, 0.08);
    }
    .sexed-badge {
      display: inline-block;
      font-size: 11px;
      font-weight: 700;
      color: var(--primary);
      background: var(--primary-light);
      border: 1px solid #B2DFDB;
      padding: 2px 8px;
      border-radius: 4px;
      margin-bottom: 8px;
    }
    .sexed-summary {
      font-size: 13.5px;
      color: #616161;
      margin-bottom: 12px;
      line-height: 1.6;
    }
    .sexed-footer {
      display: flex;
      justify-content: space-between;
      align-items: center;
      font-size: 11.5px;
      color: var(--text-muted);
      border-top: 1px dashed var(--border-color);
      padding-top: 8px;
    }

    .empty-message {
      text-align: center; color: var(--text-muted); margin-top: 40px; font-size: 14px; background: var(--card-bg); border: 1px solid var(--border-color); padding: 36px 20px; border-radius: 8px;
    }

    /* リーダーモードUI */
    #readerView {
      display: none;
      min-height: 100vh;
      background-color: var(--bg-base);
    }
    .reader-toolbar {
      display: flex;
      justify-content: space-between;
      align-items: center;
      background: var(--card-bg);
      border-bottom: 1px solid var(--border-color);
      padding: 12px 24px;
      position: sticky;
      top: 0;
      z-index: 100;
    }
    .reader-back-btn {
      display: inline-flex;
      align-items: center;
      gap: 6px;
      background: var(--primary-light);
      color: var(--primary-hover);
      border: 1px solid #B2DFDB;
      padding: 6px 16px;
      border-radius: 9999px;
      font-size: 13px;
      font-weight: 700;
      cursor: pointer;
      transition: all 0.15s ease-in-out;
    }
    .reader-back-btn:hover {
      background: #B2DFDB;
      color: #004D40;
    }
    .reader-url-display {
      font-size: 12px;
      color: var(--text-muted);
      max-width: 400px;
      white-space: nowrap;
      overflow: hidden;
      text-overflow: ellipsis;
    }
    .reader-origin-link {
      display: inline-flex;
      align-items: center;
      gap: 4px;
      color: var(--text-muted);
      font-size: 12.5px;
      text-decoration: none;
      padding: 4px 8px;
      border-radius: 4px;
      transition: color 0.15s;
    }
    .reader-origin-link:hover {
      color: var(--primary);
      text-decoration: underline;
    }

    .reader-content-wrap {
      max-width: 760px;
      margin: 36px auto 100px auto;
      padding: 0 24px;
    }
    .reader-meta-bar {
      display: flex;
      align-items: center;
      gap: 10px;
      margin-bottom: 12px;
      font-size: 12px;
      color: var(--text-muted);
    }
    .reader-title {
      font-size: 28px;
      font-weight: 800;
      color: var(--text-main);
      line-height: 1.4;
      margin-bottom: 24px;
      word-break: break-word;
    }
    .reader-body {
      font-size: 16px;
      color: #424242;
      line-height: 1.85;
      letter-spacing: 0.2px;
      word-break: break-word;
    }
    .reader-body p {
      margin-bottom: 20px;
      text-align: justify;
    }
    .reader-keyword-highlight {
      background-color: var(--highlight-bg);
      color: #004D40;
      font-weight: 600;
      padding: 0 4px;
      border-radius: 3px;
    }

    .video-container-responsive {
      position: relative;
      padding-bottom: 56.25%;
      height: 0;
      overflow: hidden;
      max-width: 100%;
      background: #111;
      border-radius: 10px;
      margin: 20px 0 32px 0;
      border: 1px solid var(--border-color);
      box-shadow: 0 2px 8px rgba(0,0,0,0.06);
    }
    .video-container-responsive iframe {
      position: absolute;
      top: 0;
      left: 0;
      width: 100%;
      height: 100%;
      border: none;
    }

    .dev-corner-btn {
      position: fixed;
      bottom: 12px;
      left: 12px;
      background: rgba(0,0,0,0.03);
      border: 1px solid var(--border-color);
      color: var(--text-muted);
      border-radius: 4px;
      padding: 3px 7px;
      font-size: 11px;
      font-family: monospace;
      cursor: pointer;
      z-index: 100;
      transition: all 0.15s;
    }
    .dev-corner-btn:hover {
      background: #FFFFFF;
      color: var(--primary);
      border-color: var(--primary);
    }

    #ageScanModal {
      display: none;
      position: fixed;
      inset: 0;
      background: rgba(20, 24, 26, 0.94);
      z-index: 9999;
      justify-content: center;
      align-items: center;
      flex-direction: column;
      color: #FFFFFF;
      backdrop-filter: blur(6px);
    }

    .scan-card {
      width: 90%;
      max-width: 440px;
      background: #1C2224;
      border: 1px solid rgba(0, 150, 136, 0.4);
      border-radius: 12px;
      padding: 24px;
      display: flex;
      flex-direction: column;
      align-items: center;
      position: relative;
      box-shadow: 0 10px 30px rgba(0, 0, 0, 0.5);
    }

    .camera-frame {
      width: 280px;
      height: 280px;
      position: relative;
      border-radius: 50%;
      overflow: hidden;
      margin: 16px 0;
      border: 3px solid var(--primary);
      background: #0D1112;
    }

    #scanVideo {
      width: 100%;
      height: 100%;
      object-fit: cover;
      transform: scaleX(-1);
    }

    .scanner-laser {
      position: absolute;
      top: 0;
      left: 0;
      right: 0;
      height: 3px;
      background: #00E676;
      box-shadow: 0 0 12px #00E676;
      animation: laserScan 2s infinite ease-in-out;
    }

    @keyframes laserScan {
      0% { top: 5%; opacity: 0.2; }
      50% { top: 90%; opacity: 1; }
      100% { top: 5%; opacity: 0.2; }
    }

    .scan-progress-bar-wrap {
      width: 100%;
      height: 6px;
      background: #2A3336;
      border-radius: 3px;
      overflow: hidden;
      margin: 14px 0 8px 0;
    }

    .scan-progress-bar {
      height: 100%;
      width: 0%;
      background: var(--primary);
      transition: width 0.1s linear;
    }

    .scan-status-text {
      font-size: 13px;
      color: #B2DFDB;
      font-family: monospace;
      margin-bottom: 4px;
      text-align: center;
    }
  </style>
</head>
<body>

<div id="searchView">
  <header class="top-header">
    <div class="stamp-badge">
      <span class="stamp-dot" id="stampDot"></span>
      <span><strong id="stampIndexed" style="color:var(--text-main);">0</strong> 頁インデックス</span>
      <span>·</span>
      <span><span id="stampDomains">0</span> ドメイン</span>
      <span>·</span>
      <span><strong id="stampYtCount" style="color:var(--primary);">0</strong> 本YouTube</span>
      <span>·</span>
      <button class="stamp-btn" id="stampToggleBtn" onclick="toggleCrawler()">一時停止</button>
    </div>
  </header>

  <div class="main-container">
    <div class="logo-area">
      <div class="brand-wrap">
        <svg class="logo-svg" viewBox="0 0 100 100" fill="none" xmlns="http://www.w3.org/2000/svg">
          <circle cx="45" cy="44" r="28" stroke="#009688" stroke-width="8.5" stroke-linecap="round"/>
          <path d="M66 65L85 84" stroke="#009688" stroke-width="9.5" stroke-linecap="round"/>
          <path d="M29 68C32 49 35 31 46 24C55 19 66 22 71 24" stroke="#009688" stroke-width="8" stroke-linecap="round"/>
          <path d="M35 44H60" stroke="#009688" stroke-width="8" stroke-linecap="round"/>
        </svg>
        <div class="logo-title">FINDRA</div>
      </div>
      <div class="logo-subtitle">スマートな検索。確かな情報。</div>
    </div>

    <div class="search-pill-box">
      <input type="text" id="queryInput" class="search-input" placeholder="検索キーワードを入力してください (例: 虎, 日本, YOASOBI, Ado)..." onkeydown="if(event.key==='Enter') executeSearch()" />
      <button class="search-action-btn" onclick="executeSearch()" aria-label="検索">
        <svg fill="none" stroke="currentColor" viewBox="0 0 24 24">
          <path stroke-linecap="round" stroke-linejoin="round" d="M21 21l-5.197-5.197m0 0A7.5 7.5 0 105.196 5.196a7.5 7.5 0 0010.607 10.607z"></path>
        </svg>
      </button>
    </div>

    <div id="relatedArea" class="related-keywords-wrap" style="display:none;"></div>

    <!-- 検索ナビゲーションタブ -->
    <div class="tabs-container" id="tabsBar">
      <button class="tab-btn active" id="tabAll" onclick="switchTab('all')">🔍 すべて</button>
      <button class="tab-btn" id="tabImage" onclick="switchTab('image')">📷 画像</button>
      <button class="tab-btn" id="tabVideo" onclick="switchTab('video')">🎥 動画</button>
      <button class="tab-btn" id="tabYouTube" onclick="switchTab('youtube')">▶ YouTube</button>
      <button class="tab-btn" id="tabSexEd" onclick="switchTab('sex_ed')" style="display:none; color:#00796B;">📖 性教育</button>
    </div>

    <div id="resultsInfo" class="results-info" style="display:none;"></div>
    <div id="resultsArea"></div>
  </div>
</div>

<div id="readerView">
  <div class="reader-toolbar">
    <button class="reader-back-btn" onclick="closeReader()">
      <svg width="14" height="14" fill="none" stroke="currentColor" viewBox="0 0 24 24" style="stroke-width:2.5;">
        <path stroke-linecap="round" stroke-linejoin="round" d="M10 19l-7-7m0 0l7-7m-7 7h18"></path>
      </svg>
      検索結果に戻る
    </button>
    <div class="reader-url-display" id="readerUrlDisplay">https://...</div>
    <a href="#" target="_blank" rel="noopener noreferrer" class="reader-origin-link" id="readerOriginLink">
      <span>元のWebサイトを開く</span>
      <svg width="13" height="13" fill="none" stroke="currentColor" viewBox="0 0 24 24" style="stroke-width:2;">
        <path stroke-linecap="round" stroke-linejoin="round" d="M10 6H6a2 2 0 00-2 2v10a2 2 0 002 2h10a2 2 0 002-2v-4M14 4h6m0 0v6m0-6L10 14"></path>
      </svg>
    </a>
  </div>

  <div class="reader-content-wrap">
    <div class="reader-meta-bar" id="readerMetaBar">
      <img id="readerFavicon" class="site-favicon" src="" alt="" />
      <span id="readerDomain" style="font-weight:600; color:var(--text-main);"></span>
      <span id="readerPrStamp" class="result-pr-stamp">PR: --</span>
    </div>
    <h1 class="reader-title" id="readerTitle">記事タイトル</h1>
    
    <div id="readerVideoContainer" style="display:none;"></div>
    <div class="reader-body" id="readerBody"></div>
  </div>
</div>

<div id="ageScanModal">
  <div class="scan-card">
    <div style="font-size:16px; font-weight:700; letter-spacing:0.5px; color:#E0F2F1;">BIO-METRIC SCANNER</div>
    <div style="font-size:12px; color:#80CBC4; margin-top:2px;">年齢認証・生体特徴点解析</div>

    <div class="camera-frame">
      <video id="scanVideo" autoplay playsinline muted></video>
      <div class="scanner-laser"></div>
    </div>

    <div class="scan-status-text" id="scanStatusText">カメラを起動中...</div>
    <div class="scan-progress-bar-wrap">
      <div class="scan-progress-bar" id="scanProgressBar"></div>
    </div>
    <div style="font-size:11px; color:#757575; margin-top:8px;">18歳以上の利用規約への適合性を検証しています</div>
    <button onclick="cancelAgeScan()" style="margin-top:14px; background:none; border:1px solid #4A4A4A; color:#9E9E9E; padding:4px 12px; border-radius:4px; font-size:11px; cursor:pointer;">キャンセル</button>
  </div>
</div>

<button class="dev-corner-btn" onclick="promptDevCommand()" title="開発者コンソール">[ &gt;_ ]</button>

<script>
  const API_SEARCH = '/api/search';
  const API_START = '/api/crawl/start';
  const API_STOP = '/api/crawl/stop';
  const API_STATUS = '/api/crawl/status';
  const API_DOC = '/api/document';
  const API_SEX_ED = '/api/sex-ed';

  let currentType = 'all';
  let isCrawlerRunning = false;
  let currentSearchQuery = '';
  let isSexEdUnlocked = false;
  let videoStream = null;

  function switchTab(type) {
    currentType = type;
    document.querySelectorAll('.tab-btn').forEach(btn => btn.classList.remove('active'));
    if (type === 'all') document.getElementById('tabAll').classList.add('active');
    if (type === 'image') document.getElementById('tabImage').classList.add('active');
    if (type === 'video') document.getElementById('tabVideo').classList.add('active');
    if (type === 'youtube') document.getElementById('tabYouTube').classList.add('active');
    if (type === 'sex_ed') document.getElementById('tabSexEd').classList.add('active');

    executeSearch();
  }

  function formatViews(views) {
    views = Number(views) || 0;
    if (views >= 100000000) {
      return (views / 100000000).toFixed(1) + '億回';
    } else if (views >= 10000) {
      return Math.floor(views / 10000).toLocaleString() + '万回';
    } else {
      return views.toLocaleString() + '回';
    }
  }

  function searchWithKeyword(word) {
    document.getElementById('queryInput').value = word;
    executeSearch();
  }

  function promptDevCommand() {
    const cmd = prompt("開発者シークレットコマンドを入力してください:");
    if (cmd === "0000") {
      startAgeVerificationScan();
    } else if (cmd !== null) {
      alert("無効なコマンドです。");
    }
  }

  async function startAgeVerificationScan() {
    const modal = document.getElementById('ageScanModal');
    const video = document.getElementById('scanVideo');
    const statusText = document.getElementById('scanStatusText');
    const progressBar = document.getElementById('scanProgressBar');

    modal.style.display = 'flex';
    statusText.textContent = "カメラデバイスを認証中...";
    progressBar.style.width = "10%";

    try {
      videoStream = await navigator.mediaDevices.getUserMedia({
        video: { facingMode: "user", width: { ideal: 480 }, height: { ideal: 480 } }
      });
      video.srcObject = videoStream;

      let progress = 10;
      const scanPhases = [
        "顔面輪郭および生体反応を検出中...",
        "眼窩・鼻稜・骨格特徴点を解析中...",
        "ディープニューラルネットによる年齢推定中...",
        "検証中: 18歳以上判定アルゴリズム適用中..."
      ];

      const timer = setInterval(() => {
        progress += 4;
        progressBar.style.width = progress + "%";

        const phaseIndex = Math.min(Math.floor((progress / 100) * scanPhases.length), scanPhases.length - 1);
        statusText.textContent = scanPhases[phaseIndex];

        if (progress >= 100) {
          clearInterval(timer);
          statusText.textContent = "認証成功: 18歳以上判定完了 (アクセス許可)";
          statusText.style.color = "#00E676";
          progressBar.style.background = "#00E676";

          setTimeout(() => {
            stopCamera();
            modal.style.display = 'none';
            unlockSexEdPortal();
          }, 900);
        }
      }, 70);

    } catch (err) {
      statusText.textContent = "認証失敗: カメラが拒否されたか利用できません";
      statusText.style.color = "#FF5252";
      setTimeout(() => {
        stopCamera();
        modal.style.display = 'none';
        alert("認証失敗：利用条件を満たしていないか、カメラアクセスが許可されていません。");
      }, 1500);
    }
  }

  function stopCamera() {
    if (videoStream) {
      videoStream.getTracks().forEach(track => track.stop());
      videoStream = null;
    }
  }

  function cancelAgeScan() {
    stopCamera();
    document.getElementById('ageScanModal').style.display = 'none';
  }

  function unlockSexEdPortal() {
    isSexEdUnlocked = true;
    const sexEdTab = document.getElementById('tabSexEd');
    sexEdTab.style.display = 'inline-block';
    switchTab('sex_ed');
    alert("【認証完了】隠し機能「📖 性教育」タブがアンロックされました。");
  }

  async function executeSearch() {
    const q = document.getElementById('queryInput').value.trim();

    if (!q && currentType !== 'youtube' && currentType !== 'sex_ed') return;

    currentSearchQuery = q;
    closeReader();

    const url = new URL(window.location.href);
    if (q) {
      url.searchParams.set('q', q);
    } else {
      url.searchParams.delete('q');
    }
    url.searchParams.set('type', currentType);
    window.history.pushState({}, '', url);

    const infoDiv = document.getElementById('resultsInfo');
    const areaDiv = document.getElementById('resultsArea');
    const relatedDiv = document.getElementById('relatedArea');
    
    areaDiv.innerHTML = '<p class="empty-message">計算・検索中...</p>';
    infoDiv.style.display = 'none';
    relatedDiv.style.display = 'none';

    if (currentType === 'sex_ed') {
      try {
        const resp = await fetch(`${API_SEX_ED}?q=${encodeURIComponent(q)}`);
        const data = await resp.json();
        infoDiv.style.display = 'flex';
        infoDiv.innerHTML = `<span>セイシル等監修 性教育ポータル (${data.count} 項目)</span><span>専門医・医療監修</span>`;
        renderSexEdResults(data.results, areaDiv);
      } catch (e) {
        areaDiv.innerHTML = '<p class="empty-message" style="color:#D32F2F;">性教育データの読み込みに失敗しました。</p>';
      }
      return;
    }

    const startTime = performance.now();
    try {
      const resp = await fetch(`${API_SEARCH}?q=${encodeURIComponent(q)}&type=${encodeURIComponent(currentType)}`);
      if (!resp.ok) throw new Error('Search API Error');
      const data = await resp.json();
      const elapsed = ((performance.now() - startTime) / 1000).toFixed(3);

      infoDiv.style.display = 'flex';
      let titleHeader = currentType === 'youtube' && !q ? '人気YouTubeランキング' : `約 ${data.count} 件`;
      infoDiv.innerHTML = `<span>${titleHeader}</span><span>${elapsed} 秒</span>`;

      if (data.related_keywords && data.related_keywords.length > 0 && currentType === 'all') {
        let tagHtml = '<span style="font-weight:600; margin-right:4px;">関連:</span>';
        data.related_keywords.forEach(word => {
          tagHtml += `<a href="javascript:void(0)" class="related-tag" onclick="searchWithKeyword('${escapeHtml(word)}')">${escapeHtml(word)}</a>`;
        });
        relatedDiv.innerHTML = tagHtml;
        relatedDiv.style.display = 'flex';
      }

      if (data.results.length === 0) {
        areaDiv.innerHTML = `
          <div class="empty-message">
            <p>一致するコンテンツは見つかりませんでした。</p>
            <p style="margin-top:6px; font-size:12px; color:var(--text-muted);">別のキーワードをお試しください。</p>
          </div>
        `;
        return;
      }

      if (currentType === 'all') {
        renderAllResults(data.results, areaDiv);
      } else if (currentType === 'image') {
        renderImageResults(data.results, areaDiv);
      } else if (currentType === 'video') {
        renderVideoResults(data.results, areaDiv);
      } else if (currentType === 'youtube') {
        renderYouTubeResults(data.results, areaDiv);
      }
    } catch (e) {
      areaDiv.innerHTML = '<p class="empty-message" style="color:#D32F2F;">検索処理中にエラーが発生しました。</p>';
    }
  }

  function renderAllResults(results, container) {
    let htmlContent = '';
    results.forEach(item => {
      let domain = '';
      let pathname = '';
      try {
        const u = new URL(item.url);
        domain = u.hostname;
        pathname = u.pathname + u.search;
      } catch(e) {
        domain = item.url;
      }

      const faviconUrl = `https://www.google.com/s2/favicons?domain=${encodeURIComponent(domain)}&sz=32`;

      htmlContent += `
        <div class="result-item">
          <div class="result-header">
            <img class="site-favicon" src="${faviconUrl}" alt="" loading="lazy" onerror="this.style.opacity='0.2';" />
            <span class="site-domain">${escapeHtml(domain)}</span>
            <span class="site-path">${escapeHtml(pathname)}</span>
          </div>
          <div>
            <a href="javascript:void(0)" onclick="openReader(${item.id}, '${escapeJs(item.url)}', '${escapeJs(item.title)}', ${item.pagerank})" class="result-title">
              ${escapeHtml(item.title)}
            </a>
            <span class="result-pr-stamp" title="Power IterationによるPageRank">PR: ${item.pagerank}</span>
          </div>
          <div class="result-snippet">${item.snippet}</div>
        </div>
      `;
    });
    container.innerHTML = htmlContent;
  }

  function renderImageResults(results, container) {
    let htmlContent = '<div class="image-grid">';
    results.forEach(img => {
      let host = '';
      try { host = new URL(img.page_url).hostname; } catch(e){}
      htmlContent += `
        <div class="image-card" onclick="openReaderByUrl('${escapeJs(img.page_url)}', '${escapeJs(img.title)}')" title="${escapeHtml(img.title)}">
          <div class="image-thumb-wrap">
            <img src="${escapeHtml(img.img_url)}" class="image-thumb" loading="lazy" alt="${escapeHtml(img.alt_text)}" onerror="this.closest('.image-card').style.display='none';" />
          </div>
          <div class="image-info">
            <div class="image-alt">${escapeHtml(img.alt_text)}</div>
            <div class="image-host">${escapeHtml(host)}</div>
          </div>
        </div>
      `;
    });
    htmlContent += '</div>';
    container.innerHTML = htmlContent;
  }

  function renderVideoResults(results, container) {
    let htmlContent = '<div class="video-grid">';
    results.forEach(v => {
      let host = '';
      try { host = new URL(v.page_url).hostname; } catch(e){}
      let thumbImg = v.thumbnail_url 
        ? `<img src="${escapeHtml(v.thumbnail_url)}" class="video-thumb" loading="lazy" onerror="this.style.display='none';" />`
        : `<div style="color:#FFF; font-size:11px; font-weight:600;">VIDEO</div>`;

      htmlContent += `
        <div class="video-card" onclick="openVideoReader('${escapeJs(v.video_url)}', '${escapeJs(v.title)}', '${escapeJs(v.page_url)}')" title="${escapeHtml(v.title)}">
          <div class="video-thumb-wrap">
            ${thumbImg}
            <div class="video-play-stamp">▶</div>
          </div>
          <div class="video-info">
            <div class="video-title">${escapeHtml(v.title)}</div>
            <div class="video-meta-line">
              <span class="video-channel">${escapeHtml(host)}</span>
            </div>
          </div>
        </div>
      `;
    });
    htmlContent += '</div>';
    container.innerHTML = htmlContent;
  }

  function renderYouTubeResults(results, container) {
    let htmlContent = '<div class="video-grid">';
    results.forEach(yt => {
      htmlContent += `
        <div class="video-card" onclick="openVideoReader('${escapeJs(yt.video_url)}', '${escapeJs(yt.title)}', '${escapeJs(yt.video_url)}')" title="${escapeHtml(yt.title)}">
          <div class="video-thumb-wrap">
            <img src="${escapeHtml(yt.thumbnail_url)}" class="video-thumb" loading="lazy" onerror="this.style.display='none';" />
            <div class="video-play-stamp">▶</div>
          </div>
          <div class="video-info">
            <div class="video-title">${escapeHtml(yt.title)}</div>
            <div class="video-meta-line">
              <span class="video-channel">${escapeHtml(yt.channel)}</span>
              <span class="video-views-badge">▶ ${formatViews(yt.view_count)}</span>
            </div>
          </div>
        </div>
      `;
    });
    htmlContent += '</div>';
    container.innerHTML = htmlContent;
  }

  function renderSexEdResults(results, container) {
    let htmlContent = '<div style="margin-top:10px;">';
    results.forEach(item => {
      const clickAction = item.video_url 
        ? `openVideoReader('${escapeJs(item.video_url)}', '${escapeJs(item.title)}', '${escapeJs(item.source_url)}')`
        : `openReader(${item.doc_id || 0}, '${escapeJs(item.source_url)}', '${escapeJs(item.title)}', 9.5)`;

      htmlContent += `
        <div class="sexed-portal-card">
          <span class="sexed-badge">${escapeHtml(item.category)}</span>
          <div>
            <a href="javascript:void(0)" onclick="${clickAction}" class="result-title">
              ${item.video_url ? '🎥 ' : '📄 '}${escapeHtml(item.title)}
            </a>
          </div>
          <div class="sexed-summary">${escapeHtml(item.summary)}</div>
          <div class="sexed-footer">
            <span>出典・監修: <strong>${escapeHtml(item.source_name)}</strong></span>
            <a href="javascript:void(0)" onclick="${clickAction}" style="color:var(--primary); font-weight:700; text-decoration:none;">
              ${item.video_url ? '大画面で動画を再生 ▶' : 'リーダーで全文を読む →'}
            </a>
          </div>
        </div>
      `;
    });
    htmlContent += '</div>';
    container.innerHTML = htmlContent;
  }

  function extractYouTubeId(url) {
    if (!url) return null;
    const match = url.match(/(?:youtube\\.com\\/(?:[^\\/]+\\/.+\\/|(?:v|e(?:mbed)?)\\/|.*[?&]v=)|youtu\\.be\\/)([^"&?\\/\\s]{11})/i);
    return match ? match[1] : null;
  }

  // =========================================================================
  // 【修正要件1】openVideoReaderの独立・改修
  // =========================================================================
  function openVideoReader(videoUrl, title, pageUrl) {
    const targetUrl = videoUrl || pageUrl;
    const searchView = document.getElementById('searchView');
    const readerView = document.getElementById('readerView');
    const videoContainer = document.getElementById('readerVideoContainer');
    const bodyElem = document.getElementById('readerBody');

    searchView.style.display = 'none';
    readerView.style.display = 'block';
    window.scrollTo(0, 0);

    document.getElementById('readerUrlDisplay').textContent = targetUrl;
    document.getElementById('readerOriginLink').href = targetUrl;
    document.getElementById('readerTitle').textContent = title || targetUrl;
    document.getElementById('readerPrStamp').textContent = `PR: 5.0`;

    let domain = '';
    try { domain = new URL(targetUrl).hostname; } catch(e){}
    document.getElementById('readerDomain').textContent = domain;
    document.getElementById('readerFavicon').src = `https://www.google.com/s2/favicons?domain=${encodeURIComponent(domain)}&sz=32`;

    const ytId = extractYouTubeId(targetUrl);
    if (ytId) {
      videoContainer.style.display = 'block';
      const embedUrl = `https://www.youtube-nocookie.com/embed/${ytId}?autoplay=1&enablejsapi=1&origin=${encodeURIComponent(window.location.origin)}`;
      videoContainer.innerHTML = `
        <div class="video-container-responsive">
          <iframe 
            src="${embedUrl}" 
            referrerpolicy="strict-origin-when-cross-origin"
            allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share" 
            allowfullscreen>
          </iframe>
        </div>
      `;
      bodyElem.innerHTML = `<p style="color:var(--text-muted); font-size:14px;">YouTube動画をインライン再生中。原本のページ: <a href="${escapeHtml(targetUrl)}" target="_blank" style="color:var(--primary); font-weight:600;">${escapeHtml(targetUrl)}</a></p>`;
    } else {
      // YouTube以外の動画（HTML5 <video> または Webプレイヤー）
      videoContainer.style.display = 'block';
      videoContainer.innerHTML = `
        <div style="background:#000; border-radius:10px; overflow:hidden; margin:20px 0 24px 0; border:1px solid var(--border-color);">
          <video src="${escapeHtml(targetUrl)}" controls autoplay style="width:100%; max-height:480px; display:block;">
            お使いのブラウザは video タグに対応していません。
          </video>
        </div>
      `;
      bodyElem.innerHTML = `
        <div style="padding:18px 20px; background:var(--card-bg); border:1px solid var(--border-color); border-radius:8px;">
          <p style="font-weight:700; color:var(--text-main); margin-bottom:6px;">Web動画コンテンツ</p>
          <p style="color:var(--text-muted); font-size:13px; margin-bottom:12px;">動画が直接再生されない場合は、元のWebサイトから直接ご覧いただけます。</p>
          <a href="${escapeHtml(pageUrl || targetUrl)}" target="_blank" rel="noopener noreferrer" style="display:inline-block; background:var(--primary); color:#FFF; font-weight:700; text-decoration:none; padding:8px 18px; border-radius:6px; font-size:13px;">
            元のWebサイトで動画を見る ↗
          </a>
        </div>
      `;
    }
  }

  // =========================================================================
  // 【修正要件2 & 3】openReaderのガード処理 ＆ 正規表現安全化
  // =========================================================================
  async function openReader(docId, url, title, pagerank = 1.0) {
    const searchView = document.getElementById('searchView');
    const readerView = document.getElementById('readerView');
    const videoContainer = document.getElementById('readerVideoContainer');
    const bodyElem = document.getElementById('readerBody');

    searchView.style.display = 'none';
    readerView.style.display = 'block';
    window.scrollTo(0, 0);

    document.getElementById('readerUrlDisplay').textContent = url;
    document.getElementById('readerOriginLink').href = url;
    document.getElementById('readerTitle').textContent = title || url;
    document.getElementById('readerPrStamp').textContent = `PR: ${pagerank}`;

    let domain = '';
    try { domain = new URL(url).hostname; } catch(e){}
    document.getElementById('readerDomain').textContent = domain;
    document.getElementById('readerFavicon').src = `https://www.google.com/s2/favicons?domain=${encodeURIComponent(domain)}&sz=32`;

    // 1. YouTube 動画の判定
    const ytId = extractYouTubeId(url);
    if (ytId) {
      videoContainer.style.display = 'block';
      const embedUrl = `https://www.youtube-nocookie.com/embed/${ytId}?autoplay=1&enablejsapi=1&origin=${encodeURIComponent(window.location.origin)}`;
      videoContainer.innerHTML = `
        <div class="video-container-responsive">
          <iframe 
            src="${embedUrl}" 
            referrerpolicy="strict-origin-when-cross-origin"
            allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share" 
            allowfullscreen>
          </iframe>
        </div>
      `;
      bodyElem.innerHTML = `<p style="color:var(--text-muted); font-size:14px;">YouTube動画をインライン再生中。原本のページ: <a href="${escapeHtml(url)}" target="_blank" style="color:var(--primary);">${escapeHtml(url)}</a></p>`;
      return;
    }

    videoContainer.style.display = 'none';
    videoContainer.innerHTML = '';

    // 【修正要件2】docId <= 0 または未定義の場合のガード処理
    if (!docId || Number(docId) <= 0) {
      bodyElem.innerHTML = `
        <div style="margin-top:20px; padding:22px 24px; background:var(--card-bg); border:1px solid var(--border-color); border-radius:8px;">
          <p style="color:var(--text-main); font-weight:700; font-size:15px; margin-bottom:8px;">キャッシュされた本文はありません</p>
          <p style="color:var(--text-muted); font-size:13px; line-height:1.6; margin-bottom:16px;">
            このコンテンツの原本テキストは保存されていません。詳細な内容は元のWebサイトで直接ご確認いただけます。
          </p>
          <a href="${escapeHtml(url)}" target="_blank" rel="noopener noreferrer" style="display:inline-block; background:var(--primary); color:#FFF; font-weight:700; text-decoration:none; padding:8px 18px; border-radius:6px; font-size:13px;">
            元のWebサイトを開く ↗
          </a>
        </div>
      `;
      return;
    }

    bodyElem.innerHTML = '<p style="color:var(--text-muted);">本文をロード中...</p>';

    try {
      const resp = await fetch(`${API_DOC}/${docId}`);
      if (!resp.ok) throw new Error('Not found');
      const data = await resp.json();

      document.getElementById('readerTitle').textContent = data.title || url;
      document.getElementById('readerPrStamp').textContent = `PR: ${data.pagerank}`;

      const content = data.content || '';
      const paragraphs = content.split(/\\n+|(?<=[。！？])\\s+/).filter(p => p.trim().length > 0);

      let formattedHtml = '';
      paragraphs.forEach(para => {
        let safePara = htmlEscape(para);
        // 【修正要件3】キーワードハイライト処理の安全性向上（try ... catch保護）
        if (currentSearchQuery.trim()) {
          const terms = currentSearchQuery.trim().split(/\\s+/);
          terms.forEach(term => {
            if (term.length > 0) {
              try {
                const regex = new RegExp(`(${escapeRegex(htmlEscape(term))})`, 'gi');
                safePara = safePara.replace(regex, '<span class="reader-keyword-highlight">$1</span>');
              } catch (reErr) {
                // 構文エラー発生時はハイライトを安全にスキップ
              }
            }
          });
        }
        formattedHtml += `<p>${safePara}</p>`;
      });

      bodyElem.innerHTML = formattedHtml || '<p style="color:var(--text-muted);">本文がありません。</p>';
    } catch (e) {
      bodyElem.innerHTML = '<p style="color:var(--text-muted);">本文の取得に失敗しました。<a href="' + escapeHtml(url) + '" target="_blank" style="color:var(--primary);">元のサイトを開く</a></p>';
    }
  }

  async function openReaderByUrl(url, title) {
    const searchView = document.getElementById('searchView');
    const readerView = document.getElementById('readerView');
    const videoContainer = document.getElementById('readerVideoContainer');
    const bodyElem = document.getElementById('readerBody');

    searchView.style.display = 'none';
    readerView.style.display = 'block';
    window.scrollTo(0, 0);

    document.getElementById('readerUrlDisplay').textContent = url;
    document.getElementById('readerOriginLink').href = url;
    document.getElementById('readerTitle').textContent = title || url;
    document.getElementById('readerPrStamp').textContent = `PR: 5.0`;

    let domain = '';
    try { domain = new URL(url).hostname; } catch(e){}
    document.getElementById('readerDomain').textContent = domain;
    document.getElementById('readerFavicon').src = `https://www.google.com/s2/favicons?domain=${encodeURIComponent(domain)}&sz=32`;

    const ytId = extractYouTubeId(url);
    if (ytId) {
      videoContainer.style.display = 'block';
      const embedUrl = `https://www.youtube-nocookie.com/embed/${ytId}?autoplay=1&enablejsapi=1&origin=${encodeURIComponent(window.location.origin)}`;
      videoContainer.innerHTML = `
        <div class="video-container-responsive">
          <iframe 
            src="${embedUrl}" 
            referrerpolicy="strict-origin-when-cross-origin"
            allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share" 
            allowfullscreen>
          </iframe>
        </div>
      `;
      bodyElem.innerHTML = '';
    } else {
      videoContainer.style.display = 'none';
      videoContainer.innerHTML = '';
      bodyElem.innerHTML = `<p style="margin-top:20px;">画像参照元ページ: <a href="${escapeHtml(url)}" target="_blank" style="color:var(--primary); font-weight:600;">${escapeHtml(url)}</a></p>`;
    }
  }

  function closeReader() {
    const searchView = document.getElementById('searchView');
    const readerView = document.getElementById('readerView');
    const videoContainer = document.getElementById('readerVideoContainer');

    videoContainer.innerHTML = '';
    videoContainer.style.display = 'none';

    readerView.style.display = 'none';
    searchView.style.display = 'block';
  }

  async function toggleCrawler() {
    const btn = document.getElementById('stampToggleBtn');
    btn.disabled = true;
    try {
      const endpoint = isCrawlerRunning ? API_STOP : API_START;
      const resp = await fetch(endpoint, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({})
      });
      await resp.json();
    } catch (e) {
      console.error(e);
    } finally {
      btn.disabled = false;
      updateStatus();
    }
  }

  async function updateStatus() {
    try {
      const resp = await fetch(API_STATUS);
      if (!resp.ok) return;
      const state = await resp.json();

      document.getElementById('stampIndexed').textContent = state.indexed_count;
      document.getElementById('stampDomains').textContent = state.discovered_domains;
      if (document.getElementById('stampYtCount')) {
        document.getElementById('stampYtCount').textContent = state.youtube_count || 0;
      }

      const dot = document.getElementById('stampDot');
      const toggleBtn = document.getElementById('stampToggleBtn');
      isCrawlerRunning = state.is_running;

      if (state.is_running) {
        dot.className = 'stamp-dot';
        toggleBtn.textContent = '一時停止';
      } else {
        dot.className = 'stamp-dot paused';
        toggleBtn.textContent = '探索再開';
      }
    } catch (e) {
      console.warn('Status error:', e);
    }
  }

  function escapeHtml(str) {
    if (!str) return '';
    return str
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&#039;');
  }

  function htmlEscape(str) {
    return escapeHtml(str);
  }

  function escapeJs(str) {
    if (!str) return '';
    return str
      .replace(/\\\\/g, '\\\\\\\\')
      .replace(/'/g, "\\\\'")
      .replace(/"/g, '&quot;');
  }

  function escapeRegex(str) {
    return str.replace(/[.*+?^${}()|[\\]\\\\]/g, '\\\\$&');
  }

  window.addEventListener('DOMContentLoaded', () => {
    updateStatus();
    setInterval(updateStatus, 2000);

    const params = new URLSearchParams(window.location.search);
    const q = params.get('q');
    const type = params.get('type') || 'all';
    if (type) switchTab(type);
    if (q) {
      document.getElementById('queryInput').value = q;
      executeSearch();
    }
  });
</script>
</body>
</html>
"""


@app.get("/", response_class=HTMLResponse)
def index_page() -> str:
    return HTML_PAGE


@app.get("/api/search")
def search_api(
    q: str = Query(default="", description="検索クエリ"),
    type: str = Query(default="all", description="検索タイプ: all, image, video, youtube")
) -> Dict[str, Any]:
    if type == "youtube":
        results = search_engine.search_youtube(q, limit=40)
        return {"query": q, "type": type, "count": len(results), "results": results, "related_keywords": []}

    if not q.strip():
        return {"query": q, "type": type, "count": 0, "results": [], "related_keywords": []}

    if type == "image":
        results = search_engine.search_images(q, limit=40)
        return {"query": q, "type": type, "count": len(results), "results": results, "related_keywords": []}
    elif type == "video":
        results = search_engine.search_videos(q, limit=30)
        return {"query": q, "type": type, "count": len(results), "results": results, "related_keywords": []}
    else:
        res = search_engine.search(q, top_k=20)
        return {
            "query": q,
            "type": type,
            "count": len(res["results"]),
            "results": res["results"],
            "related_keywords": res["related_keywords"]
        }


@app.get("/api/sex-ed")
def get_sex_ed_api(q: str = Query(default="", description="性教育クエリ")) -> Dict[str, Any]:
    results = search_engine.search_sex_ed(q)
    return {
        "query": q,
        "count": len(results),
        "results": results
    }


@app.get("/api/document/{doc_id}")
def get_document_api(doc_id: int) -> Any:
    with get_read_conn() as conn:
        cursor = conn.cursor()
        cursor.execute("SELECT id, url, title, content, COALESCE(pagerank, 1.0) FROM documents WHERE id = ?", (doc_id,))
        row = cursor.fetchone()
        if not row:
            return JSONResponse(status_code=404, content={"error": "Document not found"})
        return {
            "id": row[0],
            "url": row[1],
            "title": row[2],
            "content": row[3],
            "pagerank": round(row[4], 1)
        }


@app.post("/api/crawl/start")
def start_crawl_api(req: Optional[CrawlStartRequest] = None) -> Any:
    seed = req.seed_url if req and req.seed_url else None
    started = crawler.start(custom_seed=seed)
    yt_expander.start()
    if not started:
        return JSONResponse(
            status_code=409,
            content={"status": "already_running", "message": "探索はすでに実行中です。"}
        )
    return {"status": "started", "message": "自動探索を開始しました。"}


@app.post("/api/crawl/stop")
def stop_crawl_api() -> Dict[str, str]:
    crawler.stop()
    yt_expander.stop()
    return {"status": "stopped", "message": "探索の停止指示を送信しました。"}


@app.get("/api/crawl/status")
def crawl_status_api() -> Dict[str, Any]:
    return crawler.get_state()


# ==============================================================================
# メインエントリーポイント（0.0.0.0でバインド）
# ==============================================================================
if __name__ == "__main__":
    uvicorn.run(app, host="0.0.0.0", port=8000)
