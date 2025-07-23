#!/usr/bin/env python3
"""
Cave Hacks Social Media Video Creator - Hetzner to DigitalOcean Production

Architecture:
- Runs on: Hetzner server (staging environment, IP: 5.161.70.26)  
- Posts to: Facebook, Instagram, Twitter, TikTok
- Database: DigitalOcean production MySQL
- Video Hosting: DigitalOcean production server

This script creates and posts daily Cave Hack videos to social media platforms.
It selects random products from the WooCommerce database, generates helpful tips,
creates videos with voiceovers and background music, and posts to all platforms.

Usage:
  python scripts/social_cave_hacks_video.py
"""

import os
import logging
import json
import pandas as pd
import time
import random
import requests
import traceback
from pathlib import Path
from urllib.parse import quote, urlencode, urlparse, parse_qs
from openai import OpenAI
import csv
from datetime import datetime, timedelta
import pytz
from fuzzywuzzy import fuzz
import base64
from dotenv import load_dotenv
from PIL import Image, ImageFont, ImageDraw
from requests_oauthlib import OAuth1, OAuth2Session
import tempfile
from functools import wraps
import numpy as np
import uuid
import sys
import re
import paramiko
import http.client as http_client
from moviepy.video.io.VideoFileClip import VideoFileClip
from moviepy.video.VideoClip import ImageClip, ColorClip
from moviepy.video.compositing.CompositeVideoClip import CompositeVideoClip
from moviepy.editor import concatenate_videoclips, concatenate_audioclips, AudioFileClip, ImageSequenceClip
from moviepy.audio.AudioClip import CompositeAudioClip, AudioClip
from moviepy.video.fx.all import resize
from moviepy.audio.fx.all import volumex, audio_fadeout
import shutil
import urllib.error
import io
from urllib.parse import urlencode
from dateutil import parser
import mysql.connector
from mysql.connector import Error
import gc
import psutil

# Set up project paths
project_root = "/opt/social-automation"
os.chdir(project_root)

# Import email relay after project_root is defined
sys.path.insert(0, project_root)
from email_relay import send_email_notification

# Load environment variables
dotenv_path = os.path.join(project_root, "credentials.env")
load_dotenv(dotenv_path)

# Set up logging
log_file_path = os.path.join(project_root, "logs", "cave_hacks_video_creation.log")

# Clear the log file at the beginning of each run
try:
    os.remove(log_file_path)
    print("Log file cleared.")
except FileNotFoundError:
    print("Log file does not exist yet.")

logging.basicConfig(
    level=logging.DEBUG,
    format="%(asctime)s - %(levelname)s - %(message)s",
    filename=log_file_path,
)
logger = logging.getLogger(__name__)

# Add a StreamHandler to print logs to the console
console_handler = logging.StreamHandler()
console_handler.setLevel(logging.DEBUG)
logger.addHandler(console_handler)

# Disable other loggers
logging.getLogger("requests").setLevel(logging.WARNING)
logging.getLogger("urllib3").setLevel(logging.WARNING)
logging.getLogger("paramiko").setLevel(logging.WARNING)

# Enable HTTP debugging
http_client.HTTPConnection.debuglevel = 0

# Force the script to use UTF-8 encoding
sys.stdout.reconfigure(encoding='utf-8')

logging.info(f"Cave Hacks Video Creator started - Hetzner to Social Media Platforms")
logging.info(f"Project root: {project_root}")
logging.info(f"Log file: {log_file_path}")

# File paths updated for new structure
logo_end_screen_path = os.path.join(project_root, "assets", "logos", "logo-white-thorak.png")
cave_hack_subjects_file = os.path.join(project_root, "data", "cave_hack_subjects.csv")
product_blacklist_file = os.path.join(project_root, "data", "posted_products_blacklist.csv")
image_descriptions_file = os.path.join(project_root, "data", "image_descriptions.json")
SOUND_DOWNLOAD_FOLDER = os.path.join(project_root, "assets", "sounds")
FREESOUND_PLACEHOLDER = os.path.join(project_root, "assets", "sounds", "freesound_placeholder.mp3")
SONG_HISTORY_FILE = os.path.join(project_root, "data", "song_history.csv")
TIKTOK_TOKEN_FILE = os.path.join(project_root, "data", "tiktok_tokens.json")

# Constants
SONG_REUSE_DAYS = 14

# Environment variables
OPENAI_API_KEY = os.getenv("OPENAI_API_KEY")
BITLY_API_KEY = os.getenv("BITLY_API_KEY")
FB_ACCESS_TOKEN = quote(os.getenv("FB_ACCESS_TOKEN"))
FB_PAGE_ID = os.getenv("FB_PAGE_ID")
INSTAGRAM_BUSINESS_ACCOUNT_ID = os.getenv("INSTAGRAM_BUSINESS_ACCOUNT_ID")
TWITTER_API_KEY = os.getenv("TWITTER_API_KEY")
TWITTER_API_SECRET = os.getenv("TWITTER_API_SECRET")
TWITTER_ACCESS_TOKEN = os.getenv("TWITTER_ACCESS_TOKEN")
TWITTER_ACCESS_TOKEN_SECRET = os.getenv("TWITTER_ACCESS_TOKEN_SECRET")
GOOGLE_SHEET_CSV_URL = os.getenv("GOOGLE_SHEET_CSV_URL")
ELEVENLABS_API_KEY = os.getenv("ELEVENLABS_API_KEY")
FREESOUND_API_KEY = os.getenv("FREESOUND_API_KEY")
SFTP_HOST = os.getenv("SFTP_HOST")
SFTP_USERNAME = os.getenv("SFTP_USERNAME")
SFTP_PASSWORD = os.getenv("SFTP_PASSWORD")

# TikTok configuration
TIKTOK_INIT_UPLOAD_URL = "https://open.tiktokapis.com/v2/post/publish/inbox/video/init/"
TIKTOK_CHECK_STATUS_URL = "https://open.tiktokapis.com/v2/post/publish/status/fetch/"
TIKTOK_CLIENT_KEY = os.getenv("TIKTOK_CLIENT_KEY")
TIKTOK_CLIENT_SECRET = os.getenv("TIKTOK_CLIENT_SECRET")
TIKTOK_REDIRECT_URI = "https://www.cavesupplies.com/callback"

# Database configuration (DigitalOcean Production)
DB_HOST = os.getenv("DB_HOST")
DB_USER = os.getenv("DB_USER")
DB_PASSWORD = os.getenv("DB_PASSWORD")
DB_NAME = os.getenv("DB_NAME")

# Initialize OpenAI client
client = OpenAI(api_key=OPENAI_API_KEY)

# Ensure required directories exist
os.makedirs(os.path.join(project_root, "logs"), exist_ok=True)
os.makedirs(os.path.join(project_root, "data"), exist_ok=True)
os.makedirs(SOUND_DOWNLOAD_FOLDER, exist_ok=True)

logger.info(f"DB_HOST: {DB_HOST}")
logger.info(f"DB_USER: {DB_USER}")
logger.info(f"DB_NAME: {DB_NAME}")

class DatabaseConfig:
    def __init__(self):
        self.host = DB_HOST
        self.user = DB_USER
        self.password = DB_PASSWORD
        self.name = DB_NAME

# Ensure all required TikTok variables are set
required_tiktok_vars = ["TIKTOK_CLIENT_KEY", "TIKTOK_CLIENT_SECRET", "TIKTOK_REDIRECT_URI"]
missing_vars = [var for var in required_tiktok_vars if not os.getenv(var)]
if missing_vars:
    logger.error(f"Missing required TikTok environment variables: {', '.join(missing_vars)}")
    raise ValueError(f"Missing required TikTok environment variables: {', '.join(missing_vars)}")

# Define OBJECT_CATEGORIES globally
OBJECT_CATEGORIES = [
    "coffee table", "led coffee table", "modular coffee table",
    "furniture", "living room furniture", "loveseat", "sofa",
    "home theater projector", "game room furniture", "games", "game table",
    "chairs", "seating", "gaming chair", "gaming desk",
    "end table", "side table", "media storage", "recliner", "sectional",
    "appliance", "beverage cooler", "electronics", "floor lamp",
    "lighting", "bar furniture", "bar stool", "counter stool",
    "bean bag chair", "home decor", "area rug", "rug",
    "audio", "audio system", "soundbar", "table lamp",
    "wall art", "video", "bar cabinet", "wine rack",
    "home theater furniture", "home theater seating",
    "tv stand", "entertainment center", "office chair",
    "office furniture", "bar table", "pub table", "bookcase", "desk",
    "compact refrigerator", "wall lamp",
    "lift top coffee table", "l-shaped sofa", "convertible sofa",
    "ottoman", "accent chair", "papasan chair", "chesterfield sofa",
    "tufted sofa", "sleeper sofa", "futon", "armchair",
    "foosball table", "pool table", "multi-game table", "poker table",
    "air hockey table", "ping pong table",
    "led strip light", "wall sconce", "floor mirror with lights",
    "pendant light", "chandelier", "task lamp", "desk lamp",
    "soundbar with subwoofer", "surround sound system", "bluetooth speaker",
    "home theater receiver", "projector screen",
    "wine cabinet", "liquor cabinet", "media console", "storage ottoman",
    "shoe rack", "coat rack", "floating shelves",
    "mini fridge", "beverage cooler", "wine cooler", "kegerator",
    "ice maker", "popcorn machine",
    "l-shaped desk", "standing desk", "ergonomic chair", "file cabinet",
    "printer stand", "cable management system",
    "wall clock", "full-length mirror", "canvas art", "neon sign",
    "throw pillow", "tapestry", "decorative tray",
    "dartboard", "bar sign", "sports memorabilia", "vintage poster",
    "record player", "cigar humidor", "poker chip set",
    "outdoor bar", "patio furniture", "fire pit", "outdoor tv",
    "bbq grill", "outdoor refrigerator",
    "smart home device", "gaming console", "virtual reality headset",
    "streaming device", "wireless charger",
    "exercise equipment", "yoga mat", "massage chair", "sauna",
    "throw blanket", "coaster set", "bar tools", "whiskey decanter",
    "record storage", "man cave sign"
]

def notify_reauthorization_required(service="Freesound"):
    subject = f"{service} Reauthorization Required - Hetzner Social Automation"
    body = f"The {service} token has expired and could not be refreshed automatically. Please run the script manually to reauthorize."
    send_notification_email(subject, body)
    logger.critical(f"{service} reauthorization required. Notification sent.")

def search_music_by_tags(tags, max_results=20, page=1):
    params = {
        'query': f'{tags} music',
        'fields': 'id,name,previews,ac_analysis,tags',
        'filter': 'duration:[30 TO 300]',
        'page_size': max_results,
        'page': page,
        'token': FREESOUND_API_KEY
    }

    try:
        response = requests.get('https://freesound.org/apiv2/search/text/', params=params, timeout=30)
        response.raise_for_status()

        json_response = response.json()
        results = json_response.get('results', [])
        logger.debug(f"Raw API response: {json_response}")
        logger.debug(f"Number of results before filtering: {len(results)}")
        
        filtered_results = []
        for r in results:
            if r is None:
                logger.warning("Encountered None result")
                continue
            if is_music(r):
                filtered_results.append(r)
            else:
                logger.debug(f"Filtered out non-music result: {r.get('name', 'Unknown')}")
        
        logger.debug(f"Number of results after filtering: {len(filtered_results)}")
        
        if filtered_results:
            logger.info(f"Found {len(filtered_results)} music results for tags: {tags}")
            return filtered_results
        elif page < 5:
            logger.info(f"No music results found on page {page} for tags: {tags}. Trying next page.")
            return search_music_by_tags(tags, max_results, page + 1)
        else:
            logger.info(f"No music results found after 5 pages for tags: {tags}")
            return None
    except requests.exceptions.RequestException as e:
        logger.error(f"Error fetching data from Freesound: {str(e)}")
        return None

def is_music(sound_data):
    if not sound_data:
        return False
    
    if not isinstance(sound_data, dict):
        return False
    
    ac_analysis = sound_data.get('ac_analysis')
    if ac_analysis and isinstance(ac_analysis, dict):
        if ac_analysis.get('ac_is_music', False):
            return True
    
    tags = sound_data.get('tags', [])
    if isinstance(tags, list):
        if 'music' in tags:
            return True
        
        instruments = ['piano', 'guitar', 'violin', 'drums', 'saxophone', 'flute']
        if any(instrument in tags for instrument in instruments):
            return True
    
    return False

def download_music(result):
    # Prefer high-quality preview; fallback to low-quality if unavailable
    preview_url = result['previews'].get('preview-hq-mp3') or result['previews'].get('preview-lq-mp3')
    if not preview_url:
        logger.error(f"No preview URL available for sound: {result.get('name', 'Unknown')}")
        return None

    try:
        with tempfile.NamedTemporaryFile(delete=False, suffix='.mp3') as temp_file:
            temp_music_path = temp_file.name
            response = requests.get(preview_url, stream=True, timeout=60)
            response.raise_for_status()
            for chunk in response.iter_content(chunk_size=8192):
                if chunk:
                    temp_file.write(chunk)
        
        if os.path.exists(temp_music_path) and os.path.getsize(temp_music_path) > 0:
            try:
                audio = AudioFileClip(temp_music_path)
                duration = audio.duration
                audio.close()
                logger.info(f"Downloaded and verified sound: {result['name']} (duration: {duration}s)")
                return temp_music_path
            except Exception as e:
                logger.error(f"Error verifying audio file: {e}")
                os.unlink(temp_music_path)
                return None
        else:
            logger.error(f"Downloaded file is empty or does not exist: {temp_music_path}")
            return None
    except requests.RequestException as e:
        logger.error(f"Failed to download sound: {result['name']} (Error: {str(e)})")
        return None

def load_song_history():
    if not os.path.exists(SONG_HISTORY_FILE):
        return {}
    
    song_history = {}
    with open(SONG_HISTORY_FILE, 'r', newline='') as csvfile:
        reader = csv.reader(csvfile)
        for row in reader:
            song_history[row[0]] = datetime.fromisoformat(row[1])
    return song_history

def save_song_history(song_history):
    with open(SONG_HISTORY_FILE, 'w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        for song_id, use_date in song_history.items():
            writer.writerow([song_id, use_date.isoformat()])

def is_song_recently_used(song_id, song_history):
    if song_id in song_history:
        last_use_date = song_history[song_id]
        return (datetime.now() - last_use_date) < timedelta(days=SONG_REUSE_DAYS)
    return False

def update_song_history(song_id, song_history):
    song_history[song_id] = datetime.now()
    save_song_history(song_history)

def send_notification_email(subject, body):
    """Send email notification using the relay"""
    # Format like old notifications
    formatted_body = f"""Cave Hacks Social Media Automation Report
Source Server: Hetzner (5.161.70.26)
Project: /opt/social-automation

{body}

Log file: {log_file_path}"""
    
    return send_email_notification(subject, formatted_body, is_error=True)

def load_cave_hack_subjects():
    cave_hack_subjects = {}
    if os.path.exists(cave_hack_subjects_file):
        with open(cave_hack_subjects_file, 'r') as f:
            reader = csv.reader(f)
            next(reader)  # Skip header row
            for row in reader:
                cave_hack_subjects[row[0]] = datetime.strptime(row[1], '%Y-%m-%d').date()
    return cave_hack_subjects

def save_cave_hack_subjects(cave_hack_subjects):
    with open(cave_hack_subjects_file, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(["Subject", "Date"])  # Write header row
        for subjects, date in cave_hack_subjects.items():
            writer.writerow([subjects, date.strftime('%Y-%m-%d')])

def can_use_subject(subjects, cave_hack_subjects):
    today = datetime.now().date()
    for subject in subjects:
        last_used_date = cave_hack_subjects.get(subject)
        if last_used_date and (today - last_used_date).days < 7:
            return False  # At least one subject was used within the last 7 days
    return True  # All subjects can be used

def load_product_blacklist():
    product_blacklist = {}
    if os.path.exists(product_blacklist_file):
        with open(product_blacklist_file, 'r') as f:
            reader = csv.reader(f)
            next(reader)  # Skip header row
            for row in reader:
                product_blacklist[row[0]] = datetime.strptime(row[1], '%Y-%m-%d %H:%M:%S').date()
    return product_blacklist

def save_product_blacklist(product_blacklist):
    with open(product_blacklist_file, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(["Product ID", "Date"])  # Write header row
        for product_id, date in product_blacklist.items():
            writer.writerow([product_id, date.strftime('%Y-%m-%d')])

def get_random_product(db_config):
    try:
        with mysql.connector.connect(
            host=db_config.host,
            user=db_config.user,
            password=db_config.password,
            database=db_config.name
        ) as connection:
            with connection.cursor(dictionary=True) as cursor:
                query = """
                WITH random_product AS (
                    SELECT p.ID 
                    FROM wp_posts p
                    JOIN wp_postmeta stock ON p.ID = stock.post_id 
                        AND stock.meta_key = '_stock_status' 
                        AND stock.meta_value = 'instock'
                    WHERE p.post_type = 'product'
                    AND p.post_status = 'publish'
                    AND p.ID NOT IN (
                        SELECT ID 
                        FROM posted_products_blacklist 
                        WHERE Timestamp > DATE_SUB(NOW(), INTERVAL 7 DAY)
                    )
                    ORDER BY RAND()
                    LIMIT 1
                )
                SELECT 
                    p.ID,
                    p.post_title as Title,
                    p.post_content as Content, 
                    p.post_excerpt as Short_Description,
                    p.guid as URL,
                    MAX(CASE WHEN pm.meta_key = '_sku' THEN pm.meta_value END) as SKU,
                    MAX(CASE WHEN pm.meta_key = '_stock_status' THEN pm.meta_value END) as Stock_Status,
                    MAX(CASE WHEN pm.meta_key = '_thumbnail_id' THEN pm.meta_value END) as Thumbnail_ID,
                    GROUP_CONCAT(DISTINCT terms.name SEPARATOR ', ') as Product_Categories,
                    p.post_status as Status,
                    (SELECT guid FROM wp_posts WHERE ID = MAX(CASE WHEN thumbnail.meta_key = '_thumbnail_id' THEN thumbnail.meta_value END)) as Image_URLs
                FROM wp_posts p
                JOIN random_product rp ON p.ID = rp.ID
                JOIN wp_postmeta pm ON p.ID = pm.post_id
                LEFT JOIN wp_postmeta thumbnail ON p.ID = thumbnail.post_id 
                    AND thumbnail.meta_key = '_thumbnail_id'
                LEFT JOIN wp_term_relationships tr ON p.ID = tr.object_id
                LEFT JOIN wp_term_taxonomy tt ON tr.term_taxonomy_id = tt.term_taxonomy_id 
                    AND tt.taxonomy = 'product_cat'
                LEFT JOIN wp_terms terms ON tt.term_id = terms.term_id
                WHERE pm.meta_key IN ('_sku', '_stock_status', '_thumbnail_id')
                GROUP BY p.ID, p.post_title, p.post_content, p.post_excerpt, p.guid, p.post_status
                """
                cursor.execute(query)
                return cursor.fetchone()
    except mysql.connector.Error as error:
        logger.error(f"Failed to get random product from database: {error}")
        return None

def add_to_blacklist(product_id, db_config):
    try:
        with mysql.connector.connect(
            host=db_config.host,
            user=db_config.user,
            password=db_config.password,
            database=db_config.name
        ) as connection:
            with connection.cursor() as cursor:
                # The table already exists, so we just need to insert
                query = """
                    INSERT INTO posted_products_blacklist (ID) 
                    VALUES (%s)
                """
                cursor.execute(query, (product_id,))
                connection.commit()
                logger.info(f"Added product {product_id} to blacklist")
                return True
    except mysql.connector.Error as error:
        logger.error(f"Failed to add product to blacklist: {error}")
        return False

def is_product_blacklisted(product_id, db_config):
    try:
        with mysql.connector.connect(
            host=db_config.host,
            user=db_config.user,
            password=db_config.password,
            database=db_config.name
        ) as connection:
            with connection.cursor() as cursor:
                query = "SELECT COUNT(*) FROM posted_products_blacklist WHERE ID = %s"
                cursor.execute(query, (product_id,))
                count = cursor.fetchone()[0]
                return count > 0
    except mysql.connector.Error as e:
        logger.error(f"Error checking product blacklist: {e}")
        return False

def load_image_descriptions():
    image_descriptions = {}
    if os.path.exists(image_descriptions_file):
        with open(image_descriptions_file, 'r') as f:
            image_descriptions = json.load(f)
    return image_descriptions

def save_image_descriptions(image_descriptions):
    with open(image_descriptions_file, 'w') as f:
        json.dump(image_descriptions, f, indent=4)

def generate_social_media_content(prompt, max_tokens=150, temperature=0.7):
    max_retries = 3
    for attempt in range(max_retries):
        try:
            logger.debug(f"Calling OpenAI with prompt: {prompt[:50]}...")
            headers = {
                "Authorization": f"Bearer {OPENAI_API_KEY}",
                "Content-Type": "application/json"
            }
            data = {
                "model": "gpt-4o-2024-08-06",
                "messages": [{"role": "user", "content": prompt}],
                "max_tokens": max_tokens,
                "temperature": temperature,
            }
            response = requests.post(
                "https://api.openai.com/v1/chat/completions", headers=headers, json=data, timeout=60
            )
            response.raise_for_status()
            response_data = response.json()
            result = response_data['choices'][0]['message']['content']
            logger.debug(f"OpenAI response: {result[:50]}...")
            return result.strip()
        except Exception as e:
            logger.error(f"Error calling OpenAI (attempt {attempt + 1}): {str(e)}")
            if attempt == max_retries - 1:
                logger.error("Failed to get response from OpenAI after maximum retries.")
                raise
            time.sleep(2**attempt)  # Exponential backoff

def shorten_url(long_url):
    headers = {
        "Authorization": f"Bearer {BITLY_API_KEY}",
        "Content-Type": "application/json",
    }
    data = {"long_url": long_url}
    try:
        response = requests.post(
            "https://api-ssl.bitly.com/v4/shorten", headers=headers, json=data, timeout=30
        )
        response_data = response.json()
        
        if 'link' in response_data:
            logger.info(f"Successfully shortened URL {long_url} to {response_data['link']}")
            return response_data["link"]
        else:
            logger.error(f"Bitly failed to shorten URL {long_url}: {response_data}")
            return long_url
    except Exception as e:
        logger.error(f"Exception occurred while shortening URL {long_url}: {str(e)}")
        return long_url

def retry_on_failure(max_retries=3, backoff_factor=2):
    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            for attempt in range(max_retries):
                try:
                    return func(*args, **kwargs)
                except requests.exceptions.HTTPError as e:
                    if e.response.status_code == 429:
                        retry_after = int(e.response.headers.get('Retry-After', backoff_factor ** attempt))
                        logger.warning(f"Rate limit exceeded. Retrying after {retry_after} seconds.")
                        time.sleep(retry_after)
                    else:
                        logger.warning(f"Attempt {attempt + 1}/{max_retries} failed: {str(e)}")
                        if attempt == max_retries - 1:
                            raise
                        time.sleep(backoff_factor ** attempt)
                except Exception as e:
                    logger.warning(f"Attempt {attempt + 1}/{max_retries} failed: {str(e)}")
                    if attempt == max_retries - 1:
                        raise
                    time.sleep(backoff_factor ** attempt)
        return wrapper
    return decorator

def post_video_to_facebook(message, video_url, page_id, access_token):
    session = requests.Session()
    url = f"https://graph.facebook.com/v18.0/{page_id}/videos"
    payload = {
        "description": message,
        "access_token": access_token,
        "file_url": video_url,
    }
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36"
    }
    logger.debug(f"Facebook API URL: {url}")
    
    filtered_payload = {k: v for k, v in payload.items() if k != 'access_token'}
    logger.debug(f"Payload (excluding access_token): {json.dumps(filtered_payload)}")
    logger.debug(f"Token being used: {access_token[:10]}...{access_token[-10:]}")

    try:
        response = session.post(url, data=payload, headers=headers, timeout=120)
        response.raise_for_status()

        logger.debug(f"Facebook API Response Status: {response.status_code}")
        logger.debug(f"Facebook API Response Content: {response.text}")

        if response.status_code == 200:
            logger.info("Successfully posted video on Facebook.")
            return True
        else:
            logger.error(f"Failed to post video on Facebook. Status code: {response.status_code}")
            logger.error(f"Response content: {response.text}")
            return False
    except requests.exceptions.RequestException as e:
        logger.error(f"Request to Facebook API failed: {str(e)}")
        if hasattr(e, 'response'):
            logger.error(f"Response content: {e.response.text}")
        return False
    except Exception as e:
        logger.error(f"Unexpected error when posting on Facebook: {str(e)}")
        return False

def post_video_to_instagram(message, video_url, max_retries=20, retry_delay=10):
    """
    Posts a video as a Reel to Instagram using the Facebook Graph API.
    """
    # Step 1: Create a container for the reel
    container_url = f"https://graph.facebook.com/v18.0/{INSTAGRAM_BUSINESS_ACCOUNT_ID}/media"
    container_payload = {
        "media_type": "REELS",
        "video_url": video_url,
        "caption": message,
        "access_token": FB_ACCESS_TOKEN
    }
    try:
        container_response = requests.post(container_url, json=container_payload, timeout=60)
        container_response.raise_for_status()
        creation_id = container_response.json()['id']
        logger.info(f"Instagram media container created with ID: {creation_id}")
        
        # Step 2: Check media status
        status_url = f"https://graph.facebook.com/v18.0/{creation_id}?fields=status_code,status"
        for attempt in range(max_retries):
            status_response = requests.get(status_url, params={"access_token": FB_ACCESS_TOKEN}, timeout=60)
            status_response.raise_for_status()
            status_data = status_response.json()
            
            if status_data.get('status_code') == 'FINISHED':
                logger.info("Media processing completed. Attempting to publish.")
                break
            elif status_data.get('status_code') in ['IN_PROGRESS', 'PROCESSING']:
                logger.info(f"Media still processing. Waiting {retry_delay} seconds before retry. Attempt {attempt + 1}/{max_retries}")
                time.sleep(retry_delay)
            else:
                logger.error(f"Unexpected status: {status_data}")
                return False
        else:
            logger.error(f"Media did not finish processing after {max_retries} attempts.")
            return False
        
        # Step 3: Publish the reel
        publish_url = f"https://graph.facebook.com/v18.0/{INSTAGRAM_BUSINESS_ACCOUNT_ID}/media_publish"
        publish_payload = {
            "creation_id": creation_id,
            "access_token": FB_ACCESS_TOKEN
        }
        
        publish_response = requests.post(publish_url, json=publish_payload, timeout=60)
        publish_response.raise_for_status()
        
        logger.info("Successfully posted Reel to Instagram.")
        return True
    
    except requests.exceptions.RequestException as e:
        logger.error(f"Failed to post Reel to Instagram. Error: {str(e)}")
        if hasattr(e, 'response'):
            logger.error(f"Response content: {e.response.text}")
        return False

@retry_on_failure(max_retries=3, backoff_factor=2)
def upload_media_to_twitter(video_path, auth):
    media_upload_url = "https://upload.twitter.com/1.1/media/upload.json"
    total_bytes = os.path.getsize(video_path)
    
    # Initialize upload
    init_data = {
        'command': 'INIT',
        'total_bytes': total_bytes,
        'media_type': 'video/mp4',
        'media_category': 'tweet_video'
    }
    try:
        init_response = requests.post(media_upload_url, auth=auth, data=init_data, timeout=60)
        init_response.raise_for_status()
        media_id = init_response.json()['media_id_string']
        logger.debug(f"Initialized Twitter media upload. Media ID: {media_id}")
    except Exception as e:
        logger.error(f"Failed to initialize Twitter media upload: {str(e)}")
        raise

    # Upload chunks
    segment_id = 0
    bytes_sent = 0
    try:
        with open(video_path, 'rb') as video_file:
            while bytes_sent < total_bytes:
                chunk = video_file.read(4*1024*1024)  # 4MB chunks
                append_data = {
                    'command': 'APPEND',
                    'media_id': media_id,
                    'segment_index': segment_id,
                }
                files = {'media': chunk}
                append_response = requests.post(media_upload_url, auth=auth, data=append_data, files=files, timeout=120)
                append_response.raise_for_status()
                logger.debug(f"Uploaded segment {segment_id} to Twitter.")
                segment_id += 1
                bytes_sent += len(chunk)
    except Exception as e:
        logger.error(f"Failed to upload Twitter media chunks: {str(e)}")
        raise
    
    # Finalize upload
    finalize_data = {
        'command': 'FINALIZE',
        'media_id': media_id,
    }
    try:
        finalize_response = requests.post(media_upload_url, auth=auth, data=finalize_data, timeout=60)
        finalize_response.raise_for_status()
        logger.debug(f"Finalized Twitter media upload. Response: {finalize_response.json()}")
    except Exception as e:
        logger.error(f"Failed to finalize Twitter media upload: {str(e)}")
        raise
    
    # Check processing status
    processing_info = finalize_response.json().get('processing_info', {})
    while processing_info.get('state') in ('pending', 'in_progress'):
        check_after_secs = processing_info.get('check_after_secs', 5)
        logger.info(f"Twitter media processing {processing_info['state']}, waiting {check_after_secs} seconds.")
        time.sleep(check_after_secs)
        try:
            status_response = requests.get(media_upload_url, params={'command': 'STATUS', 'media_id': media_id}, auth=auth, timeout=60)
            status_response.raise_for_status()
            processing_info = status_response.json().get('processing_info', {})
        except Exception as e:
            logger.error(f"Error checking Twitter media status: {str(e)}")
            raise
    
    if processing_info.get('state') == 'succeeded':
        logger.info(f"Twitter media processing completed. Media ID: {media_id}")
        return media_id
    else:
        error_message = processing_info.get('error', {}).get('message', 'Unknown error')
        logger.error(f"Twitter media processing failed: {error_message}")
        return None

@retry_on_failure(max_retries=3, backoff_factor=2)
def post_to_twitter_v2(status, media_id=None):
    url = "https://api.twitter.com/2/tweets"
    headers = {"Content-Type": "application/json"}
    payload = {"text": status}
    if media_id:
        payload["media"] = {"media_ids": [media_id]}
    
    auth = OAuth1(TWITTER_API_KEY, TWITTER_API_SECRET, TWITTER_ACCESS_TOKEN, TWITTER_ACCESS_TOKEN_SECRET)
    
    try:
        response = requests.post(url, auth=auth, json=payload, headers=headers, timeout=60)
        response.raise_for_status()
        
        if response.status_code == 201:
            logger.info("Successfully posted to Twitter (v2) using OAuth 1.0a.")
            return True
        else:
            logger.error(f"Unexpected status code from Twitter API: {response.status_code}")
            logger.error(f"Response content: {response.text}")
            return False
        
    except requests.exceptions.HTTPError as e:
        logger.error(f"HTTP error occurred while posting to Twitter: {e}")
        logger.error(f"Response status code: {e.response.status_code}")
        logger.error(f"Response content: {e.response.text}")
        
        if e.response.status_code == 403:
            logger.error("403 Forbidden error. Possible reasons:")
            logger.error("1. Incorrect API keys or access tokens")
            logger.error("2. Account doesn't have permission to post tweets")
            logger.error("3. Account is suspended or restricted")
        elif e.response.status_code == 429:
            logger.error("429 Too Many Requests error. You may have hit rate limits.")
        
        return False
    
    except Exception as e:
        logger.error(f"Unexpected error occurred while posting to Twitter: {str(e)}")
        return False

def twitter_post_with_media(status, video_path):
    try:
        auth = OAuth1(TWITTER_API_KEY, TWITTER_API_SECRET, TWITTER_ACCESS_TOKEN, TWITTER_ACCESS_TOKEN_SECRET)
        
        # Upload media
        media_id = upload_media_to_twitter(video_path, auth)
        if not media_id:
            logger.error("Failed to upload media to Twitter.")
            return False
        
        # Post tweet with media
        success = post_to_twitter_v2(status, media_id)
        if success:
            logger.info(f"Successfully posted tweet with media: {status[:50]}...")
            return True
        else:
            logger.error("Failed to post tweet with media.")
            return False
    
    except Exception as e:
        logger.error(f"Error in twitter_post_with_media: {str(e)}")
        return False

# TikTok-specific functions
def load_tiktok_tokens():
    """Load TikTok tokens and update global variables"""
    if not os.path.exists(TIKTOK_TOKEN_FILE):
        logger.warning(f"{TIKTOK_TOKEN_FILE} does not exist.")
        return None, None
    try:
        with open(TIKTOK_TOKEN_FILE, 'r') as f:
            tokens = json.load(f)
        access_token = tokens.get("TIKTOK_ACCESS_TOKEN")
        refresh_token = tokens.get("TIKTOK_REFRESH_TOKEN")
        if not access_token or not refresh_token:
            logger.warning("TikTok tokens are missing in tiktok_tokens.json.")
            return None, None
        return access_token, refresh_token
    except json.JSONDecodeError as e:
        logger.error(f"JSON decode error while reading {TIKTOK_TOKEN_FILE}: {e}")
        return None, None
    except Exception as e:
        logger.error(f"Unexpected error while reading {TIKTOK_TOKEN_FILE}: {e}")
        return None, None

def save_tiktok_tokens(access_token, refresh_token):
    """Save TikTok access and refresh tokens to tiktok_tokens.json"""
    token_data = {
        "TIKTOK_ACCESS_TOKEN": access_token,
        "TIKTOK_REFRESH_TOKEN": refresh_token
    }
    try:
        with open(TIKTOK_TOKEN_FILE, 'w') as f:
            json.dump(token_data, f, indent=4)
        logger.info("TikTok Access and Refresh tokens have been updated successfully in tiktok_tokens.json.")
    except PermissionError as e:
        logger.error(f"Permission denied while writing to {TIKTOK_TOKEN_FILE}: {e}")
        raise
    except Exception as e:
        logger.error(f"Unexpected error while writing to {TIKTOK_TOKEN_FILE}: {e}")
        raise

def refresh_tiktok_token():
    """Refresh TikTok access token using the refresh token"""
    access_token, refresh_token = load_tiktok_tokens()
    if not refresh_token:
        logger.error("No refresh token available to refresh TikTok access token.")
        return False

    refresh_url = "https://open.tiktokapis.com/v2/oauth/token/"
    data = {
        "client_key": TIKTOK_CLIENT_KEY,
        "client_secret": TIKTOK_CLIENT_SECRET,
        "grant_type": "refresh_token",
        "refresh_token": refresh_token
    }
    headers = {'Content-Type': 'application/x-www-form-urlencoded'}

    try:
        logger.info("Refreshing TikTok access token...")
        response = requests.post(refresh_url, data=data, headers=headers, timeout=60)
        response.raise_for_status()
        token_data = response.json()

        if 'access_token' in token_data:
            new_access_token = token_data['access_token']
            new_refresh_token = token_data.get('refresh_token', refresh_token)

            logger.info("TikTok tokens have been refreshed successfully.")
            save_tiktok_tokens(new_access_token, new_refresh_token)
            return True
        else:
            logger.error(f"Failed to refresh TikTok token. Unexpected response structure: {token_data}")
            return False
    except requests.exceptions.RequestException as e:
        logger.error(f"Request Exception while refreshing TikTok token: {e}")
        return False
    except Exception as e:
        logger.error(f"Unexpected error while refreshing TikTok token: {e}")
        return False

def validate_tiktok_token():
    """Validate the current TikTok access token"""
    access_token, _ = load_tiktok_tokens()
    if not access_token:
        logger.warning("No TikTok access token found.")
        return False

    validate_url = "https://open.tiktokapis.com/v2/user/info/"
    headers = {'Authorization': f'Bearer {access_token}'}

    try:
        response = requests.get(validate_url, headers=headers, timeout=30)
        if response.status_code == 200:
            logger.info("TikTok token is valid.")
            return True
        else:
            logger.warning("TikTok token may be invalid. Attempting to refresh...")
            return False
    except requests.exceptions.RequestException as e:
        logger.error(f"Request exception while validating TikTok token: {e}")
        return False
    except Exception as e:
        logger.error(f"Unexpected error while validating TikTok token: {e}")
        return False

def get_tiktok_authorization_url():
    """Generate the TikTok authorization URL for manual reauthorization"""
    try:
        params = {
            "client_key": TIKTOK_CLIENT_KEY,
            "response_type": "code",
            "scope": "user.info.basic,video.upload",
            "redirect_uri": TIKTOK_REDIRECT_URI,
            "state": "state"
        }
        url = f"https://www.tiktok.com/v2/auth/authorize/?{urlencode(params)}"
        logger.info(f"Generated TikTok authorization URL: {url}")
        return url
    except Exception as e:
        logger.error(f"Failed to generate TikTok authorization URL: {str(e)}")
        return None

def exchange_code_for_token(code):
    """Exchange the authorization code for access and refresh tokens"""
    token_url = "https://open.tiktokapis.com/v2/oauth/token/"
    data = {
        "client_key": TIKTOK_CLIENT_KEY,
        "client_secret": TIKTOK_CLIENT_SECRET,
        "code": code,
        "grant_type": "authorization_code",
        "redirect_uri": TIKTOK_REDIRECT_URI
    }
    headers = {'Content-Type': 'application/x-www-form-urlencoded'}
    try:
        response = requests.post(token_url, data=data, headers=headers, timeout=60)
        response.raise_for_status()
        return response.json()
    except Exception as e:
        logger.error(f"Error exchanging code for token: {e}")
        raise

def reauthorize_tiktok():
    """Handle manual reauthorization for TikTok"""
    logger.info("Starting TikTok reauthorization process...")
    auth_url = get_tiktok_authorization_url()
    if not auth_url:
        logger.error("Failed to generate TikTok authorization URL.")
        return False

    print("\nTikTok reauthorization required. Please follow these steps:")
    print(f"1. Visit this URL in your web browser: {auth_url}")
    print("2. Log in to TikTok and authorize the application.")
    print("3. After authorizing, you will be redirected to a new page.")
    print("4. Copy the entire URL of the page you are redirected to.")
    print("5. Paste that full URL here when prompted.\n")

    redirected_url = input("Enter the full redirected URL: ").strip()

    parsed_url = urlparse(redirected_url)
    query_params = parse_qs(parsed_url.query)
    code = query_params.get('code', [None])[0]

    if not code:
        logger.error("Failed to extract authorization code from the provided URL.")
        return False

    try:
        token_response = exchange_code_for_token(code)
        if 'access_token' in token_response:
            new_access_token = token_response['access_token']
            new_refresh_token = token_response.get('refresh_token')

            save_tiktok_tokens(new_access_token, new_refresh_token)
            logger.info("TikTok reauthorization successful. New tokens obtained and saved.")
            return True
        else:
            logger.error(f"Failed to obtain new TikTok tokens. Response: {token_response}")
            return False
    except Exception as e:
        logger.error(f"Error during TikTok reauthorization: {str(e)}")
        return False

@retry_on_failure(max_retries=3, backoff_factor=2)
def initiate_tiktok_video_upload(video_path):
    access_token, _ = load_tiktok_tokens()
    headers = {
        'Authorization': f'Bearer {access_token}',
        'Content-Type': 'application/json',
    }
    video_file_size = os.path.getsize(video_path)
    data = {
        "source_info": {
            "source": "FILE_UPLOAD",
            "video_size": video_file_size,
            "chunk_size": video_file_size,
            "total_chunk_count": 1
        }
    }
    try:
        response = requests.post(TIKTOK_INIT_UPLOAD_URL, headers=headers, json=data, timeout=60)
        response.raise_for_status()
        response_data = response.json()
        logger.info(f"TikTok upload initialization response: {response_data}")
        return response_data['data']['upload_url'], response_data['data']['publish_id']
    except Exception as e:
        logger.error(f"Failed to initialize TikTok video upload: {str(e)}")
        raise

@retry_on_failure(max_retries=3, backoff_factor=2)
def upload_video_to_tiktok(upload_url, video_path):
    access_token, _ = load_tiktok_tokens()
    video_file_size = os.path.getsize(video_path)
    headers = {
        'Content-Type': 'video/mp4',
        'Authorization': f'Bearer {access_token}',
        'Content-Range': f"bytes 0-{video_file_size-1}/{video_file_size}"
    }
    try:
        with open(video_path, 'rb') as video_file:
            response = requests.put(upload_url, headers=headers, data=video_file, timeout=300)
        response.raise_for_status()
        logger.info(f"TikTok video upload response: {response.text}")
        return response.status_code == 201
    except Exception as e:
        logger.error(f"Failed to upload video to TikTok: {str(e)}")
        raise

@retry_on_failure(max_retries=10, backoff_factor=1)
def check_tiktok_upload_status(publish_id):
    access_token, _ = load_tiktok_tokens()
    headers = {
        'Authorization': f'Bearer {access_token}',
        'Content-Type': 'application/json',
    }
    data = {"publish_id": publish_id}
    try:
        response = requests.post(TIKTOK_CHECK_STATUS_URL, headers=headers, json=data, timeout=30)
        response.raise_for_status()
        status_data = response.json()
        logger.info(f"TikTok upload status: {status_data}")
        return status_data['data']['status'] == "SEND_TO_USER_INBOX"
    except Exception as e:
        logger.error(f"Failed to check TikTok upload status: {str(e)}")
        raise

def post_to_tiktok(video_path):
    """Complete TikTok posting process"""
    if not validate_tiktok_token():
        logger.info("TikTok token is invalid. Attempting to refresh...")
        if not refresh_tiktok_token():
            logger.error("Failed to refresh TikTok token. Manual reauthorization may be required.")
            notify_reauthorization_required("TikTok")
            return False

    upload_url, publish_id = initiate_tiktok_video_upload(video_path)
    if not upload_url or not publish_id:
        logger.error("Failed to initiate TikTok video upload.")
        return False

    if not upload_video_to_tiktok(upload_url, video_path):
        logger.error("Failed to upload video to TikTok.")
        return False

    # Polling for upload status
    for attempt in range(10):
        if check_tiktok_upload_status(publish_id):
            logger.info("Video successfully posted to TikTok.")
            return True
        else:
            logger.info(f"Waiting 30 seconds before next status check. Attempt {attempt + 1}/10")
            time.sleep(30)

    logger.warning("TikTok upload status did not reach inbox after maximum retries.")
    return False

def generate_cave_hack_for_product(product):
    product_category = product['Product_Categories'].split('>')[-1].strip()
    product_name = product['Title']
    product_description = product['Short_Description']

    prompt = (
        f"Generate a helpful tip or trick of 30-50 words for enhancing a man cave or personal space, "
        f"related to the category '{product_category}'. Use this product for inspiration: '{product_name}'. "
        f"Product description: '{product_description}'\n"
        f"Make the tip generic without mentioning the specific product name. "
        f"Include 1-2 emojis in the content. Use the following format:\n\n"
        f"## Cave Hack: [Title of the Cave Hack]\n\n"
        f"[Content of the Cave Hack (30-50 words)]\n\n"
        f"**Keywords:** [Comma-separated list of relevant keywords]"
    )

    cave_hack_content = generate_social_media_content(prompt, max_tokens=150)

    try:
        parts = cave_hack_content.split("**Keywords:**")

        if len(parts) == 2:
            content_part = parts[0].strip()
            keywords_part = parts[1].strip()
            keywords = [kw.strip() for kw in keywords_part.split(",")]
        else:
            logger.warning("Keywords section missing in GPT-4o output. Using content for keywords.")
            content_part = cave_hack_content
            keywords = []

        title_start = content_part.find("Cave Hack:") + len("Cave Hack:")
        title_end = content_part.find("\n", title_start)
        title = content_part[title_start:title_end].strip()

        content = content_part[title_end:].strip()
        
        # Ensure the content is within the 30-50 word limit
        content_words = content.split()
        if len(content_words) > 50:
            content = ' '.join(content_words[:50])
        elif len(content_words) < 30:
            logger.warning(f"Cave Hack content is too short ({len(content_words)} words). Regenerating...")
            return generate_cave_hack_for_product(product)

        return {
            "title": title,
            "content": content,
            "keywords": keywords,
            "product_id": product['ID'],
            "product_url": product['URL'],
            "image_url": product['Image_URLs'].split('|')[0] if product['Image_URLs'] else None
        }

    except Exception as e:
        logger.error(f"Error parsing Cave Hack content: {str(e)}")
        return None

def select_best_cave_hack(cave_hacks):
    prompt = (
        "You are a social media expert for a man cave supplies company. "
        "You need to select the best Cave Hack from the following options. "
        "Evaluate based on creativity, relevance to the product, and potential for audience engagement. "
        "Provide a brief explanation for your choice.\n\n"
    )

    for i, hack in enumerate(cave_hacks, 1):
        prompt += f"Option {i}:\n"
        prompt += f"Product: {hack.get('product_name', 'Unknown')}\n"
        prompt += f"Cave Hack: {hack['title']}\n"
        prompt += f"{hack['content']}\n\n"

    prompt += "Which option is the best Cave Hack? Provide your answer in this format:\n"
    prompt += "Best Option: [Number]\n"
    prompt += "Explanation: [Your reasoning]\n"

    response = generate_social_media_content(prompt, max_tokens=150, temperature=0.7)
    logger.debug(f"GPT Response for best cave hack: {response}")

    try:
        lines = response.split('\n')
        best_option = None
        
        # Find the best option number
        for line in lines:
            if line.startswith('Best Option:'):
                try:
                    option_num = int(line.split(':')[1].strip())
                    if 1 <= option_num <= len(cave_hacks):
                        best_option = option_num
                        break
                except ValueError:
                    logger.error(f"Could not parse best option from line: {line}")
                    continue
        
        if best_option is None:
            logger.error("No valid best option found in response")
            return random.choice(cave_hacks), "Random selection due to parsing error"
            
        # Find the explanation
        explanation_line = next((line for line in lines if line.startswith('Explanation:')), None)
        explanation = explanation_line.split(':')[1].strip() if explanation_line else "No explanation provided"
        
        logger.info(f"Selected best Cave Hack: Option {best_option}")
        logger.info(f"Selection explanation: {explanation}")
        
        return cave_hacks[best_option - 1], explanation
    except Exception as e:
        logger.error(f"Error parsing best Cave Hack selection: {str(e)}")
        return random.choice(cave_hacks), "Random selection due to parsing error"

def get_main_category(product_categories):
    categories = [cat.strip() for cat in product_categories.split('>')]
    return categories[0] if categories else ""

def extract_main_concept(cave_hack_content):
    object_categories_string = ", ".join(OBJECT_CATEGORIES)
    prompt = (
        f"Extract the main concept or category from the following Cave Hack tip. "
        f"The concept should ideally be one of these: {object_categories_string}. "
        f"If none of these match exactly, provide the closest related category.\n\n"
        f"{cave_hack_content}"
    )
    concept = generate_social_media_content(prompt, max_tokens=20, temperature=0.0)
    logger.debug(f"Extracted concept: {concept}")
    return concept.strip().lower()

def generate_image_description(image_url, image_descriptions):
    if image_url in image_descriptions:
        logger.debug(f"Image description found in cache for: {image_url}")
        return image_descriptions[image_url]

    logger.debug(f"Generating image description for: {image_url}")

    try:
        image_response = requests.get(image_url, timeout=30)
        image_response.raise_for_status()

        base64_image = base64.b64encode(image_response.content).decode('utf-8')

        prompt = (
            f"Describe the objects and the scene in this image. "
            f"Be specific and detailed in your description. "
            f"Provide a concise summary of what the image depicts."
        )

        headers = {
            "Authorization": f"Bearer {OPENAI_API_KEY}",
            "Content-Type": "application/json"
        }
        data = {
            "model": "gpt-4o-2024-08-06",
            "messages": [
                {"role": "user", "content": [
                    {"type": "text", "text": prompt},
                    {"type": "image_url", "image_url": {"url": f"data:image/jpeg;base64,{base64_image}"}}
                ]}
            ],
            "max_tokens": 50,
            "temperature": 0.5,
        }
        response = requests.post("https://api.openai.com/v1/chat/completions", headers=headers, json=data, timeout=60)
        response.raise_for_status()
        response_data = response.json()

        description = response_data['choices'][0]['message']['content']
        logger.debug(f"OpenAI response: {description[:50]}...")

        image_descriptions[image_url] = description
        save_image_descriptions(image_descriptions)

        return description.strip()

    except Exception as e:
        logger.error(f"Error generating image description: {str(e)}")
        traceback.print_exc()
        return None

def generate_hashtags(cave_hack_content):
    prompt = (
        f"Suggest two relevant and engaging hashtags (making sure to output only the hashtags with no surrounding context) "
        f"for the following Cave Hack content:\n\n{cave_hack_content}"
    )
    hashtags_response = generate_social_media_content(prompt, max_tokens=30, temperature=0.8)
    hashtags = [f"{tag.strip()}" for tag in hashtags_response.split(' ') if tag.strip()]
    return hashtags

def generate_twitter_content(original_content):
    prompt = (
        f"Please revise the following cave hack tip to be appropriate for Twitter, ensuring that it is 225 characters or less. "
        f"Please maintain usage of emojis but do not include any hashtags:\n\n'{original_content}'"
    )
    
    shortened_content = generate_social_media_content(prompt, max_tokens=100, temperature=0.7)
    return shortened_content.strip()

def gpt4_generate_mood_and_instrument(text, image_description):
    prompt = (
        f"Given the following image description: '{image_description}' "
        f"and the text: '{text}', please provide:\n"
        f"1. A comma-separated list of up to 3 moods that best fit the image and text.\n"
        f"2. A comma-separated list of up to 3 instruments that would suit the mood.\n"
        f"Respond in this exact format:\n"
        f"moods: <mood1>, <mood2>, <mood3>\n"
        f"instruments: <instrument1>, <instrument2>, <instrument3>"
    )

    headers = {
        "Authorization": f"Bearer {OPENAI_API_KEY}",
        "Content-Type": "application/json"
    }
    data = {
        "model": "gpt-4o-2024-08-06",
        "messages": [{"role": "user", "content": prompt}],
        "max_tokens": 100,
        "temperature": 0.7,
    }
    try:
        response = requests.post(
            "https://api.openai.com/v1/chat/completions", headers=headers, json=data, timeout=60
        )
        response.raise_for_status()
        result = response.json()['choices'][0]['message']['content']
        logger.debug(f"GPT-4o suggested moods and instruments: {result}")
        return result.strip()
    except requests.exceptions.RequestException as e:
        logger.error(f"Request failed: {str(e)}")
        raise Exception(f"Failed to generate moods and instruments: {str(e)}")
    except Exception as e:
        logger.error(f"Error generating moods and instruments: {str(e)}")
        raise Exception(f"Failed to generate moods and instruments: {str(e)}")

def gpt4_extract_mood_instrument(response_text):
    try:
        lines = response_text.split('\n')
        moods = [mood.strip() for mood in lines[0].split(':')[1].split(',')]
        instruments = [instrument.strip() for instrument in lines[1].split(':')[1].split(',')]

        logger.info(f"Extracted moods: {moods}")
        logger.info(f"Extracted instruments: {instruments}")
        return moods, instruments
    except Exception as e:
        logger.error(f"Error extracting moods and instruments: {str(e)}")
        return ["whimsical"], ["piano"]

def search_and_download_music(cave_hack_content):
    try:
        response_text = gpt4_generate_mood_and_instrument(cave_hack_content, "")
        moods, instruments = gpt4_extract_mood_instrument(response_text)

        song_history = load_song_history()
        used_tags = []

        for mood in moods + instruments:
            if mood in used_tags:
                continue
            used_tags.append(mood)
    
            logger.info(f"Searching for music with tag: {mood}")
            music_results = search_music_by_tags(mood)
            
            if not music_results:
                logger.warning(f"No valid music results found for tag: {mood}")
                continue

            random.shuffle(music_results)
            for result in music_results:
                if is_song_recently_used(result['id'], song_history):
                    logger.info(f"Skipping recently used song: {result['name']}")
                    continue
            
                temp_music_path = download_music(result)
                if temp_music_path:
                    try:
                        logger.info(f"Download successful. Loading music file: {temp_music_path}")
                        music_sound = AudioFileClip(temp_music_path)
                        
                        if music_sound is None or music_sound.duration == 0:
                            raise ValueError("AudioFileClip failed to load the file properly")
                        
                        logger.info(f"Successfully loaded music file. Duration: {music_sound.duration}")
                        logger.info(f"Successfully processed music for {result['name']}")
                        
                        update_song_history(result['id'], song_history)
                        return music_sound
                    except Exception as e:
                        logger.error(f"Error processing music file: {str(e)}")
                        logger.error(f"Error details: {traceback.format_exc()}")
                        if os.path.exists(temp_music_path):
                            os.remove(temp_music_path)
                            logger.info(f"Removed problematic file: {temp_music_path}")
                else:
                    logger.warning(f"Failed to download music: {result['name']}")

        logger.warning("No valid music found. Using fallback audio.")
        return process_fallback_audio()

    except Exception as e:
        logger.error(f"Error in search_and_download_music: {str(e)}")
        logger.error(f"Error details: {traceback.format_exc()}")
        return process_fallback_audio()

def process_fallback_audio():
    try:
        logger.info(f"Loading fallback audio from: {FREESOUND_PLACEHOLDER}")
        fallback_sound = AudioFileClip(FREESOUND_PLACEHOLDER)
        logger.info(f"Using fallback audio")
        return fallback_sound
    except Exception as e:
        logger.error(f"Error processing fallback audio: {str(e)}")
        return None

def clean_text_for_voiceover(text):
    # Remove any non-alphanumeric characters that shouldn't be read out loud
    cleaned_text = re.sub(r'[^\w\s]', '', text)
    return cleaned_text.strip()

def create_audio_with_elevenlabs(text, output_path):
    url = "https://api.elevenlabs.io/v1/text-to-speech/kPzsL2i3teMYv0FxEYQ6"
    headers = {
        "Accept": "audio/mpeg",
        "Content-Type": "application/json",
        "xi-api-key": ELEVENLABS_API_KEY
    }
    data = {
        "text": text,
        "model_id": "eleven_monolingual_v1",
        "voice_settings": {
            "stability": 0.8,
            "similarity_boost": 0.5,
            "style": 0.5,
            "speaking_rate": 0.25
        }
    }

    max_retries = 3
    for attempt in range(max_retries):
        try:
            logger.info(f"Attempting to contact ElevenLabs (Attempt {attempt + 1}/{max_retries})...")
            response = requests.post(url, json=data, headers=headers, timeout=(120 + attempt * 30))
            response.raise_for_status()

            with open(output_path, "wb") as f:
                f.write(response.content)
            logger.info(f"Audio file created successfully: {output_path}")

            voiceover = AudioFileClip(output_path)
            voiceover_with_fade = voiceover.audio_fadeout(0.5)
            silence = AudioClip(lambda t: 0, duration=1)
            voiceover_with_silence = concatenate_audioclips([voiceover_with_fade, silence])

            final_output_path = output_path.replace(".mp3", "_final.mp3")
            voiceover_with_silence.write_audiofile(final_output_path, fps=44100, logger=None)

            logger.info(f"Audio file with added fade-out and silence created: {final_output_path}")
            return final_output_path

        except requests.exceptions.ReadTimeout as e:
            logger.warning(f"ElevenLabs API timed out on attempt {attempt + 1}. Retrying in a moment...")
            if attempt == max_retries - 1:
                logger.error("ElevenLabs API failed after maximum retries.")
                raise Exception("Failed to get response from ElevenLabs after multiple timeouts.") from e
            time.sleep(5 * (attempt + 1))

        except requests.RequestException as e:
            logger.error(f"A network error occurred while contacting ElevenLabs: {e}")
            raise Exception(f"API call to ElevenLabs failed with a network error: {e}") from e

        except Exception as e:
           logger.error(f"An unexpected error occurred in create_audio_with_elevenlabs: {str(e)}")
           raise

def match_music_to_duration(music_sound, target_duration):
    try:
        music_duration = music_sound.duration
        if music_duration > target_duration:
            logger.info(f"Truncating music to match target duration: {target_duration} seconds")
            return music_sound.subclip(0, target_duration)
        elif music_duration < target_duration:
            logger.info(f"Repeating music to match target duration: {target_duration} seconds")
            repeat_count = int(target_duration // music_duration) + 1
            extended_music = concatenate_audioclips([music_sound] * repeat_count)
            return extended_music.subclip(0, target_duration)
        return music_sound
    except Exception as e:
        logger.error(f"Error matching music duration: {e}")
        return None

def ensure_rgb(image_path):
    with Image.open(image_path) as img:
        if img.mode != 'RGB':
            rgb_img = img.convert('RGB')
            rgb_image_path = os.path.splitext(image_path)[0] + '_rgb.png'
            rgb_img.save(rgb_image_path)
            logger.info(f"Converted image to RGB: {rgb_image_path}")
            return rgb_image_path
        else:
            logger.debug("Image is already in RGB mode.")
            return image_path

def download_image(image_url):
    try:
        with tempfile.NamedTemporaryFile(delete=False, suffix='.png') as temp_file:
            temp_image_path = temp_file.name
            response = requests.get(image_url, timeout=60)
            response.raise_for_status()
            with open(temp_image_path, "wb") as file:
                file.write(response.content)
        logger.info(f"Downloaded image to temporary file: {temp_image_path}")
        return temp_image_path
    except Exception as e:
        logger.error(f"Error downloading image: {str(e)}")
        raise

def create_end_screen(logo_path, background_color, duration, video_size):
    bg_color = tuple(int(background_color.lstrip('#')[i:i+2], 16) for i in (0, 2, 4))
    bg_color_rgba = bg_color + (255,)

    background = ColorClip(size=video_size, color=bg_color).set_duration(duration)

    with Image.open(logo_path) as img:
        if img.mode != 'RGBA':
            img = img.convert('RGBA')

        img.thumbnail((video_size[0] // 2, video_size[1] // 2), Image.LANCZOS)

        new_img = Image.new('RGBA', video_size, bg_color_rgba)
        paste_position = ((video_size[0] - img.width) // 2, (video_size[1] - img.height) // 2)
        new_img.paste(img, paste_position, img)

        new_img = new_img.convert('RGB')

        temp_logo_path = tempfile.mktemp(suffix='.png')
        new_img.save(temp_logo_path, 'PNG')

    logo = ImageClip(temp_logo_path).set_duration(duration)

    end_screen = CompositeVideoClip([background, logo]).set_duration(duration)

    os.remove(temp_logo_path)
    logger.debug(f"Created end screen with logo: {temp_logo_path}")

    return end_screen

def create_typing_effect(text, duration, video_size, font_path, buffer_duration=2):
    frames = []
    raw_sentences = re.split(r'(?<=[.!?])\s+', text)
    raw_sentences = [s.strip() for s in raw_sentences if s.strip()]

    sentences = []
    current_sentence = ""
    for sentence in raw_sentences:
        if len(current_sentence.split()) < 4:
            current_sentence += " " + sentence
        else:
            if current_sentence:
                sentences.append(current_sentence.strip())
            current_sentence = sentence
    if current_sentence:
        sentences.append(current_sentence.strip())

    total_words = sum(len(sentence.split()) for sentence in sentences)
    base_word_duration = (duration - buffer_duration) / (total_words * 1.1)

    current_time = 0

    for i, sentence in enumerate(sentences):
        words = sentence.split()
        sentence_frames = []

        for j, word in enumerate(words):
            current_words = words[:j+1]
            frame = create_subtitle_frame(current_words, video_size, font_path)
            sentence_frames.append(frame)

            if word.endswith(','):
                word_duration = base_word_duration * 1.2
            elif word.endswith('.') or word.endswith('?') or word.endswith('!'):
                word_duration = base_word_duration * 1.5
            else:
                word_duration = base_word_duration

            word_frames = int(word_duration * 24)
            frames.extend([frame] * word_frames)

            current_time += word_duration

    # Extend the last frame for the buffer duration
    if frames:
        last_frame = frames[-1]
        buffer_frames = int(buffer_duration * 24)
        frames.extend([last_frame] * buffer_frames)

    typing_clip = ImageSequenceClip(frames, fps=24).set_duration(duration + buffer_duration)
    logger.debug("Created typing effect clip.")
    return typing_clip

def create_subtitle_frame(sentence_words, video_size, font_path):
    img = Image.new('RGBA', video_size, (0, 0, 0, 0))
    draw = ImageDraw.Draw(img)

    font_sizes = [100, 70, 56, 34, 80, 56]
    words_per_row = [1, 2, 2, 3, 2, 2]
    y_position = video_size[1] // 4
    left_margin = video_size[0] // 10
    padding = 5

    word_index = 0
    for row, (initial_font_size, word_count) in enumerate(zip(font_sizes, words_per_row)):
        if word_index >= len(sentence_words) or row >= 6:
            break

        row_words = sentence_words[word_index:word_index + word_count]
        text = ' '.join(row_words).upper()

        font_size = initial_font_size
        max_width = video_size[0] - (2 * left_margin)

        while font_size > 10:
            try:
                font = ImageFont.truetype(font_path, font_size)
            except IOError:
                logger.error(f"Font file not found: {font_path}")
                raise
            text_bbox = draw.textbbox((0, 0), text, font=font)
            text_width = text_bbox[2] - text_bbox[0]
            if text_width <= max_width:
                break
            font_size -= 2

        font = ImageFont.truetype(font_path, font_size)
        text_bbox = draw.textbbox((left_margin, y_position), text, font=font)
        text_width = text_bbox[2] - text_bbox[0]
        text_height = text_bbox[3] - text_bbox[1]

        bg_top = text_bbox[1] - padding
        bg_bottom = text_bbox[3] + padding

        background_shape = [
            left_margin - padding,
            bg_top,
            left_margin + text_width + padding,
            bg_bottom
        ]
        draw.rectangle(background_shape, fill=(0, 0, 0, 120))

        draw.text((left_margin, y_position), text, font=font, fill=(255, 255, 255, 255))

        y_position += text_height + padding + 15

        word_index += word_count

    return np.array(img)

def create_zoom_effect(clip, duration, zoom_factor=1.5):
    def zoom(t):
        progress = t / duration
        scale = 1 + (zoom_factor - 1) * progress
        return min(scale, zoom_factor)

    zoomed_clip = clip.resize(lambda t: zoom(t)).set_position("center").set_duration(duration)
    logger.debug("Created zoom effect clip centered.")
    return zoomed_clip

def clean_caption(caption):
    # Remove emojis (emoji ranges cover most common emoji Unicode blocks)
    emoji_pattern = re.compile(
        "["
        u"\U0001F600-\U0001F64F"  # emoticons
        u"\U0001F300-\U0001F5FF"  # symbols & pictographs
        u"\U0001F680-\U0001F6FF"  # transport & map symbols
        u"\U0001F700-\U0001F77F"  # alchemical symbols
        u"\U0001F780-\U0001F7FF"  # geometric shapes
        u"\U0001F800-\U0001F8FF"  # supplemental arrows
        u"\U0001F900-\U0001F9FF"  # supplemental symbols and pictographs
        u"\U0001FA00-\U0001FA6F"  # chess symbols and medical symbols
        u"\U00002702-\U000027B0"  # dingbats
        u"\U0001F1E0-\U0001F1FF"  # flags (iOS)
        "]+", flags=re.UNICODE
    )

    # Remove double quotes and asterisks
    cleaned_caption = re.sub(r'[\"*]', '', caption)

    # Remove emojis
    cleaned_caption = emoji_pattern.sub(r'', cleaned_caption)

    # Remove extra spaces before punctuation
    cleaned_caption = re.sub(r'\s+([?.!,])', r'\1', cleaned_caption)

    # Remove the second punctuation if two punctuation marks appear consecutively
    cleaned_caption = re.sub(r'([?.!,])(?=[?.!,])', '', cleaned_caption)

    return cleaned_caption.strip()

def upload_file_via_sftp(local_path, remote_path, host, username, password):
    try:
        transport = paramiko.Transport((host, 22))
        transport.connect(username=username, password=password)

        sftp = paramiko.SFTPClient.from_transport(transport)
        sftp.put(local_path, remote_path)
        sftp.close()
        transport.close()
        logger.debug(f"Uploaded file to {remote_path} on {host}")
    except Exception as e:
        logger.error(f"Failed to upload file via SFTP: {str(e)}")
        raise

def delete_remote_file(remote_path, host, username, password):
    """Delete file from remote server via SFTP"""
    try:
        transport = paramiko.Transport((host, 22))
        transport.connect(username=username, password=password)
        sftp = paramiko.SFTPClient.from_transport(transport)
        sftp.remove(remote_path)
        sftp.close()
        transport.close()
        logger.info(f"Successfully deleted remote file: {remote_path}")
    except Exception as e:
        logger.warning(f"Failed to delete remote file {remote_path}: {e}")

def create_cave_hack_video(cave_hack_content, image_url, logo_end_screen_path):
    temp_files = []
    clips_to_close = []
    try:
        logger.info(f"Starting video creation for Cave Hack")
        
        # Download and process the image
        image_path = download_image(image_url)
        temp_files.append(image_path)
        rgb_image_path = ensure_rgb(image_path)
        if rgb_image_path != image_path:
            temp_files.append(rgb_image_path)
        
        # Clean the caption
        cleaned_caption = clean_caption(cave_hack_content)
        
        # Clean the caption for the voiceover
        cleaned_caption_for_voiceover = clean_text_for_voiceover(cleaned_caption)
        
        # Generate audio with ElevenLabs using the cleaned text for the voiceover
        with tempfile.NamedTemporaryFile(delete=False, suffix='.mp3') as temp_audio:
            temp_audio_path = temp_audio.name
        temp_files.append(temp_audio_path)
        
        final_audio_path = create_audio_with_elevenlabs(cleaned_caption_for_voiceover, temp_audio_path)
        temp_files.append(final_audio_path)
        
        voiceover = AudioFileClip(final_audio_path)
        clips_to_close.append(voiceover)
        voiceover_duration = voiceover.duration
        logger.info(f"Voiceover duration: {voiceover_duration} seconds")

        # Add 2 seconds for buffer and 3 seconds for the end screen
        total_duration = voiceover_duration + 2 + 3

        # Search for and download music from Freesound
        music_sound = search_and_download_music(cave_hack_content)
        if music_sound:
            clips_to_close.append(music_sound)

        if music_sound is None:
            logger.warning("No valid music found. Using fallback audio.")
            music_sound = AudioFileClip(FREESOUND_PLACEHOLDER)
            clips_to_close.append(music_sound)

        music_sound = match_music_to_duration(music_sound, total_duration)

        # Create the final audio by combining voiceover and background music
        final_audio = CompositeAudioClip([
            voiceover.set_start(0),
            music_sound.volumex(0.1).set_duration(total_duration)
        ])

        # Load and process the image
        logger.info(f"Loading image from {rgb_image_path}")
        clip = ImageClip(rgb_image_path)
        clips_to_close.append(clip)

        # Apply zoom effect to the main part (including 2-second buffer)
        zoomed_clip = create_zoom_effect(clip, voiceover_duration + 2)

        font_path = os.path.join(project_root, "assets", "fonts", "Jost-Bold.ttf")
        if not os.path.exists(font_path):
            logger.error(f"Font file not found: {font_path}")
            raise FileNotFoundError(f"Font file not found: {font_path}")

        video_size = clip.size

        # Create typing effect frames (including 2-second buffer)
        typing_clip = create_typing_effect(cleaned_caption, voiceover_duration, video_size, font_path, buffer_duration=2)

        # Combine zoomed clip and typing effect for the main part
        main_video = CompositeVideoClip([zoomed_clip, typing_clip.set_position(('center', 'center'))], size=video_size)
        main_video = main_video.set_duration(voiceover_duration + 2)

        # Create end screen
        end_screen = create_end_screen(logo_end_screen_path, "#012445", 3, video_size)
        
        # Concatenate main video and end screen
        final_clip = concatenate_videoclips([main_video, end_screen])
        
        # Set the audio for the entire video
        final_clip = final_clip.set_audio(final_audio)
        
        # Create a temporary file for the output video
        with tempfile.NamedTemporaryFile(delete=False, suffix='.mp4') as temp_video:
            output_path = temp_video.name
        
        gc.collect()
        
        final_clip.write_videofile(
            output_path, 
            fps=24, 
            codec='libx264', 
            audio_codec='aac', 
            threads=2,
            logger=None
        )
        
        logger.info(f"Video creation completed successfully: {output_path}")
        return output_path, temp_files
        
    except Exception as e:
        logger.error(f"An error occurred during video creation: {str(e)}")
        raise
    finally:
        # Clean up clips
        for clip in clips_to_close:
            try:
                if hasattr(clip, 'close'):
                    clip.close()
            except Exception as e:
                logger.warning(f"Error closing clip: {e}")
        gc.collect()

def post_to_all_platforms_with_cleanup(video_path, formatted_caption, caption, short_video_url, remote_video_path, sftp_host, sftp_username, sftp_password, page_id, FB_ACCESS_TOKEN):
    """Post to all platforms and cleanup files"""
    
    # Post to Facebook
    facebook_success = post_video_to_facebook(formatted_caption, short_video_url, page_id, FB_ACCESS_TOKEN)
    print("Posted to Facebook!" if facebook_success else "Failed to post to Facebook.")

    # Post to Instagram  
    instagram_success = post_video_to_instagram(formatted_caption, short_video_url)
    print("Posted to Instagram!" if instagram_success else "Failed to post to Instagram.")

    # Twitter posting (uses local file)
    twitter_caption = trim_to_full_sentence(caption, 280 - len("# Cave Hack # "))
    twitter_caption = f"# Cave Hack # {twitter_caption}"
    twitter_success = twitter_post_with_media(twitter_caption, video_path)
    print("Posted to Twitter!" if twitter_success else "Failed to post to Twitter.")

    # TikTok posting (uses local file)
    logger.info("Posting to TikTok")
    tiktok_success = post_to_tiktok(video_path)
    print("Posted to TikTok!" if tiktok_success else "Failed to post to TikTok.")

    # Wait a bit for platforms to download the video
    logger.info("Waiting 60 seconds for platforms to process video...")
    time.sleep(60)

    # Cleanup remote file
    try:
        delete_remote_file(remote_video_path, sftp_host, sftp_username, sftp_password)
    except Exception as e:
        logger.warning(f"Could not delete remote video file: {e}")

    return facebook_success, instagram_success, twitter_success, tiktok_success

def trim_to_full_sentence(text, max_length):
    sentences = re.split(r'(?<=[.!?]) +', text.strip())
    final_caption = ""

    for sentence in sentences:
        if len(final_caption) + len(sentence) + 1 <= max_length:
            final_caption += sentence + " "
        else:
            break

    final_caption = final_caption.strip()

    # Ensure that the caption does not end with an incomplete sentence
    if len(final_caption) > 0 and final_caption[-1] not in '.!?':
        final_caption = final_caption.rsplit(' ', 1)[0].rstrip()

    return final_caption.strip()

def send_email(facebook_status, instagram_status, twitter_status, tiktok_status):
    """Send status email using the relay"""
    timestamp_str = datetime.now().strftime("%y%m%d:%H%M%S")

    # Count successful posts
    successful_posts = sum([facebook_status, instagram_status, twitter_status, tiktok_status])
    total_posts = 4

    # Create subject line (without prefixes - relay will add them)
    if successful_posts == total_posts:
        subject = f"Cave Hacks Video Posted - All Successful - {timestamp_str}"
    else:
        subject = f"Cave Hacks Video Posted - {total_posts - successful_posts} Failure(s) - {timestamp_str}"

    # Create email body with exact old formatting
    body = f"""Cave Hacks Social Media Automation Report
Source Server: Hetzner (5.161.70.26)
Project: /opt/social-automation

Cave Hacks Video Posting Summary:

Facebook: {"Success" if facebook_status else "Failed"}
Instagram: {"Success" if instagram_status else "Failed"}
Twitter: {"Success" if twitter_status else "Failed"}
TikTok: {"Success" if tiktok_status else "Failed"}

Please check the platforms for any failed postings.


Log file: {log_file_path}"""
    
    # Send email with is_error=False to avoid error prefixes
    return send_email_notification(subject, body, is_error=False)

def log_memory_usage(tag=""):
    process = psutil.Process(os.getpid())
    memory = process.memory_info().rss / 1024 / 1024  # Convert to MB
    logger.info(f"Memory usage {tag}: {memory:.2f} MB")

if __name__ == "__main__":
    start_time = time.time()
    page_id = FB_PAGE_ID
    timestamp_str = datetime.now().strftime("%y%m%d:%H%M%S")
    temp_files = []

    print(f"Script is running from: {project_root}")
    print(f"Log file will be saved to: {log_file_path}")
    print(f"Starting Cave Hack video generation...")

    log_memory_usage("at start")

    try:
        db_config = DatabaseConfig()
        logger.info("Connecting to DigitalOcean production database...")

        # Select 3 random products
        selected_products = []
        for _ in range(3):
            product = get_random_product(db_config)
            if product:
                selected_products.append(product)
            else:
                logger.warning("Failed to get a random product from the database")

        if len(selected_products) == 0:
            logger.error("Failed to get any random products from the database")
            sys.exit(1)

        log_memory_usage("after getting products")

        # Generate Cave Hacks for each product
        cave_hacks = []
        for product in selected_products:
            cave_hack = generate_cave_hack_for_product(product)
            if cave_hack:
                cave_hack['product_name'] = product['Title']
                cave_hacks.append(cave_hack)

        log_memory_usage("after generating hacks")

        # Select the best Cave Hack
        if cave_hacks:
            best_cave_hack, explanation = select_best_cave_hack(cave_hacks)
            logger.info(f"Selected Cave Hack: {best_cave_hack['title']}")
            logger.info(f"Selection explanation: {explanation}")

            log_memory_usage("after selecting best hack")

            # Generate additional hashtags
            additional_hashtags = generate_hashtags(best_cave_hack['content'])

            # Prepare the final post content
            final_post_content = (
                f"## Daily Cave Hack ##\n\n"
                f"{best_cave_hack['content']}\n\n"
                f"#Mancave {' '.join(additional_hashtags)}"
            )

        log_memory_usage("before video creation")

        # Create video
        logger.info("Starting video creation")
        video_path, video_temp_files = create_cave_hack_video(
            best_cave_hack['content'], 
            best_cave_hack['image_url'], 
            logo_end_screen_path
        )
        temp_files.extend(video_temp_files)
        logger.info("Video creation completed")

        # Prepare SFTP details
        sftp_host = SFTP_HOST
        sftp_username = SFTP_USERNAME
        sftp_password = SFTP_PASSWORD
        remote_video_filename = f"social_cave_hacks_{uuid.uuid4().hex}.mp4"
        remote_video_path = f"/home/runcloud/webapps/cavesupplies-production/videos/{remote_video_filename}"

        # Ensure the video file exists before attempting to upload
        if os.path.exists(video_path):
            logger.info("Uploading video to DigitalOcean production server")
            if sftp_host and sftp_username and sftp_password:
                upload_file_via_sftp(video_path, remote_video_path, sftp_host, sftp_username, sftp_password)
                logger.info("Video upload completed")
                
                # Get hosted video URL
                hosted_video_url = f"https://cavesupplies.com/videos/{remote_video_filename}"
                
                # Shorten the hosted URL using Bitly
                short_video_url = shorten_url(hosted_video_url)
            else:
                logger.error("SFTP credentials are not properly set in the environment variables.")
                hosted_video_url = None
                short_video_url = None
        else:
            logger.error(f"Video file not found at {video_path}. Cannot upload.")
            hosted_video_url = None
            short_video_url = None

        # Initialize posting statuses
        facebook_success = False
        instagram_success = False
        twitter_success = False
        tiktok_success = False

        # Post to all platforms and cleanup remote video
        if short_video_url:
            facebook_success, instagram_success, twitter_success, tiktok_success = post_to_all_platforms_with_cleanup(
                video_path, 
                final_post_content, 
                best_cave_hack['content'], 
                short_video_url, 
                remote_video_path, 
                sftp_host, 
                sftp_username, 
                sftp_password, 
                page_id, 
                FB_ACCESS_TOKEN
            )
        else:
            logger.error("Cannot post to platforms: No hosted video URL available.")

        # Add product to blacklist
        if not add_to_blacklist(best_cave_hack['product_id'], db_config):
            logger.error(f"Failed to add product {best_cave_hack['product_id']} to blacklist")

        # Send email notifications
        send_email(facebook_success, instagram_success, twitter_success, tiktok_success)

    except ValueError as ve:
        logger.error(f"Validation error: {ve}")
    except Exception as e:
        logger.error(f"An error occurred: {str(e)}")
        logger.error(traceback.format_exc())
        subject = f"Cave Hacks Video Script Failed - {timestamp_str}"
        error_message = f"An error occurred: {str(e)}\n\nTraceback:\n{traceback.format_exc()}"
        send_email_notification(f"Cave Hacks Video Script Failed - {timestamp_str}", error_message, is_error=True)

    finally:
        # Clean up temporary files
        for temp_file in temp_files:
            try:
                if isinstance(temp_file, str) and os.path.exists(temp_file):
                    os.remove(temp_file)
                    logger.debug(f"Removed temporary file: {temp_file}")
                elif hasattr(temp_file, 'close'):
                    temp_file.close()
                    logger.debug(f"Closed temporary file object: {temp_file}")
            except Exception as e:
                logger.warning(f"Failed to remove/close temporary file {temp_file}: {str(e)}")

        # Remove the main video file
        if 'video_path' in locals() and os.path.exists(video_path):
            try:
                os.remove(video_path)
                logger.debug(f"Removed main video file: {video_path}")
            except Exception as e:
                logger.warning(f"Failed to remove main video file {video_path}: {str(e)}")

    total_time = time.time() - start_time
    logger.info(f"Total execution time: {total_time:.2f} seconds")
    print(f"Total execution time: {total_time:.2f} seconds")
    print(f"Script execution completed. Please check {log_file_path} for detailed logs.")