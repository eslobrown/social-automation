#!/usr/bin/env python3
"""
Product Review Social Media Video Creator - Hetzner to DigitalOcean Production

Architecture:
- Runs on: Hetzner server (staging environment, IP: 5.161.70.26)  
- Posts to: Facebook, Instagram, Twitter, TikTok
- Database: DigitalOcean production MySQL (174.138.92.252)
- Video Hosting: DigitalOcean production server

This script creates and posts daily product review videos featuring Thorak's caveman 
perspective to social media platforms. It selects random in-stock products from the 
WooCommerce database, generates engaging content, creates videos with voiceovers and 
background music, and posts to all major social platforms.

Usage:
  python scripts/social_product_posting_video.py
"""

import sys
import os
import logging
import json
import pandas as pd
import time
import random
import requests
import traceback
from pathlib import Path
from openai import OpenAI
import csv
from functools import wraps
from datetime import datetime, timedelta
import pytz
from dotenv import load_dotenv
from requests_oauthlib import OAuth1, OAuth2Session
import uuid
from PIL import Image, ImageDraw, ImageFont
import tempfile
from moviepy.editor import *
import re
import numpy as np
import paramiko
import base64
import http.client as http_client
from moviepy.editor import ImageSequenceClip
from logging.handlers import RotatingFileHandler
from oauthlib.oauth2 import TokenExpiredError
from urllib.parse import quote, urlencode, urlparse, parse_qs
import mysql.connector

# Set up project paths
project_root = "/opt/social-automation"
os.chdir(project_root)

# Load environment variables
dotenv_path = os.path.join(project_root, "credentials.env")
load_dotenv(dotenv_path)

# Import email relay after project_root is defined
sys.path.insert(0, project_root)
from email_relay import send_email_notification

# Set up logging
log_file_path = os.path.join(project_root, "logs", "social_product_posting_video.log")

# Clear log file before starting
if os.path.exists(log_file_path):
    os.remove(log_file_path)

# Custom filter to remove non-printable characters
class NonPrintableFilter(logging.Filter):
    def filter(self, record):
        if isinstance(record.msg, str):
            record.msg = ''.join(char for char in record.msg if ord(char) > 31 or ord(char) == 9)
        return True

# Create a custom filter
class CustomFilter(logging.Filter):
    def filter(self, record):
        # Exclude PIL debug messages
        if record.name.startswith('PIL'):
            return False
        # Exclude messages containing specific content
        unwanted_content = ['preview-hq-mp3', 'preview-lq-ogg', 'ac_analysis']
        return not any(content in record.getMessage() for content in unwanted_content)

# Create a logger for this script
logger = logging.getLogger(__name__)
logger.setLevel(logging.INFO)

# Create handlers
file_handler = RotatingFileHandler(log_file_path, maxBytes=10*1024*1024, backupCount=5)
console_handler = logging.StreamHandler()

# Create formatter
formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s', datefmt='%Y-%m-%d %H:%M:%S')

# Set formatter for handlers
file_handler.setFormatter(formatter)
console_handler.setFormatter(formatter)

# Add custom filter to handlers
custom_filter = CustomFilter()
file_handler.addFilter(custom_filter)
console_handler.addFilter(custom_filter)

# Add handlers to logger
logger.addHandler(file_handler)
logger.addHandler(console_handler)

# Disable other loggers
logging.getLogger("requests").setLevel(logging.WARNING)
logging.getLogger("urllib3").setLevel(logging.WARNING)
logging.getLogger("paramiko").setLevel(logging.WARNING)
logging.getLogger("PIL").setLevel(logging.WARNING)

# Disable HTTP debugging
http_client.HTTPConnection.debuglevel = 0

# Force the script to use UTF-8 encoding
sys.stdout.reconfigure(encoding='utf-8')

logging.info(f"Product Review Video Creator started - Hetzner to Social Media Platforms")
logging.info(f"Project root: {project_root}")
logging.info(f"Log file: {log_file_path}")

# Database configuration (DigitalOcean Production)
DB_HOST = os.getenv("DB_HOST")
DB_USER = os.getenv("DB_USER")
DB_PASSWORD = os.getenv("DB_PASSWORD")
DB_NAME = os.getenv("DB_NAME")

class DatabaseConfig:
    def __init__(self):
        logger.info("Initializing DatabaseConfig for DigitalOcean production")
        self.host = DB_HOST
        self.user = DB_USER
        self.password = DB_PASSWORD
        self.name = DB_NAME
        logger.info("DatabaseConfig initialization complete")

# Create database configuration
db_config = DatabaseConfig()

if not all([DB_HOST, DB_USER, DB_PASSWORD, DB_NAME]):
    logger.error("Database credentials are missing. Please check your credentials.env file.")
    sys.exit(1)

# API keys from environment variables
OPENAI_API_KEY = os.getenv("OPENAI_API_KEY")
FB_ACCESS_TOKEN = quote(os.getenv("FB_ACCESS_TOKEN"))
BITLY_API_KEY = os.getenv("BITLY_API_KEY")
INSTAGRAM_BUSINESS_ACCOUNT_ID = os.getenv("INSTAGRAM_BUSINESS_ACCOUNT_ID")
TWITTER_API_KEY = os.getenv("TWITTER_API_KEY")
TWITTER_API_SECRET = os.getenv("TWITTER_API_SECRET")
TWITTER_ACCESS_TOKEN = os.getenv("TWITTER_ACCESS_TOKEN")
TWITTER_ACCESS_TOKEN_SECRET = os.getenv("TWITTER_ACCESS_TOKEN_SECRET")
ELEVENLABS_API_KEY = os.getenv("ELEVENLABS_API_KEY")
FREESOUND_API_KEY = os.getenv("FREESOUND_API_KEY")
FREESOUND_CLIENT_ID = os.getenv("FREESOUND_CLIENT_ID")
FREESOUND_CLIENT_SECRET = os.getenv("FREESOUND_CLIENT_SECRET")
FREESOUND_REDIRECT_URI = os.getenv("FREESOUND_REDIRECT_URI")
FB_PAGE_ID = os.getenv("FB_PAGE_ID")
SFTP_HOST = os.getenv("SFTP_HOST")
SFTP_USERNAME = os.getenv("SFTP_USERNAME")
SFTP_PASSWORD = os.getenv("SFTP_PASSWORD")
GOOGLE_SHEET_CSV_URL = os.getenv("GOOGLE_SHEET_CSV_URL")
TIKTOK_CLIENT_KEY = os.getenv("TIKTOK_CLIENT_KEY")
TIKTOK_CLIENT_SECRET = os.getenv("TIKTOK_CLIENT_SECRET")
TIKTOK_REDIRECT_URI = os.getenv("TIKTOK_REDIRECT_URI")

# Initialize OpenAI client
client = OpenAI(api_key=OPENAI_API_KEY)

# File paths updated for new structure
TWEET_LABEL = "# Daily Review # "
TOKEN_FILE = os.path.join(project_root, "data", "freesound_token.json")
SONG_HISTORY_FILE = os.path.join(project_root, "data", "song_history.csv")
SONG_REUSE_DAYS = 14
SOUND_DOWNLOAD_FOLDER = os.path.join(project_root, "assets", "sounds")
FREESOUND_PLACEHOLDER = os.path.join(project_root, "assets", "sounds", "freesound_placeholder.mp3")
TIKTOK_TOKEN_FILE = os.path.join(project_root, "data", "tiktok_tokens.json")

# TikTok API endpoints
TIKTOK_INIT_UPLOAD_URL = "https://open.tiktokapis.com/v2/post/publish/inbox/video/init/"
TIKTOK_CHECK_STATUS_URL = "https://open.tiktokapis.com/v2/post/publish/status/fetch/"

# Ensure required directories exist
os.makedirs(os.path.join(project_root, "logs"), exist_ok=True)
os.makedirs(os.path.join(project_root, "data"), exist_ok=True)
os.makedirs(SOUND_DOWNLOAD_FOLDER, exist_ok=True)

logger.info(f"DB_HOST: {DB_HOST}")
logger.info(f"DB_USER: {DB_USER}")
logger.info(f"DB_NAME: {DB_NAME}")

def get_random_product():
    """Get a random in-stock product that hasn't been posted recently"""
    try:
        with mysql.connector.connect(
            host=db_config.host,
            user=db_config.user,
            password=db_config.password,
            database=db_config.name
        ) as mydb:
            with mydb.cursor(dictionary=True) as cursor:
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
                        WHERE Timestamp > DATE_SUB(NOW(), INTERVAL 14 DAY)
                    )
                    ORDER BY RAND()
                    LIMIT 1
                )
                SELECT
                    p.ID,
                    p.post_title as Title,
                    p.post_content as Content,
                    p.post_excerpt as Short_Description,
                    p.guid as Base_URL,
                    MAX(CASE WHEN sku.meta_key = '_sku' THEN sku.meta_value END) as SKU,
                    MAX(CASE WHEN stock.meta_key = '_stock_status' THEN stock.meta_value END) as Stock_Status,
                    p.post_status as Status,
                    GROUP_CONCAT(DISTINCT terms.name SEPARATOR ', ') as Product_Categories,
                    (SELECT guid FROM wp_posts WHERE ID = MAX(CASE WHEN thumb.meta_key = '_thumbnail_id' THEN thumb.meta_value END)) as thumbnail,
                    GROUP_CONCAT(DISTINCT CASE WHEN gallery.meta_key = '_product_image_gallery' THEN gallery.meta_value END) as gallery_ids
                FROM random_product rp
                JOIN wp_posts p ON rp.ID = p.ID
                LEFT JOIN wp_postmeta stock ON p.ID = stock.post_id
                    AND stock.meta_key = '_stock_status'
                LEFT JOIN wp_postmeta sku ON p.ID = sku.post_id
                    AND sku.meta_key = '_sku'
                LEFT JOIN wp_postmeta thumb ON p.ID = thumb.post_id
                    AND thumb.meta_key = '_thumbnail_id'
                LEFT JOIN wp_postmeta gallery ON p.ID = gallery.post_id
                    AND gallery.meta_key = '_product_image_gallery'
                LEFT JOIN wp_term_relationships tr ON p.ID = tr.object_id
                LEFT JOIN wp_term_taxonomy tt ON tr.term_taxonomy_id = tt.term_taxonomy_id
                    AND tt.taxonomy = 'product_cat'
                LEFT JOIN wp_terms terms ON tt.term_id = terms.term_id
                GROUP BY p.ID, p.post_title, p.post_content, p.post_excerpt, p.guid, p.post_status
                ORDER BY RAND()
                LIMIT 1;
                """
                cursor.execute(query)
                return cursor.fetchone()
    except mysql.connector.Error as err:
        logger.error(f"Database Error getting random product: {err}")
        return None

def add_to_blacklist(product_id):
    """Add a product to the posted products blacklist"""
    try:
        with mysql.connector.connect(
            host=db_config.host,
            user=db_config.user,
            password=db_config.password,
            database=db_config.name
        ) as mydb:
            with mydb.cursor() as cursor:
                cursor.execute("INSERT INTO posted_products_blacklist (ID) VALUES (%s)",
                             (product_id,))
                mydb.commit()
                logger.info(f"Added product {product_id} to blacklist")
                return True
    except mysql.connector.Error as err:
        logger.error(f"Failed to add product to blacklist: {err}")
        return False

# Function to call OpenAI API to generate social media posts
def generate_social_media_post(prompt):
    max_retries = 3
    for attempt in range(max_retries):
        try:
            logger.debug(f"Calling OpenAI with prompt: {prompt[:50]}...")
            response = client.chat.completions.create(
                model="gpt-4o-2024-08-06",
                messages=[{"role": "user", "content": prompt}],
                max_tokens=150,
                temperature=0.7,
            )
            result = response.choices[0].message.content
            logger.debug(f"OpenAI response: {result[:50]}...")
            return result
        except Exception as e:
            logger.error(f"Error calling OpenAI (attempt {attempt + 1}): {str(e)}")
            if attempt == max_retries - 1:
                logger.error("Failed to get response from OpenAI after maximum retries.")
                raise
            time.sleep(2**attempt)  # Exponential backoff

# Function to shorten URLs using Bitly
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

        # Check if the response contains 'link' field
        if 'link' in response_data:
            logger.info(f"Bitly successfully shortened URL: {response_data['link']}")
            return response_data["link"]
        else:
            logger.error(f"Bitly failed to shorten URL {long_url}: {response_data}")
            return long_url  # Return the original URL if Bitly fails
    except Exception as e:
        logger.error(f"Exception occurred while shortening URL {long_url}: {str(e)}")
        return long_url  # Return the original URL if an exception occurs

def retry_on_failure(max_retries=3, backoff_factor=2):
    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            for attempt in range(max_retries):
                try:
                    return func(*args, **kwargs)
                except Exception as e:
                    logger.warning(f"Attempt {attempt + 1}/{max_retries} failed: {str(e)}")
                    if attempt == max_retries - 1:
                        raise
                    time.sleep(backoff_factor ** attempt)
        return wrapper
    return decorator

# Function to post to Facebook
def post_to_facebook(message, video_url, page_id, access_token):
    session = requests.Session()
    url = f"https://graph.facebook.com/v18.0/{page_id}/videos"
    payload = {
        "description": message,
        "access_token": access_token,
        "file_url": video_url,
    }
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                      "AppleWebKit/537.36 (KHTML, like Gecko) "
                      "Chrome/91.0.4472.124 Safari/537.36"
    }
    logger.debug(f"Facebook API URL: {url}")
    logger.debug(
        f"Payload (excluding access_token): {json.dumps({k:v for k,v in payload.items() if k != 'access_token'})}"
    )
    logger.debug(f"Token being used: {access_token[:10]}...{access_token[-10:]}")

    try:
        response = session.post(url, data=payload, headers=headers, timeout=120)
        response.raise_for_status()

        logger.debug(f"Facebook API Response Status: {response.status_code}")
        logger.debug(f"Facebook API Response Content: {response.text}")

        if response.status_code == 200:
            logger.info(f"Successfully posted video on Facebook.")
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

# Function to post to Instagram
def post_to_instagram(message, video_url, max_retries=20, retry_delay=10):
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

        # Step 2: Check media status
        status_url = f"https://graph.facebook.com/v18.0/{creation_id}?fields=status_code,status"
        for attempt in range(max_retries):
            status_response = requests.get(status_url, params={"access_token": FB_ACCESS_TOKEN}, timeout=60)
            status_response.raise_for_status()
            status_data = status_response.json()

            if status_data.get('status_code') == 'FINISHED':
                logger.info("Media processing completed. Attempting to publish.")
                break
            elif status_data.get('status_code') in ['IN_PROGRESS', 'PROCESSING', 'PROCESSING_UPLOAD']:
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

        logger.info(f"Successfully posted Reel to Instagram.")
        return True

    except requests.exceptions.RequestException as e:
        logger.error(f"Failed to post Reel to Instagram. Error: {str(e)}")
        if hasattr(e, 'response'):
            logger.error(f"Response content: {e.response.text}")
        return False

# Function to upload media to Twitter
@retry_on_failure(max_retries=3, backoff_factor=2)
def upload_media_to_twitter(video_path, auth):
    try:
        media_upload_url = "https://upload.twitter.com/1.1/media/upload.json"
        total_bytes = os.path.getsize(video_path)

        # Initialize upload
        init_data = {
            'command': 'INIT',
            'total_bytes': total_bytes,
            'media_type': 'video/mp4',
            'media_category': 'tweet_video'
        }
        init_response = requests.post(media_upload_url, auth=auth, data=init_data, timeout=60)
        init_response.raise_for_status()
        media_id = init_response.json()['media_id_string']

        # Upload chunks
        segment_id = 0
        bytes_sent = 0
        with open(video_path, 'rb') as video_file:
            while bytes_sent < total_bytes:
                chunk = video_file.read(4*1024*1024)
                append_data = {
                    'command': 'APPEND',
                    'media_id': media_id,
                    'segment_index': segment_id,
                }
                files = {'media': chunk}
                append_response = requests.post(media_upload_url, auth=auth, data=append_data, files=files, timeout=120)
                append_response.raise_for_status()
                segment_id += 1
                bytes_sent += len(chunk)

        # Finalize upload
        finalize_data = {
            'command': 'FINALIZE',
            'media_id': media_id,
        }
        finalize_response = requests.post(media_upload_url, auth=auth, data=finalize_data, timeout=60)
        finalize_response.raise_for_status()

        # Check processing status
        processing_info = finalize_response.json().get('processing_info', {})
        while processing_info.get('state') in ('pending', 'in_progress'):
            check_after_secs = processing_info.get('check_after_secs', 5)
            logger.info(f"Media processing {processing_info['state']}, waiting {check_after_secs} seconds.")
            time.sleep(check_after_secs)
            status_data = {'command': 'STATUS', 'media_id': media_id}
            status_response = requests.get(media_upload_url, auth=auth, params=status_data, timeout=60)
            status_response.raise_for_status()
            processing_info = status_response.json().get('processing_info', {})

        if processing_info.get('state') == 'succeeded':
            logger.info(f"Media processing completed. Media ID: {media_id}")
            return media_id
        else:
            error_message = processing_info.get('error', {}).get('message', 'Unknown error')
            logger.error(f"Media processing failed: {error_message}")
            return None

    except requests.exceptions.RequestException as e:
        logger.error(f"Request error during Twitter media upload: {str(e)}")
        if hasattr(e, 'response'):
            logger.error(f"Response content: {e.response.text}")
        raise
    except Exception as e:
        logger.error(f"Unexpected error during Twitter media upload: {str(e)}")
        raise

# Function to post to Twitter using v2 API with OAuth 1.0a User Context
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

    except requests.exceptions.RequestException as e:
        logger.error(f"Request exception occurred while posting to Twitter: {str(e)}")
        if hasattr(e, 'response'):
            logger.error(f"Response content: {e.response.text}")
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

def initiate_tiktok_video_upload(video_path):
    """Initiate TikTok video upload and return upload URL and publish ID"""
    access_token, _ = load_tiktok_tokens()
    if not access_token:
        logger.error("No TikTok access token available")
        return None, None

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
        logger.info("Initiating TikTok video upload...")
        response = requests.post(TIKTOK_INIT_UPLOAD_URL, headers=headers, json=data, timeout=60)
        response.raise_for_status()
        response_data = response.json()

        if 'data' not in response_data or 'upload_url' not in response_data['data'] or 'publish_id' not in response_data['data']:
            logger.error(f"Unexpected response structure from TikTok API: {response_data}")
            return None, None

        upload_url = response_data['data']['upload_url']
        publish_id = response_data['data']['publish_id']
        logger.info(f"TikTok upload URL obtained. Publish ID: {publish_id}")
        return upload_url, publish_id
    except requests.exceptions.RequestException as e:
        logger.error(f"Failed to get TikTok upload URL. Error: {str(e)}")
        if hasattr(e, 'response'):
            logger.error(f"Response content: {e.response.text}")
        return None, None
    except Exception as e:
        logger.error(f"Unexpected error when initiating TikTok video upload: {str(e)}")
        return None, None

def upload_video_to_tiktok(upload_url, video_path, max_retries=3, backoff_factor=2):
    """Upload video file to TikTok"""
    access_token, _ = load_tiktok_tokens()
    if not access_token:
        logger.error("No TikTok access token available")
        return False

    video_file_size = os.path.getsize(video_path)
    headers = {
        'Content-Type': 'video/mp4',
        'Authorization': f'Bearer {access_token}',
        'Content-Range': f"bytes 0-{video_file_size-1}/{video_file_size}"
    }

    for attempt in range(max_retries):
        try:
            with open(video_path, 'rb') as video_file:
                logger.info(f"Attempting to upload video to TikTok (Attempt {attempt + 1}/{max_retries})")
                response = requests.put(upload_url, headers=headers, data=video_file, timeout=300)

                logger.info(f"TikTok upload response status: {response.status_code}")

                if response.status_code == 201:
                    logger.info("Video uploaded successfully to TikTok inbox.")
                    return True
                elif response.status_code == 503:
                    logger.warning(f"TikTok server error (503). Retrying in {backoff_factor ** attempt} seconds.")
                    time.sleep(backoff_factor ** attempt)
                else:
                    logger.error(f"Failed to upload video to TikTok. Status code: {response.status_code}")
                    return False
        except requests.exceptions.RequestException as e:
            logger.error(f"Request exception during TikTok upload: {str(e)}")
            if attempt < max_retries - 1:
                logger.info(f"Retrying in {backoff_factor ** attempt} seconds.")
                time.sleep(backoff_factor ** attempt)
            else:
                logger.error("Max retries reached. Upload failed.")
                return False
        except Exception as e:
            logger.error(f"Unexpected error during TikTok upload: {str(e)}")
            return False

    return False

def check_tiktok_upload_status(publish_id):
    """Check TikTok upload status"""
    access_token, _ = load_tiktok_tokens()
    if not access_token:
        logger.error("No TikTok access token available")
        return None

    headers = {
        'Authorization': f'Bearer {access_token}',
        'Content-Type': 'application/json',
    }

    data = {"publish_id": publish_id}

    try:
        logger.info(f"Checking TikTok upload status for Publish ID: {publish_id}")
        response = requests.post(TIKTOK_CHECK_STATUS_URL, headers=headers, json=data, timeout=30)
        response.raise_for_status()
        response_data = response.json()
        logger.debug(f"TikTok status response: {json.dumps(response_data, indent=2)}")
        return response_data
    except requests.exceptions.RequestException as e:
        logger.error(f"Failed to check TikTok upload status. Error: {str(e)}")
        if hasattr(e, 'response') and e.response is not None:
            logger.error(f"Response content: {e.response.text}")
        return None
    except Exception as e:
        logger.error(f"Unexpected error while checking TikTok upload status: {e}")
        return None

def poll_tiktok_status_until_inbox(publish_id, max_retries=10, poll_interval=30):
    """Poll TikTok status until video reaches inbox"""
    for attempt in range(max_retries):
        status_response = check_tiktok_upload_status(publish_id)
        if status_response:
            status = status_response['data'].get('status')
            uploaded_bytes = status_response['data'].get('uploaded_bytes', 0)
            logger.info(f"TikTok upload status: {status}. Uploaded bytes: {uploaded_bytes}")

            if status == "SEND_TO_USER_INBOX":
                logger.info("Video sent to TikTok inbox. You can now post it from the TikTok app.")
                return True
            elif status in ['IN_PROGRESS', 'PROCESSING', 'PROCESSING_UPLOAD']:
                logger.info(f"Media still processing. Waiting {poll_interval} seconds before retry. Attempt {attempt + 1}/{max_retries}")
                time.sleep(poll_interval)
            else:
                logger.error(f"Unexpected status: {status}")
                return False
        else:
            logger.warning(f"Failed to retrieve status on attempt {attempt + 1}. Retrying in {poll_interval} seconds.")
            time.sleep(poll_interval)

    logger.warning("TikTok upload status did not reach SEND_TO_USER_INBOX after maximum retries.")
    return False

def post_to_tiktok(video_path):
    """Complete TikTok posting process"""
    if not validate_tiktok_token():
        logger.info("TikTok token is invalid. Attempting to refresh...")
        if not refresh_tiktok_token():
            logger.error("Failed to refresh TikTok token. Manual reauthorization may be required.")
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
        if poll_tiktok_status_until_inbox(publish_id):
            logger.info("Video successfully posted to TikTok.")
            return True
        else:
            logger.info(f"Waiting 30 seconds before next status check. Attempt {attempt + 1}/10")
            time.sleep(30)

    logger.warning("TikTok upload status did not reach inbox after maximum retries.")
    return False

# Function to send email notifications
def send_email(subject: str, body: str):
    """Send status email using the relay"""
    # Create email body with HTML formatting matching cave hacks script
    formatted_body = f"""<p><strong>Product Review Social Media Automation Report</strong></p>
<p>Source Server: Hetzner (5.161.70.26)<br>
Project: /opt/social-automation</p>

<p><strong>Product Video Posting Summary:</strong></p>

<p>{body}</p>

<p>Please check the platforms for any failed postings.</p>

<p>Log file: {log_file_path}</p>"""
    
    return send_email_notification(subject, formatted_body, is_error=False)

def load_song_history():
    if not os.path.exists(SONG_HISTORY_FILE):
        return {}

    song_history = {}
    with open(SONG_HISTORY_FILE, 'r', newline='') as csvfile:
        reader = csv.reader(csvfile)
        for row in reader:
            if len(row) >= 2:
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

def generate_image(prompt):
    try:
        headers = {
            "Authorization": f"Bearer {OPENAI_API_KEY}",
            "Content-Type": "application/json"
        }
        data = {
            "prompt": prompt,
            "n": 1,
            "size": "1024x1024",
            "model": "dall-e-3",
            "quality": "hd",
            "style": "vivid"
        }
        response = requests.post(
            "https://api.openai.com/v1/images/generations", headers=headers, json=data, timeout=60
        )
        response_data = response.json()
        if response.status_code == 200:
            image_url = response_data['data'][0]['url']
            logger.debug(f"Generated image URL: {image_url}")
            return image_url
        else:
            logger.error(f"Failed to generate image: {response_data}")
            raise Exception(f"OpenAI API error: {response_data}")
    except Exception as e:
        logger.error(f"Error generating image: {str(e)}")
        raise

def download_image(image_url):
    try:
        response = requests.get(image_url, timeout=60)
        if response.status_code == 200:
            # Create a temporary file
            with tempfile.NamedTemporaryFile(delete=False, suffix=".png") as temp_file:
                temp_file.write(response.content)
                temp_path = temp_file.name
            logger.info(f"Image saved temporarily: {temp_path}")
            return temp_path
        else:
            logger.error(f"Failed to download image: HTTP {response.status_code}")
            return None
    except Exception as e:
        logger.error(f"Failed to save image: {e}")
        return None

def describe_image_vision(image_path):
    try:
        with open(image_path, "rb") as image_file:
            base64_image = base64.b64encode(image_file.read()).decode('utf-8')

        headers = {
            "Authorization": f"Bearer {OPENAI_API_KEY}",
            "Content-Type": "application/json"
        }
        data = {
            "model": "gpt-4o-2024-08-06",
            "messages": [
                {
                    "role": "user",
                    "content": [
                        {"type": "text", "text": "Describe what's happening in this image."},
                        {"type": "image_url", "image_url": {"url": f"data:image/png;base64,{base64_image}"}}
                    ]
                }
            ],
            "max_tokens": 300,
        }
        response = requests.post(
            "https://api.openai.com/v1/chat/completions", headers=headers, json=data, timeout=60
        )

        response.raise_for_status()
        response_data = response.json()
        result = response_data['choices'][0]['message']['content']
        logger.debug(f"Vision-based image description: {result[:50]}...")
        return result.strip()
    except requests.exceptions.RequestException as e:
        logger.error(f"Request to OpenAI API failed: {str(e)}")
        if hasattr(e, 'response') and e.response is not None:
            logger.error(f"Response status code: {e.response.status_code}")
        return "Failed to generate image description due to API error."
    except json.JSONDecodeError as e:
        logger.error(f"Failed to decode JSON response: {str(e)}")
        return "Failed to generate image description due to unexpected API response."
    except Exception as e:
        logger.error(f"Error generating vision-based description: {str(e)}")
        return "Failed to generate image description due to an unexpected error."

def generate_hashtags(caption, max_tokens=30):
    try:
        headers = {
            "Authorization": f"Bearer {OPENAI_API_KEY}",
            "Content-Type": "application/json"
        }
        hashtag_prompt = (
            f"Based on this product review caption: \"{caption}\", "
            "generate 2 relevant and engaging hashtags. "
            "The hashtags should be product-related and engaging for social media. "
            "Don't use spaces in the hashtags. Return only the hashtags, separated by spaces."
        )
        data = {
            "model": "gpt-4o-2024-08-06",
            "messages": [{"role": "user", "content": hashtag_prompt}],
            "max_tokens": max_tokens,
            "temperature": 0.7,
        }
        response = requests.post(
            "https://api.openai.com/v1/chat/completions", headers=headers, json=data, timeout=60
        )
        response_data = response.json()
        result = response_data['choices'][0]['message']['content']
        logger.debug(f"Generated hashtags: {result}")
        return result.strip()
    except Exception as e:
        logger.error(f"Error generating hashtags: {str(e)}")
        return "#ProductReview #CaveMan"  # Fallback hashtags

def clean_caption(caption):
    # Remove emojis and symbols
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

    # Remove leading/trailing whitespace and compress multiple spaces
    caption = caption.strip()

    # Remove emojis
    cleaned_caption = emoji_pattern.sub('', caption)

    # Remove spaces before punctuation
    cleaned_caption = re.sub(r'\s+([.,!?])', r'\1', cleaned_caption)

    # Compress multiple spaces into one
    cleaned_caption = re.sub(r'\s+', ' ', cleaned_caption)

    # Final strip to remove any leftover leading/trailing spaces
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

def format_post(caption, hashtags):
    return f"""## Daily Thorak Review ##

{caption}

{hashtags}
"""

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
    response = requests.post(
        "https://api.openai.com/v1/chat/completions", headers=headers, json=data, timeout=60
    )

    if response.status_code == 200:
        result = response.json()['choices'][0]['message']['content']
        logger.debug(f"GPT-4o suggested moods and instruments: {result}")
        return result.strip()
    else:
        logger.error(f"Failed to generate moods and instruments: {response.text}")
        raise Exception(f"GPT-4o API error: {response.text}")

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

def search_music_by_tags(tags, max_results=20, page=1):
    params = {
        'query': f'{tags} music',
        'fields': 'id,name,previews,tags',
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
        logger.debug(f"Number of results before filtering: {len(results)}")

        filtered_results = [r for r in results if is_music(r)]

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
    preview_url = result['previews'].get('preview-hq-mp3')
    if not preview_url:
        logger.error(f"No preview URL found for sound: {result['name']}")
        return None

    try:
        response = requests.get(preview_url, stream=True, timeout=60)
        response.raise_for_status()

        with tempfile.NamedTemporaryFile(delete=False, suffix='.mp3') as temp_file:
            for chunk in response.iter_content(chunk_size=8192):
                if chunk:
                    temp_file.write(chunk)

        if os.path.exists(temp_file.name) and os.path.getsize(temp_file.name) > 0:
            try:
                audio = AudioFileClip(temp_file.name)
                duration = audio.duration
                audio.close()
                logger.info(f"Downloaded and verified sound preview: {result['name']} (duration: {duration}s)")
                return temp_file.name
            except Exception as e:
                logger.error(f"Error verifying audio file: {e}")
                os.unlink(temp_file.name)
                return None
        else:
            logger.error(f"Downloaded file is empty or does not exist: {temp_file.name}")
            return None
    except requests.exceptions.RequestException as e:
        logger.error(f"Failed to download sound preview: {result['name']} (Error: {str(e)})")
        return None

def create_audio_with_elevenlabs(text, output_path):
    url = "https://api.elevenlabs.io/v1/text-to-speech/3CPYpnjA7qcrob1wmN2h"
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

            # Load the created audio into MoviePy
            voiceover = AudioFileClip(output_path)

            # Apply a fade-out effect to the last 0.5 seconds of the voiceover
            voiceover_with_fade = voiceover.audio_fadeout(0.5)

            # Create 1 second of silence
            silence = AudioClip(lambda t: 0, duration=1)

            # Concatenate the faded voiceover with the silence
            voiceover_with_silence = concatenate_audioclips([voiceover_with_fade, silence])

            # Write the final result to a new file
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
    logger.debug(f"Created end screen with logo")

    return end_screen

def adjust_frames_to_voiceover_duration(frames, voiceover_duration):
    # Total number of frames that should match the voiceover duration
    expected_frame_count = int(voiceover_duration * 24)

    # If we have fewer frames than the required duration, add more frames at the end
    if len(frames) < expected_frame_count:
        remaining_frames = expected_frame_count - len(frames)
        frames.extend([frames[-1]] * remaining_frames)  # Extend the last frame
    # If we have more frames, trim to match the voiceover
    elif len(frames) > expected_frame_count:
        frames = frames[:expected_frame_count]  # Trim the extra frames

    return frames

def create_typing_effect(text, voiceover_duration, video_size, font_path):
    frames = []
    words = text.split()
    total_words = len(words)

    base_word_duration = voiceover_duration / total_words

    start_index = 0
    while start_index < total_words:
        end_index = min(start_index + 10, total_words)
        current_words = words[start_index:end_index]

        for i in range(len(current_words)):
            frame = create_subtitle_frame(words[start_index:start_index + i + 1], video_size, font_path)
            word_frames = max(1, int(base_word_duration * 24))  # Ensure at least 1 frame per word
            frames.extend([frame] * word_frames)

        start_index = end_index

    # Convert list of frames (numpy arrays) to an ImageSequenceClip
    video_clip = ImageSequenceClip(frames, fps=24)

    return video_clip

def create_subtitle_frame(sentence_words, video_size, font_path, max_font_size=100, min_font_size=30):
    img = Image.new('RGBA', video_size, (0, 0, 0, 0))  # Create transparent image
    draw = ImageDraw.Draw(img)

    # Define font sizes and words per row for dynamic layout
    font_sizes = [100, 70, 56, 34, 80, 56]
    words_per_row = [1, 2, 2, 3, 2, 2]  # Adjusted for different sizes of text

    y_position = video_size[1] // 4  # Start drawing text from 1/4th down the video
    left_margin = video_size[0] // 10  # 10% margin from the left
    right_margin = video_size[0] // 10  # 10% margin from the right
    max_text_width = video_size[0] - left_margin - right_margin  # Adjusted for margins

    padding = 10  # Padding around the text for background
    max_words_per_screen = 10  # Maximum words per subtitle screen

    words_to_draw = sentence_words[:max_words_per_screen]
    row_word_index = 0

    for row, (font_size, word_count) in enumerate(zip(font_sizes, words_per_row)):
        if row_word_index >= len(words_to_draw):
            break  # Stop if all words are used for this chunk

        # Loop to reduce font size if the text doesn't fit within the frame
        while font_size >= min_font_size:
            try:
                font = ImageFont.truetype(font_path, font_size)
            except IOError:
                logger.error(f"Font file not found: {font_path}")
                raise
            row_words = words_to_draw[row_word_index:row_word_index + word_count]  # Select words for this row
            text = ' '.join(row_words).upper()  # Convert to uppercase for subtitle style

            # Calculate text size
            text_bbox = draw.textbbox((left_margin, y_position), text, font=font)
            text_width = text_bbox[2] - text_bbox[0]

            # Check if the text fits within the allowed width
            if text_width <= max_text_width:
                break  # If the text fits, break out of the loop
            else:
                font_size -= 5  # Decrease the font size and try again

        # Adjust background's vertical position
        text_height = text_bbox[3] - text_bbox[1]
        bg_top = text_bbox[1] - padding
        bg_bottom = text_bbox[3] + padding

        # Draw semi-transparent background for text
        background_shape = [
            left_margin - padding,
            bg_top,
            left_margin + text_width + padding,
            bg_bottom
        ]
        draw.rectangle(background_shape, fill=(0, 0, 0, 120))  # Semi-transparent background

        # Draw the text
        draw.text((left_margin, y_position), text, font=font, fill=(255, 255, 255, 255))

        y_position += font_size * 1.2  # Move down for the next line
        row_word_index += word_count  # Move to the next set of words

    return np.array(img)

def create_zoom_effect(clip, duration, zoom_factor=1.5):
    def zoom(t):
        progress = t / duration
        scale = 1 + (zoom_factor - 1) * progress
        return scale

    return clip.resize(lambda t: zoom(t)).set_position(('center', 'center')).set_duration(duration)

def create_video_with_zooming_image_and_music(image_path, text, logo_end_screen_path):
    temp_files = []
    clips_to_close = []
    
    try:
        logger.info(f"Starting video creation with image: {image_path}")

        if not os.path.exists(image_path):
            raise FileNotFoundError(f"Image file not found: {image_path}")

        # Convert image to RGB
        rgb_image_path = ensure_rgb(image_path)
        if rgb_image_path != image_path:
            temp_files.append(rgb_image_path)

        # Generate image description and mood/instrument suggestions
        image_description = describe_image_vision(rgb_image_path)
        if image_description.startswith("Failed to generate"):
            logger.warning(f"Using fallback image description: {image_description}")
            image_description = "A product image"  # Fallback description

        response_text = gpt4_generate_mood_and_instrument(text, image_description)
        moods, instruments = gpt4_extract_mood_instrument(response_text)

        # Create audio with ElevenLabs
        with tempfile.NamedTemporaryFile(delete=False, suffix='.mp3') as temp_audio:
            temp_audio_path = temp_audio.name
        temp_files.append(temp_audio_path)
        
        final_audio_path = create_audio_with_elevenlabs(text, temp_audio_path)
        temp_files.append(final_audio_path)

        voiceover = AudioFileClip(final_audio_path)
        clips_to_close.append(voiceover)
        silence = AudioClip(lambda t: 0, duration=1)  # 1 second of silence
        voiceover_with_silence = concatenate_audioclips([voiceover, silence])
        voiceover_duration = voiceover_with_silence.duration
        logger.info(f"Voiceover duration (with silence): {voiceover_duration} seconds")

        # Search for and download music from Freesound
        music_path = None
        song_history = load_song_history()
        music_sound = None
        used_tags = []

        for mood in moods + instruments:
            if mood in used_tags:
                continue
            used_tags.append(mood)

            logger.info(f"Searching for music with tag: {mood}")
            music_results = search_music_by_tags(mood)

            if music_results is None:
                logger.warning(f"No music results found for tag: {mood}")
                continue

            if not music_results:
                logger.warning(f"Empty music results for tag: {mood}")
                continue

            random.shuffle(music_results)
            for result in music_results:
                if is_song_recently_used(result['id'], song_history):
                    logger.info(f"Skipping recently used song: {result['name']}")
                    continue

                music_path = download_music(result)
                if music_path:
                    temp_files.append(music_path)
                    try:
                        music_sound = AudioFileClip(music_path)
                        clips_to_close.append(music_sound)
                        logger.info(f"Successfully found and loaded music for {mood}: {result['name']}")
                        update_song_history(result['id'], song_history)
                        break
                    except Exception as e:
                        logger.error(f"Error loading music file: {e}")
                        music_sound = None

            if music_sound:
                break

        if music_sound is None:
            logger.warning("No valid music found. Using fallback audio.")
            music_sound = AudioFileClip(FREESOUND_PLACEHOLDER)
            clips_to_close.append(music_sound)

        total_duration = voiceover_duration + 3  # Main video (including 1-second buffer) + end screen
        music_sound = match_music_to_duration(music_sound, total_duration)

        # Load and process the image
        logger.info(f"Loading image from {rgb_image_path}")
        clip = ImageClip(rgb_image_path)
        clips_to_close.append(clip)
        zoomed_clip = create_zoom_effect(clip, voiceover_duration, zoom_factor=1.5)

        # Use cleaned caption for subtitles
        cleaned_caption = clean_caption(text)

        # Create subtitles
        font_path = os.path.join(project_root, "assets", "fonts", "Jost-Bold.ttf")
        if not os.path.exists(font_path):
            logger.error(f"Font file not found: {font_path}")
            raise FileNotFoundError(f"Font file not found: {font_path}")
            
        video_size = clip.size

        subtitle_clip = create_typing_effect(cleaned_caption, voiceover_duration, video_size, font_path)

        # Compose the main video (zoomed image + subtitles)
        main_video = CompositeVideoClip([zoomed_clip, subtitle_clip])
        main_video = main_video.set_duration(voiceover_duration)  # This includes the 1-second buffer

        # Create end screen
        end_screen = create_end_screen(logo_end_screen_path, "#012445", 3, video_size)

        # Concatenate main video and end screen
        final_clip = concatenate_videoclips([main_video, end_screen])

        # Set the audio for the entire video
        final_audio = CompositeAudioClip([
            voiceover_with_silence,
            music_sound.volumex(0.1).set_duration(final_clip.duration)
        ])
        final_clip = final_clip.set_audio(final_audio)

        # Create temporary output video file
        with tempfile.NamedTemporaryFile(delete=False, suffix='.mp4') as temp_video_file:
            output_video_path = temp_video_file.name
            final_clip.write_videofile(output_video_path, fps=24, codec='libx264', audio_codec='aac', threads=2, logger=None)
            logger.info(f"Video saved temporarily: {output_video_path}")

        return output_video_path, temp_files

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

def trim_to_full_sentence(text, max_length):
    sentences = re.split(r'(?<=[.!?]) +', text.strip())  # Split by sentence-ending punctuation
    final_caption = ""

    for sentence in sentences:
        if len(final_caption) + len(sentence) + 1 <= max_length:  # +1 for space
            final_caption += sentence + " "
        else:
            break

    final_caption = final_caption.strip()

    # Ensure that the caption does not end with an incomplete sentence
    if len(final_caption) > 0 and final_caption[-1] not in '.!?':
        # Remove the incomplete sentence if it exists
        final_caption = final_caption.rsplit(' ', 1)[0].rstrip()

    return final_caption.strip()

def post_to_all_platforms_with_cleanup(video_path, final_fb_ig_post_content, final_twitter_post_content, hosted_video_url, remote_video_path, sftp_host, sftp_username, sftp_password, page_id, FB_ACCESS_TOKEN):
    """Post to all platforms and cleanup files"""
    
    # Post to Facebook
    facebook_success = post_to_facebook(final_fb_ig_post_content, hosted_video_url, page_id, FB_ACCESS_TOKEN)
    print("Posted to Facebook!" if facebook_success else "Failed to post to Facebook.")

    # Post to Instagram  
    instagram_success = post_to_instagram(final_fb_ig_post_content, hosted_video_url)
    print("Posted to Instagram!" if instagram_success else "Failed to post to Instagram.")

    # Twitter posting (uses local file)
    twitter_success = twitter_post_with_media(final_twitter_post_content, video_path)
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

# Log database configuration
logger.info("Database Configuration:")
logger.info(f"Host: {db_config.host}")
logger.info(f"Database: {db_config.name}")
logger.info(f"User: {db_config.user}")

# Main execution
if __name__ == "__main__":
    start_time = time.time()
    image_path = None
    video_path = None
    temp_files = []

    # Define your Facebook Page ID and SFTP details (loaded from .env)
    page_id = FB_PAGE_ID
    sftp_host = SFTP_HOST
    sftp_username = SFTP_USERNAME
    sftp_password = SFTP_PASSWORD

    # Path to the logo images - Updated for new structure
    logo_end_screen_path = os.path.join(project_root, "assets", "logos", "logo-white-thorak.png")

    logger.info(f"Script is running from: {project_root}")
    logger.info(f"Log file will be saved to: {log_file_path}")
    logger.info("Starting product review video generation...")

    # Get the current timestamp in the desired format
    timestamp = datetime.now().strftime("%y%m%d:%H%M%S")

    try:
        # Check for Freesound API key
        if not FREESOUND_API_KEY:
            raise ValueError("Freesound API key is missing. Please check your credentials.env file.")
        logger.info("Freesound API key found.")

        logger.info("Connecting to DigitalOcean production database...")

        # Get random product from database
        selected_product = get_random_product()
        if not selected_product:
            logger.error("Failed to get random product from database")
            sys.exit(1)

        logger.info("Selected product details:")
        logger.info(f"Title: {selected_product['Title']}")
        logger.info(f"Base_URL: {selected_product['Base_URL']}")
        logger.info(f"Thumbnail: {selected_product['thumbnail']}")
        logger.info(f"Gallery IDs: {selected_product['gallery_ids']}")

        # Generate content for social media
        fb_ig_prompt = (
            f"""Write a short and catchy social media post of 50 words or less promoting the following product
in the tongue-in-cheek voice of a caveman named Thorak. Please mention each
product by name and highlight the unique selling points of the product,
crafting posts that will capture the attention of the audience.
Please include emojis throughout, and place two line breaks after the post.
Do not use double asterisks (**) for emphasis or formatting.
At the end of the post, include two hashtags that are 20 characters or less each and
that are specific to the product but do not include #mancave as one of those hashtags.:\n\n
Product: {selected_product['Title']}\n
Description: {selected_product['Short_Description']}\n\n
Include an engaging call to action.\n\n"""
        )
        fb_ig_post_content = generate_social_media_post(fb_ig_prompt)

        fb_ig_post_content = fb_ig_post_content.strip('"')

        hashtags = [word for word in fb_ig_post_content.split() if word.startswith('#')]
        non_hashtag_content = ' '.join([word for word in fb_ig_post_content.split() if not word.startswith('#')])

        # Ensure we have at least 2 hashtags generated by GPT-4o
        while len(hashtags) < 2:
            hashtags.append(f"#{selected_product['Title'].replace(' ', '').lower()}")  # Add a simple hashtag based on the title

        # Shorten the product URL
        short_url = shorten_url(selected_product['Base_URL'])

        final_fb_ig_post_content = f"## Daily Thorak Review ##\n\n{non_hashtag_content}\n\n{' '.join(hashtags[:2])} #Mancave\n\nLearn More: {short_url}"

        final_fb_ig_post_content = final_fb_ig_post_content.replace("[Link to product]", "").strip()

        # Generate content for Twitter based on the original post
        twitter_prompt = (
            f"Please revise '{non_hashtag_content}' to be appropriate for Twitter, ensuring that it is {280 - len(TWEET_LABEL) - len(short_url) - 1} characters or less. "
            f"Please maintain usage of emojis but do not include any hashtags."
        )
        twitter_post_content = generate_social_media_post(twitter_prompt)

        final_twitter_post_content = f"{TWEET_LABEL}{twitter_post_content.strip()} {short_url}"

        product_title = selected_product['Title']
        product_url = selected_product['Base_URL']
        image_url = selected_product['thumbnail']  # Use thumbnail URL directly
        if not image_url:
            logger.error("No thumbnail image found for product")
            raise ValueError("Product thumbnail URL is missing")

        if not product_url:
            logger.warning(f"Missing Product URL for post: {final_fb_ig_post_content[:50]}...")
            raise ValueError("Product URL is missing")

        # Download the image
        image_path = download_image(image_url)
        if not image_path:
            raise ValueError("Failed to download image")
        temp_files.append(image_path)

        # Create the video
        video_path, video_temp_files = create_video_with_zooming_image_and_music(image_path, non_hashtag_content, logo_end_screen_path)
        if not video_path:
            raise ValueError("Failed to create video")
        temp_files.extend(video_temp_files)

        # Upload the final video to your server via SFTP
        remote_video_filename = f"social_product_posting_{uuid.uuid4().hex}.mp4"
        remote_video_path = f"/home/runcloud/webapps/cavesupplies-production/videos/{remote_video_filename}"
        
        if sftp_host and sftp_username and sftp_password:
            upload_file_via_sftp(video_path, remote_video_path, sftp_host, sftp_username, sftp_password)
            logger.info("Video upload completed")
            
            # Use the hosted video URL for posting
            hosted_video_url = f"https://cavesupplies.com/videos/{remote_video_filename}"

            # Post to all platforms and cleanup remote video
            facebook_success, instagram_success, twitter_success, tiktok_success = post_to_all_platforms_with_cleanup(
                video_path, 
                final_fb_ig_post_content, 
                final_twitter_post_content, 
                hosted_video_url, 
                remote_video_path, 
                sftp_host, 
                sftp_username, 
                sftp_password, 
                page_id, 
                FB_ACCESS_TOKEN
            )
        else:
            logger.error("SFTP credentials are not properly set in the environment variables.")
            facebook_success = instagram_success = twitter_success = tiktok_success = False

        # Add product to blacklist
        if not add_to_blacklist(selected_product['ID']):
            logger.error(f"Failed to add product {selected_product['ID']} to blacklist")

        # Update email notification
        posting_statuses = {
            "Facebook": "Success" if facebook_success else "Failed",
            "Instagram": "Success" if instagram_success else "Failed",
            "Twitter": "Success" if twitter_success else "Failed",
            "TikTok": "Success" if tiktok_success else "Failed"
        }
        failed_count = sum(1 for status in posting_statuses.values() if status == "Failed")
        timestamp = datetime.now().strftime('%y%m%d:%H%M%S')
        if failed_count == 0:
            subject = f"Product Video Posted - All Successful - {timestamp}"
        else:
            subject = f"Product Video Posted - {failed_count} Failed - {timestamp}"
        body_lines = []
        for platform, status in posting_statuses.items():
            body_lines.append(f"{platform}: {status}")

        body = "<br>".join(body_lines)
        send_email(subject, body)

    except ValueError as ve:
        logger.error(f"Validation error: {ve}")
        timestamp = datetime.now().strftime('%y%m%d:%H%M%S')
        subject = f"Product Video Posting Script Failed - {timestamp}"
        body = f"Validation error: {str(ve)}\n\nPlease check the script configuration."
        send_email(subject, body)
    except requests.exceptions.RequestException as re:
        logger.error(f"API request error: {str(re)}")
        if re.response is not None:
            logger.error(f"API response status code: {re.response.status_code}")
            logger.error(f"API response content: {re.response.text}")
        timestamp = datetime.now().strftime('%y%m%d:%H%M%S')
        subject = f"Product Video Posting Script Failed - {timestamp}"
        body = f"API request error: {str(re)}\n\nPlease check API credentials and connectivity."
        send_email(subject, body)
    except Exception as e:
        logger.error(f"Failed to generate or post content: {str(e)}")
        logger.error(f"Error details: {type(e).__name__}, {str(e)}")
        logger.error(f"Traceback: {traceback.format_exc()}")
        print(f"Error: Failed to generate or post content: {str(e)}")

        # Script failed
        timestamp = datetime.now().strftime('%y%m%d:%H%M%S')
        subject = f"Product Video Posting Script Failed - {timestamp}"
        body = f"An error occurred: {str(e)}\n\nTraceback:\n{traceback.format_exc()}"
        send_email(subject, body)

    finally:
        # Clean up temporary files
        for temp_file in temp_files + [video_path]:
            if temp_file and os.path.exists(temp_file):
                try:
                    os.unlink(temp_file)
                    logger.debug(f"Removed temporary file: {temp_file}")
                except Exception as e:
                    logger.warning(f"Failed to remove temporary file {temp_file}: {str(e)}")

    total_time = time.time() - start_time
    logger.debug(f"Total execution time: {total_time:.2f} seconds")
    print(f"Total execution time: {total_time:.2f} seconds")

    print(f"Script execution completed. Please check {log_file_path} for detailed logs.")