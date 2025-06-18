#!/usr/bin/env python3
"""
Thorak Social Media Video Creator - Hetzner to DigitalOcean Production

Architecture:
- Runs on: Hetzner server (staging environment, IP: 5.161.70.26)  
- Posts to: Facebook, Instagram, Twitter, TikTok
- Database: DigitalOcean production (if needed for analytics)

This script creates and posts daily Thorak caveman thought videos to social media platforms.
It generates images using DALL-E, creates voiceovers with ElevenLabs, adds background music
from Freesound, and posts the final videos to all major social platforms.

Usage:
  python scripts/social_thorak_thoughts_video.py
"""

import os
import logging
import json
import time
import requests
import traceback
from pathlib import Path
from urllib.parse import quote, urlencode, urlparse, parse_qs
import uuid
from datetime import datetime, timedelta
import pytz
from PIL import Image, ImageDraw, ImageFont
from dotenv import load_dotenv
import smtplib
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
import random
import base64
import paramiko
from moviepy.editor import *
import tempfile
import re
import numpy as np
import csv
from functools import wraps
from requests_oauthlib import OAuth1

# Set up project paths
project_root = "/opt/social-automation"
os.chdir(project_root)

# Load environment variables
dotenv_path = os.path.join(project_root, "credentials.env")
load_dotenv(dotenv_path)

# Set up logging
log_file_path = os.path.join(project_root, "logs", "thorak_video_creation.log")

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

logging.info(f"Thorak Video Creator started - Hetzner to Social Media Platforms")
logging.info(f"Project root: {project_root}")
logging.info(f"Log file: {log_file_path}")

# Load environment variables
OPENAI_API_KEY = os.getenv("OPENAI_API_KEY")
FB_ACCESS_TOKEN = quote(os.getenv("FB_ACCESS_TOKEN"))
INSTAGRAM_BUSINESS_ACCOUNT_ID = os.getenv("INSTAGRAM_BUSINESS_ACCOUNT_ID")
SENDER_EMAIL = os.getenv("SENDER_EMAIL")
SENDER_PASSWORD = os.getenv("SENDER_PASSWORD")
SMTP_SERVER = os.getenv("SMTP_SERVER")
SMTP_PORT = int(os.getenv("SMTP_PORT", 587))  # Changed from 465 to 587
RECIPIENT_EMAIL = os.getenv("RECIPIENT_EMAIL")
ELEVENLABS_API_KEY = os.getenv("ELEVENLABS_API_KEY")
GPT_4O_API_KEY = os.getenv("OPENAI_API_KEY")
FREESOUND_API_KEY = os.getenv("FREESOUND_API_KEY")
FREESOUND_CLIENT_ID = os.getenv("FREESOUND_CLIENT_ID")
FREESOUND_CLIENT_SECRET = os.getenv("FREESOUND_CLIENT_SECRET")
FREESOUND_REDIRECT_URI = os.getenv("FREESOUND_REDIRECT_URI")
TWITTER_API_KEY = os.getenv("TWITTER_API_KEY")
TWITTER_API_SECRET = os.getenv("TWITTER_API_SECRET")
TWITTER_ACCESS_TOKEN = os.getenv("TWITTER_ACCESS_TOKEN")
TWITTER_ACCESS_TOKEN_SECRET = os.getenv("TWITTER_ACCESS_TOKEN_SECRET")
BITLY_API_KEY = os.getenv("BITLY_API_KEY")

# File paths updated for new structure
SONG_HISTORY_FILE = os.path.join(project_root, "data", "song_history.csv")
SONG_REUSE_DAYS = 14
SOUND_DOWNLOAD_FOLDER = os.path.join(project_root, "assets", "sounds")
FREESOUND_PLACEHOLDER = os.path.join(project_root, "assets", "sounds", "freesound_placeholder.mp3")
IMAGE_DESCRIPTIONS_FILE = os.path.join(project_root, "data", "image_descriptions.json")

# TikTok credentials
TIKTOK_ACCESS_TOKEN = os.getenv("TIKTOK_ACCESS_TOKEN")
TIKTOK_REFRESH_TOKEN = os.getenv("TIKTOK_REFRESH_TOKEN")
TIKTOK_CLIENT_KEY = os.getenv("TIKTOK_CLIENT_KEY")
TIKTOK_CLIENT_SECRET = os.getenv("TIKTOK_CLIENT_SECRET")
TIKTOK_REDIRECT_URI = "https://www.cavesupplies.com/callback"

# TikTok API endpoints
TIKTOK_INIT_UPLOAD_URL = "https://open.tiktokapis.com/v2/post/publish/inbox/video/init/"
TIKTOK_CHECK_STATUS_URL = "https://open.tiktokapis.com/v2/post/publish/status/fetch/"

# TikTok tokens file
TIKTOK_TOKEN_FILE = os.path.join(project_root, "data", "tiktok_tokens.json")

# Ensure the sound download folder exists
os.makedirs(SOUND_DOWNLOAD_FOLDER, exist_ok=True)

# Ensure all required TikTok variables are set
required_tiktok_vars = ["TIKTOK_CLIENT_KEY", "TIKTOK_CLIENT_SECRET", "TIKTOK_REDIRECT_URI", "TIKTOK_ACCESS_TOKEN", "TIKTOK_REFRESH_TOKEN"]
missing_vars = [var for var in required_tiktok_vars if not globals()[var]]
if missing_vars:
    logger.error(f"Missing required TikTok environment variables: {', '.join(missing_vars)}")
    raise ValueError(f"Missing required TikTok environment variables: {', '.join(missing_vars)}")

def notify_reauthorization_required(service="Freesound"):
    subject = f"{service} Reauthorization Required - Hetzner Social Automation"
    body = f"The {service} token has expired and could not be refreshed automatically. Please run the script manually to reauthorize."
    send_email(subject, body)
    logger.critical(f"{service} reauthorization required. Notification sent.")

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

        logger.debug(f"OpenAI API response: {response_data}")

        if 'choices' not in response_data:
            logger.error(f"Unexpected response structure. 'choices' key not found. Full response: {response_data}")
            return "Error: Unable to generate image description due to unexpected API response."

        result = response_data['choices'][0]['message']['content']
        logger.debug(f"Vision-based image description: {result[:50]}...")
        return result.strip()
    except requests.exceptions.RequestException as e:
        logger.error(f"Request failed: {str(e)}")
        return f"Error: Request to OpenAI API failed - {str(e)}"
    except KeyError as e:
        logger.error(f"KeyError: {str(e)}. Full response: {response_data}")
        return f"Error: Unexpected response structure from OpenAI API - {str(e)}"
    except Exception as e:
        logger.error(f"Error generating vision-based description: {str(e)}")
        return f"Error: Failed to generate image description - {str(e)}"

def generate_social_media_caption(description, selected_quote, max_tokens=60):
    max_retries = 3
    for attempt in range(max_retries):
        try:
            logger.debug(f"Calling OpenAI with image description: {description[:50]}...")
            headers = {
                "Authorization": f"Bearer {OPENAI_API_KEY}",
                "Content-Type": "application/json"
            }
            caption_prompt = (
                "You are Thorak, a simple caveman. "
                "You have been transplanted from the prehistoric age and just discovered one of life's modern comforts and are inspired. "
                "Here's a wise saying you just heard: \"{}\". "
                "Think about this saying and describe your thoughts in relation to what you are doing in the image described here: "
                f"{description}. "
                "Describe those thoughts in a humorous, tongue-in-cheek, but primitive and straightforward way, referring to yourself as 'Thorak.' "
                "Please don't mention any specific item or type of furniture and don't mention sitting."
                "Speak in short, broken sentences with simple words, like a caveman. Avoid complex thoughts or language. "
                "Write a description of 20-30 words in this style that includes emojis."
            ).format(selected_quote)
            data = {
                "model": "gpt-4o-2024-08-06",
                "messages": [{"role": "user", "content": caption_prompt}],
                "max_tokens": max_tokens,
                "temperature": 0.7,
            }
            response = requests.post(
                "https://api.openai.com/v1/chat/completions", headers=headers, json=data, timeout=60
            )
            response.raise_for_status()
            response_data = response.json()
            result = response_data['choices'][0]['message']['content']
            logger.debug(f"OpenAI caption: {result[:50]}...")
            return result.strip()
        except requests.exceptions.RequestException as e:
            logger.error(f"Request failed: {str(e)}")
            if attempt == max_retries - 1:
                logger.error("Failed to get caption from OpenAI after maximum retries.")
                raise
            time.sleep(2**attempt)  # Exponential backoff
        except Exception as e:
            logger.error(f"Error generating caption (attempt {attempt + 1}): {str(e)}")
            if attempt == max_retries - 1:
                logger.error("Failed to get caption from OpenAI after maximum retries.")
                raise
            time.sleep(2**attempt)  # Exponential backoff

def generate_hashtags(caption, max_tokens=30):
    try:
        headers = {
            "Authorization": f"Bearer {OPENAI_API_KEY}",
            "Content-Type": "application/json"
        }
        hashtag_prompt = (
            f"Based on this caveman-style caption: \"{caption}\", "
            "generate 3 relevant and humorous hashtags. "
            "The hashtags should be in the style of a caveman discovering modern concepts. "
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
        response.raise_for_status()
        response_data = response.json()
        result = response_data['choices'][0]['message']['content']
        logger.debug(f"Generated hashtags: {result}")
        return result.strip()
    except requests.exceptions.RequestException as e:
        logger.error(f"Request failed: {str(e)}")
        return "#CavemanThoughts #UggaBooga #RockLife"  # Fallback hashtags
    except Exception as e:
        logger.error(f"Error generating hashtags: {str(e)}")
        return "#CavemanThoughts #UggaBooga #RockLife"  # Fallback hashtags

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

    # Remove double quotes only
    cleaned_caption = re.sub(r'["]', '', caption)

    # Remove emojis
    cleaned_caption = emoji_pattern.sub(r'', cleaned_caption)

    # Remove extra spaces before punctuation (e.g., periods, commas, etc.)
    cleaned_caption = re.sub(r'\s+([?.!,])', r'\1', cleaned_caption)

    # Remove the second punctuation if two punctuation marks appear consecutively
    cleaned_caption = re.sub(r'([?.!,])(?=[?.!,])', '', cleaned_caption)

    # Return cleaned caption without unnecessary symbols
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

def format_post(caption, hashtags):
    return f"""## Daily Thorak Thought ##

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
        "Authorization": f"Bearer {GPT_4O_API_KEY}",
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

def validate_freesound_api_key():
    """Validate the Freesound API key."""
    if not FREESOUND_API_KEY:
        logger.error("FREESOUND_API_KEY is missing. Please check your environment variables.")
        return False

    test_url = "https://freesound.org/apiv2/search/text/"
    params = {
        'query': 'piano',  # A simple query to test the API
        'token': FREESOUND_API_KEY,
        'format': 'json'
    }

    try:
        response = requests.get(test_url, params=params, timeout=30)
        if response.status_code == 200:
            logger.info("Freesound API key is valid.")
            return True
        elif response.status_code == 401:  # Unauthorized
            logger.error("Freesound API key is invalid.")
            return False
        else:
            logger.error(f"Unexpected status code when validating Freesound API key: {response.status_code}")
            logger.error(f"Response content: {response.text}")
            return False
    except requests.RequestException as e:
        logger.error(f"Error validating Freesound API key: {str(e)}")
        return False

def handle_freesound_reauthorization():
    """Handle the reauthorization process for Freesound."""
    print("\nFreesound reauthorization required. Please follow these steps:")
    print("1. Go to https://freesound.org/apiv2/apply/")
    print("2. Log in and create a new API key")
    print("3. Enter the new API key below")

    new_api_key = input("Enter your new Freesound API key: ").strip()

    if new_api_key:
        # Update the environment variable
        os.environ['FREESOUND_API_KEY'] = new_api_key
        # Update the global variable
        global FREESOUND_API_KEY
        FREESOUND_API_KEY = new_api_key
        logger.info("Freesound API key updated. Validating the new key...")
        return validate_freesound_api_key()
    else:
        logger.error("No API key provided. Reauthorization failed.")
        return False

def search_music_by_tags(tags, max_results=20, page=1):
    params = {
        'query': f'{tags} music',
        'fields': 'id,name,previews,tags',  # Include 'previews' in fields
        'filter': 'duration:[30 TO 300]',
        'page_size': max_results,
        'page': page,
        'token': FREESOUND_API_KEY,
        'format': 'json'  # Explicitly specify JSON format
    }

    try:
        response = requests.get('https://freesound.org/apiv2/search/text/', params=params, timeout=30)
        response.raise_for_status()

        json_response = response.json()
        results = json_response.get('results', [])
        logger.debug(f"Raw API response: {json.dumps(json_response, indent=2)}")
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
                logger.info(f"Downloaded and verified preview sound: {result['name']} (duration: {duration}s)")
                return temp_music_path
            except Exception as e:
                logger.error(f"Error verifying audio file: {e}")
                os.unlink(temp_music_path)
                return None
        else:
            logger.error(f"Downloaded preview file is empty or does not exist: {temp_music_path}")
            return None
    except requests.RequestException as e:
        logger.error(f"Failed to download preview sound: {result['name']} (Error: {str(e)})")
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
            # Increase timeout slightly with each attempt
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

            return final_output_path # Success, exit the function

        except requests.exceptions.ReadTimeout as e:
            logger.warning(f"ElevenLabs API timed out on attempt {attempt + 1}. Retrying in a moment...")
            if attempt == max_retries - 1: # If this was the last attempt
                logger.error("ElevenLabs API failed after maximum retries.")
                raise Exception("Failed to get response from ElevenLabs after multiple timeouts.") from e
            time.sleep(5 * (attempt + 1)) # Wait 5, 10 seconds before retrying

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

   font_sizes = [100, 70, 56, 34, 80, 56]  # Initial font sizes per row
   words_per_row = [1, 2, 2, 3, 2, 2]      # Number of words per row
   y_position = video_size[1] // 4
   left_margin = video_size[0] // 10  # Use 10% of the video width for left margin
   padding = 5  # Reduced padding for a better fit around text

   word_index = 0
   for row, (initial_font_size, word_count) in enumerate(zip(font_sizes, words_per_row)):
       if word_index >= len(sentence_words) or row >= 6:
           break

       # Get the words for the current row
       row_words = sentence_words[word_index:word_index + word_count]
       text = ' '.join(row_words).upper()

       # Set initial font size and dynamically reduce if necessary
       font_size = initial_font_size
       max_width = video_size[0] - (2 * left_margin)  # Available width minus margins

       # Reduce the font size if the text exceeds the available width
       while font_size > 10:  # Prevent font size from becoming too small
           try:
               font = ImageFont.truetype(font_path, font_size)
           except IOError:
               logger.error(f"Font file not found: {font_path}")
               raise
           text_bbox = draw.textbbox((0, 0), text, font=font)  # Get text size (without offset)
           text_width = text_bbox[2] - text_bbox[0]
           if text_width <= max_width:
               break
           font_size -= 2  # Decrease font size

       # Update font after potential size adjustment
       font = ImageFont.truetype(font_path, font_size)
       text_bbox = draw.textbbox((left_margin, y_position), text, font=font)
       text_width = text_bbox[2] - text_bbox[0]
       text_height = text_bbox[3] - text_bbox[1]

       # Adjust vertical position of background
       bg_top = text_bbox[1] - padding
       bg_bottom = text_bbox[3] + padding

       # Draw semi-transparent black background
       background_shape = [
           left_margin - padding,  # Ensure the background includes the margin
           bg_top,
           left_margin + text_width + padding,  # Ensure the text is offset by the margin
           bg_bottom
       ]
       draw.rectangle(background_shape, fill=(0, 0, 0, 120))  # 50% opacity (adjust as needed)

       # Draw the text with the left margin applied
       draw.text((left_margin, y_position), text, font=font, fill=(255, 255, 255, 255))

       # Move to the next row, increasing the spacing
       y_position += text_height + padding + 15  # Increased spacing between rows

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

def create_video_with_center_image_and_music(image_path, text, logo_end_screen_path):
   try:
       logger.info(f"Starting video creation with image: {image_path}")

       # Generate temporary MP4 file for the final output
       with tempfile.NamedTemporaryFile(delete=False, suffix='.mp4') as temp_video_file:
           video_output_path = temp_video_file.name

       if not os.path.exists(image_path):
           raise FileNotFoundError(f"Image file not found: {image_path}")

       # Convert image to RGB
       rgb_image_path = ensure_rgb(image_path)

       # Generate image description using GPT-4o's vision capabilities
       image_description = describe_image_vision(rgb_image_path)
       if image_description.startswith("Error:"):
           logger.warning(f"Failed to generate image description: {image_description}")
           image_description = "An image of a caveman named Thorak in a humorous situation."

       # Generate moods and instruments
       response_text = gpt4_generate_mood_and_instrument(text, image_description)
       moods, instruments = gpt4_extract_mood_instrument(response_text)

       # Clean the caption
       cleaned_caption = clean_caption(text)

       # Create audio with ElevenLabs
       with tempfile.NamedTemporaryFile(delete=False, suffix='.mp3') as temp_audio:
           temp_audio_path = temp_audio.name

       final_audio_path = create_audio_with_elevenlabs(text, temp_audio_path)

       voiceover = AudioFileClip(final_audio_path)
       silence = AudioClip(lambda t: 0, duration=2)  # 2 seconds of silence
       voiceover_with_silence = concatenate_audioclips([voiceover, silence])
       voiceover_duration = voiceover_with_silence.duration
       logger.info(f"Voiceover duration (with silence): {voiceover_duration} seconds")

       # Search for and download music from Freesound
       temp_music_path = None
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

               temp_music_path = download_music(result)
               if temp_music_path:
                   try:
                       music_sound = AudioFileClip(temp_music_path)
                       logger.info(f"Successfully found and loaded music for {mood}: {result['name']}")
                       update_song_history(result['id'], song_history)
                       break
                   except Exception as e:
                       logger.error(f"Error loading music file: {e}")
                       if os.path.exists(temp_music_path):
                           os.remove(temp_music_path)
                       temp_music_path = None

           if music_sound:
               break

       if music_sound is None:
           logger.warning("No valid music found. Using fallback audio.")
           music_sound = AudioFileClip(FREESOUND_PLACEHOLDER)

       total_duration = voiceover_duration + 3  # Main video + end screen
       music_sound = match_music_to_duration(music_sound, total_duration)
       if music_sound is None:
           logger.error("Failed to match music to duration. Exiting video creation.")
           raise Exception("Music matching failed.")

       final_audio = CompositeAudioClip([
           voiceover_with_silence,
           music_sound.volumex(0.1).set_duration(total_duration)
       ])

       # Load and process the image
       clip = ImageClip(rgb_image_path).set_duration(voiceover_duration)
       zoomed_clip = create_zoom_effect(clip, voiceover_duration, zoom_factor=1.5)

       # Create subtitles
       font_path = os.path.join(project_root, "assets", "fonts", "Jost-Bold.ttf")
       if not os.path.exists(font_path):
           logger.error(f"Font file not found: {font_path}")
           raise FileNotFoundError(f"Font file not found: {font_path}")

       video_size = clip.size

       subtitle_clip = create_typing_effect(cleaned_caption, voiceover_duration, video_size, font_path, buffer_duration=2)

       # Compose the main video (zoomed image + subtitles)
       main_video = CompositeVideoClip([zoomed_clip, subtitle_clip.set_position(('center', 'center'))], size=video_size)
       main_video = main_video.set_duration(voiceover_duration)

       # Create end screen
       end_screen = create_end_screen(logo_end_screen_path, "#012445", 3, video_size)

       # Concatenate main video and end screen
       final_clip = concatenate_videoclips([main_video, end_screen])

       # Set the audio for the entire video
       final_clip = final_clip.set_audio(final_audio)

       # Write the final video to the temporary file
       final_clip.write_videofile(video_output_path, fps=24, codec='libx264', audio_codec='aac', threads=2, logger=None)

       logger.info(f"Video creation completed successfully: {video_output_path}")
       return video_output_path, temp_audio_path, final_audio_path, temp_music_path

   except Exception as e:
       logger.error(f"An error occurred during video creation: {str(e)}")
       raise

def send_email(subject: str, body: str):
   if not all([SENDER_EMAIL, SENDER_PASSWORD, SMTP_SERVER, SMTP_PORT, RECIPIENT_EMAIL]):
       logger.error("Email credentials or recipient email is missing. Please check your environment variables.")
       return

   try:
       message = MIMEMultipart()
       message['From'] = SENDER_EMAIL
       message['To'] = RECIPIENT_EMAIL
       message['Subject'] = f"Thorak Social Automation - Hetzner: {subject}"

       # Enhanced body with architecture info
       enhanced_body = f"""Thorak Social Media Automation Report
Source Server: Hetzner (5.161.70.26)
Project: /opt/social-automation

{body}

Log file: {log_file_path}
"""
       message.attach(MIMEText(enhanced_body, 'plain'))

       # Use STARTTLS on port 587 instead of SSL on port 465
       with smtplib.SMTP(SMTP_SERVER, SMTP_PORT, timeout=30) as server:
           server.starttls()  # Enable TLS encryption
           server.login(SENDER_EMAIL, SENDER_PASSWORD)
           server.send_message(message)

       logger.info("Email notification sent successfully using SMTP.")
   except Exception as e:
       logger.error(f"Failed to send email notification: {str(e)}")

def generate_email_summary(facebook_status, instagram_status, twitter_status, tiktok_status):
   timestamp = datetime.now().strftime('%y%m%d:%H%M%S')

   # Check the statuses
   success_count = sum([facebook_status, instagram_status, twitter_status, tiktok_status])
   total = 4  # Total number of platforms
   failed_count = total - success_count

   if failed_count == 0:
       subject = f"Thorak Video Posted - All Successful - {timestamp}"
   else:
       subject = f"Thorak Video Posted - {failed_count} Failures - {timestamp}"

   body = (
       f"Thorak Video Posting Summary:\n\n"
       f"Facebook: {'Success' if facebook_status else 'Failure'}\n"
       f"Instagram: {'Success' if instagram_status else 'Failure'}\n"
       f"Twitter: {'Success' if twitter_status else 'Failure'}\n"
       f"TikTok: {'Success' if tiktok_status else 'Failure'}\n\n"
       "Please check the platforms for any failed postings."
   )
   return subject, body

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

# Function to upload media to Twitter
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
    global TIKTOK_ACCESS_TOKEN, TIKTOK_REFRESH_TOKEN
    
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
        
        # Update global variables
        TIKTOK_ACCESS_TOKEN = access_token
        TIKTOK_REFRESH_TOKEN = refresh_token
        
        return access_token, refresh_token
    except json.JSONDecodeError as e:
        logger.error(f"JSON decode error while reading {TIKTOK_TOKEN_FILE}: {e}")
        return None, None
    except Exception as e:
        logger.error(f"Unexpected error while reading {TIKTOK_TOKEN_FILE}: {e}")
        return None, None

def refresh_tiktok_token():
   """
   Refresh TikTok access token using the refresh token.
   Updates the tokens in tiktok_tokens.json if successful.
   Returns True if successful, False otherwise.
   """
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
        if response.status_code == 200 or response.status_code == 201:  # Both are success
            short_url = response_data["link"]
            logger.info(f"Successfully shortened URL: {long_url} -> {short_url}")
            return short_url
        else:
            logger.error(f"Bitly failed to shorten URL {long_url}: {response_data}")
            return long_url
    except Exception as e:
        logger.error(f"Exception occurred while shortening URL {long_url}: {str(e)}")
        return long_url

def validate_tiktok_token():
   """
   Validate the current TikTok access token.
   Returns True if valid, False otherwise.
   """
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

def save_tiktok_tokens(access_token, refresh_token):
   """
   Save TikTok access and refresh tokens to tiktok_tokens.json.
   """
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

def get_tiktok_authorization_url():
   """
   Generate the TikTok authorization URL for manual reauthorization.
   """
   try:
       params = {
           "client_key": TIKTOK_CLIENT_KEY,
           "response_type": "code",
           "scope": "user.info.basic,video.upload",
           "redirect_uri": TIKTOK_REDIRECT_URI,
           "state": "state"  # You can set a unique state if needed
       }
       url = f"https://www.tiktok.com/v2/auth/authorize/?{urlencode(params)}"
       logger.info(f"Generated TikTok authorization URL: {url}")
       return url
   except Exception as e:
       logger.error(f"Failed to generate TikTok authorization URL: {str(e)}")
       return None

def exchange_code_for_token(code):
   """
   Exchange the authorization code for access and refresh tokens.
   """
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
   """
   Handle manual reauthorization for TikTok.
   """
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

def post_to_tiktok(video_path):
   """
   Complete TikTok posting process: initiate upload, upload video, check status.
   Returns True if successful, False otherwise.
   """
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

def initiate_tiktok_video_upload(video_path):
   global TIKTOK_ACCESS_TOKEN
   headers = {
       'Authorization': f'Bearer {TIKTOK_ACCESS_TOKEN}',
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

def upload_video_to_tiktok(upload_url, video_path):
   global TIKTOK_ACCESS_TOKEN
   video_file_size = os.path.getsize(video_path)
   headers = {
       'Content-Type': 'video/mp4',
       'Authorization': f'Bearer {TIKTOK_ACCESS_TOKEN}',
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

def check_tiktok_upload_status(publish_id):
   global TIKTOK_ACCESS_TOKEN
   headers = {
       'Authorization': f'Bearer {TIKTOK_ACCESS_TOKEN}',
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

def post_to_facebook(message, video_url, page_id, access_token):
   session = requests.Session()
   url = f"https://graph.facebook.com/v18.0/{page_id}/videos"
   payload = {
       "description": message,
       "access_token": access_token,
       "file_url": video_url,
   }
   headers = {
       "User-Agent": (
           "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
           "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36"
       )
   }
   logger.debug(f"Facebook API URL: {url}")

   # Compute the filtered payload outside the f-string
   filtered_payload = {k: v for k, v in payload.items() if k != 'access_token'}
   logger.debug(f"Payload (excluding access_token): {json.dumps(filtered_payload)}")

   # Optionally, log the access token partially for security
   logger.debug(f"Token being used: {access_token[:10]}...{access_token[-10:]}")

   # Make the API request
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

# Function to post to Instagram
def post_to_instagram(message, video_url, max_retries=20, retry_delay=10):
   """
   Posts a video as a Reel to Instagram using the Facebook Graph API.

   Args:
       message (str): The caption/message for the Reel.
       video_url (str): The URL of the video to be posted.
       max_retries (int, optional): Maximum number of retries for status checks. Defaults to 20.
       retry_delay (int, optional): Delay in seconds between retries. Defaults to 10.

   Returns:
       bool: True if the post was successful, False otherwise.
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
       logger.info(f"Successfully posted Reel to Instagram.")
       return True

   except requests.exceptions.RequestException as e:
       logger.error(f"Failed to post Reel to Instagram. Error: {str(e)}")
       if hasattr(e, 'response'):
           logger.error(f"Response content: {e.response.text}")
       return False

@retry_on_failure(max_retries=10, backoff_factor=1)
def poll_tiktok_status_until_inbox(publish_id, max_retries=10, retry_delay=30):
   check_status_url = "https://open.tiktokapis.com/v2/post/publish/status/fetch/"
   headers = {
       'Authorization': f'Bearer {TIKTOK_ACCESS_TOKEN}',
       'Content-Type': 'application/json',
   }
   data = {
       "publish_id": publish_id
   }

   for attempt in range(max_retries):
       try:
           response = requests.post(check_status_url, headers=headers, json=data, timeout=30)
           response.raise_for_status()
           status_response = response.json()
           status = status_response['data'].get('status')

           if status == "SEND_TO_USER_INBOX":
               logger.info("Video sent to TikTok inbox.")
               return True
           else:
               logger.info(f"Current TikTok upload status: {status}. Retrying in {retry_delay} seconds.")
               time.sleep(retry_delay)
       except Exception as e:
           logger.error(f"Error checking TikTok upload status: {str(e)}")
           time.sleep(retry_delay)
   return False

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

def post_to_all_platforms_with_cleanup(video_path, formatted_caption, caption, short_video_url, remote_video_path, sftp_host, sftp_username, sftp_password, page_id, FB_ACCESS_TOKEN):
    """Post to all platforms and cleanup files"""
    
    # Post to Facebook
    facebook_success = post_to_facebook(formatted_caption, short_video_url, page_id, FB_ACCESS_TOKEN)
    print("Posted to Facebook!" if facebook_success else "Failed to post to Facebook.")

    # Post to Instagram  
    instagram_success = post_to_instagram(formatted_caption, short_video_url)
    print("Posted to Instagram!" if instagram_success else "Failed to post to Instagram.")

    # Twitter posting (uses local file)
    twitter_caption = trim_to_full_sentence(caption, 280 - len("# Thorak Thought # "))
    twitter_caption = f"# Thorak Thought # {twitter_caption}"
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

if __name__ == "__main__":
   start_time = time.time()
    
   # Load TikTok tokens at startup
   load_tiktok_tokens()

   # Define your Facebook Page ID and SFTP details (loaded from .env)
   page_id = os.getenv("FB_PAGE_ID")
   sftp_host = os.getenv("SFTP_HOST")
   sftp_username = os.getenv("SFTP_USERNAME")
   sftp_password = os.getenv("SFTP_PASSWORD")

   # Path to the logo images - Updated for new structure
   logo_end_screen_path = os.path.join(project_root, "assets", "logos", "logo-white-thorak.png")

   # Load quotes from JSON file - Updated for new structure
   quotes_file_path = os.path.join(project_root, "data", "source_quotes.json")
   if not os.path.exists(quotes_file_path):
       logger.error(f"Quotes file not found at {quotes_file_path}. Exiting.")
       raise FileNotFoundError(f"Quotes file not found at {quotes_file_path}.")

   with open(quotes_file_path, 'r') as f:
       quotes = json.load(f)

   if not quotes:
       logger.error("No quotes found in the quotes file. Exiting.")
       raise ValueError("No quotes found in the quotes file.")

   # Keep track of used quotes
   used_quotes = set()

   # Get the current timestamp in the desired format
   timestamp = datetime.now().strftime("%y%m%d:%H%M%S")

   # Initialize success flags for each platform
   facebook_success = instagram_success = twitter_success = tiktok_success = False

   # Initialize paths to temp files (for cleanup later)
   image_path = video_path = temp_music_path = temp_audio_path = final_audio_path = None

   try:
       # Freesound API key validation
       if not validate_freesound_api_key():
           if not handle_freesound_reauthorization():
               raise ValueError("Failed to validate or reauthorize Freesound API key")

       logger.info("Freesound API key validation completed.")

       # Generate the image using DALL·E 3 via OpenAI API
       image_prompt = (
           "Create a humorous, tongue-in-cheek image from the perspective of a caveman named Thorak "
           "who has recently made a new discovery and is expressing a sense of wonder or quiet reflection. "
           "The image should be designed in a vintage cartoon style, "
           "reminiscent of mid-20th-century comic strips or retro advertisements. The artwork should feature "
           "bold, clean lines with a slightly exaggerated, hand-drawn aesthetic. The colors should be muted, "
           "with a palette that includes earth tones, giving it an aged or weathered look. The character design "
           "should be simple yet expressive, with a strong emphasis on the caveman's friendly yet rugged features. The background "
           "should be minimalistic, with a soft, gradient effect to suggest depth without distracting from the central figures. "
           "Overall, the style should evoke a sense of nostalgia, blending humor with a classic, old-school illustrative approach. "
           "Please make sure that the image does not contain any letters or words."
       )
       image_url = generate_image(image_prompt)

       # Download the image to a temporary file
       image_path = download_image(image_url)

       # Generate an image description using GPT-4o's vision capabilities
       image_description = describe_image_vision(image_path)
       if image_description.startswith("Error:"):
           logger.warning(f"Failed to generate image description: {image_description}")
           image_description = "An image of a caveman named Thorak in a humorous situation."

       # Select a random unused quote
       while True:
           random_index = random.randint(0, len(quotes) - 1)
           if random_index not in used_quotes:
               selected_quote = quotes[random_index]['Quote']
               break

       # Generate the social media caption using OpenAI
       caption = generate_social_media_caption(image_description, selected_quote)

       # Generate hashtags
       hashtags = generate_hashtags(caption)

       # Format the post with "Thorak Thought##"
       formatted_caption = format_post(caption, hashtags)

       # Add the quote to the used quotes list
       used_quotes.add(random_index)

       # Create the video with temporary audio and video files
       video_path, temp_audio_path, final_audio_path, temp_music_path = create_video_with_center_image_and_music(
           image_path, caption, logo_end_screen_path
       )

       # Upload the final video to your server via SFTP
       remote_video_filename = f"social_product_posting_{uuid.uuid4().hex}.mp4"
       remote_video_path = f"/home/runcloud/webapps/cavesupplies-production/videos/{remote_video_filename}"
       upload_file_via_sftp(video_path, remote_video_path, sftp_host, sftp_username, sftp_password)

       # Use the hosted video URL for posting
       hosted_video_url = f"https://cavesupplies.com/videos/{remote_video_filename}"

       # Shorten the hosted URL using Bitly
       short_video_url = shorten_url(hosted_video_url)

       # Post to all platforms and cleanup remote video
       facebook_success, instagram_success, twitter_success, tiktok_success = post_to_all_platforms_with_cleanup(
           video_path, 
           formatted_caption, 
           caption, 
           short_video_url, 
           remote_video_path, 
           sftp_host, 
           sftp_username, 
           sftp_password, 
           page_id, 
           FB_ACCESS_TOKEN
       )

   except ValueError as ve:
       logger.error(f"Validation error: {ve}")
   except Exception as e:
       logger.error(f"Failed to generate or post content: {str(e)}")
       logger.error(f"Error details: {type(e).__name__}, {str(e)}")
       logger.error(f"Traceback: {traceback.format_exc()}")

   finally:
       # Clean up temporary files
       for temp_file in [image_path, temp_audio_path, final_audio_path, temp_music_path, video_path]:
           if temp_file and os.path.exists(temp_file):
               try:
                   os.remove(temp_file)
                   logger.info(f"Temporary file deleted: {temp_file}")
               except Exception as e:
                   logger.error(f"Failed to delete temporary file {temp_file}: {str(e)}")

       # Generate email summary and send notification
       subject, body = generate_email_summary(facebook_success, instagram_success, twitter_success, tiktok_success)
       send_email(subject, body)

       total_time = time.time() - start_time
       logger.debug(f"Total execution time: {total_time:.2f} seconds")
       print(f"Total execution time: {total_time:.2f} seconds")

       print(f"Script execution completed. Please check {log_file_path} for detailed logs.")
