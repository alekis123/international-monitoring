"""
Run ONCE on your own computer to let the monitor read Telegram channels.
1. Get api_id and api_hash at https://my.telegram.org -> API development tools
2. pip install telethon
3. python gen_session.py  (log in with your phone number + code Telegram sends you)
4. Copy the printed string into the TG_SESSION secret. Treat it like a password.
A spare Telegram account is safer than your personal one.
"""
from telethon.sessions import StringSession
from telethon.sync import TelegramClient

api_id = int(input("api_id: "))
api_hash = input("api_hash: ")
with TelegramClient(StringSession(), api_id, api_hash) as client:
    print("\nTG_SESSION =\n" + client.session.save())
