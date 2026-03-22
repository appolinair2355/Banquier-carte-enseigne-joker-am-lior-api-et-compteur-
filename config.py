# config.py
"""
Configuration BACCARAT AI 🤖
"""

import os

def parse_channel_id(env_var: str, default: str) -> int:
    """Parse l'ID de canal Telegram."""
    value = os.getenv(env_var) or default
    try:
        channel_id = int(value)
        if channel_id > 0 and len(str(channel_id)) >= 10:
            channel_id = -channel_id
        return channel_id
    except:
        return int(default)

# Canal de prédiction uniquement
PREDICTION_CHANNEL_ID = parse_channel_id('PREDICTION_CHANNEL_ID', '-1002935867322')

# Authentification
ADMIN_ID = int(os.getenv('ADMIN_ID') or '0')
API_ID = int(os.getenv('API_ID') or '0')
API_HASH = os.getenv('API_HASH') or ''
BOT_TOKEN = os.getenv('BOT_TOKEN') or ''
TELEGRAM_SESSION = os.getenv('TELEGRAM_SESSION', '')

# Admins supplémentaires (IDs fixes + variable d'env optionnelle)
_extra_admins_env = os.getenv('EXTRA_ADMIN_IDS', '')
_extra_admins = [int(x.strip()) for x in _extra_admins_env.split(',') if x.strip().isdigit()]
EXTRA_ADMIN_IDS: list = [1190237801, 1309049556] + _extra_admins

def is_admin(user_id: int) -> bool:
    """Retourne True si l'utilisateur est admin principal ou admin supplémentaire."""
    if ADMIN_ID != 0 and user_id == ADMIN_ID:
        return True
    if user_id in EXTRA_ADMIN_IDS:
        return True
    return False

# Serveur — Render.com injecte automatiquement $PORT=10000
PORT = int(os.getenv('PORT') or '10000')

# Polling API (secondes entre chaque appel)
API_POLL_INTERVAL = int(os.getenv('API_POLL_INTERVAL') or '5')

# Compteur2 - BP = seuil de différence entre inverses pour déclencher une prédiction
COMPTEUR2_ACTIVE = os.getenv('COMPTEUR2_ACTIVE', 'true').lower() == 'true'
COMPTEUR2_BP = int(os.getenv('COMPTEUR2_BP') or os.getenv('COMPTEUR2_B') or '7')

# FK = nombre maximum de prédictions consécutives du même costume autorisées
COMPTEUR2_FK = int(os.getenv('COMPTEUR2_FK') or '3')

# Nombre maximum de rattrapages (vérification jusqu'à jeu prédit + MAX_RATTRAPAGE)
MAX_RATTRAPAGE = int(os.getenv('MAX_RATTRAPAGE') or '3')

# Seuils d'écart pour la détection de "faux chiffres"
# Écart > MAX_GAP_VALID  → exclu des statistiques du rapport détaillé
# Écart > MAX_GAP_SPECIAL → marqué FAUX CHIFFRE dans le rapport spécial / PDF
MAX_GAP_VALID   = int(os.getenv('MAX_GAP_VALID')   or '50')
MAX_GAP_SPECIAL = int(os.getenv('MAX_GAP_SPECIAL') or '150')

# Couleurs (costumes du joueur)
ALL_SUITS = ['♠', '♥', '♦', '♣']

SUIT_DISPLAY = {
    '♠': '♠️',
    '♥': '❤️',
    '♦': '♦️',
    '♣': '♣️'
}

# Inverse des couleurs (pour les prédictions Compteur2)
SUIT_INVERSE = {
    '♠': '♦',
    '♦': '♠',
    '♥': '♣',
    '♣': '♥',
}

# Paires inverses (pour éviter de traiter deux fois la même paire)
INVERSE_PAIRS = [('♠', '♦'), ('♥', '♣')]
