import asyncio
import logging
import sys
from typing import List, Optional, Dict
from datetime import datetime, timedelta
from telethon import TelegramClient, events
from telethon.sessions import StringSession
from telethon.errors import ChatWriteForbiddenError, UserBannedInChannelError
from aiohttp import web

from config import (
    API_ID, API_HASH, BOT_TOKEN, ADMIN_ID, TELEGRAM_SESSION,
    PREDICTION_CHANNEL_ID, PORT, API_POLL_INTERVAL,
    ALL_SUITS, SUIT_DISPLAY, SUIT_INVERSE, INVERSE_PAIRS,
    COMPTEUR2_ACTIVE, COMPTEUR2_BP, COMPTEUR2_FK, MAX_RATTRAPAGE,
    MAX_GAP_VALID, MAX_GAP_SPECIAL,
    EXTRA_ADMIN_IDS, is_admin
)
from utils import get_latest_results

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[logging.StreamHandler(sys.stdout)]
)
logger = logging.getLogger(__name__)

if not API_ID or API_ID == 0:
    logger.error("API_ID manquant")
    exit(1)
if not API_HASH:
    logger.error("API_HASH manquant")
    exit(1)
if not BOT_TOKEN:
    logger.error("BOT_TOKEN manquant")
    exit(1)

# ============================================================================
# VARIABLES GLOBALES
# ============================================================================

client = None
prediction_channel_ok = False
current_game_number = 0
last_prediction_time: Optional[datetime] = None

# Prédictions en attente de vérification {game_number: {...}}
pending_predictions: Dict[int, dict] = {}

# Compteur2 - comptage des apparitions par costume chez le banquier
# Reset automatique à chaque heure pile
compteur2_active = COMPTEUR2_ACTIVE
compteur2_bp = COMPTEUR2_BP
compteur2_fk = COMPTEUR2_FK          # Max prédictions consécutives du même costume
compteur2_counts: Dict[str, int] = {suit: 0 for suit in ALL_SUITS}
compteur2_last_game = 0
compteur2_processed_games: set = set()
compteur2_last_reset: Optional[datetime] = None

# Historique des prédictions
prediction_history: List[Dict] = []
MAX_HISTORY_SIZE = 100

# Jeux pour lesquels la main du joueur a déjà été traitée (compteur2)
player_processed_games: set = set()

# Cache des derniers résultats API {game_number: result_dict}
api_results_cache: Dict[int, dict] = {}

# Dernier numéro de jeu pour lequel une prédiction a été envoyée
last_prediction_game: int = 0

# Jeux pour lesquels la prédiction a déjà été déclenchée (dès que joueur a fini de tirer)
player_prediction_triggered: set = set()

# Pour éviter de déclencher le reset plusieurs fois pour la partie 1440
reset_done_for_cycle: bool = False

# Compteur de prédictions (N dans le message joueur#N:game)
prediction_counter: int = 0

# ── Compteur instantané (DM aux admins, édité en temps réel) ──────────────────
counter_dm_message_ids: Dict[int, int] = {}   # {admin_id: message_id}

# ── Suivi des écarts (gap tracker) ───────────────────────────────────────────
# Pour chaque costume: écart courant (parties sans apparition), historique, max
gap_tracker: Dict[str, Dict] = {
    suit: {
        'current_gap': 0,        # parties consécutives sans ce costume
        'last_seen_game': 0,     # dernier jeu où ce costume est apparu
        'historical_gaps': [],   # liste des écarts passés (une fois le costume réapparu)
        'max_gap': 0,            # plus grand écart jamais enregistré
        'total_appearances': 0,  # total apparitions depuis démarrage
    }
    for suit in ALL_SUITS
}
gap_games_processed: int = 0     # nombre total de parties analysées
# MAX_GAP_VALID et MAX_GAP_SPECIAL sont importés depuis config.py

# ── Rapport Spécial — tracker par catégorie ───────────────────────────────────
# Catégories: victoires, pair/impair, nombre de cartes, combinaisons
SPECIAL_CATEGORIES = [
    'joueur', 'banquier', 'tie',
    'pair', 'impair',
    'pair_b', 'impair_b',
    '2k', '3k',
    '3_2', '3_3', '2_3', '2_2',
]
special_tracker: Dict[str, Dict] = {
    cat: {
        'current_gap': 0,
        'historical_gaps': [],
        'gap_history_with_games': [],  # liste de (gap_size, game_number_qui_a_clos_lecart)
        'max_gap': 0,
        'total_appearances': 0,
    }
    for cat in SPECIAL_CATEGORIES
}
special_games_processed: int = 0  # parties complètes traitées par le tracker spécial

# Suivi des heures de jeu (game_number → datetime de traitement)
game_timestamps: Dict[int, datetime] = {}
cycle_start_time: Optional[datetime] = None   # horodatage du premier jeu du cycle
cycle_first_game: int = 0
cycle_last_game: int = 0

# ── Rapport automatique ───────────────────────────────────────────────────────
rapport_interval: int = 0                        # minutes entre rapports (0 = désactivé)
last_rapport_time: Optional[datetime] = None     # horodatage du dernier rapport envoyé

# ============================================================================
# UTILITAIRES - Costumes
# ============================================================================

def get_local_time() -> datetime:
    """Retourne l'heure locale Bénin/Cameroun (UTC+1 = WAT)."""
    return datetime.utcnow() + timedelta(hours=1)

def normalize_suit(suit_emoji: str) -> str:
    """Convertit un costume emoji (♠️) en costume simple (♠)."""
    return suit_emoji.replace('\ufe0f', '').replace('❤', '♥')

def player_suits_from_cards(player_cards: list) -> List[str]:
    """Extrait la liste des costumes uniques des cartes du joueur."""
    suits = set()
    for card in player_cards:
        raw = card.get('S', '')
        normalized = normalize_suit(raw)
        if normalized in ALL_SUITS:
            suits.add(normalized)
    return list(suits)

def count_suits_from_cards(player_cards: list) -> Dict[str, int]:
    """Compte toutes les occurrences de chaque costume dans les cartes du joueur.
    Ex: [♠️, ♠️, ♦️] → {♠: 2, ♦: 1, ♥: 0, ♣: 0}
    """
    counts = {suit: 0 for suit in ALL_SUITS}
    for card in player_cards:
        raw = card.get('S', '')
        normalized = normalize_suit(raw)
        if normalized in ALL_SUITS:
            counts[normalized] += 1
    return counts

def has_player_cards(result: dict) -> bool:
    """Retourne True si le joueur a au moins 2 cartes (main prête)."""
    return len(result.get('player_cards', [])) >= 2


def baccarat_value(raw_rank) -> int:
    """Valeur baccarat d'une carte (A=1, 2-9=face, 10/J/Q/K=0)."""
    try:
        r = int(raw_rank)
        return r if 1 <= r <= 9 else 0
    except (ValueError, TypeError):
        return 0


def _update_special_cat(cat: str, active: bool, game_number: int = 0):
    """Met à jour le tracker d'écart pour une catégorie spéciale.
    Enregistre (gap_size, game_number) quand un écart se clôture.
    """
    info = special_tracker[cat]
    if active:
        if info['current_gap'] > 0:
            gap = info['current_gap']
            info['historical_gaps'].append(gap)
            info['gap_history_with_games'].append((gap, game_number))
            if gap > info['max_gap']:
                info['max_gap'] = gap
        info['current_gap'] = 0
        info['total_appearances'] += 1
    else:
        info['current_gap'] += 1


def update_special_tracker(result: dict):
    """Met à jour le tracker spécial après chaque partie complète terminée."""
    global special_games_processed

    player_cards = result.get('player_cards', [])
    banker_cards = result.get('banker_cards', [])
    winner       = result.get('winner')
    game_number  = result.get('game_number', 0)

    # Partie complète : au moins 2 cartes chaque côté et un gagnant
    if len(player_cards) < 2 or len(banker_cards) < 2 or winner is None:
        return

    special_games_processed += 1
    np = len(player_cards)
    nb = len(banker_cards)

    # 1. Victoires
    _update_special_cat('joueur',   winner == 'Player',  game_number)
    _update_special_cat('banquier', winner == 'Banker',  game_number)
    _update_special_cat('tie',      winner == 'Tie',     game_number)

    # 2. Pair / Impair (total baccarat du joueur)
    player_total = sum(baccarat_value(c.get('R', 0)) for c in player_cards) % 10
    _update_special_cat('pair',   player_total % 2 == 0, game_number)
    _update_special_cat('impair', player_total % 2 != 0, game_number)

    # 2b. Pair / Impair (total baccarat du banquier)
    banker_total = sum(baccarat_value(c.get('R', 0)) for c in banker_cards) % 10
    _update_special_cat('pair_b',   banker_total % 2 == 0, game_number)
    _update_special_cat('impair_b', banker_total % 2 != 0, game_number)

    # 3. Nombre de cartes du joueur
    _update_special_cat('2k', np == 2, game_number)
    _update_special_cat('3k', np == 3, game_number)

    # 4. Combinaisons joueur/banquier
    _update_special_cat('3_2', np == 3 and nb == 2, game_number)
    _update_special_cat('3_3', np == 3 and nb == 3, game_number)
    _update_special_cat('2_3', np == 2 and nb == 3, game_number)
    _update_special_cat('2_2', np == 2 and nb == 2, game_number)

def is_prediction_time_allowed() -> bool:
    """Retourne True uniquement si on est entre H:00 et H:29.
    Les prédictions sont bloquées de H:30 à H:59."""
    return datetime.now().minute < 30

def count_consecutive_same_suit(suit: str) -> int:
    """Compte le nombre de prédictions consécutives les plus récentes ayant le même costume.
    Parcourt l'historique (du plus récent au plus ancien) et compte tant que le costume correspond."""
    count = 0
    for pred in prediction_history:
        if pred['suit'] == suit:
            count += 1
        else:
            break
    return count

# ============================================================================
# UTILITAIRES - Canaux
# ============================================================================

def normalize_channel_id(channel_id) -> Optional[int]:
    if not channel_id:
        return None
    s = str(channel_id)
    if s.startswith('-100'):
        return int(s)
    if s.startswith('-'):
        return int(s)
    return int(f"-100{s}")

async def resolve_channel(entity_id):
    try:
        if not entity_id:
            return None
        normalized = normalize_channel_id(entity_id)
        entity = await client.get_entity(normalized)
        return entity
    except Exception as e:
        logger.error(f"❌ Impossible de résoudre le canal {entity_id}: {e}")
        return None

# ============================================================================
# COMPTEUR INSTANTANÉ — message live dans le canal
# ============================================================================

def build_counter_message() -> str:
    """Construit le texte du message compteur instantané (heure WAT Bénin/Cameroun)."""
    now_wat = get_local_time()
    reset_str = (compteur2_last_reset + timedelta(hours=1)).strftime('%H:%M') if compteur2_last_reset else now_wat.strftime('%H:%M')
    next_reset = (now_wat + timedelta(hours=1)).replace(minute=0, second=0, microsecond=0)
    return (
        f"📈 **Compteur banquier**\n"
        f"♠️ : {compteur2_counts.get('♠', 0)}\n"
        f"♥️ : {compteur2_counts.get('♥', 0)}\n"
        f"♦️ : {compteur2_counts.get('♦', 0)}\n"
        f"♣️ : {compteur2_counts.get('♣', 0)}\n\n"
        f"🕐 Reset effectué: {reset_str} WAT\n"
        f"⏭ Prochain reset: {next_reset.strftime('%H:%M')} WAT"
    )

async def send_or_update_counter_message(force: bool = False):
    """Gère le message compteur banquier en DM privé pour tous les admins.

    - force=False (après chaque partie banquier) : ÉDITE le message existant.
      Si aucun message n'existe encore, en crée un nouveau.
    - force=True (reset horaire ou reset complet) : envoie toujours un NOUVEAU
      message et réinitialise les IDs stockés.
    - N'envoie jamais dans le canal de prédiction.
    """
    global counter_dm_message_ids

    if not client or not client.is_connected():
        return

    all_admin_ids = []
    if ADMIN_ID and ADMIN_ID != 0:
        all_admin_ids.append(ADMIN_ID)
    for aid in EXTRA_ADMIN_IDS:
        if aid not in all_admin_ids:
            all_admin_ids.append(aid)

    if not all_admin_ids:
        return

    msg = build_counter_message()

    for admin_id in all_admin_ids:
        try:
            if force:
                # Reset → nouveau message, on oublie l'ancien
                sent = await client.send_message(admin_id, msg)
                counter_dm_message_ids[admin_id] = sent.id
                logger.info(f"📈 Nouveau compteur (reset) envoyé en DM à admin {admin_id}")
            else:
                existing_id = counter_dm_message_ids.get(admin_id)
                if existing_id:
                    # Éditer le message existant
                    try:
                        await client.edit_message(admin_id, existing_id, msg)
                        logger.debug(f"📈 Compteur édité en DM pour admin {admin_id}")
                    except Exception:
                        # Message supprimé ou inaccessible → en créer un nouveau
                        sent = await client.send_message(admin_id, msg)
                        counter_dm_message_ids[admin_id] = sent.id
                        logger.info(f"📈 Compteur recréé en DM pour admin {admin_id}")
                else:
                    # Pas encore de message → en créer un
                    sent = await client.send_message(admin_id, msg)
                    counter_dm_message_ids[admin_id] = sent.id
                    logger.info(f"📈 Compteur initial créé en DM pour admin {admin_id}")
        except Exception as e:
            logger.error(f"❌ Erreur compteur DM admin {admin_id}: {e}")

# ============================================================================
# HISTORIQUE DES PRÉDICTIONS
# ============================================================================

def add_prediction_to_history(game_number: int, suit: str, triggered_by_pair: str, counter: int):
    global prediction_history
    # Snapshot des compteurs et de l'écart au moment de la prédiction (pour /raison)
    counts_snapshot = dict(compteur2_counts)
    inv_suit = SUIT_INVERSE.get(triggered_by_pair, '?')
    c1 = counts_snapshot.get(triggered_by_pair, 0)
    c2 = counts_snapshot.get(inv_suit, 0)
    prediction_history.insert(0, {
        'predicted_game': game_number,
        'suit': suit,
        'triggered_by': triggered_by_pair,
        'counter': counter,
        'predicted_at': datetime.now(),
        'status': 'en_cours',
        'result_game': None,
        'counts_snapshot': counts_snapshot,
        'trigger_c1': c1,
        'trigger_c2': c2,
        'trigger_diff': abs(c1 - c2),
    })
    if len(prediction_history) > MAX_HISTORY_SIZE:
        prediction_history = prediction_history[:MAX_HISTORY_SIZE]

def update_prediction_history_status(game_number: int, suit: str, status: str, result_game: int):
    for pred in prediction_history:
        if pred['predicted_game'] == game_number and pred['suit'] == suit:
            pred['status'] = status
            pred['result_game'] = result_game
            break

def update_gap_tracker(game_number: int, player_suits: List[str]):
    """Met à jour le tracker d'écarts après chaque partie terminée."""
    global gap_games_processed
    gap_games_processed += 1
    for suit in ALL_SUITS:
        info = gap_tracker[suit]
        if suit in player_suits:
            # Costume apparu → clore l'écart courant si > 0
            if info['current_gap'] > 0:
                info['historical_gaps'].append(info['current_gap'])
                if len(info['historical_gaps']) > 500:
                    info['historical_gaps'] = info['historical_gaps'][-500:]
                if info['current_gap'] > info['max_gap']:
                    info['max_gap'] = info['current_gap']
                info['current_gap'] = 0
            info['last_seen_game'] = game_number
            info['total_appearances'] += 1
        else:
            # Costume absent → incrémenter l'écart courant
            info['current_gap'] += 1

# ============================================================================
# ENVOI ET MISE À JOUR DES PRÉDICTIONS
# ============================================================================

NUMBER_EMOJI = {0: "0️⃣", 1: "1️⃣", 2: "2️⃣", 3: "3️⃣", 4: "4️⃣", 5: "5️⃣"}

def build_prediction_message(counter: int, game_number: int, suit: str, rattrapage: int, result: str) -> str:
    """Construit le message de prédiction au format unifié."""
    suit_display = SUIT_DISPLAY.get(suit, suit)
    return (
        f"🎮 banquier №{game_number}\n"
        f"⚜️ Couleur de la carte:{suit_display}\n"
        f"🎰 Poursuite  🔰+{MAX_RATTRAPAGE} jeux\n"
        f"🗯️ Résultats : {result}"
    )

async def send_prediction(game_number: int, suit: str, triggered_by_suit: str) -> Optional[int]:
    """Envoie une prédiction au canal."""
    global last_prediction_time, last_prediction_game, prediction_counter

    if not PREDICTION_CHANNEL_ID:
        logger.error("❌ PREDICTION_CHANNEL_ID non configuré")
        return None

    prediction_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
    if not prediction_entity:
        logger.error(f"❌ Canal prédiction inaccessible: {PREDICTION_CHANNEL_ID}")
        return None

    prediction_counter += 1
    msg = build_prediction_message(prediction_counter, game_number, suit, 0, "en cours ⌛")

    try:
        sent = await client.send_message(prediction_entity, msg)
        last_prediction_time = datetime.now()
        last_prediction_game = game_number

        pending_predictions[game_number] = {
            'suit': suit,
            'triggered_by': triggered_by_suit,
            'message_id': sent.id,
            'status': 'en_cours',
            'awaiting_rattrapage': 0,
            'sent_time': datetime.now(),
            'counter': prediction_counter,
        }

        add_prediction_to_history(game_number, suit, triggered_by_suit, prediction_counter)

        logger.info(f"✅ Prédiction #{prediction_counter} envoyée: jeu {game_number} → {suit} (écart BP via {triggered_by_suit}↔{SUIT_INVERSE.get(triggered_by_suit, '?')})")
        return sent.id

    except ChatWriteForbiddenError:
        logger.error(f"❌ Pas la permission d'écrire dans le canal {PREDICTION_CHANNEL_ID}")
        prediction_counter -= 1
        return None
    except UserBannedInChannelError:
        logger.error(f"❌ Bot banni du canal {PREDICTION_CHANNEL_ID}")
        prediction_counter -= 1
        return None
    except Exception as e:
        logger.error(f"❌ Erreur envoi prédiction: {e}")
        prediction_counter -= 1
        return None

async def update_prediction_message(game_number: int, status: str, trouve: bool, rattrapage: int = 0):
    """Met à jour le message de prédiction avec le résultat."""
    if game_number not in pending_predictions:
        return

    pred = pending_predictions[game_number]
    suit = pred['suit']
    msg_id = pred['message_id']
    counter = pred['counter']

    num_emoji = NUMBER_EMOJI.get(rattrapage, str(rattrapage))
    if trouve:
        result_line = f"✅{num_emoji}GAGNÉ"
    else:
        result_line = "❌PERDU"

    new_msg = build_prediction_message(counter, game_number, suit, rattrapage, result_line)

    try:
        prediction_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
        if not prediction_entity:
            logger.error("❌ Canal prédiction inaccessible pour mise à jour")
            return

        await client.edit_message(prediction_entity, msg_id, new_msg)
        pred['status'] = status

        status_key = 'gagne' if trouve else 'perdu'
        update_prediction_history_status(game_number, suit, status_key, game_number)

        if trouve:
            logger.info(f"✅ Gagné: jeu #{game_number} {suit} (rattrapage {rattrapage})")
        else:
            logger.info(f"❌ Perdu: jeu #{game_number} {suit}")

        del pending_predictions[game_number]

    except Exception as e:
        logger.error(f"❌ Erreur update message: {e}")

# ============================================================================
# VÉRIFICATION DYNAMIQUE (dès que les cartes du joueur apparaissent)
# ============================================================================

async def check_prediction_result_dynamic(game_number: int, banker_suits: List[str], is_finished: bool):
    """Vérification dynamique des prédictions.

    Règles :
    - Si le costume prédit apparaît dans les cartes du banquier → gagné immédiatement
      (dès que is_finished=True et les cartes du banquier sont disponibles).
    - Si pas trouvé ET partie terminée (is_finished) → avancer rattrapage.
    - Si pas trouvé ET partie encore en cours → ne rien faire, attendre le prochain poll.
    """

    # --- Vérification directe (jeu prédit = jeu en cours) ---
    if game_number in pending_predictions:
        pred = pending_predictions[game_number]
        if pred.get('awaiting_rattrapage', 0) == 0:
            target_suit = pred['suit']
            status_flag = pred.get('check_done_direct', False)
            if status_flag:
                return

            if target_suit in banker_suits:
                logger.info(f"🔍 [DYN] #{game_number}: {target_suit} ✅ trouvé chez banquier")
                await update_prediction_message(game_number, '✅', True, 0)
            elif is_finished:
                pred['awaiting_rattrapage'] = 1
                logger.info(f"🔍 [DYN] #{game_number}: {target_suit} ❌ absent → rattrapage #{game_number + 1}")
            else:
                logger.debug(f"🔍 [DYN] #{game_number}: partie en cours, costume banquier pas encore visible - attente")
            return

    # --- Vérification rattrapages ---
    for original_game, pred in list(pending_predictions.items()):
        awaiting = pred.get('awaiting_rattrapage', 0)
        if awaiting <= 0:
            continue
        if game_number != original_game + awaiting:
            continue

        target_suit = pred['suit']

        if target_suit in banker_suits:
            logger.info(f"🔍 [DYN] R{awaiting} #{game_number}: {target_suit} ✅ trouvé chez banquier")
            await update_prediction_message(original_game, '✅', True, awaiting)
        elif is_finished:
            if awaiting < MAX_RATTRAPAGE:
                pred['awaiting_rattrapage'] = awaiting + 1
                logger.info(f"🔍 [DYN] R{awaiting} #{game_number}: {target_suit} ❌ absent → R{awaiting+1} #{original_game + awaiting + 1}")
            else:
                logger.info(f"🔍 [DYN] R{awaiting} #{game_number}: {target_suit} ❌ → perdu (max R{MAX_RATTRAPAGE} atteint)")
                await update_prediction_message(original_game, '❌', False, awaiting)
        else:
            logger.debug(f"🔍 [DYN] R{awaiting} #{game_number}: partie en cours - attente")
        return

# ============================================================================
# COMPTEUR2 - Logique principale (comptage costumes du banquier)
# ============================================================================

def get_compteur2_status_text() -> str:
    status = "✅ ON" if compteur2_active else "❌ OFF"
    last_game_str = f"#{compteur2_last_game}" if compteur2_last_game else "Aucun"
    reset_str = compteur2_last_reset.strftime('%H:%M:%S') if compteur2_last_reset else "Aucun"
    now = datetime.now()
    time_ok = now.minute < 30
    time_status = f"✅ H:00-H:29 ({now.strftime('%H:%M')})" if time_ok else f"🚫 BLOQUÉ H:30-H:59 ({now.strftime('%H:%M')})"

    lines = [
        f"📊 Compteur2: {status} | BP={compteur2_bp} | FK={compteur2_fk} | R.max={MAX_RATTRAPAGE}",
        f"🕐 Fenêtre prédiction: {time_status}",
        f"🎮 Dernier jeu traité: {last_game_str}",
        f"🎯 Dernière prédiction: #{last_prediction_game}" if last_prediction_game else "🎯 Dernière prédiction: Aucune",
        f"🔄 Dernier reset horaire: {reset_str}",
        "",
        "Comptage costumes banquier (depuis dernier reset horaire):",
    ]

    for suit in ALL_SUITS:
        count = compteur2_counts.get(suit, 0)
        display = SUIT_DISPLAY.get(suit, suit)
        consec = count_consecutive_same_suit(suit)
        fk_warn = f" ⚠️ FK atteint ({consec}/{compteur2_fk})" if consec >= compteur2_fk else f" ({consec}/{compteur2_fk} consécutif)"
        lines.append(f"{display} : {count} apparition(s){fk_warn}")

    lines.append("")
    lines.append("Différences entre paires inverses:")
    for s1, s2 in INVERSE_PAIRS:
        d1 = SUIT_DISPLAY.get(s1, s1)
        d2 = SUIT_DISPLAY.get(s2, s2)
        c1 = compteur2_counts.get(s1, 0)
        c2 = compteur2_counts.get(s2, 0)
        diff = abs(c1 - c2)
        flag = " ⚡ SEUIL ATTEINT!" if diff >= compteur2_bp else ""
        lines.append(f"{d1}({c1}) vs {d2}({c2}) → diff={diff}/{compteur2_bp}{flag}")

    return "\n".join(lines)

async def process_compteur2(game_number: int, player_suits: List[str], player_cards: list):
    """Traite le Compteur2 après que la partie du banquier est terminée (is_finished=True).

    Nouvelle logique :
    - Compte toutes les apparitions de chaque costume dans les cartes du banquier
      (ex: ♠️♠️ = +2 pour ♠)
    - Pour chaque paire inverse (♠/♦ et ♥/♣), si la différence de comptage >= BP :
      → Prédire le costume le moins vu pour le prochain jeu (banquier)
    - Reset automatique du compteur à chaque heure pile (géré par hourly_reset_task)
    """
    global compteur2_counts, compteur2_last_game, compteur2_processed_games
    global game_timestamps, cycle_start_time, cycle_first_game, cycle_last_game

    if not compteur2_active:
        return

    if game_number in compteur2_processed_games:
        return

    compteur2_processed_games.add(game_number)
    if len(compteur2_processed_games) > 200:
        oldest = min(compteur2_processed_games)
        compteur2_processed_games.discard(oldest)

    compteur2_last_game = game_number

    # Enregistrer l'horodatage de ce jeu (heure locale WAT)
    now_ts = get_local_time()
    game_timestamps[game_number] = now_ts
    if len(game_timestamps) > 1500:
        oldest_k = min(game_timestamps.keys())
        del game_timestamps[oldest_k]

    # Premier jeu du cycle
    if cycle_start_time is None or game_number < cycle_first_game or cycle_first_game == 0:
        cycle_start_time = now_ts
        cycle_first_game = game_number
    cycle_last_game = game_number

    # --- Compter TOUTES les occurrences de chaque costume dans les cartes ---
    game_counts = count_suits_from_cards(player_cards)
    for suit in ALL_SUITS:
        if game_counts[suit] > 0:
            compteur2_counts[suit] += game_counts[suit]
            logger.info(
                f"📊 Compteur2 jeu #{game_number}: {SUIT_DISPLAY.get(suit, suit)} "
                f"+{game_counts[suit]} → total {compteur2_counts[suit]}"
            )

    logger.info(
        f"📊 Compteur2 #{game_number} | "
        + " | ".join(
            f"{SUIT_DISPLAY.get(s, s)}={compteur2_counts[s]}"
            for s in ALL_SUITS
        )
    )

    # --- Mettre à jour les écarts (gap tracker) ---
    update_gap_tracker(game_number, player_suits)

    # --- Éditer le message compteur en DM chez les admins ---
    await send_or_update_counter_message()

    # --- Vérifier chaque paire inverse pour le seuil BP ---
    for suit_a, suit_b in INVERSE_PAIRS:
        count_a = compteur2_counts[suit_a]
        count_b = compteur2_counts[suit_b]
        diff = abs(count_a - count_b)

        if diff < compteur2_bp:
            continue

        # Le costume le plus vu → prédire l'inverse (le moins vu)
        if count_a > count_b:
            predict_suit = suit_b
            trigger_suit = suit_a
        else:
            predict_suit = suit_a
            trigger_suit = suit_b

        pred_game = game_number + 1

        logger.info(
            f"🔮 Compteur2: paire {SUIT_DISPLAY.get(suit_a, suit_a)}/{SUIT_DISPLAY.get(suit_b, suit_b)} "
            f"diff={diff} >= BP={compteur2_bp} → prédit {SUIT_DISPLAY.get(predict_suit, predict_suit)} jeu #{pred_game}"
        )

        # ── Règle 0 : Jeu prédit déjà apparu dans l'API → trop tard ────
        if pred_game in api_results_cache:
            logger.info(
                f"⏸ Prédiction #{pred_game} {SUIT_DISPLAY.get(predict_suit, predict_suit)} ignorée: "
                f"jeu #{pred_game} déjà commencé dans l'API"
            )
            continue

        # ── Règle 1 : Restriction horaire H:00-H:29 uniquement ──────────
        if not is_prediction_time_allowed():
            now_t = datetime.now()
            logger.info(
                f"🚫 Prédiction #{pred_game} {predict_suit} ignorée: "
                f"hors fenêtre horaire ({now_t.strftime('%H:%M')} — prédictions bloquées H:30-H:59)"
            )
            continue

        # ── Règle 2 : FK — limite de prédictions consécutives du même costume
        consec = count_consecutive_same_suit(predict_suit)
        if consec >= compteur2_fk:
            # Exception : si 30+ minutes sans aucune prédiction → débloquer le FK
            trente_min_sans_pred = (
                last_prediction_time is None or
                (datetime.now() - last_prediction_time).total_seconds() >= 1800
            )
            if trente_min_sans_pred:
                logger.info(
                    f"⏰ FK ignoré: 30+ min sans prédiction → {SUIT_DISPLAY.get(predict_suit, predict_suit)} "
                    f"autorisé malgré {consec}/{compteur2_fk} consécutifs"
                )
            else:
                logger.info(
                    f"🚫 Prédiction #{pred_game} {SUIT_DISPLAY.get(predict_suit, predict_suit)} ignorée: "
                    f"FK={compteur2_fk} atteint ({consec} prédictions consécutives du même costume)"
                )
                continue

        # ── Règle 4 : Attendre que toutes les vérifications soient faites ──
        if pending_predictions:
            logger.info(
                f"⏸ Prédiction #{pred_game} {predict_suit} ignorée: "
                f"vérification en cours pour {list(pending_predictions.keys())}"
            )
            continue

        # ── Règle 5 : Écart minimum de 2 entre prédictions ──────────────
        if last_prediction_game > 0 and pred_game < last_prediction_game + 2:
            logger.info(
                f"⏸ Prédiction #{pred_game} {predict_suit} ignorée: "
                f"écart insuffisant (dernier prédit: #{last_prediction_game}, "
                f"écart requis: 2, écart actuel: {pred_game - last_prediction_game})"
            )
            continue

        # ── Règle 6 : Pas de prédiction pour le même numéro deux fois ───
        if pred_game == last_prediction_game:
            logger.info(
                f"⏸ Prédiction #{pred_game} {predict_suit} ignorée: "
                f"jeu #{pred_game} déjà prédit"
            )
            continue

        await send_prediction(pred_game, predict_suit, trigger_suit)
        # Une seule prédiction par jeu traité (première paire qui déclenche)
        break

# ============================================================================
# RESET HORAIRE AUTOMATIQUE DU COMPTEUR2
# ============================================================================

async def hourly_reset_task():
    """Remet à zéro le Compteur2 à chaque heure pile."""
    global compteur2_counts, compteur2_processed_games, compteur2_last_reset

    while True:
        now = datetime.now()
        next_hour = (now + timedelta(hours=1)).replace(minute=0, second=0, microsecond=0)
        wait_seconds = (next_hour - now).total_seconds()

        logger.info(f"⏰ Prochain reset horaire Compteur2 dans {int(wait_seconds)}s (à {next_hour.strftime('%H:%M:%S')})")
        await asyncio.sleep(wait_seconds)

        compteur2_counts = {suit: 0 for suit in ALL_SUITS}
        compteur2_processed_games = set()
        compteur2_last_reset = datetime.now()

        logger.info(f"⏰ Reset horaire Compteur2 effectué à {compteur2_last_reset.strftime('%H:%M:%S')}")

        # Mettre à jour le message compteur live avec les valeurs remises à zéro
        # force=True pour ignorer le throttle et afficher immédiatement le reset
        await send_or_update_counter_message(force=True)

# ============================================================================
# BOUCLE DE POLLING API - DYNAMIQUE
# ============================================================================

def _player_drawing_done(player_cards: list) -> bool:
    """Retourne True dès que le joueur a terminé de tirer ses cartes.

    Règles Baccarat :
    - 3 cartes → toujours terminé.
    - 2 cartes et total baccarat >= 6 (6,7,8,9) → joueur reste (pas de 3ème carte).
    - 2 cartes et total < 6 (0-5) → joueur va tirer une 3ème carte → pas encore fini.
    """
    n = len(player_cards)
    if n >= 3:
        return True
    if n == 2:
        total = sum(baccarat_value(c.get('R', 0)) for c in player_cards) % 10
        return total >= 6
    return False


async def api_polling_loop():
    """Interroge l'API 1xBet en continu.

    Comportement :
    - Vérification dynamique : dès que les cartes du banquier sont disponibles et la partie terminée.
    - Compteur2 + Prédiction : déclenché dès que la partie est terminée (is_finished=True)
      et que le banquier a ses cartes.
    - Tracker spécial : déclenché quand la partie est entièrement terminée (is_finished=True).
    - Reset automatique : déclenché quand la partie #1440 est terminée.
    """
    global current_game_number, api_results_cache, player_processed_games
    global reset_done_for_cycle, player_prediction_triggered

    loop = asyncio.get_event_loop()
    logger.info(f"🔄 Polling API dynamique démarré (intervalle: {API_POLL_INTERVAL}s)")

    while True:
        try:
            results = await loop.run_in_executor(None, get_latest_results)

            if results:
                for result in results:
                    game_number = result["game_number"]
                    is_finished = result["is_finished"]
                    player_cards = result.get("player_cards", [])
                    banker_cards = result.get("banker_cards", [])

                    # Mettre à jour le cache
                    api_results_cache[game_number] = result

                    # Extraire costumes banquier (uniques, pour la vérification et le compteur)
                    banker_suits = player_suits_from_cards(banker_cards)
                    ready = len(banker_cards) >= 2

                    if not ready:
                        continue

                    current_game_number = game_number

                    b_display = " ".join(SUIT_DISPLAY.get(s, s) for s in banker_suits) or "—"

                    # ── 1. VÉRIFICATION DYNAMIQUE ──────────────────────────────
                    # Dès que les cartes du banquier sont disponibles
                    await check_prediction_result_dynamic(game_number, banker_suits, is_finished)

                    # ── 2. COMPTEUR2 + PRÉDICTION ─────────────────────────────
                    # Déclenché quand la partie est terminée (banquier a fini de tirer)
                    drawing_done = is_finished
                    if game_number not in player_prediction_triggered and drawing_done:
                        player_prediction_triggered.add(game_number)
                        if len(player_prediction_triggered) > 500:
                            oldest = min(player_prediction_triggered)
                            player_prediction_triggered.discard(oldest)

                        logger.info(
                            f"🃏 Banquier #{game_number} FINI de tirer | Main: {b_display} "
                            f"| is_finished={is_finished}"
                        )
                        # Compter les costumes banquier et déclencher la prédiction du JEU SUIVANT
                        await process_compteur2(game_number, banker_suits, banker_cards)

                        # ── ENVOI ET RESET AUTOMATIQUE — PARTIE #1440 ───────────
                        # Dès que le JOUEUR a terminé de tirer ses cartes sur la partie #1440,
                        # on envoie les rapports et on repart sur un nouveau cycle.
                        if game_number == 1440 and not reset_done_for_cycle:
                            reset_done_for_cycle = True
                            logger.info("🔔 Partie #1440 côté joueur terminée — envoi rapports automatiques")

                            # Tenter d'inclure #1440 dans le tracker spécial si résultat disponible
                            if (result.get('winner') is not None
                                    and len(result.get('banker_cards', [])) >= 2
                                    and game_number not in player_processed_games):
                                player_processed_games.add(game_number)
                                update_special_tracker(result)
                                logger.info("📊 Tracker spécial #1440 mis à jour avant rapport")

                            # ── Rapport journalier détaillé ──────────────────────
                            try:
                                daily_msg = build_daily_rapport_1440()
                                await send_rapport_to_admins(daily_msg)
                                logger.info("📅 Rapport journalier #1440 envoyé aux admins")
                            except Exception as e:
                                logger.error(f"❌ Erreur rapport journalier #1440: {e}")

                            # ── Rapport spécial PDF ──────────────────────────────
                            try:
                                await send_special_pdf_to_admins()
                                logger.info("📄 Rapport spécial PDF #1440 envoyé aux admins")
                            except Exception as e:
                                logger.error(f"❌ Erreur rapport spécial PDF #1440: {e}")

                            # ── Reset complet APRÈS l'envoi ──────────────────────
                            await perform_full_reset("Reset automatique (partie #1440 joueur terminée)")

                    # ── TRACKER SPÉCIAL ─────────────────────────────────────────
                    # Nécessite banker_cards + winner → attend que la partie soit entièrement terminée.
                    # (Pour #1440 : déjà traité ci-dessus si données disponibles au bon moment.)
                    if game_number not in player_processed_games and is_finished:
                        player_processed_games.add(game_number)
                        if len(player_processed_games) > 500:
                            oldest = min(player_processed_games)
                            player_processed_games.discard(oldest)

                        logger.info(
                            f"✅ Jeu #{game_number} TERMINÉ | Gagnant: {result.get('winner')}"
                        )
                        update_special_tracker(result)

                    # Remettre à zéro le flag si on repart au début du cycle
                    if game_number < 100 and reset_done_for_cycle:
                        reset_done_for_cycle = False
                        logger.info("🔄 Nouveau cycle détecté (game < 100) → flag reset remis à zéro")

                # Nettoyage du cache (garder 300 derniers)
                if len(api_results_cache) > 300:
                    oldest = min(api_results_cache.keys())
                    del api_results_cache[oldest]

        except Exception as e:
            logger.error(f"❌ Erreur polling API: {e}")
            import traceback
            logger.error(traceback.format_exc())

        await asyncio.sleep(API_POLL_INTERVAL)

# ============================================================================
# RESET COMPLET
# ============================================================================

async def perform_full_reset(reason: str):
    global pending_predictions, last_prediction_time
    global compteur2_counts, compteur2_last_game
    global compteur2_processed_games
    global player_processed_games, player_prediction_triggered, api_results_cache
    global last_prediction_game, reset_done_for_cycle, prediction_counter
    global gap_games_processed, game_timestamps, cycle_start_time, cycle_first_game, cycle_last_game
    global special_games_processed, counter_dm_message_ids

    stats = len(pending_predictions)
    pending_predictions.clear()
    last_prediction_time = None
    last_prediction_game = 0
    compteur2_counts = {suit: 0 for suit in ALL_SUITS}
    compteur2_processed_games = set()
    compteur2_last_game = 0
    player_processed_games = set()
    player_prediction_triggered = set()
    api_results_cache = {}
    prediction_counter = 0
    counter_dm_message_ids = {}   # Forcer un nouveau message compteur au prochain cycle

    # Réinitialiser le gap tracker pour le nouveau cycle
    # On conserve max_gap (record historique global) mais on repart de zéro pour ce cycle
    gap_games_processed = 0
    for suit in ALL_SUITS:
        gap_tracker[suit]['current_gap'] = 0
        gap_tracker[suit]['last_seen_game'] = 0
        gap_tracker[suit]['historical_gaps'] = []
        gap_tracker[suit]['total_appearances'] = 0
        # max_gap est conservé (record global, jamais réinitialisé)

    # Réinitialiser les timestamps du cycle
    game_timestamps.clear()
    cycle_start_time = None
    cycle_first_game = 0
    cycle_last_game = 0

    # Réinitialiser le tracker spécial (max_gap conservé comme record global)
    special_games_processed = 0
    for cat in SPECIAL_CATEGORIES:
        special_tracker[cat]['current_gap'] = 0
        special_tracker[cat]['historical_gaps'] = []
        special_tracker[cat]['gap_history_with_games'] = []
        special_tracker[cat]['total_appearances'] = 0

    logger.info(f"🔄 {reason} - {stats} prédictions cleared")

    # Mettre à jour le message compteur live (canal uniquement — données uniquement)
    await send_or_update_counter_message(force=True)

    # Notifier les admins en privé (JAMAIS dans le canal de prédiction)
    now_str = get_local_time().strftime('%d/%m/%Y %H:%M')
    reset_msg = (
        f"🔄 **RESET SYSTÈME — {now_str} (WAT)**\n\n"
        f"Raison: {reason}\n"
        f"✅ Compteurs remis à zéro\n"
        f"✅ {stats} prédiction(s) effacée(s)\n"
        f"✅ Gap tracker réinitialisé\n\n"
        f"🎲 Baccarat AI — Nouveau cycle démarré"
    )
    all_admin_ids = []
    if ADMIN_ID and ADMIN_ID != 0:
        all_admin_ids.append(ADMIN_ID)
    for aid in EXTRA_ADMIN_IDS:
        if aid not in all_admin_ids:
            all_admin_ids.append(aid)
    for admin_id in all_admin_ids:
        try:
            await client.send_message(admin_id, reset_msg)
        except Exception as e:
            logger.error(f"❌ Notif reset admin {admin_id}: {e}")

# ============================================================================
# COMMANDES ADMIN
# ============================================================================

async def cmd_compteur2(event):
    global compteur2_active, compteur2_bp, compteur2_fk, compteur2_counts, compteur2_last_game
    global compteur2_processed_games, player_processed_games, player_prediction_triggered

    if event.is_group or event.is_channel:
        return
    if not is_admin(event.sender_id):
        await event.respond("🔒 Admin uniquement")
        return

    parts = event.message.message.strip().split()

    if len(parts) == 1 or (len(parts) == 2 and parts[1].lower() == 'status'):
        await event.respond(get_compteur2_status_text())
        return

    arg = parts[1].lower()

    if arg == 'on':
        compteur2_active = True
        compteur2_counts = {suit: 0 for suit in ALL_SUITS}
        compteur2_processed_games = set()
        player_processed_games = set()
        player_prediction_triggered = set()
        await event.respond(
            f"✅ Compteur2 ACTIVÉ | BP={compteur2_bp}\n\n" + get_compteur2_status_text()
        )

    elif arg == 'off':
        compteur2_active = False
        await event.respond("❌ Compteur2 DÉSACTIVÉ")

    elif arg == 'reset':
        compteur2_counts = {suit: 0 for suit in ALL_SUITS}
        compteur2_processed_games = set()
        player_processed_games = set()
        player_prediction_triggered = set()
        compteur2_last_game = 0
        await event.respond("🔄 Compteur2 remis à zéro\n\n" + get_compteur2_status_text())

    elif arg == 'bp':
        if len(parts) < 3:
            await event.respond("Usage: `/compteur2 bp <valeur>` (ex: `/compteur2 bp 7`)")
            return
        try:
            val = int(parts[2])
            if not 1 <= val <= 100:
                await event.respond("❌ BP doit être entre 1 et 100")
                return
            old_bp = compteur2_bp
            compteur2_bp = val
            compteur2_counts = {suit: 0 for suit in ALL_SUITS}
            compteur2_processed_games = set()
            player_processed_games = set()
            player_prediction_triggered = set()
            await event.respond(
                f"✅ Compteur2 BP: {old_bp} → {compteur2_bp} | Compteurs remis à zéro\n\n"
                + get_compteur2_status_text()
            )
        except ValueError:
            await event.respond("❌ Valeur invalide. Usage: `/compteur2 bp 7`")

    elif arg == 'fk':
        if len(parts) < 3:
            await event.respond("Usage: `/compteur2 fk <valeur>` (ex: `/compteur2 fk 3`)")
            return
        try:
            val = int(parts[2])
            if not 1 <= val <= 50:
                await event.respond("❌ FK doit être entre 1 et 50")
                return
            old_fk = compteur2_fk
            compteur2_fk = val
            await event.respond(
                f"✅ Compteur2 FK: {old_fk} → {compteur2_fk}\n"
                f"Maximum {compteur2_fk} prédiction(s) consécutive(s) du même costume.\n\n"
                + get_compteur2_status_text()
            )
        except ValueError:
            await event.respond("❌ Valeur invalide. Usage: `/compteur2 fk 3`")

    else:
        await event.respond(
            "📊 **COMPTEUR2 - Aide**\n\n"
            "`/compteur2` — Afficher l'état\n"
            "`/compteur2 on` — Activer\n"
            "`/compteur2 off` — Désactiver\n"
            "`/compteur2 bp <val>` — Changer le seuil BP (défaut: 7)\n"
            "`/compteur2 fk <val>` — Max prédictions consécutives même costume (défaut: 3)\n"
            "`/compteur2 reset` — Remettre les compteurs à zéro"
        )

async def cmd_history(event):
    if event.is_group or event.is_channel:
        return
    if not is_admin(event.sender_id):
        await event.respond("🔒 Admin uniquement")
        return

    if not prediction_history:
        await event.respond("📜 Aucune prédiction dans l'historique.")
        return

    lines = [
        "📜 **HISTORIQUE DES PRÉDICTIONS**",
        "═══════════════════════════════════════",
        ""
    ]

    for i, pred in enumerate(prediction_history[:20], 1):
        pred_game = pred['predicted_game']
        suit = SUIT_DISPLAY.get(pred['suit'], pred['suit'])
        trig = SUIT_DISPLAY.get(pred['triggered_by'], pred['triggered_by'])
        time_str = pred['predicted_at'].strftime('%H:%M:%S')
        counter = pred.get('counter', '?')

        status = pred['status']
        if status == 'en_cours':
            status_str = "⏳ En cours..."
        elif status == 'gagne':
            status_str = "✅ GAGNÉ"
        elif status == 'perdu':
            status_str = "❌ PERDU"
        else:
            status_str = f"❓ {status}"

        lines.append(
            f"{i}. 🕐 `{time_str}` | **joueur#{counter}:{pred_game}** {suit}\n"
            f"   📉 Déclenché par écart BP sur: {trig}\n"
            f"   📊 Résultat: {status_str}"
        )
        lines.append("")

    if pending_predictions:
        lines.append("**🔮 PRÉDICTIONS ACTIVES:**")
        for num, pred in sorted(pending_predictions.items()):
            suit = SUIT_DISPLAY.get(pred['suit'], pred['suit'])
            ar = pred.get('awaiting_rattrapage', 0)
            st = f"Attente R{ar} (#{num + ar})" if ar > 0 else "Vérification directe"
            lines.append(f"• joueur#{pred['counter']}:{num} {suit}: {st}")
        lines.append("")

    lines.append("═══════════════════════════════════════")
    await event.respond("\n".join(lines))

async def cmd_channels(event):
    if event.is_group or event.is_channel:
        return
    if not is_admin(event.sender_id):
        await event.respond("🔒 Admin uniquement")
        return

    pred_status = "❌"
    pred_name = "Inaccessible"

    try:
        if PREDICTION_CHANNEL_ID:
            pred_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
            if pred_entity:
                pred_status = "✅"
                pred_name = getattr(pred_entity, 'title', 'Sans titre')
    except Exception as e:
        pred_status = f"❌ ({str(e)[:30]})"

    await event.respond(
        f"📡 **CONFIGURATION**\n\n"
        f"**Source des données:** API 1xBet (polling {API_POLL_INTERVAL}s)\n"
        f"**Jeux en cache:** {len(api_results_cache)}\n"
        f"**Jeux traités (joueur):** {len(player_processed_games)}\n\n"
        f"**Canal Prédiction:**\n"
        f"ID: `{PREDICTION_CHANNEL_ID}`\n"
        f"Status: {pred_status}\n"
        f"Nom: {pred_name}\n\n"
        f"**Paramètres:**\n"
        f"Compteur2 BP={compteur2_bp} | Actif: {'✅' if compteur2_active else '❌'}\n"
        f"Dernière prédiction: #{last_prediction_game if last_prediction_game else 'Aucune'}\n"
        f"Reset horaire: chaque heure pile\n"
        f"Reset jeu: #1440 (fin de partie)\n"
        f"Admin principal: `{ADMIN_ID}`\n"
        f"Admins supplémentaires: {', '.join(f'`{a}`' for a in EXTRA_ADMIN_IDS)}"
    )

async def cmd_test(event):
    if event.is_group or event.is_channel:
        return
    if not is_admin(event.sender_id):
        await event.respond("🔒 Admin uniquement")
        return

    await event.respond("🧪 Test de connexion au canal de prédiction...")

    try:
        if not PREDICTION_CHANNEL_ID:
            await event.respond("❌ PREDICTION_CHANNEL_ID non configuré")
            return

        prediction_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
        if not prediction_entity:
            await event.respond(
                f"❌ **Canal inaccessible** `{PREDICTION_CHANNEL_ID}`\n\n"
                f"Vérifiez:\n"
                f"1. L'ID est correct\n"
                f"2. Le bot est administrateur du canal\n"
                f"3. Le bot a les permissions d'envoi"
            )
            return

        test_msg = build_prediction_message(0, 9999, '♠', 0, "en cours ⌛ [TEST]")
        sent = await client.send_message(prediction_entity, test_msg)
        await asyncio.sleep(2)

        await client.edit_message(
            prediction_entity, sent.id,
            build_prediction_message(0, 9999, '♠', 0, "✅ GAGNÉ [TEST]")
        )
        await asyncio.sleep(2)
        await client.delete_messages(prediction_entity, [sent.id])

        pred_name_display = getattr(prediction_entity, 'title', str(prediction_entity.id))
        await event.respond(
            f"✅ **TEST RÉUSSI!**\n\n"
            f"Canal: `{pred_name_display}`\n"
            f"Envoi, modification et suppression: OK"
        )

    except ChatWriteForbiddenError:
        await event.respond(
            "❌ **Permission refusée** — Ajoutez le bot comme administrateur."
        )
    except Exception as e:
        await event.respond(f"❌ Échec du test: {e}")

async def cmd_reset(event):
    if event.is_group or event.is_channel:
        return
    if not is_admin(event.sender_id):
        await event.respond("🔒 Admin uniquement")
        return

    await event.respond("🔄 Reset en cours...")
    await perform_full_reset("Reset manuel admin")
    await event.respond("✅ Reset effectué! Compteurs remis à zéro.")

async def cmd_status(event):
    if event.is_group or event.is_channel:
        return
    if not is_admin(event.sender_id):
        await event.respond("🔒 Admin uniquement")
        return

    _first_g = cycle_first_game if cycle_first_game > 0 else 1
    lines = [
        "📈 **ÉTAT DU BOT**",
        "",
        get_compteur2_status_text(),
        "",
        f"🎮 Jeu actuel: #{current_game_number} | Plage: #{_first_g} → #{current_game_number}",
        f"📊 Parties analysées: {gap_games_processed} | Spécial: {special_games_processed}",
        f"🔮 Prédictions actives: {len(pending_predictions)}",
        f"📡 Source: API 1xBet (polling {API_POLL_INTERVAL}s)",
        f"📦 Jeux en cache: {len(api_results_cache)}",
        f"⏰ Reset horaire: chaque heure pile",
        f"🔄 Reset automatique: partie #1440 terminée",
    ]

    if pending_predictions:
        lines.append("")
        for num, pred in sorted(pending_predictions.items()):
            suit = SUIT_DISPLAY.get(pred['suit'], pred['suit'])
            trig = SUIT_DISPLAY.get(pred['triggered_by'], pred['triggered_by'])
            ar = pred.get('awaiting_rattrapage', 0)
            st = f"R{ar} en attente (#{num+ar})" if ar > 0 else "Vérification directe"
            lines.append(f"• joueur#{pred['counter']}:{num} {suit} (écart BP {trig}): {st}")

    await event.respond("\n".join(lines))

async def cmd_announce(event):
    if event.is_group or event.is_channel:
        return
    if not is_admin(event.sender_id):
        await event.respond("🔒 Admin uniquement")
        return

    parts = event.message.message.split(' ', 1)
    if len(parts) < 2:
        await event.respond("Usage: `/announce Message`")
        return

    text = parts[1].strip()
    if len(text) > 500:
        await event.respond("❌ Trop long (max 500 caractères)")
        return

    try:
        prediction_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
        if not prediction_entity:
            await event.respond("❌ Canal de prédiction non accessible")
            return

        now = datetime.now()
        msg = (
            f"╔══════════════════════════════════════╗\n"
            f"║     📢 ANNONCE OFFICIELLE 📢          ║\n"
            f"╠══════════════════════════════════════╣\n\n"
            f"{text}\n\n"
            f"╠══════════════════════════════════════╣\n"
            f"║  📅 {now.strftime('%d/%m/%Y')}  🕐 {now.strftime('%H:%M')}\n"
            f"╚══════════════════════════════════════╝\n\n"
            f"🎲𝐁𝐀𝐂𝐂𝐀𝐑𝐀 𝐏𝐑𝐄𝐌𝐈𝐔𝐌+2 ✨🎲"
        )
        sent = await client.send_message(prediction_entity, msg)
        await event.respond(f"✅ Annonce envoyée (ID: {sent.id})")
    except Exception as e:
        await event.respond(f"❌ Erreur: {e}")

async def cmd_help(event):
    if event.is_group or event.is_channel:
        return

    await event.respond(
        "📖 **BACCARAT PREMIUM+2 - AIDE**\n\n"
        "**🎮 Système de prédiction (Compteur2):**\n"
        "• Lit les cartes du joueur depuis l'API 1xBet\n"
        "• Compteur déclenché UNIQUEMENT quand la partie du joueur est terminée\n"
        "• Compte TOUTES les apparitions de chaque costume (ex: ♠️♠️ = +2 ♠)\n"
        "• Pour chaque paire inverse (♠↔♦ et ❤↔♣):\n"
        "  Si différence ≥ BP → prédit le costume le moins vu\n"
        "• Reset automatique à chaque heure pile\n\n"
        "**⏰ Restriction horaire:**\n"
        "• Prédictions autorisées uniquement de H:00 à H:29\n"
        "• Bloquées de H:30 à H:59 (ex: 12h00→12h29 OK, 12h30→12h59 BLOQUÉ)\n\n"
        "**🚫 Règle FK (costumes consécutifs):**\n"
        "• FK = max de prédictions consécutives du même costume\n"
        "• Ex: FK=3 → si les 3 dernières prédictions étaient ♠️, la 4ème ♠️ est bloquée\n"
        "• Déblocage auto si une autre costume est prédite entre-temps\n"
        "• Déblocage auto si 30+ min sans prédiction dans le cycle\n\n"
        "**📊 Format des prédictions:**\n"
        "🤖 joueur#N:jeu\n"
        "🔰Couleur de la carte :costume\n"
        "🔰 Rattrapages : X(🔰+X)\n"
        "🧨 Résultats : en cours ⌛ / ✅ GAGNÉ / ❌ PERDU\n\n"
        "**🛡️ Règles anti-spam prédictions:**\n"
        "• Écart minimum de 2 entre les numéros de jeu prédits\n"
        "• Un seul prédit à la fois (attend la vérification avant d'envoyer)\n"
        "• Pas de doublon sur le même numéro de jeu\n\n"
        "**🔍 Vérification dynamique:**\n"
        "• Dès que les cartes du joueur apparaissent → vérifie la prédiction\n"
        "• Costume trouvé → résultat immédiat\n"
        "• Pas trouvé et partie terminée → rattrapage (max 2)\n\n"
        "**🔄 Resets:**\n"
        "• Horaire: chaque heure pile\n"
        "• Automatique: quand la partie #1440 est terminée\n\n"
        "**🔧 Commandes Admin:**\n"
        "`/compteur2` — État et gestion du Compteur2\n"
        "`/compteur2 on/off` — Activer/désactiver\n"
        "`/compteur2 bp <val>` — Changer le seuil BP (défaut: 7)\n"
        "`/compteur2 fk <val>` — Max prédictions consécutives même costume (défaut: 3)\n"
        "`/compteur2 reset` — Remettre les compteurs à zéro\n"
        "`/status` — État complet\n"
        "`/history` — Historique des prédictions\n"
        "`/channels` — Configuration\n"
        "`/test` — Tester le canal\n"
        "`/reset` — Reset complet\n"
        "`/announce <msg>` — Annonce\n"
        "`/raison [N]` — Raison de la prédiction N (ou dernière)\n"
        "`/manquants` — Costumes manquants et écarts historiques\n"
        "`/rapport [minutes|now]` — Rapports auto périodiques\n"
        "`/help` — Cette aide"
    )

# ============================================================================
# RAPPORT AUTOMATIQUE
# ============================================================================

def _suit_conseil_detaille(suit: str, app: int, total_g: int, max_app: int, min_app: int) -> str:
    """Génère un conseil précis pour un costume basé sur sa fréquence et ses écarts."""
    d = SUIT_DISPLAY.get(suit, suit)
    pct = round(app / total_g * 100, 1) if total_g > 0 else 0
    inv = SUIT_INVERSE.get(suit, '?')
    inv_d = SUIT_DISPLAY.get(inv, inv)
    inv_app = gap_tracker[inv]['total_appearances']
    inv_pct = round(inv_app / total_g * 100, 1) if total_g > 0 else 0
    cur_gap = gap_tracker[suit]['current_gap']
    mx_gap = gap_tracker[suit]['max_gap']
    hist = [g for g in gap_tracker[suit]['historical_gaps'] if g <= MAX_GAP_VALID]
    avg_gap = round(sum(hist) / len(hist), 1) if hist else 0
    diff_with_inv = app - inv_app

    lines = []
    if app == min_app and max_app > 0 and app < max_app * 0.5:
        lines.append(f"🚨 **{d}** : SOUS-REPRÉSENTÉ ({pct}%) — apparaît 2× moins que {inv_d} ({inv_pct}%).")
        lines.append(f"   → Forte probabilité de rattrapage. Surveiller en priorité.")
    elif app == min_app:
        lines.append(f"⚠️ **{d}** : En retrait ({pct}%) vs {inv_d} ({inv_pct}%) — écart de {abs(diff_with_inv)} apparitions.")
        lines.append(f"   → Gardez-le dans votre radar, il devrait revenir.")
    elif app == max_app:
        lines.append(f"🔺 **{d}** : DOMINANT ({pct}%) — {abs(diff_with_inv)} apparitions de plus que son inverse {inv_d} ({inv_pct}%).")
        lines.append(f"   → Sur-représenté, peut ralentir. Moins prioritaire.")
    else:
        lines.append(f"📊 **{d}** : Fréquence correcte ({pct}%) — équilibré avec {inv_d} ({inv_pct}%).")
        lines.append(f"   → Pas de signal particulier.")

    if cur_gap > 0:
        if mx_gap > 0 and cur_gap >= mx_gap * 0.8:
            lines.append(f"   ⚠️ Absent depuis {cur_gap} parties ({round(cur_gap/mx_gap*100)}% du max historique {mx_gap}) — retour probable!")
        elif cur_gap > avg_gap and avg_gap > 0:
            lines.append(f"   📍 Absent depuis {cur_gap} parties (moy: {avg_gap}) — légèrement au-dessus de la moyenne.")
    return "\n".join(lines)


def build_rapport_special() -> str:
    """Rapport spécial : victoires, pair/impair, cartes, combinaisons.
    Chaque catégorie affiche: apparitions, %, écart courant, max, historique.
    Tout écart > MAX_GAP_SPECIAL (150) est signalé comme faux chiffre.
    """
    now = get_local_time()
    lines = []
    lines.append("🃏 **RAPPORT SPÉCIAL — BACCARAT AI**")
    lines.append(f"🕐 {now.strftime('%d/%m/%Y %H:%M')} (WAT)")
    first_g = cycle_first_game if cycle_first_game > 0 else 1
    lines.append(f"🎮 Parties analysées: {special_games_processed} | Plage: #{first_g} → #{current_game_number}")
    lines.append("")

    LABELS = {
        'joueur':   "👤 Victoire Joueur",
        'banquier': "🏦 Victoire Banquier",
        'tie':      "🤝 Match Nul",
        'pair':     "🔵 Pair Joueur (total pts joueur pair)",
        'impair':   "🔴 Impair Joueur (total pts joueur impair)",
        'pair_b':   "🔵 Pair Banquier (total pts banquier pair)",
        'impair_b': "🔴 Impair Banquier (total pts banquier impair)",
        '2k':       "2️⃣ Joueur 2 cartes (2K)",
        '3k':       "3️⃣ Joueur 3 cartes (3K)",
        '3_2':      "🔹 Joueur 3K / Banquier 2K",
        '3_3':      "🔸 Joueur 3K / Banquier 3K",
        '2_3':      "🔷 Joueur 2K / Banquier 3K",
        '2_2':      "🔶 Joueur 2K / Banquier 2K",
    }

    GROUPS = [
        ("━━━━━━━━━━━━━━━━━━━━━━━━━━\n🏆 **VICTOIRES**\n━━━━━━━━━━━━━━━━━━━━━━━━━━",
            ['joueur', 'banquier', 'tie']),
        ("━━━━━━━━━━━━━━━━━━━━━━━━━━\n🔵🔴 **PAIR / IMPAIR — JOUEUR** (total pts joueur)\n━━━━━━━━━━━━━━━━━━━━━━━━━━",
            ['pair', 'impair']),
        ("━━━━━━━━━━━━━━━━━━━━━━━━━━\n🔵🔴 **PAIR / IMPAIR — BANQUIER** (total pts banquier)\n━━━━━━━━━━━━━━━━━━━━━━━━━━",
            ['pair_b', 'impair_b']),
        ("━━━━━━━━━━━━━━━━━━━━━━━━━━\n🃏 **NOMBRE DE CARTES JOUEUR**\n━━━━━━━━━━━━━━━━━━━━━━━━━━",
            ['2k', '3k']),
        ("━━━━━━━━━━━━━━━━━━━━━━━━━━\n🎴 **COMBINAISONS JOUEUR/BANQUIER**\n━━━━━━━━━━━━━━━━━━━━━━━━━━",
            ['3_2', '3_3', '2_3', '2_2']),
    ]

    total_g = special_games_processed

    for header, cats in GROUPS:
        lines.append(header)

        for cat in cats:
            info = special_tracker[cat]
            label = LABELS.get(cat, cat)
            app = info['total_appearances']
            pct = round(app / total_g * 100, 1) if total_g > 0 else 0
            cur_gap = info['current_gap']
            mx_gap = info['max_gap']
            hist_valid = [g for g in info['historical_gaps'] if g <= MAX_GAP_SPECIAL]
            hist_faux  = [g for g in info['historical_gaps'] if g > MAX_GAP_SPECIAL]
            avg_gap = round(sum(hist_valid) / len(hist_valid), 1) if hist_valid else 0

            lines.append(f"\n{label}")
            if total_g == 0:
                lines.append("  ❓ Pas encore de données.")
                continue

            # Barre de fréquence
            bar_f = round(pct / 100 * 15)
            bar = "🟩" * bar_f + "⬜" * (15 - bar_f)
            lines.append(f"  📊 {app} fois | {pct}% | {bar}")

            # Écart courant
            if cur_gap > 0:
                if cur_gap > MAX_GAP_SPECIAL:
                    lines.append(f"  🚫 Absent depuis {cur_gap} parties → **FAUX CHIFFRE** (>{MAX_GAP_SPECIAL})")
                elif mx_gap > 0 and cur_gap >= mx_gap * 0.8:
                    lines.append(f"  🚨 Absent depuis {cur_gap} parties ({round(cur_gap/mx_gap*100)}% du max {mx_gap}) — retour imminent !")
                elif cur_gap > avg_gap and avg_gap > 0:
                    lines.append(f"  ⚠️ Absent depuis {cur_gap} parties (moy: {avg_gap}) — au-dessus de la moyenne")
                else:
                    lines.append(f"  📍 Absent depuis {cur_gap} parties (moy: {avg_gap})")
            else:
                lines.append(f"  ✅ Présent à la dernière partie")

            # Stats écarts
            lines.append(f"  📐 Écart max: {mx_gap} | Moy valide: {avg_gap} | Historique: {len(hist_valid)} écart(s)")

            if hist_faux:
                lines.append(f"  🚫 Faux chiffres (>{MAX_GAP_SPECIAL}): {', '.join(str(g) for g in sorted(hist_faux, reverse=True)[:5])}")

        lines.append("")

    lines.append(f"📌 Seuil faux chiffres: écart > {MAX_GAP_SPECIAL} parties")
    lines.append(f"🕐 Généré le {now.strftime('%d/%m/%Y à %H:%M')} (WAT)")
    return "\n".join(lines)


def build_rapport_simple() -> str:
    """Rapport bref — chiffres globaux uniquement. Envoyé périodiquement aux admins."""
    now = get_local_time()
    lines = []
    lines.append(f"📊 **RAPPORT BACCARAT AI** — {now.strftime('%d/%m/%Y %H:%M')} (WAT)")
    first_g = cycle_first_game if cycle_first_game > 0 else 1
    lines.append(f"🎮 Parties analysées: {gap_games_processed} | Plage: #{first_g} → #{current_game_number}")
    lines.append("")

    # Prédictions
    total_pred = len(prediction_history)
    gagnes = sum(1 for p in prediction_history if p['status'] == 'gagne')
    perdus = sum(1 for p in prediction_history if p['status'] == 'perdu')
    taux = round(gagnes / (gagnes + perdus) * 100, 1) if (gagnes + perdus) > 0 else 0
    lines.append(f"🎯 Prédictions: {total_pred} | ✅ {gagnes} | ❌ {perdus} | 🏆 {taux}%")

    # Compteurs
    lines.append(f"📈 Compteurs (depuis dernier reset horaire):")
    for suit in ALL_SUITS:
        d = SUIT_DISPLAY.get(suit, suit)
        lines.append(f"  {d}: {compteur2_counts[suit]}")

    # Manquants urgents
    urgents = [
        f"{SUIT_DISPLAY.get(s, s)}({gap_tracker[s]['current_gap']}j)"
        for s in ALL_SUITS
        if gap_tracker[s]['current_gap'] > 0 and gap_tracker[s]['max_gap'] > 0
        and gap_tracker[s]['current_gap'] >= gap_tracker[s]['max_gap'] * 0.7
    ]
    if urgents:
        lines.append(f"⚠️ Manquants à surveiller: {', '.join(urgents)}")

    lines.append("")
    lines.append("💡 Envoie `/rapport details` pour le rapport complet.")
    return "\n".join(lines)


def build_rapport_detaille() -> str:
    """Rapport détaillé avec fréquences, manquants, écarts et conseils comparatifs."""
    now = get_local_time()
    date_str = now.strftime('%d/%m/%Y à %H:%M')
    lines = []

    lines.append(f"📊 **BILAN COMPLET — BACCARAT AI**")
    lines.append(f"🕐 {date_str} (heure Bénin/Cameroun)")
    first_g = cycle_first_game if cycle_first_game > 0 else 1
    lines.append(f"🎮 Parties analysées: {gap_games_processed} | Plage: #{first_g} → #{current_game_number}")
    lines.append("")

    # ── 1. Fréquence des costumes ─────────────────────────────────────────────
    lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━")
    lines.append("🃏 **FRÉQUENCE DES COSTUMES (JOUEUR)**")
    lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━")

    total_g = gap_games_processed
    if total_g > 0:
        sorted_by_freq = sorted(ALL_SUITS, key=lambda s: gap_tracker[s]['total_appearances'], reverse=True)
        max_app = max(gap_tracker[s]['total_appearances'] for s in ALL_SUITS) or 1
        min_app = min(gap_tracker[s]['total_appearances'] for s in ALL_SUITS)

        lines.append("📋 **Nombre d'apparitions :**")
        for suit in sorted_by_freq:
            app = gap_tracker[suit]['total_appearances']
            d = SUIT_DISPLAY.get(suit, suit)
            pct = round(app / total_g * 100, 1)
            bar_f = round(app / max_app * 20) if max_app > 0 else 0
            bar = "🟦" * bar_f + "⬜" * (20 - bar_f)
            icon = "🔺" if app == max_app else ("🔻" if app == min_app else "✅")
            lines.append(f"{icon} {d} : {app} apparitions ({pct}%)")
            lines.append(f"   {bar}")

        lines.append("")
        lines.append("🎯 **Analyse comparative et conseils :**")
        for suit in sorted(ALL_SUITS, key=lambda s: gap_tracker[s]['total_appearances']):
            app = gap_tracker[suit]['total_appearances']
            lines.append(_suit_conseil_detaille(suit, app, total_g, max_app, min_app))
            lines.append("")

        max_d = SUIT_DISPLAY.get(sorted_by_freq[0], sorted_by_freq[0])
        min_d = SUIT_DISPLAY.get(sorted_by_freq[-1], sorted_by_freq[-1])
        max_v = gap_tracker[sorted_by_freq[0]]['total_appearances']
        min_v = gap_tracker[sorted_by_freq[-1]]['total_appearances']
        diff_pct = round((max_v - min_v) / total_g * 100, 1)
        lines.append(f"📌 **Résumé :** {min_d} est le plus rare ({min_v}×) vs {max_d} le plus fréquent ({max_v}×) — écart global: {diff_pct}%")
        if diff_pct > 25:
            lines.append("🚨 Déséquilibre fort — le costume rare a une forte probabilité de revenir dans les prochaines parties.")
        elif diff_pct > 10:
            lines.append("⚠️ Léger déséquilibre — à surveiller.")
        else:
            lines.append("✅ Répartition équilibrée — aucun costume en situation critique.")

        # Comparaison paires inverses
        lines.append("")
        lines.append("🔄 **Comparaison paires inverses :**")
        for s1, s2 in INVERSE_PAIRS:
            d1, d2 = SUIT_DISPLAY.get(s1, s1), SUIT_DISPLAY.get(s2, s2)
            c1 = gap_tracker[s1]['total_appearances']
            c2 = gap_tracker[s2]['total_appearances']
            diff = abs(c1 - c2)
            dominant = d1 if c1 > c2 else d2
            rare = d2 if c1 > c2 else d1
            if diff == 0:
                lines.append(f"  {d1} ↔ {d2}: Équilibre parfait ({c1}/{c2})")
            else:
                lines.append(f"  {d1} ↔ {d2}: écart {diff} — {dominant} domine, {rare} probable prochain")
    else:
        lines.append("❓ Pas encore de données.")

    lines.append("")

    # ── 2. Bilan des prédictions ──────────────────────────────────────────────
    lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━")
    lines.append("🎯 **BILAN DES PRÉDICTIONS**")
    lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━")

    total_pred = len(prediction_history)
    gagnes = sum(1 for p in prediction_history if p['status'] == 'gagne')
    perdus = sum(1 for p in prediction_history if p['status'] == 'perdu')
    en_cours = sum(1 for p in prediction_history if p['status'] == 'en_cours')
    taux = round(gagnes / (gagnes + perdus) * 100, 1) if (gagnes + perdus) > 0 else 0

    lines.append(f"📈 Total: {total_pred} | ✅ Gagnées: {gagnes} | ❌ Perdues: {perdus} | ⏳ En cours: {en_cours}")
    lines.append(f"🏆 Taux de réussite: {taux}%")

    if total_pred > 0:
        lines.append("")
        lines.append("🎯 **Par costume :**")
        for suit in ALL_SUITS:
            d = SUIT_DISPLAY.get(suit, suit)
            st = sum(1 for p in prediction_history if p['suit'] == suit)
            sg = sum(1 for p in prediction_history if p['suit'] == suit and p['status'] == 'gagne')
            if st > 0:
                lines.append(f"  {d}: {sg}/{st} ({round(sg/st*100)}%)")

    lines.append("")

    # ── 3. Manquants en cours ─────────────────────────────────────────────────
    lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━")
    lines.append("⏳ **MANQUES EN COURS**")
    lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━")

    presentes = []
    for suit in sorted(ALL_SUITS, key=lambda s: gap_tracker[s]['current_gap'], reverse=True):
        info = gap_tracker[suit]
        d = SUIT_DISPLAY.get(suit, suit)
        cur = info['current_gap']
        mx = info['max_gap']
        hist = info['historical_gaps']
        avg = round(sum(hist) / len(hist), 1) if hist else 0
        last = info['last_seen_game']
        if cur == 0:
            presentes.append(d)
        else:
            urgence = ""
            if mx > 0 and cur >= mx:
                urgence = "CRITIQUE — proche du max"
            elif mx > 0 and cur >= mx * 0.7:
                urgence = "Attention!"
            lines.append(f"🚨 {d} : {cur} jeu(x) depuis #{last}")
            lines.append(f"   Max jamais: {mx} | Moy: {avg} | {urgence}")
    if presentes:
        lines.append(f"✅ Présents récemment: {', '.join(presentes)}")
    if all(gap_tracker[s]['current_gap'] == 0 for s in ALL_SUITS):
        lines.append("✅ Tous les costumes sont présents régulièrement.")

    lines.append("")

    # ── 4. Écarts historiques ─────────────────────────────────────────────────
    lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━")
    lines.append("📊 **ÉCARTS HISTORIQUES PAR COSTUME**")
    lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━")

    for suit in ALL_SUITS:
        info = gap_tracker[suit]
        d = SUIT_DISPLAY.get(suit, suit)
        hist = info['historical_gaps']
        if hist:
            avg = round(sum(hist) / len(hist), 1)
            mx = info['max_gap']
            recent = hist[-3:]
            trend = ""
            if len(recent) >= 2:
                trend = " 📈 (hausse)" if recent[-1] > recent[-2] else (" 📉 (baisse)" if recent[-1] < recent[-2] else "")
            lines.append(f"{d} — Max: {mx} | Moy: {avg} | Derniers: {', '.join(str(g) for g in recent)}{trend}")
        else:
            lines.append(f"{d} — Aucun écart enregistré")

    lines.append("")
    lines.append(f"🕐 Généré le {date_str} (WAT)")

    return "\n".join(lines)


def build_daily_rapport_1440() -> str:
    """Rapport journalier complet — cycle #1 → #1440, avec heures de jeu précises.

    Règle écarts : tout écart > MAX_GAP_VALID (50) = faux chiffre (exclu des stats).
    Affiche les 20 plus grands écarts valides par costume.
    """
    now = get_local_time()
    date_str = now.strftime('%d/%m/%Y à %H:%M')

    # ── Résoudre les heures du cycle ─────────────────────────────────────────
    if cycle_start_time:
        heure_debut = cycle_start_time.strftime('%H:%M:%S')
    else:
        heure_debut = "—"
    heure_fin = now.strftime('%H:%M:%S')

    # Heure du premier et dernier jeu enregistrés
    if game_timestamps:
        ts_sorted = sorted(game_timestamps.items())
        first_g_num, first_g_ts = ts_sorted[0]
        last_g_num, last_g_ts = ts_sorted[-1]
        heure_premier = f"#{first_g_num} à {first_g_ts.strftime('%H:%M:%S')}"
        heure_dernier = f"#{last_g_num} à {last_g_ts.strftime('%H:%M:%S')}"
        duree_min = round((last_g_ts - first_g_ts).total_seconds() / 60)
        duree_str = f"{duree_min} min ({duree_min // 60}h{duree_min % 60:02d})"
    else:
        heure_premier = heure_dernier = duree_str = "—"

    lines = []
    lines.append("📅 **RAPPORT JOURNALIER — BACCARAT AI**")
    lines.append(f"🕐 {date_str} (WAT)")
    lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━")
    lines.append("🕰️ **INFORMATIONS DU CYCLE**")
    lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━")
    _first = cycle_first_game if cycle_first_game > 0 else 1
    _last  = cycle_last_game  if cycle_last_game  > 0 else current_game_number
    lines.append(f"📌 Cycle: Jeu #{_first} → #{_last}")
    lines.append(f"🎮 Parties traitées: {gap_games_processed} / 1440")
    lines.append(f"🕐 Début cycle: {heure_debut}")
    lines.append(f"🕐 Fin cycle:   {heure_fin}")
    lines.append(f"⏱️ Durée totale: {duree_str}")
    lines.append(f"🎲 Premier jeu: {heure_premier}")
    lines.append(f"🎲 Dernier jeu: {heure_dernier}")
    lines.append("")

    # ── 1. Bilan des prédictions ──────────────────────────────────────────────
    lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━")
    lines.append("🎯 **BILAN DES PRÉDICTIONS**")
    lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━")

    total_pred = len(prediction_history)
    gagnes = sum(1 for p in prediction_history if p['status'] == 'gagne')
    perdus = sum(1 for p in prediction_history if p['status'] == 'perdu')
    en_cours = sum(1 for p in prediction_history if p['status'] == 'en_cours')
    taux = round(gagnes / (gagnes + perdus) * 100, 1) if (gagnes + perdus) > 0 else 0

    lines.append(f"📈 Total: {total_pred} | ✅ {gagnes} gagnées | ❌ {perdus} perdues | ⏳ {en_cours} en cours")
    lines.append(f"🏆 Taux de réussite: **{taux}%**")

    if total_pred > 0:
        lines.append("")
        lines.append("🎯 **Par costume :**")
        for suit in ALL_SUITS:
            d = SUIT_DISPLAY.get(suit, suit)
            st = sum(1 for p in prediction_history if p['suit'] == suit)
            sg = sum(1 for p in prediction_history if p['suit'] == suit and p['status'] == 'gagne')
            sp = sum(1 for p in prediction_history if p['suit'] == suit and p['status'] == 'perdu')
            if st > 0:
                t = round(sg / st * 100)
                bar_f = round(t / 100 * 10)
                bar = "🟩" * bar_f + "⬜" * (10 - bar_f)
                lines.append(f"  {d}: {sg}/{st} ({t}%) {bar}")

        # Meilleure/pire heure de prédiction
        if prediction_history:
            pred_by_hour: Dict[int, list] = {}
            for p in prediction_history:
                h = p['predicted_at'].hour
                pred_by_hour.setdefault(h, []).append(p)
            best_hour = max(pred_by_hour, key=lambda h: sum(
                1 for p in pred_by_hour[h] if p['status'] == 'gagne'))
            lines.append(f"\n  ⏰ Meilleure heure de prédiction: **{best_hour:02d}h**")

    lines.append("")

    # ── 2. Fréquence et variations ────────────────────────────────────────────
    lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━")
    lines.append("🃏 **FRÉQUENCE & VARIATIONS DES COSTUMES**")
    lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━")

    total_g = gap_games_processed
    if total_g > 0:
        sorted_by_freq = sorted(ALL_SUITS, key=lambda s: gap_tracker[s]['total_appearances'], reverse=True)
        max_app = max(gap_tracker[s]['total_appearances'] for s in ALL_SUITS) or 1
        min_app = min(gap_tracker[s]['total_appearances'] for s in ALL_SUITS)

        for suit in sorted_by_freq:
            app = gap_tracker[suit]['total_appearances']
            d = SUIT_DISPLAY.get(suit, suit)
            pct = round(app / total_g * 100, 1)
            bar_f = round(app / max_app * 20) if max_app > 0 else 0
            bar = "🟦" * bar_f + "⬜" * (20 - bar_f)
            icon = "🔺" if app == max_app else ("🔻" if app == min_app else "✅")
            lines.append(f"{icon} {d} : {app} apparitions ({pct}%)")
            lines.append(f"   {bar}")

        lines.append("")
        lines.append("🎯 **Analyse comparative et conseils :**")
        for suit in sorted(ALL_SUITS, key=lambda s: gap_tracker[s]['total_appearances']):
            app = gap_tracker[suit]['total_appearances']
            lines.append(_suit_conseil_detaille(suit, app, total_g, max_app, min_app))
            lines.append("")

        # Comparaison paires inverses
        lines.append("🔄 **Comparaison paires inverses :**")
        for s1, s2 in INVERSE_PAIRS:
            d1, d2 = SUIT_DISPLAY.get(s1, s1), SUIT_DISPLAY.get(s2, s2)
            c1 = gap_tracker[s1]['total_appearances']
            c2 = gap_tracker[s2]['total_appearances']
            diff = abs(c1 - c2)
            if diff == 0:
                lines.append(f"  {d1} ↔ {d2}: Équilibre parfait ({c1}/{c2}) ✅")
            else:
                dominant = d1 if c1 > c2 else d2
                rare = d2 if c1 > c2 else d1
                lines.append(f"  {d1} ↔ {d2}: écart {diff} — {dominant} domine → {rare} probable prochain cycle")
    else:
        lines.append("❓ Pas de données ce cycle.")

    lines.append("")

    # ── 3. Écarts par costume — TOP 20 ────────────────────────────────────────
    lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━")
    lines.append(f"📊 **ÉCARTS PAR COSTUME — TOP 20** (seuil faux: >{MAX_GAP_VALID})")
    lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━")

    for suit in ALL_SUITS:
        info = gap_tracker[suit]
        d = SUIT_DISPLAY.get(suit, suit)
        all_gaps = info['historical_gaps'][:]
        if info['current_gap'] > 0:
            all_gaps.append(info['current_gap'])

        valid_gaps = [g for g in all_gaps if g <= MAX_GAP_VALID]
        faux_gaps = [g for g in all_gaps if g > MAX_GAP_VALID]

        if not all_gaps:
            lines.append(f"{d} — Aucun écart enregistré ce cycle.")
            lines.append("")
            continue

        top20 = sorted(valid_gaps, reverse=True)[:20]
        max_v = max(valid_gaps) if valid_gaps else 0
        avg_v = round(sum(valid_gaps) / len(valid_gaps), 1) if valid_gaps else 0
        global_max = info['max_gap']

        lines.append(f"**{d}** — {len(valid_gaps)} écart(s) | Max cycle: {max_v} | Moy: {avg_v} | Record global: {global_max}")
        if top20:
            lines.append(f"  🏆 Top 20: {' | '.join(str(g) for g in top20)}")
        if faux_gaps:
            lines.append(f"  🚫 Faux chiffres (>{MAX_GAP_VALID}) exclus: {', '.join(str(g) for g in sorted(faux_gaps, reverse=True))}")
        if max_v >= 40:
            lines.append(f"  ⚠️ Écart élevé ({max_v}) — peut être absent longtemps au prochain cycle.")
        lines.append("")

    lines.append("")
    lines.append(f"🔄 Le bot repart sur un nouveau cycle (#1 → #1440).")
    lines.append(f"🕐 Rapport généré le {date_str} (WAT)")

    return "\n".join(lines)


async def send_rapport_to_admins(message: str):
    """Envoie le rapport à tous les admins configurés."""
    global last_rapport_time
    last_rapport_time = datetime.now()

    all_admin_ids = []
    if ADMIN_ID and ADMIN_ID != 0:
        all_admin_ids.append(ADMIN_ID)
    for aid in EXTRA_ADMIN_IDS:
        if aid not in all_admin_ids:
            all_admin_ids.append(aid)

    for admin_id in all_admin_ids:
        try:
            await client.send_message(admin_id, message)
            logger.info(f"📊 Rapport envoyé à admin {admin_id}")
        except Exception as e:
            logger.error(f"❌ Erreur envoi rapport à {admin_id}: {e}")


async def rapport_task_loop():
    """Tâche asynchrone — envoie le rapport SIMPLE périodiquement aux admins."""
    logger.info("📊 Tâche rapport automatique démarrée")
    while True:
        await asyncio.sleep(60)
        if rapport_interval <= 0:
            continue
        now = datetime.now()
        if (last_rapport_time is None or
                (now - last_rapport_time).total_seconds() >= rapport_interval * 60):
            try:
                msg = build_rapport_simple()
                await send_rapport_to_admins(msg)
                logger.info("📊 Rapport simple périodique envoyé")
            except Exception as e:
                logger.error(f"❌ Erreur tâche rapport: {e}")


# ============================================================================
# COMMANDES — RAISON / MANQUANTS / RAPPORT
# ============================================================================

async def cmd_raison(event):
    """Explique pourquoi le bot a fait une prédiction donnée."""
    if event.is_group or event.is_channel:
        return
    if not is_admin(event.sender_id):
        await event.respond("🔒 Admin uniquement")
        return

    parts = event.message.message.strip().split()
    pred = None

    if len(parts) >= 2:
        try:
            n = int(parts[1])
            for p in prediction_history:
                if p['counter'] == n:
                    pred = p
                    break
            if not pred:
                await event.respond(f"❓ Prédiction numéro {n} introuvable dans l'historique.")
                return
        except ValueError:
            await event.respond("Usage: `/raison [N]` — N = numéro de prédiction (optionnel, défaut: dernière)")
            return
    else:
        pred = prediction_history[0] if prediction_history else None

    if not pred:
        await event.respond("❓ Aucune prédiction dans l'historique.")
        return

    suit = pred['suit']
    suit_d = SUIT_DISPLAY.get(suit, suit)
    trig = pred['triggered_by']
    trig_d = SUIT_DISPLAY.get(trig, trig)
    inv = SUIT_INVERSE.get(trig, '?')
    inv_d = SUIT_DISPLAY.get(inv, inv)
    c1 = pred.get('trigger_c1', '?')
    c2 = pred.get('trigger_c2', '?')
    diff = pred.get('trigger_diff', '?')
    time_str = pred['predicted_at'].strftime('%H:%M:%S')

    status = pred['status']
    status_str = {"en_cours": "⏳ En cours", "gagne": "✅ GAGNÉ", "perdu": "❌ PERDU"}.get(status, status)

    counts = pred.get('counts_snapshot', {})
    counts_lines = "\n".join(
        f"  {SUIT_DISPLAY.get(s, s)}: {counts.get(s, 0)} apparition(s)"
        for s in ALL_SUITS
    )

    await event.respond(
        f"🔍 **RAISON — joueur#{pred['counter']}:{pred['predicted_game']}**\n\n"
        f"🎯 Costume prédit: **{suit_d}**\n"
        f"🕐 Heure: {time_str}\n"
        f"📊 Résultat: {status_str}\n\n"
        f"**📉 Pourquoi ce costume ?**\n"
        f"Paire analysée: {trig_d} ↔ {inv_d}\n"
        f"• {trig_d} avait **{c1}** apparition(s)\n"
        f"• {inv_d} avait **{c2}** apparition(s)\n"
        f"• Écart = **{diff}** (seuil BP = {compteur2_bp})\n"
        f"→ {suit_d} est le moins représenté → prédit comme prochain costume.\n\n"
        f"**📋 Compteurs au moment de la prédiction:**\n"
        f"{counts_lines}"
    )


async def cmd_manquants(event):
    """Affiche les costumes manquants et l'analyse des écarts."""
    if event.is_group or event.is_channel:
        return
    if not is_admin(event.sender_id):
        await event.respond("🔒 Admin uniquement")
        return

    _first_g = cycle_first_game if cycle_first_game > 0 else 1
    lines = [
        "⏳ **MANQUANTS & ÉCARTS PAR COSTUME**",
        f"🎮 Parties analysées: {gap_games_processed} | Plage: #{_first_g} → #{current_game_number}",
        "══════════════════════════════════════",
        ""
    ]

    sorted_suits = sorted(ALL_SUITS, key=lambda s: gap_tracker[s]['current_gap'], reverse=True)

    for suit in sorted_suits:
        info = gap_tracker[suit]
        d = SUIT_DISPLAY.get(suit, suit)
        cur = info['current_gap']
        mx = info['max_gap']
        hist = info['historical_gaps']
        last = info['last_seen_game']
        total_app = info['total_appearances']
        avg = round(sum(hist) / len(hist), 1) if hist else 0

        if cur == 0:
            urgence = "✅ Présent récemment"
        elif mx > 0 and cur >= mx:
            urgence = "🚨 CRITIQUE — proche du max!"
        elif mx > 0 and cur >= mx * 0.7:
            urgence = "⚠️ Attention!"
        else:
            urgence = f"📍 Absent depuis {cur} partie(s)"

        hist_str = ", ".join(str(g) for g in hist[-5:]) if hist else "Aucun"

        lines.append(f"**{d}**")
        lines.append(f"  📍 Absent depuis: {cur} jeu(x) | Dernier jeu: #{last}")
        lines.append(f"  📈 Max écart: {mx} | Moy: {avg} | Total: {total_app} app.")
        lines.append(f"  📜 Derniers écarts: {hist_str}")
        lines.append(f"  {urgence}")
        lines.append("")

    await event.respond("\n".join(lines))


async def cmd_rapport(event):
    """Gère les rapports: simple (périodique) et détaillé (sur demande).

    /rapport            → statut actuel
    /rapport <N>        → activer rapport simple toutes les N minutes
    /rapport 0          → désactiver
    /rapport now        → envoyer rapport simple maintenant
    /rapport details    → envoyer rapport détaillé maintenant
    /rapport 1440       → envoyer rapport journalier complet maintenant
    """
    global rapport_interval

    if event.is_group or event.is_channel:
        return
    if not is_admin(event.sender_id):
        await event.respond("🔒 Admin uniquement")
        return

    parts = event.message.message.strip().split()

    if len(parts) == 1:
        status = f"✅ Actif (toutes les {rapport_interval} min)" if rapport_interval > 0 else "❌ Désactivé"
        last = last_rapport_time.strftime('%H:%M:%S') if last_rapport_time else "Jamais"
        await event.respond(
            f"📊 **RAPPORTS AUTOMATIQUES**\n\n"
            f"Statut: {status}\n"
            f"Dernier rapport envoyé: {last}\n\n"
            f"**Commandes disponibles:**\n"
            f"`/rapport <N>` — Rapport simple toutes les N min (ex: 60)\n"
            f"`/rapport 0` — Désactiver\n"
            f"`/rapport now` — Rapport simple maintenant\n"
            f"`/rapport details` — Rapport détaillé complet maintenant\n"
            f"`/rapport 1440` — Rapport journalier (fin de cycle) maintenant\n\n"
            f"ℹ️ Le rapport simple = chiffres globaux rapides\n"
            f"ℹ️ Le rapport détaillé = analyse complète avec conseils"
        )
        return

    arg = parts[1].lower()

    if arg == 'now':
        await event.respond("⏳ Génération du rapport simple...")
        msg = build_rapport_simple()
        await send_rapport_to_admins(msg)
        await event.respond("✅ Rapport simple envoyé à tous les admins en privé.")
        return

    if arg == 'details':
        await event.respond("⏳ Génération du rapport détaillé...")
        msg = build_rapport_detaille()
        await send_rapport_to_admins(msg)
        await event.respond("✅ Rapport détaillé envoyé à tous les admins en privé.")
        return

    if arg == '1440':
        await event.respond("⏳ Génération du rapport journalier complet...")
        msg = build_daily_rapport_1440()
        await send_rapport_to_admins(msg)
        await event.respond("✅ Rapport journalier envoyé à tous les admins en privé.")
        return

    try:
        minutes = int(arg)
        if minutes < 0:
            await event.respond("❌ Valeur invalide (doit être ≥ 0).")
            return
        rapport_interval = minutes
        if minutes == 0:
            await event.respond("❌ **Rapports automatiques désactivés**")
        else:
            await event.respond(
                f"✅ **Rapports automatiques activés**\n\n"
                f"Fréquence: toutes les **{minutes} minutes**\n"
                f"Type: rapport simple (chiffres globaux)\n"
                f"Destinataires: tous les admins en privé\n\n"
                f"💡 Utilise `/rapport details` pour un rapport détaillé à la demande."
            )
    except ValueError:
        await event.respond(
            "❌ Argument non reconnu.\n\n"
            "`/rapport <N>` | `/rapport now` | `/rapport details` | `/rapport 1440`"
        )


# ============================================================================
# COMMANDE RAPPORT SPÉCIAL
# ============================================================================

def _pdf_bar(value: float, total: float, width: int = 20) -> str:
    """Génère une barre de progression en texte pour le PDF."""
    if total == 0:
        return "[" + "-" * width + "]"
    filled = round(value / total * width)
    filled = max(0, min(filled, width))
    return "[" + "#" * filled + "-" * (width - filled) + "]"


def generate_special_pdf(path: str):
    """Génère le rapport spécial complet en PDF et l'enregistre à `path`."""
    from fpdf import FPDF
    from fpdf.enums import XPos, YPos

    # Helvetica ne supporte que Latin-1 → remplacer les caractères hors-plage
    _UNICODE_REPLACE = {
        '\u2014': '-',   # em dash —
        '\u2013': '-',   # en dash –
        '\u2192': '->',  # flèche →
        '\u2190': '<-',  # flèche ←
        '\u2194': '<->', # flèche ↔
        '\u00b7': '*',   # point médian ·
        '\u2022': '*',   # puce •
        '\u00ab': '<<',  # «
        '\u00bb': '>>',  # »
        '\u201c': '"',   # "
        '\u201d': '"',   # "
        '\u2026': '...', # …
        '\u00e9': 'e',   # é  (latin-1, en fait supporté — laissé pour sécurité)
    }

    def safe(text: str) -> str:
        """Remplace les caractères non supportés par Helvetica (hors Latin-1)."""
        for ch, repl in _UNICODE_REPLACE.items():
            text = text.replace(ch, repl)
        return text.encode('latin-1', errors='replace').decode('latin-1')

    now = get_local_time()

    LABELS = {
        'joueur':   'Victoire Joueur',
        'banquier': 'Victoire Banquier',
        'tie':      'Match Nul',
        'pair':     'Pair Joueur  (total pts joueur pair)',
        'impair':   'Impair Joueur  (total pts joueur impair)',
        'pair_b':   'Pair Banquier  (total pts banquier pair)',
        'impair_b': 'Impair Banquier  (total pts banquier impair)',
        '2k':       'Joueur 2 cartes  (2K)',
        '3k':       'Joueur 3 cartes  (3K)',
        '3_2':      'Joueur 3K / Banquier 2K',
        '3_3':      'Joueur 3K / Banquier 3K',
        '2_3':      'Joueur 2K / Banquier 3K',
        '2_2':      'Joueur 2K / Banquier 2K',
    }
    GROUPS = [
        ('VICTOIRES',                             ['joueur', 'banquier', 'tie']),
        ('PAIR / IMPAIR  (points joueur)',         ['pair', 'impair']),
        ('PAIR / IMPAIR  (points banquier)',       ['pair_b', 'impair_b']),
        ('NOMBRE DE CARTES JOUEUR',               ['2k', '3k']),
        ('COMBINAISONS JOUEUR / BANQUIER',        ['3_2', '3_3', '2_3', '2_2']),
    ]

    # Couleurs
    C_DARK   = (30, 30, 60)
    C_HEAD   = (52, 73, 94)
    C_SUB    = (41, 128, 185)
    C_GREEN  = (39, 174, 96)
    C_ORANGE = (230, 126, 34)
    C_RED    = (192, 57, 43)
    C_GRAY   = (149, 165, 166)
    C_WHITE  = (255, 255, 255)
    C_LIGHT  = (236, 240, 241)

    pdf = FPDF()
    pdf.set_auto_page_break(auto=True, margin=15)
    pdf.add_page()

    # ── En-tête ──────────────────────────────────────────────────────────────
    pdf.set_fill_color(*C_DARK)
    pdf.rect(0, 0, 210, 38, 'F')
    pdf.set_text_color(*C_WHITE)
    pdf.set_font('Helvetica', 'B', 22)
    pdf.set_xy(10, 6)
    pdf.cell(190, 12, 'RAPPORT SPECIAL  -  BACCARAT AI', align='C',
             new_x=XPos.LMARGIN, new_y=YPos.NEXT)
    _first_g = cycle_first_game if cycle_first_game > 0 else 1
    _last_g  = current_game_number if current_game_number > 0 else special_games_processed
    pdf.set_font('Helvetica', '', 11)
    pdf.set_xy(10, 20)
    pdf.cell(190, 8,
             f"Genere le {now.strftime('%d/%m/%Y a %H:%M')} (WAT)  |  "
             f"Parties: {special_games_processed}  |  Plage: #{_first_g} -> #{_last_g}  |  "
             f"Seuil faux chiffres: > {MAX_GAP_SPECIAL} parties",
             align='C', new_x=XPos.LMARGIN, new_y=YPos.NEXT)
    pdf.ln(14)

    total_g = special_games_processed

    def section_header(title: str):
        pdf.set_fill_color(*C_HEAD)
        pdf.set_text_color(*C_WHITE)
        pdf.set_font('Helvetica', 'B', 13)
        pdf.cell(0, 9, f'  {title}', fill=True,
                 new_x=XPos.LMARGIN, new_y=YPos.NEXT)
        pdf.ln(3)

    def cat_row(cat: str):
        info = special_tracker[cat]
        label = LABELS.get(cat, cat)
        app   = info['total_appearances']
        pct   = round(app / total_g * 100, 1) if total_g > 0 else 0.0
        cur   = info['current_gap']
        mx    = info['max_gap']
        hist_v = [g for g in info['historical_gaps'] if g <= MAX_GAP_SPECIAL]
        hist_f = [g for g in info['historical_gaps'] if g > MAX_GAP_SPECIAL]
        avg   = round(sum(hist_v) / len(hist_v), 1) if hist_v else 0.0

        # Fond alterné
        bg = C_LIGHT if getattr(cat_row, '_toggle', False) else C_WHITE
        cat_row._toggle = not getattr(cat_row, '_toggle', False)

        # Ligne titre catégorie
        pdf.set_fill_color(*bg)
        pdf.set_text_color(*C_DARK)
        pdf.set_font('Helvetica', 'B', 11)
        pdf.cell(0, 7, f'  {label}', fill=True,
                 new_x=XPos.LMARGIN, new_y=YPos.NEXT)

        # Ligne stats
        pdf.set_font('Helvetica', '', 10)
        pdf.set_fill_color(*bg)
        bar = _pdf_bar(app, total_g, 25)
        stats_line = (f"    Apparitions: {app}   |   Pourcentage: {pct}%   |   "
                      f"Ecart courant: {cur}   |   Max: {mx}   |   Moy: {avg}   |   "
                      f"Historique: {len(hist_v)} ecart(s)")
        pdf.multi_cell(0, 6, stats_line, fill=True,
                       new_x=XPos.LMARGIN, new_y=YPos.NEXT)

        # Barre de fréquence
        pdf.set_font('Courier', '', 9)
        pdf.set_fill_color(*bg)
        pdf.cell(0, 6, f'    {bar}  {pct}%', fill=True,
                 new_x=XPos.LMARGIN, new_y=YPos.NEXT)

        # Analyse écart courant
        pdf.set_font('Helvetica', 'I', 10)
        if total_g == 0:
            analysis = '    Pas encore de donnees.'
            pdf.set_text_color(*C_GRAY)
        elif cur == 0:
            analysis = '    OK - Present a la derniere partie.'
            pdf.set_text_color(*C_GREEN)
        elif cur > MAX_GAP_SPECIAL:
            analysis = f'    FAUX CHIFFRE - Absent depuis {cur} parties (depasse le seuil {MAX_GAP_SPECIAL}).'
            pdf.set_text_color(*C_RED)
        elif mx > 0 and cur >= mx * 0.8:
            analysis = (f'    ALERTE - Absent depuis {cur} parties '
                        f'({round(cur/mx*100)}% du max {mx}) - Retour imminent!')
            pdf.set_text_color(*C_RED)
        elif cur > avg > 0:
            analysis = f'    Attention - Absent depuis {cur} parties (moy: {avg}) - Au-dessus de la moyenne.'
            pdf.set_text_color(*C_ORANGE)
        else:
            analysis = f'    Normal - Absent depuis {cur} parties (moy: {avg}).'
            pdf.set_text_color(*C_DARK)
        pdf.set_fill_color(*bg)
        pdf.cell(0, 6, analysis, fill=True, new_x=XPos.LMARGIN, new_y=YPos.NEXT)

        # Faux chiffres
        if hist_f:
            pdf.set_text_color(*C_RED)
            faux_str = ', '.join(str(g) for g in sorted(hist_f, reverse=True)[:8])
            pdf.set_font('Helvetica', 'I', 9)
            pdf.cell(0, 6, f'    Faux chiffres exclus (>{MAX_GAP_SPECIAL}): {faux_str}',
                     fill=True, new_x=XPos.LMARGIN, new_y=YPos.NEXT)
        pdf.set_text_color(*C_DARK)
        pdf.ln(2)

    # ── Corps du document ─────────────────────────────────────────────────────
    if total_g == 0:
        pdf.set_font('Helvetica', 'I', 12)
        pdf.set_text_color(*C_GRAY)
        pdf.cell(0, 10, 'Aucune donnee disponible pour le moment.',
                 align='C', new_x=XPos.LMARGIN, new_y=YPos.NEXT)
    else:
        for grp_title, cats in GROUPS:
            section_header(grp_title)
            cat_row._toggle = False
            for cat in cats:
                cat_row(cat)
            pdf.ln(4)

    # ── Page 2 : Résumé TOP 10 des écarts (cycle #1 → #1440) ─────────────────
    pdf.add_page()

    # Titre de la page résumé
    pdf.set_fill_color(*C_DARK)
    pdf.rect(0, 0, 210, 32, 'F')
    pdf.set_text_color(*C_WHITE)
    pdf.set_font('Helvetica', 'B', 18)
    pdf.set_xy(10, 5)
    pdf.cell(190, 10, 'RESUME  -  TOP 10 DES ECARTS  -  CYCLE #1 a #1440',
             align='C', new_x=XPos.LMARGIN, new_y=YPos.NEXT)
    pdf.set_font('Helvetica', '', 10)
    pdf.set_xy(10, 17)
    pdf.cell(190, 8,
             f'Toutes categories confondues  |  Seuil faux chiffres: > {MAX_GAP_SPECIAL} parties  |  '
             f'{total_g} parties analysees',
             align='C', new_x=XPos.LMARGIN, new_y=YPos.NEXT)
    pdf.ln(14)

    # Collecter tous les écarts avec numéro de jeu
    LABELS_SHORT = {
        'joueur':'Victoire Joueur','banquier':'Victoire Banquier','tie':'Match Nul',
        'pair':'Pair Joueur','impair':'Impair Joueur',
        'pair_b':'Pair Banquier','impair_b':'Impair Banquier',
        '2k':'2K (joueur)','3k':'3K (joueur)',
        '3_2':'3K/2K','3_3':'3K/3K','2_3':'2K/3K','2_2':'2K/2K',
    }
    all_gaps = []
    for cat in SPECIAL_CATEGORIES:
        info = special_tracker[cat]
        label = LABELS_SHORT.get(cat, cat)
        # Écarts historiques clôturés
        for gap, g_num in info['gap_history_with_games']:
            all_gaps.append((gap, g_num, label, 'Clos'))
        # Écart courant non encore clôturé
        if info['current_gap'] > 0:
            all_gaps.append((info['current_gap'], 0, label, 'En cours'))

    # Trier par écart décroissant, prendre top 10
    top10 = sorted(all_gaps, key=lambda x: x[0], reverse=True)[:10]

    # ── Tableau ──────────────────────────────────────────────────────────────
    COL_W = [12, 60, 28, 35, 55]   # Rang | Catégorie | Écart | Partie # | Statut
    HEADERS = ['Rang', 'Categorie', 'Ecart', 'Partie #', 'Statut']

    def table_header_row():
        pdf.set_fill_color(*C_HEAD)
        pdf.set_text_color(*C_WHITE)
        pdf.set_font('Helvetica', 'B', 10)
        for i, h in enumerate(HEADERS):
            pdf.cell(COL_W[i], 9, h, border=1, fill=True, align='C')
        pdf.ln()

    def table_data_row(rank: int, gap: int, g_num: int, label: str, statut: str):
        is_faux = gap > MAX_GAP_SPECIAL
        bg = (255, 230, 230) if is_faux else (C_LIGHT if rank % 2 == 0 else C_WHITE)
        pdf.set_fill_color(*bg)
        pdf.set_text_color(*(C_RED if is_faux else C_DARK))
        pdf.set_font('Helvetica', 'B' if rank == 1 else '', 10)

        part_str = f'#{g_num}' if g_num > 0 else 'En cours'
        faux_mark = '  [FAUX]' if is_faux else ''
        statut_str = f'{statut}{faux_mark}'

        pdf.cell(COL_W[0], 8, str(rank), border=1, fill=True, align='C')
        pdf.cell(COL_W[1], 8, label, border=1, fill=True)
        pdf.cell(COL_W[2], 8, str(gap), border=1, fill=True, align='C')
        pdf.cell(COL_W[3], 8, part_str, border=1, fill=True, align='C')
        pdf.cell(COL_W[4], 8, statut_str, border=1, fill=True, align='C')
        pdf.ln()

    if not top10:
        pdf.set_font('Helvetica', 'I', 11)
        pdf.set_text_color(*C_GRAY)
        pdf.cell(0, 10, 'Aucun ecart enregistre pour ce cycle.', align='C',
                 new_x=XPos.LMARGIN, new_y=YPos.NEXT)
    else:
        table_header_row()
        for rank, (gap, g_num, label, statut) in enumerate(top10, 1):
            table_data_row(rank, gap, g_num, label, statut)
        pdf.ln(6)

        # Note faux chiffres
        nb_faux = sum(1 for g, _, _, _ in top10 if g > MAX_GAP_SPECIAL)
        if nb_faux > 0:
            pdf.set_font('Helvetica', 'I', 9)
            pdf.set_text_color(*C_RED)
            pdf.cell(0, 6,
                     f'* {nb_faux} entree(s) marquee(s) [FAUX] : ecart superieur au seuil {MAX_GAP_SPECIAL} parties.',
                     new_x=XPos.LMARGIN, new_y=YPos.NEXT)

        pdf.ln(4)

        # Sous-tableau par catégorie : max gap du cycle
        pdf.set_text_color(*C_DARK)
        pdf.set_fill_color(*C_HEAD)
        pdf.set_text_color(*C_WHITE)
        pdf.set_font('Helvetica', 'B', 11)
        pdf.cell(0, 8, '  ECART MAXIMUM PAR CATEGORIE  (cycle complet)',
                 fill=True, new_x=XPos.LMARGIN, new_y=YPos.NEXT)
        pdf.ln(2)

        COL_W2 = [60, 28, 35, 65]
        HEADERS2 = ['Categorie', 'Max ecart', 'Partie #', 'Statut ecart courant']
        pdf.set_fill_color(*C_HEAD)
        pdf.set_text_color(*C_WHITE)
        pdf.set_font('Helvetica', 'B', 10)
        for i, h in enumerate(HEADERS2):
            pdf.cell(COL_W2[i], 9, h, border=1, fill=True, align='C')
        pdf.ln()

        for idx, cat in enumerate(SPECIAL_CATEGORIES):
            info = special_tracker[cat]
            label = LABELS_SHORT.get(cat, cat)
            mx = info['max_gap']
            cur = info['current_gap']
            # Trouver le numéro de jeu du max
            mx_game = 0
            for gap, g_num in info['gap_history_with_games']:
                if gap == mx and mx > 0:
                    mx_game = g_num
                    break
            mx_part = f'#{mx_game}' if mx_game > 0 else ('En cours' if cur == mx and cur > 0 else 'N/A')

            if cur == 0:
                cur_str = 'Present a la derniere partie'
            elif cur > MAX_GAP_SPECIAL:
                cur_str = f'FAUX - absent {cur} parties'
            elif mx > 0 and cur >= mx * 0.8:
                cur_str = f'ALERTE - absent {cur} parties'
            else:
                cur_str = f'Absent {cur} parties'

            bg = C_LIGHT if idx % 2 == 0 else C_WHITE
            pdf.set_fill_color(*bg)
            faux_mx = mx > MAX_GAP_SPECIAL
            pdf.set_text_color(*(C_RED if faux_mx else C_DARK))
            pdf.set_font('Helvetica', '', 9)
            pdf.cell(COL_W2[0], 7, label, border=1, fill=True)
            pdf.cell(COL_W2[1], 7, f'{mx}{"*" if faux_mx else ""}', border=1, fill=True, align='C')
            pdf.cell(COL_W2[2], 7, mx_part, border=1, fill=True, align='C')
            pdf.set_text_color(*C_DARK)
            pdf.cell(COL_W2[3], 7, cur_str, border=1, fill=True)
            pdf.ln()

    # ── Pied de page (toutes les pages) ──────────────────────────────────────
    pdf.set_y(-20)
    pdf.set_fill_color(*C_DARK)
    pdf.rect(0, pdf.get_y(), 210, 20, 'F')
    pdf.set_text_color(*C_WHITE)
    pdf.set_font('Helvetica', '', 8)
    pdf.cell(0, 20,
             f'Baccarat AI  -  Rapport Special  -  {now.strftime("%d/%m/%Y %H:%M")} WAT  -  '
             f'{total_g} parties analysees  -  Cycle #1 a #1440',
             align='C', new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    pdf.output(path)


async def send_special_pdf_to_admins():
    """Génère le rapport spécial PDF et l'envoie à tous les admins en privé.
    Utilisé automatiquement au jeu #1440 et sur commande /special.
    """
    all_admin_ids = []
    if ADMIN_ID and ADMIN_ID != 0:
        all_admin_ids.append(ADMIN_ID)
    for aid in EXTRA_ADMIN_IDS:
        if aid not in all_admin_ids:
            all_admin_ids.append(aid)

    pdf_path = '/tmp/rapport_special_1440.pdf'
    loop = asyncio.get_event_loop()
    await loop.run_in_executor(None, generate_special_pdf, pdf_path)

    now_str = get_local_time().strftime('%d/%m/%Y %H:%M')
    _fg = cycle_first_game if cycle_first_game > 0 else 1
    _lg = current_game_number if current_game_number > 0 else special_games_processed
    caption = (
        f"📄 **Rapport Spécial — Baccarat AI**\n"
        f"🕐 {now_str} (WAT)\n"
        f"🎮 {special_games_processed} parties analysées | Plage: #{_fg} → #{_lg}\n\n"
        f"📋 Contenu:\n"
        f"  • Victoires Joueur / Banquier / Nul\n"
        f"  • Pair / Impair (total points joueur)\n"
        f"  • Pair / Impair (total points banquier)\n"
        f"  • Joueur 2K / 3K\n"
        f"  • Combinaisons 3/2 · 3/3 · 2/3 · 2/2\n"
        f"  • Top 10 ecarts avec numeros de partie\n\n"
        f"Seuil faux chiffres: > {MAX_GAP_SPECIAL} parties"
    )

    for admin_id in all_admin_ids:
        try:
            await client.send_file(
                admin_id,
                pdf_path,
                caption=caption,
                force_document=True,
                attributes=[],
            )
            logger.info(f"📄 Rapport spécial PDF envoyé à admin {admin_id}")
        except Exception as e:
            logger.error(f"❌ Erreur envoi PDF à admin {admin_id}: {e}")

    try:
        import os as _os
        _os.remove(pdf_path)
    except Exception:
        pass


async def cmd_special(event):
    """Envoie le rapport spécial en PDF sur commande /special (admin uniquement)."""
    if event.is_group or event.is_channel:
        return
    if not is_admin(event.sender_id):
        await event.respond("🔒 Admin uniquement")
        return

    if special_games_processed == 0:
        await event.respond(
            "❓ **Rapport Spécial**\n\n"
            "Pas encore de données — le bot n'a pas encore traité de parties complètes.\n"
            "Reviens dans quelques instants."
        )
        return

    await event.respond("⏳ Génération du rapport spécial en PDF...")

    pdf_path = f"/tmp/rapport_special_{event.sender_id}.pdf"
    try:
        loop = asyncio.get_event_loop()
        await loop.run_in_executor(None, generate_special_pdf, pdf_path)
        now_str = get_local_time().strftime('%d/%m/%Y %H:%M')
        _fg = cycle_first_game if cycle_first_game > 0 else 1
        await client.send_file(
            event.chat_id,
            pdf_path,
            caption=(
                f"📄 **Rapport Spécial — Baccarat AI**\n"
                f"🕐 {now_str} (WAT)\n"
                f"🎮 {special_games_processed} parties analysées | Plage: #{_fg} -> #{current_game_number}\n\n"
                f"📋 Victoires | Pair/Impair Joueur & Banquier | Cartes | Combinaisons\n"
                f"📊 Page 2 : Top 10 ecarts (#{_fg} -> #{current_game_number})\n\n"
                f"Seuil faux chiffres: > {MAX_GAP_SPECIAL} parties"
            ),
            force_document=True,
            attributes=[],
        )
        logger.info(f"📄 Rapport spécial PDF envoyé à {event.sender_id}")
    except Exception as e:
        logger.error(f"❌ Erreur génération PDF rapport spécial: {e}")
        await event.respond(f"❌ Erreur lors de la génération du PDF: {e}")
    finally:
        try:
            import os as _os
            _os.remove(pdf_path)
        except Exception:
            pass


# ============================================================================
# CONFIGURATION DES HANDLERS
# ============================================================================

def setup_handlers():
    client.add_event_handler(cmd_compteur2, events.NewMessage(pattern=r'^/compteur2'))
    client.add_event_handler(cmd_status, events.NewMessage(pattern=r'^/status$'))
    client.add_event_handler(cmd_history, events.NewMessage(pattern=r'^/history$'))
    client.add_event_handler(cmd_help, events.NewMessage(pattern=r'^/help$'))
    client.add_event_handler(cmd_reset, events.NewMessage(pattern=r'^/reset$'))
    client.add_event_handler(cmd_channels, events.NewMessage(pattern=r'^/channels$'))
    client.add_event_handler(cmd_test, events.NewMessage(pattern=r'^/test$'))
    client.add_event_handler(cmd_announce, events.NewMessage(pattern=r'^/announce'))
    client.add_event_handler(cmd_raison, events.NewMessage(pattern=r'^/raison'))
    client.add_event_handler(cmd_manquants, events.NewMessage(pattern=r'^/manquants$'))
    client.add_event_handler(cmd_rapport, events.NewMessage(pattern=r'^/rapport'))
    client.add_event_handler(cmd_special, events.NewMessage(pattern=r'^/special$'))

# ============================================================================
# DÉMARRAGE
# ============================================================================

async def start_bot():
    global client, prediction_channel_ok

    client = TelegramClient(StringSession(TELEGRAM_SESSION), API_ID, API_HASH)

    try:
        await client.start(bot_token=BOT_TOKEN)
        setup_handlers()

        if PREDICTION_CHANNEL_ID:
            try:
                pred_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
                if pred_entity:
                    prediction_channel_ok = True
                    logger.info(f"✅ Canal prédiction OK: {getattr(pred_entity, 'title', 'Unknown')}")
                else:
                    logger.error(f"❌ Canal prédiction inaccessible: {PREDICTION_CHANNEL_ID}")
            except Exception as e:
                logger.error(f"❌ Erreur vérification canal: {e}")

        logger.info(f"🤖 Bot démarré | Compteur2 BP={compteur2_bp} | FK={compteur2_fk}")
        logger.info(f"⏰ Reset horaire: chaque heure pile")
        logger.info(f"🔄 Reset automatique configuré: fin de la partie #1440")
        return True

    except Exception as e:
        logger.error(f"❌ Erreur démarrage: {e}")
        return False

async def main():
    try:
        if not await start_bot():
            return

        asyncio.create_task(api_polling_loop())
        asyncio.create_task(hourly_reset_task())
        asyncio.create_task(rapport_task_loop())
        logger.info("🔄 Polling API dynamique démarré")
        logger.info("⏰ Tâche de reset horaire démarrée")
        logger.info("📊 Tâche de rapport automatique démarrée")

        app = web.Application()
        app.router.add_get('/health', lambda r: web.Response(text="OK"))
        app.router.add_get('/', lambda r: web.Response(text="BACCARAT PREMIUM+2 🎲 Running"))

        runner = web.AppRunner(app)
        await runner.setup()
        site = web.TCPSite(runner, '0.0.0.0', PORT)
        await site.start()

        logger.info(f"🌐 Serveur web démarré sur port {PORT}")

        await client.run_until_disconnected()

    except Exception as e:
        logger.error(f"❌ Erreur main: {e}")
    finally:
        if client and client.is_connected():
            await client.disconnect()
            logger.info("🔌 Déconnecté")

if __name__ == '__main__':
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        logger.info("Arrêté par l'utilisateur")
    except Exception as e:
        logger.error(f"Fatal: {e}")
        sys.exit(1)
