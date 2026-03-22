import requests
import json


API_URL = "https://1xbet.com/service-api/LiveFeed/GetSportsShortZip"
API_PARAMS = {
    "sports": 236,
    "champs": 2050671,
    "lng": "en",
    "gr": 285,
    "country": 96,
    "virtualSports": "true",
    "groupChamps": "true"
}
API_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/120.0.0.0 Safari/537.36",
    "Accept": "application/json",
    "Referer": "https://1xbet.com/",
}

SUIT_MAP = {0: "♠️", 1: "♣️", 2: "♦️", 3: "♥️"}


def _parse_cards(sc_s_list):
    """
    Extrait les cartes joueur et banquier depuis le champ SC.S du jeu.
    sc_s_list = [{"Key":"P","Value":"[{...}]"}, {"Key":"B","Value":"[{...}]"}, ...]
    Retourne (player_cards, banker_cards) sous forme de listes [{S, R}, ...]
    """
    player_cards = []
    banker_cards = []
    for entry in sc_s_list:
        key = entry.get("Key", "")
        val = entry.get("Value", "[]")
        try:
            cards = json.loads(val)
        except Exception:
            cards = []
        if key == "P":
            player_cards = cards
        elif key == "B":
            banker_cards = cards
    return player_cards, banker_cards


def _parse_winner(sc_s_list):
    """Retourne 'Player', 'Banker', 'Tie' ou None."""
    for entry in sc_s_list:
        if entry.get("Key") == "S":
            val = entry.get("Value", "")
            if val == "Win1":
                return "Player"
            elif val == "Win2":
                return "Banker"
            elif val == "Tie":
                return "Tie"
    return None


def get_latest_results():
    """
    Récupère les derniers résultats de Baccara depuis l'API 1xBet.
    Structure réelle de l'API :
      data["Value"] → liste de sports
        sport["L"]  → liste de championnats
          champ["G"] → liste de jeux
    """
    try:
        response = requests.get(API_URL, params=API_PARAMS, headers=API_HEADERS, timeout=30)
        data = response.json()

        if "Value" not in data or not isinstance(data["Value"], list):
            return []

        baccara_sport = None
        for sport in data["Value"]:
            if sport.get("N") == "Baccarat" or sport.get("I") == 236:
                if "L" in sport:
                    baccara_sport = sport
                    break

        if baccara_sport is None:
            return []

        results = []

        for championship in baccara_sport["L"]:
            games = championship.get("G", [])
            for game in games:
                if "DI" not in game:
                    continue

                game_number = int(game["DI"])
                sc = game.get("SC", {})
                sc_s = sc.get("S", [])

                is_finished = game.get("F", False) or sc.get("CPS") == "Match finished"

                player_cards, banker_cards = _parse_cards(sc_s)
                winner = _parse_winner(sc_s)

                def fmt_cards(cards):
                    return [{"S": SUIT_MAP.get(c.get("S"), "?"), "R": c.get("R", "?"), "raw": c.get("S", -1)} for c in cards]

                result = {
                    "game_number": game_number,
                    "player_cards": fmt_cards(player_cards),
                    "banker_cards": fmt_cards(banker_cards),
                    "winner": winner,
                    "is_finished": is_finished,
                    "score": sc.get("FS", {}),
                }
                results.append(result)

        return results

    except Exception as e:
        import traceback
        traceback.print_exc()

    return []


def update_history(results, history):
    """Met à jour l'historique avec les jeux terminés."""
    for result in results:
        if result["is_finished"]:
            game_number = result["game_number"]
            new_entry = {
                "player_cards": result["player_cards"],
                "banker_cards": result["banker_cards"],
                "winner": result.get("winner"),
                "score": result.get("score"),
                "is_finished": True
            }
            if game_number not in history:
                history[game_number] = new_entry
            else:
                old = history[game_number]
                old_b = len(old.get("banker_cards", []))
                new_b = len(result["banker_cards"])
                if new_b > old_b:
                    history[game_number] = new_entry
    return history
