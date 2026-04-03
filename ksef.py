"""
KSeF Desktop - Obsługa Krajowego Systemu e-Faktur
Aplikacja desktopowa z interfejsem graficznym (tkinter)
"""

import tkinter as tk
from tkinter import ttk, messagebox, filedialog, scrolledtext
import threading
import json
import os
import sys
import datetime
import base64
import hashlib
import xml.etree.ElementTree as ET
from pathlib import Path
import configparser
import re

# ── Opcjonalne importy sieciowe ──────────────────────────────────────────────
try:
    import requests
    HAS_REQUESTS = True
except ImportError:
    HAS_REQUESTS = False

try:
    from cryptography.hazmat.primitives.asymmetric import padding as _crypto_padding
    HAS_CRYPTO = True
except ImportError:
    HAS_CRYPTO = False

# ── Stałe ────────────────────────────────────────────────────────────────────
APP_NAME    = "KSeF Desktop"
APP_VERSION = "1.0.0"
COLOR_BG        = "#0f1117"
COLOR_PANEL     = "#1a1d27"
COLOR_CARD      = "#22263a"
COLOR_BORDER    = "#2d3250"
COLOR_ACCENT    = "#4f8ef7"
COLOR_ACCENT2   = "#7b5ea7"
COLOR_SUCCESS   = "#2ecc71"
COLOR_WARNING   = "#f39c12"
COLOR_ERROR     = "#e74c3c"
COLOR_TEXT      = "#e8eaf6"
COLOR_MUTED     = "#8892b0"
COLOR_HOVER     = "#2d3250"

FONT_TITLE   = ("Segoe UI", 20, "bold")
FONT_HEADING = ("Segoe UI", 13, "bold")
FONT_BODY    = ("Segoe UI", 10)
FONT_SMALL   = ("Segoe UI", 9)
FONT_MONO    = ("Consolas", 9)

# KSeF 2.0 – nowe adresy od 1 lutego 2026
API_ENDPOINTS = {
    "integracyjne": "https://api-test.ksef.mf.gov.pl/v2",
    "demo":         "https://api-demo.ksef.mf.gov.pl/v2",
    "produkcja":    "https://api.ksef.mf.gov.pl/v2",
}

CONFIG_FILE = os.path.join(os.path.expanduser("~"), ".ksef_desktop.ini")


# ════════════════════════════════════════════════════════════════════════════
#  FUNKCJE POMOCNICZE DO ESCAPOWANIA XML
# ════════════════════════════════════════════════════════════════════════════
def escape_xml(text: str) -> str:
    """Escapuje znaki specjalne w XML."""
    if not text:
        return text
    return (text.replace('&', '&amp;')
                .replace('<', '&lt;')
                .replace('>', '&gt;')
                .replace('"', '&quot;')
                .replace("'", '&apos;'))


# ════════════════════════════════════════════════════════════════════════════
#  KONFIGURACJA
# ════════════════════════════════════════════════════════════════════════════
class Config:
    def __init__(self):
        self.cfg = configparser.ConfigParser()
        self._defaults()
        self.load()

    def _defaults(self):
        self.cfg["ksef"] = {
            "environment": "integracyjne",
            "nip": "",
            "token": "",
        }
        self.cfg["ui"] = {"theme": "dark"}

    def load(self):
        if os.path.exists(CONFIG_FILE):
            self.cfg.read(CONFIG_FILE, encoding="utf-8")

    def save(self):
        with open(CONFIG_FILE, "w", encoding="utf-8") as f:
            self.cfg.write(f)

    def get(self, section, key, fallback=""):
        return self.cfg.get(section, key, fallback=fallback)

    def set(self, section, key, value):
        if section not in self.cfg:
            self.cfg[section] = {}
        self.cfg[section][key] = str(value)


# ════════════════════════════════════════════════════════════════════════════
#  KLIENT KSEF API
# ════════════════════════════════════════════════════════════════════════════
class KSeFClient:
    """Prosty klient REST dla KSeF API."""

    def __init__(self, env: str = "integracyjne"):
        self.base_url      = API_ENDPOINTS.get(env, API_ENDPOINTS["integracyjne"])
        self.token         = None   # token autoryzacyjny (API key z podatki.gov.pl)
        self.access_token  = None   # JWT Bearer – ważny ~5 min
        self.refresh_token = None   # JWT Refresh – ważny dłużej
        self.session_ref   = None   # numer referencyjny sesji
        self._aes_key      = None   # klucz AES-256 (32 bajty) do szyfrowania faktur
        self._aes_iv       = None   # wektor IV (16 bajtów)

    # ── helpers ─────────────────────────────────────────────────────────────
    def _headers(self, extra: dict | None = None) -> dict:
        # KSeF 2.0: Bearer JWT zamiast SessionToken
        h = {"Content-Type": "application/json", "Accept": "application/json"}
        if self.access_token:
            h["Authorization"] = f"Bearer {self.access_token}"
        if extra:
            h.update(extra)
        return h

    def _get(self, path: str) -> dict:
        if not HAS_REQUESTS:
            raise RuntimeError("Brak biblioteki 'requests'. Zainstaluj: pip install requests")
        r = requests.get(f"{self.base_url}{path}", headers=self._headers(), timeout=30)
        r.raise_for_status()
        return r.json()

    def _post(self, path: str, payload: dict | str, raw: bool = False,
              extra_headers: dict | None = None) -> dict:
        if not HAS_REQUESTS:
            raise RuntimeError("Brak biblioteki 'requests'. Zainstaluj: pip install requests")
        headers = self._headers(extra_headers)

        # Dla KSeF 2.0 - dodaj referencję sesji jeśli istnieje
        if self.session_ref and "invoices" in path:
            headers["X-KSEF-ReferenceNumber"] = self.session_ref

        if raw:
            headers["Content-Type"] = "application/octet-stream"
            r = requests.post(f"{self.base_url}{path}", headers=headers,
                              data=payload, timeout=60)
        else:
            r = requests.post(f"{self.base_url}{path}", headers=headers,
                              json=payload, timeout=60)

        # Lepsza obsługa błędów
        if r.status_code >= 400:
            error_msg = f"HTTP {r.status_code}: {r.text}"
            raise RuntimeError(error_msg)

        try:
            return r.json()
        except Exception:
            return {"status": r.status_code, "raw": r.text}

    # ── autoryzacja KSeF 2.0 – token KSeF z szyfrowaniem RSA-OAEP ──────────
    def _get_public_key_cert(self, usage: str = "KsefTokenEncryption") -> bytes:
        """
        Pobiera certyfikat klucza publicznego KSeF.
        usage: 'KsefTokenEncryption'      – do szyfrowania tokenu autoryzacyjnego
               'SymmetricKeyEncryption'    – do szyfrowania klucza AES sesji online
        """
        result = self._get("/security/public-key-certificates")
        items = result if isinstance(result, list) else result.get("items", [])

        # Szukaj certyfikatu z odpowiednim usage
        for cert_info in items:
            usages = cert_info.get("usage", [])
            if usage in usages:
                cert_b64 = cert_info.get("certificate", "")
                if cert_b64:
                    return base64.b64decode(cert_b64)

        # Fallback: pierwszy dostępny certyfikat
        if items:
            cert_b64 = items[0].get("certificate", "")
            if cert_b64:
                return base64.b64decode(cert_b64)
        raise RuntimeError(f"Nie znaleziono certyfikatu ({usage}): {result}")

    def _encrypt_token(self, token: str, cert_der: bytes,
                        challenge_ts=None) -> str:
        """
        Szyfruje token algorytmem RSA-OAEP/SHA-256/MGF1.
        Format: 'token|timestamp_ms'
        challenge_ts: int (ms bezpośrednio z timestampMs) lub str ISO 8601
        """
        try:
            from cryptography.hazmat.primitives.asymmetric import padding
            from cryptography.hazmat.primitives import hashes
            from cryptography.x509 import load_der_x509_certificate
        except ImportError:
            raise RuntimeError(
                "Brak biblioteki cryptography. Zainstaluj: pip install cryptography"
            )
        # Ustal timestamp_ms z pola challenge
        if isinstance(challenge_ts, int) and challenge_ts > 0:
            ts_ms = challenge_ts          # timestampMs – gotowa wartość
        elif isinstance(challenge_ts, str) and challenge_ts:
            try:
                ts_clean = challenge_ts.replace("Z", "+00:00")
                import re as _re
                ts_clean = _re.sub(r'(\.\d{6})\d+', r'\1', ts_clean)
                ts_dt = datetime.datetime.fromisoformat(ts_clean)
                ts_ms = int(ts_dt.timestamp() * 1000)
            except Exception:
                ts_ms = int(datetime.datetime.now(datetime.timezone.utc).timestamp() * 1000)
        else:
            ts_ms = int(datetime.datetime.now(datetime.timezone.utc).timestamp() * 1000)
        plaintext = f"{token}|{ts_ms}".encode("utf-8")
        cert      = load_der_x509_certificate(cert_der)
        pub_key   = cert.public_key()
        encrypted = pub_key.encrypt(
            plaintext,
            padding.OAEP(
                mgf=padding.MGF1(algorithm=hashes.SHA256()),
                algorithm=hashes.SHA256(),
                label=None,
            ),
        )
        return base64.b64encode(encrypted).decode("ascii")

    def init_session_token(self, nip: str, auth_token: str) -> dict:
        """
        KSeF 2.0 – autoryzacja tokenem KSeF (z MCU / ksef.podatki.gov.pl):

          1. GET  /security/public-key-certificates → klucz RSA do szyfrowania
          2. POST /auth/challenge                   → {challenge}
          3. Szyfruj: RSA-OAEP(token|timestamp_ms) → encryptedToken (Base64)
          4. POST /auth/ksef-token                  → {authenticationToken, referenceNumber}
          5. GET  /auth/{referenceNumber}  (polling) → status 200 = sukces
          6. POST /auth/token/redeem                → {accessToken, refreshToken}
        """
        import time

        # Krok 1: klucz publiczny do szyfrowania tokenu
        cert_der = self._get_public_key_cert("KsefTokenEncryption")

        # Krok 2: challenge
        ch_result = self._post("/auth/challenge", {})
        challenge = ch_result.get("challenge")
        if not challenge:
            raise RuntimeError(f"Brak challenge: {ch_result}")

        # Krok 3: zaszyfruj token RSA-OAEP
        # KSeF 2.0 zwraca timestampMs (int, ms od epoch) – używamy bezpośrednio
        ts_ms = ch_result.get("timestampMs") or ch_result.get("timestamp_ms")
        if not ts_ms:
            # fallback: sparsuj pole "timestamp" ISO 8601
            ts_ms = ch_result.get("timestamp", "")
        encrypted_token = self._encrypt_token(auth_token, cert_der, ts_ms)

        # Krok 4: wyślij token KSeF
        ksef_result = self._post("/auth/ksef-token", {
            "challenge": challenge,
            "contextIdentifier": {
                "type": "Nip",
                "value": nip,
            },
            "encryptedToken":      encrypted_token,
            "authorizationPolicy": None,
        })
        ref    = ksef_result.get("referenceNumber")
        tmp_tk = (ksef_result.get("authenticationToken") or {}).get("token") or                  ksef_result.get("authenticationToken")
        if not ref:
            raise RuntimeError(f"Brak referenceNumber: {ksef_result}")
        self.session_ref = ref

        # Krok 5: odpytuj status (max 30 s)
        for _ in range(15):
            time.sleep(2)
            status_r = requests.get(
                f"{self.base_url}/auth/{ref}",
                headers={"Authorization": f"Bearer {tmp_tk}"} if tmp_tk else {},
                timeout=15,
            )
            if status_r.status_code == 200:
                sr = status_r.json()
                status_code = (sr.get("status") or {}).get("code", 0)
                if status_code == 200:
                    tmp_tk = (sr.get("authenticationToken") or {}).get("token") or tmp_tk
                    break
                if status_code >= 300:
                    raise RuntimeError(f"Błąd autoryzacji {status_code}: {sr}")

        # Krok 6: wymień authenticationToken na accessToken + refreshToken
        redeem_r = requests.post(
            f"{self.base_url}/auth/token/redeem",
            headers={"Authorization": f"Bearer {tmp_tk}", "Content-Type": "application/json"},
            json={},
            timeout=30,
        )
        redeem_r.raise_for_status()
        redeem = redeem_r.json()
        self.access_token  = (redeem.get("accessToken")  or {}).get("token") or redeem.get("accessToken")
        self.refresh_token = (redeem.get("refreshToken") or {}).get("token") or redeem.get("refreshToken")
        if not self.access_token:
            raise RuntimeError(f"Brak accessToken po redeem: {redeem}")
        return redeem

    def open_online_session(self, form_code: str = "FA",
                            schema_version: str = "1-0E",
                            system_code: str = "FA (3)") -> dict:
        """
        POST /sessions/online – otwiera sesję interaktywną KSeF 2.0.

        Generuje losowy klucz AES-256 + IV, szyfruje klucz kluczem publicznym MF
        (RSA-OAEP/SHA-256) i wysyła do API.  Klucz AES jest potem używany
        do szyfrowania faktur przed wysyłką.
        """
        try:
            from cryptography.hazmat.primitives.asymmetric import padding as asym_padding
            from cryptography.hazmat.primitives import hashes
            from cryptography.x509 import load_der_x509_certificate
        except ImportError:
            raise RuntimeError("Brak biblioteki 'cryptography'. Zainstaluj: pip install cryptography")

        # 1. Wygeneruj losowy klucz AES-256 (32 B) i IV (16 B)
        self._aes_key = os.urandom(32)
        self._aes_iv  = os.urandom(16)

        # 2. Pobierz klucz publiczny MF do szyfrowania klucza symetrycznego
        cert_der = self._get_public_key_cert("SymmetricKeyEncryption")
        cert     = load_der_x509_certificate(cert_der)
        pub_key  = cert.public_key()
        encrypted_key = pub_key.encrypt(
            self._aes_key,
            asym_padding.OAEP(
                mgf=asym_padding.MGF1(algorithm=hashes.SHA256()),
                algorithm=hashes.SHA256(),
                label=None,
            ),
        )

        # 3. POST /sessions/online
        payload = {
            "formCode": {
                "systemCode":    system_code,
                "schemaVersion": schema_version,
                "value":         form_code,
            },
            "encryption": {
                "encryptedSymmetricKey": base64.b64encode(encrypted_key).decode(),
                "initializationVector":  base64.b64encode(self._aes_iv).decode(),
            },
        }
        result = self._post("/sessions/online", payload)
        self.session_ref = result.get("referenceNumber")
        if not self.session_ref:
            raise RuntimeError(f"Brak referenceNumber z /sessions/online: {result}")
        return result

    def close_online_session(self) -> dict:
        """POST /sessions/online/{ref}/close – zamyka sesję interaktywną."""
        if not self.session_ref:
            raise RuntimeError("Brak aktywnej sesji.")
        result = self._post(f"/sessions/online/{self.session_ref}/close", {})
        self.session_ref = None
        self._aes_key    = None
        self._aes_iv     = None
        return result

    def _encrypt_aes(self, data: bytes) -> bytes:
        """Szyfruje dane AES-256-CBC z PKCS#7 padding."""
        try:
            from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
            from cryptography.hazmat.primitives import padding as sym_padding
        except ImportError:
            raise RuntimeError("Brak 'cryptography'.")
        if not self._aes_key or not self._aes_iv:
            raise RuntimeError("Brak klucza AES – najpierw otwórz sesję online.")
        padder = sym_padding.PKCS7(128).padder()
        padded = padder.update(data) + padder.finalize()
        cipher = Cipher(algorithms.AES(self._aes_key), modes.CBC(self._aes_iv))
        enc    = cipher.encryptor()
        return enc.update(padded) + enc.finalize()

    def refresh_access_token(self) -> dict:
        """POST /auth/token/refresh – odświeża JWT używając refreshToken."""
        if not self.refresh_token:
            raise RuntimeError("Brak refresh tokena – najpierw zaloguj się.")
        old_at = self.access_token
        self.access_token = self.refresh_token   # tymczasowo bearer = refresh
        result = self._post("/auth/token/refresh", {})
        self.access_token  = result.get("accessToken", old_at)
        self.refresh_token = result.get("refreshToken", self.refresh_token)
        return result

    def terminate_session(self) -> dict:
        """DELETE /auth/sessions/current – unieważnia bieżącą sesję."""
        if not HAS_REQUESTS:
            raise RuntimeError("Brak 'requests'")
        r = requests.delete(
            f"{self.base_url}/auth/sessions/current",
            headers=self._headers(), timeout=30
        )
        self.access_token  = None
        self.refresh_token = None
        self.session_ref   = None
        return {"status": r.status_code}

    # ── faktury KSeF 2.0 ────────────────────────────────────────────────────
    def send_invoice(self, xml_content: str) -> dict:
        """POST /sessions/online/{ref}/invoices – wysyłka zaszyfrowanej faktury."""
        if not self.session_ref:
            raise RuntimeError("Brak aktywnej sesji KSeF. Najpierw otwórz sesję w zakładce 'Sesja'.")
        if not self._aes_key:
            raise RuntimeError("Brak klucza AES – otwórz sesję online ponownie.")

        # Oryginalna faktura
        xml_bytes       = xml_content.encode("utf-8")
        invoice_hash    = base64.b64encode(hashlib.sha256(xml_bytes).digest()).decode()
        invoice_size    = len(xml_bytes)

        # Zaszyfrowana faktura (AES-256-CBC, PKCS#7)
        encrypted_bytes = self._encrypt_aes(xml_bytes)
        enc_hash        = base64.b64encode(hashlib.sha256(encrypted_bytes).digest()).decode()
        enc_size        = len(encrypted_bytes)
        enc_b64         = base64.b64encode(encrypted_bytes).decode()

        payload = {
            "invoiceHash":             invoice_hash,
            "invoiceSize":             invoice_size,
            "encryptedInvoiceHash":    enc_hash,
            "encryptedInvoiceSize":    enc_size,
            "encryptedInvoiceContent": enc_b64,
        }
        return self._post(f"/sessions/online/{self.session_ref}/invoices", payload)

    def check_invoice_status(self, reference_no: str) -> dict:
        """GET /sessions/{sessionRef}/invoices/{referenceNumber}"""
        if not self.session_ref:
            raise RuntimeError("Brak aktywnej sesji KSeF.")
        return self._get(f"/sessions/{self.session_ref}/invoices/{reference_no}")

    def query_invoices(self, date_from: str, date_to: str,
                       subject_type: str = "subject1") -> dict:
        """GET /sessions/{sessionRef}/invoices – wyszukiwanie faktur w sesji KSeF 2.0."""
        if not self.session_ref:
            raise RuntimeError("Brak aktywnej sesji KSeF.")
        return self._get(f"/sessions/{self.session_ref}/invoices")

    def download_invoice(self, ksef_ref: str) -> dict:
        """GET /sessions/{sessionRef}/invoices/{ksefReferenceNumber} – pobranie faktury."""
        if not self.session_ref:
            raise RuntimeError("Brak aktywnej sesji KSeF.")
        return self._get(f"/sessions/{self.session_ref}/invoices/{ksef_ref}")

    def get_upo(self, reference_no: str) -> dict:
        """GET /sessions/{sessionRef}/invoices/{referenceNumber}/upo – pobranie UPO."""
        if not self.session_ref:
            raise RuntimeError("Brak aktywnej sesji KSeF.")
        return self._get(f"/sessions/{self.session_ref}/invoices/{reference_no}/upo")

    def validate_invoice(self, xml_content: str) -> dict:
        """POST /sessions/online/{ref}/invoices/validate – walidacja XML bez wysyłki."""
        if not self.session_ref:
            raise RuntimeError("Brak aktywnej sesji KSeF.")
        xml_bytes = xml_content.encode("utf-8")
        b64 = base64.b64encode(xml_bytes).decode()
        return self._post(f"/sessions/online/{self.session_ref}/invoices/validate",
                          {"invoiceBody": b64})

    def check_connection(self) -> bool:
        try:
            # GET /security/public-key-certificates – publiczny endpoint (bez auth)
            r = requests.get(f"{self.base_url}/security/public-key-certificates",
                             timeout=10)
            return r.status_code < 500
        except Exception:
            return False


# ════════════════════════════════════════════════════════════════════════════
#  WIDŻETY POMOCNICZE
# ════════════════════════════════════════════════════════════════════════════
class Card(tk.Frame):
    def __init__(self, parent, title="", **kw):
        super().__init__(parent, bg=COLOR_CARD, bd=0, highlightthickness=1,
                         highlightbackground=COLOR_BORDER, **kw)
        if title:
            tk.Label(self, text=title, font=FONT_HEADING, bg=COLOR_CARD,
                     fg=COLOR_ACCENT).pack(anchor="w", padx=18, pady=(14, 4))
            ttk.Separator(self).pack(fill="x", padx=14, pady=(0, 8))
        self.body = tk.Frame(self, bg=COLOR_CARD)
        self.body.pack(fill="both", expand=True)


class FlatButton(tk.Label):
    def __init__(self, parent, text, command=None, color=COLOR_ACCENT,
                 width=None, **kw):
        super().__init__(parent, text=text, font=("Segoe UI", 10, "bold"),
                         bg=color, fg="white", cursor="hand2",
                         padx=20, pady=8, relief="flat", **kw)
        if width:
            self.config(width=width)
        self._cmd   = command
        self._color = color
        self.bind("<Button-1>", lambda e: command() if command else None)
        self.bind("<Enter>", lambda e: self.config(bg=self._darken(color)))
        self.bind("<Leave>", lambda e: self.config(bg=color))

    @staticmethod
    def _darken(hex_color: str) -> str:
        c = hex_color.lstrip("#")
        if len(c) != 6:
            return hex_color
        try:
            r, g, b = int(c[0:2], 16), int(c[2:4], 16), int(c[4:6], 16)
        except ValueError:
            return hex_color
        return "#{:02x}{:02x}{:02x}".format(max(r-30, 0), max(g-30, 0), max(b-30, 0))


class StatusBar(tk.Frame):
    def __init__(self, parent, **kw):
        super().__init__(parent, bg=COLOR_PANEL, height=28, **kw)
        self._label = tk.Label(self, text="Gotowy", font=FONT_SMALL,
                               bg=COLOR_PANEL, fg=COLOR_MUTED)
        self._label.pack(side="left", padx=10)
        self._dot = tk.Label(self, text="●", font=FONT_SMALL,
                             bg=COLOR_PANEL, fg=COLOR_ERROR)
        self._dot.pack(side="right", padx=10)
        self._env_lbl = tk.Label(self, text="środowisko: test",
                                 font=FONT_SMALL, bg=COLOR_PANEL, fg=COLOR_MUTED)
        self._env_lbl.pack(side="right", padx=4)

    def set(self, msg: str, kind: str = "info"):
        colors = {"info": COLOR_MUTED, "ok": COLOR_SUCCESS,
                  "warn": COLOR_WARNING, "error": COLOR_ERROR}
        self._label.config(text=msg, fg=colors.get(kind, COLOR_MUTED))

    def set_connected(self, ok: bool, env: str = "test"):
        self._dot.config(fg=COLOR_SUCCESS if ok else COLOR_ERROR)
        status = "połączono" if ok else "rozłączono"
        self._env_lbl.config(text=f"{status} · {env}")


class LogBox(tk.Frame):
    def __init__(self, parent, **kw):
        super().__init__(parent, bg=COLOR_CARD, **kw)
        self.text = scrolledtext.ScrolledText(
            self, font=FONT_MONO, bg="#0a0d14", fg=COLOR_TEXT,
            insertbackground=COLOR_ACCENT, relief="flat", bd=0, wrap="word",
            state="disabled"
        )
        self.text.pack(fill="both", expand=True, padx=2, pady=2)
        self.text.tag_config("ok",    foreground=COLOR_SUCCESS)
        self.text.tag_config("warn",  foreground=COLOR_WARNING)
        self.text.tag_config("error", foreground=COLOR_ERROR)
        self.text.tag_config("info",  foreground=COLOR_ACCENT)
        self.text.tag_config("dim",   foreground=COLOR_MUTED)

    def log(self, msg: str, kind: str = ""):
        ts = datetime.datetime.now().strftime("%H:%M:%S")
        self.text.config(state="normal")
        self.text.insert("end", f"[{ts}] ", "dim")
        self.text.insert("end", msg + "\n", kind or "")
        self.text.see("end")
        self.text.config(state="disabled")

    def clear(self):
        self.text.config(state="normal")
        self.text.delete("1.0", "end")
        self.text.config(state="disabled")


def labeled(parent, text: str, row: int, col: int = 0) -> tk.Label:
    lbl = tk.Label(parent, text=text, font=FONT_BODY, bg=COLOR_CARD,
                   fg=COLOR_MUTED, anchor="w")
    lbl.grid(row=row, column=col, sticky="w", padx=(16, 8), pady=5)
    return lbl


def entry(parent, row: int, col: int = 1, width: int = 40, show: str = "",
          **kw) -> tk.Entry:
    e = tk.Entry(parent, font=FONT_BODY, bg=COLOR_BG, fg=COLOR_TEXT,
                 insertbackground=COLOR_ACCENT, relief="flat", bd=4,
                 width=width, show=show, **kw)
    e.grid(row=row, column=col, sticky="ew", padx=(0, 16), pady=5)
    return e


# ════════════════════════════════════════════════════════════════════════════
#  ZAKŁADKA – PULPIT
# ════════════════════════════════════════════════════════════════════════════
class DashboardTab(tk.Frame):
    def __init__(self, parent, app):
        super().__init__(parent, bg=COLOR_BG)
        self.app = app
        self._build()

    def _build(self):
        # Nagłówek
        hdr = tk.Frame(self, bg=COLOR_BG)
        hdr.pack(fill="x", padx=24, pady=(24, 12))
        tk.Label(hdr, text=f"  KSeF Desktop", font=FONT_TITLE,
                 bg=COLOR_BG, fg=COLOR_TEXT).pack(side="left")
        tk.Label(hdr, text=f"v{APP_VERSION}", font=FONT_SMALL,
                 bg=COLOR_BG, fg=COLOR_MUTED).pack(side="left", padx=8, pady=8)

        # Karty statystyk
        stats = tk.Frame(self, bg=COLOR_BG)
        stats.pack(fill="x", padx=24, pady=8)
        self._stat_cards = {}
        for i, (label, val, color) in enumerate([
            ("Aktywna sesja", "Brak", COLOR_WARNING),
            ("Środowisko", "test", COLOR_ACCENT),
            ("NIP", "—", COLOR_TEXT),
            ("Stan API", "nieznany", COLOR_MUTED),
        ]):
            c = tk.Frame(stats, bg=COLOR_CARD, bd=0, highlightthickness=1,
                         highlightbackground=COLOR_BORDER)
            c.grid(row=0, column=i, padx=6, pady=4, sticky="nsew", ipadx=16, ipady=12)
            stats.columnconfigure(i, weight=1)
            tk.Label(c, text=label, font=FONT_SMALL, bg=COLOR_CARD,
                     fg=COLOR_MUTED).pack(anchor="w", padx=12, pady=(10, 0))
            lbl = tk.Label(c, text=val, font=("Segoe UI", 14, "bold"),
                           bg=COLOR_CARD, fg=color)
            lbl.pack(anchor="w", padx=12, pady=(2, 10))
            self._stat_cards[label] = lbl

        # Szybkie akcje
        qa = Card(self, title="⚡  Szybkie akcje")
        qa.pack(fill="x", padx=24, pady=10)
        row = tk.Frame(qa.body, bg=COLOR_CARD)
        row.pack(padx=16, pady=12)
        btns = [
            ("  Wyślij fakturę", self._goto_send,  COLOR_ACCENT),
            ("  Konwerter CR→FA(3)", self._goto_conv, "#2e5070"),
            ("  Pobierz faktury", self._goto_recv, COLOR_ACCENT2),
            ("  Sprawdź status", self._goto_status, "#2e7d52"),
            ("  Sesja", self._goto_auth, "#7d4e2e"),
        ]
        for txt, cmd, col in btns:
            FlatButton(row, text=txt, command=cmd, color=col).pack(
                side="left", padx=6)

        # Log zdarzeń
        log_card = Card(self, title="  Dziennik zdarzeń")
        log_card.pack(fill="both", expand=True, padx=24, pady=(4, 12))
        self.log = LogBox(log_card.body)
        self.log.pack(fill="both", expand=True, padx=12, pady=(0, 12))

        self.log.log("Aplikacja uruchomiona. Skonfiguruj połączenie w zakładce 'Ustawienia'.", "info")
        if not HAS_REQUESTS:
            self.log.log("UWAGA: brak 'requests' – zainstaluj: pip install requests cryptography", "error")
        if not HAS_CRYPTO:
            self.log.log("UWAGA: brak 'cryptography' – autoryzacja KSeF 2.0 niedostępna!", "error")
            self.log.log("       Zainstaluj: pip install cryptography", "warn")

    def update_stats(self, **kw):
        mapping = {
            "session":     "Aktywna sesja",
            "environment": "Środowisko",
            "nip":         "NIP",
            "api_status":  "Stan API",
        }
        colors = {
            "session":     {True: COLOR_SUCCESS, False: COLOR_WARNING},
        }
        for k, v in kw.items():
            label = mapping.get(k, k)
            if label in self._stat_cards:
                lbl = self._stat_cards[label]
                lbl.config(text=str(v))
                if k == "session":
                    lbl.config(fg=COLOR_SUCCESS if v != "Brak" else COLOR_WARNING)
                elif k == "api_status":
                    lbl.config(fg=COLOR_SUCCESS if v == "OK" else COLOR_ERROR)

    def _goto_send(self):   self.app.show_tab("Wyślij")
    def _goto_conv(self):   self.app.show_tab("Konwerter")
    def _goto_recv(self):   self.app.show_tab("Odebrane")
    def _goto_status(self): self.app.show_tab("Status")
    def _goto_auth(self):   self.app.show_tab("Sesja")


# ════════════════════════════════════════════════════════════════════════════
#  ZAKŁADKA – SESJA / AUTORYZACJA
# ════════════════════════════════════════════════════════════════════════════
class SessionTab(tk.Frame):
    def __init__(self, parent, app):
        super().__init__(parent, bg=COLOR_BG)
        self.app = app
        self._build()

    def _build(self):
        wrap = tk.Frame(self, bg=COLOR_BG)
        wrap.pack(fill="both", expand=True, padx=24, pady=24)
        tk.Label(wrap, text="  Zarządzanie sesją", font=FONT_TITLE,
                 bg=COLOR_BG, fg=COLOR_TEXT).pack(anchor="w", pady=(0, 16))

        # Dane do logowania
        form = Card(wrap, title="Dane autoryzacyjne")
        form.pack(fill="x", pady=(0, 12))
        fb = form.body
        fb.columnconfigure(1, weight=1)

        labeled(fb, "NIP podatnika:", 0)
        self.nip_var = tk.StringVar(value=self.app.config.get("ksef", "nip"))
        self.nip_entry = entry(fb, 0, width=30)
        self.nip_entry.insert(0, self.nip_var.get())

        labeled(fb, "Token autoryzacyjny:", 1)
        self.token_entry = entry(fb, 1, show="*", width=50)
        self.token_entry.insert(0, self.app.config.get("ksef", "token"))

        labeled(fb, "Środowisko:", 2)
        self.env_var = tk.StringVar(value=self.app.config.get("ksef", "environment", "integracyjne"))
        env_frame = tk.Frame(fb, bg=COLOR_CARD)
        env_frame.grid(row=2, column=1, sticky="w", padx=(0, 16), pady=5)
        for env, lbl in [("integracyjne","Integracyjne (TEST)"),
                          ("demo","Demo (przedprodukcyjne)"),
                          ("produkcja","Produkcja")]:
            tk.Radiobutton(env_frame, text=lbl, variable=self.env_var,
                           value=env, bg=COLOR_CARD, fg=COLOR_TEXT,
                           selectcolor=COLOR_BG, activebackground=COLOR_CARD,
                           font=FONT_BODY).pack(side="left", padx=8)

        # Przyciski
        btn_row = tk.Frame(fb, bg=COLOR_CARD)
        btn_row.grid(row=3, column=0, columnspan=2, pady=12, padx=16, sticky="w")
        FlatButton(btn_row, "  Zapisz dane",     self._save,    COLOR_ACCENT2).pack(side="left", padx=4)
        FlatButton(btn_row, "  Otwórz sesję",   self._open,    COLOR_ACCENT ).pack(side="left", padx=4)
        FlatButton(btn_row, "  Odśwież token",  self._refresh, "#2e6b2e"    ).pack(side="left", padx=4)
        FlatButton(btn_row, "  Zamknij sesję",  self._close,   COLOR_ERROR  ).pack(side="left", padx=4)
        FlatButton(btn_row, "  Ping API",        self._ping,    "#555"       ).pack(side="left", padx=4)

        # Log sesji
        log_card = Card(wrap, title="Log sesji")
        log_card.pack(fill="both", expand=True)
        self.log = LogBox(log_card.body)
        self.log.pack(fill="both", expand=True, padx=12, pady=(0, 12))

    def _save(self):
        nip   = self.nip_entry.get().strip().replace("-", "")
        token = self.token_entry.get().strip()
        env   = self.env_var.get()
        if not nip or len(nip) != 10 or not nip.isdigit():
            messagebox.showerror("Błąd", "NIP musi składać się z 10 cyfr.")
            return
        self.app.config.set("ksef", "nip",         nip)
        self.app.config.set("ksef", "token",        token)
        self.app.config.set("ksef", "environment",  env)
        self.app.config.save()
        self.app.client = KSeFClient(env)
        self.app.client.token = token
        self.app.dashboard.update_stats(nip=nip, environment=env)
        self.app.status_bar.set_connected(False, env)
        url = API_ENDPOINTS.get(env, "?")
        self.log.log(f"Dane zapisane. Środowisko: {env}  ({url})", "ok")
        self.log.log(f"NIP: {nip[:3]}*******", "ok")

    def _open(self):
        if not HAS_REQUESTS:
            self.log.log("Brak 'requests' – instalacja: pip install requests", "error")
            return
        nip   = self.nip_entry.get().strip().replace("-", "")
        token = self.token_entry.get().strip()
        if not nip or not token:
            messagebox.showwarning("Brak danych", "Podaj NIP i token autoryzacyjny.")
            return
        self._save()
        self.log.log("Inicjowanie sesji…", "info")

        def _task():
            try:
                self.log.log("Krok 1/7: pobieranie klucza publicznego RSA…", "info")
                result = self.app.client.init_session_token(nip, token)
                if self.app.client.access_token:
                    at_short = self.app.client.access_token[:24]
                    self.log.log("Krok 2/7: challenge pobrany ✔", "ok")
                    self.log.log("Krok 3/7: token zaszyfrowany RSA-OAEP ✔", "ok")
                    self.log.log("Krok 4/7: token KSeF wysłany ✔", "ok")
                    self.log.log("Krok 5/7: status autoryzacji OK ✔", "ok")
                    self.log.log("Krok 6/7: JWT access token otrzymany ✔", "ok")
                    self.log.log(f"Access token (JWT): {at_short}…", "ok")

                    # Krok 7: otwórz sesję interaktywną (z kluczem AES do szyfrowania faktur)
                    self.log.log("Krok 7/7: otwieranie sesji online (AES-256)…", "info")
                    session_result = self.app.client.open_online_session()
                    ref = self.app.client.session_ref or "brak"
                    self.log.log(f"Sesja online otwarta ✔  ref: {ref}", "ok")
                    valid_until = session_result.get("validUntil", "?")
                    self.log.log(f"Sesja ważna do: {valid_until}", "info")

                    self.app.dashboard.update_stats(session="Aktywna", api_status="OK")
                    self.app.status_bar.set_connected(True, self.env_var.get())
                    self.app.dashboard.log.log("Sesja KSeF 2.0 otwarta pomyślnie (token→JWT→online).", "ok")
                else:
                    self.log.log(f"Odpowiedź API: {json.dumps(result, indent=2, ensure_ascii=False)}", "warn")
            except Exception as ex:
                self.log.log(f"Błąd: {ex}", "error")
                messagebox.showerror("Błąd sesji", str(ex))

        threading.Thread(target=_task, daemon=True).start()

    def _close(self):
        if not self.app.client.access_token:
            self.log.log("Brak aktywnej sesji JWT.", "warn")
            return

        def _task():
            try:
                # Zamknij sesję online (jeśli otwarta)
                if self.app.client.session_ref:
                    self.app.client.close_online_session()
                    self.log.log("Sesja online zamknięta.", "ok")
                self.app.client.terminate_session()
                self.log.log("Sesja JWT zamknięta.", "ok")
                self.app.dashboard.update_stats(session="Brak")
                self.app.status_bar.set_connected(False, self.env_var.get())
            except Exception as ex:
                self.log.log(f"Błąd zamknięcia sesji: {ex}", "error")

        threading.Thread(target=_task, daemon=True).start()

    def _refresh(self):
        if not HAS_REQUESTS:
            self.log.log("Brak 'requests'.", "error")
            return
        if not self.app.client.refresh_token:
            self.log.log("Brak refresh tokena – zaloguj się najpierw.", "warn")
            return
        def _task():
            try:
                result = self.app.client.refresh_access_token()
                self.log.log(f"Token odświeżony ✔  {self.app.client.access_token[:20]}…", "ok")
            except Exception as ex:
                self.log.log(f"Błąd odświeżania tokena: {ex}", "error")
        threading.Thread(target=_task, daemon=True).start()

    def _ping(self):
        if not HAS_REQUESTS:
            self.log.log("Brak 'requests'.", "error")
            return

        def _task():
            self.log.log("Testowanie połączenia z KSeF 2.0…", "info")
            try:
                ok = self.app.client.check_connection()
                if ok:
                    self.log.log("Połączenie z API KSeF 2.0 OK ✔", "ok")
                    self.app.dashboard.update_stats(api_status="OK")
                else:
                    self.log.log("API KSeF 2.0 niedostępne.", "error")
                    self.app.dashboard.update_stats(api_status="BŁĄD")
            except Exception as ex:
                self.log.log(f"Ping nieudany: {ex}", "error")

        threading.Thread(target=_task, daemon=True).start()


# ════════════════════════════════════════════════════════════════════════════
#  ZAKŁADKA – WYŚLIJ FAKTURĘ
# ════════════════════════════════════════════════════════════════════════════
class SendTab(tk.Frame):
    def __init__(self, parent, app):
        super().__init__(parent, bg=COLOR_BG)
        self.app = app
        self._build()

    def _build(self):
        wrap = tk.Frame(self, bg=COLOR_BG)
        wrap.pack(fill="both", expand=True, padx=24, pady=24)
        tk.Label(wrap, text="  Wyślij fakturę", font=FONT_TITLE,
                 bg=COLOR_BG, fg=COLOR_TEXT).pack(anchor="w", pady=(0, 16))

        # Wybór pliku
        file_card = Card(wrap, title="Plik XML faktury")
        file_card.pack(fill="x", pady=(0, 10))
        row = tk.Frame(file_card.body, bg=COLOR_CARD)
        row.pack(padx=16, pady=10, fill="x")
        self.file_var = tk.StringVar(value="Brak wybranego pliku")
        tk.Label(row, textvariable=self.file_var, font=FONT_BODY,
                 bg=COLOR_CARD, fg=COLOR_MUTED, anchor="w").pack(side="left", fill="x", expand=True)
        FlatButton(row, "  Wybierz plik", self._pick_file, color="#444").pack(side="right")

        # Podgląd XML
        prev_card = Card(wrap, title="Podgląd treści XML")
        prev_card.pack(fill="both", expand=True, pady=(0, 10))
        self.xml_view = scrolledtext.ScrolledText(
            prev_card.body, font=FONT_MONO, bg="#0a0d14", fg=COLOR_TEXT,
            insertbackground=COLOR_ACCENT, relief="flat", bd=0, wrap="none",
            height=12
        )
        self.xml_view.pack(fill="both", expand=True, padx=12, pady=(0, 10))
        FlatButton(prev_card.body, "  Wstaw przykładową FA(3) – KSeF 2.0",
                   self._insert_sample, color="#2e5050").pack(anchor="w", padx=12, pady=(0, 10))

        # Akcje
        action_row = tk.Frame(wrap, bg=COLOR_BG)
        action_row.pack(fill="x", pady=4)
        FlatButton(action_row, "  Waliduj XML", self._validate, "#2e6b2e").pack(side="left")
        FlatButton(action_row, "  Wyślij do KSeF", self._send, COLOR_ACCENT).pack(side="left", padx=8)
        FlatButton(action_row, "  Wyczyść", self._clear, "#444").pack(side="left")

        # Wynik
        res_card = Card(wrap, title="Wynik wysyłki")
        res_card.pack(fill="x", pady=(8, 0))
        self.result_log = LogBox(res_card.body)
        self.result_log.pack(fill="both", expand=True, padx=12, pady=(0, 10))

    def _pick_file(self):
        path = filedialog.askopenfilename(
            title="Wybierz plik XML faktury",
            filetypes=[("Pliki XML", "*.xml"), ("Wszystkie pliki", "*.*")]
        )
        if path:
            self.file_var.set(path)
            try:
                with open(path, encoding="utf-8") as f:
                    content = f.read()
                self.xml_view.delete("1.0", "end")
                self.xml_view.insert("end", content)
            except Exception as ex:
                messagebox.showerror("Błąd odczytu", str(ex))

    def _insert_sample(self):
        sample = self._sample_xml()
        self.xml_view.delete("1.0", "end")
        self.xml_view.insert("end", sample)
        self.file_var.set("(treść wpisana ręcznie)")

    def _clear(self):
        self.xml_view.delete("1.0", "end")
        self.file_var.set("Brak wybranego pliku")
        self.result_log.clear()

    def _send(self):
        if not HAS_REQUESTS:
            messagebox.showerror("Błąd", "Brak biblioteki 'requests'.")
            return
        if not self.app.client.access_token:
            messagebox.showwarning("Brak sesji JWT",
                                   "Najpierw otwórz sesję KSeF 2.0 w zakładce 'Sesja'.")
            return
        xml_content = self.xml_view.get("1.0", "end").strip()
        if not xml_content:
            messagebox.showwarning("Brak danych", "Wpisz lub wczytaj treść faktury XML.")
            return
        try:
            ET.fromstring(xml_content)
        except ET.ParseError as ex:
            messagebox.showerror("Błędny XML", f"Dokument XML jest niepoprawny:\n{ex}")
            return

        self.result_log.log("Wysyłanie faktury do KSeF 2.0…", "info")

        def _task():
            try:
                result = self.app.client.send_invoice(xml_content)
                ref = result.get("referenceNumber") or result.get("ksefReferenceNumber", "brak")
                self.result_log.log(f"Faktura wysłana ✔  Numer referencyjny: {ref}", "ok")
                self.result_log.log(f"Pełna odpowiedź:\n{json.dumps(result, indent=2, ensure_ascii=False)}", "")
                self.app.dashboard.log.log(f"Wysłano fakturę, ref: {ref}", "ok")
            except Exception as ex:
                self.result_log.log(f"Błąd wysyłki: {ex}", "error")

        threading.Thread(target=_task, daemon=True).start()


    def _validate(self):
        """Lokalna walidacja XML (składnia + podstawowa struktura FA(3))."""
        xml_content = self.xml_view.get("1.0", "end").strip()
        if not xml_content:
            messagebox.showwarning("Brak danych", "Wpisz lub wczytaj treść faktury XML.")
            return
        self.result_log.log("Walidacja lokalna XML…", "info")
        errors = []

        # 1) Sprawdź poprawność XML
        try:
            root = ET.fromstring(xml_content.encode("utf-8"))
        except ET.ParseError as ex:
            self.result_log.log(f" Błąd składni XML: {ex}", "error")
            return

        self.result_log.log("✔  Składnia XML poprawna", "ok")

        # 2) Sprawdź namespace FA(3)
        ns = root.tag
        if "19456" in ns or "FA(3)" in xml_content or "WariantFormularza>3" in xml_content:
            self.result_log.log("  Schemat FA(3) wykryty", "ok")
        elif "12648" in ns or "FA(2)" in xml_content:
            self.result_log.log("  Schemat FA(2) – od 01.02.2026 wymagany FA(3)!", "warn")
            errors.append("Użyj schematu FA(3)")
        else:
            self.result_log.log(" Nie rozpoznano wersji schematu", "warn")

        # 3) Sprawdź obowiązkowe elementy
        xml_text = xml_content
        required = {
            "Naglowek":   "Nagłówek faktury",
            "Podmiot1":   "Sprzedawca (Podmiot1)",
            "Podmiot2":   "Nabywca (Podmiot2)",
            "Fa":         "Dane faktury (Fa)",
            "KodWaluty":  "Kod waluty",
            "P_1":        "Data wystawienia (P_1)",
            "P_2":        "Numer faktury (P_2)",
            "P_15":       "Kwota należności (P_15)",
            "RodzajFaktury": "Rodzaj faktury",
        }
        for tag, desc in required.items():
            if f"<{tag}" not in xml_text and f"<{tag}>" not in xml_text:
                errors.append(f"Brak elementu: {desc} <{tag}>")

        # 4) Sprawdź NIP w Podmiot1
        import re as _re
        nip_match = _re.search(r'<Podmiot1>.*?<NIP>(\d+)</NIP>', xml_text, _re.DOTALL)
        if nip_match:
            nip_val = nip_match.group(1)
            if len(nip_val) != 10:
                errors.append(f"NIP sprzedawcy '{nip_val}' – musi mieć 10 cyfr")
            else:
                self.result_log.log(f"✔  NIP sprzedawcy: {nip_val[:3]}*******", "ok")

        # 5) Wynik
        if errors:
            self.result_log.log(f" Znaleziono {len(errors)} problem(y):", "error")
            for e in errors:
                self.result_log.log(f"   • {e}", "warn")
        else:
            self.result_log.log("✔  Faktura wygląda poprawnie (walidacja lokalna)", "ok")
            self.result_log.log("ℹ  Pełna walidacja nastąpi po wysyłce do KSeF.", "info")

    def _sample_xml(self):
        nip = "1234567890"
        today = datetime.date.today().isoformat()
        return f"""<?xml version="1.0" encoding="UTF-8"?>
<Faktura xmlns="http://crd.gov.pl/wzor/2025/06/25/13775/"
         xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance">
  <Naglowek>
    <KodFormularza kodSystemowy="FA (3)" wersjaSchemy="1-0E">FA</KodFormularza>
    <WariantFormularza>3</WariantFormularza>
    <DataWytworzeniaFa>{datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%S.000Z')}</DataWytworzeniaFa>
    <SystemInfo>KSeF Desktop v{APP_VERSION}</SystemInfo>
  </Naglowek>
  <Podmiot1>
    <DaneIdentyfikacyjne>
      <NIP>{nip}</NIP>
      <Nazwa>Przykładowa Spółka Sp. z o.o.</Nazwa>
    </DaneIdentyfikacyjne>
    <Adres>
      <KodKraju>PL</KodKraju>
      <AdresL1>ul. Testowa 1</AdresL1>
      <AdresL2>00-001 Warszawa</AdresL2>
    </Adres>
  </Podmiot1>
  <Podmiot2>
    <DaneIdentyfikacyjne>
      <NIP>9876543210</NIP>
      <Nazwa>Nabywca Testowy Sp. z o.o.</Nazwa>
    </DaneIdentyfikacyjne>
    <Adres>
      <KodKraju>PL</KodKraju>
      <AdresL1>ul. Kupiecka 5</AdresL1>
      <AdresL2>30-001 Kraków</AdresL2>
    </Adres>
  </Podmiot2>
  <Fa>
    <KodWaluty>PLN</KodWaluty>
    <P_1>{today}</P_1>
    <P_2>FV/2024/001</P_2>
    <P_6>{today}</P_6>
    <P_13_1>1000.00</P_13_1>
    <P_14_1>230.00</P_14_1>
    <P_15>1230.00</P_15>
    <Adnotacje>
      <P_16>2</P_16>
      <P_17>2</P_17>
      <P_18>2</P_18>
      <P_18A>2</P_18A>
      <P_19>2</P_19>
      <P_22>2</P_22>
      <P_23>2</P_23>
    </Adnotacje>
    <RodzajFaktury>VAT</RodzajFaktury>
    <FaWiersz>
      <NrWierszaFa>1</NrWierszaFa>
      <P_7>Usługi informatyczne</P_7>
      <P_8A>szt.</P_8A>
      <P_8B>1</P_8B>
      <P_9A>1000.00</P_9A>
      <P_11>1000.00</P_11>
      <P_12>23</P_12>
    </FaWiersz>
  </Fa>
</Faktura>"""


# ════════════════════════════════════════════════════════════════════════════
#  ZAKŁADKA – ODEBRANE / WYSZUKAJ
# ════════════════════════════════════════════════════════════════════════════
class ReceiveTab(tk.Frame):
    def __init__(self, parent, app):
        super().__init__(parent, bg=COLOR_BG)
        self.app = app
        self._build()

    def _build(self):
        wrap = tk.Frame(self, bg=COLOR_BG)
        wrap.pack(fill="both", expand=True, padx=24, pady=24)
        tk.Label(wrap, text="  Wyszukaj i pobierz faktury", font=FONT_TITLE,
                 bg=COLOR_BG, fg=COLOR_TEXT).pack(anchor="w", pady=(0, 16))

        # Filtry
        flt = Card(wrap, title="Kryteria wyszukiwania")
        flt.pack(fill="x", pady=(0, 10))
        fb = flt.body
        fb.columnconfigure(1, weight=1)
        fb.columnconfigure(3, weight=1)

        labeled(fb, "Data od:", 0)
        self.date_from = entry(fb, 0, col=1, width=16)
        self.date_from.insert(0, (datetime.date.today() - datetime.timedelta(days=30)).isoformat())

        labeled(fb, "Data do:", 0, col=2)
        self.date_to = entry(fb, 0, col=3, width=16)
        self.date_to.insert(0, datetime.date.today().isoformat())

        labeled(fb, "Rola podmiotu:", 1)
        self.role_var = tk.StringVar(value="subject1")
        role_frame = tk.Frame(fb, bg=COLOR_CARD)
        role_frame.grid(row=1, column=1, columnspan=3, sticky="w", padx=(0, 16), pady=5)
        for val, lbl in [("subject1", "Sprzedawca"), ("subject2", "Nabywca"),
                         ("subject3", "Podmiot trzeci")]:
            tk.Radiobutton(role_frame, text=lbl, variable=self.role_var, value=val,
                           bg=COLOR_CARD, fg=COLOR_TEXT, selectcolor=COLOR_BG,
                           activebackground=COLOR_CARD, font=FONT_BODY).pack(side="left", padx=8)

        btn_row = tk.Frame(fb, bg=COLOR_CARD)
        btn_row.grid(row=2, column=0, columnspan=4, pady=10, padx=16, sticky="w")
        FlatButton(btn_row, "  Szukaj", self._search, COLOR_ACCENT).pack(side="left", padx=4)
        FlatButton(btn_row, "  Pobierz zaznaczoną", self._download_selected,
                   COLOR_ACCENT2).pack(side="left", padx=4)

        # Lista wyników
        res_card = Card(wrap, title="Wyniki")
        res_card.pack(fill="both", expand=True)

        cols = ("data", "numer", "sprzedawca", "nabywca", "kwota", "ref_ksef")
        self.tree = ttk.Treeview(res_card.body, columns=cols, show="headings", height=12)
        for col, head, w in zip(cols,
                                ["Data", "Numer FA", "Sprzedawca", "Nabywca",
                                 "Kwota", "Nr KSeF"],
                                [90, 140, 180, 180, 90, 160]):
            self.tree.heading(col, text=head)
            self.tree.column(col, width=w, anchor="w")

        style = ttk.Style()
        style.theme_use("clam")
        style.configure("Treeview", background=COLOR_CARD, foreground=COLOR_TEXT,
                        fieldbackground=COLOR_CARD, rowheight=26,
                        font=FONT_BODY)
        style.configure("Treeview.Heading", background=COLOR_BORDER,
                        foreground=COLOR_ACCENT, font=("Segoe UI", 9, "bold"))
        style.map("Treeview", background=[("selected", COLOR_ACCENT)])

        vsb = ttk.Scrollbar(res_card.body, orient="vertical",   command=self.tree.yview)
        hsb = ttk.Scrollbar(res_card.body, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)

        self.tree.pack(side="left", fill="both", expand=True, padx=(12, 0), pady=(0, 4))
        vsb.pack(side="left", fill="y", pady=(0, 4))
        hsb.pack(side="bottom", fill="x", padx=12)

        self.log = LogBox(wrap)
        self.log.pack(fill="x", pady=(8, 0))
        self.log.text.config(height=5)

    def _search(self):
        if not HAS_REQUESTS:
            messagebox.showerror("Błąd", "Brak 'requests'.")
            return
        if not self.app.client.access_token:
            messagebox.showwarning("Brak sesji JWT", "Otwórz sesję KSeF 2.0 przed wyszukiwaniem.")
            return
        d_from = self.date_from.get().strip()
        d_to   = self.date_to.get().strip()
        role   = self.role_var.get()
        self.log.log(f"Szukam faktur od {d_from} do {d_to}, rola: {role}…", "info")

        def _task():
            try:
                result = self.app.client.query_invoices(
                    f"{d_from}T00:00:00Z", f"{d_to}T23:59:59Z", role)
                invoices = result.get("invoiceHeaderList", [])
                self.tree.delete(*self.tree.get_children())
                for inv in invoices:
                    self.tree.insert("", "end", values=(
                        inv.get("invoicingDate", ""),
                        inv.get("invoiceReferenceNumber", ""),
                        inv.get("subjectBy", {}).get("issuedByName", ""),
                        inv.get("subjectTo", {}).get("issuedToName", ""),
                        inv.get("gross", ""),
                        inv.get("ksefReferenceNumber", ""),
                    ))
                self.log.log(f"Znaleziono {len(invoices)} faktur.", "ok")
            except Exception as ex:
                self.log.log(f"Błąd zapytania: {ex}", "error")

        threading.Thread(target=_task, daemon=True).start()

    def _download_selected(self):
        sel = self.tree.selection()
        if not sel:
            messagebox.showinfo("Info", "Zaznacz fakturę w tabeli.")
            return
        item  = self.tree.item(sel[0])
        ksef_ref = item["values"][5]
        if not ksef_ref:
            messagebox.showwarning("Brak ref.", "Brak numeru KSeF dla zaznaczonej faktury.")
            return
        save_path = filedialog.asksaveasfilename(
            defaultextension=".xml",
            filetypes=[("XML", "*.xml")],
            initialfile=f"faktura_{ksef_ref[:20]}.xml"
        )
        if not save_path:
            return

        def _task():
            try:
                result = self.app.client.download_invoice(ksef_ref)
                xml_b64 = result.get("invoiceData", "")
                xml_bytes = base64.b64decode(xml_b64)
                with open(save_path, "wb") as f:
                    f.write(xml_bytes)
                self.log.log(f"Zapisano: {save_path}", "ok")
            except Exception as ex:
                self.log.log(f"Błąd pobierania: {ex}", "error")

        threading.Thread(target=_task, daemon=True).start()


# ════════════════════════════════════════════════════════════════════════════
#  ZAKŁADKA – STATUS FAKTURY
# ════════════════════════════════════════════════════════════════════════════
class StatusTab(tk.Frame):
    def __init__(self, parent, app):
        super().__init__(parent, bg=COLOR_BG)
        self.app = app
        self._build()

    def _build(self):
        wrap = tk.Frame(self, bg=COLOR_BG)
        wrap.pack(fill="both", expand=True, padx=24, pady=24)
        tk.Label(wrap, text="  Status faktury", font=FONT_TITLE,
                 bg=COLOR_BG, fg=COLOR_TEXT).pack(anchor="w", pady=(0, 16))

        q_card = Card(wrap, title="Sprawdź po numerze referencyjnym")
        q_card.pack(fill="x", pady=(0, 10))
        qb = q_card.body
        qb.columnconfigure(1, weight=1)

        labeled(qb, "Numer referencyjny:", 0)
        self.ref_entry = entry(qb, 0, width=50)

        btn_row = tk.Frame(qb, bg=COLOR_CARD)
        btn_row.grid(row=1, column=0, columnspan=2, pady=10, padx=16, sticky="w")
        FlatButton(btn_row, "  Sprawdź status",  self._check_status, COLOR_ACCENT).pack(side="left", padx=4)
        FlatButton(btn_row, "  Pobierz UPO",     self._get_upo,      COLOR_ACCENT2).pack(side="left", padx=4)

        # Wynik
        res = Card(wrap, title="Wynik")
        res.pack(fill="both", expand=True)
        self.log = LogBox(res.body)
        self.log.pack(fill="both", expand=True, padx=12, pady=(0, 12))

    def _check_status(self):
        ref = self.ref_entry.get().strip()
        if not ref:
            messagebox.showwarning("Brak danych", "Podaj numer referencyjny.")
            return
        if not HAS_REQUESTS:
            messagebox.showerror("Błąd", "Brak 'requests'.")
            return

        self.log.log(f"Sprawdzam status dla: {ref}…", "info")

        def _task():
            try:
                result = self.app.client.check_invoice_status(ref)
                self.log.log(json.dumps(result, indent=2, ensure_ascii=False), "")
                proc_status = result.get("processingCode", "?")
                desc = {
                    100: "Zakończono sukcesem (100)",
                    200: "Przetwarzanie w toku (200)",
                    300: "Błąd przetwarzania (300)",
                }.get(proc_status, f"Kod: {proc_status}")
                kind = "ok" if proc_status == 100 else ("warn" if proc_status == 200 else "error")
                self.log.log(f"Status: {desc}", kind)
            except Exception as ex:
                self.log.log(f"Błąd: {ex}", "error")

        threading.Thread(target=_task, daemon=True).start()

    def _get_upo(self):
        ref = self.ref_entry.get().strip()
        if not ref:
            messagebox.showwarning("Brak danych", "Podaj numer referencyjny.")
            return
        save_path = filedialog.asksaveasfilename(
            defaultextension=".pdf",
            filetypes=[("PDF", "*.pdf"), ("XML", "*.xml")],
            initialfile=f"UPO_{ref[:20]}.pdf"
        )
        if not save_path:
            return

        def _task():
            try:
                result  = self.app.client.get_upo(ref)
                upo_b64 = result.get("upo", "")
                with open(save_path, "wb") as f:
                    f.write(base64.b64decode(upo_b64))
                self.log.log(f"UPO zapisane: {save_path}", "ok")
            except Exception as ex:
                self.log.log(f"Błąd pobierania UPO: {ex}", "error")

        threading.Thread(target=_task, daemon=True).start()


# ════════════════════════════════════════════════════════════════════════════
#  ZAKŁADKA – USTAWIENIA
# ════════════════════════════════════════════════════════════════════════════
class SettingsTab(tk.Frame):
    def __init__(self, parent, app):
        super().__init__(parent, bg=COLOR_BG)
        self.app = app
        self._build()

    def _build(self):
        wrap = tk.Frame(self, bg=COLOR_BG)
        wrap.pack(fill="both", expand=True, padx=24, pady=24)
        tk.Label(wrap, text="  Ustawienia", font=FONT_TITLE,
                 bg=COLOR_BG, fg=COLOR_TEXT).pack(anchor="w", pady=(0, 16))

        # Informacje o programie
        info = Card(wrap, title="Informacje o aplikacji")
        info.pack(fill="x", pady=(0, 12))
        rows = [
            ("Nazwa:", APP_NAME),
            ("Wersja:", APP_VERSION),
            ("KSeF API:", "2.0 (od 1 lutego 2026)"),
            ("Schemat faktury:", "FA(3)"),
            ("Interpreter Python:", sys.version.split()[0]),
            ("Plik konfiguracji:", CONFIG_FILE),
            ("requests:", "zainstalowany " if HAS_REQUESTS else "BRAK — pip install requests"),
            ("cryptography:", "zainstalowana " if HAS_CRYPTO else "BRAK — pip install cryptography"),
        ]
        for i, (lbl, val) in enumerate(rows):
            tk.Label(info.body, text=lbl, font=FONT_BODY, bg=COLOR_CARD,
                     fg=COLOR_MUTED).grid(row=i, column=0, sticky="w", padx=16, pady=3)
            tk.Label(info.body, text=val, font=FONT_BODY, bg=COLOR_CARD,
                     fg=COLOR_SUCCESS if "" in val else
                     (COLOR_ERROR if "BRAK" in val else COLOR_TEXT)).grid(
                         row=i, column=1, sticky="w", padx=8, pady=3)

        # Instrukcja budowania exe
        build = Card(wrap, title="🔨  Budowanie pliku .exe (PyInstaller)")
        build.pack(fill="x", pady=(0, 12))
        instructions = (
            "1. Zainstaluj PyInstaller:   pip install pyinstaller\n"
            "2. W katalogu z plikiem ksef.py wykonaj:\n\n"
            "   pyinstaller --onefile --windowed --name KSeF_Desktop \\\n"
            "               --icon=ksef_icon.ico ksef.py\n\n"
            "3. Plik EXE pojawi się w folderze dist/\n"
            "   Nie wymaga instalacji Pythona na docelowym komputerze."
        )
        tk.Label(build.body, text=instructions, font=FONT_MONO, bg=COLOR_CARD,
                 fg=COLOR_TEXT, justify="left").pack(anchor="w", padx=16, pady=(4, 12))

        btn_row = tk.Frame(wrap, bg=COLOR_BG)
        btn_row.pack(anchor="w", pady=8)
        FlatButton(btn_row, "🗑  Usuń konfigurację", self._reset, COLOR_ERROR).pack(side="left")

    def _reset(self):
        if messagebox.askyesno("Potwierdź", "Czy na pewno usunąć plik konfiguracji?"):
            try:
                os.remove(CONFIG_FILE)
                messagebox.showinfo("Gotowe", "Plik konfiguracji usunięty.")
            except FileNotFoundError:
                messagebox.showinfo("Info", "Plik konfiguracji nie istnieje.")


# ════════════════════════════════════════════════════════════════════════════
#  KONWERTER – Crystal Reports XML  →  KSeF FA(3)
# ════════════════════════════════════════════════════════════════════════════

CR_NS = 'urn:crystal-reports:schemas'

def _t(name): return f'{{{CR_NS}}}{name}'

def _get(root, obj_name, vtag='Value'):
    for obj in root.iter(_t('FormattedReportObject')):
        n = obj.find(_t('ObjectName'))
        if n is not None and n.text == obj_name:
            v = obj.find(_t(vtag))
            return (v.text or '').strip() if v is not None else ''
    return ''

def _parse_nip(raw):
    return re.sub(r'[^0-9]', '', raw)

def _parse_addr(raw):
    parts = [p.strip() for p in raw.split('\n') if p.strip()]
    l1 = parts[0] if len(parts) > 0 else ''
    l2 = parts[1] if len(parts) > 1 else ''
    return l1, l2

def _fmt(val_str, decimals=2):
    try:
        return f"{float(val_str):.{decimals}f}"
    except Exception:
        return val_str

def _detail_rows(root):
    rows = []
    for area in root.iter(_t('FormattedArea')):
        if area.get('Type') == 'Details':
            secs = area.find(_t('FormattedSections'))
            if secs is None: continue
            for sec in secs.findall(_t('FormattedSection')):
                objs = {}
                for obj in sec.iter(_t('FormattedReportObject')):
                    n = obj.find(_t('ObjectName'))
                    v = obj.find(_t('Value'))
                    if n is not None and v is not None:
                        objs[n.text] = (v.text or '').strip()
                if any(k in objs for k in ('z1Iloscf1', 'z1WartNettoZRabf1')):
                    rows.append(objs)
    return rows

def _vat_rows(root):
    rows = []
    for area in root.iter(_t('FormattedArea')):
        if area.get('Type') == 'Details':
            secs = area.find(_t('FormattedSections'))
            if secs is None: continue
            for sec in secs.findall(_t('FormattedSection')):
                objs = {}
                for obj in sec.iter(_t('FormattedReportObject')):
                    n = obj.find(_t('ObjectName'))
                    v = obj.find(_t('Value'))
                    if n is not None and v is not None:
                        objs[n.text] = (v.text or '').strip()
                if 'z1VObrotNettof1' in objs:
                    rows.append(objs)
    return rows

def parse_crystal_xml(xml_content: str) -> dict:
    """Parsuje Crystal Reports XML i zwraca słownik danych faktury."""
    root = ET.fromstring(xml_content.encode('utf-8'))

    tytul = _get(root, 'Tytul')
    nr_match = re.search(r'(\d+/\d+)', tytul)
    nr_faktury = nr_match.group(1) if nr_match else tytul.strip()

    sp_adres_raw  = _get(root, 'FldAdresPodmiotu')
    nab_adres_raw = _get(root, 'FldAdresNabywcy')
    sp_l1, sp_l2   = _parse_addr(sp_adres_raw)
    nab_l1, nab_l2 = _parse_addr(nab_adres_raw)

    data = {
        'nr':              nr_faktury,
        'data_wystawienia': _get(root, 'FldDataWyst'),
        'data_dostawy':    _get(root, 'FldDataSprz'),
        'miejsce':         _get(root, 'FldMiejsceWyst'),
        'sprzedawca': {
            'nazwa': _get(root, 'FldNazwaPelnaPodmiotu'),
            'nip':   _parse_nip(_get(root, 'FldNipPodmiotu')),
            'l1':    sp_l1, 'l2': sp_l2,
        },
        'nabywca': {
            'nazwa': _get(root, 'FldNabywcaNazwaPelna'),
            'nip':   _parse_nip(_get(root, 'FldNipNabywcy')),
            'l1':    nab_l1, 'l2': nab_l2,
        },
        'total_netto':  _get(root, 'Field4'),
        'total_vat':    _get(root, 'pof1'),
        'total_brutto': _get(root, 'Field3'),
        'items':        _detail_rows(root),
        'vat_rows':     _vat_rows(root),
    }
    return data

def build_fa3_xml(d: dict) -> str:
    """Buduje XML FA(3) z danych słownikowych."""
    now_iso = datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%S.000Z')

    # Kwoty per stawka VAT — bierz z tabeli VAT (vat_rows), nie z pozycji
    vat_groups = {}
    for vr in d.get('vat_rows', []):
        # Wyciągnij stawkę z nazwy, np. "Podstawowy podatek VAT 23%" → "23"
        nazwa_stawki = vr.get('z1VNazwaStawkif1', '')
        m = re.search(r'(\d+)\s*%', nazwa_stawki)
        stawka = m.group(1) if m else '23'
        netto  = float(vr.get('z1VObrotNettof1', '0') or 0)
        vat_kw = float(vr.get('z1VKwotaVATf1', '0') or 0)
        brutto = float(vr.get('z1VObrotBruttof1', '0') or 0)
        vat_groups[stawka] = {'netto': netto, 'vat': vat_kw, 'brutto': brutto}

    # Fallback: jeśli brak vat_rows, oblicz z pozycji
    if not vat_groups:
        for row in d['items']:
            stawka = row.get('z1StawkaVATf1', '23').replace('%', '').strip()
            netto  = float(row.get('z1WartNettoZRabf1', '0') or 0)
            vat    = float(row.get('z1WartVatZRabf1', '0') or 0)
            brutto = float(row.get('z1WartBruttoZRabf1', '0') or 0)
            if stawka not in vat_groups:
                vat_groups[stawka] = {'netto': 0.0, 'vat': 0.0, 'brutto': 0.0}
            vat_groups[stawka]['netto']  += netto
            vat_groups[stawka]['vat']    += vat
            vat_groups[stawka]['brutto'] += brutto

    total_netto  = _fmt(d['total_netto'])
    total_vat    = _fmt(d['total_vat'])
    total_brutto = _fmt(d['total_brutto'])

    sp  = d['sprzedawca']
    nab = d['nabywca']

    # Escapowanie nazw (mogą zawierać &, <, > itp.)
    sp_nazwa = escape_xml(sp['nazwa'])
    nab_nazwa = escape_xml(nab['nazwa'])
    sp_l1 = escape_xml(sp['l1'])
    sp_l2 = escape_xml(sp['l2'])
    nab_l1 = escape_xml(nab['l1'])
    nab_l2 = escape_xml(nab['l2'])

    # --- Pozycje FA ---
    wiersze_xml = ''
    for i, row in enumerate(d['items'], 1):
        nazwa   = escape_xml(row.get('z1NazwaLubOpisf1', '').strip())
        ilosc   = _fmt(row.get('z1Iloscf1', '1'), 3)
        jm      = escape_xml(row.get('z1Jmf1', 'szt.'))
        cena    = _fmt(row.get('z1CenaNBzRabf1', '0'))
        netto   = _fmt(row.get('z1WartNettoZRabf1', '0'))
        stawka  = row.get('z1StawkaVATf1', '23').replace('%', '').strip()
        wiersze_xml += f"""
  <FaWiersz>
    <NrWierszaFa>{i}</NrWierszaFa>
    <P_7>{nazwa}</P_7>
    <P_8A>{jm}</P_8A>
    <P_8B>{ilosc}</P_8B>
    <P_9A>{cena}</P_9A>
    <P_11>{netto}</P_11>
    <P_12>{stawka}</P_12>
  </FaWiersz>"""

    # --- Kwoty per stawka (P_13_x = netto, P_14_x = VAT) ---
    stawka_map = {'23': ('1','1'), '8': ('2','2'), '5': ('3','3'), '0': ('5','5'), 'ZW': ('6',''), 'NP': ('10','')}
    kwoty_xml = ''
    for stawka, vals in vat_groups.items():
        suffix = stawka_map.get(stawka, ('1','1'))
        kwoty_xml += f"\n    <P_13_{suffix[0]}>{_fmt(vals['netto'])}</P_13_{suffix[0]}>"
        if suffix[1]:
            kwoty_xml += f"\n    <P_14_{suffix[1]}>{_fmt(vals['vat'])}</P_14_{suffix[1]}>"

    xml = f"""<?xml version="1.0" encoding="UTF-8"?>
<Faktura xmlns="http://crd.gov.pl/wzor/2025/06/25/13775/"
         xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance">
  <Naglowek>
    <KodFormularza kodSystemowy="FA (3)" wersjaSchemy="1-0E">FA</KodFormularza>
    <WariantFormularza>3</WariantFormularza>
    <DataWytworzeniaFa>{now_iso}</DataWytworzeniaFa>
    <SystemInfo>KSeF Desktop – Konwerter Crystal Reports</SystemInfo>
  </Naglowek>
  <Podmiot1>
    <DaneIdentyfikacyjne>
      <NIP>{sp['nip']}</NIP>
      <Nazwa>{sp_nazwa}</Nazwa>
    </DaneIdentyfikacyjne>
    <Adres>
      <KodKraju>PL</KodKraju>
      <AdresL1>{sp_l1}</AdresL1>
      <AdresL2>{sp_l2}</AdresL2>
    </Adres>
  </Podmiot1>
  <Podmiot2>
    <DaneIdentyfikacyjne>
      <NIP>{nab['nip']}</NIP>
      <Nazwa>{nab_nazwa}</Nazwa>
    </DaneIdentyfikacyjne>
    <Adres>
      <KodKraju>PL</KodKraju>
      <AdresL1>{nab_l1}</AdresL1>
      <AdresL2>{nab_l2}</AdresL2>
    </Adres>
  </Podmiot2>
  <Fa>
    <KodWaluty>PLN</KodWaluty>
    <P_1>{d['data_wystawienia']}</P_1>
    <P_2>{escape_xml(d['nr'])}</P_2>
    <P_6>{d['data_dostawy']}</P_6>{kwoty_xml}
    <P_15>{total_brutto}</P_15>
    <Adnotacje>
      <P_16>2</P_16>
      <P_17>2</P_17>
      <P_18>2</P_18>
      <P_18A>2</P_18A>
      <P_19>2</P_19>
      <P_22>2</P_22>
      <P_23>2</P_23>
    </Adnotacje>
    <RodzajFaktury>VAT</RodzajFaktury>{wiersze_xml}
  </Fa>
</Faktura>"""
    return xml


# ─── Zakładka GUI ────────────────────────────────────────────────────────────


class ConvertTab(tk.Frame):
    def __init__(self, parent, app):
        super().__init__(parent, bg=COLOR_BG)
        self.app = app
        self._xml_data = None
        self._fa3_xml  = None
        self._build()

    def _build(self):
        wrap = tk.Frame(self, bg=COLOR_BG)
        wrap.pack(fill="both", expand=True, padx=24, pady=24)

        tk.Label(wrap, text="  Konwerter faktur → KSeF FA(3)",
                 font=FONT_TITLE, bg=COLOR_BG, fg=COLOR_TEXT).pack(anchor="w", pady=(0,4))
        tk.Label(wrap, text="Wczytaj XML z Crystal Reports / systemu sprzedaży i konwertuj do FA(3)",
                 font=FONT_SMALL, bg=COLOR_BG, fg=COLOR_MUTED).pack(anchor="w", pady=(0,12))

        # ── Wybór pliku ──────────────────────────────────────────────────────
        file_card = tk.Frame(wrap, bg=COLOR_CARD, highlightthickness=1,
                             highlightbackground=COLOR_BORDER)
        file_card.pack(fill="x", pady=(0,10))
        file_row = tk.Frame(file_card, bg=COLOR_CARD)
        file_row.pack(padx=16, pady=10, fill="x")
        self.file_lbl = tk.Label(file_row, text="Brak wybranego pliku",
                                 font=FONT_BODY, bg=COLOR_CARD, fg=COLOR_MUTED, anchor="w")
        self.file_lbl.pack(side="left", fill="x", expand=True)
        self._btn("  Wybierz XML", self._pick, COLOR_ACCENT, file_row).pack(side="right")

        # ── Podgląd wyodrębnionych danych ────────────────────────────────────
        pane = tk.PanedWindow(wrap, orient="horizontal", bg=COLOR_BG,
                              sashwidth=6, sashrelief="flat")
        pane.pack(fill="both", expand=True)

        # Lewa – dane faktury
        left = tk.Frame(pane, bg=COLOR_BG)
        pane.add(left, minsize=320)
        tk.Label(left, text="  Dane wejściowe", font=("Segoe UI",11,"bold"),
                 bg=COLOR_BG, fg=COLOR_ACCENT).pack(anchor="w", pady=(0,4))
        self.info_box = scrolledtext.ScrolledText(
            left, font=FONT_MONO, bg="#0a0d14", fg=COLOR_TEXT,
            relief="flat", bd=0, state="disabled", wrap="word")
        self.info_box.pack(fill="both", expand=True)

        # Prawa – wygenerowany FA(3)
        right = tk.Frame(pane, bg=COLOR_BG)
        pane.add(right, minsize=380)
        tk.Label(right, text="  Wygenerowany FA(3) XML", font=("Segoe UI",11,"bold"),
                 bg=COLOR_BG, fg=COLOR_ACCENT).pack(anchor="w", pady=(0,4))
        self.xml_box = scrolledtext.ScrolledText(
            right, font=FONT_MONO, bg="#0a0d14", fg=COLOR_TEXT,
            relief="flat", bd=0, state="disabled", wrap="none")
        self.xml_box.pack(fill="both", expand=True)

        # ── Przyciski akcji ──────────────────────────────────────────────────
        btn_row = tk.Frame(wrap, bg=COLOR_BG)
        btn_row.pack(fill="x", pady=(10,0))
        self._btn("  Konwertuj", self._convert, COLOR_ACCENT,  btn_row).pack(side="left")
        self._btn("  Wyślij do KSeF", self._to_send, "#2e6b2e", btn_row).pack(side="left", padx=8)
        self._btn("  Zapisz FA(3).xml", self._save,  COLOR_ACCENT2, btn_row).pack(side="left")
        self.status_lbl = tk.Label(btn_row, text="", font=FONT_SMALL,
                                   bg=COLOR_BG, fg=COLOR_MUTED)
        self.status_lbl.pack(side="right", padx=8)

    @staticmethod
    def _btn(text, cmd, color, parent):
        b = tk.Label(parent, text=text, font=("Segoe UI",10,"bold"),
                     bg=color, fg="white", cursor="hand2",
                     padx=18, pady=8, relief="flat")
        b.bind("<Button-1>", lambda e: cmd())
        c = color
        b.bind("<Enter>", lambda e, w=b: w.config(bg=ConvertTab._dk(c)))
        b.bind("<Leave>", lambda e, w=b: w.config(bg=c))
        return b

    @staticmethod
    def _dk(h):
        c = h.lstrip('#')
        if len(c) != 6:
            return h
        try:
            r,g,b = int(c[0:2],16),int(c[2:4],16),int(c[4:6],16)
        except ValueError:
            return h
        return "#{:02x}{:02x}{:02x}".format(max(r-30,0),max(g-30,0),max(b-30,0))

    def _set_info(self, txt):
        self.info_box.config(state="normal")
        self.info_box.delete("1.0","end")
        self.info_box.insert("end", txt)
        self.info_box.config(state="disabled")

    def _set_xml(self, txt):
        self.xml_box.config(state="normal")
        self.xml_box.delete("1.0","end")
        self.xml_box.insert("end", txt)
        self.xml_box.config(state="disabled")

    def _pick(self):
        path = filedialog.askopenfilename(
            title="Wybierz XML z Crystal Reports",
            filetypes=[("Pliki XML","*.xml"),("Wszystkie","*.*")])
        if not path:
            return
        self.file_lbl.config(text=os.path.basename(path), fg=COLOR_TEXT)
        try:
            with open(path, encoding="utf-8", errors="replace") as f:
                self._xml_data = f.read()
            self._fa3_xml = None
            self._set_xml("")
            self._set_info(f"Plik wczytany:\n{path}\n\nKliknij 'Konwertuj'.")
            self.status_lbl.config(text="Plik wczytany ✔", fg=COLOR_SUCCESS)
        except Exception as ex:
            messagebox.showerror("Błąd", str(ex))

    def _convert(self):
        if not self._xml_data:
            messagebox.showwarning("Brak pliku", "Najpierw wybierz plik XML.")
            return
        try:
            d = parse_crystal_xml(self._xml_data)
            self._fa3_xml = build_fa3_xml(d)

            # Podgląd danych
            sp  = d['sprzedawca']
            nab = d['nabywca']
            info = (
                f"FAKTURA  {d['nr']}\n"
                f"{'─'*44}\n"
                f"Data wystawienia:  {d['data_wystawienia']}\n"
                f"Data dostawy:      {d['data_dostawy']}\n\n"
                f"SPRZEDAWCA\n"
                f"  {sp['nazwa']}\n"
                f"  NIP: {sp['nip']}\n"
                f"  {sp['l1']}, {sp['l2']}\n\n"
                f"NABYWCA\n"
                f"  {nab['nazwa']}\n"
                f"  NIP: {nab['nip']}\n"
                f"  {nab['l1']}, {nab['l2']}\n\n"
                f"POZYCJE ({len(d['items'])})\n"
                f"{'─'*44}\n"
            )
            for i, row in enumerate(d['items'], 1):
                info += (
                    f"  {i}. {row.get('z1NazwaLubOpisf1','').strip()}\n"
                    f"     {row.get('z1Iloscf1','')} {row.get('z1Jmf1','')}  "
                    f"× {row.get('z1CenaNBzRabf1','')} zł  |  VAT {row.get('z1StawkaVATf1','')}%\n"
                    f"     Netto: {row.get('z1WartNettoZRabf1','')}  "
                    f"VAT: {row.get('z1WartVatZRabf1','')}  "
                    f"Brutto: {row.get('z1WartBruttoZRabf1','')}\n"
                )
            info += (
                f"\n{'─'*44}\n"
                f"  Razem netto:   {d['total_netto']} PLN\n"
                f"  Razem VAT:     {d['total_vat']} PLN\n"
                f"  Razem brutto:  {d['total_brutto']} PLN\n"
            )
            self._set_info(info)
            self._set_xml(self._fa3_xml)
            self.status_lbl.config(text="Konwersja OK ✔", fg=COLOR_SUCCESS)
            self.app.dashboard.log.log(
                f"Konwersja CR→FA(3): {d['nr']} | {d['total_brutto']} PLN", "ok")
        except Exception as ex:
            messagebox.showerror("Błąd konwersji", str(ex))
            self.status_lbl.config(text=f"Błąd: {ex}", fg=COLOR_ERROR)

    def _to_send(self):
        if not self._fa3_xml:
            messagebox.showwarning("Brak XML", "Najpierw kliknij 'Konwertuj'.")
            return
        send_tab = self.app._tabs.get("Wyślij")
        if send_tab:
            send_tab.xml_view.delete("1.0", "end")
            send_tab.xml_view.insert("end", self._fa3_xml)
            send_tab.file_var.set("(z konwertera Crystal Reports)")
            self.app.show_tab("Wyślij")
            self.status_lbl.config(text="Załadowano do zakładki Wyślij ✔", fg=COLOR_SUCCESS)

    def _save(self):
        if not self._fa3_xml:
            messagebox.showwarning("Brak XML", "Najpierw kliknij 'Konwertuj'.")
            return
        path = filedialog.asksaveasfilename(
            defaultextension=".xml",
            filetypes=[("XML FA(3)","*.xml")],
            initialfile="faktura_FA3.xml")
        if path:
            with open(path, "w", encoding="utf-8") as f:
                f.write(self._fa3_xml)
            self.status_lbl.config(text=f"Zapisano: {os.path.basename(path)}", fg=COLOR_SUCCESS)


# ════════════════════════════════════════════════════════════════════════════
#  GŁÓWNA APLIKACJA
# ════════════════════════════════════════════════════════════════════════════
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(APP_NAME)
        self.geometry("1100x760")
        self.minsize(900, 600)
        self.configure(bg=COLOR_BG)

        # Ikona (jeśli dostępna)
        try:
            self.iconbitmap("ksef_icon.ico")
        except Exception:
            pass

        self.config  = Config()
        self.client  = KSeFClient(self.config.get("ksef", "environment", "integracyjne"))
        self.client.token = self.config.get("ksef", "token")

        self._build_ui()

    # ── budowanie interfejsu ─────────────────────────────────────────────────
    def _build_ui(self):
        # Pasek tytułowy
        title_bar = tk.Frame(self, bg=COLOR_PANEL, height=50)
        title_bar.pack(fill="x", side="top")
        title_bar.pack_propagate(False)
        tk.Label(title_bar, text="   KSeF Desktop",
                 font=("Segoe UI", 13, "bold"), bg=COLOR_PANEL,
                 fg=COLOR_ACCENT).pack(side="left", padx=12, pady=10)
        tk.Label(title_bar, text="Krajowy System e-Faktur",
                 font=FONT_SMALL, bg=COLOR_PANEL, fg=COLOR_MUTED).pack(
                     side="left", padx=4, pady=10)

        # Pasek statusu (dół)
        self.status_bar = StatusBar(self)
        self.status_bar.pack(fill="x", side="bottom")
        self.status_bar.set_connected(False, self.config.get("ksef", "environment"))

        # Główny układ: sidebar + treść
        main = tk.Frame(self, bg=COLOR_BG)
        main.pack(fill="both", expand=True)

        # Sidebar
        sidebar = tk.Frame(main, bg=COLOR_PANEL, width=180)
        sidebar.pack(fill="y", side="left")
        sidebar.pack_propagate(False)

        # Obszar treści
        self._content = tk.Frame(main, bg=COLOR_BG)
        self._content.pack(fill="both", expand=True)

        # Zakładki
        self._tabs: dict[str, tk.Frame] = {}
        self._nav_btns: dict[str, tk.Label] = {}

        self.dashboard = DashboardTab(self._content, self)
        self._tabs["Pulpit"]  = self.dashboard
        self._tabs["Sesja"]   = SessionTab(self._content, self)
        self._tabs["Wyślij"]  = SendTab(self._content, self)
        self._tabs["Konwerter"] = ConvertTab(self._content, self)
        self._tabs["Odebrane"]= ReceiveTab(self._content, self)
        self._tabs["Status"]  = StatusTab(self._content, self)
        self._tabs["Ustawienia"] = SettingsTab(self._content, self)

        icons = {"Pulpit": "🏠", "Sesja": "🔐", "Wyślij": "📤",
                 "Konwerter": "🔄", "Odebrane": "📥", "Status": "🔍", "Ustawienia": "⚙"}

        tk.Frame(sidebar, bg=COLOR_BORDER, height=1).pack(fill="x", pady=(16, 8))

        for name, tab in self._tabs.items():
            btn = tk.Label(sidebar,
                           text=f"  {icons.get(name,'')}  {name}",
                           font=("Segoe UI", 11), bg=COLOR_PANEL,
                           fg=COLOR_MUTED, anchor="w", cursor="hand2",
                           pady=10, padx=8)
            btn.pack(fill="x")
            btn.bind("<Button-1>", lambda e, n=name: self.show_tab(n))
            btn.bind("<Enter>",    lambda e, b=btn: b.config(bg=COLOR_HOVER, fg=COLOR_TEXT))
            btn.bind("<Leave>",    lambda e, b=btn, n=name:
                     b.config(bg=COLOR_ACCENT if self._current == n else COLOR_PANEL,
                              fg=COLOR_TEXT if self._current == n else COLOR_MUTED))
            self._nav_btns[name] = btn
            tab.place(in_=self._content, x=0, y=0, relwidth=1, relheight=1)

        self._current = None
        self.show_tab("Pulpit")

        # Aktualizuj dashboard ze startowymi danymi
        nip = self.config.get("ksef", "nip")
        env = self.config.get("ksef", "environment")
        self.dashboard.update_stats(nip=nip or "—", environment=env)

    def show_tab(self, name: str):
        if name not in self._tabs:
            return
        if self._current and self._current in self._nav_btns:
            self._nav_btns[self._current].config(bg=COLOR_PANEL, fg=COLOR_MUTED)
        self._tabs[name].lift()
        self._current = name
        btn = self._nav_btns[name]
        btn.config(bg=COLOR_ACCENT, fg="white")
        self.status_bar.set(f"Zakładka: {name}")


# ════════════════════════════════════════════════════════════════════════════
#  PUNKT WEJŚCIA
# ════════════════════════════════════════════════════════════════════════════
if __name__ == "__main__":
    app = App()
    app.mainloop()