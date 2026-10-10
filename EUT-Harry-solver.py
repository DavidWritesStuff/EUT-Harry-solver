#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Everything Upgrade Tree – Harryho puzzle (GUI solver)
Features: motivy (světlý/tmavý), perzistence, barevná legenda/sloupce,
1-based idx a (r,c), 25-řádkový výstup (OK ↑, ERR, EMPTY ↓),
P1–P4 (výrazy, rovnice s x, přiřazení a/b/x), Action & Error log (ACT/ERR/OK),
overlay rank v mřížce, kompaktní režim s rychlým menu, Info panel i jako okno.
"""
from __future__ import annotations
import ast
import json
import math
import re
import tkinter as tk
import ctypes
from tkinter import ttk, messagebox
from datetime import datetime
from pathlib import Path
from typing import List, Tuple, Optional, Dict

# --------------------- Parsování & Eval ---------------------
Coord = Tuple[int, int]

# P2 – mapování symbolů na číslice
SHIFT_MAP = {
    '!': '1', '@': '2', '#': '3', '$': '4', '%': '5',
    '^': '6', '&': '7', '*': '8', '(': '9', ')': '0'
}
SHIFT_ALLOWED = set(SHIFT_MAP) \
    | set("0123456789")

# P3 – formáty báze
PARENS_PAT = re.compile(r'^\s*([\+\-]?[0-9A-Za-z]+)\s*\(\s*(\d{1,2})\s*\)\s*$')
COLON_PAT  = re.compile(r'^\s*([\+\-]?[0-9A-Za-z]+)\s*:\s*(\d{1,2})\s*$')

# P4 – whitelist pro bezpečný eval
_ALLOWED_NAMES: Dict[str, object] = {
    'pi': math.pi, 'e': math.e, 'tau': math.tau,
    'abs': abs, 'sqrt': math.sqrt,
    'sin': math.sin, 'cos': math.cos, 'tan': math.tan,
    'asin': math.asin, 'acos': math.acos, 'atan': math.atan,
    'log': math.log, 'ln': math.log, 'log10': math.log10,
    'floor': math.floor, 'ceil': math.ceil, 'round': round,
    # faktoriál přes bezpečný wrapper (doplní se po definici _fac)
    'factorial': None,   # placeholder
    'fac': None,         # placeholder
    'pow': pow,
    'min': min, 'max': max, 'sum': sum
}

# Povolené AST uzly
_ALLOWED_NODES = {
    ast.Expression, ast.BinOp, ast.UnaryOp, ast.Constant,
    ast.Add, ast.Sub, ast.Mult, ast.Div, ast.FloorDiv, ast.Mod, ast.Pow,
    ast.USub, ast.UAdd, ast.Load, ast.Call, ast.Name, ast.Tuple, ast.List
}

# ----------------- Bezpečný faktoriál -----------------
def _fac(x: float) -> int:
    """
    Bezpečná varianta faktoriálu:
      - vyžaduje celé nezáporné číslo,
      - toleruje integer-like float (např. 5.0),
      - jinak vyhodí srozumitelný ValueError.
    """
    if abs(x - round(x)) > 1e-12:
        raise ValueError("Argument faktoriálu musí být celé číslo")
    n = int(round(x))
    if n < 0:
        raise ValueError("Faktoriál je definován jen pro nezáporná celá čísla")
    return math.factorial(n)

# zaregistruj _fac do whitelistu
_ALLOWED_NAMES['fac'] = _fac
_ALLOWED_NAMES['factorial'] = _fac

# --------------- normalizace výrazu (P4) ---------------
def apply_factorials(s: str) -> str:
    """
    Převod postfixového '!' (i vícenásobného) na volání fac(...).
    Příklady:
      5!        -> fac(5)
      (3+2)!    -> fac((3+2))
      a!!       -> fac(fac(a))
      foo(3)!   -> fac(foo(3))
    Pozn.: '!!' = opakované použití faktoriálu, nikoli double factorial.
    """
    # 1) Nejprve nahrazuj '(...)!'/ 'f(...)!' – vše, co končí na ')'
    paren_pat = re.compile(r'(\([^()]*\))(!+)')
    while True:
        new_s = paren_pat.sub(lambda m: ('fac(' * len(m.group(2))) + m.group(1) + (')' * len(m.group(2))), s)
        if new_s == s:
            break
        s = new_s

    # 2) Čísla / identifikátory před '!'
    atom_pat = re.compile(r'(\b(?:\d+(?:\.\d+)?|[A-Za-z_]\w*))(!+)')
    def repl_atom(m):
        expr, bangs = m.group(1), m.group(2)
        k = len(bangs)
        return ('fac(' * k) + expr + (')' * k)
    s = atom_pat.sub(repl_atom, s)
    return s

def normalize_expr(expr: str) -> str:
    s = expr.strip()
    s = s.replace('^', '**')  # ^ -> **
    s = re.sub(r'\bmod\b', '%', s, flags=re.I)  # mod -> %
    s = s.replace('π', 'pi')  # π -> pi

    # implicitní násobení (číslo/var/závorky) – 1. průchod
    patterns = [
        (r'(\d)\s*([abxABX])', r'\1*\2'),
        (r'([abxABX])\s*(\d)', r'\1*\2'),
        (r'(\))\s*([abxABX])', r'\1*\2'),
        (r'([abxABX])\s*(\()', r'\1*\2'),
        (r'([abxABX])\s*([abxABX])', r'\1*\2'),
        (r'(\d)\s*(\()', r'\1*\2'),
        (r'(\))\s*(\d)', r'\1*\2'),
    ]
    for pat, repl in patterns:
        s = re.sub(pat, repl, s)

    # postfixové faktoriály '!' -> volání fac(...)
    s = apply_factorials(s)

    # implicitní násobení – 2. průchod (kvůli novým sekvencím po nahrazení '!'),
    # + speciální případy okolo 'fac('
    post_fac_patterns = [
        # pokud něco stojí těsně před 'fac('
        (r'(\d)\s*(fac\()', r'\1*\2'),
        (r'([abxABX])\s*(fac\()', r'\1*\2'),
        (r'(\))\s*(fac\()', r'\1*\2'),
        # a když 'fac(... )' stojí před číslem/var
        (r'(\))\s*([abxABX])', r'\1*\2'),
        (r'(\))\s*(\d)', r'\1*\2'),
    ]
    for pat, repl in post_fac_patterns:
        s = re.sub(pat, repl, s)

    return s

def _safe_eval_node(node: ast.AST, env: Dict[str, object]):
    if type(node) not in _ALLOWED_NODES:
        raise ValueError(f"Nepovolený prvek výrazu: {type(node).__name__}")

    if isinstance(node, ast.Expression):
        return _safe_eval_node(node.body, env)

    if isinstance(node, ast.Constant):
        if isinstance(node.value, int):
            return node.value
        if isinstance(node.value, float) and node.value.is_integer():
            return int(node.value)
        raise ValueError("Pouze číselné literály jsou povolené")

    if isinstance(node, ast.Name):
        name = node.id
        if name in env:
            return env[name]
        raise ValueError(f"Nedefinovaná proměnná '{name}'")

    if isinstance(node, ast.UnaryOp):
        v = _safe_eval_node(node.operand, env)
        if isinstance(node.op, ast.UAdd): return v
        if isinstance(node.op, ast.USub): return -v
        raise ValueError("Nepodporovaný unární operátor")

    if isinstance(node, ast.BinOp):
        l = _safe_eval_node(node.left, env)
        r = _safe_eval_node(node.right, env)
        if isinstance(node.op, ast.Add): return l + r
        if isinstance(node.op, ast.Sub): return l - r
        if isinstance(node.op, ast.Mult): return l * r
        if isinstance(node.op, ast.Div):
            if isinstance(l, int) and isinstance(r, int) and l % r == 0:
                return l // r
            return l / r
        if isinstance(node.op, ast.FloorDiv): return l // r
        if isinstance(node.op, ast.Mod): return l % r
        if isinstance(node.op, ast.Pow): return pow(l, r)
        raise ValueError("Nepodporovaný binární operátor")

    if isinstance(node, ast.Call):
        if not isinstance(node.func, ast.Name):
            raise ValueError("Povoleny jsou jen jednoduché funkce")
        fn = node.func.id
        if fn not in env or not callable(env[fn]):
            raise ValueError(f"Funkce '{fn}' není povolena")
        args = [_safe_eval_node(a, env) for a in node.args]
        return env[fn](*args)

    if isinstance(node, (ast.Tuple, ast.List)):
        return sum(_safe_eval_node(elt, env) for elt in node.elts)

    raise ValueError("Nepodporovaná struktura výrazu")

def eval_math_with_vars(expr: str, vars_map: Optional[Dict[str, float]] = None) -> float:
    s = normalize_expr(expr)
    tree = ast.parse(s, mode='eval')
    env: Dict[str, object] = dict(_ALLOWED_NAMES)
    if vars_map:
        for k, v in vars_map.items():
            kl = k.lower()
            if kl not in ('a', 'b', 'c', 'x'):
                raise ValueError(f"Povoleny jsou jen proměnné a,b,c,x (máš '{k}')")
            env[kl] = v
    return _safe_eval_node(tree, env)

# ---------------------- P1, P2, P3 ----------------------
def parse_plain_number(s: str) -> float:
    s2 = s.strip().replace('_', '')
    if re.fullmatch(r'[+\-]?\d+', s2):
        return float(int(s2))
    try:
        return float(s2)
    except ValueError:
        raise ValueError("Neplatné čisté číslo")

def decode_shifted_number(s: str) -> float:
    s2 = s.strip()
    if not s2 or any(ch not in SHIFT_MAP for ch in s2):
        raise ValueError("Neplatný shifted formát")
    mapped = ''.join(SHIFT_MAP[ch] for ch in s2)
    return float(int(mapped))

def parse_base_number(s: str) -> float:
    t = s.strip()
    m = PARENS_PAT.match(t) or COLON_PAT.match(t)
    if not m:
        raise ValueError("Neplatný zápis báze (NUM(BASE) nebo NUM:BASE)")
    num_str, base_str = m.groups()
    base = int(base_str)
    if not (2 <= base <= 36):
        raise ValueError("Podporované báze jsou 2..36")
    try:
        return float(int(num_str, base))
    except ValueError:
        # tohle je „invalid literal“ → dovolíme fallback na P4
        raise

# --- P4: assignment chain / lineární rovnice / čistý výraz ---
ASSIGN_SPLIT = re.compile(r'\s*[,;]\s*')

def is_assignment_chain(s: str) -> bool:
    if s.count('=') <= 1:
        return False
    parts = ASSIGN_SPLIT.split(s)
    return sum(1 for p in parts if '=' in p) >= 2

def evaluate_assignment_chain(s: str) -> tuple[float, Dict[str, float]]:
    text = normalize_expr(s)
    env: Dict[str, float] = {}
    parts = ASSIGN_SPLIT.split(text)
    if not parts:
        raise ValueError("Prázdná série přiřazení")
    for raw in parts:
        if not raw.strip():
            continue
        if '=' not in raw:
            raise ValueError(f"Člen '{raw}' neobsahuje '='")
        name, expr = map(str.strip, raw.split('=', 1))
        name = name.lower()
        if name not in ('a', 'b', 'c', 'x'):
            raise ValueError(f"Povoleny jsou pouze proměnné a,b,c,x (máš '{name}')")

        env[name] = eval_math_with_vars(expr, env)
    if 'x' not in env:
        raise ValueError("Série přiřazení nedefinuje proměnnou 'x'")
    return env['x'], env

def _has_x(node: ast.AST) -> bool:
    if isinstance(node, ast.Name):
        return node.id == 'x'
    return any(_has_x(ch) for ch in ast.iter_child_nodes(node))

def _eval_const_node(node: ast.AST, env: Dict[str, float]) -> float:
    if _has_x(node):
        raise ValueError("Očekávána konstanta (bez x)")
    expr_ast = ast.Expression(body=node)
    return float(_safe_eval_node(expr_ast, dict(_ALLOWED_NAMES, **env)))

def _linear_form(node: ast.AST, env: Dict[str, float]) -> Tuple[float, float]:
    if not _has_x(node):
        return 0.0, _eval_const_node(node, env)
    if isinstance(node, ast.Name) and node.id == 'x':
        return 1.0, 0.0
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
        k, c = _linear_form(node.operand, env)
        return (k, c) if isinstance(node.op, ast.UAdd) else (-k, -c)
    if isinstance(node, ast.BinOp):
        if isinstance(node.op, (ast.Add, ast.Sub)):
            k1, c1 = _linear_form(node.left, env)
            k2, c2 = _linear_form(node.right, env)
            return (k1 + k2, c1 + c2) if isinstance(node.op, ast.Add) else (k1 - k2, c1 - c2)
        if isinstance(node.op, ast.Mult):
            l, r = node.left, node.right
            lh, rh = _has_x(l), _has_x(r)
            if lh and rh:
                raise ValueError("Nelineární výraz: násobení dvou členů obsahujících x")
            k, c = _linear_form(l if lh else r, env)
            const = _eval_const_node(r if lh else l, env)
            return k * const, c * const
        if isinstance(node.op, (ast.Div, ast.FloorDiv)):
            if _has_x(node.right):
                raise ValueError("Nelineární výraz: x ve jmenovateli")
            k, c = _linear_form(node.left, env)
            const = _eval_const_node(node.right, env)
            if isinstance(node.op, ast.FloorDiv):
                if abs(k) > 1e-12:
                    raise ValueError("Nelineární výraz: // s proměnnou x")
                return 0.0, math.floor(c / const)
            return k / const, c / const
        if isinstance(node.op, ast.Pow):
            raise ValueError("Nelineární výraz: mocnina s x")
    if isinstance(node, ast.Call):
        for a in node.args:
            if _has_x(a):
                raise ValueError("Nelineární výraz: funkce aplikovaná na x")
        return 0.0, _eval_const_node(node, env)
    raise ValueError("Nepodporovaná konstrukce v lineární rovnici")

def solve_linear_equation_x(equation: str, env: Optional[Dict[str, float]] = None) -> float:
    env = dict(env or {})
    s = normalize_expr(equation)
    if s.count('=') != 1:
        raise ValueError("Očekávám právě jednu '=' pro lineární rovnici")
    left, right = map(str.strip, s.split('=', 1))
    L, R = ast.parse(left, mode='eval'), ast.parse(right, mode='eval')
    k1, c1 = _linear_form(L.body, env)
    k2, c2 = _linear_form(R.body, env)
    k, d = k1 - k2, c2 - c1
    if abs(k) < 1e-12:
        if abs(d) < 1e-12:
            raise ValueError("Nekonečně mnoho řešení (totožnost)")
        else:
            raise ValueError("Žádné řešení (rozpornost)")
    return d / k

def p4_value_and_display(text: str) -> tuple[float, str]:
    s = text.strip()
    if not s:
        raise ValueError("Prázdný vstup")
    if is_assignment_chain(s):
        xval, _ = evaluate_assignment_chain(s)
        return xval, f"x = {xval}"
    if s.count('=') == 1:
        xval = solve_linear_equation_x(s)
        return xval, f"x = {xval}"
    val = eval_math_with_vars(s, {})
    return float(val), str(val)

# --- Autodetekce typu buňky: P1 → P2 → P3 (fallback) → P4 ---
def autodetect_and_parse(s: str) -> Tuple[str, float, str]:
    """
    Vrací (typ, numeric_value, display_text). Typ ∈ {'P1','P2','P3','P4'}.
    P3 vs. P4: pokud zápis vypadá jako NUM(BASE)/NUM:BASE a padne na invalid literal,
    pokračujeme jako P4; formátové chyby P3 necháme propadnout jako P3-ERR.
    """
    txt = s.strip()
    # P1 – čisté číslo
    try:
        v = parse_plain_number(txt)
        return 'P1', v, str(v)
    except Exception:
        pass
    # P2 – shifted !@#$%^&*()
    try:
        v = decode_shifted_number(txt)
        return 'P2', v, str(v)
    except Exception:
        pass
    # P3 – NUM(BASE) / NUM:BASE (s fallbackem na P4)
    m = PARENS_PAT.match(txt) or COLON_PAT.match(txt)
    if m:
        try:
            v = parse_base_number(txt)  # může vyhodit ValueError
            return 'P3', v, str(v)
        except ValueError as e:
            msg = str(e)
            if ("Podporované báze" in msg) or ("Neplatný zápis báze" in msg):
                raise
            # jinak fallback → P4
    # P4 – výrazy/rovnice/přiřazení
    v, disp = p4_value_and_display(txt)
    return 'P4', v, disp

def compute_maps(grid_texts: List[List[str]]):
    entries_map: Dict[Tuple[int, int], Tuple[str, float]] = {}
    display_map: Dict[Tuple[int, int], str] = {}
    errors_map: Dict[Tuple[int, int], str] = {}
    empty_set = set()
    for r in range(5):
        for c in range(5):
            raw = grid_texts[r][c]
            if raw.strip() == '':
                empty_set.add((r, c))
                continue
            try:
                typ, val, disp = autodetect_and_parse(raw)
                entries_map[(r, c)] = (typ, val)
                display_map[(r, c)] = disp
            except Exception as e:
                errors_map[(r, c)] = str(e)
    return entries_map, display_map, errors_map, empty_set

def stable_sorted(entries_map: dict) -> List[Tuple[int, int, str, float]]:
    items = [(r, c, typ, val) for (r, c), (typ, val) in entries_map.items()]
    items.sort(key=lambda t: (t[3], t[0]*5 + t[1]))  # value asc; stable by linear index
    return items

# ---------------- GUI – palety ----------------
# Barvy sloupců (na obou motivech čitelné)
COL_IDX   = "#80CBC4"  # teal
COL_RANK  = "#C3E88D"  # green
COL_TYP   = "#F78C6C"  # orange
COL_VALUE = "#FFCB6B"  # yellow
COL_RC    = "#82AAFF"  # blue
COL_STATE = "#C792EA"  # purple

# Řezy sloupců v monospaced textu (srovnané s formátováním níže)
COL_SLICES = [(0, 3), (5, 9), (11, 14), (16, 28), (30, 36), (38, None)]

# Palety motivů
PALETTE_DARK = dict(
    BG="#121212", FG="#E0E0E0", PANEL_BG="#1E1E1E",
    EMPTY_BG="#2B2B2B", ERROR_BG="#5A1D1D", OK_BG="#1E1E1E",
    SEP="#555555", ERR_TEXT="#FF5370", EMPTY_TEXT="#B0BEC5"
)
PALETTE_LIGHT = dict(
    BG="#FAFAFA", FG="#1A1A1A", PANEL_BG="#FFFFFF",
    EMPTY_BG="#EEEEEE", ERROR_BG="#FFCDD2", OK_BG="#FFFFFF",
    SEP="#888888", ERR_TEXT="#D32F2F", EMPTY_TEXT="#546E7A"
)

MONO_FONT = ("Consolas", 11)
UI_FONT   = ("Segoe UI", 10)

# Responsive breakpoint pro kompaktní layout (šířka hlavního okna v px)
COMPACT_BREAKPOINT = 980

# Perzistence
CONFIG_PATH = Path.home() / ".eut_harry_gui.json"
DEFAULT_CONFIG = {
    "theme": "dark",
    "rgb": [18, 18, 18],
    "root_geometry": "1080x780+200+100",
    "out_geometry": "700x780+1100+60",
    "console_geometry": "700x300+1100+860",
    "save_grid": False,
    "grid": [],  # 5x5 strings
    "start_compact": False
}

# ---------------- HUD Overlay ----------------
GWL_EXSTYLE = -20
WS_EX_TRANSPARENT = 0x00000020
WS_EX_LAYERED = 0x00080000
TRANS_COLOR = "#000001"

class OverlayWindow:
    def __init__(self, parent: tk.Tk):
        self.parent = parent
        self.is_locked = False

        # 1. Řídicí okénko
        self.ctrl = tk.Toplevel(parent)
        self.ctrl.title("HUD Overlay - Ovládání")
        self.ctrl.geometry("340x210")
        self.ctrl.attributes("-topmost", True)
        self.ctrl.resizable(False, False)

        tk.Label(
            self.ctrl, 
            text="Roblox HUD Overlay", 
            font=("Segoe UI", 11, "bold")
        ).pack(pady=(10, 5))

        self.btn_toggle = tk.Button(
            self.ctrl, 
            text="🔒 Zamknout & Zapnout proklikávání", 
            command=self.toggle_clickthrough, 
            bg="#4CAF50", 
            fg="white", 
            font=("Segoe UI", 10, "bold"),
            padx=10,
            pady=5
        )
        self.btn_toggle.pack(pady=5)

        # Posuvník pro nastavení opacity podkladu
        tk.Label(self.ctrl, text="Opacita políček:").pack(pady=(8, 2))
        self.alpha_var = tk.DoubleVar(value=0.6)
        self.slider_alpha = ttk.Scale(
            self.ctrl, 
            from_=0.1, 
            to=1.0, 
            variable=self.alpha_var, 
            command=self.update_alpha
        )
        self.slider_alpha.pack(fill='x', padx=20)

        # 2. Průhledné Overlay okno
        self.overlay = tk.Toplevel(parent)
        self.overlay.title("Roblox HUD Grid")
        self.overlay.geometry("400x400+500+200")
        self.overlay.attributes("-topmost", True)
        self.overlay.configure(bg=TRANS_COLOR)
        self.overlay.attributes("-transparentcolor", TRANS_COLOR)
        self.overlay.attributes("-alpha", self.alpha_var.get())

        for i in range(5):
            self.overlay.rowconfigure(i, weight=1)
            self.overlay.columnconfigure(i, weight=1)

        self.labels: List[List[tk.Label]] = []
        for r in range(5):
            row_labs = []
            for c in range(5):
                lbl = tk.Label(
                    self.overlay, 
                    text="", 
                    font=("Consolas", 22, "bold"),
                    fg="#00FF00",
                    bg="#151515",
                    bd=1,
                    relief="solid"
                )
                lbl.grid(row=r, column=c, padx=4, pady=4, sticky="nsew")
                row_labs.append(lbl)
            self.labels.append(row_labs)

        self.ctrl.protocol("WM_DELETE_WINDOW", self.destroy)
        self.overlay.protocol("WM_DELETE_WINDOW", self.destroy)

    def update_alpha(self, val):
        if self.overlay and tk.Toplevel.winfo_exists(self.overlay):
            self.overlay.attributes("-alpha", float(val))

    def toggle_clickthrough(self):
        if not (self.overlay and tk.Toplevel.winfo_exists(self.overlay)):
            return

        if not hasattr(ctypes, "windll"):
            messagebox.showwarning("Systém", "Proklikávání je dostupné pouze na Windows.")
            return

        if not self.is_locked:
            self.overlay.overrideredirect(True)
            self.overlay.update_idletasks()

            hwnd = ctypes.windll.user32.GetParent(self.overlay.winfo_id())
            if hwnd == 0:
                hwnd = self.overlay.winfo_id()

            style = ctypes.windll.user32.GetWindowLongW(hwnd, GWL_EXSTYLE)
            style |= (WS_EX_TRANSPARENT | WS_EX_LAYERED)
            ctypes.windll.user32.SetWindowLongW(hwnd, GWL_EXSTYLE, style)

            self.is_locked = True
            self.btn_toggle.config(
                text="🔓 Odemknout (posun / změna velikosti)", 
                bg="#f44336"
            )
        else:
            self.overlay.overrideredirect(False)
            self.overlay.update_idletasks()

            hwnd = ctypes.windll.user32.GetParent(self.overlay.winfo_id())
            if hwnd == 0:
                hwnd = self.overlay.winfo_id()

            style = ctypes.windll.user32.GetWindowLongW(hwnd, GWL_EXSTYLE)
            style &= ~WS_EX_TRANSPARENT
            ctypes.windll.user32.SetWindowLongW(hwnd, GWL_EXSTYLE, style)

            self.is_locked = False
            self.btn_toggle.config(
                text="🔒 Zamknout & Zapnout proklikávání", 
                bg="#4CAF50"
            )

    def update_ranks(self, rank_map: Dict[Tuple[int, int], int]):
        """Aktualizuje čísla v mřížce podle vypočítaného rank_map."""
        if not (self.overlay and tk.Toplevel.winfo_exists(self.overlay)):
            return
        for r in range(5):
            for c in range(5):
                rk = rank_map.get((r, c))
                txt = str(rk) if rk is not None else ""
                self.labels[r][c].config(text=txt)

    def destroy(self):
        try:
            if self.overlay and tk.Toplevel.winfo_exists(self.overlay):
                self.overlay.destroy()
        except Exception:
            pass
        try:
            if self.ctrl and tk.Toplevel.winfo_exists(self.ctrl):
                self.ctrl.destroy()
        except Exception:
            pass

# ---------------- App ----------------
class App:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Harryho puzzle – Everything Upgrade Tree (GUI)")
        self.root.geometry(DEFAULT_CONFIG["root_geometry"])

        # motiv (výchozí tmavý)
        self.C = dict(PALETTE_DARK)

        # ttk styl
        self.style = ttk.Style(self.root)
        try:
            self.style.theme_use('clam')
        except Exception:
            pass
        self._configure_styles()

        # --- horní panel ---
        self.top_panel = ttk.Frame(self.root); self.top_panel.pack(fill='x', padx=12, pady=(10, 6))

        # motiv toggle
        self.light_mode = tk.BooleanVar(value=False)
        ttk.Checkbutton(self.top_panel, text="Světlý motiv", variable=self.light_mode, command=self.on_theme_toggle).grid(row=0, column=0, padx=(0, 12), sticky='w')

        # RGB
        ttk.Label(self.top_panel, text="Barva pozadí (RGB):").grid(row=0, column=1, padx=(6, 12), sticky='w')
        self.r_var = tk.IntVar(value=18); self.g_var = tk.IntVar(value=18); self.b_var = tk.IntVar(value=18)
        self._mk_slider(self.top_panel, "R", self.r_var, 0, 2)
        self._mk_slider(self.top_panel, "G", self.g_var, 0, 4)
        self._mk_slider(self.top_panel, "B", self.b_var, 0, 6)
        self.color_preview = tk.Canvas(self.top_panel, width=56, height=20, highlightthickness=0, bg=self.C['BG'])
        self.color_preview.grid(row=0, column=8, padx=(12, 0))

        # perzistence
        self.save_grid_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(self.top_panel, text="Ukládat obsah mřížky", variable=self.save_grid_var).grid(row=0, column=9, padx=(12, 8))
        ttk.Button(self.top_panel, text="Uložit nastavení", command=self.save_config).grid(row=0, column=10, padx=(4, 8))
        ttk.Button(self.top_panel, text="Obnovit výchozí nastavení", command=self.reset_to_defaults).grid(row=0, column=11, padx=(4, 0))

        # Action & Error log – tlačítko otevřít konzoli
        ttk.Button(self.top_panel, text="Otevřít konzoli (ACT/ERR/OK)", command=self.open_console).grid(row=0, column=12, padx=(12, 0))
        
        # HUD Overlay tlačítko
        ttk.Button(self.top_panel, text="🎯 HUD Overlay", command=self.open_overlay).grid(row=0, column=13, padx=(12, 0))
        self.overlay_win: Optional[OverlayWindow] = None

        # RGB callbacky
        self.r_var.trace_add('write', self.update_bg_color)
        self.g_var.trace_add('write', self.update_bg_color)
        self.b_var.trace_add('write', self.update_bg_color)

        # --- hlavní grid + side panel ---
        self.grid_panel = ttk.Frame(self.root); self.grid_panel.pack(side='left', padx=(12, 6), pady=6, anchor='n')
        self.side_panel = ttk.Frame(self.root); self.side_panel.pack(side='left', fill='y', padx=(6, 12), pady=6, anchor='n')
        ttk.Label(self.grid_panel, text="Vstup 5×5 (auto detekce typu na buňku)").grid(row=0, column=0, columnspan=5, pady=(0, 6))

        self.entries: List[List[tk.Entry]] = []
        self.entry_vars: List[List[tk.StringVar]] = []
        for r in range(5):
            row_e, row_v = [], []
            for c in range(5):
                var = tk.StringVar()
                ent = tk.Entry(self.grid_panel, width=15, font=MONO_FONT,
                               bg=self.C['EMPTY_BG'], fg=self.C['FG'], insertbackground=self.C['FG'],
                               relief='flat', highlightthickness=1, highlightbackground="#333", highlightcolor="#666")
                ent.grid(row=r+1, column=c, padx=3, pady=3)
                ent.config(textvariable=var)
                var.trace_add('write', self.on_change)
                row_e.append(ent); row_v.append(var)
            self.entries.append(row_e); self.entry_vars.append(row_v)

        # ---- overlay rank labels (5×5) ----
        self.rank_labels: List[List[tk.Label]] = []
        for r in range(5):
            row = []
            for c in range(5):
                lab = tk.Label(self.grid_panel, text="", font=("Segoe UI", 9, "bold"),
                               fg=COL_RANK, bg=self.C['OK_BG'])
                lab.place(x=0, y=0)
                row.append(lab)
            self.rank_labels.append(row)
        # aktualizace pozice overlayů při změně layoutu
        self.grid_panel.bind("<Configure>", lambda e: self.position_overlays())

        # --- ovladače pod gridem ---
        self.btns_panel = ttk.Frame(self.grid_panel); self.btns_panel.grid(row=7, column=0, columnspan=5, pady=(10, 0))
        ttk.Button(self.btns_panel, text="Vyčistit vše", command=self.clear_all).grid(row=0, column=0, padx=4)
        ttk.Button(self.btns_panel, text="Zkopírovat výstup (25 řádků)", command=self.copy_output).grid(row=0, column=1, padx=4)
        ttk.Button(self.btns_panel, text="HUD Overlay", command=self.open_overlay).grid(row=0, column=2, padx=4)

        # --- rychlé ovládání pro malé displeje (menu + info) ---
        self.bottom_menu = ttk.Frame(self.grid_panel)
        self.bottom_menu.grid(row=9, column=0, columnspan=5, pady=(8, 6))
        ttk.Button(self.bottom_menu, text="☰ Menu", command=self.open_quick_menu).grid(row=0, column=0, padx=4)
        self.side_visible = tk.BooleanVar(value=True)
        ttk.Button(self.bottom_menu, text="ℹ️ Info panel", command=self.toggle_side_panel).grid(row=0, column=1, padx=4)

        # status
        self.status = ttk.Label(self.grid_panel, text="Připraveno", anchor='w')
        self.status.grid(row=8, column=0, columnspan=5, sticky='we', pady=(10, 0))

        # --- side info (panel) ---
        self.info_text = tk.Text(self.side_panel, width=48, height=28, bg=self.C['PANEL_BG'], fg=self.C['FG'],
                                 insertbackground=self.C['FG'], bd=0, relief='flat', font=MONO_FONT)
        self.info_text.pack(fill='both', expand=True)
        self.info_text.insert('1.0', self._help_text())
        self.info_text.config(state='disabled')

        # --- Info jako okno (volitelné) ---
        self.info_as_window = tk.BooleanVar(value=False)
        self.info_window = None
        self.info_window_text = None

        # --- výstupní okno ---
        self.out = tk.Toplevel(self.root)
        self.out.title("Výstup – 25 řádků (OK ↑, ERR, EMPTY ↓)")
        self.out.geometry(DEFAULT_CONFIG["out_geometry"])

        # legenda (barevná)
        self.legend_text = tk.Text(self.out, height=3, bg=self.C['BG'], fg=self.C['FG'], bd=0,
                                   relief='flat', wrap='word', font=("Segoe UI", 9))
        self.legend_text.pack(fill='x', padx=8, pady=(8, 4))
        self._build_legend()

        # výstupní tabulka
        self.out_text = tk.Text(self.out, bg=self.C['PANEL_BG'], fg=self.C['FG'], insertbackground=self.C['FG'],
                                bd=0, relief='flat', font=MONO_FONT)
        self.out_text.pack(fill='both', expand=True, padx=8, pady=8)
        self._init_output_tags()

        # konzole (Action & Error log) – lazy
        self.console = None
        self.console_text = None
        self.console_filters = {"ACT": tk.BooleanVar(value=True),
                                "ERR": tk.BooleanVar(value=True),
                                "OK":  tk.BooleanVar(value=True)}
        self.console_autoscroll = tk.BooleanVar(value=True)
        self._log_buffer: List[Tuple[str, str, str]] = []  # (ts, level, msg)
        self._prev_errors: Dict[Tuple[int, int], str] = {}

        # perzistence a zavírání
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.out.protocol("WM_DELETE_WINDOW", self.on_close)

        # aplikuj barvy + načti konfiguraci
        self._apply_window_colors()
        self.load_config()

        # responsive: sleduj změnu velikosti hlavního okna
        self.root.bind("<Configure>", self._on_root_resize)

        # první vyhodnocení
        self.pending_after: Optional[str] = None
        self._last_lines: List[str] = []
        self.evaluate()

        self.root.after_idle(self._enable_enter_navigation)

    def open_overlay(self):
        if self.overlay_win and self.overlay_win.ctrl and tk.Toplevel.winfo_exists(self.overlay_win.ctrl):
            self.overlay_win.ctrl.deiconify()
            self.overlay_win.ctrl.lift()
            return
        self.overlay_win = OverlayWindow(self.root)
        self.evaluate()
        self.log("ACT", "HUD Overlay opened")

    # --------------- Quick menu & panel toggling ---------------
    def open_quick_menu(self):
        if hasattr(self, "_quick_menu") and self._quick_menu and tk.Toplevel.winfo_exists(self._quick_menu):
            self._quick_menu.deiconify(); self._quick_menu.lift()
            return
        self._quick_menu = tk.Toplevel(self.root)
        self._quick_menu.title("Rychlé menu")
        self._quick_menu.configure(bg=self.C['BG'])
        self._quick_menu.resizable(False, False)

        frm_act = ttk.LabelFrame(self._quick_menu, text="Akce"); frm_act.pack(fill='x', padx=10, pady=(10, 6))
        ttk.Button(frm_act, text="Vyčistit vše", command=self.clear_all).pack(side='left', padx=4, pady=6)
        ttk.Button(frm_act, text="Zkopírovat výstup", command=self.copy_output).pack(side='left', padx=4, pady=6)
        ttk.Button(frm_act, text="HUD Overlay", command=self.open_overlay).pack(side='left', padx=4, pady=6)  # <-- ZDE
        ttk.Button(frm_act, text="Konzole (ACT/ERR/OK)", command=self.open_console).pack(side='left', padx=4, pady=6)

        frm_view = ttk.LabelFrame(self._quick_menu, text="Zobrazení"); frm_view.pack(fill='x', padx=10, pady=6)
        ttk.Checkbutton(frm_view, text="Světlý motiv", variable=self.light_mode, command=self.on_theme_toggle).pack(side='left', padx=4, pady=6)
        ttk.Checkbutton(frm_view, text="Zobrazit Info panel", variable=self.side_visible, command=self.toggle_side_panel).pack(side='left', padx=4, pady=6)
        ttk.Checkbutton(frm_view, text="Info jako okno (Toplevel)", variable=self.info_as_window, command=self.on_info_as_window_toggle).pack(side='left', padx=12, pady=6)
        ttk.Button(frm_view, text="Otevřít Info okno", command=self.open_info_window).pack(side='left', padx=6, pady=6)

        frm_rgb = ttk.LabelFrame(self._quick_menu, text="Barva pozadí (RGB)"); frm_rgb.pack(fill='x', padx=10, pady=6)
        self._mk_slider(frm_rgb, "R", self.r_var, 0, 0)
        self._mk_slider(frm_rgb, "G", self.g_var, 0, 2)
        self._mk_slider(frm_rgb, "B", self.b_var, 0, 4)

        frm_set = ttk.LabelFrame(self._quick_menu, text="Nastavení"); frm_set.pack(fill='x', padx=10, pady=(6, 10))
        ttk.Checkbutton(frm_set, text="Ukládat obsah mřížky", variable=self.save_grid_var).pack(side='left', padx=4, pady=6)
        ttk.Button(frm_set, text="Uložit nastavení", command=self.save_config).pack(side='left', padx=4, pady=6)
        ttk.Button(frm_set, text="Obnovit výchozí", command=self.reset_to_defaults).pack(side='left', padx=4, pady=6)

    def on_info_as_window_toggle(self):
        if self.info_as_window.get():
            self.open_info_window()
        else:
            self.close_info_window()

    def open_info_window(self):
        if self.info_window and tk.Toplevel.winfo_exists(self.info_window):
            self.info_window.deiconify(); self.info_window.lift()
        else:
            self.info_window = tk.Toplevel(self.root)
            self.info_window.title("Info")
            self.info_window.configure(bg=self.C['BG'])
            self.info_window_text = tk.Text(self.info_window, width=56, height=28,
                                            bg=self.C['PANEL_BG'], fg=self.C['FG'],
                                            insertbackground=self.C['FG'], bd=0, relief='flat', font=MONO_FONT)
            self.info_window_text.pack(fill='both', expand=True, padx=8, pady=8)
            self.info_window.protocol("WM_DELETE_WINDOW", self.close_info_window)
            # když je info jako okno, skryj panel
            if self.side_visible.get():
                self.side_visible.set(False)
                self.toggle_side_panel()
            self.info_as_window.set(True)

    def close_info_window(self):
        if self.info_window and tk.Toplevel.winfo_exists(self.info_window):
            try:
                self.info_window.destroy()
            except Exception:
                pass
        self.info_window = None
        self.info_window_text = None
        self.info_as_window.set(False)

    def toggle_side_panel(self):
        """Zobrazí/skrývá postranní Info panel – NEzobrazuje panel, pokud je aktivní Info-okno."""
        if self.info_as_window.get():
            try:
                self.side_panel.pack_forget()
            except Exception:
                pass
            return
        if self.side_visible.get():
            # přepnout na skrytí
            try:
                self.side_panel.pack_forget()
            except Exception:
                pass
            self.side_visible.set(False)
        else:
            self.side_panel.pack(side='left', fill='y', padx=(6, 12), pady=6, anchor='n')
            self.side_visible.set(True)
            self.position_overlays()

    def _on_root_resize(self, event):
        """Jednoduchý responsive: při malé šířce schovej horní + boční panel (ne však Info-okno)."""
        try:
            w = self.root.winfo_width()
        except Exception:
            return
        if w < COMPACT_BREAKPOINT:
            try:
                self.top_panel.pack_forget()
            except Exception:
                pass
            if self.side_visible.get():
                self.side_visible.set(False)
                self.toggle_side_panel()
        else:
            try:
                self.top_panel.pack_forget()
            except Exception:
                pass
            self.top_panel.pack(fill='x', padx=12, pady=(10, 6))
            if self.side_visible.get() and not self.info_as_window.get():
                self.toggle_side_panel()

    # ---------------- Styl, legenda, barvení ----------------
    def _configure_styles(self):
        self.root.configure(bg=self.C['BG'])
        self.style.configure("TLabel", background=self.C['BG'], foreground=self.C['FG'], font=UI_FONT)
        self.style.configure("TFrame", background=self.C['BG'])
        self.style.configure("TButton", background=self.C['PANEL_BG'], foreground=self.C['FG'], font=UI_FONT)
        self.style.map("TButton", background=[('active', '#2A2A2A')])

    def _apply_window_colors(self):
        try:
            self.root.configure(bg=self.C['BG']); self.out.configure(bg=self.C['BG'])
            for w in (self.grid_panel, self.side_panel, self.top_panel):
                w.configure(style="TFrame")
        except Exception:
            pass
        self.info_text.configure(bg=self.C['PANEL_BG'], fg=self.C['FG'], insertbackground=self.C['FG'])
        if self.legend_text:
            self.legend_text.configure(bg=self.C['BG'], fg=self.C['FG'])
        if self.out_text:
            self.out_text.configure(bg=self.C['PANEL_BG'], fg=self.C['FG'], insertbackground=self.C['FG'])
        # přebarvit vstupy + overlay bg
        for r in range(5):
            for c in range(5):
                self.entries[r][c].configure(fg=self.C['FG'], insertbackground=self.C['FG'])
                self.rank_labels[r][c].configure(bg=self.C['OK_BG'])
        # Info okno
        if self.info_window_text:
            try:
                self.info_window.configure(bg=self.C['BG'])
                self.info_window_text.configure(bg=self.C['PANEL_BG'], fg=self.C['FG'], insertbackground=self.C['FG'])
            except Exception:
                pass

    def on_theme_toggle(self):
        self.C = dict(PALETTE_LIGHT if self.light_mode.get() else PALETTE_DARK)
        self._configure_styles()
        self._apply_window_colors()
        self._build_legend()
        self._init_output_tags()
        self.log("ACT", f"theme={'light' if self.light_mode.get() else 'dark'}")
        self.evaluate()

    def _build_legend(self):
        self.legend_text.configure(state='normal'); self.legend_text.delete('1.0', 'end')
        self.legend_text.tag_configure('lg_idx',   foreground=COL_IDX,   font=("Segoe UI", 9, 'bold'))
        self.legend_text.tag_configure('lg_rank',  foreground=COL_RANK,  font=("Segoe UI", 9, 'bold'))
        self.legend_text.tag_configure('lg_typ',   foreground=COL_TYP,   font=("Segoe UI", 9, 'bold'))
        self.legend_text.tag_configure('lg_val',   foreground=COL_VALUE, font=("Segoe UI", 9, 'bold'))
        self.legend_text.tag_configure('lg_rc',    foreground=COL_RC,    font=("Segoe UI", 9, 'bold'))
        self.legend_text.tag_configure('lg_state', foreground=COL_STATE, font=("Segoe UI", 9, 'bold'))
        self.legend_text.tag_configure('lg_sep',   foreground=self.C['SEP'])
        self.legend_text.tag_configure('lg_ok',    foreground=COL_RANK)
        self.legend_text.tag_configure('lg_err',   foreground=self.C['ERR_TEXT'])
        self.legend_text.tag_configure('lg_empty', foreground=self.C['EMPTY_TEXT'])

        text = ("Legenda: "
                "idx = lineární index (1–25), "
                "rank = pořadí kliknutí (jen OK), "
                "typ = P1/P2/P3/P4, "
                "výstup = číslo nebo „x = …“, "
                "(r,c) = souřadnice 1–5, "
                "stav = OK/ERR/EMPTY\n"
                "Řazení: OK nahoře vzestupně podle hodnoty (stabilní při rovnosti), "
                "ERR a EMPTY dole podle idx.")
        self.legend_text.insert('1.0', text)

        def _tag_word(word, tag):
            idx = '1.0'
            while True:
                pos = self.legend_text.search(word, idx, stopindex='end')
                if not pos: break
                self.legend_text.tag_add(tag, pos, f"{pos}+{len(word)}c")
                idx = f"{pos}+{len(word)}c"

        for word, tag in [("idx", "lg_idx"), ("rank", "lg_rank"), ("typ", "lg_typ"),
                          ("výstup", "lg_val"), ("(r,c)", "lg_rc"), ("stav", "lg_state"),
                          ("OK", "lg_ok"), ("ERR", "lg_err"), ("EMPTY", "lg_empty"), ("Řazení:", "lg_sep")]:
            _tag_word(word, tag)
        self.legend_text.configure(state='disabled')

    def _init_output_tags(self):
        if not self.out_text: return
        self.out_text.tag_configure('col_idx',   foreground=COL_IDX)
        self.out_text.tag_configure('col_rank',  foreground=COL_RANK)
        self.out_text.tag_configure('col_typ',   foreground=COL_TYP)
        self.out_text.tag_configure('col_val',   foreground=COL_VALUE)
        self.out_text.tag_configure('col_rc',    foreground=COL_RC)
        self.out_text.tag_configure('col_state', foreground=COL_STATE)
        self.out_text.tag_configure('sep_line',  foreground=self.C['SEP'])
        self.out_text.tag_configure('header',    foreground=self.C['FG'], font=("Consolas", 11, "bold"))

    def _apply_column_colors(self, total_lines: int):
        # header + separator
        self.out_text.tag_add('header', "1.0", "1.end")
        self.out_text.tag_add('sep_line', "2.0", "2.end")

        for ln in range(3, total_lines + 1):
            line = self.out_text.get(f"{ln}.0", f"{ln}.end")
            if not line.strip():
                continue

            parts = line.split()
            col = 0
            idx = 0

            for part in parts:
                start = line.find(part, idx)
                end = start + len(part)

                if col == 0:
                    tag = 'col_idx'
                elif col == 1:
                    tag = 'col_rank'
                elif col == 2:
                    tag = 'col_typ'
                elif col == 3:
                    tag = 'col_val'
                elif col == 4:
                    tag = 'col_rc'
                elif col == 5:
                    tag = 'col_state'
                else:
                    tag = None

                if tag is not None:
                    self.out_text.tag_add(
                        tag,
                        f"{ln}.{start}",
                        f"{ln}.{end}"
                    )

                idx = end
                col += 1

    # --------------- Overlay rank v gridu ---------------
    def position_overlays(self):
        self.root.update_idletasks()
        for r in range(5):
            for c in range(5):
                ent = self.entries[r][c]
                try:
                    x = ent.winfo_x(); y = ent.winfo_y()
                    w = ent.winfo_width()
                    self.rank_labels[r][c].place(x=x + w - 18, y=y + 2)
                except Exception:
                    pass

    def update_overlays(self, rank_map: Dict[Tuple[int, int], int],
                        errors_map: Dict[Tuple[int, int], str],
                        empty_set: set):
        for r in range(5):
            for c in range(5):
                lab = self.rank_labels[r][c]
                if (r, c) in empty_set or (r, c) in errors_map:
                    lab.config(text="")
                else:
                    rk = rank_map.get((r, c))
                    lab.config(text=str(rk) if rk is not None else "")
        # barvy overlayů dle motivu
        for r in range(5):
            for c in range(5):
                self.rank_labels[r][c].configure(bg=self.C['OK_BG'], fg=COL_RANK)

    # --------------- Perzistence a obsluha GUI ---------------
    def load_config(self):
        cfg = DEFAULT_CONFIG.copy()
        if CONFIG_PATH.exists():
            try:
                data = json.loads(CONFIG_PATH.read_text(encoding="utf-8"))
                cfg.update(data)
            except Exception:
                pass
        # Motiv
        self.light_mode.set(cfg.get("theme", "dark") == "light")
        self.on_theme_toggle()  # aplikuje paletu i styly
        # RGB
        r, g, b = cfg.get("rgb", [18, 18, 18])
        self.r_var.set(int(r)); self.g_var.set(int(g)); self.b_var.set(int(b))
        self.update_bg_color()
        # Geometrie
        try:
            self.root.geometry(cfg.get("root_geometry", DEFAULT_CONFIG["root_geometry"]))
            self.out.geometry(cfg.get("out_geometry", DEFAULT_CONFIG["out_geometry"]))
        except Exception:
            pass
        # Ukládání mřížky
        self.save_grid_var.set(bool(cfg.get("save_grid", False)))
        grid = cfg.get("grid", [])
        if self.save_grid_var.get() and isinstance(grid, list) and len(grid) == 5:
            for r in range(5):
                if not isinstance(grid[r], list) or len(grid[r]) != 5: continue
                for c in range(5):
                    try:
                        self.entry_vars[r][c].set(str(grid[r][c]))
                    except Exception:
                        pass
        # Start v kompaktním režimu?
        if cfg.get("start_compact", False):
            try:
                self.top_panel.pack_forget()
            except Exception:
                pass
            if self.side_visible.get():
                self.side_visible.set(False)
                self.toggle_side_panel()
        self.log("ACT", "config loaded")

    def save_config(self):
        cfg = {
            "theme": "light" if self.light_mode.get() else "dark",
            "rgb": [self.r_var.get(), self.g_var.get(), self.b_var.get()],
            "root_geometry": self.root.winfo_geometry(),
            "out_geometry": self.out.winfo_geometry(),
            "console_geometry": self.console.winfo_geometry() if self.console else DEFAULT_CONFIG["console_geometry"],
            "save_grid": self.save_grid_var.get(),
            # uložíme, zda je okno pod breakpointem (kompaktní režim)
            "start_compact": (self.root.winfo_width() < COMPACT_BREAKPOINT),
        }
        if self.save_grid_var.get():
            grid = [[self.entry_vars[r][c].get() for c in range(5)] for r in range(5)]
            cfg["grid"] = grid
        try:
            CONFIG_PATH.write_text(json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8")
            self.status.config(text=f"Nastavení uloženo → {CONFIG_PATH}")
            self.log("ACT", "config saved")
        except Exception as e:
            self.status.config(text=f"Ukládání selhalo: {e}")
            self.log("ERR", f"config save failed: {e}")

    def on_close(self):
        self.save_config()
        try:
            if self.overlay_win: self.overlay_win.destroy()
            if self.console: self.console.destroy()
            self.out.destroy()
        except Exception:
            pass
        self.root.destroy()

    def reset_to_defaults(self):
        ok = messagebox.askyesno(
            "Obnovit výchozí nastavení",
            "Vrátit aplikaci do výchozího stavu (tmavý motiv, RGB 18/18/18, výchozí okna, prázdná mřížka) a smazat uložený konfigurační soubor?"
        )
        if not ok:
            self.log("ACT", "reset cancelled")
            return
        # motiv + styly
        self.light_mode.set(False)
        self.C = dict(PALETTE_DARK)
        self._configure_styles()
        self._apply_window_colors()
        self._build_legend()
        self._init_output_tags()
        # RGB
        r, g, b = DEFAULT_CONFIG["rgb"]
        self.r_var.set(r); self.g_var.set(g); self.b_var.set(b)
        self.update_bg_color()
        # geometrie
        try:
            self.root.geometry(DEFAULT_CONFIG["root_geometry"])
            self.out.geometry(DEFAULT_CONFIG["out_geometry"])
        except Exception:
            pass
        # mřížka
        for r in range(5):
            for c in range(5):
                self.entry_vars[r][c].set("")
        self.save_grid_var.set(False)
        # smazat config
        try:
            if CONFIG_PATH.exists():
                CONFIG_PATH.unlink()
        except Exception:
            pass
        self.evaluate()
        self.status.config(text="Vráceno na výchozí nastavení (config odstraněn)")
        self.log("ACT", "reset to defaults")

    # ---------------- GUI helpers ----------------
    # ===== ENTER / SHIFT+ENTER NAVIGATION (SAFE, NO GUI CHANGES) =====

    def _enable_enter_navigation(self):
        # plochý seznam Entry widgetů v pořadí řádek-po-řádku
        self._entry_list = [e for row in self.entries for e in row]
        self._entry_index = {e: i for i, e in enumerate(self._entry_list)}

        for e in self._entry_list:
            e.bind("<Return>", self._on_enter_left)
            e.bind("<Shift-Return>", self._on_enter_right)

    def _on_enter_left(self, event):
        return self._move_entry(+1)

    def _on_enter_right(self, event):
        return self._move_entry(-1)

    def _move_entry(self, delta):
        w = self.root.focus_get()
        if w not in self._entry_index:
            return "break"

        idx = self._entry_index[w]
        idx = (idx + delta) % len(self._entry_list)  # ✅ warp

        nxt = self._entry_list[idx]
        nxt.focus_set()
        nxt.icursor('end')
        return "break"
    
    def _mk_slider(self, parent, label, var, row, col):
        ttk.Label(parent, text=label).grid(row=row, column=col, sticky='w')
        s = ttk.Scale(parent, from_=0, to=255, orient='horizontal', variable=var, length=180)
        s.grid(row=row, column=col+1, padx=(6, 12))

    def update_bg_color(self, *args):
        # RGB override pouze pro „BG“ oken/panelů (motiv drží kontrasty)
        r, g, b = self.r_var.get(), self.g_var.get(), self.b_var.get()
        r = max(0, min(255, r)); g = max(0, min(255, g)); b = max(0, min(255, b))
        color = f"#{r:02x}{g:02x}{b:02x}"
        try:
            self.root.configure(bg=color); self.out.configure(bg=color)
            self.grid_panel.configure(style="TFrame"); self.side_panel.configure(style="TFrame"); self.top_panel.configure(style="TFrame")
        except Exception:
            pass
        try:
            self.legend_text.configure(bg=color)
        except Exception:
            pass
        self.color_preview.configure(bg=color)
        self.log("ACT", f"rgb={r},{g},{b}")

    def clear_all(self):
        for r in range(5):
            for c in range(5):
                self.entry_vars[r][c].set("")
        self.evaluate()
        self.log("ACT", "grid cleared")

    def on_change(self, *args):
        if self.pending_after is not None:
            try: self.root.after_cancel(self.pending_after)
            except Exception: pass
        self.pending_after = self.root.after(120, self.evaluate)

    def get_grid_texts(self) -> List[List[str]]:
        return [[self.entry_vars[r][c].get() for c in range(5)] for r in range(5)]

    # ---------------- Evaluate + Output + Logging ----------------
    def evaluate(self):
        self.pending_after = None
        texts = self.get_grid_texts()
        entries_map, display_map, errors_map, empty_set = compute_maps(texts)

        # barvy buněk dle stavu
        for r in range(5):
            for c in range(5):
                self.entries[r][c].configure(bg=self.C['EMPTY_BG'] if (r, c) in empty_set else self.C['OK_BG'])
        for (r, c), _ in errors_map.items():
            self.entries[r][c].configure(bg=self.C['ERROR_BG'])

        # --- Sestav Info obsah ---
        info_lines: List[str] = []
        if entries_map:
            info_lines.append("Detekované buňky (validní):")
            for (r, c), (typ, val) in sorted(entries_map.items(), key=lambda t: (t[0][0]*5 + t[0][1])):
                disp = display_map.get((r, c), str(val))
                info_lines.append(f"[{r+1},{c+1}] {typ:<2} = {disp}")
        else:
            info_lines.append("Zatím žádná validní data.")
        if errors_map:
            info_lines.append("")
            info_lines.append("Chyby:")
            for (r, c), msg in sorted(errors_map.items(), key=lambda t: (t[0][0]*5 + t[0][1])):
                info_lines.append(f"[{r+1},{c+1}] {msg}")
        info_buf = "\n".join(info_lines)

        # Zapiš Info do panelu
        self.info_text.config(state='normal'); self.info_text.delete('1.0', 'end')
        self.info_text.insert('1.0', info_buf)
        self.info_text.config(state='disabled')

        # Zapiš i do Info okna (pokud existuje)
        if self.info_window_text:
            try:
                self.info_window_text.config(state='normal'); self.info_window_text.delete('1.0', 'end')
                self.info_window_text.insert('1.0', info_buf)
                self.info_window_text.config(state='disabled')
            except Exception:
                pass
        # Výstup: 25 řádků (OK ↑, ERR, EMPTY ↓), 1-based idx & (r,c)
        valid_sorted = stable_sorted(entries_map)
        rank_map = {(r, c): i for i, (r, c, _, _) in enumerate(valid_sorted, start=1)}
        err_sorted = sorted(errors_map.keys(), key=lambda rc: rc[0]*5 + rc[1])
        emp_sorted = sorted(empty_set, key=lambda rc: rc[0]*5 + rc[1])

        ordered_rows: List[Tuple[int, str, str, str, str, str]] = []
        for (r, c, typ, val) in valid_sorted:
            idx1 = r*5 + c + 1
            ordered_rows.append((idx1, str(rank_map[(r, c)]), typ,
                                 display_map.get((r, c), str(val)),
                                 f"({r+1},{c+1})", "OK"))
        for (r, c) in err_sorted:
            idx1 = r*5 + c + 1
            ordered_rows.append((idx1, "-", "-", "-", f"({r+1},{c+1})", "ERR"))
        for (r, c) in emp_sorted:
            idx1 = r*5 + c + 1
            ordered_rows.append((idx1, "-", "-", "-", f"({r+1},{c+1})", "EMPTY"))

        if len(ordered_rows) != 25:
            present = {row[0] for row in ordered_rows}
            for idx1 in range(1, 26):
                if idx1 not in present:
                    r, c = divmod(idx1-1, 5)
                    ordered_rows.append((idx1, "-", "-", "-", f"({r+1},{c+1})", "EMPTY"))

        header = f"{'idx':>3} {'rank':>4} {'typ':^3} {'výstup':>12} {'(r,c)':>6} {'stav'}"
        sep = "-" * len(header)
        lines = [header, sep]
        for (idx1, rank, typ, disp, rc_str, state) in ordered_rows:
            lines.append(f"{idx1:>3} {rank:>4} {typ:^3} {disp:>12} {rc_str:>6} {state}")

        self.out_text.delete('1.0', 'end')
        self.out_text.insert('1.0', "\n".join(lines) + "\n")
        self._last_lines = lines[:]
        self._init_output_tags()
        self._apply_column_colors(total_lines=len(lines))

        # Overlay (rank u OK buněk)
        self.update_overlays(rank_map, errors_map, empty_set)
        self.position_overlays()

        # Status + logging
        valid_cnt, err_cnt, emp_cnt = len(valid_sorted), len(err_sorted), len(emp_sorted)
        self.status.config(
            text=f"Validních: {valid_cnt} Chyb: {err_cnt} Prázdných: {emp_cnt} Řazení: OK podle hodnoty; ERR/EMPTY podle idx"
        )
        self.log("ACT", f"evaluate: ok={valid_cnt} err={err_cnt} empty={emp_cnt}")

        # zaloguj nové chyby a vyřešené chyby
        new_err_keys = set(errors_map.keys())
        old_err_keys = set(self._prev_errors.keys())
        for rc in sorted(new_err_keys - old_err_keys, key=lambda rc: rc[0]*5 + rc[1]):
            r, c = rc
            self.log("ERR", f"cell({r+1},{c+1}): {errors_map[rc]}")
        for rc in sorted(old_err_keys - new_err_keys, key=lambda rc: rc[0]*5 + rc[1]):
            r, c = rc
            self.log("OK", f"cell({r+1},{c+1}) fixed")
            
        # Aktualizace HUD Overlay okna (pokud existuje)
        if self.overlay_win:
            self.overlay_win.update_ranks(rank_map)

        self._prev_errors = dict(errors_map)

    def copy_output(self):
        txt = "\n".join(self._last_lines) if self._last_lines else ""
        self.root.clipboard_clear(); self.root.clipboard_append(txt)
        self.status.config(text="Výstup (25 řádků) zkopírován do schránky")
        self.log("ACT", "output copied")

    # --------------- Action & Error log ---------------
    def open_console(self):
        if self.console and tk.Toplevel.winfo_exists(self.console):
            self.console.deiconify(); self.console.lift()
            return
        self.console = tk.Toplevel(self.root)
        self.console.title("Konzole – Action & Error log")
        self.console.geometry(DEFAULT_CONFIG["console_geometry"])
        self.console.configure(bg=self.C['BG'])

        bar = ttk.Frame(self.console); bar.pack(fill='x', padx=8, pady=(8, 4))
        ttk.Checkbutton(bar, text="ACT", variable=self.console_filters["ACT"], command=self.refresh_console).pack(side='left', padx=(0, 8))
        ttk.Checkbutton(bar, text="ERR", variable=self.console_filters["ERR"], command=self.refresh_console).pack(side='left', padx=8)
        ttk.Checkbutton(bar, text="OK",  variable=self.console_filters["OK"],  command=self.refresh_console).pack(side='left', padx=8)
        ttk.Checkbutton(bar, text="Autoscroll", variable=self.console_autoscroll).pack(side='left', padx=(24, 8))
        ttk.Button(bar, text="Copy",  command=self.console_copy).pack(side='right', padx=(8, 0))
        ttk.Button(bar, text="Clear", command=self.console_clear).pack(side='right', padx=(8, 0))

        self.console_text = tk.Text(self.console, bg=self.C['PANEL_BG'], fg=self.C['FG'],
                                    insertbackground=self.C['FG'], bd=0, relief='flat',
                                    font=("Consolas", 10))
        self.console_text.pack(fill='both', expand=True, padx=8, pady=(0, 8))
        self.console_text.tag_configure("TS",  foreground=self.C['EMPTY_TEXT'])
        self.console_text.tag_configure("ACT", foreground="#00BCD4")  # cyan
        self.console_text.tag_configure("ERR", foreground=self.C['ERR_TEXT'])
        self.console_text.tag_configure("OK",  foreground="#8BC34A")
        self.refresh_console()
        self.log("ACT", "console opened")

    def log(self, level: str, msg: str):
        level = level.upper()
        ts = datetime.now().strftime("%H:%M:%S.%f")[:-3]
        self._log_buffer.append((ts, level, msg))
        if self.console and tk.Toplevel.winfo_exists(self.console):
            if self.console_filters.get(level, tk.BooleanVar(value=True)).get():
                self.console_text.insert('end', f"[{ts}] ", ("TS",))
                self.console_text.insert('end', f"[{level}] ", (level,))
                self.console_text.insert('end', f"{msg}\n")
                if self.console_autoscroll.get():
                    self.console_text.see('end')

    def refresh_console(self):
        if not (self.console and self.console_text): return
        self.console_text.delete('1.0', 'end')
        show = {k for k, v in self.console_filters.items() if v.get()}
        for ts, level, msg in self._log_buffer:
            if level in show:
                self.console_text.insert('end', f"[{ts}] ", ("TS",))
                self.console_text.insert('end', f"[{level}] ", (level,))
                self.console_text.insert('end', f"{msg}\n")
                if self.console_autoscroll.get():
                    self.console_text.see('end')

    def console_copy(self):
        if not self.console_text: return
        txt = self.console_text.get('1.0', 'end').rstrip()
        self.console.clipboard_clear(); self.console.clipboard_append(txt)
        self.log("ACT", "console copied")

    def console_clear(self):
        self._log_buffer.clear()
        self.refresh_console()
        self.log("ACT", "console cleared")

    # ---------------- Main & help ----------------
    @staticmethod
    def _help_text() -> str:
        return (
            "Nápověda – typy vstupu (auto detekce):\n"
            " P1 – Číslo: 42, -7, 3.14, 1e3\n"
            " P2 – Shift číslo: !@ (->12), %^& (->567), )! (->01)\n"
            " P3 – Báze: 1A(16), 101(2), Z:36, -A:16\n"
            " P4 – Výraz: 2^8, 3*sqrt(4)+pi, 10 mod 3, floor(5/2), 5!, (3+2)!, a!!\n"
            " – Rovnice: 2x+5 = 11 → x = 3 (lineární v x)\n"
            " – Přiřazení: a=54.4, b=a^2, x=ceil(a+b/7)! → x = ...\n"
            "\n"
            "Indexy a souřadnice ve výstupu jsou 1-based: idx ∈ {1..25}, (r,c) ∈ {1..5}×{1..5}\n"
            "Výstup: 25 řádků – nahoře OK (podle hodnoty), uprostřed ERR, dole EMPTY.\n"
            "Přepínač motivu vlevo nahoře; RGB posuvníky ladí barvu pozadí (BG).\n"
        )

def main():
    root = tk.Tk()
    app = App(root)
    root.mainloop()

if __name__ == "__main__":
    main()