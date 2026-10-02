#!/usr/bin/env python3
"""
Oregairu Nintendo Switch Translation Tool (MAGES SC3 Engine)
Clean rewrite from scratch based on decompiled C# source (SC3Editor/SC3Library/SC3Tool)
and verified working Switch release.

Key Fixes & Features:
1. Verified Charset: Uses resources/ogvd/charset.utf8 (exact charset from working Switch release).
2. Character Name Rendering: Automatically uses full-width ideographic space (U+3000, 80 3F)
   for names instead of ASCII space (80 00, which terminates the nameplate in-engine).
3. Name Ordering: Automatically formats names as 'Surname　GivenName' matching the game's
   official nameplate convention, with configurable modes (english, western, orig, fullwidth).
4. Scene Transition Safety: Reimport automatically pairs each recompiled .msb with its matching
   .scx file into output/, preventing out-of-bounds crashes when advancing past scene endings.
5. Non-Destructive: Source script/ and resources/ directories are strictly read-only and never modified.
6. Clean Extraction & Reimport Workflow:
   - extract:  .msb -> msb_extracted/ , .scx -> scx_extracted/
   - reimport: reads translation files from exported_txt/ and compiles into output/mes00/*.msb
               and output/*.scx
"""

import os
import sys
import glob
import struct
import re
import shutil
import argparse
import unicodedata
from typing import List, Tuple, Optional, Dict, Set

# Ensure UTF-8 output on Windows console
if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding='utf-8')
        sys.stderr.reconfigure(encoding='utf-8')
    except Exception:
        pass


# ============================================================
# Default Paths & Configuration
# ============================================================

BASE_DIR      = os.path.dirname(os.path.abspath(__file__))
SCRIPT_DIR    = os.path.join(BASE_DIR, "script")
TXT_DIR       = os.path.join(BASE_DIR, "exported_txt")
OUTPUT_DIR    = os.path.join(BASE_DIR, "output")
CHARSET_PATH  = os.path.join(BASE_DIR, "resources", "ogvd", "charset.utf8")

MSB_EXTRACTED = os.path.join(BASE_DIR, "msb_extracted")
SCX_EXTRACTED = os.path.join(BASE_DIR, "scx_extracted")


# ============================================================
# Full-Width Character Converter (Matches C# FullWidthConverter)
# ============================================================

STD_ASCII = " !\"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~"
FULL_ASCII = "\u3000！＂＃＄％＆＇（）＊＋，－．／０１２３４５６７８９：；＜＝＞？＠ＡＢＣＤＥＦＧＨＩＪＫＬＭＮＯＰＱＲＳＴＵＶＷＸＹＺ［＼］\uff3e\uff3f\uff40ａｂｃｄｅｆｇｈｉｊｋｌｍｎｏｐｑｒｓｔｕｖｗｘｙｚ｛｜｝～"
TO_FULLWIDTH_MAP = str.maketrans(dict(zip(STD_ASCII, FULL_ASCII)))

def to_fullwidth(text: str) -> str:
    """Convert standard ASCII string to full-width characters."""
    return text.translate(TO_FULLWIDTH_MAP)


# Common Oregairu character names mapping (Western 'Given Surname' -> Japanese 'Surname Given')
KNOWN_NAME_ORDER: Dict[str, str] = {
    "Hachiman Hikigaya": "Hikigaya\u3000Hachiman",
    "Komachi Hikigaya": "Hikigaya\u3000Komachi",
    "Yukino Yukinoshita": "Yukinoshita\u3000Yukino",
    "Haruno Yukinoshita": "Yukinoshita\u3000Haruno",
    "Yui Yuigahama": "Yuigahama\u3000Yui",
    "Saika Totsuka": "Totsuka\u3000Saika",
    "Shizuka Hiratsuka": "Hiratsuka\u3000Shizuka",
    "Shizuka Hikigaya": "Hikigaya\u3000Shizuka",
    "Saki Kawasaki": "Kawasaki\u3000Saki",
    "Taishi Kawasaki": "Kawasaki\u3000Taishi",
    "Keika Kawasaki": "Kawasaki\u3000Keika",
    "Yoshiteru Zaimokuza": "Zaimokuza\u3000Yoshiteru",
    "Hayato Hayama": "Hayama\u3000Hayato",
    "Hina Ebina": "Ebina\u3000Hina",
    "Yumiko Miura": "Miura\u3000Yumiko",
    "Rumi Tsurumi": "Tsurumi\u3000Rumi",
    "Kakeru Tobe": "Tobe\u3000Kakeru",
    "Sho Tobe": "Tobe\u3000Sho",
    "Minami Sagami": "Sagami\u3000Minami",
    "Meguri Shiromeguri": "Shiromeguri\u3000Meguri",
    "Kaori Orimoto": "Orimoto\u3000Kaori",
    "Chika Tamanawa": "Tamanawa\u3000Chika",
    "Iroha Isshiki": "Isshiki\u3000Iroha",
}

# Fallback character mappings for common typography symbols
CHAR_FALLBACKS: Dict[str, str] = {
    '’': "'", '‘': "'", 'ʹ': "'", 'ˊ': "'", 'ˋ': "'", '❜': "'", '`': "'",
    '“': '"', '”': '"', '„': '"',
    '—': '―', '–': '-', '−': '-',
    '♥': '♪', '♡': '♪',
    '┬': 'T',
    '￣': '~',
    'ﾟ': '゜', '゚': '゜', '゙': '゛',
    '¬': '-',
    '\u0301': '', '\u0304': '',  # combining acute & macron
}


# ============================================================
# Charset Loader
# ============================================================

class Charset:
    def __init__(self, direct: List[Optional[str]]):
        self.direct = direct
        self.reverse: Dict[str, int] = {}
        for idx, char in enumerate(direct):
            if char and char not in self.reverse:
                self.reverse[char] = idx

    def decode(self, code: int) -> str:
        idx = code & 0x7FFF
        if idx < len(self.direct) and self.direct[idx] is not None:
            return self.direct[idx]
        return f"<{idx}>"


def load_charset(path: str) -> Charset:
    """Load character table from charset.utf8 safely stripping UTF-8 BOM."""
    if not os.path.isfile(path):
        raise FileNotFoundError(f"Charset file not found: {path}")
    with open(path, 'r', encoding='utf-8-sig') as f:
        lines = [line.rstrip('\r\n') for line in f]
    direct: List[Optional[str]] = []
    for line in lines:
        if line.startswith("␃"):
            break
        direct.append(line if line else None)
    return Charset(direct)


# ============================================================
# SC3 Expression Parser & Encoder (Color tags, etc.)
# ============================================================

EXPR_IMM = 0x696D6D
EXPR_END = 0x656E64

OPINFO = {
    0:  (0, False, False, 'none'),
    1:  (3, False, True,  'bin'),
    2:  (3, False, True,  'bin'),
    3:  (4, False, True,  'bin'),
    4:  (4, False, True,  'bin'),
    5:  (3, False, True,  'bin'),
    6:  (5, False, True,  'bin'),
    7:  (5, False, True,  'bin'),
    8:  (7, False, True,  'bin'),
    9:  (6, False, True,  'bin'),
    10: (5, False, True,  'bin'),
    11: (2, True,  True,  'pre'),
    12: (8, False, True,  'bin'),
    13: (8, False, True,  'bin'),
    14: (9, False, True,  'bin'),
    15: (9, False, True,  'bin'),
    16: (9, False, True,  'bin'),
    17: (9, False, True,  'bin'),
    18: (1, False, False, 'bin'),
    19: (1, False, False, 'bin'),
    20: (2, True,  False, 'pre'),
    21: (2, True,  False, 'pre'),
    22: (0, False, False, 'none'),
    23: (0, False, False, 'none'),
    24: (0, False, False, 'none'),
    25: (0, False, False, 'none'),
    26: (0, False, False, 'none'),
    27: (0, False, False, 'none'),
    28: (0, False, False, 'none'),
    29: (0, False, False, 'none'),
    30: (0, False, False, 'none'),
    31: (0, False, False, 'none'),
    32: (0, False, False, 'none'),
    33: (0, False, False, 'none'),
    34: (0, False, False, 'none'),
    35: (10, False, False, 'none'),
    36: (13, True,  False, 'two'),
    37: (13, True,  False, 'two'),
    38: (13, True,  False, 'two'),
}

class ExprNode:
    __slots__ = ('type', 'value', 'lhs', 'rhs')
    def __init__(self, t, value=0, lhs=None, rhs=None):
        self.type, self.value, self.lhs, self.rhs = t, value, lhs, rhs

    def simplify(self):
        info = OPINFO.get(self.type)
        if info is None: return ExprNode(EXPR_END)
        prec, rassoc, const_ok, ops = info
        if self.type == EXPR_IMM:
            return ExprNode(EXPR_IMM, value=self.value)
        if ops == 'bin':
            l = self.lhs.simplify() if self.lhs else ExprNode(EXPR_END)
            r = self.rhs.simplify() if self.rhs else ExprNode(EXPR_END)
            if l.type == EXPR_IMM and r.type == EXPR_IMM and const_ok:
                v = 0
                if self.type == 1: v = l.value * r.value
                elif self.type == 2: v = 0 if r.value == 0 else int(l.value / r.value)
                elif self.type == 3: v = l.value + r.value
                elif self.type == 4: v = l.value - r.value
                return ExprNode(EXPR_IMM, value=v)
            return ExprNode(self.type, lhs=l, rhs=r)
        return ExprNode(self.type)

def parse_expression(data: bytes, pos: int) -> Tuple[ExprNode, int]:
    start = pos
    stack: List[ExprNode] = []
    while pos < len(data):
        b0 = data[pos]
        if (b0 & 0x80) == 0x80:
            kind = b0 & 0x60
            if kind == 0x00:
                v = b0 & 0x1F
                if b0 & 0x10: v |= 0x7FFFFFE0
                pos += 1
            elif kind == 0x20:
                v = ((b0 & 0x1F) << 8) | data[pos+1]
                if b0 & 0x10: v |= 0x7FFFE000
                pos += 2
            elif kind == 0x40:
                v = ((b0 & 0x1F) << 16) | (data[pos+2] << 8) | data[pos+1]
                if b0 & 0x10: v |= 0x7FE00000
                pos += 3
            else:
                pos += 1
                v = struct.unpack_from('<i', data, pos)[0]
                pos += 4
            stack.append(ExprNode(EXPR_IMM, value=v))
            continue
        pos += 1
        if b0 == 0:
            break
        info = OPINFO.get(b0)
        if not info:
            continue
        cur = ExprNode(b0)
        ops = info[3]
        if ops == 'bin' and len(stack) >= 2:
            cur.rhs = stack.pop()
            cur.lhs = stack.pop()
        elif ops in ('pre', 'post') and len(stack) >= 1:
            cur.lhs = stack.pop()
        stack.append(cur)
    root = stack.pop() if stack else ExprNode(EXPR_END)
    return root, pos - start

def expr_get_raw(val: int) -> bytes:
    if val >= 0 and val <= 15:
        return bytes([(val & 0x1F) | 0x80, 0])
    if val >= 0 and val <= 4095:
        high = ((val >> 8) & 0x1F) | 0xA0
        return bytes([high, val & 0xFF, 0])
    if val >= 0 and val <= 1048575:
        high = ((val >> 16) & 0x1F) | 0xC0
        return bytes([high, val & 0xFF, (val >> 8) & 0xFF, 0])
    return bytes([0xE0]) + struct.pack('<i', val) + bytes([0])


# ============================================================
# String Parser & String Encoder
# ============================================================

class ParsedString:
    __slots__ = ('text', 'name', 'extra_text', 'extra', 'text_bytes')
    def __init__(self):
        self.text: Optional[str] = None
        self.name: Optional[str] = None
        self.extra_text: str = ""
        self.extra: Optional[bytes] = None
        self.text_bytes: List[int] = []


class MesStringParser:
    def __init__(self, charset: Charset):
        self.charset = charset
        self.result = ParsedString()

    def parse(self, data: bytes):
        pos, end = 0, len(data)
        while pos < end:
            b = data[pos]
            if b == 0xFF:
                pos += 1
                self.result.extra = bytes([0xFF])
                continue
            if b < 0x80:
                if b == 1:
                    self.result.name, pos = self._text(data, pos + 1, end)
                    continue
                if b == 2:
                    self.result.text, pos = self._text(data, pos + 1, end)
                    continue
                if b not in (0, 4, 12):
                    self.result.extra = data[pos:end]
                    return
            chunk, pos = self._text(data, pos, end)
            self.result.extra_text += chunk

    def _text(self, data: bytes, pos: int, end: int) -> Tuple[str, int]:
        out = []
        while pos < end and data[pos] != 0xFF:
            if data[pos] < 0x80:
                r = self._cmd(data, pos, end)
                if r is None:
                    break
                s, pos = r
                out.append(s)
            else:
                code = (data[pos] << 8) | data[pos + 1]
                pos += 2
                self.result.text_bytes.append(code & 0x7FFF)
                out.append(self.charset.decode(code))
        return "".join(out), pos

    def _cmd(self, data: bytes, pos: int, end: int) -> Optional[Tuple[str, int]]:
        b = data[pos]
        if b == 0xFF:
            return None
        if b == 9:
            sub, pos = self._text(data, pos + 1, end)
            return f"<prompt>{sub}", pos
        if b == 30:
            return "<charCenter>", pos + 1
        if b == 10:
            return "<upperText>", pos + 1
        if b == 11:
            return "</prompt>", pos + 1
        if b == 12:
            val = (data[pos + 1] << 8) | data[pos + 2]
            return f"<font={val}>", pos + 3
        if b == 14:
            return "<parallel>", pos + 1
        if b == 4:
            node, length = parse_expression(data, pos + 1)
            simp = node.simplify()
            val = simp.value if simp.type == EXPR_IMM else 0
            return f"<color={val:X}>", pos + 1 + length
        if b == 31:
            return "<alt_br>", pos + 1
        if b == 0:
            return "<br>", pos + 1
        return None


TAG_RE = re.compile(r'^<(?P<name>\/?([a-zA-Z0-9  _\-= ]+)\/?)\>')

def encode_string(name: Optional[str],
                  text: Optional[str],
                  extra_text: str,
                  extra_bytes: Optional[bytes],
                  charset: Charset) -> bytes:
    """Encode string entry matching C# MesString.Write output."""
    out = bytearray()
    if extra_text:
        _write_text_segment(extra_text, charset, out)
    if name is not None:
        out.append(1)
        _write_text_segment(name, charset, out)
    if text is not None:
        out.append(2)
        _write_text_segment(text, charset, out)
    if extra_bytes:
        out.extend(extra_bytes)
    return bytes(out)


def _write_text_segment(text: str, charset: Charset, out: bytearray):
    text = text.replace('\r', '').replace('\n', '').replace('&nbsp;', ' ')
    text = unicodedata.normalize('NFKC', text)
    while text:
        m = TAG_RE.match(text)
        if m:
            _write_tag(m.group('name'), out)
            text = text[m.end():]
            continue

        sym = text[0]
        # In Switch MAGES engine, normal space ' ' must be encoded as \u3000 (code 63, 80 3F)
        # because standard ASCII space (80 00) acts as null terminator in nameplates
        # and has zero width in dialogue rendering.
        if sym == ' ':
            sym = '\u3000'

        # Apply typography / symbol fallbacks
        sym = CHAR_FALLBACKS.get(sym, sym)
        if not sym:
            text = text[1:]
            continue

        if sym < ' ':
            out.append(ord(sym))
            text = text[1:]
            continue

        # Prefer single character in charset (codepoint < 7551)
        code = charset.reverse.get(sym)
        if code is not None and code < 7551:
            out.append(((code >> 8) & 0xFF) | 0x80)
            out.append(code & 0xFF)
            text = text[1:]
            continue

        # If not found directly, check full-width equivalent
        fw = to_fullwidth(sym)
        code_fw = charset.reverse.get(fw)
        if code_fw is not None:
            out.append(((code_fw >> 8) & 0xFF) | 0x80)
            out.append(code_fw & 0xFF)
            text = text[1:]
            continue

        # If still not found, check 2-character compound (for files like mail that require it)
        if len(text) >= 2 and text[:2] in charset.reverse:
            code2 = charset.reverse[text[:2]]
            out.append(((code2 >> 8) & 0xFF) | 0x80)
            out.append(code2 & 0xFF)
            text = text[2:]
            continue

        if code is not None:
            out.append(((code >> 8) & 0xFF) | 0x80)
            out.append(code & 0xFF)
            text = text[1:]
            continue

        raise ValueError(f"Character {sym!r} (U+{ord(sym):04X}) not found in charset")


def _write_tag(tag: str, out: bytearray):
    if tag == 'prompt':
        out.append(9)
    elif tag == 'parallel':
        out.append(14)
    elif tag == 'upperText':
        out.append(10)
    elif tag == 'charCenter':
        out.append(30)
    elif tag == '/prompt':
        out.append(11)
    elif tag == 'rcolor':
        out.append(5)
    elif tag.startswith('color='):
        out.append(4)
        out.extend(expr_get_raw(int(tag[6:], 16)))
    elif tag.startswith('font='):
        val = int(tag[5:])
        out.append(12)
        out.append((val >> 8) & 0xFF)
        out.append(val & 0xFF)
    elif tag == 'alt_br':
        out.append(31)
    elif tag in ('br', 'br/'):
        out.append(0)
    else:
        try:
            code = int(tag)
            out.append(((code >> 8) & 0xFF) | 0x80)
            out.append(code & 0xFF)
        except ValueError:
            pass


# ============================================================
# Containers (.msb and .scx)
# ============================================================

class MesFile:
    def __init__(self, data: bytes):
        if data[:4] != b'MES\0':
            raise ValueError("Invalid MES magic")
        self.version = struct.unpack_from('<I', data, 4)[0]
        self.count = struct.unpack_from('<I', data, 8)[0]
        self.data_offset = struct.unpack_from('<I', data, 12)[0]

        entries = []
        pos = 16
        for _ in range(self.count):
            mem_off = struct.unpack_from('<I', data, pos)[0]
            file_pos = struct.unpack_from('<I', data, pos + 4)[0] + self.data_offset
            entries.append((mem_off, file_pos))
            pos += 8

        self.string_entries: List[Tuple[int, bytes]] = []
        for i, (mem, fpos) in enumerate(entries):
            end = entries[i + 1][1] if i + 1 < len(entries) else len(data)
            self.string_entries.append((mem, data[fpos:end]))

        self.header_bytes = data[:16]

    def rebuild(self, new_contents: List[bytes]) -> bytes:
        if len(new_contents) != len(self.string_entries):
            raise ValueError(f"String count mismatch: got {len(new_contents)}, expected {len(self.string_entries)}")
        data_offset = 16 + self.count * 8
        positions = []
        cur = data_offset
        for c in new_contents:
            positions.append(cur)
            cur += len(c)

        out = bytearray(self.header_bytes)
        for (mem, _), p in zip(self.string_entries, positions):
            out.extend(struct.pack('<I', mem))
            out.extend(struct.pack('<I', p - data_offset))
        for c in new_contents:
            out.extend(c)
        return bytes(out)


class SCXFile:
    def __init__(self, data: bytes):
        if data[:4] != b'SC3\0':
            raise ValueError("Invalid SC3 magic")
        self.raw = data
        self.strings_offset, self.returns_offset = struct.unpack_from('<II', data, 4)

        # Strings count
        self.string_count = (self.returns_offset - self.strings_offset) // 4
        self.string_addrs = [
            struct.unpack_from('<I', data, self.strings_offset + i * 4)[0]
            for i in range(self.string_count)
        ]

        self.string_contents: List[bytes] = []
        for i, addr in enumerate(self.string_addrs):
            end = self.string_addrs[i + 1] if i + 1 < len(self.string_addrs) else len(data)
            self.string_contents.append(data[addr:end])

    def rebuild(self, new_contents: List[bytes]) -> bytes:
        """Rebuild SCX binary with new string contents matching C# SCXFile.Save."""
        if len(new_contents) != len(self.string_contents):
            raise ValueError(f"SCX string count mismatch: expected {len(self.string_contents)}, got {len(new_contents)}")

        code_bytes = bytearray(self.raw[:self.strings_offset])
        div = len(code_bytes) % 4
        if div != 0:
            code_bytes.extend(b'\x00' * (4 - div))

        new_strings_offset = len(code_bytes)
        num_strings = len(new_contents)
        new_returns_offset = new_strings_offset + num_strings * 4

        first_str_addr = self.string_addrs[0] if num_strings > 0 else len(self.raw)
        returns_table_bytes = self.raw[self.returns_offset:first_str_addr]

        new_string_addrs = []
        cur_pos = new_returns_offset + len(returns_table_bytes)
        for c in new_contents:
            new_string_addrs.append(cur_pos)
            cur_pos += len(c)

        out = bytearray(code_bytes)
        for addr in new_string_addrs:
            out.extend(struct.pack('<I', addr))
        out.extend(returns_table_bytes)
        for c in new_contents:
            out.extend(c)

        struct.pack_into('<II', out, 4, new_strings_offset, new_returns_offset)
        return bytes(out)


# ============================================================
# Text Formatting & Character Name Resolution
# ============================================================

def format_character_name(parsed_name: Optional[str], orig_name: Optional[str], mode: str) -> Optional[str]:
    """
    Format character name safely for the Switch engine:
    1. 'orig'      : Keeps original Japanese name.
    2. 'fullwidth' : Converts letters to full-width and space to U+3000.
    3. 'western'   : Keeps Given Surname order, replacing space with U+3000.
    4. 'english'   : Formats name in Japanese order 'Surname　GivenName' using U+3000 space
                     (matching the official game engine's verified nameplate encoding).
    """
    if mode == 'orig' or parsed_name is None:
        return orig_name

    clean = parsed_name.strip()
    if mode == 'english':
        if clean in KNOWN_NAME_ORDER:
            target = KNOWN_NAME_ORDER[clean]
        else:
            # Replace ASCII space with U+3000
            target = clean.replace(' ', '\u3000')
    elif mode == 'western':
        target = clean.replace(' ', '\u3000')
    elif mode == 'fullwidth':
        if clean in KNOWN_NAME_ORDER:
            target = KNOWN_NAME_ORDER[clean]
        else:
            target = clean.replace(' ', '\u3000')
        return to_fullwidth(target)
    else:
        target = clean.replace(' ', '\u3000')

    return target


_IMPORT_RE = re.compile(r'^(?:\[Name\](?P<name>.*?))?(?:\[Line\](?P<line>.*))?$', re.DOTALL)

def parse_import_line(line: str) -> Tuple[Optional[str], Optional[str], str]:
    line = line.rstrip('\r\n').replace('\\n', '\n')
    if line.startswith('[Name]') or line.startswith('[Line]'):
        m = _IMPORT_RE.match(line)
        if m:
            return m.group('name'), m.group('line'), ''
    return None, None, line

def render_string(p: ParsedString) -> str:
    has_fields = (p.name is not None) or (p.text is not None)
    if not has_fields:
        return p.extra_text.replace('\r', '').replace('\n', '\\n')
    parts = []
    if p.name is not None:
        parts.append('[Name]' + p.name)
    if p.text is not None:
        parts.append('[Line]' + p.text)
    return ''.join(parts).replace('\r', '').replace('\n', '\\n')


# ============================================================
# Core Actions: Extract & Reimport
# ============================================================

def do_extract(charset: Charset, script_dir: str = SCRIPT_DIR):
    """
    Extract source scripts:
    - .msb files -> msb_extracted/<stem>.txt
    - .scx files -> scx_extracted/<stem>.txt
    """
    os.makedirs(MSB_EXTRACTED, exist_ok=True)
    os.makedirs(SCX_EXTRACTED, exist_ok=True)

    print("=" * 60)
    print("EXTRACTING SCRIPT FILES")
    print(f"  Source (Read-Only) : {script_dir}")
    print(f"  MSB Output         : {MSB_EXTRACTED}")
    print(f"  SCX Output         : {SCX_EXTRACTED}")
    print("=" * 60 + "\n")

    msb_files = glob.glob(os.path.join(script_dir, "**/*.msb"), recursive=True)
    scx_files = glob.glob(os.path.join(script_dir, "*.scx"), recursive=False)

    print(f"Found {len(msb_files)} .msb file(s) and {len(scx_files)} .scx file(s).\n")

    ok_msb = 0
    for path in msb_files:
        stem = os.path.splitext(os.path.basename(path))[0]
        out_path = os.path.join(MSB_EXTRACTED, stem + ".txt")
        try:
            with open(path, 'rb') as f:
                mf = MesFile(f.read())
            with open(out_path, 'w', encoding='utf-8', newline='\n') as f:
                for _, raw in mf.string_entries:
                    parser = MesStringParser(charset)
                    parser.parse(raw)
                    f.write(render_string(parser.result) + '\n')
            ok_msb += 1
        except Exception as e:
            print(f"  [FAIL] {os.path.basename(path)}: {e}")

    ok_scx = 0
    for path in scx_files:
        stem = os.path.splitext(os.path.basename(path))[0]
        out_path = os.path.join(SCX_EXTRACTED, stem + ".txt")
        try:
            with open(path, 'rb') as f:
                scx = SCXFile(f.read())
            with open(out_path, 'w', encoding='utf-8', newline='\n') as f:
                for raw in scx.string_contents:
                    parser = MesStringParser(charset)
                    parser.parse(raw)
                    f.write(render_string(parser.result) + '\n')
            ok_scx += 1
        except Exception as e:
            print(f"  [FAIL] {os.path.basename(path)}: {e}")

    print(f"\nExtracted: {ok_msb}/{len(msb_files)} MSBs, {ok_scx}/{len(scx_files)} SCXs.")


def do_reimport(charset: Charset,
                script_dir: str = SCRIPT_DIR,
                txt_dir: str = TXT_DIR,
                output_dir: str = OUTPUT_DIR,
                name_mode: str = "english"):
    """
    Recompile translations from txt_dir into output/ directory.
    - Matches translation files by name against source scripts.
    - Enforces U+3000 space and proper name formatting.
    - Synchronizes matching .scx files into output/ to prevent scene end crashes.
    """
    if not os.path.isdir(txt_dir):
        print(f"ERROR: Translation directory does not exist: {txt_dir}")
        return

    out_mes00 = os.path.join(output_dir, "mes00")
    os.makedirs(out_mes00, exist_ok=True)
    os.makedirs(output_dir, exist_ok=True)

    # Build mapping of base filename -> source script path
    msb_source_map: Dict[str, str] = {}
    for path in glob.glob(os.path.join(script_dir, "**/*.msb"), recursive=True):
        stem = os.path.splitext(os.path.basename(path))[0].lower()
        msb_source_map[stem] = path

    scx_source_map: Dict[str, str] = {}
    for path in glob.glob(os.path.join(script_dir, "*.scx"), recursive=False):
        stem = os.path.splitext(os.path.basename(path))[0].lower()
        scx_source_map[stem] = path

    # Scan txt_dir for translation files
    txt_files = glob.glob(os.path.join(txt_dir, "**/*.txt"), recursive=True)
    if not txt_files:
        print(f"No .txt translation files found under '{txt_dir}'.")
        return

    print("=" * 60)
    print("RECOMPILING TRANSLATIONS")
    print(f"  Source Scripts (Read-Only) : {script_dir}")
    print(f"  Translations From          : {txt_dir}")
    print(f"  Output Directory           : {output_dir}")
    print(f"  Character Name Mode        : {name_mode.upper()}")
    print("=" * 60 + "\n")

    ok_msb = 0
    ok_rebuilt_scx = 0
    rebuilt_scx_stems: Set[str] = set()
    scx_to_sync: Set[str] = set()

    for tp in txt_files:
        stem = os.path.splitext(os.path.basename(tp))[0].lower()

        # Check if translation matches an MSB file
        if stem in msb_source_map:
            src_msb = msb_source_map[stem]
            out_msb = os.path.join(out_mes00, os.path.basename(src_msb))

            try:
                with open(src_msb, 'rb') as f:
                    mf = MesFile(f.read())

                with open(tp, 'r', encoding='utf-8-sig') as f:
                    content = f.read().replace('\r\n', '\n').replace('\r', '\n')
                lines = content.split('\n')
                if len(lines) == mf.count + 1 and lines[-1] == '':
                    lines = lines[:-1]

                if len(lines) != mf.count:
                    print(f"  [SKIP] {stem}: line count mismatch ({len(lines)} txt vs {mf.count} binary)")
                    continue

                new_contents: List[bytes] = []
                for i, line in enumerate(lines):
                    parser = MesStringParser(charset)
                    parser.parse(mf.string_entries[i][1])
                    orig = parser.result

                    p_name, text, extra = parse_import_line(line)
                    if p_name is None and text is None:
                        if orig.name is not None and orig.text is None:
                            p_name, text, extra = line.replace('\\n', '\n'), None, ''
                        elif orig.text is not None and orig.name is None:
                            p_name, text, extra = None, line.replace('\\n', '\n'), ''
                        else:
                            p_name, text, extra = None, None, line.replace('\\n', '\n')

                    final_name = format_character_name(p_name, orig.name, name_mode)
                    raw_enc = encode_string(final_name, text, extra or '', orig.extra, charset)
                    new_contents.append(raw_enc)

                out_data = mf.rebuild(new_contents)
                with open(out_msb, 'wb') as f:
                    f.write(out_data)

                # Identify matching .scx parent (e.g. og_n001ess0_00.msb -> og_n001ess0.scx)
                parent_stem = stem[:-3] if stem.endswith('_00') else stem
                if parent_stem in scx_source_map:
                    scx_to_sync.add(scx_source_map[parent_stem])

                print(f"  [OK MSB] {stem}.msb ({len(new_contents)} strings)")
                ok_msb += 1
            except Exception as e:
                print(f"  [FAIL MSB] {stem}: {e}")

        # Check if translation matches an SCX file
        elif stem in scx_source_map:
            src_scx = scx_source_map[stem]
            out_scx = os.path.join(output_dir, os.path.basename(src_scx))

            try:
                with open(src_scx, 'rb') as f:
                    scx = SCXFile(f.read())

                with open(tp, 'r', encoding='utf-8-sig') as f:
                    content = f.read().replace('\r\n', '\n').replace('\r', '\n')
                lines = content.split('\n')
                if len(lines) == scx.string_count + 1 and lines[-1] == '':
                    lines = lines[:-1]

                if len(lines) != scx.string_count:
                    print(f"  [SKIP SCX] {stem}: string count mismatch ({len(lines)} txt vs {scx.string_count} binary)")
                    continue

                new_contents: List[bytes] = []
                for i, line in enumerate(lines):
                    parser = MesStringParser(charset)
                    parser.parse(scx.string_contents[i])
                    orig = parser.result

                    p_name, text, extra = parse_import_line(line)
                    if p_name is None and text is None and not extra:
                        extra = line.replace('\\n', '\n')

                    final_name = format_character_name(p_name, orig.name, name_mode)
                    raw_enc = encode_string(final_name, text, extra or '', orig.extra, charset)
                    new_contents.append(raw_enc)

                rebuilt_data = scx.rebuild(new_contents)
                with open(out_scx, 'wb') as f:
                    f.write(rebuilt_data)

                rebuilt_scx_stems.add(stem)
                print(f"  [OK SCX REBUILD] {stem}.scx ({len(new_contents)} strings)")
                ok_rebuilt_scx += 1
            except Exception as e:
                print(f"  [FAIL SCX REBUILD] {stem}: {e}")

    # Synchronize corresponding .scx files into output/ (if not already rebuilt from translation)
    ok_synced_scx = 0
    print(f"\nSynchronizing matching .scx bytecode files into '{output_dir}'...")
    for scx_path in sorted(scx_to_sync):
        parent_stem = os.path.splitext(os.path.basename(scx_path))[0].lower()
        if parent_stem in rebuilt_scx_stems:
            continue  # Already recompiled with translated strings
        dest_scx = os.path.join(output_dir, os.path.basename(scx_path))
        try:
            shutil.copy2(scx_path, dest_scx)
            ok_synced_scx += 1
        except Exception as e:
            print(f"  [FAIL SCX SYNC] {os.path.basename(scx_path)}: {e}")

    print(f"\n" + "=" * 60)
    print("COMPILATION SUMMARY:")
    print(f"  Successfully recompiled : {ok_msb} .msb file(s) -> {out_mes00}")
    if ok_rebuilt_scx:
        print(f"  Rebuilt from translation : {ok_rebuilt_scx} .scx file(s) -> {output_dir}")
    print(f"  Synchronized bytecode   : {ok_synced_scx} .scx file(s) -> {output_dir}")
    print("=" * 60)
    print("\nMod Folder Deployment Instructions:")
    print(f"  Copy all files and folders inside '{output_dir}' directly into your Nintendo Switch mod folder:")
    print("  atmosphere/contents/<TitleID>/romfs/script/\n")


# ============================================================
# Main Entry Point
# ============================================================

def main():
    parser = argparse.ArgumentParser(description="Oregairu Nintendo Switch Translation Tool")
    parser.add_argument("action", nargs="?", choices=["extract", "reimport"], help="Action: 'extract' or 'reimport'")
    parser.add_argument("--script-dir", default=SCRIPT_DIR, help="Source scripts directory (default: script/)")
    parser.add_argument("--txt-dir", default=TXT_DIR, help="Translation text directory (default: exported_txt/)")
    parser.add_argument("--output-dir", default=OUTPUT_DIR, help="Output directory (default: output/)")
    parser.add_argument("--name-mode", choices=["english", "western", "orig", "fullwidth"], default="english",
                        help="Character name mode: 'english' (Surname　GivenName in ASCII), 'western' (GivenName　Surname in ASCII), 'orig' (Japanese), or 'fullwidth'")
    parser.add_argument("--charset", default=CHARSET_PATH, help="Path to charset.utf8 (default: resources/ogvd/charset.utf8)")

    args = parser.parse_args()

    # If run without arguments, display interactive menu
    if not args.action:
        print("=" * 60)
        print("  OREGAIRU NINTENDO SWITCH TRANSLATION TOOL")
        print("=" * 60)
        print("1. Reimport (Compile translations into output/)")
        print("2. Extract (Dump scripts to msb_extracted/ & scx_extracted/)")
        print("3. Exit")
        choice = input("\nEnter choice [1-3] (default 1): ").strip()
        if choice == "2":
            args.action = "extract"
        elif choice == "3":
            sys.exit(0)
        else:
            args.action = "reimport"

    charset = load_charset(args.charset)

    if args.action == "extract":
        do_extract(charset, args.script_dir)
    elif args.action == "reimport":
        do_reimport(charset, args.script_dir, args.txt_dir, args.output_dir, args.name_mode)


if __name__ == "__main__":
    main()
