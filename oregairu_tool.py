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
4. Line Splitting (ON by default, --no-split to disable): a dialogue line is only touched
   when it genuinely overflows the text box.  The character limit is DEFAULT_BOX_WIDTH
   (51 half-width cells per rendered line) and the box shows DEFAULT_BOX_LINES (3) such
   lines.  The engine wraps per line and wastes cells at every word boundary, so the
   packer simulates that wrap (_Wrapper / wrap_line_count) instead of budgeting a flat
   cell count -- a flat budget fills the box with text the engine then pushes onto a
   fourth, invisible line.  The overflow moves into extra boxes revealed on button press,
   which requires renumbering .msb memory offsets AND patching the paired .scx bytecode
   (see SplitPlan / SCXFile.apply_split_plan).  Raise --box-width for bigger boxes; the
   split points are recomputed from scratch on every build.
5. Scene Transition Safety: Reimport automatically pairs each recompiled .msb with its
   matching .scx file into output/, preventing out-of-bounds crashes at scene endings.
6. Non-Destructive: Source script/ and resources/ are strictly read-only, never modified.
7. Clean Extraction & Reimport Workflow:
   - extract:  .msb -> msb_extracted/ , .scx -> scx_extracted/
   - reimport: reads exported_txt/ and compiles into output/mes00/*.msb and output/*.scx

This file is deliberately monolithic: it carries its own port of the SC3Tool Switch
disassembler (see the "SC3 Switch disassembler" section below), so the only companion
module is deploy_output.py.
"""

import os
import sys
import glob
import json
import struct
import re
import shutil
import argparse
import unicodedata
from typing import Dict, List, Optional, Sequence, Set, Tuple


# Ensure UTF-8 output on Windows console
if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding='utf-8') # pyright: ignore[reportAttributeAccessIssue]
        sys.stderr.reconfigure(encoding='utf-8') # pyright: ignore[reportAttributeAccessIssue]
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
NAME_DB_PATH  = os.path.join(BASE_DIR, "names.json")

MSB_EXTRACTED = os.path.join(BASE_DIR, "msb_extracted")
SCX_EXTRACTED = os.path.join(BASE_DIR, "scx_extracted")


# ============================================================
# Build Options
# ============================================================
# Every command-line flag has its default here, so the whole build can be
# reconfigured by editing one block.  Command-line flags override these.

#: Nameplate order.  'english' = exactly what names.json says.  'western'
#: reverses 'Surname Given' into 'Given Surname' for display.  'orig' = keep the
#: Japanese from the source .msb.  'fullwidth' = full-width Latin.
DEFAULT_NAME_MODE = "english"

#: Split dialogue lines that overflow the text box into extra boxes revealed on
#: button press.  ON: validated against the shipped English patch, which uses the
#: same construct (an inserted MessWindow_ShowCurrent / AwaitShowCurrent /
#: Mes_LoadDialogue / MesMain_DisplayDialogue block plus one extra .msb entry)
#: 429 times and works in-game.  Running this splitter over that patch's own
#: English text reproduces 15,284 of its 15,332 split decisions (99.69%).
#: See analysis/analyze_ref_split.py and analysis/analyze_our_split.py
DEFAULT_SPLIT = True

#: THE CHARACTER LIMIT.  Width of ONE rendered line of the dialogue text box, in
#: half-width cells (a glyph counts 1 cell when its charset code is < 126, else 2).
#:
#: The box is a window, not a single line: it shows DEFAULT_BOX_LINES lines of this
#: width and the engine greedily wraps inside it.  Changing this number re-derives
#: every split point in the game on the next build -- nothing else has to be kept in
#: sync.  Use --box-width to try a different value without editing the file.
#:
#: Why 65: measured from rendered output, not guessed.  The sharpest observation is
#: one box in og_n001ess1_00 whose three rendered lines our simulation reproduces
#: character for character at 64 and 65 -- but NOT at 66, where we pack an extra word
#: onto line 3 and the engine clips it off the bottom of the box:
#:     "「To begin with! It's entirely because Onii-chan is who he is"   61 cells
#:     "that things ended up like this, right?! As his little sister, I" 63 cells
#:     "don't even know how to apologize enough... I am so, so sorry for" 64 cells
#: Other observations bracket it as 64..67 (see analyze_line_width_exact.py); 65 is
#: the value that matches the most precise sample and errs on the safe side, since
#: over-estimating costs a lost word while under-estimating only wastes a cell.
#:
#: Caveat worth knowing: the observations are not perfectly self-consistent.  One
#: other box appears to have rendered a 66-cell line, which no single fixed-cell
#: width can reconcile with the sample above.  The console's own renderer is NOT in
#: fulldecomp/ (that is the editor, whose AutoformatHelper.WordLength is a fixed
#: 1-or-2-cell model this tool reproduces exactly -- see verify_width_model.py), so
#: the console most likely advances by real font metrics rather than whole cells.
#: Without the font's advance widths there is no way to model that precisely, so
#: this stays a measured constant.  Raise it to 66 for slightly fuller boxes at the
#: risk of occasionally clipping a word off the bottom; lower it to be safer.
DEFAULT_BOX_WIDTH = 65

#: How many rendered lines the text box shows at once, so a box holds at most
#: DEFAULT_BOX_WIDTH * this many cells (195 by default).  In practice a box holds a
#: little less, because the engine wraps per line and loses cells at every word
#: boundary -- the splitter simulates that wrap rather than budgeting a flat count.
DEFAULT_BOX_LINES = 3

#: Translate the 257-entry character-name registry inside _system_00.msb
#: (memory ids >= 100000) from names.json.  The engine matches that registry
#: against the dialogue nameplates, so both must agree or no nameplate is drawn.
#: With this off, registry entries keep the source .msb text.
DEFAULT_TRANSLATE_SYSTEM_NAMES = True

#: Copy output/ into the emulator's script folder when the build finishes.
DEFAULT_DEPLOY = True

#: Where the emulator expects the scripts.  The contents of this folder are
#: deleted before copying.
DEPLOY_TARGET = (r"C:\Users\Sam\AppData\Roaming\yuzu\load"
                 r"\0100E0D0154BC000\eng\romfs\script")


# ============================================================
# SC3 Switch disassembler
# ============================================================
# Python port of the SC3Tool (SC3Library/SC3Tool) Switch disassembler,
# a faithful port of the decompiled C# in ``fulldecomp/``:
#
#   SwitchDisassembler.DisassembleAt       -> decode()
#   SC3BaseDisassembler.DisassembleFile    -> disassemble()
#   SCXFile.ParseHeader / ReadLabels       -> parse_labels()
#   SC3Expression (raw length + tokenise)  -> expr_len(), expr_value()
#
# Used to locate Mes_Load* instructions inside an .scx so over-long dialogue
# lines can be split into extra text boxes (see iter_instructions()).
#

# ---- arg kinds ----
BYTE, UINT16, EXPR, LOCALLABEL, FARPABEL, RETADDR, STRREF = (
    'Byte', 'UInt16', 'Expression', 'LocalLabel', 'FarLabel', 'ReturnAddress', 'StringRef')
EXPRFLAG, EXPRGLOBAL, EXPRTHREAD, EXPRSTRINGREF = (
    'ExprFlagRef', 'ExprGlobalVarRef', 'ExprThreadVarRef', 'ExprStringRef')


def _expr_len(data: bytes, p: int) -> int:
    """Return length of expression starting at p (matching SC3Expression.RawLength).

    Every token consumes an extra 'precedence' byte after its payload; the
    terminating 0x00 end token is NOT consumed but IS counted (RawLength = consumed + 1).
    """
    start = p
    n = len(data)
    while p < n:
        b = data[p]
        if b & 0x80:
            kind = b & 0x60
            p += {0x00: 1, 0x20: 2, 0x40: 3, 0x60: 5}[kind] + 1
            continue
        if b == 0:
            break  # end token is peeked, not consumed; RawLength counts it
        p += 2  # operator token: type byte + precedence byte
    return p - start + 1


def _expr_value(data: bytes, p: int) -> int:
    """Evaluate a constant expression (returns 0 if not constant)."""
    # simple: single immediate
    b = data[p]
    if b & 0x80:
        kind = b & 0x60
        if kind == 0x00:
            v = b & 0x1F
            if b & 0x10:
                v |= 0x7FFFFFE0
            return v
        if kind == 0x20:
            return ((b & 0x1F) << 8) | data[p + 1]
        if kind == 0x40:
            return ((b & 0x1F) << 16) | (data[p + 2] << 8) | data[p + 1]
        if kind == 0x60:
            return struct.unpack_from('<i', data, p + 1)[0]
    return 0


FUNC_NAMES = {40: 'GlobalVars', 41: 'Flags', 42: 'DataAccess', 43: 'LabelTable',
              44: 'FarLabelTable', 45: 'ThreadVars', 46: 'DMA', 47: 'GetUnk2F',
              48: 'GetUnk30', 49: 'Nop31', 50: 'Nop32', 51: 'Random', 11: '~'}


def _expr_str(data: bytes, p: int) -> str:
    ln = _expr_len(data, p)
    raw = data[p:p + ln]
    b0 = raw[0]
    if (b0 & 0xE0) == 0x28 and ln > 4 and (b0 & 0x1F) in FUNC_NAMES:
        return '%s[%d]' % (FUNC_NAMES[b0 & 0x1F], _expr_value(data, p + 2))
    return str(_expr_value(data, p))


class Builder:
    """Collects decoded arguments.

    Each argument is recorded as ``(kind, name, value, offset, length)`` where
    ``offset`` is relative to the start of the instruction. Callers that rewrite
    bytecode (e.g. retargeting .msb references) use the offset/length to splice
    a re-encoded value in place of the original bytes.
    """

    def __init__(self, data: bytes, p: int, maxlen: int):
        self.data = data
        self.start = p
        self.p = p
        self.maxlen = maxlen
        self.args: List[Tuple[str, str, object, int, int]] = []

    def _add(self, kind, name, value, nbytes):
        self.args.append((kind, name, value, self.p - self.start, nbytes))
        self.p += nbytes
        return value

    def byte_arg(self, name):
        return self._add(BYTE, name, self.data[self.p], 1)

    def u16_arg(self, name):
        return self._add(UINT16, name, struct.unpack_from('<H', self.data, self.p)[0], 2)

    def expr_arg(self, name):
        ln = _expr_len(self.data, self.p)
        return self._add(EXPR, name, _expr_str(self.data, self.p), ln)

    def expr_strref_arg(self, name):
        ln = _expr_len(self.data, self.p)
        return self._add(EXPRSTRINGREF, name, _expr_value(self.data, self.p), ln)

    def label_arg(self, name):
        return self._add(LOCALLABEL, name, struct.unpack_from('<H', self.data, self.p)[0], 2)

    def strref_arg(self, name):
        return self._add(STRREF, name, struct.unpack_from('<H', self.data, self.p)[0], 2)

    def far_arg(self, name):
        ln = _expr_len(self.data, self.p)
        self._add(FARPABEL, name, _expr_value(self.data, self.p), ln)
        self._add('UInt16Tail', name + '_id', 0, 2)
        return None

    def ret_arg(self, name):
        return self._add(RETADDR, name, struct.unpack_from('<H', self.data, self.p)[0], 2)

    def flag_arg(self, name):
        ln = _expr_len(self.data, self.p)
        return self._add(EXPRFLAG, name, _expr_value(self.data, self.p), ln)

    def global_arg(self, name):
        ln = _expr_len(self.data, self.p)
        return self._add(EXPRGLOBAL, name, _expr_value(self.data, self.p), ln)

    def thread_arg(self, name):
        ln = _expr_len(self.data, self.p)
        return self._add(EXPRTHREAD, name, _expr_value(self.data, self.p), ln)

    def done(self, name):
        return name, self.p - self.start, self.args


# ---- fixed-arity instruction table (opcode -> (name, arg kinds)) ----
def _spec(name, *kinds):
    return (name, list(kinds))


E = EXPR
U16 = UINT16
B = BYTE
LL = LOCALLABEL
FL = FARPABEL
RA = RETADDR
SR = STRREF
FX = EXPRFLAG
GV = EXPRGLOBAL

SIMPLE = {
    0x0000: _spec('End'),
    0x0002: _spec('KillThread', E),
    0x0003: _spec('Reset'),
    0x0004: _spec('ScriptLoad', E, E),
    0x0005: _spec('Wait', E),
    0x0006: _spec('Halt'),
    0x0007: _spec('Jump', LL),
    0x0008: _spec('JumpTable', E, LL),
    0x0009: _spec('GetLabelAdr', LL),
    0x000A: _spec('If', B, E, LL),
    0x000B: _spec('Call', LL, RA),
    0x000C: _spec('JumpFar', FL),
    0x000D: _spec('CallFar', FL, RA),
    0x000E: _spec('Return'),
    0x000F: _spec('Loop', LL, E),
    0x0010: _spec('FlagOnJump', B, FX, LL),
    0x0011: _spec('FlagOnWait', B, FX),
    0x0014: _spec('CopyFlag', FX, FX),
    0x0015: _spec('KeyOnJump', B, E, E, LL),
    0x0016: _spec('KeyWait', B, E, E),
    0x0018: _spec('MemberWrite', E, E),
    0x0019: _spec('ThreadControl', E, E),
    0x001A: _spec('GetSelfPointer'),
    0x001B: _spec('LoadJump', E, U16),
    0x001C: _spec('Vsync'),
    0x001D: _spec('Test', E),
    0x001F: _spec('Switch', E),
    0x0020: _spec('Case', E, LL),
    0x0022: _spec('BGMstop', B),
    0x0024: _spec('SEstop', B),
    0x0025: _spec('PadAct', E, E, E),
    0x0026: _spec('SSEplay', E),
    0x0027: _spec('SSEstop'),
    0x0028: _spec('CopyThreadWork', E, E, E, E),
    0x0029: _spec('UPLmenuUI', B),
    0x002A: _spec('Unk002A', B),
    0x002B: _spec('SaveIconLoad', B),
    0x002C: _spec('BGMflag', B),
    0x002D: _spec('UPLxTitle', B),
    0x002E: _spec('Presence', B, E),
    0x0030: _spec('SetPlayer', B),
    0x0031: _spec('VoiceTableLoadMaybe', E),
    0x0032: _spec('SetPadCustom'),
    0x0033: _spec('Mwait', E, E),
    0x0034: _spec('Terminate'),
    0x0035: _spec('SignIn'),
    0x0036: _spec('AchievementIcon', B),
    0x0037: _spec('VoicePlay', B, E, E),
    0x0038: _spec('VoiceStop', B, E),
    0x0039: _spec('VoicePlayWait', B),
    0x003B: _spec('SNDpause', B),
    0x003C: _spec('SEplayWait', B),
    0x003D: _spec('DebugPrint', E, E),
    0x003E: _spec('ResetSoundAll'),
    0x003F: _spec('SNDloadStop'),
    0x0040: _spec('BGMstopWait'),
    0x0041: _spec('Unk0041'),
    0x0042: _spec('SetX360SysMesPos', E),
    0x0045: _spec('GetNowTime'),
    0x0046: _spec('GetSystemStatus', E),
    0x0047: _spec('Reboot'),
    0x0048: _spec('ReloadScript'),
    0x0049: _spec('ReloadScriptMenu', B),
    0x004D: _spec('SysVoicePlay', B, E),
    0x004E: _spec('PadActEx', E, E, E),
    0x004F: _spec('DebugSetup', E),
    0x0051: _spec('GlobalSystemMessage', E),
    0x0080: _spec('Unk0080', B),
    0x0081: _spec('Unk0081', B),
    0x0082: _spec('Unk0082', B, B),
    0x00A0: _spec('Unk00A0', E, E),
    0x0101: _spec('CreateSurf'),
    0x0102: _spec('ReleaseSurf', E),
    0x0103: _spec('LoadPic', E, E, E),
    0x0104: _spec('ReleaseSurf', E),
    0x0105: _spec('SurfFill', E, E, E, E, E),
    0x0107: _spec('SetMesWinPri', E, E, E),
    0x0108: _spec('MesSync'),
    0x010B: _spec('MesVoiceWait'),
    0x010E: _spec('SetMesModeFormat', E, LL),
    0x010F: _spec('SetNGmoji', SR, SR),
    0x1001: _spec('BGload', E, E),
    0x1002: _spec('BGswap', E, E),
    0x1003: _spec('BGsetColor', E, E),
    0x1005: _spec('Unk1005', B, E, E),
    0x1007: _spec('BGcopy', E, E),
    0x1009: _spec('SaveSlot', E, E),
    0x100A: _spec('SystemMain'),
    0x100B: _spec('Unk100B'),
    0x100C: _spec('GameInfoInit', B),
    0x1012: _spec('ClearFlagChk'),
    0x1014: _spec('SystemDataReset', B),
    0x1015: _spec('DebugData', B),
    0x1016: _spec('GetCharaPause', E, GV),
    0x1017: _spec('BGfadeExpInit', E),
    0x101A: _spec('Unk101A', B),
    0x101C: _spec('AchievementMenu', B),
    0x101E: _spec('AllClear'),
    0x1029: _spec('Unk1029', B, E),
    0x102A: _spec('Unk102A', B, E, E, E),
    0x102D: _spec('Unk102D'),
    0x1034: _spec('Unk1034'),
    0x1038: _spec('Unk1038', B),
    0x2000: _spec('Unk2000', U16, U16, U16),
    0x4000: _spec('Unk4000', U16, U16, U16),
}


def _mes_viewflag(b, d):
    b.byte_arg('channel'); t = b.byte_arg('type')
    if t == 0:
        b.expr_arg('arg1'); b.expr_arg('arg2'); return 'MesViewFlag_Set'
    if t == 1:
        b.global_arg('destination'); b.expr_arg('arg1'); b.expr_arg('arg2'); return 'MesViewFlag_Chk'
    return None


def _mescls(b, d):
    t = b.byte_arg('type')
    if (t & 0xFE) != 4 and (t & 1) == 0:
        b.expr_arg('arg1')
    return 'MesCls'


def _mesmain(b, d):
    t = b.byte_arg('type')
    return 'MesMain_DisplayDialogue' if t == 0 else None


def _messetid(b, d):
    t = b.byte_arg('type')
    if (t & 0xF) == 0:
        b.u16_arg('savePointId'); return 'MesSetID_SetSavePoint'
    if (t & 0xF) == 1:
        b.u16_arg('savePointId'); b.expr_arg('unk'); return 'MesSetID_SetSavePoint1'
    if (t & 0xF) == 2:
        b.expr_arg('unk'); return 'MetSetID_02'
    return 'MesSetID'


def _mesrev(b, d):
    t = b.byte_arg('type')
    return {0: 'MesRev_DispInit', 1: 'MesRev_Main', 2: 'MesRev_AllCls',
            3: 'MesRev_ChkLoad', 4: 'MesRev_SAVELoad', 5: 'MesRev_SoundUnk',
            10: 'MesRev_DispInit'}.get(t)


def _messwindow(b, d):
    t = b.byte_arg('type')
    names = {0: 'MessWindow_HideCurrent', 1: 'MessWindow_ShowCurrent',
             2: 'MessWindow_AwaitShowCurrent', 3: 'MessWindow_AwaitHideCurrent',
             4: 'MessWindow_Current04'}
    if t in names:
        return names[t]
    if t in (5, 6, 7):
        b.expr_arg('messWindowId')
        return 'MessWindow_Hide' if t == 5 else 'MessWindow_HideSlow'
    return None


def _mes(b, d):
    t = b.byte_arg('type')
    if t == 0:
        b.expr_arg('characterId'); b.strref_arg('line'); return 'Vita_Mes_LoadDialogue'
    if t == 128:
        b.expr_arg('characterId'); b.expr_strref_arg('mesline'); return 'Switch_Mes_LoadDialogue'
    if t == 3:
        b.expr_arg('audioId'); b.expr_arg('animationId'); b.expr_arg('characterId')
        b.strref_arg('line'); return 'Vita_Mes_LoadVoicedDialogue'
    if t == 131:
        b.expr_arg('audioId'); b.expr_arg('animationId'); b.expr_arg('characterId')
        b.expr_strref_arg('mesline'); return 'Switch_Mes_LoadVoicedDialogue'
    return None


def _sel(b, d):
    t = b.byte_arg('type')
    if t == 130:
        b.expr_arg('arg2'); b.expr_arg('arg3'); return 'Sel'
    if t == 129:
        b.expr_strref_arg('arg2'); return 'Sel'
    if t == 3:
        b.byte_arg('arg1'); b.strref_arg('arg2'); b.expr_arg('arg3'); return 'Sel'
    if t == 4:
        b.byte_arg('arg1'); b.strref_arg('arg2'); b.expr_arg('arg3'); return 'Sel'
    if t == 0:
        b.u16_arg('arg2'); b.expr_arg('arg3'); return 'Sel'
    if t == 2:
        b.strref_arg('arg2'); b.expr_arg('arg3'); return 'Sel'
    if t == 1:
        b.strref_arg('arg2'); return 'Sel'
    return 'Sel'


def _select(b, d):
    t = b.byte_arg('type')
    if t == 2:
        b.expr_arg('arg1')
    return 'Select'


def _syssel(b, d):
    t = b.byte_arg('type')
    if t == 2:
        b.expr_arg('arg1')
    return 'SysSel'


def _sysselect(b, d):
    b.byte_arg('arg1'); t = d[b.p - 1]
    if (t & 0xF) == 2 or (t & 0xF) == 3:
        b.global_arg('destination')
    return 'SysSelect'


def _bgmplay(b, d):
    loop = b.byte_arg('loop'); b.expr_arg('track')
    if loop == 2:
        b.expr_arg('unk')
    return 'BGMplay'


def _seplay(b, d):
    b.byte_arg('channel'); t = b.byte_arg('type')
    if t != 2:
        b.expr_arg('effect'); b.expr_arg('loop')
    return 'SEplay'


def _threadcontrolstore(b, d):
    t = b.byte_arg('type')
    return {0: 'ThreadControlRestore', 1: 'ThreadControlStore'}.get(t)


def _un0121(b, d):
    d2 = b.data[b.p]; b.p += 1
    b.byte_arg('arg1'); b.u16_arg('arg2'); b.u16_arg('arg3')
    return 'Unk0121'


def _un0122(b, d):
    x = d[b.p] & 0xF; b.p += 1
    b.byte_arg('arg1'); b.byte_arg('arg1b'); b.expr_arg('arg2'); b.expr_arg('arg3')
    if x != 1:
        b.expr_arg('arg4'); b.expr_arg('arg5'); b.expr_arg('arg6')
    return 'Unk0122'


def _un0123(b, d):
    b.p += 1; b.byte_arg('arg1'); return 'Unk0123'


def _un012c(b, d):
    t = b.byte_arg('type'); b.byte_arg('arg2'); b.byte_arg('arg3')
    if t == 8:
        b.byte_arg('arg4')
    return 'Unk012C'


def _un012e(b, d):
    t = b.byte_arg('type')
    if t == 2:
        b.expr_arg('arg1')
    return 'Unk012E'


def _un012f(b, d):
    t = b.byte_arg('type')
    if t == 1:
        b.expr_arg('arg1'); b.expr_arg('arg2'); b.expr_arg('arg3')
        b.expr_arg('arg4'); b.byte_arg('arg5')
    return 'Unk012F'


def _un0125(b, d):
    b.p += 1; b.byte_arg('type'); b.expr_arg('arg1'); return 'Unk0125'


def _un0127(b, d):
    b.p += 1; b.byte_arg('arg1'); return 'Unk0127'


def _un0128(b, d):
    b.p += 1; b.expr_arg('arg1'); return 'Unk0128'


def _un1000(b, d):
    t = b.byte_arg('type')
    if t in (128, 138):
        b.u16_arg('arg1')
    return 'Unk1000'


def _un1006(b, d):
    b.p += 1; b.expr_arg('arg1'); b.expr_arg('arg2'); return 'Unk1006'


def _un1010(b, d):
    b.p += 1; b.expr_arg('arg1'); return 'Unk1010'


def _un1011(b, d):
    b.p += 1; b.expr_arg('arg1'); return 'Unk1011'


def _un101a(b, d):
    b.byte_arg('arg1'); return 'Unk101A'


def _un101f(b, d):
    t = b.byte_arg('type')
    return {0: 'Album_EXmenuInit', 1: 'Album_EXmenuMain', 3: 'Album_3',
            10: 'Album_ProfSetXboxEvent'}.get(t)


def _un1023(b, d):
    t = b.byte_arg('type')
    if t == 0:
        b.byte_arg('arg2')
    return 'Unk1023'


def _un1024(b, d):
    t = b.byte_arg('type')
    if t == 0:
        b.expr_arg('arg1'); b.expr_arg('arg2')
    return 'Unk1024'


def _un102d(b, d):
    return 'Unk102D'


def _un1032(b, d):
    b.p += 1; b.byte_arg('type'); b.expr_arg('arg1'); b.byte_arg('arg2'); return 'Unk1032'


def _un1033(b, d):
    b.p += 1; b.byte_arg('type'); return 'Unk1033'


def _un1034(b, d):
    return 'Unk1034'


def _un1036(b, d):
    b.p += 1; b.expr_arg('arg2'); return 'Unk1036'


def _un1037(b, d):
    t = b.byte_arg('type')
    if t != 1:
        b.expr_arg('arg2')
    return 'Unk1037'


def _un1038(b, d):
    b.byte_arg('arg1'); return 'Unk1038'


def _bgsetlink(b, d):
    i = b.byte_arg('id'); b.expr_arg('arg1'); b.expr_arg('arg2')
    if i >= 4:
        b.expr_arg('arg3')
    b.expr_arg('arg4')
    return 'BGsetLink'


def _option(b, d):
    t = b.byte_arg('type')
    return {0: 'OptionInit', 10: 'OptionInit', 1: 'OptionMain', 2: 'OptionCancel',
            3: 'Option_V2toV1vol', 4: 'OptionDefault'}.get(t)


def _help(b, d):
    t = b.byte_arg('type')
    return {0: 'HelpInit', 1: 'HelpMain', 4: 'Help_DisplayModeInit',
            5: 'Help_DisplayModeMain'}.get(t)


def _soundmenu(b, d):
    t = b.byte_arg('type')
    return {0: 'SoundMenu_MusicInit', 1: 'SoundMenu_MusicMain',
            10: 'SoundMenu_ProfSetXboxEvent'}.get(t)


def _moviemode(b, d):
    t = b.byte_arg('type')
    return {0: 'MovieModeInit', 1: 'MovieModeMain'}.get(t)


def _clistinit(b, d):
    t = b.byte_arg('type')
    return {0: 'ClistInit_PDmenuInit', 1: 'ClistInit_PlayDataMain',
            3: 'ClistInit_PDmenuInit2', 10: 'ClistInit_ProfSetXboxEvent'}.get(t)


def _autosave(b, d):
    t = b.byte_arg('type')
    if t in (0, 1, 2, 3, 5, 20, 21, 255):
        return {0: 'AutoSave_QuickSave', 1: 'AutoSave_01', 2: 'AutoSave_02',
                3: 'AutoSave_03', 5: 'AutoSave_05', 20: 'AutoSave_14',
                21: 'AutoSave_15', 255: 'AutoSave_FF'}[t]
    if t == 10:
        b.u16_arg('checkpointId'); return 'AutoSave_SaveState'
    if t in (4, 6, 7, 8, 9):
        return 'AutoSave_NotImplemented'
    return None


def _bgloadex(b, d):
    t = b.byte_arg('arg1'); b.byte_arg('arg2')
    if t == 160:
        b.byte_arg('arg3')
    return 'InstBGloadEx'


def _keywaittimer(b, d):
    b.byte_arg('type'); b.expr_arg('timer'); b.expr_arg('arg1'); b.expr_arg('arg2')
    return 'KeyWait'


def _achievement(b, d):
    t = b.byte_arg('type')
    if t == 1:
        b.expr_arg('arg1')
    return 'Achievement'


def _debuediter(b, d):
    t = b.byte_arg('type')
    return {0: 'DebugEditerInit', 1: 'DebugEditerMain', 2: 'DebugEditerLoad'}.get(t)


def _systemmenu(b, d):
    t = b.byte_arg('type')
    return {0: 'SystemMenuInit', 1: 'SystemMenuMain'}.get(t)


def _un004b(b, d):
    t = b.byte_arg('type')
    if t == 1:
        b.u16_arg('arg1')
    return 'Unk004b'


def _un0041(b, d):
    return 'Unk0041'


def _signin(b, d):
    return 'SignIn'


def _pressstart(b, d):
    t = b.byte_arg('type')
    if t == 1:
        b.expr_arg('arg1')
    return 'PressStart'


def _systemmes(b, d):
    t = b.byte_arg('type')
    if t == 1:
        b.expr_arg('arg1')
    elif t == 2:
        b.expr_arg('arg1')
    return 'SystemMes'


def _voicetable(b, d):
    t = b.byte_arg('type')
    if t == 1:
        b.u16_arg('arg1')
    return 'VoiceTableLoadMaybe'


def _un52(b, d):
    t = b.byte_arg('type')
    if t != 0:
        b.expr_arg('arg1')
    return 'Unk0052'


def _un53(b, d):
    t = b.byte_arg('type'); b.expr_arg('arg1')
    if t != 1:
        b.expr_arg('arg2')
    else:
        b.u16_arg('arg2')
    return 'Unk0053'


def _un54(b, d):
    b.byte_arg('type'); b.expr_arg('arg1')
    return 'Unk0054'


def _un55(b, d):
    b.expr_arg('arg1'); b.expr_arg('arg2'); b.expr_arg('arg3')
    return 'Unk0055'


def _un0052(b, d):
    t = b.byte_arg('type')
    if t != 0:
        b.expr_arg('arg1')
    return 'Unk0052'


def _vgmisc(b, d):
    return None


def _bgmduel(b, d):
    t = b.byte_arg('type')
    if t in (0, 1, 2, 3):
        if t in (0, 2, 3):
            b.expr_arg('arg1')
        return {0: 'BGMduelPlay_00', 1: 'BGMduelPlay_01',
                2: 'BGMduelPlay_02', 3: 'BGMduelPlay_03'}[t]
    return None


def _calc(b, d):
    t = b.byte_arg('type')
    if t in (0, 1, 2, 3, 4, 5, 6):
        b.global_arg('destination')
        if t in (0, 1):
            b.expr_arg('angle')
        elif t == 2:
            b.expr_arg('x'); b.expr_arg('y')
        elif t in (3, 4):
            b.expr_arg('base'); b.expr_arg('angle'); b.expr_arg('offset')
        elif t == 5:
            b.expr_arg('value'); b.expr_arg('multiplier'); b.expr_arg('divider')
        elif t == 6:
            b.expr_arg('x'); b.expr_arg('a'); b.expr_arg('b')
        return 'Calc'
    return None


def _setflag(b, d):
    b.p += 1
    b.byte_arg('arg1')
    b.flag_arg('arg2')
    return 'SetFlag'


def _resetflag(b, d):
    b.p += 1
    b.byte_arg('arg1')
    b.flag_arg('arg2')
    return 'ResetFlag'


def _createthread(b, d):
    t = b.byte_arg('type')
    b.expr_arg('threadId')
    ln = _expr_len(b.data, b.p)
    b.p += ln + 2  # FarLabel: expr + uint16
    if t == 128:
        while b.data[b.p] != 0:
            b.p += 1
        b.p += 2
    return 'CreateThread'


SPECIAL = {
    0x0001: _createthread,
    0x0012: _setflag,
    0x0013: _resetflag,
    0x0017: _keywaittimer,
    0x001E: _threadcontrolstore,
    0x0021: _bgmplay,
    0x0023: _seplay,
    0x002F: _achievement,
    0x003A: _bgmduel,
    0x0043: _systemmes,
    0x0044: _systemmenu,
    0x004A: _debuediter,
    0x004B: _un004b,
    0x0053: _un53,
    0x0105: _calc,
    0x0106: _mes_viewflag,
    0x0109: _messetid,
    0x010A: _mescls,
    0x010C: _mes,
    0x010D: _mesmain,
    0x0110: _mesrev,
    0x0111: _messwindow,
    0x0112: _sel,
    0x0113: _select,
    0x0114: _syssel,
    0x0115: _sysselect,
    0x0121: _un0121,
    0x0122: _un0122,
    0x0123: _un0123,
    0x0125: _un0125,
    0x0127: _un0127,
    0x0128: _un0128,
    0x012C: _un012c,
    0x012E: _un012e,
    0x012F: _un012f,
    0x1000: _un1000,
    0x1004: _bgsetlink,
    0x1006: _un1006,
    0x100E: _bgloadex,
    0x1010: _un1010,
    0x1011: _un1011,
    0x1013: _option,
    0x101B: _help,
    0x101D: _soundmenu,
    0x101F: _un101f,
    0x1020: _moviemode,
    0x1021: _clistinit,
    0x1022: _autosave,
    0x1023: _un1023,
    0x1024: _un1024,
    0x1032: _un1032,
    0x1033: _un1033,
    0x1036: _un1036,
    0x1037: _un1037,
}

ARG_ADDERS = {
    BYTE: lambda b, n: b.byte_arg(n),
    UINT16: lambda b, n: b.u16_arg(n),
    EXPR: lambda b, n: b.expr_arg(n),
    LOCALLABEL: lambda b, n: b.label_arg(n),
    FARPABEL: lambda b, n: b.far_arg(n),
    RETADDR: lambda b, n: b.ret_arg(n),
    STRREF: lambda b, n: b.strref_arg(n),
    EXPRFLAG: lambda b, n: b.flag_arg(n),
    EXPRGLOBAL: lambda b, n: b.global_arg(n),
    EXPRTHREAD: lambda b, n: b.thread_arg(n),
}


def decode(data: bytes, addr: int, maxlen: int):
    """Decode one instruction at ``addr``.

    Argument offsets/lengths are reported relative to ``addr`` (the start of the
    opcode), so ``ins.raw[off:off+len]`` always slices the encoded bytes.
    """
    op = (data[addr] << 8) | data[addr + 1]
    # Port of ProcBuilder.DECODER_PROC_INIT (or the 1-byte Assign prefix):
    # the Builder starts at the opcode so recorded offsets are instruction-relative.
    b = Builder(data, addr, maxlen)
    b.p = addr + (1 if (op & 0xFF00) == 0xFE00 else 2)
    if (op & 0xFF00) == 0xFE00:
        b.expr_arg('expr')
        return 'Assign', b.p - addr, b.args
    fn = SPECIAL.get(op)
    if fn is not None:
        name = fn(b, data)
    else:
        spec = SIMPLE.get(op)
        if spec is None:
            return '__Unrecognized__', maxlen, []
        name, kinds = spec
        for k in kinds:
            ARG_ADDERS[k](b, k)
    if name is None:
        return '__Unrecognized__', maxlen, []
    return name, b.p - addr, b.args


def parse_labels(data: bytes, strings_offset: int):
    labels = [struct.unpack_from('<I', data, 12)[0]]
    p = 16
    while p < labels[0]:
        addr = struct.unpack_from('<I', data, p)[0]
        p += 4
        if addr == 0:
            break
        labels.append(addr)
    return labels, p


def op_of(data: bytes, addr: int) -> int:
    return (data[addr] << 8) | data[addr + 1]


# Instructions that load a dialogue line from an .msb.  The trailing arg is an
# ExprStringRef whose value is the .msb *memory offset* (== entry index * 100).
MES_LOAD_NAMES = (
    'Switch_Mes_LoadDialogue',
    'Switch_Mes_LoadVoicedDialogue',
    'Vita_Mes_LoadDialogue',
    'Vita_Mes_LoadVoicedDialogue',
)

MES_MAIN_DIALOGUE = 'MesMain_DisplayDialogue'


class Instruction:
    """A decoded instruction with raw byte range and decoded arguments."""

    __slots__ = ('address', 'opcode', 'name', 'args', 'length', 'raw')

    def __init__(self, address: int, opcode: int, name: str, args, length: int, raw: bytes):
        self.address = address
        self.opcode = opcode
        self.name = name
        self.args = args
        self.length = length
        self.raw = raw

    def arg(self, name: str, default=None):
        for kind, aname, value, _off, _ln in self.args:
            if aname == name:
                return value
        return default

    def args_of(self, kind: str):
        """All args of a given kind as ``(name, value, offset, length)``."""
        return [(n, v, o, l) for (k, n, v, o, l) in self.args if k == kind]

    @property
    def end(self) -> int:
        return self.address + self.length

    def __repr__(self):
        return '<%04X %s len=%d @%X>' % (self.opcode, self.name, self.length, self.address)


def disassemble(data: bytes, strings_offset: int):
    """Port of SC3BaseDisassembler.DisassembleFile.

    Returns ``(labels, [(label_addr, [(addr, opcode, name, args, length)])])``.
    Instruction tuples include their byte ``length`` so callers can copy/splice
    the code section without re-decoding.
    """
    labels, _table_end = parse_labels(data, strings_offset)
    out = []
    for i, laddr in enumerate(labels):
        end = labels[i + 1] if i + 1 < len(labels) else strings_offset
        p = laddr
        block = []
        while end - p > 1:
            name, length, args = decode(data, p, end - p)
            if length <= 0:
                break
            block.append((p, op_of(data, p), name, args, length))
            p += length
        out.append((laddr, block))
    return labels, out


def iter_instructions(data: bytes, strings_offset: int) -> List[Instruction]:
    """Flat, address-ordered list of every instruction in the code section."""
    _labels, blocks = disassemble(data, strings_offset)
    out: List[Instruction] = []
    for _laddr, block in blocks:
        for (a, op, name, args, length) in block:
            out.append(Instruction(a, op, name, args, length, data[a:a + length]))
    out.sort(key=lambda i: i.address)
    return out


def mes_loads(instructions: List[Instruction]) -> List[Instruction]:
    """All Mes_Load* instructions (i.e. the ones that reference an .msb entry)."""
    return [i for i in instructions if i.name in MES_LOAD_NAMES]


def write_expr(value: int) -> bytes:
    """Encode an integer as an SC3 expression (port of SC3Expression.getRaw).

    Mirrors the C# byte-for-byte, including the extra padding byte emitted by the
    4-byte and 7-byte forms.
    """
    v = value
    sign = 0x10 if v < 0 else 0x00
    a = abs(v)
    if a < 16:
        return bytes([0x80 | sign | (v & 0x0F), 0, 0])
    if a < 4096:
        return bytes([0xA0 | sign | ((v & 0xF00) >> 8), v & 0xFF, 0, 0])
    if a < 1048576:
        return bytes([0xC0 | sign | ((v & 0xF0000) >> 16), v & 0xFF, (v & 0xFF00) >> 8, 0, 0])
    return (bytes([0xE0 | sign]) + struct.pack('<I', v & 0xFFFFFFFF) + bytes([0, 0]))


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
    # Turkish dotless i: NFKC decomposes "I\u0307" into this, which the engine
    # font lacks.  The charset does have ASCII 'I', so fold it back.
    'İ': 'I', 'ı': 'i',
    # Cyrillic/Greek look-alikes that show up in untranslated text.
    'ё': 'e', 'Ё': 'E',
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
            return self.direct[idx] # pyright: ignore[reportReturnType]
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
        # EXPR_IMM is not a small opcode, so it never appears in OPINFO -- the
        # immediate check has to come first or every literal falls through to
        # EXPR_END and decodes as 0 (which is how <color=31> became <color=0>).
        if self.type == EXPR_IMM:
            return ExprNode(EXPR_IMM, value=self.value)
        info = OPINFO.get(self.type)
        if info is None: return ExprNode(EXPR_END)
        prec, rassoc, const_ok, ops = info
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


TAG_RE = re.compile(r'\<(?P<name>\/?([a-zA-Z0-9  _\-= ]+)\/?)\>')

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


#: Zero-width / formatting characters that carry no glyph in the engine's font.
INVISIBLE_CHARS = '\u200b\u200c\u200d\ufeff\u2060\u00ad'

#: Characters the engine parses *structurally* and that must never be rewritten.
#:
#: ``＆`` (U+FF06 FULLWIDTH AMPERSAND) is the engine's two-speaker nameplate
#: separator: every ``<parallel>`` line in the original scripts spells its
#: nameplate ``SpeakerA＆SpeakerB`` so the engine knows to draw two nameplates.
#: NFKC folds U+FF06 to ASCII ``&``, and *no* nameplate in the entire original
#: script set uses ASCII ``&`` -- so the separator is destroyed and the engine
#: can no longer split the name.
NFKC_PROTECTED = {
    '\uff06': '\ue000',   # ＆  two-speaker nameplate separator
}


def _nfkc_preserving(text: str, charset: Optional['Charset'] = None) -> str:
    """Normalise ``text`` to NFKC without touching anything the game can render.

    NFKC is the right tool for the leftovers a translator leaves behind (smart
    quotes, ``ﬁ``, ``①``, decomposed accents), but it is destructive on the
    game's own typography: it folds ``＆``→``&``, ``（）``→``()``, ``？``→``?``,
    ``…``→``...``, full-width Latin→ASCII.  Round-tripping the shipped English
    patch through our encoder changed 4,456 entries that way.

    So the rule is: **if the game's own charset contains the character, keep it
    exactly as written; only fold characters the font has no glyph for.**  That
    matches what the original scripts do -- they are full of ``（``, ``？``,
    ``…``, ``＆`` and all of them survive a real playthrough.
    """
    if charset is None:
        for ch, sentinel in NFKC_PROTECTED.items():
            if ch in text:
                text = text.replace(ch, sentinel)
        text = unicodedata.normalize('NFKC', text)
        for ch, sentinel in NFKC_PROTECTED.items():
            text = text.replace(sentinel, ch)
        return text

    known = charset.reverse
    out: List[str] = []
    for ch in text:
        if ch in known or ch in CHAR_FALLBACKS or ch in NFKC_PROTECTED:
            out.append(ch)                       # the game has a glyph: leave it
        else:
            out.append(unicodedata.normalize('NFKC', ch))
    return ''.join(out)


def _write_text_segment(text: str, charset: Charset, out: bytearray):
    text = text.replace('\r', '').replace('\n', '').replace('&nbsp;', ' ')
    # Strip zero-width formatting characters (stray BOMs, ZWSP, soft hyphens).
    # They have no glyph in the engine font and would otherwise abort the build.
    for ch in INVISIBLE_CHARS:
        text = text.replace(ch, '')
    text = _nfkc_preserving(text, charset)
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

        # Typography / symbol fallbacks only apply when the game has no glyph for
        # the character.  Applying them unconditionally replaced '–' (charset 275)
        # with ASCII '-' across 919 entries of the shipped English patch.
        if sym not in charset.reverse:
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
        self.raw = data
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

    def rebuild_with_plan(self, blobs: List[bytes], offsets: List[int]) -> bytes:
        """Rebuild with an explicit entry count and explicit memory offsets.

        Splitting a line into extra text boxes changes both the number of entries
        and their memory offsets (the engine addresses entries by ``index * 100``,
        so every entry after an inserted one shifts).  This variant takes the
        caller-supplied offsets instead of reusing the original table.
        """
        count = len(blobs)
        data_offset = 16 + count * 8
        positions = []
        cur = data_offset
        for c in blobs:
            positions.append(cur)
            cur += len(c)

        out = bytearray(self.raw[:16])
        struct.pack_into('<I', out, 8, count)
        struct.pack_into('<I', out, 12, data_offset)
        for off, p in zip(offsets, positions):
            out.extend(struct.pack('<I', off))
            out.extend(struct.pack('<I', p - data_offset))
        for c in blobs:
            out.extend(c)
        return bytes(out)


class SCXFile:
    """Reader/writer for .scx bytecode containers.

    Layout (see SCXFile.ParseHeader / SCXFile.Save in the decompiled C#)::

        0x00  "SC3\\0"
        0x04  strings_offset   -- file offset of the string address table
        0x08  returns_offset   -- file offset of the return-address table
        0x0C  label table     -- uint32 code addresses, ends at first_label_offset
              code section    -- [first_label_offset, strings_offset)
              string addrs   -- string_count uint32
              return addrs   -- uint32 absolute code addresses
              string data    -- the strings themselves
    """

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

    @property
    def first_label_offset(self) -> int:
        """File offset at which the executable code section begins."""
        return struct.unpack_from('<I', self.raw, 12)[0]

    @property
    def labels(self) -> List[int]:
        vals, _ = parse_labels(self.raw, self.strings_offset)
        return vals

    @property
    def return_addresses(self) -> List[int]:
        first_str = self.string_addrs[0] if self.string_addrs else len(self.raw)
        out = []
        p = self.returns_offset
        while p + 4 <= first_str:
            out.append(struct.unpack_from('<I', self.raw, p)[0])
            p += 4
        return out

    def rebuild(self, new_contents: List[bytes]) -> bytes:
        """Rebuild SCX binary with new string contents matching C# SCXFile.Save."""
        if len(new_contents) != len(self.string_contents):
            raise ValueError(
                f"SCX string count mismatch: expected {len(self.string_contents)}, "
                f"got {len(new_contents)}")
        return self._assemble(self.raw[:self.strings_offset], new_contents, None)

    # ------------------------------------------------------------------
    # Line-splitting support
    # ------------------------------------------------------------------

    def apply_split_plan(self, plan: 'SplitPlan',
                         new_contents: Optional[List[bytes]] = None) -> bytes:
        """Rewrite the bytecode so split lines are revealed one box at a time.

        ``new_contents`` are this .scx's *own* string blobs (the short strings
        stored in the bytecode container, e.g. choice labels).  It defaults to the
        original contents; splitting .msb dialogue lines never changes them.  For
        every line that became N>1 boxes we emit, immediately after the original
        line's ``MesMain_DisplayDialogue``::

            MessWindow_ShowCurrent(1)
            MessWindow_AwaitShowCurrent(2)
            Mes_LoadDialogue(type=128, characterId=<same>, mesline=<next box>)
            MesMain_DisplayDialogue(0)

        This is exactly the sequence the shipped English patch uses.  Because the
        code section grows, every absolute address in the label table and the
        return-address table is shifted by the number of bytes inserted ahead of
        it, and every .msb reference is retargeted to its new memory offset.
        """
        instructions = iter_instructions(self.raw, self.strings_offset)
        code_start = self.first_label_offset

        # ---- 1. retarget .msb references, find insertion points ----
        ref_map: Dict[int, int] = {}
        inserts: Dict[int, bytes] = {}     # code offset -> bytes to insert *before* it

        for pos, ins in enumerate(instructions):
            if ins.name not in MES_LOAD_NAMES:
                continue
            old_ref = ins.arg('mesline', ins.arg('line'))
            if old_ref is None:
                continue
            old_index = old_ref // 100
            if old_index not in plan.index_map:
                continue
            new_index = plan.index_map[old_index]
            boxes = plan.box_count.get(old_index, 1)
            ref_map[old_ref] = new_index * 100

            if boxes <= 1:
                continue
            # the MesMain_DisplayDialogue that shows this box
            anchor = None
            for nxt in instructions[pos + 1:]:
                if nxt.name == MES_MAIN_DIALOGUE:
                    anchor = nxt
                    break
                if nxt.name in MES_LOAD_NAMES:
                    break
            if anchor is None:
                continue
            # Reuse the speaker id expression verbatim so the continuation box
            # is drawn by the same character.
            span = self._arg_span(ins, 'characterId')
            cid_raw = ins.raw[span[0]:span[0] + span[1]] if span else write_expr(0)
            blob = bytearray()
            for extra in range(1, boxes):
                blob += bytes([0x01, 0x11, 0x01])   # MessWindow_ShowCurrent(1)
                blob += bytes([0x01, 0x11, 0x02])   # MessWindow_AwaitShowCurrent(2)
                blob += bytes([0x01, 0x0C, 0x80])   # Mes_LoadDialogue type=128
                blob += cid_raw
                blob += write_expr((new_index + extra) * 100)
                blob += bytes([0x01, 0x0D, 0x00])   # MesMain_DisplayDialogue(0)
            inserts[anchor.end] = bytes(blob)

        if new_contents is None:
            new_contents = list(self.string_contents)
        if len(new_contents) != len(self.string_contents):
            raise ValueError(
                f"SCX string count mismatch: expected {len(self.string_contents)}, "
                f"got {len(new_contents)}")
        if not ref_map:
            return self.rebuild(new_contents)

        # ---- 2. rebuild the code section, tracking old->new offsets ----
        new_code, segments = self._rewrite_code(instructions, code_start, ref_map, inserts)

        def shift(old_addr: int) -> int:
            return _apply_segments(segments, old_addr)

        # ---- 3. rewrite the header + label table ----
        header = bytearray(self.raw[:12])
        label_bytes = bytearray()
        for addr in self.labels:
            label_bytes += struct.pack('<I', shift(addr))
        pad = code_start - 12 - len(label_bytes)
        if pad < 0:
            raise ValueError("label table overflowed its reserved space")

        code_bytes = bytes(header) + bytes(label_bytes) + b'\x00' * pad + new_code

        # ---- 4. return-address table (absolute code addresses) ----
        new_returns = b''.join(struct.pack('<I', shift(a)) for a in self.return_addresses)

        return self._assemble(code_bytes, new_contents, new_returns)

    def _rewrite_code(self, instructions, code_start: int,
                      ref_map: Dict[int, int], inserts: Dict[int, bytes]):
        """Emit the patched code section and return old->new offset segments."""
        out = bytearray()
        # ``segments`` maps ORIGINAL file offsets to NEW file offsets.  ``out``
        # is only the code section, so every recorded position must be biased by
        # ``code_start`` to become a real file offset.
        segments: List[Tuple[int, int, int, int]] = []   # old_start, old_end, new_start, new_end
        cursor = code_start

        def pos() -> int:
            return code_start + len(out)

        for ins in instructions:
            if ins.address > cursor:
                # undecoded gap: copy verbatim so byte offsets stay honest
                gap = self.raw[cursor:ins.address]
                segments.append((cursor, ins.address, pos(), pos() + len(gap)))
                out += gap
                cursor = ins.address

            new_raw = self._retarget(ins, ref_map)
            segments.append((ins.address, ins.end, pos(), pos() + len(new_raw)))
            out += new_raw
            cursor = ins.end

            if ins.end in inserts:
                blob = inserts[ins.end]
                out += blob

        if cursor < self.strings_offset:
            tail = self.raw[cursor:self.strings_offset]
            segments.append((cursor, self.strings_offset, pos(), pos() + len(tail)))
            out += tail

        return bytes(out), segments

    def _retarget(self, ins: Instruction, ref_map: Dict[int, int]) -> bytes:
        """Return ``ins`` with any .msb reference replaced by its new value.

        A new offset may need a wider expression encoding (crossing the 4096
        boundary), so the instruction is allowed to change size.  That is safe
        because the code section is rebuilt from decoded instructions and every
        label/return address is remapped through the resulting offset map.
        """
        spans = []
        seen = set()
        for (_k, _n, _v, off, ln) in ins.args:
            if _k != EXPRSTRINGREF or off in seen:
                continue
            seen.add(off)
            value = _const_expr(ins.raw, off, ln)
            if value is not None and value in ref_map:
                spans.append((off, ln, ref_map[value]))
        if not spans:
            return ins.raw

        out = bytearray()
        cursor = 0
        for off, ln, new_val in spans:
            out += ins.raw[cursor:off]
            out += write_expr(new_val)
            cursor = off + ln
        out += ins.raw[cursor:]
        return bytes(out)

    @staticmethod
    def _arg_span(ins: Instruction, name: str) -> Optional[Tuple[int, int]]:
        """Exact (offset, length) of a named argument.

        The length comes from the decoder, which walked the expression token by
        token, so nested forms like ``GlobalVars[...]`` are sliced exactly as they
        were consumed.
        """
        for (_k, nm, _v, off, ln) in ins.args:
            if nm == name:
                return off, ln
        return None

    def _assemble(self, code: bytes, new_contents: List[bytes],
                  returns_table_bytes: Optional[bytes]) -> bytes:
        code_bytes = bytearray(code)
        div = len(code_bytes) % 4
        if div != 0:
            code_bytes.extend(b'\x00' * (4 - div))

        new_strings_offset = len(code_bytes)
        num_strings = len(new_contents)
        new_returns_offset = new_strings_offset + num_strings * 4

        if returns_table_bytes is None:
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


def _const_expr(raw: bytes, off: int, length: int) -> Optional[int]:
    """Evaluate a raw expression, returning None if it is not a plain constant."""
    if length < 3:
        return None
    b0 = raw[off]
    if not (b0 & 0x80):
        return None
    kind = b0 & 0x60
    if kind == 0x00:
        if length < 2:
            return None
        v = b0 & 0x1F
        return v | 0x7FFFFFE0 if (b0 & 0x10) else v
    if kind == 0x20:
        if length < 3:
            return None
        return ((b0 & 0x1F) << 8) | raw[off + 1]
    if kind == 0x40:
        if length < 4:
            return None
        return ((b0 & 0x1F) << 16) | (raw[off + 2] << 8) | raw[off + 1]
    return None


def _apply_segments(segments: Sequence[Tuple[int, int, int, int]], old_addr: int) -> int:
    """Map an original code address onto the patched code section."""
    for old_start, old_end, new_start, new_end in segments:
        if old_start <= old_addr <= old_end:
            return new_start + (old_addr - old_start)
    # address before the first decoded instruction
    return old_addr


# ============================================================
# Text Formatting & Character Name Resolution
# ============================================================

#: The engine's two-speaker nameplate separator.  Every ``<parallel>`` line in
#: the original scripts spells its nameplate ``A＆B`` (and ``雪乃＆結衣＆いろは``
#: for three speakers); the engine splits on it to draw one nameplate per column.
#: No nameplate anywhere in the original script set uses ASCII ``&``.
PARALLEL_SEP = '\uff06'


def _apply_name_mode(en: str, mode: str) -> str:
    """Put a names.json value into the requested display order."""
    if mode == 'fullwidth':
        return to_fullwidth(en)
    if mode == 'western':
        parts = en.split('\u3000')
        if len(parts) == 2:
            return parts[1] + '\u3000' + parts[0]
    return en


def fix_engine_breaking(value: str) -> str:
    """Repair only what would stop the engine rendering the nameplate.

    names.json is authoritative: whatever order you write a name in is the order
    that gets written to the .msb.  The single exception is the two-speaker
    separator -- the engine parses ``\uff06`` (U+FF06 FULLWIDTH AMPERSAND) to decide
    it must draw two nameplates, and no nameplate in the original scripts uses
    ASCII ``&``.  NFKC also folds U+FF06 to ``&``, so typing (or importing) an
    ASCII ampersand has to be promoted back.

    Idempotent: a value already using \uff06 comes back unchanged.
    """
    return value.replace('&', PARALLEL_SEP)


class NameDB:
    """names.json: the single source of truth for every nameplate.

    Keyed on the nameplate **as it appears in the pristine source .msb**, so the
    key can never drift.  The ``[Name]`` field in exported_txt is deliberately
    ignored: it has been rewritten by name_inserter, by hand, and by several
    migrations, and every divergence from names.json silently suppressed the
    nameplate in-game (a stale ASCII "&" separator, " and " instead of ＆,
    western word order, ...).  names.json is edited deliberately; the .txt files
    hold dialogue only.

    Lookups are exact first, then NFKC-normalised with ＆ shielded, because
    names.json is hand-edited with ASCII parens/letters while the scripts use
    full-width forms ('生徒(女子)A' vs '生徒（女子）Ａ').
    """

    def __init__(self, path: Optional[str] = None):
        self.exact: Dict[str, str] = {}
        self.norm: Dict[str, str] = {}
        path = path or NAME_DB_PATH
        if not os.path.isfile(path):
            return
        with open(path, encoding='utf-8') as f:
            raw = json.load(f)
        for k, v in raw.items():
            if not isinstance(k, str) or not isinstance(v, str):
                continue
            if v == k:
                continue                       # no-op entry, never a translation
            # Accept any word order and either ampersand: the value is normalised
            # to the engine's own form on the way in, so names.json can be
            # written the way the translator finds natural.
            v = fix_engine_breaking(v)
            if v == k:
                continue
            self.exact.setdefault(k, v)
            self.norm.setdefault(_nfkc_preserving(k), v)

    def lookup(self, jp: Optional[str]) -> Optional[str]:
        """English nameplate for a Japanese one, or None if not in the database."""
        if not jp:
            return None
        v = self.exact.get(jp)
        if v is not None:
            return v
        return self.norm.get(_nfkc_preserving(jp))

    def __len__(self) -> int:
        return len(self.exact)


def resolve_nameplate(db: 'NameDB', jp_name: Optional[str], mode: str) -> Optional[str]:
    """The nameplate to write, derived only from the source .msb + names.json.

    An unknown name falls back to the Japanese original rather than to anything in
    the .txt.  Both the dialogue nameplate and the matching _system_00.msb
    registry entry go through this same function, so a name we have no translation
    for stays Japanese on *both* sides and still matches.
    """
    if jp_name is None:
        return None
    if mode == 'orig':
        return jp_name
    en = db.lookup(jp_name)
    if en is None:
        return jp_name
    return _apply_name_mode(en, mode)


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
# Text Box Fitting / Replic Splitting
# ============================================================
#
# A single .msb entry renders as one text box (one "replic").  When a translated
# line is wider/taller than the box, the tail is clipped and never shown.  The
# SC3 engine already supports showing several boxes in sequence: a dialogue line
# can be followed by MessWindow_ShowCurrent / MessWindow_AwaitShowCurrent and a
# second Mes_LoadDialogue, which reveals the next box on button press.
#
# Width is measured with the same rule the decompiled C# editor uses
# (AutoformatHelper.WordLength): a glyph counts 1 cell when its charset code is
# < 126 and 2 cells otherwise, so Japanese/full-width glyphs are double width.

# DEFAULT_BOX_WIDTH and DEFAULT_BOX_LINES live in the "Build Options" block at the
# top of this file -- that is the single place any of them is defined.  They used to
# be redefined here as well, which silently shadowed the real setting.
#
# The box is a window: it shows DEFAULT_BOX_LINES rendered lines of DEFAULT_BOX_WIDTH
# cells, and the engine greedily wraps inside it.  A box therefore holds at most
# WIDTH * LINES cells, and slightly fewer in practice because the wrap loses cells at
# every word boundary -- split_line_to_boxes() simulates that wrap.

#: Maximum number of text boxes a single line may occupy before we give up and leave
#: it whole (letting the engine clip it) rather than dropping text.
MAX_BOXES_PER_LINE = 8

#: Tokens that must never be split across boxes.
_PROTECTED_TOKENS = (
    '<prompt>', '</prompt>', '<parallel>', '<upperText>', '<charCenter>',
    '<alt_br>', '<br>', '<br/>',
)

#: Only real scene scripts get the line-splitting treatment.  Everything else
#: (``_mail_*``, ``_system_00``, ``_startup_swi_00``, ``_tips_*``, ``main*_*``,
#: ``clrflg_*``, ``macrosys*``, ``anime_*``, ``zz*``) is UI/system text rendered
#: in scrolling panels, not in a 3-line dialogue box -- splitting it corrupts the
#: UI and buys nothing.
SCENE_STEM_PREFIXES = ('og_', 'og2_')


def is_scene_script(stem: str) -> bool:
    return stem.startswith(SCENE_STEM_PREFIXES)


#: Memory ids at or above this value in _system_00.msb are the engine's canonical
#: character-name registry (257 entries, ids 100000..110020).  No script loads
#: them -- the engine reads them directly and matches them against the nameplates
#: in the dialogue .msb files.  They are the only part of _system_00.msb that
#: must be translated for English nameplates to appear.
NAME_REGISTRY_BASE = 100000

#: Files whose text is UI/system rather than dialogue.  The official C# tool has
#: no special handling for them at all (nothing in SC3Tool/SC3Library references
#: a system file by name), and the shipped English patch translates _system_00.msb
#: wholesale and works, so we translate them too.  What *is* special is the
#: character-name registry they carry, whose entries are forced to names.json so
#: they cannot drift from the dialogue nameplates the engine matches them against.
SYSTEM_FILE_STEMS = frozenset({
    '_system_00', '_startup_swi_00', '_mail_og_00', '_mail_og2_00',
})


def validate_system_output(stem: str, src_msb: MesFile, out_data: bytes) -> List[str]:
    """Structural checks that keep a rebuilt system file loadable.

    The engine reads these files by memory id, so the only things that can break
    it are a changed entry count, changed memory ids, or an entry that no longer
    decodes.  Text *length* is free: the shipped patch's _system_00.msb is 86%
    larger than the Japanese original and works fine.
    """
    problems: List[str] = []
    try:
        out = MesFile(out_data)
    except Exception as e:
        return ['%s: output is not a valid .msb (%s)' % (stem, e)]
    if out.count != src_msb.count:
        problems.append('%s: entry count %d -> %d' % (stem, src_msb.count, out.count))
    a = [m for m, _ in src_msb.string_entries]
    b = [m for m, _ in out.string_entries]
    if a != b:
        n = sum(1 for x, y in zip(a, b) if x != y)
        problems.append('%s: %d memory id(s) changed' % (stem, n))
    for i, (_m, raw) in enumerate(out.string_entries):
        if not raw:
            problems.append('%s: entry %d encoded to nothing' % (stem, i))
    return problems


#: The separator the engine expects between words inside a .msb string.  ASCII
#: space cannot be stored there (it terminates the string), so every word boundary
#: is written as U+3000 IDEOGRAPHIC SPACE.  Exactly one per boundary.
IDEO_SPACE = '\u3000'


def char_width(ch: str, charset: Charset) -> int:
    """Display width of a single glyph, per AutoformatHelper.WordLength."""
    code = charset.reverse.get(ch)
    if code is None:
        code = 126
    return 1 if code < 126 else 2


def text_width(text: str, charset: Charset) -> int:
    """Display width of ``text`` ignoring any <tags> it contains."""
    total = 0
    i = 0
    n = len(text)
    while i < n:
        m = TAG_RE.match(text, i)
        if m:
            i = m.end()
            continue
        total += char_width(text[i], charset)
        i += 1
    return total


def _tokenize_line(text: str) -> List[Tuple[bool, str]]:
    """Split text into (is_break_opportunity, chunk) pairs.

    A break opportunity is any ASCII space or U+3000 that is not inside a
    <tag>.  Runs of separators collapse into a single break point so we do not
    emit leading/trailing spaces on the new box.
    """
    tokens: List[Tuple[bool, str]] = []
    buf: List[str] = []
    i = 0
    n = len(text)
    while i < n:
        m = TAG_RE.match(text, i)
        if m:
            buf.append(m.group(0))
            i = m.end()
            continue
        ch = text[i]
        if ch in (' ', '\u3000'):
            # consume the whole run of whitespace as one break opportunity
            j = i
            while j < n and text[j] in (' ', '\u3000'):
                j += 1
            if buf:
                tokens.append((False, ''.join(buf)))
                buf = []
            tokens.append((True, '\u3000'))
            i = j
            continue
        buf.append(ch)
        i += 1
    if buf:
        tokens.append((False, ''.join(buf)))
    return tokens


class _Wrapper:
    """Simulates the engine's greedy line wrap inside one text box.

    The engine does NOT treat the box as a single flat character budget.  It wraps
    the text at ``box_width`` cells per rendered line and the box shows
    ``box_lines`` lines.  Whenever the next word does not fit in what is left of
    the current line it is pushed down to the next one and the gap is wasted, so a
    box holding 153 cells of text can still need FOUR rendered lines.  That is
    exactly how text gets clipped while the third line looks half empty.

    Modelling the wrap is what lets the packer know when a box is genuinely full.
    """

    __slots__ = ('width', 'lines')

    def __init__(self, width: int) -> None:
        self.width = width
        self.lines = [0]

    def clone(self) -> '_Wrapper':
        w = _Wrapper.__new__(_Wrapper)
        w.width = self.width
        w.lines = list(self.lines)
        return w

    def add(self, word_w: int, space_w: int) -> None:
        """Append one word plus the separator that precedes it."""
        cur = self.lines[-1]
        sp = space_w if cur else 0
        if cur + sp + word_w <= self.width:
            self.lines[-1] = cur + sp + word_w
            return
        if word_w <= self.width:
            self.lines.append(word_w)
            return
        # a single word wider than a whole line: the engine hard-breaks it
        self.lines.append(self.width)
        rest = word_w - self.width
        while rest > self.width:
            self.lines.append(self.width)
            rest -= self.width
        self.lines.append(rest)

    @property
    def count(self) -> int:
        return len(self.lines)


def wrap_line_count(text: str, charset: Charset, box_width: int) -> int:
    """How many rendered lines the engine needs for ``text`` at ``box_width``."""
    wrap = _Wrapper(box_width)
    sp = text_width(' ', charset)
    for word in text.replace(IDEO_SPACE, ' ').split(' '):
        if word:
            wrap.add(text_width(word, charset), sp)
    return wrap.count


def split_line_to_boxes(text: str, charset: Charset, box_width: int,
                        box_lines: int = DEFAULT_BOX_LINES,
                        max_boxes: int = 0) -> List[str]:
    """Split one dialogue line into as many text boxes as it really needs.

    ``box_width`` is THE character limit: how many half-width cells fit on ONE
    rendered line of the text box.  ``box_lines`` is how many such lines the box
    shows at once, so one box holds at most ``box_width * box_lines`` cells.  Raise
    ``box_width`` to make the boxes bigger; the split points are recomputed from
    scratch on every build, so there is nothing else to keep in sync.

    The line is left completely untouched unless it genuinely does not fit, so the
    overwhelmingly common case is a one-element list and the reader sees exactly
    one text box, as in the original game.

    Splits only at whitespace, never inside a <tag>, and packs each box as full as
    the engine's own line wrapping allows: a word moves to the next box only when
    adding it would push the box past ``box_lines`` rendered lines.  Budgeting a
    flat number of cells instead fills the box with text that the engine then
    wraps onto a fourth, invisible line.
    """
    if not text:
        return [text]

    # Lines that already contain an explicit line break are laid out by the
    # engine itself; splitting them further would fight the author's intent.
    if any(tok in text for tok in ('<br>', '<br/>', '<prompt>', '<parallel>')):
        return [text]

    if wrap_line_count(text, charset, box_width) <= box_lines:
        return [text]

    tokens = _tokenize_line(text)
    space_w = text_width(' ', charset)
    boxes: List[str] = []
    cur: List[str] = []
    wrap = _Wrapper(box_width)

    def flush():
        nonlocal cur, wrap
        if cur:
            joined = ''.join(cur).strip(' ' + IDEO_SPACE)
            if joined:
                boxes.append(joined)
        cur = []
        wrap = _Wrapper(box_width)

    for is_break, chunk in tokens:
        if is_break:
            # A break token is only a *marker* for a possible wrap point.  It must
            # not contribute a character itself: the single separator is emitted
            # below, together with the word that follows the break.  Emitting it
            # in both places doubled every space on a split line, inflating each
            # box by one cell per word and making it overflow the real text box.
            continue

        cw = text_width(chunk, charset)
        if not cur:
            cur.append(chunk)
            wrap.add(cw, space_w)
            continue
        trial = wrap.clone()
        trial.add(cw, space_w)
        if trial.count <= box_lines:
            cur.append(IDEO_SPACE)
            cur.append(chunk)
            wrap = trial
        else:
            flush()
            cur.append(chunk)
            wrap.add(cw, space_w)
    flush()

    if len(boxes) <= 1:
        return [text]

    # Never drop text: if the line would need more boxes than we allow, leave it
    # whole and let the engine clip it, exactly as the unpatched game does.
    if max_boxes and len(boxes) > max_boxes:
        return [text]

    # Preserve the opening bracket on the first box and the closing one on the
    # last, so the quote marks still wrap the whole sentence across boxes.
    # (The reference English patch does exactly this: its split lines end with a
    #  bare 「 on the first box and the 」 only reappears on the final box.)
    return boxes


# ============================================================
# Replic split plan
# ============================================================

def parent_stem_hint(stem: str) -> str:
    """og_n001ess0_00 -> og_n001ess0 (the owning .scx stem)."""
    return stem[:-3] if stem.endswith('_00') else stem


class SplitPlan:
    """Describes how .msb entries are re-laid-out when lines are split.

    The engine addresses .msb entries by *memory offset* which the original
    scripts space at ``index * 100`` (see MesScript.AddAt/RemoveAt in the
    decompiled C#).  Splitting a line into N boxes therefore means:

      * inserting N-1 new entries,
      * renumbering every later entry's offset,
      * and rewriting every .msb reference in the .scx bytecode.
    """

    def __init__(self) -> None:
        #: new entry index for each original entry index
        self.index_map: Dict[int, int] = {}
        #: original entry index -> number of text boxes it became
        self.box_count: Dict[int, int] = {}
        #: list of (original_entry_index, text) in final output order
        self.outputs: List[Tuple[int, str]] = []
        self.total_entries = 0
        self.split_lines = 0

    @property
    def has_splits(self) -> bool:
        return self.split_lines > 0

    def new_ref(self, old_index: int, box: int = 0) -> int:
        """Memory offset of box ``box`` (0-based) of original entry ``old_index``."""
        return (self.index_map[old_index] + box) * 100

    def build(self, per_entry: Sequence[List[str]]) -> None:
        """Record the output layout given, per original entry, its box texts."""
        out_index = 0
        for old_index, boxes in enumerate(per_entry):
            self.index_map[old_index] = out_index
            self.box_count[old_index] = len(boxes)
            if len(boxes) > 1:
                self.split_lines += 1
            for text in boxes:
                self.outputs.append((old_index, text))
                out_index += 1
        self.total_entries = out_index


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
                name_mode: str = DEFAULT_NAME_MODE,
                split_enabled: bool = DEFAULT_SPLIT,
                box_width: int = DEFAULT_BOX_WIDTH,
                box_lines: int = DEFAULT_BOX_LINES,
                translate_system_names: bool = DEFAULT_TRANSLATE_SYSTEM_NAMES,
                name_db_path: str = NAME_DB_PATH,
                deploy_target: Optional[str] = None):
    """
    Recompile translations from txt_dir into output/ directory.
    - Matches translation files by name against source scripts.
    - Enforces U+3000 space and proper name formatting.
    - Splits dialogue lines that overflow the text box into a sequence of
      boxes revealed on button press (patches both the .msb and its .scx).
      A line is only split when its width exceeds ``box_width * box_lines``.
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
    if split_enabled:
        print(f"  Line Splitting             : ON "
              f"(box = {box_width} cells x {box_lines} lines "
              f"= {box_width * box_lines} cells before overflow)")
    else:
        print("  Line Splitting             : OFF")
    db = NameDB(name_db_path)
    print(f"  Nameplate Database         : {os.path.basename(name_db_path)} "
          f"({len(db)} entries) -- [Name] fields in the .txt are ignored")
    print(f"  System Name Registry       : {'translated' if translate_system_names else 'verbatim'}")
    print("=" * 60 + "\n")

    ok_msb = 0
    registry_stats: Dict[str, Tuple[int, int]] = {}
    system_problems: List[str] = []
    ok_rebuilt_scx = 0
    ok_patched_scx = 0
    rebuilt_scx_stems: Set[str] = set()
    scx_to_sync: Set[str] = set()
    #: parent scx stem -> SplitPlan produced by its .msb
    split_report: Dict[str, SplitPlan] = {}
    #: rebuilt .scx files awaiting write (see the deferred pass below)
    deferred_scx: List[Tuple[str, str, 'SCXFile', List[bytes]]] = []
    total_split_lines = 0
    total_split_boxes = 0

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

                # ---- parse every line into (name, boxes) first ----
                plan = SplitPlan()
                per_entry: List[List[str]] = []
                # (nameplate, is_this_text_in_the_extra_field, unused, original binary tail)
                encoded: List[Tuple[Optional[str], bool, str,
                                     Optional[bytes]]] = []

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
                    # p_name is intentionally unused: the nameplate comes from
                    # names.json keyed on orig.name, never from the translation.

                    final_name = resolve_nameplate(db, orig.name, name_mode)
                    # A line is either a spoken line (goes in the [Line] field) or
                    # narration (goes in the leading extra-text field).
                    if text is not None:
                        payload, as_extra = text, False
                    else:
                        payload, as_extra = (extra or ''), True
                    # _system_00.msb's character-name registry stores its names in the
                    # leading extra-text field (no 0x02 LINE marker), and the engine
                    # reads them from there.  They go through the same names.json
                    # lookup as the dialogue nameplates so the two always agree, and
                    # anything names.json has no entry for -- UI strings, and the
                    # '？？？' narrator name the shipped patch also leaves Japanese --
                    # falls back to the source bytes untouched.
                    if (orig.name is None and translate_system_names
                            and mf.string_entries[i][0] >= NAME_REGISTRY_BASE):
                        jp = (orig.extra_text or orig.text or '')
                        stripped = jp.strip()
                        en = db.lookup(stripped)
                        payload = _apply_name_mode(en, name_mode) if en is not None else jp
                        as_extra = True
                        hit, tot = registry_stats.get(stem, (0, 0))
                        registry_stats[stem] = (hit + (1 if en is not None else 0), tot + 1)
                    # The character limit (box_width) and the box height
                    # (box_lines) fully determine where the split points fall;
                    # they are recomputed here on every build.
                    boxes = ([payload] if not (split_enabled and is_scene_script(stem))
                             else split_line_to_boxes(payload, charset, box_width,
                                                      box_lines, MAX_BOXES_PER_LINE))
                    per_entry.append(boxes)
                    encoded.append((final_name, as_extra, '', orig.extra))

                plan.build(per_entry)

                # ---- encode, replicating the name onto every box ----
                new_contents: List[bytes] = []
                for old_index, boxes in enumerate(per_entry):
                    name, as_extra, _unused, extra_bin = encoded[old_index]
                    for bi, box_text in enumerate(boxes):
                        # A spoken line splits into (name, line) pairs, repeating
                        # the nameplate on each continuation box.  Narration lives
                        # in the leading extra-text field, which has no nameplate,
                        # so only the first box carries it.
                        if as_extra:
                            new_contents.append(encode_string(
                                name, None, box_text, extra_bin, charset))
                        else:
                            new_contents.append(encode_string(
                                name, box_text, '', extra_bin, charset))

                parent = parent_stem_hint(stem)
                if plan.has_splits:
                    offsets = [i * 100 for i in range(len(new_contents))]
                    out_data = mf.rebuild_with_plan(new_contents, offsets)
                    split_report[parent] = plan
                    total_split_lines += plan.split_lines
                    total_split_boxes += plan.total_entries - mf.count
                else:
                    out_data = mf.rebuild(new_contents)

                note = ''
                if stem in SYSTEM_FILE_STEMS:
                    probs = validate_system_output(stem, mf, out_data)
                    system_problems.extend(probs)
                    src_size = len(open(src_msb, 'rb').read())
                    note = (f"  [system file: {src_size} -> {len(out_data)} bytes, "
                            f"{registry_stats.get(stem, (0, 0))[1]} name-registry "
                            f"entries forced from names.json]")
                with open(out_msb, 'wb') as f:
                    f.write(out_data)

                if parent in scx_source_map:
                    scx_to_sync.add(scx_source_map[parent])

                if plan.has_splits:
                    print(f"  [OK MSB] {stem}.msb ({mf.count} -> {len(new_contents)} strings, "
                          f"{plan.split_lines} line(s) split)")
                else:
                    print(f"  [OK MSB] {stem}.msb ({len(new_contents)} strings)")
                if note:
                    print(note)
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

                    final_name = resolve_nameplate(db, orig.name, name_mode)
                    # p_name is ignored here too -- names come from names.json only.
                    raw_enc = encode_string(final_name, text, extra or '', orig.extra, charset)
                    new_contents.append(raw_enc)

                rebuilt_data = scx.rebuild(new_contents)

                rebuilt_scx_stems.add(stem)
                # Deferred: this .scx may also need its bytecode patched because
                # the paired .msb grew entries.  Translation files are visited in
                # glob order, so the .msb may not have been compiled yet -- write
                # it after every .msb has been processed.
                deferred_scx.append((out_scx, stem, scx, new_contents))
                ok_rebuilt_scx += 1
            except Exception as e:
                print(f"  [FAIL SCX REBUILD] {stem}: {e}")

    # ---- write rebuilt .scx files, applying any split plan from their .msb ----
    for out_scx, stem, scx, new_contents in deferred_scx:
        msb_plan = split_report.get(stem)
        try:
            if msb_plan is not None and msb_plan.has_splits:
                patched = scx.apply_split_plan(msb_plan, new_contents)
                with open(out_scx, 'wb') as f:
                    f.write(patched)
                ok_patched_scx += 1
                print(f"  [OK SCX REBUILD+SPLIT] {stem}.scx "
                      f"({len(new_contents)} strings, {msb_plan.split_lines} line(s) split)")
            else:
                with open(out_scx, 'wb') as f:
                    f.write(scx.rebuild(new_contents))
                print(f"  [OK SCX REBUILD] {stem}.scx ({len(new_contents)} strings)")
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
        plan = split_report.get(parent_stem)
        try:
            if plan is not None and plan.has_splits:
                # The .msb grew extra entries, so the bytecode must be patched to
                # load each new box: otherwise the engine would address the wrong
                # memory offsets and every line after the first split would break.
                with open(scx_path, 'rb') as f:
                    scx = SCXFile(f.read())
                patched = scx.apply_split_plan(plan)
                with open(dest_scx, 'wb') as f:
                    f.write(patched)
                ok_patched_scx += 1
                print(f"  [OK SCX SPLIT] {parent_stem}.scx "
                      f"({plan.split_lines} line(s) -> {plan.total_entries} boxes)")
                continue
            shutil.copy2(scx_path, dest_scx)
            ok_synced_scx += 1
        except Exception as e:
            print(f"  [FAIL SCX SYNC] {os.path.basename(scx_path)}: {e}")

    print(f"\n" + "=" * 60)
    print("COMPILATION SUMMARY:")
    if system_problems:
        print("  !! SYSTEM FILE PROBLEMS (these would stop the game loading them):")
        for pb in system_problems[:20]:
            print("     " + pb)
        if len(system_problems) > 20:
            print("     ... and %d more" % (len(system_problems) - 20))
    else:
        print("  System file structure        : OK "
              "(entry counts and memory ids intact, every entry decodes)")
    print(f"  Successfully recompiled : {ok_msb} .msb file(s) -> {out_mes00}")
    if ok_rebuilt_scx:
        print(f"  Rebuilt from translation : {ok_rebuilt_scx} .scx file(s) -> {output_dir}")
    if ok_patched_scx:
        print(f"  Patched for line splits  : {ok_patched_scx} .scx file(s) -> {output_dir}")
    print(f"  Synchronized bytecode   : {ok_synced_scx} .scx file(s) -> {output_dir}")
    if split_enabled and total_split_lines:
        print(f"  Lines split across boxes: {total_split_lines} "
              f"(+{total_split_boxes} extra text boxes)")
    print("=" * 60)

    if deploy_target:
        import deploy_output
        print()
        rc = deploy_output.deploy(output_dir, deploy_target)
        if rc != 0:
            print("\nDeployment did not complete; the build is still in %s" % output_dir)
    else:
        print("\nDeployment skipped (--no-deploy). To install manually, copy everything")
        print("  inside '%s' into your mod folder, replacing what is there." % output_dir)


# ============================================================
# Main Entry Point
# ============================================================

def main():
    parser = argparse.ArgumentParser(description="Oregairu Nintendo Switch Translation Tool")
    parser.add_argument("action", nargs="?", choices=["extract", "reimport"], help="Action: 'extract' or 'reimport'")
    parser.add_argument("--script-dir", default=SCRIPT_DIR, help="Source scripts directory (default: script/)")
    parser.add_argument("--txt-dir", default=TXT_DIR, help="Translation text directory (default: exported_txt/)")
    parser.add_argument("--output-dir", default=OUTPUT_DIR, help="Output directory (default: output/)")
    parser.add_argument("--name-mode", choices=["english", "western", "orig", "fullwidth"],
                        default=DEFAULT_NAME_MODE,
                        help="Character name mode: 'english' (Surname　GivenName in ASCII), 'western' (GivenName　Surname in ASCII), 'orig' (Japanese), or 'fullwidth'")
    parser.add_argument("--charset", default=CHARSET_PATH, help="Path to charset.utf8 (default: resources/ogvd/charset.utf8)")
    parser.add_argument("--split", dest="split", action="store_true",
                        default=DEFAULT_SPLIT,
                        help="Split over-long dialogue lines into extra text boxes revealed on "
                             "button press.  ON by default.  A line that does not fit the box is "
                             "otherwise silently clipped -- the tail never appears on screen and "
                             "is not in the text log either.  The shipped English patch uses this "
                             "construct on 429 lines, so the engine definitely supports it.")
    parser.add_argument("--no-split", dest="split", action="store_false",
                        help="Leave over-long lines in a single text box (they will be clipped "
                             "on screen).")
    parser.add_argument("--box-width", type=int, default=DEFAULT_BOX_WIDTH,
                        help="THE CHARACTER LIMIT: half-width cells that fit on ONE "
                             "rendered line of the dialogue text box (default: "
                             f"{DEFAULT_BOX_WIDTH}, the value the game itself uses). "
                             "Raise it for bigger text boxes and fewer split lines; "
                             "every split point is recomputed from this number on each "
                             "build. Past ~54 the tail stops fitting and is clipped "
                             "on screen. See DEFAULT_BOX_WIDTH in the source.")
    parser.add_argument("--names-db", default=NAME_DB_PATH,
                        help="Nameplate database keyed on the original Japanese name "
                             "(default: names.json).  This is the ONLY source of names; the "
                             "[Name] fields in the .txt files are ignored.")
    parser.add_argument("--no-translate-system-names", dest="sysnames",
                        action="store_false",
                        default=DEFAULT_TRANSLATE_SYSTEM_NAMES,
                        help="Leave _system_00.msb's 257-entry character-name registry in "
                             "Japanese.  Translating it is what makes English nameplates "
                             "appear, so it is on by default.")
    parser.add_argument("--no-deploy", dest="deploy", action="store_false",
                        default=DEFAULT_DEPLOY,
                        help="Do not copy output/ into the emulator script folder when "
                             "the build finishes.")
    parser.add_argument("--deploy-target", default=DEPLOY_TARGET,
                        help="Emulator script folder to deploy into (default: %(default)s)")
    parser.add_argument("--box-lines", type=int, default=DEFAULT_BOX_LINES,
                        help=f"How many rendered lines the dialogue text box shows at "
                             f"once (default: {DEFAULT_BOX_LINES}). Together with "
                             f"--box-width this sets the box size; note the engine "
                             f"wraps per line and loses cells at each word boundary, so "
                             f"a box holds a little less than "
                             f"{DEFAULT_BOX_WIDTH}*{DEFAULT_BOX_LINES} cells in practice.")

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
        do_reimport(charset, args.script_dir, args.txt_dir, args.output_dir,
                    args.name_mode, args.split, args.box_width, args.box_lines, args.sysnames,
                     args.names_db,
                     args.deploy_target if args.deploy else None)


if __name__ == "__main__":
    main()
