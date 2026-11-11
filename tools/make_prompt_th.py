"""Build "Prompt TH": Prompt with extra raised Thai tone marks for Tk.

Tk on Linux draws text through Xft without OpenType shaping, so a tone mark
that follows an upper vowel (ที่, นิ้ว, เมื่อ) is drawn on top of the vowel and
disappears. This adds pre-raised copies of the tone marks at private-use code
points; main.thai_marks() swaps them in before text reaches Tk.

    U+F710..F714  tone mark after a short upper vowel (ั ิ)
    U+F720..F724  tone mark after a tall upper vowel (ี ึ ื ็) or before ำ
    U+F730..F734  tone mark on a tall consonant (ป ฝ ฟ ฬ), moved left of its stem

Prompt is (c) Cadson Demak, SIL OFL 1.1 (no Reserved Font Name). The modified
fonts are renamed "Prompt TH" and keep the same licence (see OFL.txt).

usage: python make_prompt_th.py SRC_DIR OUT_DIR
"""
import os
import sys

from fontTools.pens.boundsPen import BoundsPen
from fontTools.ttLib import TTFont
from fontTools.ttLib.tables._g_l_y_f import Glyph, GlyphComponent

TONES = [0x0E48, 0x0E49, 0x0E4A, 0x0E4B, 0x0E4C]
SHORT = [0x0E31, 0x0E34]
TALL = [0x0E35, 0x0E36, 0x0E37, 0x0E47, 0x0E33]
GAP = 40  # font units between vowel top and raised tone mark
WEIGHTS = ["Light", "Regular", "SemiBold", "Bold"]


def bounds(font, name):
    pen = BoundsPen(font.getGlyphSet())
    font.getGlyphSet()[name].draw(pen)
    return pen.bounds


def build(src, out):
    font = TTFont(src)
    cmap = font.getBestCmap()
    tone_bottom = min(bounds(font, cmap[c])[1] for c in TONES)
    short_top = max(bounds(font, cmap[c])[3] for c in SHORT)
    tall_top = max(bounds(font, cmap[c])[3] for c in TALL)
    glyf, hmtx = font["glyf"], font["hmtx"]
    order = list(font.getGlyphOrder())
    new_cmap = {}
    for base_cp, top, suffix in ((0xF710, short_top, "raised"), (0xF720, tall_top, "high")):
        shift = top + GAP - tone_bottom
        for i, cp in enumerate(TONES):
            source = cmap[cp]
            name = f"{source}.{suffix}"
            glyph = Glyph()
            glyph.numberOfContours = -1
            comp = GlyphComponent()
            comp.glyphName, comp.x, comp.y, comp.flags = source, 0, shift, 0x4  # ROUND_XY_TO_GRID
            glyph.components = [comp]
            glyf[name] = glyph
            hmtx[name] = hmtx[source]
            order.append(name)
            new_cmap[base_cp + i] = name
    # Tall consonants: keep the mark at its height, move it left of the stem.
    glyph_ref = cmap[0x0E1B]  # ป
    coords, _, _ = glyf[glyph_ref].getCoordinates(glyf)
    stem_left = min(x for x, y in coords if y > 600)
    advance = hmtx[glyph_ref][0]
    for i, cp in enumerate(TONES):
        source = cmap[cp]
        name = f"{source}.left"
        right = bounds(font, source)[2]
        glyph = Glyph()
        glyph.numberOfContours = -1
        comp = GlyphComponent()
        comp.glyphName, comp.y, comp.flags = source, 0, 0x4
        comp.x = round(stem_left - GAP / 2 - (advance + right))
        glyph.components = [comp]
        glyf[name] = glyph
        hmtx[name] = hmtx[source]
        order.append(name)
        new_cmap[0xF730 + i] = name
    font.setGlyphOrder(order)
    glyf.glyphOrder = order
    for table in font["cmap"].tables:
        if table.isUnicode():
            table.cmap.update(new_cmap)
    for glyph_name in new_cmap.values():
        glyf[glyph_name].recalcBounds(glyf)
        # FreeType places the outline by the hmtx left side bearing, so it must
        # match the moved outline or the horizontal shift is undone.
        hmtx[glyph_name] = (hmtx[glyph_name][0], glyf[glyph_name].xMin)
    font["maxp"].numGlyphs = len(order)
    for record in font["name"].names:
        if record.nameID in (1, 3, 4, 16, 18):
            record.string = record.toUnicode().replace("Prompt", "Prompt TH")
        elif record.nameID == 6:
            record.string = record.toUnicode().replace("Prompt", "PromptTH")
    font.save(out)


if __name__ == "__main__":
    src_dir, out_dir = sys.argv[1:3]
    os.makedirs(out_dir, exist_ok=True)
    for weight in WEIGHTS:
        build(os.path.join(src_dir, f"Prompt-{weight}.ttf"), os.path.join(out_dir, f"PromptTH-{weight}.ttf"))
        print("built", weight)
