#!/usr/bin/env python3
"""Draw the delivered orders that refute Total order (`black-marlin.md` §14).

The two `ab-deliver` sequences of `LeanDagTest/BlackMarlin/Divergence.lean`,
computed there by `commitSeq` — Algorithm 1's own recursion — and segmented
by the invocation of `commit` that emitted each block. Blocks `5` and `7`
are authored by reliable validators and come out in opposite orders.

    scripts/black-marlin-order-figure.py  ->  docs/figures/black-marlin-order.svg
"""
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "docs/figures/black-marlin-order.svg"

# Segments as `commitSeq` emits them: (anchor of the invocation, blocks).
V_SEGS = [(3, [3]), (8, [0, 1, 2, 4, 5, 6, 8]), (7, [7]), (12, []),
          (19, [9, 10, 11, 13, 15, 16, 19])]
W_SEGS = [(3, [3]), (7, [1, 2, 7]), (12, [0, 4, 6, 12]),
          (19, [5, 9, 10, 11, 13, 15, 16, 19])]

MARK = {5: "#e65100", 7: "#00695c"}       # the two reliably authored blocks
TWIN = {8: "#dff0d8", 12: "#f8d7da"}      # the twins, one delivered by each

X0, DX, R = 116, 73, 20
VY, WY = 236, 476


def heading(y, label, sub):
    """A row's two title lines, with a halo so connectors pass behind."""
    return [f'<rect x="18" y="{y - 106}" width="{len(label) * 8.2 + 12}" height="22" '
            f'fill="#ffffff"/>',
            f'<text x="24" y="{y - 90}" font-size="15" fill="#111">{label}</text>',
            f'<rect x="18" y="{y - 84}" width="{len(sub) * 6.4 + 12}" height="19" '
            f'fill="#ffffff"/>',
            f'<text x="24" y="{y - 70}" font-size="12" fill="#777">{sub}</text>']


def row(segs, y, out):
    """One validator's delivered sequence, bracketed by commit invocation."""
    pos, i, empty = {}, 0, []
    for anchor, blocks in segs:
        if not blocks:
            empty.append((anchor, X0 + DX * i - DX // 2))
            continue
        x1 = X0 + DX * i - R - 8
        x2 = X0 + DX * (i + len(blocks) - 1) + R + 8
        out.append(f'<rect x="{x1}" y="{y - R - 14}" width="{x2 - x1}" '
                   f'height="{2 * R + 28}" rx="10" fill="none" stroke="#cccccc" '
                   f'stroke-width="1.2"/>')
        out.append(f'<text x="{(x1 + x2) / 2}" y="{y - R - 22}" font-size="12" '
                   f'fill="#888" text-anchor="middle">commit({anchor})</text>')
        for b in blocks:
            x = X0 + DX * i
            pos[b] = x
            fill = TWIN.get(b, "#ffffff")
            stroke = MARK.get(b, "#bbbbbb")
            w = 3.4 if b in MARK else 1.3
            out.append(f'<circle cx="{x}" cy="{y}" r="{R}" fill="{fill}" '
                       f'stroke="{stroke}" stroke-width="{w}"/>')
            col = MARK.get(b, "#222")
            out.append(f'<text x="{x}" y="{y + 5}" font-size="14" fill="{col}" '
                       f'text-anchor="middle">{b}</text>')
            i += 1
    return pos, empty


def main():
    W, H = 1330, 780
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" '
           f'viewBox="0 0 {W} {H}" font-family="Helvetica,Arial,sans-serif">',
           f'<rect width="{W}" height="{H}" fill="#ffffff"/>',
           '<defs>',
           '<marker id="mo" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" '
           'markerHeight="6" orient="auto"><path d="M0,0 L10,5 L0,10 z" fill="#e65100"/></marker>',
           '<marker id="mt" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" '
           'markerHeight="6" orient="auto"><path d="M0,0 L10,5 L0,10 z" fill="#00695c"/></marker>',
           '</defs>',
           f'<text x="24" y="44" font-size="17" fill="#111">Two reliable validators, '
           f'two delivered sequences</text>',
           f'<text x="24" y="68" font-size="13" fill="#666">Blocks are drawn in the order '
           f'each validator ab-delivers them. Boxes group the blocks emitted by one '
           f'invocation of commit.</text>']

    vp, ve = row(V_SEGS, VY, out)
    wp, we = row(W_SEGS, WY, out)

    # the inversion
    for b, marker in ((5, "mo"), (7, "mt")):
        col = MARK[b]
        x1, x2 = vp[b], wp[b]
        out.append(f'<path d="M{x1},{VY + R + 16} C{x1},{VY + 110} {x2},{WY - 110} '
                   f'{x2},{WY - R - 20}" fill="none" stroke="{col}" stroke-width="2.6" '
                   f'stroke-dasharray="6,5" marker-end="url(#{marker})"/>')
    out.append(f'<text x="{wp[5]}" y="{WY + R + 34}" font-size="13" fill="#e65100" '
               f'text-anchor="middle">5 arrives late</text>')
    out.append(f'<text x="{wp[7]}" y="{WY + R + 34}" font-size="13" fill="#00695c" '
               f'text-anchor="middle">7 arrives early</text>')

    # headings and side-notes last, so the connectors pass behind them
    out += heading(VY, "first validator — commits 8 at delivery(4), "
                       "then 19 at delivery(6)",
                   "delivery(4) emits the first two boxes; delivery(6) emits the rest")
    out += heading(WY, "second validator — delivery(4) fails, commits 19 at delivery(6)",
                   "a single invocation, descending 19 → 12 → 7 → 3 before emitting anything")
    for anchor, x in ve:
        msg = f'commit({anchor}) emits nothing — 12 is dropped by L27'
        out.append(f'<rect x="{x - len(msg) * 3.2}" y="{VY + R + 22}" '
                   f'width="{len(msg) * 6.4}" height="19" fill="#ffffff"/>')
        out.append(f'<text x="{x}" y="{VY + R + 36}" font-size="12" '
                   f'fill="#c62828" text-anchor="middle">{msg}</text>')

    ly = H - 208
    notes = [
        ("#e65100", "block 5 — created by validator 1, which is reliable; no twin, so "
                    "L27's filter never examines it"),
        ("#00695c", "block 7 — created by validator 3, which is reliable, and the anchor "
                    "of round 1; likewise no twin"),
        ("#dff0d8", "block 8 and block 12 — the equivocator's twins. The first validator "
                    "delivers 8 and the second 12, which is the Agreement failure"),
    ]
    for n, (col, text) in enumerate(notes):
        y = ly + n * 26
        if col.startswith("#d"):
            out.append(f'<circle cx="84" cy="{y - 4}" r="8" fill="#dff0d8" '
                       f'stroke="#bbbbbb" stroke-width="1.2"/>')
            out.append(f'<circle cx="102" cy="{y - 4}" r="8" fill="#f8d7da" '
                       f'stroke="#bbbbbb" stroke-width="1.2"/>')
        else:
            out.append(f'<circle cx="90" cy="{y - 4}" r="8" fill="none" stroke="{col}" '
                       f'stroke-width="2.6"/>')
        out.append(f'<text x="112" y="{y}" font-size="13" fill="#333">{text}</text>')

    tail = [
        "The first validator delivers 5 before 7 and the second 7 before 5, so Definition 1's "
        "Total order fails. What orders them is which",
        "segment they fall in: 5 lies in the cone of 8 and 7 in the cone of 12, so each "
        "validator takes one of them with the twin it committed",
        "and the other only later. Neither block is a twin and neither is authored by the "
        "equivocator, so no rule for choosing among twins",
        "repairs this — only a rule that makes the two descents agree, which is what no "
        "validator can run from its own view.",
    ]
    for n, text in enumerate(tail):
        out.append(f'<text x="90" y="{ly + 3 * 26 + 18 + n * 20}" font-size="13" '
                   f'fill="#111">{text}</text>')

    out.append('</svg>')
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text("\n".join(out) + "\n")
    v = [b for _, bs in V_SEGS for b in bs]
    w = [b for _, bs in W_SEGS for b in bs]
    print(f"{OUT.relative_to(ROOT)}: {len(v)} and {len(w)} blocks delivered; "
          f"5 at {v.index(5)}/{w.index(5)}, 7 at {v.index(7)}/{w.index(7)}")


if __name__ == "__main__":
    main()
