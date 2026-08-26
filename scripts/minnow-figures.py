#!/usr/bin/env python3
"""Draw the three executions that defeat Minnow's `crs*` (`minnow.md`).

Each figure is generated from the same vertex and edge tables as the
witnesses in `LeanDagTest/Minnow/`, so the pictures assert nothing the
machine has not checked. The empty-slot reading of §19.2 has no figure:
it is a reading of a sentence, and the reading it loses to is the right
one.

    scripts/minnow-figures.py   ->  docs/figures/minnow-skip.svg
                                    docs/figures/minnow-deadlock.svg
"""
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
FIGS = ROOT / "docs/figures"

BYZ = "#c62828"
OK = "#2e7d32"
LEAD = "#1565c0"
DEAD = "#f8d7da"


def head(w, h, title, sub):
    return [f'<svg xmlns="http://www.w3.org/2000/svg" width="{w}" height="{h}" '
            f'viewBox="0 0 {w} {h}" font-family="Helvetica,Arial,sans-serif">',
            f'<rect width="{w}" height="{h}" fill="#ffffff"/>',
            '<defs>',
            '<marker id="ag" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" '
            f'markerHeight="6" orient="auto"><path d="M0,0 L10,5 L0,10 z" fill="{OK}"/></marker>',
            '<marker id="ar" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" '
            f'markerHeight="6" orient="auto"><path d="M0,0 L10,5 L0,10 z" fill="{BYZ}"/></marker>',
            '</defs>',
            f'<text x="24" y="40" font-size="17" fill="#111">{title}</text>',
            f'<text x="24" y="64" font-size="13" fill="#666">{sub}</text>']


def draw(out, pos, refs, r, special=(), fills=None, labels=None):
    """Faint edges for everything, coloured edges for `special`."""
    fills = fills or {}
    for a, bs in refs.items():
        for b in bs:
            if (a, b) in dict(special):
                continue
            (x1, y1), (x2, y2) = pos[a], pos[b]
            dx, dy = x2 - x1, y2 - y1
            d = (dx * dx + dy * dy) ** 0.5
            ux, uy = dx / d, dy / d
            out.append(f'<line x1="{x1 - ux * r:.1f}" y1="{y1 - uy * r:.1f}" '
                       f'x2="{x2 + ux * r:.1f}" y2="{y2 + uy * r:.1f}" '
                       f'stroke="#e6e6e6" stroke-width="1.3"/>')
    for (a, b), col in special:
        (x1, y1), (x2, y2) = pos[a], pos[b]
        dx, dy = x2 - x1, y2 - y1
        d = (dx * dx + dy * dy) ** 0.5
        ux, uy = dx / d, dy / d
        mk = "ar" if col == BYZ else "ag"
        out.append(f'<line x1="{x1 - ux * r:.1f}" y1="{y1 - uy * r:.1f}" '
                   f'x2="{x2 + ux * r:.1f}" y2="{y2 + uy * r:.1f}" '
                   f'stroke="{col}" stroke-width="2.4" marker-end="url(#{mk})"/>')
    for v, (x, y) in pos.items():
        f, s, w = fills.get(v, ("#ffffff", "#bbbbbb", 1.3))
        out.append(f'<circle cx="{x}" cy="{y}" r="{r}" fill="{f}" stroke="{s}" '
                   f'stroke-width="{w}"/>')
        out.append(f'<text x="{x}" y="{y + 5}" font-size="13" fill="#222" '
                   f'text-anchor="middle">{v}</text>')
    for x, y, txt, col, anch, size in (labels or []):
        out.append(f'<text x="{x}" y="{y}" font-size="{size}" fill="{col}" '
                   f'text-anchor="{anch}">{txt}</text>')


def rounds_and_lanes(out, x0, dx, y0, dy, nrounds, procs, leadfn, byz=None):
    for r in range(nrounds):
        x = x0 + dx * r
        out.append(f'<text x="{x}" y="{y0 - 62}" font-size="14" fill="#555" '
                   f'text-anchor="middle">round {r}</text>')
        ls = leadfn(r)
        if ls is not None:
            out.append(f'<text x="{x}" y="{y0 - 44}" font-size="11" fill="{LEAD}" '
                       f'text-anchor="middle">leaders {ls}</text>')
    for i, p in enumerate(procs):
        col = BYZ if p == byz else "#999"
        note = " (faulty)" if p == byz else ""
        out.append(f'<text x="{x0 - 108}" y="{y0 + dy * i + 5}" font-size="12" '
                   f'fill="{col}">p{p}{note}</text>')


def skip():
    """Committed and skipped at once, by equivocation at the round above."""
    W, H = 1100, 660
    X0, DX, Y0, DY, R = 280, 420, 230, 82, 20
    out = head(W, H, "One vertex, committed and skipped at the same time",
               "The quorum clause counts processes; the skip clause counts vertices. "
               "An equivocator's spare vertices count only for the second.")
    pos = {0: (X0, Y0), 1: (X0, Y0 + DY), 2: (X0, Y0 + 2 * DY), 3: (X0, Y0 + 3 * DY),
           4: (X0 + DX, Y0 - 46), 5: (X0 + DX, Y0), 6: (X0 + DX, Y0 + 46),
           7: (X0 + DX, Y0 + DY), 8: (X0 + DX, Y0 + 2 * DY), 9: (X0 + DX, Y0 + 3 * DY)}
    refs = {4: [0, 1, 2], 7: [0, 1, 2], 8: [0, 1, 2],
            5: [1, 2, 3], 6: [1, 2, 3], 9: [1, 2, 3]}
    for r in range(2):
        out.append(f'<text x="{X0 + DX * r}" y="{Y0 - 118}" font-size="14" fill="#555" '
                   f'text-anchor="middle">round {r}</text>')
    for i, p in enumerate([0, 1, 2, 3]):
        col = BYZ if p == 0 else "#999"
        note = " (faulty)" if p == 0 else ""
        out.append(f'<text x="{X0 - 110}" y="{Y0 + DY * i + 5}" font-size="12" '
                   f'fill="{col}">p{p}{note}</text>')
    out.append(f'<rect x="{X0 + DX - R - 16}" y="{Y0 - 46 - R - 12}" '
               f'width="{2 * R + 32}" height="{92 + 2 * R + 24}" rx="12" fill="#fdf1f1" '
               f'stroke="{BYZ}" stroke-width="1.2" stroke-dasharray="5,4"/>')
    out.append(f'<text x="{X0 + DX}" y="{Y0 - 46 - R - 22}" font-size="11" fill="{BYZ}" '
               f'text-anchor="middle">process 0 issues three vertices here</text>')
    special = [((4, 0), OK), ((7, 0), OK), ((8, 0), OK)]
    fills = {0: (DEAD, BYZ, 2.6), 4: ("#ffffff", BYZ, 2.2), 5: ("#ffffff", BYZ, 2.2),
             6: ("#ffffff", BYZ, 2.2)}
    labels = [
        (X0 + DX + R + 36, Y0 - 42, "points to 0", OK, "start", 12),
        (X0 + DX + R + 36, Y0 + 4, "does not", BYZ, "start", 12),
        (X0 + DX + R + 36, Y0 + 50, "does not", BYZ, "start", 12),
        (X0 + DX + R + 36, Y0 + DY + 5, "points to 0", OK, "start", 12),
        (X0 + DX + R + 36, Y0 + 2 * DY + 5, "points to 0", OK, "start", 12),
        (X0 + DX + R + 36, Y0 + 3 * DY + 5, "does not", BYZ, "start", 12),
        (X0, Y0 - R - 62, "the vertex in question", "#111", "middle", 12),
    ]
    draw(out, pos, refs, R, special, fills, labels)
    rows = [
        (OK, "Quorum: processes {0, 1, 2} have a pointing vertex — three of four, "
             "so 2f + 1. The clause holds."),
        (BYZ, "Skip: vertices 5, 6 and 9 carry no edge to it — three vertices, "
              "so 2f + 1. The clause holds too."),
        ("#111", "Counting the skip by process instead gives {3} alone, one of four, "
                 "and the two clauses stop competing."),
    ]
    for n, (col, txt) in enumerate(rows):
        y = H - 116 + n * 24
        out.append(f'<line x1="28" y1="{y - 4}" x2="66" y2="{y - 4}" stroke="{col}" '
                   f'stroke-width="2.6"/>')
        out.append(f'<text x="78" y="{y}" font-size="13" fill="#111">{txt}</text>')
    out.append(f'<text x="28" y="{H - 26}" font-size="13" fill="#111">'
               f'So one process may commit the slot while another skips it, and the '
               f'rule sanctions both. A round holds n vertices only while nobody '
               f'equivocates.</text>')
    out.append('</svg>')
    (FIGS / "minnow-skip.svg").write_text("\n".join(out) + "\n")
    return "minnow-skip.svg"


def deadlock():
    """The dead zone, sustained every other round."""
    W, H = 1240, 640
    X0, DX, Y0, DY, R = 220, 168, 186, 74, 19
    out = head(W, H, "A DAG in which crs* commits nothing, ever",
               "Process 0 sends each of its vertices to process 1 alone. Two "
               "processes then point to it: too few to commit, too many to skip.")
    pos, refs = {}, {}
    for i in range(24):
        r, p = i // 4, i % 4
        pos[i] = (X0 + DX * r, Y0 + DY * p)
        if r == 0:
            refs[i] = []
        else:
            base = 4 * (r - 1)
            refs[i] = [base, base + 1, base + 2, base + 3] if p < 2 \
                else [base + 1, base + 2, base + 3]
    rounds_and_lanes(out, X0, DX, Y0, DY, 6, [0, 1, 2, 3],
                     lambda r: f"({2 * r % 4},{r}) then ({(2 * r + 1) % 4},{r})", byz=0)
    dead = [0, 8, 16]
    special = [((4 * r + 4, 4 * r), BYZ) for r in range(5)] + \
              [((4 * r + 5, 4 * r), BYZ) for r in range(5)]
    fills = {}
    for i in range(24):
        if i in dead:
            fills[i] = (DEAD, BYZ, 3.0)
        elif i % 4 == 0:
            fills[i] = (DEAD, BYZ, 1.6)
    for k in range(10):
        v = {0: 0, 1: 1, 2: 6, 3: 7, 4: 8, 5: 9, 6: 14, 7: 15, 8: 16, 9: 17}[k]
        x, y = pos[v]
        out.append(f'<circle cx="{x}" cy="{y}" r="{R + 5}" fill="none" stroke="{LEAD}" '
                   f'stroke-width="1.6"/>')
    labels = [(X0 + DX * k, Y0 + R + 30, "2 pointers — dead", BYZ, "middle", 11)
              for k in (0, 2, 4)]
    draw(out, pos, refs, R, special, fills, labels)
    out.append(f'<circle cx="40" cy="{H - 146}" r="9" fill="none" stroke="{LEAD}" '
               f'stroke-width="1.6"/>')
    out.append(f'<text x="60" y="{H - 142}" font-size="13" fill="#111">'
               f'a leader slot under round robin, two a round</text>')
    tail = [
        "Every vertex of process 0 is pointed to by exactly two processes: itself and "
        "process 1, the only one it sent to. Committing needs three, and",
        "skipping needs three non-pointers, of which there are two. So the slot is "
        "neither, and no later vertex can change the count — the round is full.",
        "Round robin then does the rest. The other leader of the same round is "
        "concurrent with the dead slot, so the causal-past escape is unavailable;",
        "and the next round's leaders are processes 2 and 3, the two that never "
        "received the vertex. Only from two rounds up does it enter every causal",
        "past, and by then process 0 leads again. All ten leaders below are checked "
        "individually: not one of them commits.",
    ]
    for n, txt in enumerate(tail):
        out.append(f'<text x="24" y="{H - 112 + n * 20}" font-size="13" '
                   f'fill="#111">{txt}</text>')
    out.append('</svg>')
    (FIGS / "minnow-deadlock.svg").write_text("\n".join(out) + "\n")
    return "minnow-deadlock.svg"


def main():
    FIGS.mkdir(parents=True, exist_ok=True)
    for f in (skip(), deadlock()):
        print(f"docs/figures/{f}")


if __name__ == "__main__":
    main()
