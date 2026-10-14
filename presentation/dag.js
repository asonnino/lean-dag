// lean-dag presentation — figures.
//
// <figure class="dag"> and <figure class="chart"> each hold a
// <script type="application/json"> spec. DAG figures draw the blocks of a
// Lean witness from window.WITNESSES (presentation/witnesses.js, generated
// from LeanDagTest). Every element may carry "step": n, and is then shown
// from step n of the slide on (deck.js). All colours come from theme.css.
//
// DAG spec fields:
//   w          witness key in window.WITNESSES (required)
//   rounds     [lo, hi]    rounds drawn (default: all)
//   only       [ids]       draw only these blocks
//   hide       [ids]       do not draw these blocks
//   byz        [v]         Byzantine validators (row shaded)
//   crashed    {v: r}      validator v stops after round r (cross drawn)
//   labels     bool        show block ids (default true)
//   edges      "all" | "none"   draw every reference faintly (default "all")
//   strong     [{from: [ids], to: [ids]?, step}]  references drawn strongly
//   paths      [{ids: [a, b, c], step}]  consecutive pairs drawn as a path
//   claims     [{from, to, step}]        dotted claim arrows (Bluestreak)
//   marks      [{ids, cls, step}]        block classes: leader vote cert
//              blame anchor fill dim evidence twin
//   badges     [{r, text, kind, step, row}]  verdict badge under round r
//   cut        {r, step}                 dashed line before round r
//   hulls      [{ids, step}]             shaded region behind blocks
//   roundNames {r: "label"}              custom round labels
//   rowOrder   [v]                       row order (default 0..n-1)
//   appear     [{ids, step}]             blocks (and their references)
//                                        drawn only from that step on
//   size       "xs" | "s" | "m" | "l"    maximum figure height
// Marks and badges also accept "until": n, hiding them from step n on.
// Stepped marks accumulate: at step k a block shows every mark whose step
// is at most k.
(function () {
  "use strict";
  const NS = "http://www.w3.org/2000/svg";

  function el(tag, attrs, parent) {
    const e = document.createElementNS(NS, tag);
    for (const k in attrs) if (attrs[k] !== undefined) e.setAttribute(k, attrs[k]);
    if (parent) parent.appendChild(e);
    return e;
  }

  function stepAttr(e, step, until) {
    if (!e) return e;
    if (step) e.setAttribute("data-step", step);
    if (until) e.setAttribute("data-until", until);
    return e;
  }

  function readSpec(fig) {
    const s = fig.querySelector('script[type="application/json"]');
    return s ? JSON.parse(s.textContent) : {};
  }

  // ---------- DAG ----------

  function drawDag(fig) {
    const spec = readSpec(fig);
    const wit = (window.WITNESSES || {})[spec.w];
    if (!wit) { fig.insertAdjacentHTML("beforeend", `<p class="caption">missing witness ${spec.w}</p>`); return; }
    const n = wit.n;
    let blocks = wit.blocks.slice();
    const lo = spec.rounds ? spec.rounds[0] : Math.min(...blocks.map((b) => b.r));
    const hi = spec.rounds ? spec.rounds[1] : Math.max(...blocks.map((b) => b.r));
    blocks = blocks.filter((b) => b.r >= lo && b.r <= hi);
    if (spec.only) blocks = blocks.filter((b) => spec.only.includes(b.id));
    if (spec.hide) blocks = blocks.filter((b) => !spec.hide.includes(b.id));
    const byId = new Map(blocks.map((b) => [b.id, b]));

    const rowOrder = spec.rowOrder || [...Array(n).keys()];
    const rowOf = new Map(rowOrder.map((v, i) => [v, i]));
    const cols = hi - lo + 1;
    const colW = Math.max(64, Math.min(110, 760 / cols));
    const rowH = n > 6 ? Math.max(34, 330 / n) : 58;
    const bw = Math.min(40, colW * 0.46), bh = Math.min(30, rowH * 0.62);
    const left = 46, top = 26;
    const width = left + cols * colW + 10;
    const badgeRows = Math.max(1, ...(spec.badges || []).map((b) => (b.row || 0) + 1));
    const height = top + n * rowH + 18 + badgeRows * 30;

    // Twins share a cell; offset them.
    const cell = new Map();
    blocks.forEach((b) => {
      const k = `${b.r}:${b.v}`;
      if (!cell.has(k)) cell.set(k, []);
      cell.get(k).push(b.id);
    });
    const pos = new Map();
    blocks.forEach((b) => {
      const group = cell.get(`${b.r}:${b.v}`);
      const j = group.indexOf(b.id), m = group.length;
      const dx = m > 1 ? (j - (m - 1) / 2) * (bw * (m > 2 ? 0.45 : 0.6)) : 0;
      const dy = m > 1 ? (j - (m - 1) / 2) * (bh * (m > 2 ? 0.55 : 0.8)) : 0;
      pos.set(b.id, {
        x: left + (b.r - lo) * colW + colW / 2 + dx,
        y: top + rowOf.get(b.v) * rowH + rowH / 2 + dy,
      });
    });

    const svg = el("svg", { class: "dag" + (spec.size ? ` size-${spec.size}` : ""), viewBox: `0 0 ${width} ${height}`, role: "img" });
    const appearStep = new Map();
    (spec.appear || []).forEach((a) => a.ids.forEach((i) => appearStep.set(i, a.step)));
    const edgeStep = (b, c) => Math.max(appearStep.get(b) || 0, appearStep.get(c) || 0) || undefined;
    const gRows = el("g", {}, svg), gHull = el("g", {}, svg), gEdges = el("g", {}, svg);
    const gStrong = el("g", {}, svg), gBlocks = el("g", {}, svg), gTop = el("g", {}, svg);

    // Rows and labels.
    rowOrder.forEach((v, i) => {
      const y = top + i * rowH;
      if ((spec.byz || []).includes(v)) el("rect", { class: "row-byz", x: left - 4, y, width: cols * colW + 8, height: rowH }, gRows);
      const t = el("text", { class: "row-label", x: 4, y: y + rowH / 2, "dominant-baseline": "central" }, gRows);
      t.textContent = `v${v}`;
    });
    for (let r = lo; r <= hi; r++) {
      const t = el("text", { class: "round-label", x: left + (r - lo) * colW + colW / 2, y: 12, "text-anchor": "middle" }, gRows);
      t.textContent = (spec.roundNames && spec.roundNames[r] !== undefined) ? spec.roundNames[r] : `round ${r}`;
    }
    for (const v in spec.crashed || {}) {
      const r = spec.crashed[v];
      const x = left + (r - lo + 1) * colW + 6, y = top + rowOf.get(+v) * rowH + rowH / 2;
      el("line", { class: "crash-mark", x1: x - 7, y1: y - 7, x2: x + 7, y2: y + 7 }, gRows);
      el("line", { class: "crash-mark", x1: x - 7, y1: y + 7, x2: x + 7, y2: y - 7 }, gRows);
    }

    // Hulls.
    (spec.hulls || []).forEach((h) => {
      const ps = h.ids.filter((i) => pos.has(i)).map((i) => pos.get(i));
      if (!ps.length) return;
      const pad = 10;
      ps.forEach((p) => stepAttr(el("rect", { class: "hull", x: p.x - bw / 2 - pad, y: p.y - bh / 2 - pad, width: bw + 2 * pad, height: bh + 2 * pad, rx: 10 }, gHull), h.step, h.until));
    });

    // Edges: a reference from b to c is drawn from b's left side to c's right side.
    const edgeLine = (b, c, cls, parent) => {
      const p = pos.get(b), q = pos.get(c);
      if (!p || !q) return null;
      return el("line", { class: cls, x1: p.x - bw / 2, y1: p.y, x2: q.x + bw / 2, y2: q.y }, parent);
    };
    if ((spec.edges || "all") === "all") {
      blocks.forEach((b) => b.refs.forEach((c) => { if (byId.has(c)) stepAttr(edgeLine(b.id, c, "edge", gEdges), edgeStep(b.id, c)); }));
    }
    (spec.strong || []).forEach((s) => {
      s.from.forEach((b) => {
        const blk = byId.get(b);
        if (!blk) return;
        blk.refs.forEach((c) => {
          if (s.to && !s.to.includes(c)) return;
          stepAttr(edgeLine(b, c, "edge strong", gStrong), Math.max(s.step || 0, edgeStep(b, c) || 0) || undefined, s.until);
        });
      });
    });
    (spec.paths || []).forEach((p) => {
      for (let i = 0; i + 1 < p.ids.length; i++) stepAttr(edgeLine(p.ids[i], p.ids[i + 1], "edge path", gStrong), p.step, p.until);
    });
    (spec.claims || []).forEach((c) => {
      const p = pos.get(c.from), q = pos.get(c.to);
      if (!p || !q) return;
      const path = `M ${p.x - bw / 2} ${p.y} C ${p.x - colW} ${p.y - rowH}, ${q.x + colW} ${q.y - rowH}, ${q.x + bw / 2} ${q.y}`;
      stepAttr(el("path", { class: "edge claim", d: path }, gStrong), c.step, c.until);
    });

    // Blocks, with their marks. A mark with a step is drawn as an overlay
    // copy so that the block's plain form is visible before that step.
    const marks = spec.marks || [];
    const drawBlock = (b, classes, parent, step, until) => {
      const p = pos.get(b.id);
      const g = el("g", { class: ["block", ...classes].join(" ") }, parent);
      el("rect", { x: p.x - bw / 2, y: p.y - bh / 2, width: bw, height: bh, rx: 5 }, g);
      if (spec.labels !== false) el("text", { x: p.x, y: p.y }, g).textContent = b.id;
      return stepAttr(g, step, until);
    };
    blocks.forEach((b) => {
      const mine = marks.filter((m) => m.ids.includes(b.id));
      // One drawing of the block per interval in which its marks are
      // constant; each carries every mark in force there.
      const points = [...new Set([0, ...mine.flatMap((m) => [m.step || 0, m.until || 0])])].sort((x, y) => x - y);
      points.forEach((k, idx) => {
        const cls = mine.filter((m) => (m.step || 0) <= k && !(m.until && m.until <= k)).map((m) => m.cls);
        const from = Math.max(k, appearStep.get(b.id) || 0) || undefined;
        drawBlock(b, cls, idx === 0 ? gBlocks : gTop, from, points[idx + 1]);
      });
    });

    // Cut line.
    if (spec.cut) {
      const x = left + (spec.cut.r - lo) * colW;
      stepAttr(el("line", { class: "cut-line", x1: x, y1: top - 4, x2: x, y2: top + n * rowH + 4 }, gTop), spec.cut.step);
    }

    // Badges.
    (spec.badges || []).forEach((bd) => {
      const x = left + (bd.r - lo) * colW + colW / 2;
      const y = top + n * rowH + 14 + (bd.row || 0) * 30;
      const w = Math.max(colW - 8, 9 * bd.text.length + 16);
      const g = el("g", { class: `badge ${bd.kind || "note"}` }, gTop);
      el("rect", { x: x - w / 2, y, width: w, height: 24 }, g);
      el("text", { x, y: y + 12 }, g).textContent = bd.text;
      stepAttr(g, bd.step, bd.until);
    });

    fig.insertBefore(svg, fig.firstChild);
  }

  // ---------- Charts ----------
  //   type "lines": {xs: [..], series: [{name, ys: [..], step}], xlabel, ylabel}
  //   type "bars":  {groups: [{label, bars: [{label, value, alt}]}], max, ylabel}

  function drawChart(fig) {
    const spec = readSpec(fig);
    const W = 640, H = 360, L = 56, R = 140, T = 16, B = 46;
    const svg = el("svg", { class: "chart" + (spec.size ? ` size-${spec.size}` : ""), viewBox: `0 0 ${W} ${H}` });
    const pw = W - L - R, ph = H - T - B;
    if (spec.type === "lines") {
      const xs = spec.xs;
      const ys = spec.series.flatMap((s) => s.ys);
      const ymax = spec.ymax || Math.max(...ys), ymin = spec.ymin || 0;
      const sx = (i) => L + (i / (xs.length - 1)) * pw;
      const sy = (v) => T + ph - ((v - ymin) / (ymax - ymin)) * ph;
      el("line", { class: "axis", x1: L, y1: T + ph, x2: L + pw, y2: T + ph }, svg);
      el("line", { class: "axis", x1: L, y1: T, x2: L, y2: T + ph }, svg);
      xs.forEach((x, i) => { el("text", { class: "tick", x: sx(i), y: T + ph + 18, "text-anchor": "middle" }, svg).textContent = x; });
      (spec.yticks || []).forEach((v) => {
        el("line", { class: "grid", x1: L, y1: sy(v), x2: L + pw, y2: sy(v) }, svg);
        el("text", { class: "tick", x: L - 6, y: sy(v), "text-anchor": "end", "dominant-baseline": "central" }, svg).textContent = v;
      });
      if (spec.xlabel) el("text", { class: "tick", x: L + pw / 2, y: H - 6, "text-anchor": "middle" }, svg).textContent = spec.xlabel;
      if (spec.ylabel) el("text", { class: "tick", x: 14, y: T + ph / 2, transform: `rotate(-90 14 ${T + ph / 2})`, "text-anchor": "middle" }, svg).textContent = spec.ylabel;
      spec.series.forEach((s, k) => {
        const g = stepAttr(el("g", { class: `s${s.color !== undefined ? s.color : k % 4}` }, svg), s.step);
        const pts = s.ys.map((y, i) => `${sx(i)},${sy(y)}`).join(" ");
        el("polyline", { class: "series", points: pts, "stroke-dasharray": s.dashed ? "6 4" : undefined }, g);
        s.ys.forEach((y, i) => el("circle", { cx: sx(i), cy: sy(y), r: 3.5 }, g));
        el("text", { class: "label", x: sx(s.ys.length - 1) + 8, y: sy(s.ys[s.ys.length - 1]) + (s.dy || 0), "dominant-baseline": "central" }, g).textContent = s.name;
      });
    } else if (spec.type === "bars") {
      const groups = spec.groups;
      const max = spec.max || Math.max(...groups.flatMap((g) => g.bars.map((b) => b.value)));
      const gw = pw / groups.length;
      el("line", { class: "axis", x1: L, y1: T + ph, x2: L + pw, y2: T + ph }, svg);
      groups.forEach((g, gi) => {
        const bw = (gw * 0.7) / g.bars.length;
        g.bars.forEach((b, bi) => {
          const x = L + gi * gw + gw * 0.15 + bi * bw;
          const h = (b.value / max) * ph;
          const gg = stepAttr(el("g", {}, svg), b.step);
          el("rect", { class: b.alt ? "bar alt" : "bar", x, y: T + ph - h, width: bw - 6, height: h }, gg);
          el("text", { class: "label", x: x + (bw - 6) / 2, y: T + ph - h - 6, "text-anchor": "middle" }, gg).textContent = b.label;
        });
        el("text", { class: "tick", x: L + gi * gw + gw / 2, y: T + ph + 18, "text-anchor": "middle" }, svg).textContent = g.label;
      });
    }
    fig.insertBefore(svg, fig.firstChild);
  }

  document.querySelectorAll("figure.dag").forEach(drawDag);
  document.querySelectorAll("figure.chart").forEach(drawChart);
})();
