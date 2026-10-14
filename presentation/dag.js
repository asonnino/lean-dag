// lean-dag presentation — figures.
//
// Three kinds of figure, each a <figure> holding a
// <script type="application/json"> spec:
//   figure.dag      the blocks of a Lean witness, from window.WITNESSES
//                   (presentation/witnesses.js, generated from LeanDagTest)
//   figure.chart    a line or bar chart from numbers in the spec
//   figure.diagram  boxes and labelled arrows on a grid
// Any element of a spec may carry "step": n (shown from step n of the slide
// on) and "until": n (hidden from step n on); deck.js applies both. All
// colours and fonts come from theme.css.
//
// DAG spec:
//   w          witness key in window.WITNESSES (required)
//   rounds     [lo, hi]    rounds drawn (default: all)
//   only, hide [ids]       draw only / omit these blocks
//   byz        [v]         Byzantine validators (row shaded and tagged)
//   crashed    {v: r}      validator v stops after round r (cross, tag)
//   labels     bool        show block ids (default true)
//   edges      "all" | "none"   every reference drawn faintly (default "all")
//   strong     [{from: [ids], to: [ids]?, step}]  references drawn with arrows
//   paths      [{ids: [a, b, c], step}]  consecutive pairs drawn as a path
//   claims     [{from, to, step}]        dotted claim arrows (Bluestreak)
//   marks      [{ids, cls, step}]        block classes: leader vote cert
//              blame anchor fill dim evidence twin
//   tags       [{id, text, step}]        a short label above a block
//   brackets   [{ids, text, kind, side, step}] a bracket beside blocks of
//                                        one round, labelled with a count;
//                                        side "right" (default) or "left"
//   badges     [{r, text, kind, step, row, at}]  verdict under round r;
//                                        "at": a block id to connect to
//   cut        {r, step}                 dashed horizon before round r
//   hulls      [{ids, step}]             shaded region behind blocks
//   roundNames {r: "label"}              custom round labels
//   rowOrder   [v]                       rows drawn, in order (default 0..n-1);
//                                        validators left out are not drawn
//   colW       number                    column width (default from rounds)
//   tags[].below  true                   place a tag below its block
//   appear     [{ids, step}]             blocks drawn only from that step on
//   size       "xs" | "s" | "m" | "ml" | "l"   maximum figure height
//   absent     [{r, v, text, step}]      dashed outline in the cell of round r,
//                                        validator v: a block not in the witness
// Stepped marks accumulate: at step k a block shows every mark in force.
(function () {
  "use strict";
  const NS = "http://www.w3.org/2000/svg";
  let uid = 0;

  function el(tag, attrs, parent) {
    const e = document.createElementNS(NS, tag);
    for (const k in attrs) if (attrs[k] !== undefined) e.setAttribute(k, attrs[k]);
    if (parent) parent.appendChild(e);
    return e;
  }

  function text(parent, x, y, s, attrs) {
    const t = el("text", Object.assign({ x, y }, attrs || {}), parent);
    const lines = String(s).split("\n");
    if (lines.length === 1) { t.textContent = s; return t; }
    const lh = (attrs && attrs.lh) || 1.15;
    lines.forEach((ln, i) => {
      const sp = el("tspan", { x, dy: i === 0 ? `${-(lines.length - 1) * lh / 2}em` : `${lh}em` }, t);
      sp.textContent = ln;
    });
    return t;
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

  // Arrowhead markers, with ids unique in the document.
  function markers(svg, kinds) {
    const defs = el("defs", {}, svg);
    const ids = {};
    kinds.forEach((k) => {
      const id = `arrow-${k}-${++uid}`;
      ids[k] = id;
      const m = el("marker", { id, viewBox: "0 0 10 10", refX: 9, refY: 5, markerWidth: 7, markerHeight: 7, orient: "auto-start-reverse", markerUnits: "userSpaceOnUse" }, defs);
      el("path", { class: `arrowhead ${k}`, d: "M 0 1 L 9 5 L 0 9 z" }, m);
    });
    return ids;
  }

  function label(fig, svg) {
    const cap = fig.querySelector("figcaption, .caption");
    if (cap) svg.setAttribute("aria-label", cap.textContent.trim().replace(/\s+/g, " "));
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
    const rowOrder = spec.rowOrder || [...Array(n).keys()];
    const rowOf = new Map(rowOrder.map((v, i) => [v, i]));
    blocks = blocks.filter((b) => rowOf.has(b.v));
    const byId = new Map(blocks.map((b) => [b.id, b]));
    const rows = rowOrder.length;
    const cols = hi - lo + 1;
    const colW = spec.colW || Math.max(66, Math.min(112, 760 / cols));
    const rowH = rows > 6 ? Math.max(36, 340 / rows) : 58;
    const bw = Math.min(40, colW * 0.46), bh = Math.min(30, rowH * 0.62);
    const tagged = (spec.byz || []).length || Object.keys(spec.crashed || {}).length;
    const left = tagged ? 70 : 46, top = 30 + ((spec.claims || []).length ? 22 : 0);
    // Room for the label of a bracket on the right of the last round.
    const lastIds = new Set(blocks.filter((b) => b.r === hi).map((b) => b.id));
    const tail = Math.max(0, ...(spec.brackets || [])
      .filter((br) => (br.side || "right") === "right" && br.ids.some((i) => lastIds.has(i)))
      .map((br) => 7.8 * String(br.text).length + 32 - (colW - bw) / 2));
    const width = left + cols * colW + 12 + tail;
    const badgeRows = Math.max(0, ...(spec.badges || []).map((b) => (b.row || 0) + 1));
    const tagsBelow = (spec.tags || []).some((t) => t.below) ? 12 : 0;
    const height = top + rows * rowH + 12 + tagsBelow + badgeRows * 30;

    // Blocks of one validator in one round (twins) share a cell; offset them.
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
      const dx = m > 1 ? (j - (m - 1) / 2) * (bw * (m > 2 ? 0.45 : 0.62)) : 0;
      const dy = m > 1 ? (j - (m - 1) / 2) * (bh * (m > 2 ? 0.55 : 0.82)) : 0;
      pos.set(b.id, {
        x: left + (b.r - lo) * colW + colW / 2 + dx,
        y: top + rowOf.get(b.v) * rowH + rowH / 2 + dy,
      });
    });
    const colX = (r) => left + (r - lo) * colW;

    const svg = el("svg", { class: "dag" + (spec.size ? ` size-${spec.size}` : ""), viewBox: `0 0 ${width} ${height}`, role: "img" });
    const arrow = markers(svg, ["strong", "path", "claim"]);
    const appearStep = new Map();
    (spec.appear || []).forEach((a) => a.ids.forEach((i) => appearStep.set(i, a.step)));
    const edgeStep = (b, c) => Math.max(appearStep.get(b) || 0, appearStep.get(c) || 0) || undefined;
    const gGrid = el("g", {}, svg), gHull = el("g", {}, svg), gEdges = el("g", {}, svg);
    const gStrong = el("g", {}, svg), gBlocks = el("g", {}, svg), gTop = el("g", {}, svg);

    // Round bands and labels.
    for (let r = lo; r <= hi; r++) {
      if ((r - lo) % 2 === 1) el("rect", { class: "round-band", x: colX(r), y: top - 4, width: colW, height: rows * rowH + 8 }, gGrid);
      const name = (spec.roundNames && spec.roundNames[r] !== undefined) ? spec.roundNames[r] : `round ${r}`;
      text(gGrid, colX(r) + colW / 2, 14, name, { class: "round-label", "text-anchor": "middle" });
    }
    // Validator rows, with tags for Byzantine and crashed validators.
    rowOrder.forEach((v, i) => {
      const y = top + i * rowH;
      const byz = (spec.byz || []).includes(v);
      const crashed = spec.crashed && spec.crashed[v] !== undefined;
      if (byz) el("rect", { class: "row-byz", x: left - 4, y: y + 1, width: cols * colW + 8, height: rowH - 2, rx: 4 }, gGrid);
      text(gGrid, 4, y + rowH / 2 - (byz || crashed ? 6 : 0), `v${v}`, { class: "row-label", "dominant-baseline": "central" });
      if (byz) text(gGrid, 4, y + rowH / 2 + 9, "Byzantine", { class: "row-tag byz", "dominant-baseline": "central" });
      else if (crashed) text(gGrid, 4, y + rowH / 2 + 9, "crashed", { class: "row-tag crash", "dominant-baseline": "central" });
    });
    for (const v in spec.crashed || {}) {
      const r = spec.crashed[v];
      const x = Math.max(left + 8, colX(r + 1) + (r < lo ? 8 : 0)), y = top + rowOf.get(+v) * rowH + rowH / 2;
      const g = el("g", { class: "crash-mark" }, gGrid);
      el("line", { x1: x - 6, y1: y - 6, x2: x + 6, y2: y + 6 }, g);
      el("line", { x1: x - 6, y1: y + 6, x2: x + 6, y2: y - 6 }, g);
    }

    // History regions: one rounded rectangle per round spanning its blocks.
    (spec.hulls || []).forEach((h) => {
      const byRound = new Map();
      h.ids.filter((i) => pos.has(i)).forEach((i) => {
        const r = byId.get(i).r;
        if (!byRound.has(r)) byRound.set(r, []);
        byRound.get(r).push(pos.get(i));
      });
      byRound.forEach((ps) => {
        const pad = 8;
        const x0 = Math.min(...ps.map((p) => p.x)) - bw / 2 - pad, x1 = Math.max(...ps.map((p) => p.x)) + bw / 2 + pad;
        const y0 = Math.min(...ps.map((p) => p.y)) - bh / 2 - pad, y1 = Math.max(...ps.map((p) => p.y)) + bh / 2 + pad;
        stepAttr(el("rect", { class: "hull", x: x0, y: y0, width: x1 - x0, height: y1 - y0, rx: 12 }, gHull), h.step, h.until);
      });
    });

    // A reference from b to c: a curve from b's left side to c's right side.
    const curve = (b, c) => {
      const p = pos.get(b), q = pos.get(c);
      if (!p || !q) return null;
      const x1 = p.x - bw / 2, x2 = q.x + bw / 2;
      const k = Math.max(10, (x1 - x2) * 0.45);
      return `M ${x1} ${p.y} C ${x1 - k} ${p.y}, ${x2 + k} ${q.y}, ${x2} ${q.y}`;
    };
    const edge = (b, c, cls, parent, marker) => {
      const d = curve(b, c);
      return d ? el("path", { class: cls, d, "marker-end": marker ? `url(#${marker})` : undefined }, parent) : null;
    };
    if ((spec.edges || "all") === "all") {
      blocks.forEach((b) => b.refs.forEach((c) => { if (byId.has(c)) stepAttr(edge(b.id, c, "edge", gEdges), edgeStep(b.id, c)); }));
    }
    (spec.strong || []).forEach((s) => {
      s.from.forEach((b) => {
        const blk = byId.get(b);
        if (!blk) return;
        blk.refs.forEach((c) => {
          if (s.to && !s.to.includes(c)) return;
          stepAttr(edge(b, c, "edge strong", gStrong, arrow.strong), Math.max(s.step || 0, edgeStep(b, c) || 0) || undefined, s.until);
        });
      });
    });
    (spec.paths || []).forEach((p) => {
      for (let i = 0; i + 1 < p.ids.length; i++) stepAttr(edge(p.ids[i], p.ids[i + 1], "edge path", gStrong, arrow.path), p.step, p.until);
    });
    (spec.claims || []).forEach((c) => {
      const p = pos.get(c.from), q = pos.get(c.to);
      if (!p || !q) return;
      const lift = rowH * 0.9;
      const d = `M ${p.x} ${p.y - bh / 2} C ${p.x} ${p.y - bh / 2 - lift}, ${q.x} ${q.y - bh / 2 - lift}, ${q.x} ${q.y - bh / 2 - 1}`;
      stepAttr(el("path", { class: "edge claim", d, "marker-end": `url(#${arrow.claim})` }, gStrong), c.step, c.until);
    });

    // Blocks, one drawing per interval in which a block's marks are constant.
    const marks = spec.marks || [];
    const drawBlock = (b, classes, parent, step, until) => {
      const p = pos.get(b.id);
      const g = el("g", { class: ["block", ...classes].join(" ") }, parent);
      el("rect", { x: p.x - bw / 2, y: p.y - bh / 2, width: bw, height: bh, rx: 6 }, g);
      if (spec.labels !== false) el("text", { x: p.x, y: p.y + 0.5 }, g).textContent = b.id;
      return stepAttr(g, step, until);
    };
    blocks.forEach((b) => {
      const mine = marks.filter((m) => m.ids.includes(b.id));
      const points = [...new Set([0, ...mine.flatMap((m) => [m.step || 0, m.until || 0])])].sort((x, y) => x - y);
      points.forEach((k, idx) => {
        const cls = mine.filter((m) => (m.step || 0) <= k && !(m.until && m.until <= k)).map((m) => m.cls);
        const from = Math.max(k, appearStep.get(b.id) || 0) || undefined;
        drawBlock(b, cls, idx === 0 ? gBlocks : gTop, from, points[idx + 1]);
      });
    });

    // Outlines of blocks that the witness does not contain.
    (spec.absent || []).forEach((a) => {
      if (!rowOf.has(a.v) || a.r < lo || a.r > hi) return;
      const x = left + (a.r - lo) * colW + colW / 2, y = top + rowOf.get(a.v) * rowH + rowH / 2;
      const g = el("g", { class: "absent" }, gTop);
      el("rect", { x: x - bw / 2, y: y - bh / 2, width: bw, height: bh, rx: 6 }, g);
      el("text", { x, y: y + 0.5 }, g).textContent = "?";
      if (a.text) text(g, x, y + bh / 2 + 13, a.text, { class: "absent-label" });
      stepAttr(g, a.step, a.until);
    });

    // Tags above blocks.
    (spec.tags || []).forEach((t) => {
      const p = pos.get(t.id);
      if (!p) return;
      const w = 8 * String(t.text).length + 14;
      const g = el("g", { class: `tag ${t.kind || ""}` }, gTop);
      const ty = t.below ? p.y + bh / 2 + 3 : p.y - bh / 2 - 21;
      el("rect", { x: p.x - w / 2, y: ty, width: w, height: 18, rx: 9 }, g);
      text(g, p.x, ty + 9.5, t.text, { "text-anchor": "middle", "dominant-baseline": "central" });
      stepAttr(g, t.step, t.until);
    });

    // Brackets: the vertical extent of some blocks of one round, with a count.
    (spec.brackets || []).forEach((br) => {
      const ps = br.ids.filter((i) => pos.has(i)).map((i) => pos.get(i));
      if (!ps.length) return;
      const leftSide = br.side === "left";
      const y0 = Math.min(...ps.map((p) => p.y)) - bh / 2, y1 = Math.max(...ps.map((p) => p.y)) + bh / 2;
      const g = el("g", { class: `bracket ${br.kind || ""}` }, gTop);
      const w = 7.8 * String(br.text).length + 14;
      const ym = (y0 + y1) / 2;
      if (leftSide) {
        const x = Math.min(...ps.map((p) => p.x)) - bw / 2 - 5;
        el("path", { d: `M ${x} ${y0} h -5 V ${y1} h 5` }, g);
        el("rect", { x: x - 8 - w, y: ym - 10, width: w, height: 20, rx: 4 }, g);
        text(g, x - 8 - w + 6, ym, br.text, { "dominant-baseline": "central" });
      } else {
        const x = Math.max(...ps.map((p) => p.x)) + bw / 2 + 5;
        el("path", { d: `M ${x} ${y0} h 5 V ${y1} h -5` }, g);
        el("rect", { x: x + 8, y: ym - 10, width: w, height: 20, rx: 4 }, g);
        text(g, x + 14, ym, br.text, { "dominant-baseline": "central" });
      }
      stepAttr(g, br.step, br.until);
    });

    // Horizon.
    if (spec.cut) {
      const x = colX(spec.cut.r);
      const g = stepAttr(el("g", { class: "cut" }, gTop), spec.cut.step);
      el("line", { class: "cut-line", x1: x, y1: top - 4, x2: x, y2: top + rows * rowH + 6 }, g);
      text(g, x + 4, top + rows * rowH + 6, spec.cut.text || "horizon", { class: "cut-label", "dominant-baseline": "hanging" });
    }

    // Verdict badges, optionally connected to a block.
    (spec.badges || []).forEach((bd) => {
      const x = colX(bd.r) + colW / 2;
      const y = top + rows * rowH + 12 + tagsBelow + (bd.row || 0) * 30;
      const w = Math.max(colW - 10, 8.2 * bd.text.length + 18);
      const g = el("g", { class: `badge ${bd.kind || "note"}` }, gTop);
      if (bd.at !== undefined && pos.has(bd.at)) {
        // Leave the block sideways into the gap left of its column, run down
        // the gap, and enter the badge from above: no other block is crossed.
        const p = pos.get(bd.at);
        const gx = p.x - colW / 2 + 3 + 5 * (bd.row || 0);
        el("path", { class: "badge-link", d: `M ${p.x - bw / 2} ${p.y} H ${gx} V ${y - 6} H ${x} V ${y}` }, g);
      }
      el("rect", { x: x - w / 2, y, width: w, height: 24, rx: 12 }, g);
      text(g, x, y + 12.5, bd.text, { "dominant-baseline": "central" });
      stepAttr(g, bd.step, bd.until);
    });

    label(fig, svg);
    fig.insertBefore(svg, fig.firstChild);
  }

  // ---------- Charts ----------
  //   type "lines": {xs, series: [{name, ys, step, dashed, color, dy, values}],
  //                  xlabel, ylabel, yticks, ymin, ymax,
  //                  hlines: [{y, text, step}]}   dashed reference lines
  //   type "bars":  {groups: [{label, bars: [{label, value, alt, step}]}], max, ylabel}

  function drawChart(fig) {
    const spec = readSpec(fig);
    const W = 640, H = 360, L = 64, R = 150, T = 18, B = 52;
    const svg = el("svg", { class: "chart" + (spec.size ? ` size-${spec.size}` : ""), viewBox: `0 0 ${W} ${H}`, role: "img" });
    const pw = W - L - R, ph = H - T - B;
    if (spec.type === "lines") {
      const xs = spec.xs;
      const ys = spec.series.flatMap((s) => s.ys).concat((spec.hlines || []).map((h) => h.y));
      const ymax = spec.ymax || Math.max(...ys), ymin = spec.ymin || 0;
      const sx = (i) => L + (i / (xs.length - 1)) * pw;
      const sy = (v) => T + ph - ((v - ymin) / (ymax - ymin)) * ph;
      (spec.yticks || []).forEach((v) => {
        el("line", { class: "grid", x1: L, y1: sy(v), x2: L + pw, y2: sy(v) }, svg);
        text(svg, L - 8, sy(v), v, { class: "tick", "text-anchor": "end", "dominant-baseline": "central" });
      });
      el("line", { class: "axis", x1: L, y1: T + ph, x2: L + pw, y2: T + ph }, svg);
      el("line", { class: "axis", x1: L, y1: T, x2: L, y2: T + ph }, svg);
      xs.forEach((x, i) => text(svg, sx(i), T + ph + 20, x, { class: "tick", "text-anchor": "middle" }));
      if (spec.xlabel) text(svg, L + pw / 2, H - 6, spec.xlabel, { class: "axis-title", "text-anchor": "middle" });
      if (spec.ylabel) text(svg, 16, T + ph / 2, spec.ylabel, { class: "axis-title", transform: `rotate(-90 16 ${T + ph / 2})`, "text-anchor": "middle" });
      (spec.hlines || []).forEach((h) => {
        const g = stepAttr(el("g", { class: "hline" }, svg), h.step, h.until);
        el("line", { x1: L, y1: sy(h.y), x2: L + pw, y2: sy(h.y) }, g);
        text(g, L + pw + 8, sy(h.y), h.text, { "dominant-baseline": "central" });
      });
      spec.series.forEach((s, k) => {
        const g = stepAttr(el("g", { class: `s${s.color !== undefined ? s.color : k % 4}` }, svg), s.step, s.until);
        const pts = s.ys.map((y, i) => `${sx(i)},${sy(y)}`).join(" ");
        el("polyline", { class: "series", points: pts, "stroke-dasharray": s.dashed ? "6 4" : undefined }, g);
        s.ys.forEach((y, i) => {
          el("circle", { cx: sx(i), cy: sy(y), r: 4 }, g);
          if (s.values) text(g, sx(i), sy(y) - 10, y, { class: "value", "text-anchor": "middle" });
        });
        text(g, sx(s.ys.length - 1) + 10, sy(s.ys[s.ys.length - 1]) + (s.dy || 0), s.name, { class: "label", "dominant-baseline": "central" });
      });
    } else if (spec.type === "bars") {
      const groups = spec.groups;
      const max = spec.max || Math.max(...groups.flatMap((g) => g.bars.map((b) => b.value)));
      const gw = pw / groups.length;
      el("line", { class: "axis", x1: L, y1: T + ph, x2: L + pw, y2: T + ph }, svg);
      if (spec.ylabel) text(svg, 16, T + ph / 2, spec.ylabel, { class: "axis-title", transform: `rotate(-90 16 ${T + ph / 2})`, "text-anchor": "middle" });
      groups.forEach((g, gi) => {
        const bwd = (gw * 0.7) / g.bars.length;
        g.bars.forEach((b, bi) => {
          const x = L + gi * gw + gw * 0.15 + bi * bwd;
          const h = (b.value / max) * ph;
          const gg = stepAttr(el("g", {}, svg), b.step, b.until);
          el("rect", { class: b.alt ? "bar alt" : "bar", x, y: T + ph - h, width: bwd - 8, height: h, rx: 3 }, gg);
          text(gg, x + (bwd - 8) / 2, T + ph - h - 8, b.label, { class: "value", "text-anchor": "middle" });
          if (b.name) text(gg, x + (bwd - 8) / 2, T + ph + 18, b.name, { class: "tick", "text-anchor": "middle" });
        });
        text(svg, L + gi * gw + gw / 2, T + ph + (g.bars.some((b) => b.name) ? 38 : 20), g.label, { class: "axis-title", "text-anchor": "middle" });
      });
    }
    label(fig, svg);
    fig.insertBefore(svg, fig.firstChild);
  }

  // ---------- Diagrams ----------
  //   {w, h,
  //    nodes:  [{id, x, y, w, h, text, sub, cls, step}]    x, y: top-left corner;
  //            cls: accent | leader | muted | dashed | ok | bad | plain
  //    edges:  [{from, to, label, cls, route, step}]      route: "straight" |
  //            "h" (horizontal first) | "v" (vertical first); cls: strong |
  //            dashed | accent | ok | bad
  //    groups: [{x, y, w, h, label, cls, step}]          background regions
  //    texts:  [{x, y, text, cls, anchor, step}]
//    lines:  [{x1, y1, x2, y2, label, cls, step}]}      cls: dashed | bad | ok | accent
  // Text may contain "\n" for a second line. Coordinates are in viewBox units.

  function drawDiagram(fig) {
    const spec = readSpec(fig);
    const svg = el("svg", { class: "diagram" + (spec.size ? ` size-${spec.size}` : ""), viewBox: `0 0 ${spec.w} ${spec.h}`, role: "img" });
    const arrow = markers(svg, ["edge", "accent", "ok", "bad"]);
    const gGroups = el("g", {}, svg), gEdges = el("g", {}, svg), gNodes = el("g", {}, svg), gTexts = el("g", {}, svg);
    const nodes = new Map((spec.nodes || []).map((nd) => [nd.id, Object.assign({ w: 140, h: 44 }, nd)]));

    (spec.groups || []).forEach((gr) => {
      const g = stepAttr(el("g", { class: `group ${gr.cls || ""}` }, gGroups), gr.step, gr.until);
      el("rect", { x: gr.x, y: gr.y, width: gr.w, height: gr.h, rx: 10 }, g);
      if (gr.label) text(g, gr.x + 10, gr.y + 16, gr.label, { class: "group-label" });
    });

    nodes.forEach((nd) => {
      const g = stepAttr(el("g", { class: `node ${nd.cls || ""}` }, gNodes), nd.step, nd.until);
      el("rect", { x: nd.x, y: nd.y, width: nd.w, height: nd.h, rx: 8 }, g);
      const cx = nd.x + nd.w / 2, cy = nd.y + nd.h / 2;
      if (nd.sub) {
        text(g, cx, cy - 9, nd.text, { class: "node-text", "text-anchor": "middle", "dominant-baseline": "central" });
        text(g, cx, cy + 11, nd.sub, { class: "node-sub", "text-anchor": "middle", "dominant-baseline": "central" });
      } else {
        text(g, cx, cy, nd.text, { class: "node-text", "text-anchor": "middle", "dominant-baseline": "central" });
      }
    });

    // Attachment point on a node's border towards a target point.
    const port = (nd, tx, ty, side) => {
      const cx = nd.x + nd.w / 2, cy = nd.y + nd.h / 2;
      const s = side || (Math.abs(tx - cx) * nd.h > Math.abs(ty - cy) * nd.w ? (tx > cx ? "r" : "l") : (ty > cy ? "b" : "t"));
      return s === "r" ? [nd.x + nd.w, cy, s] : s === "l" ? [nd.x, cy, s] : s === "b" ? [cx, nd.y + nd.h, s] : [cx, nd.y, s];
    };
    (spec.edges || []).forEach((e) => {
      const a = nodes.get(e.from), b = nodes.get(e.to);
      if (!a || !b) return;
      const bc = [b.x + b.w / 2, b.y + b.h / 2], ac = [a.x + a.w / 2, a.y + a.h / 2];
      const [x1, y1] = port(a, bc[0], bc[1], e.fromSide);
      const [x2, y2] = port(b, ac[0], ac[1], e.toSide);
      let d, lx, ly;
      if (e.route === "h") { d = `M ${x1} ${y1} H ${x2} V ${y2}`; lx = (x1 + x2) / 2; ly = y1; }
      else if (e.route === "v") { d = `M ${x1} ${y1} V ${y2} H ${x2}`; lx = x1; ly = (y1 + y2) / 2; }
      else { d = `M ${x1} ${y1} L ${x2} ${y2}`; lx = (x1 + x2) / 2; ly = (y1 + y2) / 2; }
      const kind = ["accent", "ok", "bad"].find((k) => (e.cls || "").includes(k)) || "edge";
      const g = stepAttr(el("g", { class: `link ${e.cls || ""}` }, gEdges), e.step, e.until);
      el("path", { d, "marker-end": e.noArrow ? undefined : `url(#${arrow[kind]})` }, g);
      if (e.label) {
        const t = text(g, lx + (e.dx || 0), ly + (e.dy !== undefined ? e.dy : -8), e.label, { class: "link-label", "text-anchor": "middle" });
        t.setAttribute("paint-order", "stroke");
      }
    });

    (spec.lines || []).forEach((ln) => {
      const g = stepAttr(el("g", { class: `rule ${ln.cls || ""}` }, gGroups), ln.step, ln.until);
      el("line", { x1: ln.x1, y1: ln.y1, x2: ln.x2, y2: ln.y2 }, g);
      if (ln.label) text(g, ln.x1 + 4, Math.min(ln.y1, ln.y2) - 6, ln.label, { class: "rule-label" });
    });

    (spec.texts || []).forEach((t) => {
      stepAttr(text(gTexts, t.x, t.y, t.text, { class: `note ${t.cls || ""}`, "text-anchor": t.anchor || "start", "dominant-baseline": "central" }), t.step, t.until);
    });

    label(fig, svg);
    fig.insertBefore(svg, fig.firstChild);
  }

  document.querySelectorAll("figure.dag").forEach(drawDag);
  document.querySelectorAll("figure.chart").forEach(drawChart);
  document.querySelectorAll("figure.diagram").forEach(drawDiagram);
})();
