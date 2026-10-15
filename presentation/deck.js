// lean-dag presentation — navigation, steps, notes.
// Keys: → / Space / PageDown next; ← / PageUp previous; Home / End;
// N toggles speaker notes; F toggles full screen.
(function () {
  "use strict";

  const slides = Array.from(document.querySelectorAll("section.slide"));
  const progress = document.querySelector(".progress");
  let index = 0;
  let step = 0;

  // Number the content slides (part dividers are not numbered, so the
  // numbers match the outline and the cross-references) and add a footer.
  const total = slides.length;
  const content = slides.filter((s) => !s.classList.contains("part"));
  content.forEach((s, i) => {
    s.dataset.number = i + 1;
    if (s.classList.contains("title-slide")) return;
    const f = document.createElement("div");
    f.className = "footer";
    const part = s.dataset.partLabel || "";
    f.innerHTML = `<span>${part}</span><span>${i + 1} / ${content.length}</span>`;
    s.appendChild(f);
  });
  // Slide number n (as in the footer) to its position in the deck.
  const positionOf = (n) => {
    const i = slides.findIndex((s) => s.dataset.number === String(n));
    return i < 0 ? n - 1 : i;
  };

  function maxStep(s) {
    let m = 0;
    s.querySelectorAll("[data-step], [data-until]").forEach((e) => {
      m = Math.max(m, parseInt(e.dataset.step, 10) || 0, parseInt(e.dataset.until, 10) || 0);
    });
    return m;
  }

  function applySteps(s, k) {
    s.querySelectorAll("[data-step], [data-until]").forEach((e) => {
      const n = parseInt(e.dataset.step, 10) || 0;
      const u = e.dataset.until ? parseInt(e.dataset.until, 10) : Infinity;
      e.classList.toggle("step-hidden", n > k || k >= u);
    });
  }

  function fit() {
    const w = window.innerWidth, h = window.innerHeight;
    const notes = document.body.classList.contains("show-notes") ? 0.7 : 1;
    const scale = Math.min(w / 1280, (h * notes) / 720) * 0.96;
    slides.forEach((s) => {
      s.style.transform = `scale(${scale})` + (notes < 1 ? ` translateY(${-(h * 0.15) / scale}px)` : "");
    });
  }

  function show(i, k) {
    index = Math.max(0, Math.min(total - 1, i));
    const s = slides[index];
    slides.forEach((x) => x.classList.toggle("active", x === s));
    step = k === "end" ? maxStep(s) : Math.max(0, Math.min(maxStep(s), k));
    applySteps(s, step);
    if (progress) progress.style.width = `${((index + 1) / total) * 100}%`;
    const label = s.dataset.number || `p${index + 1}`;
    history.replaceState(null, "", `#${label}` + (step ? `.${step}` : ""));
  }

  function next() {
    if (step < maxStep(slides[index])) show(index, step + 1);
    else if (index < total - 1) show(index + 1, 0);
  }

  function prev() {
    if (step > 0) show(index, step - 1);
    else if (index > 0) show(index - 1, "end");
  }

  document.addEventListener("keydown", (e) => {
    if (e.metaKey || e.ctrlKey || e.altKey) return;
    switch (e.key) {
      case "ArrowRight": case " ": case "PageDown": e.preventDefault(); next(); break;
      case "ArrowLeft": case "PageUp": e.preventDefault(); prev(); break;
      case "Home": show(0, 0); break;
      case "End": show(total - 1, 0); break;
      case "n": case "N": document.body.classList.toggle("show-notes"); fit(); break;
      case "f": case "F":
        if (!document.fullscreenElement) document.documentElement.requestFullscreen();
        else document.exitFullscreen();
        break;
    }
  });

  document.addEventListener("click", (e) => {
    if (e.target.closest("a, .notes")) return;
    if (e.clientX > window.innerWidth / 3) next(); else prev();
  });

  window.addEventListener("resize", fit);
  // Links of the form href="#59" move to that slide.
  // Hashes name slides by their footer number: #59 or #59.2 (a step).
  function fromHash() {
    const h = location.hash.match(/^#(p?)(\d+)(?:\.(\d+))?/);
    if (!h) return null;
    const i = h[1] ? parseInt(h[2], 10) - 1 : positionOf(parseInt(h[2], 10));
    return [i, h[3] ? parseInt(h[3], 10) : 0];
  }
  window.addEventListener("hashchange", () => {
    const t = fromHash();
    if (t && (t[0] !== index || t[1] !== step)) show(t[0], t[1]);
  });
  // Print each slide at its final step.
  window.addEventListener("beforeprint", () => slides.forEach((s) => applySteps(s, maxStep(s))));
  window.addEventListener("afterprint", () => show(index, step));

  fit();
  const t = fromHash();
  show(t ? t[0] : 0, t ? t[1] : 0);
})();
