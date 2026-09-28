#!/usr/bin/env python3
"""Guard the arc's third claim: mechanisms reach protocols through the properties.

`docs/target-properties.md` part 2 says a rule that shows the properties
composes with each mechanism *with no further proof*. The test is not
that a mechanism never mentions a protocol — a theorem about garbage
collection over Hydrozoan must say `Hydrozoan.Decided` — but that its
**proof** never reaches a protocol theorem about verdicts except through
the properties.

So: take the dependency closure of every mechanism theorem, with the
properties layer and each protocol's conformance file as barriers, and
report the protocol theorems about verdicts that are still reachable.
Those are the bespoke protocol-to-mechanism links.

A link whose protocol has no `Banded` is not a defect of the arc: there
is nothing to route through. Those are reported separately and do not
fail the run. A link whose protocol shows the six is recorded in
`docs/bespoke-links.md` until it is routed; an unrecorded one fails.

Reads `docs/depgraph/deps.tsv`; regenerate it before trusting a run
(see the top of `scripts/audit-report.py`). Exits 1 on an unrecorded
finding, or when a recorded one has been fixed and not struck off.
"""

import collections
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

# Modules that *are* a protocol: its model, its rules, its own theorems.
PROTOCOL = (
    "LeanDag.Mysticeti.Rule", "LeanDag.Mysticeti.Liveness", "LeanDag.Common.Persistence",
    "LeanDag.Common.Support", "LeanDag.Common.Schedule", "LeanDag.Common.WaveRobin",
    "LeanDag.Common.Participation", "LeanDag.Hydrozoan.", "LeanDag.Odontoceti.",
    "LeanDag.Nemo.", "LeanDag.Hybrid.", "LeanDag.MahiMahi.",
    "LeanDag.FinWhale.", "LeanDag.BlackMarlin.", "LeanDag.OptimalHydrozoan.",
    "LeanDag.Reactive.Mysticeti", "LeanDag.Reactive.Odontoceti",
    "LeanDag.Minnow", "LeanDag.AsyncBlueBottle.",
)

# The conformance layer: where a protocol states the properties it shows.
# A mechanism reaching a protocol through one of these is going the right
# way round, so these are barriers rather than targets.
CONFORMANCE = (
    "LeanDag.Mysticeti.Properties", "LeanDag.Odontoceti.Properties",
    "LeanDag.Reactive.MysticetiProperties", "LeanDag.Hydrozoan.Properties",
    "LeanDag.Hydrozoan.Helpers.Commit", "LeanDag.Hydrozoan.Helpers.Banded",
    "LeanDag.Hydrozoan.Helpers.Carrier", "LeanDag.Hydrozoan.Helpers.Skippability",
    "LeanDag.Odontoceti.Carrier",
    "LeanDag.Nemo.Carrier", "LeanDag.Nemo.Properties",
    "LeanDag.Hybrid.Carrier", "LeanDag.Hybrid.Properties",
    "LeanDag.OptimalHydrozoan.Carrier", "LeanDag.OptimalHydrozoan.Helpers.Banded",
    "LeanDag.AsyncBlueBottle.Carrier", "LeanDag.AsyncBlueBottle.Properties",
    "LeanDag.Barnacle.Helpers.DagRule", "LeanDag.Barnacle.Helpers.Descent",
)

# The rules that show the six required properties: for these, and only
# these, a bespoke link is a gap rather than a necessity.
CONFORMING = (
    "LeanDag.Mysticeti.Rule", "LeanDag.Mysticeti.Liveness", "LeanDag.Common.Persistence",
    "LeanDag.Common.Support", "LeanDag.Common.Schedule", "LeanDag.Common.WaveRobin",
    "LeanDag.Common.Participation", "LeanDag.Hydrozoan.", "LeanDag.Odontoceti.",
    "LeanDag.Nemo.", "LeanDag.Hybrid.", "LeanDag.OptimalHydrozoan.",
    "LeanDag.Reactive.Mysticeti", "LeanDag.Reactive.Odontoceti",
    "LeanDag.AsyncBlueBottle.",
)

# Every decision relation named by a protocol rather than by a carrier
# field. `BaseRule.Decided` and `DagRule.Decided` are deliberately absent:
# a theorem over a generic rule is the thing we are aiming for.
RELATION = re.compile(
    r"^LeanDag\.(Decided|DecidedWithin"
    r"|Hydrozoan\.Decided|Odontoceti\.Decided|Odontoceti\.DecidedWithin"
    r"|Nemo\.Decided|Hybrid\.Decided|MahiMahi\.Decided"
    r"|OptimalHydrozoan\.DecidedOpt"
    r"|AsyncBlueBottle\.Decided|AsyncBlueBottle\.DecidedWithin)(\.|$)")

AUTO = ("._proof_", ".match_", "._simp_", "._eq_", "._sunfold", ".congr_simp",
        "._cstage", ".noConfusion", ".injEq", ".sizeOf_spec", "._sizeOf_",
        "._flat_ctor", ".ndrec")

# Links still to route, from `docs/bespoke-links.md`. Each entry is a
# mechanism theorem; strike one off when its proof stops reaching a
# protocol theorem about verdicts outside the properties.
RECORDED = set()

RECORDED_PATH = ROOT / "docs" / "bespoke-links.md"
RECORD_LINE = re.compile(r"^\|\s*`([A-Za-z0-9_.]+)`\s*\|")


def load_recorded():
    if not RECORDED_PATH.exists():
        return set()
    out = set()
    for line in RECORDED_PATH.read_text().splitlines():
        m = RECORD_LINE.match(line.strip())
        if m and m.group(1) != "theorem":
            out.add(m.group(1))
    return out


def main():
    deps = ROOT / "docs" / "depgraph" / "deps.tsv"
    node_mod, kind = {}, {}
    uses = collections.defaultdict(set)
    for line in deps.read_text().splitlines():
        p = line.split("\t")
        if p[0] == "NODE":
            node_mod[p[1]], kind[p[1]] = p[2], p[3]
        elif p[0] == "EDGE":
            uses[p[1]].add(p[2])

    def cls(m):
        if m.startswith("LeanDagTest"):
            return "TEST"
        if m.startswith("LeanDag.Properties"):
            return "PROPS"
        if any(m.startswith(c) for c in CONFORMANCE):
            return "CONF"
        if any(m.startswith(p) for p in PROTOCOL):
            return "PROTO"
        return "MECH"

    C = {d: cls(m) for d, m in node_mod.items()}
    real = lambda d: not any(a in d for a in AUTO)

    # A protocol theorem is "about verdicts" when its own proof or type
    # names a decision relation. Those are what a mechanism must not
    # borrow; structural facts about DAGs and committees are shared and
    # the properties never abstracted them.
    verdict = {d for d in node_mod
               if C[d] == "PROTO" and kind.get(d) == "thm" and real(d)
               and any(RELATION.match(x) for x in uses[d])}

    def borrowed(start):
        seen, stack, found = {start}, [start], set()
        while stack:
            for y in uses[stack.pop()]:
                if y in seen or C.get(y) in ("PROPS", "CONF"):
                    continue
                seen.add(y)
                if y in verdict:
                    found.add(y)
                stack.append(y)
        return found

    gaps, allowed = collections.defaultdict(list), collections.defaultdict(list)
    for d, m in sorted(node_mod.items()):
        if C[d] != "MECH" or kind.get(d) != "thm" or not real(d):
            continue
        b = borrowed(d)
        if not b:
            continue
        near = {t for t in b if any(node_mod[t].startswith(p) for p in CONFORMING)}
        (gaps if near else allowed)[m].append((d, sorted(near or b)))

    recorded = load_recorded()
    total = sum(len(v) for v in gaps.values())
    print(f"{len(verdict)} protocol theorems are about verdicts.")
    print(f"{total} mechanism theorems reach one outside the properties, "
          f"for a rule that shows the six.\n")
    live = set()
    for m in sorted(gaps):
        print(f"  {m}")
        for d, b in sorted(gaps[m]):
            short = d.replace("LeanDag.", "")
            live.add(short)
            mark = "recorded" if short in recorded else "UNRECORDED"
            print(f"    {mark:10s} {short:52s} <- "
                  f"{sorted(x.replace('LeanDag.', '') for x in b)}")
    extra = sum(len(v) for v in allowed.values())
    if extra:
        print(f"\n{extra} more, for rules with no `Banded` to route through: "
              f"not a gap in the arc.")

    bad = sorted(live - recorded)
    stale = sorted(recorded - live)
    if bad:
        print("\nFAIL unrecorded bespoke link: " + ", ".join(bad))
    if stale:
        print("\nFAIL recorded but no longer bespoke (strike it off "
              "docs/bespoke-links.md): " + ", ".join(stale))
    if not bad and not stale:
        print("\nok — every remaining link is recorded."
              if live else "\nok — no bespoke links remain.")
    return 1 if (bad or stale) else 0


if __name__ == "__main__":
    sys.exit(main())
