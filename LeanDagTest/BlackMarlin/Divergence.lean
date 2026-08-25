import LeanDagTest.BlackMarlin.Ledger
import LeanDag.BlackMarlin.Repair.Proof

/-!
# Black Marlin — two honest parties, two different blocks

A universe on which one validator outputs a Byzantine anchor's block `8`
and another outputs its twin `12`, and neither ever outputs the other.
That is Definition 1's **Agreement** refuted for the protocol as
specified (`black-marlin.md` §13).

Four validators, `0` Byzantine, seven rounds; ids run in production
order, with round `2` carrying five blocks because validator `0`
equivocates there. The rotation anchors rounds `0` to `6` by
`3, 3, 0, 1, 2, 3, 1`.

The construction turns on three facts, each settled by `decide` below.

* Block `8` is **committed by the rule**: three round-3 blocks reference
  it, and the round-3 anchor `14` both references it and carries three
  supporters. Its twin `12` is supported by one validator only, so BM1 is
  not contradicted.
* The round-4 anchor `19` **omits `14`** from its references — legal, a
  block needs `n − f = 3` of `4`, and a correct validator that has not
  yet received `14` will do exactly this. Its cone therefore holds no
  round-3 anchor, so a descent arriving at `19` skips round `3` and
  faces both twins at round `2`.
* The tie-break of L24 prefers `12`: `8` omits the round-1 anchor from
  its own references and `12` includes it, so `12` is one round from the
  highest anchor of its cone and `8` is two.

A validator that committed `8` at round `2` flushes it then. One whose
view at `delivery(4)` lacked `17`, `18` and `20` saw `14` unsupported,
so the attempt failed; the protocol never retries a round, so it commits
`19` at round `6` instead and its descent takes `12`.

**No timing hypothesis is needed.** Agreement is a safety property, which
the paper states holds during asynchrony as well, and asynchrony is
exactly the freedom to delay those three blocks to the second validator.
Every block below references only blocks of the round beneath it that
its author could have held, and each honest one carries every block of
that round it holds, as L46–L48 require.
-/

namespace LeanDagTest

namespace BlackMarlin

set_option maxRecDepth 4000000

open LeanDag LeanDag.BlackMarlin

/-- The rotation: rounds `0` to `6` anchored by `3, 3, 0, 1, 2, 3, 1`.
Round `2` is anchored by the Byzantine validator. -/
local instance divRot : Rotation (Fin 4) where
  anchor r := match r with
    | 0 => 3 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 3 | 6 => 1 | _ => 0

/-- The blocks. Id order is production order, so references always carry
smaller identifiers. -/
def divBlk : Fin 29 → Block (Fin 4) (Fin 29) Unit := fun i =>
  { round :=
      match (i : ℕ) with
      | 0 | 1 | 2 | 3 => 0
      | 4 | 5 | 6 | 7 => 1
      | 8 | 9 | 10 | 11 | 12 => 2
      | 13 | 14 | 15 | 16 => 3
      | 17 | 18 | 19 | 20 => 4
      | 21 | 22 | 23 | 24 => 5
      | _ => 6,
    creator :=
      match (i : ℕ) with
      | 0 | 4 | 8 | 12 | 13 | 17 | 21 | 25 => 0
      | 1 | 5 | 9 | 14 | 18 | 22 | 26 => 1
      | 2 | 6 | 10 | 15 | 19 | 23 | 27 => 2
      | _ => 3,
    refs :=
      match (i : ℕ) with
      | 0 | 1 | 2 | 3 => ∅
      | 4 => {0, 1, 2} | 5 => {0, 1, 2} | 6 => {1, 2, 3} | 7 => {1, 2, 3}
      | 8 => {4, 5, 6} | 9 => {4, 5, 6} | 10 => {4, 5, 6} | 11 => {5, 6, 7}
      | 12 => {4, 6, 7}
      | 13 => {9, 10, 12} | 14 => {8, 9, 10} | 15 => {8, 9, 10} | 16 => {8, 9, 11}
      | 17 => {13, 14, 15} | 18 => {13, 14, 15} | 19 => {13, 15, 16}
      | 20 => {14, 15, 16}
      | 21 => {17, 18, 19} | 22 => {17, 18, 19} | 23 => {17, 18, 19}
      | 24 => {18, 19, 20}
      | 25 => {21, 22, 23} | 26 => {22, 23, 24} | 27 => {22, 23, 24}
      | _ => {22, 23, 24},
    payload := () }

/-- The universe: valid, and equivocating only at the Byzantine
validator. -/
def Udiv : BlockUniverse (Fin 4) (Fin 29) Unit where
  ids := Finset.univ
  block := divBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-! ## The equivocation, and what the rule admits -/

/-- Blocks `8` and `12` are twins: both anchor round `2`, both by the
Byzantine validator. -/
example : IsAnchor Udiv 2 8 ∧ IsAnchor Udiv 2 12 ∧ (8 : Fin 29) ≠ 12 ∧
    (Udiv.block 8).creator ∉ (Correct : Finset (Fin 4)) := by decide

/-- **The rule commits `8`** — and only `8`: its twin carries one
supporter, so anchor uniqueness is not contradicted. -/
example : Committed Udiv 8 2 ∧ ¬ Supported Udiv 12 2 := by decide

/-- The round-4 anchor omits the round-3 anchor, so its cone holds no
anchor of round `3` and a descent arriving there skips the round. -/
example : IsAnchor Udiv 4 19 ∧ (14 : Fin 29) ∉ (Udiv.block 19).refs ∧
    coneAnchors Udiv 19 3 = ∅ := by decide

/-- And the round-4 anchor is itself committed, so a validator that
missed round `2` still commits later. -/
example : Committed Udiv 19 4 := by decide

/-! ## The descent parts the two -/

/-- Both twins are candidates below the round-4 anchor, and the metric of
L24 prefers `12`. -/
example : maxAnchor Udiv (strongOf Udiv 19) = {8, 12} ∧
    anchorGap Udiv 12 = 1 ∧ anchorGap Udiv 8 = 2 := by decide

/-- Both metrics are readings of a real anchor rather than of an absent
one: each twin's cone holds an anchor, so L24 compares two defined
quantities and the preference for `12` does not rest on how the empty
case is read. -/
example : (anchorsOf Udiv (strongOf Udiv 8)).Nonempty ∧
    (anchorsOf Udiv (strongOf Udiv 12)).Nonempty ∧
    maxAnchorRound Udiv (strongOf Udiv 8) = 0 ∧
    maxAnchorRound Udiv (strongOf Udiv 12) = 1 := by decide

/-- And neither twin lies in the other's cone, so which twin a validator
flushes at round `2` is settled by the record alone — no property of the
sort `τ` enters. -/
example : (8 : Fin 29) ∉ history Udiv 12 ∧ (12 : Fin 29) ∉ history Udiv 8 := by decide

/-- **The records disagree at round `2`.** The validator that committed
`8` flushed `8`; the descent from the round-4 anchor takes `12`. -/
example : flushRecord Udiv 8 2 = some 8 ∧ flushRecord Udiv 19 2 = some 12 := by decide

/-! ## And so the two output different blocks

Identifiers run downward along references here too, so sorting by
identifier is a topological sort. -/

example : ∀ b : Fin 29, ∀ j ∈ (Udiv.block b).refs, j < b := by decide

/-- The sort of this model. -/
def divSort : TopoSort Udiv := TopoSort.ofFinOrder Udiv (by decide)

/-- The record of the validator that committed `8` at round `2`. -/
def vFlush : Flush Udiv := toFlush Udiv 8 (by decide) (by decide)

/-- The record of the validator that missed round `2` and committed the
round-4 anchor at round `6` instead. -/
def wFlush : Flush Udiv := toFlush Udiv 19 (by decide) (by decide)

example : wFlush.block 4 = some 19 ∧ wFlush.block 3 = none ∧
    wFlush.block 2 = some 12 ∧ wFlush.block 1 = some 7 ∧
    wFlush.block 0 = some 3 := by decide

/-- **Definition 1's Agreement, refuted.** The first validator outputs
`8` and never `12`; the second outputs `12` and never `8`. Both are
honest, both follow the rules, and the filter of L27 bars each from ever
emitting the other's block, since a block of that author and round has
already gone out. -/
example :
    (8 : Fin 29) ∈ deliverSeq Udiv vFlush divSort 3 ∧
    (12 : Fin 29) ∉ deliverSeq Udiv vFlush divSort 3 ∧
    (12 : Fin 29) ∈ deliverSeq Udiv wFlush divSort 5 ∧
    (8 : Fin 29) ∉ deliverSeq Udiv wFlush divSort 5 := by decide

/-- The second validator does flush `8` — it is in the round-4 anchor's
cone — and drops it only at the filter. So the divergence is not a
missing block but a **different choice of twin**. -/
example : (8 : Fin 29) ∈ ledgerSeq Udiv wFlush divSort 5 ∧
    key Udiv 8 = key Udiv 12 := by decide

/-- **The dilemma.** Both twins are flushed by the second validator, and
they carry one author-and-round between them, so L27 must drop one:
emitting both would output two blocks for a single `(party, round)`,
which Definition 1's Integrity forbids "at most once regardless of `B`".
It drops `8` — the block the first validator has already output. So the
execution admits no reading that satisfies both properties: filter, and
Agreement fails; do not filter, and Integrity does. -/
example : key Udiv 8 = key Udiv 12 ∧
    (8 : Fin 29) ∈ ledgerSeq Udiv wFlush divSort 5 ∧
    (12 : Fin 29) ∈ ledgerSeq Udiv wFlush divSort 5 ∧
    (8 : Fin 29) ∉ deliverSeq Udiv wFlush divSort 5 ∧
    (12 : Fin 29) ∈ deliverSeq Udiv wFlush divSort 5 := by decide

/-- Nothing above contradicts safety of the rule: the two records agree
wherever both flush a committed anchor, and `12` is not one. -/
example : ¬ Committed Udiv 12 2 := by decide


/-! ## The repair, on this execution -/

/-- **The side-condition closes it.** Only one of the two candidates
below the round-4 anchor is supported, so the repaired descent takes `8`
— the block the rule committed and the first validator output — and the
two records now agree at round `2`. -/
example : suppCandidates Udiv 19 = {8} ∧ descendSupp Udiv 19 = some 8 ∧
    flushRecordSupp Udiv 19 2 = some 8 ∧ flushRecordSupp Udiv 8 2 = some 8 := by decide

/-- **And what it costs, on data.** The repaired chain passes through
`8`, whose cone holds no round-1 anchor, so it flushes nothing at round
`1` where the unrepaired chain flushed `7`. No block is lost — `7` is in
the round-4 anchor's cone and is delivered in that segment instead — but
the segmentation differs, which is why BMP4 speaks of a step and not of
a record. -/
example : flushRecordSupp Udiv 19 1 = none ∧ flushRecord Udiv 19 1 = some 7 ∧
    (7 : Fin 29) ∈ history Udiv 19 := by decide

/-- Nothing the commit rule admits has changed: `8` is still committed
and `12` still is not, since `Committed` mentions no part of the
descent. -/
example : Committed Udiv 8 2 ∧ ¬ Committed Udiv 12 2 := by decide

/-! ### The strengthened repair -/

/-- **The strengthened descent never faces the choice at all.** The only
supported anchor in the round-4 anchor's cone is `8`, so the descent goes
straight to it, and the two records agree at every round. `12` is never a
boundary for anyone: a round whose anchors carry no quorum is not one. -/
example : suppAnchorsOf Udiv (strongOf Udiv 19) = {8} ∧
    descendS Udiv 19 = some 8 ∧
    flushRecordS Udiv 19 2 = flushRecordS Udiv 8 2 ∧
    flushRecordS Udiv 19 1 = flushRecordS Udiv 8 1 ∧
    flushRecordS Udiv 19 0 = flushRecordS Udiv 8 0 := by decide

/-- Its boundaries are the committed anchors and nothing else here: the
round-1 and round-0 anchors carry two supporters apiece, one short, so
neither is a boundary and their blocks come out inside the segment
above. -/
example : ¬ Supported Udiv 7 1 ∧ ¬ Supported Udiv 3 0 ∧
    flushRecordS Udiv 19 4 = some 19 ∧ flushRecordS Udiv 19 3 = none ∧
    flushRecordS Udiv 19 1 = none ∧ flushRecordS Udiv 19 0 = none := by decide

/-- **And here the support really is in view.** `Supported` is a fact
about the universe, so a validator can act on it only where its own view
carries the witnesses. The three supporters of `8` lie in the cone of
every round-6 block, and the second validator holds a quorum of those by
the time it concludes round `6` and commits the round-4 anchor — so it
can see `8` supported exactly when its descent needs to know. That this
holds in general is not established. -/
example : ∀ b : Fin 29, (Udiv.block b).round = 6 →
    ({14, 15, 16} : Finset (Fin 29)) ⊆ history Udiv b := by decide

example : supporters Udiv 8 3 = {1, 2, 3} := by decide

end BlackMarlin

end LeanDagTest
