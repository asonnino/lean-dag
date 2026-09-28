import LeanDag.Steelhead.Model.Period
import LeanDag.Steelhead.Model.Pair
import LeanDag.Common.History
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Nat.Log
/-!
# Steelhead — the replay

The paper's Algorithm 3 as data, as `replay.rs` computes it: the
evidence a window holds, read from the anchor's causal history at the
rounds `round A − I` and above (`ofAnchor`); the three passes of
`REPLAY(W, k')` over that evidence, each a recursion on the round index
as the algorithm walks it, each slot decided by its own wave, a
synchronous slot exactly where the window holds its certificates and by
the probes' rate elsewhere, an asynchronous slot averaged over the `n`
candidate leaders (`timingAt`), a round output when the first slot at or
above it commits (`firstCommitAt`) and no earlier than every lower
slot's decision (`gateAt`, `score`); and the hysteretic selection among
the candidate periods, the powers of two up to the largest
(`candidatesUpto`), ties favouring the larger candidate and the
hysteresis keeping the current period unless a candidate improves on it
(`select`). Exact rationals stand in for the expectations; the
implementation computes them in units of `1/n`, rounding down, a
difference the results here do not read. `anchorUpdate` is the whole as
an `UpdateRule`; the failover is the scan's own step (`PeriodAt.anchor`,
`Model/Period.lean`), taken before the rule is consulted.

Evidence is indexed by proposal round, wave and candidate author, and
counts distinct validators, so that an equivocator is one author
however many blocks it made. A missing anchor, a round outside the
window and the recurrences' initial values read the window's top, the
common penalty for an unresolved outcome, as the algorithm has it.

The evidence is the rule's support, as the paper's Appendix B reads it:
`n − f` supporters at the decision round commit, `n − f` blames at the
rule's blame round skip, and the indirect threshold of supporters within
the window stands in for the anchor's certificate. Each pair fills it
from its own rules: the `3f + 1` pair's window (`ofAnchor`) counts
Mahi-Mahi's certificates and blames at the slot's wave; BlueBottle's
(`BlueBottlePair.Replay.ofAnchor`) counts the decision-round votes
themselves, Odontoceti's references one round up at wave two and Async
BlueBottle's cone votes two rounds up otherwise, with `n − 3f` of them
the indirect threshold. Where the blame round lies is the one parameter
of the replay itself: the vote round for the `3f + 1` pair and the
decision round for BlueBottle's, the implementation's
`merged_certificates` (`Config.merged`).

**Definitions only**, as in the other model files.
-/

namespace LeanDag

namespace Steelhead

namespace Replay

/-- **The evidence a window holds**, indexed by proposal round, wave and candidate author. -/
structure Evidence (Validator : Type) where
  /-- The first round the window retains. -/
  bottom : ℕ
  /-- The last round the window retains, the anchor's. -/
  top : ℕ
  /-- A quorum of the window's blocks at the decision round certify a block of this author. -/
  commits : ℕ → ℕ → Validator → Bool
  /-- A quorum of the window's blocks at the vote round blame this author's slot. -/
  skips : ℕ → ℕ → Validator → Bool
  /-- The window holds a certificate for a block of this author. -/
  certified : ℕ → ℕ → Validator → Bool

/-- **The replay's parameters**: the two waves, the canary spacing, none when no round carries
the canary wait, and the known-leader schedule, read at every round whether or not it ran
synchronously. -/
structure Config (Validator : Type) where
  /-- The synchronous wave. -/
  ws : ℕ
  /-- The asynchronous wave. -/
  wa : ℕ
  /-- The canary spacing, `none` when the canary is off. -/
  canary : Option ℕ
  /-- The known-leader schedule. -/
  known : ℕ → Validator
  /-- Whether the decision-round votes are themselves the certificates, the implementation's
  `merged_certificates`: BlueBottle's pair blames at the decision round, the `3f + 1` pair at
  the vote round below it. -/
  merged : Bool := false

/-- **A canary round**: a multiple of the canary spacing; no round when the canary is off. -/
def Config.canaried {Validator : Type} (C : Config Validator) (r : ℕ) : Bool :=
  match C.canary with
  | some c => r % c == 0
  | none => false

/-- **The offset of the blame round** at a wave: the decision round `w − 1` under merged
certificates, the vote round `w − 2` otherwise, the paper's `β(w)`. -/
def Config.blame {Validator : Type} (C : Config Validator) (w : ℕ) : ℕ :=
  if C.merged then w - 1 else w - 2

/-- **A slot's expected decision and commit rounds**; the window's top stands for an outcome the
window does not resolve. -/
structure Timing where
  /-- The expected decision round. -/
  decision : ℚ
  /-- The expected commit round. -/
  commit : ℚ
  deriving DecidableEq, Repr

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
  [Faults Validator] [LinearOrder BlockId]

/-- **The window**: the anchor's causal history at the rounds `round A − I` and above, round `0`
excluded. -/
def windowIds (U : BlockUniverse Validator BlockId Payload) (A : BlockId) (I : ℕ) :
    Finset BlockId :=
  (history U A).filter fun b =>
    windowBottom U A I ≤ (U.block b).round ∧ (U.block b).round ≤ (U.block A).round

/-- **The evidence of an anchor's window**: a candidate is a block of the author at the round
inside the window; it is committed when a quorum of distinct validators certify it within the
window, skipped when a quorum of the window's vote-round blocks blame the author's slot, and
certified when the window holds one certificate for it. The votes are Mahi-Mahi's, so an
equivocator's blocks are arbitrated as the rule arbitrates them. -/
def ofAnchor (U : BlockUniverse Validator BlockId Payload) (A : BlockId) (I : ℕ) :
    Evidence Validator :=
  let ids := windowIds U A I
  let candidates := fun r a => (blocksAt U r).filter fun L => (U.block L).creator = a ∧ L ∈ ids
  let certs := fun r w L => MahiMahi.certificates U w L r ∩ ids
  { bottom := windowBottom U A I
    top := (U.block A).round
    commits := fun r w a => decide (∃ L ∈ candidates r a,
      quorumCard Validator ≤ (creatorsOf U.block (certs r w L)).card)
    skips := fun r w a => decide (quorumCard Validator ≤
      (creatorsOf U.block (((blocksAt U (MahiMahi.votingRound w r)).filter
        fun q => MahiMahi.Blames U q a r) ∩ ids)).card)
    certified := fun r w a => decide (∃ L ∈ candidates r a, certs r w L ≠ ∅) }

/-- The window's rounds, in increasing order. -/
def rounds (E : Evidence Validator) : List ℕ :=
  (List.range (E.top + 1 - E.bottom)).map (E.bottom + ·)

/-- **The committed candidates of a round**: the authors the evidence marks committed at the wave,
the paper's `c_r`. -/
def committedCount (E : Evidence Validator) (r w : ℕ) : ℕ :=
  (Finset.univ.filter fun a => E.commits r w a = true).card

/-- **The probes of a candidate period**: the canary rounds it replays as synchronous slots
whose decision round the window holds, and how many of them hold a quorum of certificates for
the known leader. -/
def probeRate (E : Evidence Validator) (C : Config Validator) (period : ℕ) : ℕ × ℕ :=
  let probes := (rounds E).filter fun r =>
    r % period != 0 && C.canaried r && r + C.ws - 1 ≤ E.top
  ((probes.filter fun r => E.commits r C.ws (C.known r)).length, probes.length)

/-- The timing of an outcome the window does not resolve: its top, for decision and commit. -/
def clipped (top : ℕ) : Timing := ⟨top, top⟩

/-- **One candidate's timing**: a direct skip at the blame round with no commit, a direct commit
at the decision round, or the anchor's decision with the anchor's commit if the window holds the
indirect threshold of supporters for the candidate and none otherwise. -/
def candidateTiming (E : Evidence Validator) (C : Config Validator) (r wave : ℕ)
    (author : Validator) (anchor : Timing) : Timing :=
  if E.skips r wave author then ⟨r + C.blame wave, E.top⟩
  else if E.commits r wave author then ⟨r + wave - 1, r + wave - 1⟩
  else ⟨anchor.decision, if E.certified r wave author then anchor.commit else E.top⟩

/-- **One round's timing** from the timings of the rounds above: clipped when its decision round
lies past the window; by the probes' rate at an unprobed synchronous slot; and otherwise the mean
over its candidates, the known leader alone at a synchronous slot and every author at an
asynchronous one, each decided directly or by the earliest committed slot at or above its floor.
Synchronous is `r mod k' ≠ 0`, as the implementation tests it, so the two waves may coincide. -/
def roundTiming (E : Evidence Validator) (C : Config Validator) (period : ℕ) (probes : ℕ × ℕ)
    (higher : ℕ → Timing) (r : ℕ) : Timing :=
  let async := r % period = 0
  let wave := if async then C.wa else C.ws
  if r + wave - 1 > E.top then clipped E.top
  else if ¬ async ∧ ¬ C.canaried r ∧ probes.2 > 0 then
    let s : ℚ := probes.1
    let t : ℚ := probes.2
    ⟨(s * (r + C.ws - 1 : ℕ) + (t - s) * (r + C.blame C.ws : ℕ)) / t,
      (s * (r + C.ws - 1 : ℕ) + (t - s) * E.top) / t⟩
  else
    let a := (rounds E).find? fun j => r + wave ≤ j && (higher j).commit < E.top
    let anchor := a.map higher |>.getD (clipped E.top)
    let authors := if async then Finset.univ else {C.known r}
    let timing := fun v => candidateTiming E C r wave v anchor
    ⟨(authors.sum fun v => (timing v).decision) / authors.card,
      (authors.sum fun v => (timing v).commit) / authors.card⟩

/-- **Pass one, from the top of the window down**: the timing of round `r` from the timings of the
rounds above it, which are `clipped E.top` outside the window; a round outside the window has that
timing itself. -/
def timingAt (E : Evidence Validator) (C : Config Validator) (period : ℕ) (probes : ℕ × ℕ) :
    ℕ → Timing
  | r =>
    if _h : E.bottom ≤ r ∧ r ≤ E.top then
      roundTiming E C period probes
        (fun j => if _hj : r < j then timingAt E C period probes j else clipped E.top) r
    else clipped E.top
termination_by r => E.top + 1 - r
decreasing_by all_goals omega

/-- **Pass two**: the earliest expected commit at or above a round, the window's top past it. -/
def firstCommitAt (E : Evidence Validator) (ts : ℕ → Timing) : ℕ → ℚ
  | r => if h : r ≤ E.top then min (ts r).commit (firstCommitAt E ts (r + 1)) else E.top
termination_by r => E.top + 1 - r
decreasing_by all_goals omega

/-- **Pass three's gate**: the latest expected decision below a round, the window's bottom at its
first round, so that a round's output waits for every lower slot's decision. -/
def gateAt (E : Evidence Validator) (ts : ℕ → Timing) : ℕ → ℚ
  | r => if h : E.bottom < r then max (gateAt E ts (r - 1)) (ts (r - 1)).decision else E.bottom
termination_by r => r
decreasing_by all_goals omega

/-- **The score**: the sum over the window of each round's delay to output, a round output when
the first commit at or above it is expected and no earlier than every lower slot's decision. -/
def score (E : Evidence Validator) (C : Config Validator) (period : ℕ) : ℚ :=
  let ts := timingAt E C period (probeRate E C period)
  ((rounds E).map fun r => max (firstCommitAt E ts r) (gateAt E ts r) - r).sum

/-- **The preference between two candidates**: the smaller score; at a tie the current period,
then the larger candidate. -/
def prefer (scores : ℕ → ℚ) (current candidate incumbent : ℕ) : Bool :=
  decide (scores candidate < scores incumbent ∨
    (scores candidate = scores incumbent ∧ incumbent ≠ current ∧
      (candidate = current ∨ incumbent < candidate)))

/-- **The best candidate**, the current period the first incumbent. -/
def best (candidates : List ℕ) (scores : ℕ → ℚ) (current : ℕ) : ℕ :=
  candidates.foldl (fun incumbent candidate =>
    if prefer scores current candidate incumbent then candidate else incumbent) current

/-- **The hysteretic selection**: the best candidate if it improves on the current period by
the factor `1 − ε`, the current period otherwise; the fold's winner outright when the current
period is not a candidate, where `choose_period` returns its best candidate and the fold, which
starts from the current period, may keep it. The implementation never reaches that case, its
period being a power of two at most the period bound. -/
def select (candidates : List ℕ) (scores : ℕ → ℚ) (current : ℕ) (epsilon : ℚ) : ℕ :=
  let winner := best candidates scores current
  if current ∈ candidates then
    if scores winner < (1 - epsilon) * scores current then winner else current
  else winner

/-- **The candidate periods**: the powers of two up to `K`, the implementation's
`{1, 2, 4, …, maxPeriod}`; every candidate once `K` is a power of two. -/
def candidatesUpto (K : ℕ) : List ℕ := (List.range (Nat.log 2 K + 1)).map (2 ^ ·)

/-- **Algorithm 3 on one window**: the selection among the candidates by the replay's scores. -/
def update (E : Evidence Validator) (C : Config Validator) (candidates : List ℕ) (current : ℕ)
    (epsilon : ℚ) : ℕ :=
  select candidates (score E C) current epsilon

/-- **Algorithm 3 as an update rule**: the replay of the anchor's window. -/
def anchorUpdate (U : BlockUniverse Validator BlockId Payload) (I : ℕ) (C : Config Validator)
    (candidates : List ℕ) (epsilon : ℚ) : UpdateRule BlockId :=
  fun A current => update (ofAnchor U A I) C candidates current epsilon

end Replay

namespace BlueBottlePair

namespace Replay

open Steelhead.Replay

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults5 Validator] [LinearOrder BlockId]

/-- **Odontoceti's blames of a slot**: the round-`(r + 1)` blocks referencing no block of author
`a` at round `r`, the core's `slotBlamers` indexed by round and author. -/
def omitters (U : BlockUniverse Validator BlockId Payload) (a : Validator) (r : ℕ) :
    Finset BlockId :=
  (blocksAt U (r + 1)).filter fun q =>
    ∀ j ∈ (U.block q).refs, ¬ ((U.block j).round = r ∧ (U.block j).creator = a)

/-- **The pair's support blocks** for a candidate `L` at round `r`, at wave `w`: Odontoceti's
references one round up at wave two, Async BlueBottle's cone votes two rounds up otherwise. -/
def supportBlocks (U : BlockUniverse Validator BlockId Payload) (w : ℕ) (L : BlockId) (r : ℕ) :
    Finset BlockId :=
  if w = 2 then votesFor U L (r + 1) else AsyncBlueBottle.voters U L r

/-- **The pair's blame blocks** of the slot `(a, r)` at wave `w`: Odontoceti's omitters one round
up at wave two, Async BlueBottle's blamers two rounds up otherwise. -/
def blameBlocks (U : BlockUniverse Validator BlockId Payload) (w : ℕ) (a : Validator) (r : ℕ) :
    Finset BlockId :=
  if w = 2 then omitters U a r else AsyncBlueBottle.blamerBlocks U a r

/-- **The evidence of an anchor's window at BlueBottle's pair**: a candidate is a block of the
author at the round inside the window; it is committed when a quorum of distinct validators
support it within the window, skipped when a quorum of the window's decision-round blocks blame
the author's slot, and certified when `n − 3f` distinct validators support it within the window,
the pair's indirect threshold. The decision-round votes are the certificates, the
implementation's `merged_certificates`; a wave of two reads Odontoceti, any other Async
BlueBottle, whose decision round does not read the wave. -/
def ofAnchor (U : BlockUniverse Validator BlockId Payload) (A : BlockId) (I : ℕ) :
    Evidence Validator :=
  let ids := windowIds U A I
  let candidates := fun r a => (blocksAt U r).filter fun L => (U.block L).creator = a ∧ L ∈ ids
  let support := fun r w L => creatorsOf U.block (supportBlocks U w L r ∩ ids)
  { bottom := windowBottom U A I
    top := (U.block A).round
    commits := fun r w a => decide (∃ L ∈ candidates r a,
      quorumCard Validator ≤ (support r w L).card)
    skips := fun r w a => decide (quorumCard Validator ≤
      (creatorsOf U.block (blameBlocks U w a r ∩ ids)).card)
    certified := fun r w a => decide (∃ L ∈ candidates r a,
      Fintype.card Validator - 3 * F.f ≤ (support r w L).card) }

/-- **Algorithm 3 as an update rule at BlueBottle's pair**: the replay of the anchor's window
read through the pair's support. -/
def anchorUpdate (U : BlockUniverse Validator BlockId Payload) (I : ℕ) (C : Config Validator)
    (candidates : List ℕ) (epsilon : ℚ) : UpdateRule BlockId :=
  fun A current => update (ofAnchor U A I) C candidates current epsilon

end Replay

end BlueBottlePair

end Steelhead

end LeanDag
