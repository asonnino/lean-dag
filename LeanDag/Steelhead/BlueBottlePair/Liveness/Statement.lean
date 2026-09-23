import LeanDag.Steelhead.Model.Pair
import LeanDag.Steelhead.Model.Clauses
import LeanDag.Steelhead.Model.Reactive
/-!
# The `5f + 1` pair's liveness — statement

Theorem 2 at BlueBottle's two variants, Odontoceti at the synchronous kind
and Async BlueBottle elsewhere, on one `n ≥ 5f + 1` committee. The
generic statements of `Liveness/Statement.lean` read a rule only through
its laws and the clauses of `Model/Clauses.lean`; this file states that
the pair's composite has them and what Theorem 2 then says of it. Five
claims:

* **SH-BB6a, the pair commits a reliable leader under synchrony** —
  clause A4 at the composite: Odontoceti's quorum of supporters one round
  up at the synchronous kind (O7), Async BlueBottle's cone votes two
  rounds up elsewhere (ABB10a), each at its own decision round;
* **SH-BB6c, the pair skips a silent leader** — a slot whose leader has no
  block at its round is skipped by the blames at its decision round, one
  round up for Odontoceti and two for Async BlueBottle;
* **SH-BB6d, partial dissemination does not defer at the asynchronous
  kind** — SH-MM6d's remark at Async BlueBottle: a candidate one reliable
  block references one round up, its leader's only block at its round, is
  directly committed in every view holding its decision round, once the
  quorum is synchronised from that round and populates the wave. The
  cone vote two rounds up is what carries it. At the synchronous kind the
  remark fails as stated: Odontoceti's vote round is the round above the
  candidate, where only the one block is known to reference it;
* **SH-BB6k, a reliable leader commits under the reactive discipline** —
  Steelhead's reactive schedule at a round that carries the leader wait:
  the reliable blocks one round up reference the leader's block, which is
  Odontoceti's commit, and reach it from two rounds up, which is Async
  BlueBottle's. No certificate wait is read, the pair having no
  certificate stage;
* **SH-BB6, Theorem 2 at the pair** — the descent from a committed landing
  (SH6m), the round count `(b + 1) · (2 + (n − |T|))` above an unskipped
  slot when every slot is synchronous (SH6j at `p = ∞`, where
  `2 · (n − |T|) < n` holds for a bare reliable quorum at `n = 5f + 1`),
  and the round count `(b + 1) · (2 + W) + 3` at a period (SH6p at the
  waves two and three).

Odontoceti and Async BlueBottle are consumed read-only.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace BlueBottlePair

namespace Liveness

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults5 Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

/-- **SH-BB6a, the pair commits a reliable leader under synchrony.** -/
def CommitsUnderSyncAtPair (U : BlockUniverse Validator BlockId Payload) : Prop :=
  CommitsUnderSync (blueBottlePairAnchored Validator BlockId Payload) U

/-- **SH-BB6c, the pair skips a silent leader.** -/
def SkipsSilentAtPair (U : BlockUniverse Validator BlockId Payload) : Prop :=
  SkipsSilent (blueBottlePairAnchored Validator BlockId Payload) U

/-- **SH-BB6d, partial dissemination does not defer at the asynchronous kind.** -/
def CommitsOfDisseminationAsync (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (k : ℕ) (L q : BlockId),
    -- the slot is asynchronous, decided by Async BlueBottle
    S.kind k ≠ 0 →
    -- T is a quorum
    quorumCard Validator ≤ T.card →
    -- L is the slot's candidate, and its leader's only block at the slot's round
    IsLeaderBlock U k L →
    (∀ L' ∈ U.ids, (U.block L').round = S.slotRound k → (U.block L').creator = S.leader k →
      L' = L) →
    -- one reliable block one round up references it ...
    q ∈ U.ids → (U.block q).round = S.slotRound k + 1 → (U.block q).creator ∈ T →
    L ∈ (U.block q).refs →
    -- ... T is synchronised from that round and populates it through the decision round ...
    SynchronisedOn U T (S.slotRound k + 1) →
    (∀ r, S.slotRound k + 1 ≤ r →
      r ≤ (blueBottlePairAnchored Validator BlockId Payload).decisionRound k → PopulatedOn U T r) →
    -- ... and the view holds the decision round
    V.CoversUpto ((blueBottlePairAnchored Validator BlockId Payload).decisionRound k) →
    -- then the slot commits its candidate in that view
    (blueBottlePairAnchored Validator BlockId Payload).Decided U V k (some L)

/-- **SH-BB6k, a reliable leader commits under the reactive discipline.** -/
def CommitsOfReactivePace (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (N R k : ℕ) (w : ℕ → ℕ)
    (waits : ℕ → Prop) (rs : ReactiveS U T N w waits),
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- the reactive schedule is past GST from R, where its timeout clears the delay
    rs.gst ≤ R → (∀ n, R ≤ n → 2 * rs.delay + rs.proc ≤ rs.timeout n) →
    -- the slot lies at or past R, its round carries the leader wait, and its decision round lies
    -- within the schedule's horizon
    R ≤ S.slotRound k → waits (S.slotRound k) →
    (blueBottlePairAnchored Validator BlockId Payload).decisionRound k ≤ N →
    -- and the view holds that round
    V.CoversUpto ((blueBottlePairAnchored Validator BlockId Payload).decisionRound k) →
    -- then a reliably led slot commits its candidate in that view, by the direct rule
    S.leader k ∈ T →
    ∃ L, IsLeaderBlock U k L ∧
      (blueBottlePairAnchored Validator BlockId Payload).Decided U V k (some L)

/-- **SH-BB6, Theorem 2 at the pair.** -/
def PairDecides (U : BlockUniverse Validator BlockId Payload) : Prop :=
  -- the descent: a chain of hops whose last landing is committed decides its start
  (∀ (V : View Validator BlockId Payload U) (h : ℕ) (x : ℕ → ℕ),
    (∀ t, S.slotRound t = t) →
    (∀ i, i < h →
      FloorHopOf (blueBottlePairAnchored Validator BlockId Payload) U V (x i) (x (i + 1))) →
    (∃ A, (blueBottlePairAnchored Validator BlockId Payload).Decided U V (x h) (some A)) →
    ∃ v, (blueBottlePairAnchored Validator BlockId Payload).Decided U V (x 0) v) ∧
  -- every slot synchronous: the chain decides within (b + 1) · (2 + (n − |T|)) rounds
  (∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R N n : ℕ) (hn : 0 < n)
    (lead : Fin n → Validator) (k : ℕ),
    (∀ t, S.slotRound t = t) → (∀ t, S.kind t = 0) →
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → V.CoversUpto N →
    (∀ v, v ∉ T → v ∉ F.byzantine →
      ∀ L ∈ U.ids, R ≤ (U.block L).round → (U.block L).creator ≠ v) →
    Function.Bijective lead → (∀ t, S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩) →
    2 * (n - T.card) < n →
    R ≤ k → ¬ (blueBottlePairAnchored Validator BlockId Payload).Decided U V k none →
    k + (F.byzantine.card + 1) * (2 + (n - T.card)) ≤ N →
    ∃ v, (blueBottlePairAnchored Validator BlockId Payload).Decided U V k v) ∧
  -- at a period: the chain decides within (b + 1) · (2 + W) + 3 rounds
  (∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R N p n W : ℕ) (hn : 0 < n)
    (lead : Fin n → Validator) (k : ℕ),
    0 < p → (∀ t, S.slotRound t = t) → (∀ t, S.kind t = periodicKind p t) →
    (∀ t, S.kind t = 0 → S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩) →
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → V.CoversUpto N →
    (∀ v, v ∉ T → v ∉ F.byzantine →
      ∀ L ∈ U.ids, R ≤ (U.block L).round → (U.block L).creator ≠ v) →
    Function.Bijective lead →
    2 * (n - T.card) + 2 * ((n + p - 1) / p) < n →
    (∀ r, ∃ a, r ≤ a ∧ a ≤ r + W ∧ S.kind a = 0 ∧ S.leader a ∈ T) →
    (∀ t, k ≤ t → S.kind t = 1 →
      ∃ v, (blueBottlePairAnchored Validator BlockId Payload).Decided U V t v) →
    R ≤ k → ¬ (blueBottlePairAnchored Validator BlockId Payload).Decided U V k none →
    k + (F.byzantine.card + 1) * (2 + W) + 3 ≤ N →
    ∃ v, (blueBottlePairAnchored Validator BlockId Payload).Decided U V k v)

/-- The `5f + 1` pair's liveness, over every fault configuration, schedule and block universe the
model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults5 Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload),
    CommitsUnderSyncAtPair U ∧ SkipsSilentAtPair U ∧ CommitsOfDisseminationAsync U ∧
      CommitsOfReactivePace U ∧ PairDecides U

end Liveness

end BlueBottlePair

end Steelhead

end LeanDag
