import LeanDag.Adaptive.Run

/-!
# Liveness: the adaptive fixpoint exists

Safety (`adaptiveRun_agree`) is uniqueness of the run; this file is
existence, under the standard interface — `SynchronisedOn` and
`Populated`, exactly as the base liveness consumes them, both untouched
by reassignment since neither mentions a leader — plus the one clause
that prices the policy's choices: `PlacesRuns`, the adaptive counterpart
of `FairRunOn`. Every assignment the policy can emit must contain, in
each epoch after the first, `c` consecutive `T`-led slots. Hammerhead's
purpose lands on this clause: a policy that reacts to observed skips
satisfies it by construction where a blind rotation satisfies it by
assumption — but which validators are reliable is not the designer's to
know, so it remains a joint condition exactly as P10 is.

The construction is by strong recursion on epochs, one instantiation of
the base machinery per epoch and nothing counted anew. The run that
`PlacesRuns` puts in epoch `e + 1` commits directly (L4 at the induced
instance, bounded trivially), and the bounded restatement of the
committed-run descent — whose proof is the base one with the anchor's
bound carried through — decides every slot below the run with anchors at
or below the run's top, strictly inside epoch `e`'s window. Partial runs
at every height glue into a total run along the diagonal, with
`partialRun_agree` supplying the coherence that the stage-by-stage
choices need not.

Every statement is on a validator's own view, caught up to the horizon
(`View.CoversUpto`) — the view whose `DirectCommitIn` the run's verdicts
are derived in, and the view its schedule is computed on. The full view
is caught up to every horizon (`View.coversUpto_full`), so the
whole-universe reading is the special case; under eventual DAG synchrony
(`liveness.md` §4.2) every correct validator's view is caught up once
delivery has reached the horizon, which is what makes the statement one
about validators.

The witnessable form is `exists_partialRun`, whose growth hypothesis is
a horizon like every base liveness statement's; the total run
(`adaptiveRun_exists`) needs the DAG populated at every round and the
view caught up to every horizon, as it must — a total run decides every
slot there is.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]

/-- **The committed-run descent, bounded.** The base
`decided_below_of_committed_run`, restated with the anchors' bound in
the conclusion: the derivation the base proof builds already anchors at
or below the run's top, so carrying `n + 1` through is a restatement,
not a new argument. -/
theorem decidedWithin_below_of_committed_run
    {V : View Validator BlockId Payload U} {b n : ℕ} (hbn : b ≤ n)
    (hspan : ∀ i, i < b → Eligible Validator i n)
    (hrun : ∀ j, b ≤ j → j ≤ n → ∃ B', DecidedWithin U V (n + 1) j (some B')) :
    ∀ i, i < b → ∃ v, DecidedWithin U V (n + 1) i v := by
  classical
  have key : ∀ d i, i < b → b - i ≤ d → ∃ v, DecidedWithin U V (n + 1) i v := by
    intro d
    induction d with
    | zero => intro i hi hd; omega
    | succ d ih =>
      intro i hi hd
      have hex : ∃ j, Eligible Validator i j ∧
          ∃ B', DecidedWithin U V (n + 1) j (some B') :=
        ⟨n, hspan i hi, hrun n hbn (le_refl n)⟩
      have hle : Nat.find hex ≤ n :=
        Nat.find_le ⟨hspan i hi, hrun n hbn (le_refl n)⟩
      obtain ⟨helig, B', hB⟩ := Nat.find_spec hex
      have hmid : ∀ i', i < i' → i' < Nat.find hex → Eligible Validator i i' →
          DecidedWithin U V (n + 1) i' none := by
        intro i' h1 h2 h3
        have hnc : ¬ ∃ C, DecidedWithin U V (n + 1) i' (some C) :=
          fun hc => Nat.find_min hex h2 ⟨h3, hc⟩
        have hi'b : i' < b := by
          by_contra hge
          exact hnc (hrun i' (by omega) (by omega))
        obtain ⟨v, hv⟩ := ih i' hi'b (by omega)
        cases v with
        | none => exact hv
        | some C => exact absurd ⟨C, hv⟩ hnc
      by_cases hc : ∃ L, IsLeaderBlock U i L ∧ CertifiedIn U B' L (S.slotRound i)
      · obtain ⟨L, hL, hcert⟩ := hc
        exact ⟨some L, DecidedWithin.indirectCommit (lt_of_eligible helig)
          (by omega) helig hB hmid hL hcert⟩
      · push Not at hc
        exact ⟨none, DecidedWithin.indirectSkip (lt_of_eligible helig)
          (by omega) helig hB hmid hc⟩
  intro i hi
  exact key (b - i) i hi (le_refl _)

/-- **The adaptive fairness clause.** Every assignment the policy can
emit places, in each epoch past the base prefix, a run of `c`
consecutive `T`-led slots. The clause liveness prices and safety never
sees: `adaptiveRun_agree` holds for policies that violate it. -/
def PlacesRuns (P : AdaptivePolicy Validator BlockId Payload)
    (T : Finset Validator) (c : ℕ) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
    (v : ℕ → Option BlockId) (e : ℕ),
    ∃ b, P.W * (e + 1) ≤ b ∧ b + c ≤ P.W * (e + 2) ∧
      ∀ i, i < c → P.pick U V v (b + i) ∈ T

omit [Fintype Validator] [DecidableEq Validator] F [DecidableEq BlockId] in
/-- Eligibility reads only the round structure, which reassignment fixes:
the spanning property transfers to every induced instance verbatim. -/
theorem spansEligible_slotsOf {hinj : Function.Injective S.slotRound}
    {a : ℕ → Validator} {c : ℕ}
    (h : SpansEligible (Validator := Validator) c) :
    SpansEligible (Validator := Validator) (S := slotsOf hinj a) c := h

section Existence

variable {P : AdaptivePolicy Validator BlockId Payload}
variable {T : Finset Validator} {c R N : ℕ}

/-- **One epoch closes.** On a view caught up to the horizon, against
the schedule an arbitrary verdict function induces, every slot of epoch
`E` is decided inside its window: the run `PlacesRuns` puts in epoch
`E + 1` commits directly — its certificates sit under the horizon, so
the view holds them — and the bounded descent clears everything below
it. -/
theorem epoch_closes (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : SpansEligible (Validator := Validator) c)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound P.W)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    (V : View Validator BlockId Payload U) (hcov : V.CoversUpto N)
    (v : ℕ → Option BlockId) (E : ℕ)
    (hN : S.slotRound (P.W * (E + 2)) + 2 ≤ N) :
    ∀ k, epochOf P.W k < E + 1 →
      ∃ w, DecidedWithin (S := slotsOf P.inj (fun m => P.pick U V v m)) U
        V (P.W * (E + 2)) k w := by
  obtain ⟨b, hb1, hb2, hbT⟩ := hruns U V v E
  have hWpos := P.W_pos
  -- Every run slot is directly committed, inside the window.
  have hrun : ∀ j, b ≤ j → j ≤ b + c - 1 →
      ∃ B', DecidedWithin (S := slotsOf P.inj (fun m => P.pick U V v m)) U
        V (b + c - 1 + 1) j (some B') := by
    intro j hj1 hj2
    have hlead : (slotsOf P.inj (fun m => P.pick U V v m)).leader j ∈ T := by
      have := hbT (j - b) (by omega)
      rw [slotsOf_leader]
      have hjb : b + (j - b) = j := by omega
      rwa [hjb] at this
    have hWle : P.W ≤ j := by
      have h1 : P.W * 1 ≤ P.W * (E + 1) := Nat.mul_le_mul_left P.W (by omega)
      omega
    have hRj : R ≤ S.slotRound j := le_trans hRW (S.mono hWle)
    have hround : S.slotRound j + 2 ≤ N := by
      have hj3 : j ≤ P.W * (E + 2) := by omega
      have := S.mono hj3
      omega
    obtain ⟨L, hL, hdc⟩ :=
      directCommit_of_leader_mem (S := slotsOf P.inj (fun m => P.pick U V v m))
        hcard hs hRj
        (hpop _ (by omega) (by omega))
        (hpop _ (by omega) (by omega))
        (hpop _ (by omega) (by omega)) hlead
    exact ⟨L, DecidedWithin.directCommit
      (S := slotsOf P.inj (fun m => P.pick U V v m)) (by omega) hL
      (directCommitIn_of_coversUpto hdc (hcov.mono hround))⟩
  -- The bounded descent clears everything below the run — all of epoch `E`.
  have hbelow :=
    decidedWithin_below_of_committed_run (V := V)
      (S := slotsOf P.inj (fun m => P.pick U V v m))
      (b := b) (n := b + c - 1) (by omega)
      (fun i hi => spansEligible_slotsOf hspans b i hi) hrun
  intro k hk
  have hkb : k < b :=
    lt_of_lt_of_le ((epochOf_lt_iff hWpos).mp hk) hb1
  obtain ⟨w, hw⟩ := hbelow k hkb
  exact ⟨w, DecidedWithin.mono (S := slotsOf P.inj (fun m => P.pick U V v m))
    hw (by omega)⟩

/-- **Partial runs exist at every height** — the witnessable, finite-
horizon form of existence, on a view caught up to the horizon, by
induction on the height: each stage re-reads the schedule off the
verdicts so far and closes one more epoch. -/
theorem exists_partialRun (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : SpansEligible (Validator := Validator) c)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound P.W)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    (V : View Validator BlockId Payload U) (hcov : V.CoversUpto N) (E : ℕ)
    (hN : S.slotRound (P.W * (E + 1)) + 2 ≤ N) :
    Nonempty (PartialRun P U V E) := by
  classical
  revert hN
  induction E with
  | zero =>
      intro hN
      exact ⟨{ assign := fun m => P.pick U V (fun _ => none) m
               vdct := fun _ => none
               closed := fun k hk => absurd hk (by omega)
               coherent := fun _ _ => rfl }⟩
  | succ E ih =>
      intro hN
      have hNprev : S.slotRound (P.W * (E + 1)) + 2 ≤ N := by
        have hmul : P.W * (E + 1) ≤ P.W * (E + 1 + 1) :=
          Nat.mul_le_mul_left P.W (by omega)
        have := S.mono hmul
        omega
      obtain ⟨R₀⟩ := ih hNprev
      have hclose := epoch_closes hT hcard hc hruns hspans hs hRW hpop
        V hcov R₀.vdct E hN
      -- The new verdicts: epoch `E` freshly decided, everything below kept.
      set v' : ℕ → Option BlockId := fun k =>
        if h : epochOf P.W k = E then (hclose k (by omega)).choose
        else R₀.vdct k with hv'
      -- The new verdicts agree with the old below epoch `E`.
      have hagree : ∀ j, epochOf P.W j < E → v' j = R₀.vdct j := by
        intro j hj
        simp only [hv', dif_neg (by omega : ¬ epochOf P.W j = E)]
      -- The two induced schedules agree below epoch `E + 2`.
      have hsched : ∀ m, m < P.W * (E + 2) →
          P.pick U V R₀.vdct m = P.pick U V v' m := by
        intro m hm
        refine P.adapted U V V R₀.vdct v' m (fun j hj => ?_)
        have hjE : epochOf P.W j < E := by
          have := (epochOf_lt_iff P.W_pos).mpr hm
          omega
        exact (hagree j hjE).symm
      refine ⟨{ assign := fun m => P.pick U V v' m
                vdct := v'
                closed := ?_
                coherent := fun _ _ => rfl }⟩
      intro k hk
      by_cases hkE : epochOf P.W k = E
      · -- The fresh epoch: transport its derivation across the schedules.
        have hspec := (hclose k (by omega)).choose_spec
        have : v' k = (hclose k (by omega)).choose := by
          simp only [hv', dif_pos hkE]
        rw [this, hkE]
        exact decidedWithin_congr (fun m hm => hsched m hm) hspec
      · -- An old epoch: transport the old derivation.
        have hkE' : epochOf P.W k < E := by omega
        have hold := R₀.closed k hkE'
        have hsched' : ∀ m, m < P.W * (epochOf P.W k + 2) →
            R₀.assign m = P.pick U V v' m := by
          intro m hm
          have hmE : epochOf P.W m < epochOf P.W k + 2 :=
            (epochOf_lt_iff P.W_pos).mpr hm
          rw [R₀.coherent m (by omega)]
          refine P.adapted U V V R₀.vdct v' m (fun j hj => ?_)
          exact (hagree j (by omega)).symm
        have := decidedWithin_congr hsched' hold
        rw [hagree k hkE']
        exact this

/-- **AL5: the adaptive fixpoint exists.** On a DAG synchronised over a
quorum of reliable validators and populated at every round, under a
policy that places runs, a total adaptive run exists on every view
caught up to every horizon — the full view, up to naming, since a total
run decides every slot there is — partial runs at every height glued
along the diagonal, `partialRun_agree` making the stage-by-stage choices
cohere. With `adaptiveRun_agree` it is THE fixpoint: adaptive Mysticeti
decides every slot, and uniquely. -/
theorem adaptiveRun_exists (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : SpansEligible (Validator := Validator) c)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound P.W)
    (hpop : ∀ r, Populated U r)
    (V : View Validator BlockId Payload U) (hcov : ∀ N, V.CoversUpto N) :
    Nonempty (AdaptiveRun P U V) := by
  classical
  -- A partial run at every height, chosen arbitrarily.
  have hex : ∀ E, Nonempty (PartialRun P U V E) := fun E =>
    exists_partialRun hT hcard hc hruns hspans hs hRW
      (N := S.slotRound (P.W * (E + 1)) + 2) (fun r _ _ => PopulatedOn.mono hT (hpop r))
      V (hcov _) E (le_refl _)
  set Rs : ∀ E, PartialRun P U V E :=
    fun E => (hex E).some with hRs
  -- The diagonal: each slot's verdict read from the first height above it.
  set vd : ℕ → Option BlockId := fun k => (Rs (epochOf P.W k + 1)).vdct k with hvd
  -- Any stage's verdicts agree with the diagonal on the epochs it closed.
  have hdiag : ∀ E j, epochOf P.W j < E → (Rs E).vdct j = vd j := by
    intro E j hj
    exact partialRun_agree (Rs E) (Rs (epochOf P.W j + 1)) j (by omega)
  refine ⟨{ assign := fun m => P.pick U V vd m
            vdct := vd
            closed := ?_
            coherent := fun _ => rfl }⟩
  intro k
  have hclosed := (Rs (epochOf P.W k + 1)).closed k (by omega)
  refine decidedWithin_congr (fun m hm => ?_) hclosed
  have hmE : epochOf P.W m < epochOf P.W k + 2 := (epochOf_lt_iff P.W_pos).mpr hm
  rw [(Rs (epochOf P.W k + 1)).coherent m (by omega)]
  refine P.adapted U V V (Rs (epochOf P.W k + 1)).vdct vd m (fun j hj => ?_)
  exact hdiag _ j (by omega)

end Existence

end LeanDag
