import LeanDagTest

/-!
Prints the blocks of the witnesses the presentation draws, as a JavaScript
file assigning `window.WITNESSES`. Run from the repository root:

    lake env lean presentation/tools/ExportWitnesses.lean > presentation/witnesses.js
-/

open LeanDag

/-- One block as a JSON object: id, round, creator, sorted references, and
optional extra fields. -/
def blockJson {V B P : Type} [LinearOrder B] (vNat : V → ℕ) (bNat : B → ℕ)
    (extra : P → String) (i : B) (b : Block V B P) : String :=
  let refs := (b.refs.sort (· ≤ ·)).map bNat
  s!"\{\"id\":{bNat i},\"r\":{b.round},\"v\":{vNat b.creator},\"refs\":{refs}{extra b.payload}}"

/-- A witness: its validator count and its blocks, sorted by id. -/
def witnessJson {V B P : Type} [LinearOrder B] (name : String) (n : ℕ) (vNat : V → ℕ)
    (bNat : B → ℕ) (ids : Finset B) (blk : B → Block V B P)
    (extra : P → String := fun _ => "") : String :=
  let bs := (ids.sort (· ≤ ·)).map fun i => blockJson vNat bNat extra i (blk i)
  s!"\"{name}\":\{\"n\":{n},\"blocks\":[{",".intercalate bs}]}"

def finW {n m : ℕ} {P : Type} (name : String) (ids : Finset (Fin m))
    (blk : Fin m → Block (Fin n) (Fin m) P) (extra : P → String := fun _ => "") : String :=
  witnessJson name n (·.val) (·.val) ids blk extra

def natW {n : ℕ} {P : Type} (name : String) (ids : Finset ℕ)
    (blk : ℕ → Block (Fin n) ℕ P) (extra : P → String := fun _ => "") : String :=
  witnessJson name n (·.val) id ids blk extra

/-- Bluestreak's payload: the leader tag and the claim. -/
def bsExtra {m : ℕ} (p : Bool × Option (Fin m)) : String :=
  s!",\"tag\":{p.1},\"claim\":{match p.2 with | some c => toString c.val | none => "null"}"

def bsExtraNat (p : Bool × Option ℕ) : String :=
  s!",\"tag\":{p.1},\"claim\":{match p.2 with | some c => toString c | none => "null"}"

/-- A Red Snapper witness: its blocks use `author` and `parents`. -/
def rsW {m : ℕ} {Tx Obj : Type} (name : String)
    (ids : Finset (Fin m)) (blk : Fin m → LeanDag.RedSnapper.Block (Fin 4) (Fin m) Tx Obj) : String :=
  let bs := (ids.sort (· ≤ ·)).map fun i =>
    let b := blk i
    s!"\{\"id\":{i.val},\"r\":{b.round},\"v\":{b.author.val},\"refs\":{(b.parents.sort (· ≤ ·)).map (·.val)}}"
  s!"\"{name}\":\{\"n\":4,\"blocks\":[{",".intercalate bs}]}"

def entries : List String := [
  finW "U3" U3.ids U3.block,
  finW "U7" U7.ids U7.block,
  natW "Ugrow6" (LeanDagTest.Ugrow 6).ids (LeanDagTest.Ugrow 6).block,
  natW "Ugrow8" (LeanDagTest.Ugrow 8).ids (LeanDagTest.Ugrow 8).block,
  finW "Unemo" LeanDagTest.Unemo.ids LeanDagTest.Unemo.block,
  finW "Ush" LeanDagTest.NemoShadow.Ush.ids LeanDagTest.NemoShadow.Ush.block,
  finW "Uskip" LeanDagTest.Uskip.ids LeanDagTest.Uskip.block,
  finW "Utwin6" LeanDagTest.Utwin6.ids LeanDagTest.Utwin6.block,
  finW "UhybX" LeanDagTest.Barnacle.OrcaellaIndirect.UhybX.ids
    LeanDagTest.Barnacle.OrcaellaIndirect.UhybX.block,
  finW "Uhyb4" LeanDagTest.Uhyb4.ids LeanDagTest.Uhyb4.block,
  finW "U5orc" LeanDagTest.Barnacle.OrcaellaIndirect.U5.ids
    LeanDagTest.Barnacle.OrcaellaIndirect.U5.block,
  finW "UtightA" LeanDagTest.UtightA.ids LeanDagTest.UtightA.block,
  finW "UtightB" LeanDagTest.UtightB.ids LeanDagTest.UtightB.block,
  finW "Dfast" LeanDagTest.FinWhale.Dfast.ids LeanDagTest.FinWhale.Dfast.block,
  finW "Dequiv" LeanDagTest.FinWhale.Dequiv.ids LeanDagTest.FinWhale.Dequiv.block,
  finW "Dbare" LeanDagTest.FinWhale.Dbare.ids LeanDagTest.FinWhale.Dbare.block,
  finW "U4hz" LeanDagTest.Hydrozoan.U4.ids LeanDagTest.Hydrozoan.U4.block,
  finW "UE" LeanDagTest.OptimalHydrozoan.UE.ids LeanDagTest.OptimalHydrozoan.UE.block,
  finW "BsU1" LeanDagTest.U1.ids LeanDagTest.U1.block bsExtra,
  finW "BsU2" LeanDagTest.U2.ids LeanDagTest.U2.block bsExtra,
  finW "twin4" LeanDagTest.twin4.ids LeanDagTest.twin4.block,
  finW "aim4" LeanDagTest.aim4.ids LeanDagTest.aim4.block,
  finW "aim6" LeanDagTest.aim6.ids LeanDagTest.aim6.block,
  finW "twin6" LeanDagTest.twin6.ids LeanDagTest.twin6.block,
  finW "hazard6" LeanDagTest.hazard6.ids LeanDagTest.hazard6.block,
  finW "st20" LeanDagTest.st20.ids LeanDagTest.st20.block,
  finW "Dpart" LeanDagTest.Minnow.Dpart.ids LeanDagTest.Minnow.Dpart.block,
  finW "Dfull" LeanDagTest.Minnow.Dfull.ids LeanDagTest.Minnow.Dfull.block,
  finW "Dm" LeanDagTest.Minnow.Dm.ids LeanDagTest.Minnow.Dm.block,
  finW "Ds" LeanDagTest.Minnow.Ds.ids LeanDagTest.Minnow.Ds.block,
  finW "Udiv" LeanDagTest.BlackMarlin.Udiv.ids LeanDagTest.BlackMarlin.Udiv.block,
  finW "Uexcl" LeanDagTest.Uexcl.ids LeanDagTest.Uexcl.block,
  finW "Ucens" LeanDagTest.Ucens.ids LeanDagTest.Ucens.block,
  finW "Udouble" LeanDagTest.Udouble.ids LeanDagTest.Udouble.block,
  natW "Ucrash2" (LeanDagTest.Ucrash 2).ids (LeanDagTest.Ucrash 2).block,
  natW "Ucrash4" (LeanDagTest.Ucrash 4).ids (LeanDagTest.Ucrash 4).block,
  natW "UcrashFill" (LeanDagTest.ucrashMsg 4 4 (by omega)).skipFill.ids
    (LeanDagTest.ucrashMsg 4 4 (by omega)).skipFill.block,
  natW "Ucut" LeanDagTest.Ucut.ids LeanDagTest.Ucut.block,
  natW "Uregen" LeanDagTest.Uregen.ids LeanDagTest.Uregen.block,
  natW "Urecover" LeanDagTest.urecover.skipFill.ids LeanDagTest.urecover.skipFill.block,
  finW "UexclCut" (chop LeanDagTest.Uexcl 2).ids (chop LeanDagTest.Uexcl 2).block,
  natW "Ucr" LeanDagTest.Recovery.Ucr.ids LeanDagTest.Recovery.Ucr.block bsExtraNat,
  natW "Ufill" LeanDagTest.Recovery.Ufill.ids LeanDagTest.Recovery.Ufill.block bsExtraNat,
  finW "Usun" LeanDagTest.Barnacle.Usun.ids LeanDagTest.Barnacle.Usun.block,
  rsW "ULive" LeanDagTest.RedSnapper.ULive.ids LeanDagTest.RedSnapper.ULive.block,
  rsW "UTri" LeanDagTest.RedSnapper.UTri.ids LeanDagTest.RedSnapper.UTri.block
]

/-- Round-entry times of the drift-collapse witness `ugrowLag`, rounds 0–5. -/
def lagTimes : String :=
  let rows := (List.finRange 4).map fun v =>
    toString ((List.range 6).map fun n => LeanDagTest.lagBuilt v n)
  s!"\"lagBuilt\":[{",".intercalate rows}]"

#eval IO.println ("// Generated by presentation/tools/ExportWitnesses.lean. Do not edit.\n" ++
  "window.WITNESSES = {\n" ++ ",\n".intercalate (entries ++ [lagTimes]) ++ "\n};")
