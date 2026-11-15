import ProteinFolding.Tetrahedral.ReductionTM2WalkModel
import ProteinFolding.Common.TM2UnaryComparison
import ProteinFolding.Common.TM2Conditional
import ProteinFolding.Cubic.Proofs.VerifierPerfectEquality

/-! Actual polynomial TM2 computation of bounded deterministic graph walks.
The input adjacency test is an actual finite machine. Bounded search and the
folder-local iteration controller account for every repeated test and transfer. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.BoundedWalk

open Computability Turing TM2CompositionPoly TM2ProductMap

variable {P : Type} (ep : FinEncoding P)

def positionsEncoding : FinEncoding (ℕ × ℕ) :=
  pairEncoding unaryFinEncodingNat unaryFinEncodingNat

def progressEncoding : FinEncoding (ℕ × Bool) :=
  pairEncoding unaryFinEncodingNat finEncodingBoolBool

def dataEncoding : FinEncoding ((ℕ × ℕ) × (ℕ × Bool)) :=
  pairEncoding positionsEncoding progressEncoding

noncomputable def parameterComputable :
    TM2ComputableInPolyTime (stateEncoding ep) (pairEncoding ep unaryFinEncodingNat)
      (fun s : State P => s.1) :=
  TM2PairProjections.fstComputable (pairEncoding ep unaryFinEncodingNat) dataEncoding

noncomputable def dataComputable :
    TM2ComputableInPolyTime (stateEncoding ep) dataEncoding (fun s : State P => s.2) :=
  TM2PairProjections.sndComputable (pairEncoding ep unaryFinEncodingNat) dataEncoding

noncomputable def sourceComputable :
    TM2ComputableInPolyTime (stateEncoding ep) ep (fun s : State P => s.1.1) :=
  compose (parameterComputable ep) (TM2PairProjections.fstComputable ep unaryFinEncodingNat)

noncomputable def boundComputable :
    TM2ComputableInPolyTime (stateEncoding ep) unaryFinEncodingNat (fun s : State P => s.1.2) :=
  compose (parameterComputable ep) (TM2PairProjections.sndComputable ep unaryFinEncodingNat)

noncomputable def positionsComputable :
    TM2ComputableInPolyTime (stateEncoding ep) positionsEncoding (fun s : State P => s.2.1) :=
  compose (dataComputable ep) (TM2PairProjections.fstComputable positionsEncoding progressEncoding)

noncomputable def progressComputable :
    TM2ComputableInPolyTime (stateEncoding ep) progressEncoding (fun s : State P => s.2.2) :=
  compose (dataComputable ep) (TM2PairProjections.sndComputable positionsEncoding progressEncoding)

noncomputable def previousComputable :
    TM2ComputableInPolyTime (stateEncoding ep) unaryFinEncodingNat (fun s : State P => s.2.1.1) :=
  compose (positionsComputable ep) (TM2PairProjections.fstComputable unaryFinEncodingNat unaryFinEncodingNat)

noncomputable def currentComputable :
    TM2ComputableInPolyTime (stateEncoding ep) unaryFinEncodingNat (fun s : State P => s.2.1.2) :=
  compose (positionsComputable ep) (TM2PairProjections.sndComputable unaryFinEncodingNat unaryFinEncodingNat)

noncomputable def lengthComputable :
    TM2ComputableInPolyTime (stateEncoding ep) unaryFinEncodingNat (fun s : State P => s.2.2.1) :=
  compose (progressComputable ep) (TM2PairProjections.fstComputable unaryFinEncodingNat finEncodingBoolBool)

noncomputable def finishedComputable :
    TM2ComputableInPolyTime (stateEncoding ep) finEncodingBoolBool (fun s : State P => s.2.2.2) :=
  compose (progressComputable ep) (TM2PairProjections.sndComputable unaryFinEncodingNat finEncodingBoolBool)

variable {adj : P × (ℕ × ℕ) → Bool}

set_option maxHeartbeats 1200000 in
noncomputable def testComputable
    (ha : TM2ComputableInPolyTime (queryEncoding ep) finEncodingBoolBool adj) :
    TM2ComputableInPolyTime (pairEncoding (queryEncoding ep) unaryFinEncodingNat)
      finEncodingBoolBool (test adj) := by
  let hq := TM2PairProjections.fstComputable (queryEncoding ep) unaryFinEncodingNat
  let hj := TM2PairProjections.sndComputable (queryEncoding ep) unaryFinEncodingNat
  let hp := compose hq (TM2PairProjections.fstComputable ep positionsEncoding)
  let hpos := compose hq (TM2PairProjections.sndComputable ep positionsEncoding)
  let hprev := compose hpos (TM2PairProjections.fstComputable unaryFinEncodingNat unaryFinEncodingNat)
  let hcur := compose hpos (TM2PairProjections.sndComputable unaryFinEncodingNat unaryFinEncodingNat)
  let hadj := compose (pairComputable hp (pairComputable hcur hj)) ha
  let heq := compose (pairComputable hj hprev) PerfectUnaryEquality.unaryEqualityComputable
  let hne := compose heq TM2Boolean.notComputable
  have h := compose (pairComputable hadj hne) TM2Boolean.andComputable
  exact changeFunction h (fun q => by simp [test])

set_option maxHeartbeats 1200000 in
noncomputable def nextComputable
    (ha : TM2ComputableInPolyTime (queryEncoding ep) finEncodingBoolBool adj) :
    TM2ComputableInPolyTime (stateEncoding ep) unaryFinEncodingNat (next adj) :=
  compose (pairComputable (pairComputable (sourceComputable ep) (positionsComputable ep))
    (boundComputable ep)) (TM2BoundedSearch.boundedSearchComputable (testComputable ep ha))

set_option maxHeartbeats 1200000 in
noncomputable def advanceComputable
    (ha : TM2ComputableInPolyTime (queryEncoding ep) finEncodingBoolBool adj) :
    TM2ComputableInPolyTime (stateEncoding ep) (stateEncoding ep)
      (fun s : State P => (s.1, ((s.2.1.2, next adj s), (s.2.2.1 + 1, false)))) :=
  pairComputable (parameterComputable ep)
    (pairComputable (pairComputable (currentComputable ep) (nextComputable ep ha))
      (pairComputable (add (lengthComputable ep) (natConstant _ 1))
        (TM2Constants.constantComputable _ finEncodingBoolBool false)))

set_option maxHeartbeats 1200000 in
noncomputable def stopComputable :
    TM2ComputableInPolyTime (stateEncoding ep) (stateEncoding ep)
      (fun s : State P => (s.1, (s.2.1, (s.2.2.1, true)))) :=
  pairComputable (parameterComputable ep)
    (pairComputable (positionsComputable ep)
      (pairComputable (lengthComputable ep) (TM2Constants.constantComputable _ finEncodingBoolBool true)))

set_option maxHeartbeats 1200000 in
noncomputable def stepComputable
    (ha : TM2ComputableInPolyTime (queryEncoding ep) finEncodingBoolBool adj) :
    TM2ComputableInPolyTime (stateEncoding ep) (stateEncoding ep) (step adj) := by
  let hlt := compose (pairComputable (nextComputable ep ha) (boundComputable ep))
    TM2UnaryComparison.ltComputable
  let hm := TM2Conditional.iteComputable hlt (advanceComputable ep ha) (stopComputable ep)
  let h := TM2Conditional.iteComputable (finishedComputable ep) (idComputableInPolyTime _) hm
  exact changeFunction h (fun s => by simp only [Function.comp_def, decide_eq_true_eq, id_eq, step])

/-- Follow an actual adjacency machine a unary number of times. The uniform
linear intermediate-size theorem is independent of the graph's structure. -/
noncomputable def computable
    (ha : TM2ComputableInPolyTime (queryEncoding ep) finEncodingBoolBool adj) :
    TM2ComputableInPolyTime (pairEncoding (stateEncoding ep) unaryFinEncodingNat)
      (stateEncoding ep) (fun x : State P × ℕ => (step adj)^[x.2] x.1) := by
  letI : Inhabited (stateEncoding ep).Γ := ⟨PairSymbol.sep⟩
  exact Iterate.computable (stepComputable ep ha) stateBound (iterate_encoding_bound ep adj)

end ProteinFolding.Tetrahedral.ReductionTM2.BoundedWalk
