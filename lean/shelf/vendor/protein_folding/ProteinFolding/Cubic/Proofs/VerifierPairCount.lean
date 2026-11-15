import ProteinFolding.Cubic.Proofs.VerifierGeometry

/-! Semantic scoring for the concrete all-suffix verifier. Every later H-H
adjacent endpoint contributes once, including consecutive sequence positions. -/

namespace ProteinFolding.CubicVerifier

open scoped BigOperators
open TM2WalkCounters

def endpointHit (startH : Bool) (c : Counts) (r : Record) : Bool :=
  decide (TM2WalkInspector.cap (totalCounts (updateCounts c r.2)) = 1) &&
    startH && labelBit r.1

def rowScore : Bool → Counts → List Record → ℕ
  | _, _, [] => 0
  | startH, c, r :: rs =>
    (endpointHit startH c r).toNat + rowScore startH (updateCounts c r.2) rs

theorem rowRun_bonds_records (ctx : Row.Context) (bonds : ℕ) (c : Counts)
    (rs : List Record) (hseen : ctx.seen = 0) :
    (Row.rowRun ctx bonds c (rs.map some)).bonds = bonds + rowScore ctx.startH c rs := by
  induction rs generalizing ctx bonds c with
  | nil => simp [Row.rowRun, rowScore]
  | cons r rs ih =>
    rw [List.map_cons, Row.rowRun]
    rw [ih _ _ _ (by rfl)]
    simp [rowScore, endpointHit, Row.hit, Row.nextContext, Row.afterLetter, Row.peekContext,
      Row.direction, hseen, Nat.add_assoc]

theorem rowScore_eq_sum (startH : Bool) (c : Counts) (rs : List Record) :
    rowScore startH c rs = ∑ k : Fin rs.length,
      (decide (TM2WalkInspector.cap
        (totalCounts (runCounts c ((rs.take (k.val + 1)).map Prod.snd))) = 1) &&
        startH && labelBit (rs.get k).1).toNat := by
  induction rs generalizing c with
  | nil => simp [rowScore]
  | cons r rs ih =>
    simp [rowScore, Fin.sum_univ_succ, endpointHit, runCounts, ih]

def allPairScore : List Record → ℕ
  | [] => 0
  | r :: rs => rowScore (labelBit r.1) (fun _ => 0) rs + allPairScore rs

theorem geometryRun_bonds_records (valid : Bool) (bonds : ℕ) (rs : List Record) :
    (geometryRun valid bonds (rs.map some)).2 = bonds + allPairScore rs := by
  induction rs generalizing valid bonds with
  | nil => simp [geometryRun, allPairScore]
  | cons r rs ih =>
    simp only [List.map_cons, geometryRun]
    rw [ih, rowRun_bonds_records _ _ _ _ (by rfl)]
    simp [allPairScore, rowContext, startLabel, Nat.add_assoc]

theorem bondCountRecords_eq_allPairScore (rs : List Record) :
    bondCountRecords (rs.map some) = allPairScore rs := by
  simpa [bondCountRecords] using geometryRun_bonds_records true 0 rs

theorem allPairScore_eq_sum (rs : List Record) :
    allPairScore rs = ∑ i : Fin rs.length,
      rowScore (labelBit (rs.get i).1) (fun _ => 0) (rs.drop (i.val + 1)) := by
  induction rs with
  | nil => simp [allPairScore]
  | cons r rs ih => simp [allPairScore, Fin.sum_univ_succ, ih]

theorem record_labels_length {S : Sequence} {rs : List Record}
    (hlabels : rs.map Prod.fst = S) : rs.length = S.length := by
  simpa using congrArg List.length hlabels

theorem record_label_get {S : Sequence} {rs : List Record}
    (hlabels : rs.map Prod.fst = S) (j : Fin S.length) (hj : j.val < rs.length) :
    (rs.get ⟨j.val, hj⟩).1 = S.get j := by
  have h := congrArg (fun xs : List Residue => xs[j.val]?) hlabels
  simpa [List.getElem?_eq_getElem, j.isLt, hj] using h

theorem rowScore_suffix_eq_sum (S : Sequence) (rs : List Record)
    (hlabels : rs.map Prod.fst = S) (i : Fin S.length) :
    rowScore (labelBit (S.get i)) (fun _ => 0) (rs.drop (i.val + 1)) =
      ∑ j ∈ (Finset.univ.filter fun j : Fin S.length => i < j),
        if S.get i = .H ∧ S.get j = .H ∧
          cubicLattice.Adj (recordPosition rs i.val) (recordPosition rs j.val)
        then 1 else 0 := by
  have hlen := record_labels_length hlabels
  rw [rowScore_eq_sum]
  let toIndex : Fin (rs.drop (i.val + 1)).length → Fin S.length := fun k =>
    ⟨i.val + 1 + k.val, by have hk := k.isLt; simp only [List.length_drop] at hk; omega⟩
  apply Finset.sum_bij (fun k _ => toIndex k)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val]
    dsimp [toIndex]
    omega
  · intro k hk l hl hkl
    apply Fin.ext
    have h := congrArg Fin.val hkl
    dsimp [toIndex] at h
    omega
  · intro j hj
    have hij : i.val < j.val := (Finset.mem_filter.mp hj).2
    let k : Fin (rs.drop (i.val + 1)).length := ⟨j.val - (i.val + 1), by
      simp only [List.length_drop]
      have := j.isLt
      omega⟩
    refine ⟨k, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    dsimp [toIndex, k]
    omega
  · intro k hk
    let j := toIndex k
    have hj : j.val < rs.length := by have := j.isLt; omega
    have hij : i.val ≤ j.val := by dsimp [j, toIndex]; omega
    have hprefix : j.val - i.val = k.val + 1 := by dsimp [j, toIndex]; omega
    have hinspect := inspected_suffix_one_iff rs i.val j.val hij hj
    rw [hprefix] at hinspect
    have hlabel : ((rs.drop (i.val + 1)).get k).1 = S.get j := by
      simp only [List.get_eq_getElem, List.getElem_drop]
      exact record_label_get hlabels j hj
    rw [hlabel]
    simp only [hinspect]
    change (decide (cubicLattice.Adj (recordPosition rs i.val) (recordPosition rs j.val)) &&
      labelBit (S.get i) && labelBit (S.get j)).toNat =
      if S.get i = .H ∧ S.get j = .H ∧
        cubicLattice.Adj (recordPosition rs i.val) (recordPosition rs j.val) then 1 else 0
    cases hi : S.get i <;> cases hj' : S.get j <;>
      by_cases hadj : cubicLattice.Adj (recordPosition rs i.val) (recordPosition rs j.val) <;>
      simp [labelBit, hadj]

theorem allPairScore_labels_sum (S : Sequence) (rs : List Record)
    (hlabels : rs.map Prod.fst = S) :
    allPairScore rs = ∑ i : Fin S.length,
      rowScore (labelBit (S.get i)) (fun _ => 0) (rs.drop (i.val + 1)) := by
  rw [allPairScore_eq_sum]
  apply Fintype.sum_equiv (finCongr (record_labels_length hlabels))
  intro i
  have hlabel := record_label_get hlabels
    ((finCongr (record_labels_length hlabels)) i) i.isLt
  simpa using congrArg (fun r => rowScore (labelBit r) (fun _ => 0)
    (rs.drop (i.val + 1))) hlabel

theorem allPairScore_eq_bondCount (S : Sequence) (rs : List Record)
    (hlabels : rs.map Prod.fst = S) (f : Fold cubicLattice S.length)
    (hpos : ∀ i, f.pos i = recordPosition rs i.val) :
    allPairScore rs = bondCount S f := by
  rw [allPairScore_labels_sum S rs hlabels]
  simp_rw [rowScore_suffix_eq_sum S rs hlabels]
  unfold bondCount hhBonds
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hpos i, hpos j]
  by_cases hij : i < j <;> simp [hij]

theorem recordFold_bondCountRecords (S : Sequence) (rs : List Record)
    (f : Fold cubicLattice S.length) (hf : recordFold S rs = some f) :
    bondCountRecords (rs.map some) = bondCount S f := by
  unfold recordFold at hf
  split at hf
  · rename_i hv
    cases Option.some.inj hf
    rw [bondCountRecords_eq_allPairScore]
    exact allPairScore_eq_bondCount S rs hv.1 _ (fun _ => rfl)
  · cases hf

end ProteinFolding.CubicVerifier
