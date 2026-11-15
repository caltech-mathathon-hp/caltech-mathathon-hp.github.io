import ProteinFolding.Tetrahedral.CertificatesTM2Semantics

/-! Each original later H-H endpoint contributes once to the concrete
all-suffix machine, including consecutive backbone contacts. -/

namespace ProteinFolding.Tetrahedral.CertificatesTM2Semantics

open scoped BigOperators
open ProteinFolding.TM2WalkCounters
open CertificatesTM2Expansion CertificatesTM2Records CertificatesTM2Pairs

def endpointHit (isA startH : Bool) (c : Counts) (r : Record) : Bool :=
  decide (CertificatesTM2Inspector.cap (totalCounts
    (runCounts c (CertificatesTM2Directions.unitDirections isA r.2))) = 3) &&
      startH && CertificatesTM2Row.labelBit r.1

def rowScore : Bool → Bool → Counts → List Record → ℕ
  | _, _, _, [] => 0
  | isA, startH, c, r :: rs =>
    (endpointHit isA startH c r).toNat +
      rowScore (!isA) startH
        (runCounts c (CertificatesTM2Directions.unitDirections isA r.2)) rs

theorem rowRun_bonds_records (ctx : Row) (bonds : ℕ) (c : Counts)
    (rs : List Record) (hseen : ctx.seen = 0) :
    (CertificatesTM2Row.rowRun ctx bonds c (rs.map some)).bonds =
      bonds + rowScore ctx.phaseA ctx.startH c rs := by
  induction rs generalizing ctx bonds c with
  | nil => simp [CertificatesTM2Row.rowRun, rowScore]
  | cons r rs ih =>
    rw [List.map_cons, CertificatesTM2Row.rowRun, ih _ _ _ (by rfl)]
    simp [rowScore, endpointHit, CertificatesTM2Row.hit, CertificatesTM2Row.nextContext,
      CertificatesTM2Row.afterLetter, CertificatesTM2Row.peekContext,
      CertificatesTM2Row.advance, CertificatesTM2Row.direction, hseen, Nat.add_assoc]

theorem rowScore_eq_sum (isA startH : Bool) (c : Counts) (rs : List Record) :
    rowScore isA startH c rs = ∑ k : Fin rs.length,
      (decide (CertificatesTM2Inspector.cap (totalCounts
        (runCounts c (expandFrom isA ((rs.take (k.val + 1)).map Prod.snd)))) = 3) &&
          startH && CertificatesTM2Row.labelBit (rs.get k).1).toNat := by
  induction rs generalizing isA c with
  | nil => simp [rowScore]
  | cons r rs ih =>
    simp [rowScore, Fin.sum_univ_succ, endpointHit, expandFrom,
      CertificatesTM2Row.runCounts_append, runCounts, ih]

def allPairScore : Bool → List Record → ℕ
  | _, [] => 0
  | previousA, r :: rs =>
    rowScore (!previousA) (CertificatesTM2Row.labelBit r.1) (fun _ => 0) rs +
      allPairScore (!previousA) rs

theorem geometryRun_bonds_records (previousA valid : Bool) (bonds : ℕ) (rs : List Record) :
    (geometryRun previousA valid bonds (rs.map some)).2 =
      bonds + allPairScore previousA rs := by
  induction rs generalizing previousA valid bonds with
  | nil => simp [geometryRun, allPairScore]
  | cons r rs ih =>
    simp only [List.map_cons, geometryRun]
    rw [CertificatesTM2Row.rowRun_startA, ih, rowRun_bonds_records _ _ _ _ (by rfl)]
    simp [allPairScore, rowContext, startLabel, Nat.add_assoc]

theorem bondCountRecords_eq_allPairScore (rs : List Record) :
    bondCountRecords (rs.map some) = allPairScore false rs := by
  simpa [bondCountRecords] using geometryRun_bonds_records false true 0 rs

theorem allPairScore_eq_sum (previousA : Bool) (rs : List Record) :
    allPairScore previousA rs = ∑ i : Fin rs.length,
      rowScore (rowColour previousA i.val) (CertificatesTM2Row.labelBit (rs.get i).1)
        (fun _ => 0) (rs.drop (i.val + 1)) := by
  induction rs generalizing previousA with
  | nil => simp [allPairScore]
  | cons r rs ih =>
    simp [allPairScore, Fin.sum_univ_succ, ih, rowColour_zero, rowColour_succ]

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
    rowScore (decide (i.val % 2 = 0)) (CertificatesTM2Row.labelBit (S.get i))
      (fun _ => 0) (rs.drop (i.val + 1)) =
      ∑ j ∈ (Finset.univ.filter fun j : Fin S.length => i < j),
        if S.get i = .H ∧ S.get j = .H ∧
          tetrahedralLattice.Adj (recordPosition rs i.val) (recordPosition rs j.val)
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
    have hinspect := inspected_suffix_three_iff rs i.val j.val hij hj
    simp only [suffixExpanded, suffixDirections, hprefix] at hinspect
    have hlabel : ((rs.drop (i.val + 1)).get k).1 = S.get j := by
      simp only [List.get_eq_getElem, List.getElem_drop]
      exact record_label_get hlabels j hj
    rw [hlabel]
    simp only [hinspect]
    change (decide (tetrahedralLattice.Adj (recordPosition rs i.val) (recordPosition rs j.val)) &&
      CertificatesTM2Row.labelBit (S.get i) && CertificatesTM2Row.labelBit (S.get j)).toNat =
      if S.get i = .H ∧ S.get j = .H ∧
        tetrahedralLattice.Adj (recordPosition rs i.val) (recordPosition rs j.val) then 1 else 0
    cases hi : S.get i <;> cases hj' : S.get j <;>
      by_cases hadj : tetrahedralLattice.Adj (recordPosition rs i.val) (recordPosition rs j.val) <;>
      simp [CertificatesTM2Row.labelBit, hadj]

theorem allPairScore_labels_sum (S : Sequence) (rs : List Record)
    (hlabels : rs.map Prod.fst = S) :
    allPairScore false rs = ∑ i : Fin S.length,
      rowScore (decide (i.val % 2 = 0)) (CertificatesTM2Row.labelBit (S.get i))
        (fun _ => 0) (rs.drop (i.val + 1)) := by
  rw [allPairScore_eq_sum]
  simp only [rowColour_false]
  apply Fintype.sum_equiv (finCongr (record_labels_length hlabels))
  intro i
  have hlabel := record_label_get hlabels
    ((finCongr (record_labels_length hlabels)) i) i.isLt
  simpa using congrArg (fun r => rowScore (decide (i.val % 2 = 0))
    (CertificatesTM2Row.labelBit r) (fun _ => 0) (rs.drop (i.val + 1))) hlabel

theorem allPairScore_eq_bondCount (S : Sequence) (rs : List Record)
    (hlabels : rs.map Prod.fst = S) (f : Fold tetrahedralLattice S.length)
    (hpos : ∀ i, f.pos i = recordPosition rs i.val) :
    allPairScore false rs = bondCount S f := by
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

theorem bondCountRecords_eq_bondCount (S : Sequence) (rs : List Record)
    (hlabels : rs.map Prod.fst = S) (f : Fold tetrahedralLattice S.length)
    (hpos : ∀ i, f.pos i = recordPosition rs i.val) :
    bondCountRecords (rs.map some) = bondCount S f := by
  rw [bondCountRecords_eq_allPairScore]
  exact allPairScore_eq_bondCount S rs hlabels f hpos

end ProteinFolding.Tetrahedral.CertificatesTM2Semantics
