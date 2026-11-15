import ProteinFolding.Cubic.Proofs.CertificatesBits
import ProteinFolding.Common.TM2WalkInspector

/-! Redundant labelled incoming-direction records for the explicit geometric
verifier. The first incoming direction is padding; all later records carry the
edge from the preceding residue. An inner suffix scan can therefore update the
relative displacement before inspecting the current endpoint.

This does not change the frozen input or problem definitions. Label equality
is an explicit part of certificate validity. -/

namespace ProteinFolding.CubicVerifier

open CubicCertificates

abbrev Record := Residue × Fin 6

def recordsOfDirections (S : Sequence) (ds : DirectionWord) : List Record :=
  List.ofFn fun i : Fin S.length =>
    (S.get i, if i.val = 0 then 0 else ds[i.val - 1]?.getD 0)

theorem recordsOfDirections_length (S : Sequence) (ds : DirectionWord) :
    (recordsOfDirections S ds).length = S.length := by simp [recordsOfDirections]

theorem recordsOfDirections_labels (S : Sequence) (ds : DirectionWord) :
    (recordsOfDirections S ds).map Prod.fst = S := by
  simp [recordsOfDirections, List.map_ofFn, Function.comp_def]

theorem recordsOfDirections_incoming (S : Sequence) (ds : DirectionWord) (k : ℕ)
    (hk : k + 1 < S.length) :
    (((recordsOfDirections S ds)[k + 1]?).map Prod.snd).getD 0 = ds[k]?.getD 0 := by
  simp [recordsOfDirections, hk]

def recordPosition (rs : List Record) : ℕ → Site
  | 0 => fun _ => 0
  | k + 1 => step (recordPosition rs k) (((rs[k + 1]?).map Prod.snd).getD 0)

def incomingDirections (rs : List Record) : List (Fin 6) := (rs.drop 1).map Prod.snd

theorem recordPosition_incoming (rs : List Record) (n : ℕ) :
    recordPosition rs n = walkPosition (incomingDirections rs) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [recordPosition, walkPosition, ih]
    congr 1
    simp [incomingDirections]

theorem step_increment (p : Site) (d : Fin 6) (k : Fin 3) :
    step p d k = p k + TM2WalkCounters.increment d k := by
  match k with
  | 0 => simp only [step, TM2WalkCounters.increment]; split_ifs <;> omega
  | 1 => simp only [step, TM2WalkCounters.increment]; split_ifs <;> omega
  | 2 => simp only [step, TM2WalkCounters.increment]; split_ifs <;> omega

theorem walkPosition_take (ds : DirectionWord) (n : ℕ) (hn : n ≤ ds.length) (k : Fin 3) :
    walkPosition ds n k = TM2WalkCounters.displacement (ds.take n) k := by
  induction n with
  | zero => simp [walkPosition, TM2WalkCounters.displacement]
  | succ n ih =>
    have hlt : n < ds.length := by omega
    rw [walkPosition, step_increment, ih (by omega), List.take_succ_eq_append_getElem hlt,
      TM2WalkCounters.displacement_append]
    simp only [TM2WalkCounters.displacement]
    have he : ds[n]?.getD 0 = ds[n] := by simp [hlt]
    rw [he]
    omega

/-- A zeroed signed-counter scan of records i+1,...,j computes exactly the
displacement between vertices i and j. This is the all-pairs verifier seam. -/
theorem suffix_counter_coordinate (rs : List Record) (i j : ℕ) (hij : i ≤ j)
    (hj : j < rs.length) (k : Fin 3) :
    TM2WalkCounters.coordinate (TM2WalkCounters.runCounts (fun _ => 0)
      (((rs.drop (i + 1)).take (j - i)).map Prod.snd)) k =
        recordPosition rs j k - recordPosition rs i k := by
  have hj' : j ≤ (incomingDirections rs).length := by
    simp only [incomingDirections, List.length_map, List.length_drop]
    omega
  have hi' : i ≤ (incomingDirections rs).length := by omega
  have hsplit : (incomingDirections rs).take j =
      (incomingDirections rs).take i ++ (((rs.drop (i + 1)).take (j - i)).map Prod.snd) := by
    rw [show j = i + (j - i) by omega, List.take_add]
    simp [incomingDirections, ← List.map_take, ← List.map_drop]
  rw [TM2WalkCounters.runCounts_zero_coordinate, recordPosition_incoming rs j,
    recordPosition_incoming rs i, walkPosition_take _ j hj' k,
    walkPosition_take _ i hi' k]
  have hd := congrArg (fun ds => TM2WalkCounters.displacement ds k) hsplit
  dsimp only at hd
  rw [TM2WalkCounters.displacement_append] at hd
  omega

theorem suffix_counter_distance (rs : List Record) (i j : ℕ) (hij : i ≤ j)
    (hj : j < rs.length) :
    TM2WalkCounters.totalCounts (TM2WalkCounters.runCounts (fun _ => 0)
      (((rs.drop (i + 1)).take (j - i)).map Prod.snd)) =
        latticeDistance (recordPosition rs j) (recordPosition rs i) := by
  rw [TM2WalkCounters.totalCounts_eq_manhattan _
    (TM2WalkCounters.runCounts_reduced _ TM2WalkCounters.zero_reduced _)]
  rw [suffix_counter_coordinate rs i j hij hj 0, suffix_counter_coordinate rs i j hij hj 1,
    suffix_counter_coordinate rs i j hij hj 2]
  exact (distance_eq _ _).symm

theorem distance_zero_iff (p q : Site) : latticeDistance p q = 0 ↔ p = q := by
  rw [distance_eq]
  constructor
  · intro h
    apply site_ext <;> omega
  · intro h; subst q; simp

theorem inspected_suffix_zero_iff (rs : List Record) (i j : ℕ) (hij : i ≤ j)
    (hj : j < rs.length) :
    TM2WalkInspector.cap (TM2WalkCounters.totalCounts (TM2WalkCounters.runCounts (fun _ => 0)
      (((rs.drop (i + 1)).take (j - i)).map Prod.snd))) = 0 ↔
        recordPosition rs i = recordPosition rs j := by
  rw [TM2WalkInspector.cap_eq_zero, suffix_counter_distance rs i j hij hj, distance_zero_iff]
  exact eq_comm

theorem inspected_suffix_one_iff (rs : List Record) (i j : ℕ) (hij : i ≤ j)
    (hj : j < rs.length) :
    TM2WalkInspector.cap (TM2WalkCounters.totalCounts (TM2WalkCounters.runCounts (fun _ => 0)
      (((rs.drop (i + 1)).take (j - i)).map Prod.snd))) = 1 ↔
        cubicLattice.Adj (recordPosition rs i) (recordPosition rs j) := by
  rw [TM2WalkInspector.cap_eq_one, suffix_counter_distance rs i j hij hj, latticeDistance_comm]
  rfl

theorem recordPosition_eq_walk (S : Sequence) (ds : DirectionWord) (k : ℕ)
    (hk : k < S.length) :
    recordPosition (recordsOfDirections S ds) k = walkPosition ds k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [recordPosition, walkPosition, ih (by omega), recordsOfDirections_incoming S ds k hk]

def ValidRecords (S : Sequence) (rs : List Record) : Prop :=
  rs.map Prod.fst = S ∧ Function.Injective (fun i : Fin S.length => recordPosition rs i.val)

instance (S : Sequence) (rs : List Record) : Decidable (ValidRecords S rs) :=
  inferInstanceAs (Decidable (_ ∧ (∀ _ _, _ → _)))

def recordFold (S : Sequence) (rs : List Record) : Option (Fold cubicLattice S.length) :=
  if h : ValidRecords S rs then
    some
      { pos := fun i => recordPosition rs i.val
        injective_pos := h.2
        consecutive := by
          intro i j hij
          rw [← hij, recordPosition]
          exact step_adj _ _ }
  else none

theorem recordsOfFold_valid {S : Sequence} (f : Fold cubicLattice S.length) :
    ValidRecords S (recordsOfDirections S (foldDirections f)) := by
  refine ⟨recordsOfDirections_labels S _, ?_⟩
  intro i j hij
  apply (foldDirections_valid f).2.1
  change walkPosition _ i.val = walkPosition _ j.val
  rw [← recordPosition_eq_walk S _ i.val i.isLt,
    ← recordPosition_eq_walk S _ j.val j.isLt]
  exact hij

def RecordsAccept (input : HPInstance × List Record) : Prop :=
  match recordFold input.1.sequence input.2 with
  | none => False
  | some f => input.1.minBonds ≤ (bondCount input.1.sequence f : ℤ)

instance (input : HPInstance × List Record) : Decidable (RecordsAccept input) := by
  unfold RecordsAccept
  split <;> infer_instance

theorem recordFold_complete {S : Sequence} (f : Fold cubicLattice S.length) :
    ∃ g, recordFold S (recordsOfDirections S (foldDirections f)) = some g ∧
      bondCount S g = bondCount S f := by
  have hv := recordsOfFold_valid f
  let g : Fold cubicLattice S.length :=
    { pos := fun i => recordPosition (recordsOfDirections S (foldDirections f)) i.val
      injective_pos := hv.2
      consecutive := by
        intro i j hij
        rw [← hij, recordPosition]
        exact step_adj _ _ }
  refine ⟨g, by simp [recordFold, hv, g], ?_⟩
  by_cases h : 0 < S.length
  · have he : g = shiftFold f (f.pos ⟨0, h⟩) := by
      apply fold_ext
      funext i
      exact (recordPosition_eq_walk S _ i.val i.isLt).trans
        (walkPosition_foldDirections f h i.val i.isLt)
    rw [he, bondCount_shift]
  · have he : g = f := by
      apply fold_ext
      funext i
      have := i.isLt
      omega
    rw [he]

theorem recordsAccept_sound (I : HPInstance) (rs : List Record)
    (h : RecordsAccept (I, rs)) : I.Accepts := by
  unfold RecordsAccept at h
  split at h
  · exact False.elim h
  · exact ⟨_, h⟩

theorem hp_records_certificate_iff (I : HPInstance) :
    I.Accepts ↔ ∃ rs : List Record, rs.length = I.sequence.length ∧ RecordsAccept (I, rs) := by
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨g, hg, hscore⟩ := recordFold_complete f
    refine ⟨recordsOfDirections I.sequence (foldDirections f), recordsOfDirections_length _ _, ?_⟩
    simp only [RecordsAccept]
    rw [hg]
    simpa [hscore] using hf
  · rintro ⟨rs, _, hr⟩
    exact recordsAccept_sound I rs hr

def labelBit : Residue → Bool
  | .H => true
  | .P => false

def encodeRecord (r : Record) : List Bool := labelBit r.1 :: encodeDirection r.2

def encodeRecords (rs : List Record) : List Bool := rs.flatMap encodeRecord

theorem encodeRecord_length (r : Record) : (encodeRecord r).length = 4 := by
  obtain ⟨r, d⟩ := r
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 => rfl

theorem encodeRecords_length (rs : List Record) : (encodeRecords rs).length = 4 * rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [encodeRecords, List.flatMap_cons, List.length_append, encodeRecord_length,
      List.length_cons, Nat.mul_succ]
    change 4 + (encodeRecords rs).length = 4 * rs.length + 4
    omega

end ProteinFolding.CubicVerifier
