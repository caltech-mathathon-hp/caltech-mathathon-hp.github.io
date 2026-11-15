import ProteinFolding.Cubic.Proofs.PackingGeometryBlockOccurrences

/-! The actual anchor blocks after the frame prefix: each wall unit contributes
short, long, short E blocks, and the final gap word contributes one E₂ block
per unit. Their literal sequence intervals are pairwise disjoint. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicPacking
open scoped BigOperators

abbrev FrameBlock (q : ℕ) := Fin q × Fin 4

def frameBlockKind {q : ℕ} (b : FrameBlock q) : AnchorKind :=
  if b.2 = 1 then .long else if b.2 = 3 then .gap else .short

def wallUnits (q Q : ℕ) : Sequence :=
  separatedCopies (wallUnit q Q) (List.replicate (2 * alpha Q) .P) q

def wallStride (q Q : ℕ) : ℕ := 8 * alpha Q + 3 * beta Q + 4 * depth q Q

def wallInnerOffset (q Q : ℕ) (k : Fin 3) : ℕ :=
  if k = 0 then 0 else if k = 1 then 3 * alpha Q + 2 * depth q Q
  else 3 * alpha Q + 3 * beta Q + 4 * depth q Q

def frameBlockOffset (q Q : ℕ) (b : FrameBlock q) : ℕ :=
  (prefixWord q Q).length +
    if h : b.2.val < 3 then b.1.val * wallStride q Q + wallInnerOffset q Q ⟨b.2.val, h⟩
    else (wallUnits q Q).length + b.1.val * (2 * alpha Q + 10)

theorem wallUnit_edge_occurrence (q Q : ℕ) (k : Fin 3) :
    ∃ o : EdgeOccurrence (wallUnit q Q) (if k = 1 then beta Q else alpha Q),
      o.pre.length = wallInnerOffset q Q k := by
  fin_cases k
  · refine ⟨⟨[], faceWord (depth q Q) ++ edgeWord (beta Q) ++
      faceWord (depth q Q) ++ edgeWord (alpha Q), ?_⟩, ?_⟩
    · simp [wallUnit, List.append_assoc]
    · simp [wallInnerOffset]
  · refine ⟨⟨edgeWord (alpha Q) ++ faceWord (depth q Q),
      faceWord (depth q Q) ++ edgeWord (alpha Q), ?_⟩, ?_⟩
    · simp [wallUnit, List.append_assoc]
    · simp [wallInnerOffset, edgeWord_length, faceWord_length _ (depth_even q Q)]
  · refine ⟨⟨edgeWord (alpha Q) ++ faceWord (depth q Q) ++ edgeWord (beta Q) ++
      faceWord (depth q Q), [], ?_⟩, ?_⟩
    · simp [wallUnit, List.append_assoc]
    · simp [wallInnerOffset, edgeWord_length, faceWord_length _ (depth_even q Q)]
      omega

theorem frame_wall_edge_occurrence (q Q : ℕ) (items : List ℕ) (j : Fin q) (k : Fin 3) :
    ∃ o : EdgeOccurrence (frameWord q Q items) (if k = 1 then beta Q else alpha Q),
      o.pre.length = (prefixWord q Q).length + j.val * wallStride q Q + wallInnerOffset q Q k := by
  obtain ⟨u, v, huv, hul⟩ := separatedCopies_occurrence (wallUnit q Q)
    (List.replicate (2 * alpha Q) .P) q j.val j.isLt
  obtain ⟨o, ho⟩ := wallUnit_edge_occurrence q Q k
  refine ⟨⟨prefixWord q Q ++ u ++ o.pre, o.post ++ v ++ gapWord q Q ++ itemWords q Q items, ?_⟩, ?_⟩
  · calc
      frameWord q Q items = prefixWord q Q ++ wallUnits q Q ++ gapWord q Q ++ itemWords q Q items := by
        simp [frameWord, walls, wallUnits, separatedCopies, List.append_assoc]
      _ = prefixWord q Q ++ (u ++ (o.pre ++ edgeWord (if k = 1 then beta Q else alpha Q) ++ o.post) ++ v) ++
          gapWord q Q ++ itemWords q Q items := by
        rw [show wallUnits q Q = u ++ wallUnit q Q ++ v from huv]
        exact congrArg (fun w => prefixWord q Q ++ (u ++ w ++ v) ++ gapWord q Q ++ itemWords q Q items) o.word_eq
      _ = _ := by simp only [List.append_assoc]
  · simp only [List.length_append, hul, ho, List.length_replicate, wallUnit_length]
    dsimp [wallStride]
    ring

theorem gapWord_separated (q Q : ℕ) :
    gapWord q Q = separatedCopies (edgeWord 2) (List.replicate (2 * alpha Q + 4) .P) q := by
  exact (repeatWord_slide (edgeWord 2) (List.replicate (2 * alpha Q + 4) .P) (q - 1)).symm

theorem frame_gap_edge_occurrence (q Q : ℕ) (items : List ℕ) (j : Fin q) :
    ∃ o : EdgeOccurrence (frameWord q Q items) 2,
      o.pre.length = (prefixWord q Q).length + (wallUnits q Q).length +
        j.val * (2 * alpha Q + 10) := by
  obtain ⟨u, v, huv, hul⟩ := separatedCopies_occurrence (edgeWord 2)
    (List.replicate (2 * alpha Q + 4) .P) q j.val j.isLt
  refine ⟨⟨prefixWord q Q ++ wallUnits q Q ++ u, v ++ itemWords q Q items, ?_⟩, ?_⟩
  · calc
      frameWord q Q items = prefixWord q Q ++ wallUnits q Q ++ gapWord q Q ++ itemWords q Q items := by
        simp [frameWord, walls, wallUnits, separatedCopies, List.append_assoc]
      _ = _ := by rw [gapWord_separated, huv]; simp only [List.append_assoc]
  · simp only [List.length_append, hul, edgeWord_length, List.length_replicate]
    ring

set_option maxHeartbeats 1000000 in
theorem frame_block_occurrence_exists (q Q : ℕ) (items : List ℕ) (b : FrameBlock q) :
    ∃ o : EdgeOccurrence (frameWord q Q items) (anchorLength Q (frameBlockKind b)),
      o.pre.length = frameBlockOffset q Q b := by
  rcases b with ⟨j, k⟩
  fin_cases k
  · simpa [frameBlockKind, anchorLength, frameBlockOffset, wallInnerOffset, Nat.add_assoc] using
      frame_wall_edge_occurrence q Q items j 0
  · simpa [frameBlockKind, anchorLength, frameBlockOffset, wallInnerOffset, Nat.add_assoc] using
      frame_wall_edge_occurrence q Q items j 1
  · simpa [frameBlockKind, anchorLength, frameBlockOffset, wallInnerOffset, Nat.add_assoc] using
      frame_wall_edge_occurrence q Q items j 2
  · simpa [frameBlockKind, anchorLength, frameBlockOffset, Nat.add_assoc] using
      frame_gap_edge_occurrence q Q items j

noncomputable def frameBlockOccurrence (q Q : ℕ) (items : List ℕ) (b : FrameBlock q) :
    EdgeOccurrence (frameWord q Q items) (anchorLength Q (frameBlockKind b)) :=
  Classical.choose (frame_block_occurrence_exists q Q items b)

theorem frameBlockOccurrence_offset (q Q : ℕ) (items : List ℕ) (b : FrameBlock q) :
    (frameBlockOccurrence q Q items b).pre.length = frameBlockOffset q Q b :=
  Classical.choose_spec (frame_block_occurrence_exists q Q items b)

theorem wallUnits_length (q Q : ℕ) :
    (wallUnits q Q).length = (q - 1) * wallStride q Q +
      (6 * alpha Q + 3 * beta Q + 4 * depth q Q) := by
  simp only [wallUnits, separatedCopies, List.length_append, repeatWord_length,
    List.length_replicate, wallUnit_length]
  dsimp [wallStride]
  ring

theorem frameBlockOffset_after_prefix (q Q : ℕ) (b : FrameBlock q) :
    (prefixWord q Q).length ≤ frameBlockOffset q Q b := by
  unfold frameBlockOffset
  omega

theorem wall_block_end_le_units (q Q : ℕ) (j : Fin q) (k : Fin 3) :
    j.val * wallStride q Q + wallInnerOffset q Q k +
      3 * (if k = 1 then beta Q else alpha Q) ≤ (wallUnits q Q).length := by
  have hj : j.val ≤ q - 1 := by omega
  have hmul := Nat.mul_le_mul_right (wallStride q Q) hj
  rw [wallUnits_length]
  fin_cases k <;> simp [wallInnerOffset]
  all_goals omega

theorem wall_block_end_le_stride (q Q : ℕ) (k : Fin 3) :
    wallInnerOffset q Q k + 3 * (if k = 1 then beta Q else alpha Q) ≤ wallStride q Q := by
  fin_cases k <;> simp [wallInnerOffset, wallStride] <;> omega

theorem frame_block_offsets_separate (q Q : ℕ) (b c : FrameBlock q) (hbc : b ≠ c) :
    frameBlockOffset q Q b + 3 * anchorLength Q (frameBlockKind b) ≤ frameBlockOffset q Q c ∨
    frameBlockOffset q Q c + 3 * anchorLength Q (frameBlockKind c) ≤ frameBlockOffset q Q b := by
  rcases b with ⟨j, k⟩
  rcases c with ⟨l, m⟩
  have hj := j.isLt
  have hl := l.isLt
  have hmuljl : j.val < l.val → (j.val + 1) * wallStride q Q ≤ l.val * wallStride q Q := by
    intro h
    exact Nat.mul_le_mul_right _ (by omega)
  have hmullj : l.val < j.val → (l.val + 1) * wallStride q Q ≤ j.val * wallStride q Q := by
    intro h
    exact Nat.mul_le_mul_right _ (by omega)
  have hgapjl : j.val < l.val → (j.val + 1) * (2 * alpha Q + 10) ≤ l.val * (2 * alpha Q + 10) := by
    intro h
    exact Nat.mul_le_mul_right _ (by omega)
  have hgaplj : l.val < j.val → (l.val + 1) * (2 * alpha Q + 10) ≤ j.val * (2 * alpha Q + 10) := by
    intro h
    exact Nat.mul_le_mul_right _ (by omega)
  have hwj0 := wall_block_end_le_units q Q j 0
  have hwj1 := wall_block_end_le_units q Q j 1
  have hwj2 := wall_block_end_le_units q Q j 2
  have hwl0 := wall_block_end_le_units q Q l 0
  have hwl1 := wall_block_end_le_units q Q l 1
  have hwl2 := wall_block_end_le_units q Q l 2
  have hs0 := wall_block_end_le_stride q Q 0
  have hs1 := wall_block_end_le_stride q Q 1
  have hs2 := wall_block_end_le_stride q Q 2
  simp only [wallInnerOffset] at hwj0 hwj1 hwj2 hwl0 hwl1 hwl2 hs0 hs1 hs2
  simp at hwj0 hwj1 hwj2 hwl0 hwl1 hwl2 hs0 hs1 hs2
  by_cases hje : j = l
  · subst l
    have hkm : k ≠ m := by intro he; subst m; exact hbc rfl
    fin_cases k <;> fin_cases m <;>
      simp_all [frameBlockOffset, frameBlockKind, anchorLength, wallInnerOffset]
    all_goals omega
  · have hord : j.val < l.val ∨ l.val < j.val := by
      have hval : j.val ≠ l.val := by intro he; exact hje (Fin.ext he)
      omega
    rcases hord with hord | hord
    · have hunit := hmuljl hord
      have hgap := hgapjl hord
      simp only [Nat.add_mul, Nat.one_mul] at hunit hgap
      fin_cases k <;> fin_cases m <;>
        simp [frameBlockOffset, frameBlockKind, anchorLength, wallInnerOffset] <;> omega
    · have hunit := hmullj hord
      have hgap := hgaplj hord
      simp only [Nat.add_mul, Nat.one_mul] at hunit hgap
      fin_cases k <;> fin_cases m <;>
        simp [frameBlockOffset, frameBlockKind, anchorLength, wallInnerOffset] <;> omega

theorem frameBlock_sites_disjoint (q Q : ℕ) (items : List ℕ)
    (f : Fold cubicLattice (frameWord q Q items).length) (b c : FrameBlock q) (hbc : b ≠ c) :
    Disjoint ((frameBlockOccurrence q Q items b).sites f) ((frameBlockOccurrence q Q items c).sites f) := by
  rcases frame_block_offsets_separate q Q b c hbc with h | h
  · apply EdgeOccurrence.sites_disjoint_of_before
    simpa only [frameBlockOccurrence_offset] using h
  · apply Disjoint.symm
    apply EdgeOccurrence.sites_disjoint_of_before
    simpa only [frameBlockOccurrence_offset] using h

end ProteinFolding.CubicPackingGeometry
