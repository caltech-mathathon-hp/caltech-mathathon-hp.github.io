import ProteinFolding.Cubic.Proofs.PackingAttachedDisjoint
import ProteinFolding.Common.FoldConcatenation

/-! Assemble explicitly decorated word blocks, preserving their H support,
attachment owners and endpoints. All seam and disjointness conditions are
geometric hypotheses, so these helpers apply independently of a reduction. -/

namespace ProteinFolding.CubicPackingLift

open CubicCertificates

def HasEnds {N : ℕ} (f : Fold cubicLattice N) (first last : Site) : Prop :=
  (∀ i : Fin N, i.val = 0 → f.pos i = first) ∧
  (∀ i : Fin N, i.val + 1 = N → f.pos i = last)

theorem hasEnds_of_indices {N : ℕ} (f : Fold cubicLattice N) (hN : 0 < N)
    (first last : Site) (hf : f.pos ⟨0, hN⟩ = first)
    (hl : f.pos ⟨N - 1, by omega⟩ = last) : HasEnds f first last := by
  constructor
  · intro i hi
    have he : i = ⟨0, hN⟩ := Fin.ext hi
    exact he ▸ hf
  · intro i hi
    have he : i = ⟨N - 1, by omega⟩ := Fin.ext (by change i.val = N - 1; omega)
    exact he ▸ hl

theorem hasEnds_seam {N M : ℕ} (f : Fold cubicLattice N) (g : Fold cubicLattice M)
    {p q r s : Site} (hf : HasEnds f p q) (hg : HasEnds g r s)
    (hqr : cubicLattice.Adj q r) (i : Fin N) (j : Fin M)
    (hi : i.val + 1 = N) (hj : j.val = 0) : cubicLattice.Adj (f.pos i) (g.pos j) := by
  rw [hf.2 i hi, hg.1 j hj]
  exact hqr

theorem appendWord_hasEnds {S T : Sequence} (f : Fold cubicLattice S.length)
    (g : Fold cubicLattice T.length) hdisjoint hseam
    (hS : 0 < S.length) (hT : 0 < T.length) {p q r s : Site}
    (hf : HasEnds f p q) (hg : HasEnds g r s) :
    HasEnds (Fold.appendWord f g hdisjoint hseam) p s := by
  constructor
  · intro i hi
    let j : Fin S.length := ⟨i.val, by omega⟩
    have he : i = Fold.leftWordIndex S T j := Fin.ext rfl
    rw [he, Fold.appendWord_pos_left]
    exact hf.1 j hi
  · intro i hi
    have hv : i.val + 1 = S.length + T.length := by simpa only [List.length_append] using hi
    let j : Fin T.length := ⟨i.val - S.length, by omega⟩
    have he : i = Fold.rightWordIndex S T j := by
      apply Fin.ext
      change i.val = S.length + (i.val - S.length)
      omega
    rw [he, Fold.appendWord_pos_right]
    apply hg.2
    change i.val - S.length + 1 = T.length
    omega

theorem appendWord_hydrophobicSites {S T : Sequence} (f : Fold cubicLattice S.length)
    (g : Fold cubicLattice T.length) hdisjoint hseam :
    hydrophobicSites (S ++ T) (Fold.appendWord f g hdisjoint hseam) =
      hydrophobicSites S f ∪ hydrophobicSites T g := by
  ext p
  exact Fold.appendWord_exists_residue f g hdisjoint hseam .H p

theorem appendWord_property {S T : Sequence} (f : Fold cubicLattice S.length)
    (g : Fold cubicLattice T.length) hdisjoint hseam (P : Site → Prop)
    (hf : ∀ i, P (f.pos i)) (hg : ∀ j, P (g.pos j)) :
    ∀ i, P ((Fold.appendWord f g hdisjoint hseam).pos i) := by
  intro i
  by_cases hi : i.val < S.length
  · let j : Fin S.length := ⟨i.val, hi⟩
    have he : i = Fold.leftWordIndex S T j := Fin.ext rfl
    rw [he, Fold.appendWord_pos_left]
    exact hf j
  · have hil := i.isLt
    simp only [List.length_append] at hil
    let j : Fin T.length := ⟨i.val - S.length, by omega⟩
    have he : i = Fold.rightWordIndex S T j := by
      apply Fin.ext
      change i.val = S.length + (i.val - S.length)
      omega
    rw [he, Fold.appendWord_pos_right]
    exact hg j

theorem range_append_owners {H K : ℕ} (p : Fin H → Site) (q : Fin K → Site) :
    Set.range (Fin.append p q) = Set.range p ∪ Set.range q := by
  ext v
  constructor
  · rintro ⟨i, hi⟩
    cases i using Fin.addCases with
    | left i => exact Or.inl ⟨i, by simpa only [Fin.append_left] using hi⟩
    | right i => exact Or.inr ⟨i, by simpa only [Fin.append_right] using hi⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd K i, Fin.append_left _ _ _⟩
    · exact ⟨Fin.natAdd H j, Fin.append_right _ _ _⟩

theorem appendWord_H_support {S T : Sequence} {H K : ℕ}
    (f : Fold cubicLattice S.length) (g : Fold cubicLattice T.length) hdisjoint hseam
    (p : Fin H → Site) (q : Fin K → Site)
    (hf : hydrophobicSites S f = Set.range p) (hg : hydrophobicSites T g = Set.range q) :
    hydrophobicSites (S ++ T) (Fold.appendWord f g hdisjoint hseam) = Set.range (Fin.append p q) := by
  rw [appendWord_hydrophobicSites, hf, hg, range_append_owners]

theorem appendWord_attached {S T : Sequence} {H K : ℕ} (a : Site) (n : ℕ)
    (f : Fold cubicLattice S.length) (g : Fold cubicLattice T.length) hdisjoint hseam
    (p : Fin H → Site) (q : Fin K → Site)
    (hf : AttachedTo a n f p) (hg : AttachedTo a n g q) :
    AttachedTo a n (Fold.appendWord f g hdisjoint hseam) (Fin.append p q) := by
  constructor
  · intro i
    cases i using Fin.addCases with
    | left i => simpa only [Fin.append_left] using hf.1 i
    | right i => simpa only [Fin.append_right] using hg.1 i
  · intro i
    by_cases hi : i.val < S.length
    · let j : Fin S.length := ⟨i.val, hi⟩
      have he : i = Fold.leftWordIndex S T j := Fin.ext rfl
      obtain ⟨k, hk⟩ := hf.2 j
      refine ⟨Fin.castAdd K k, ?_⟩
      simpa only [he, Fold.appendWord_pos_left, Fin.append_left] using hk
    · have hil := i.isLt
      simp only [List.length_append] at hil
      let j : Fin T.length := ⟨i.val - S.length, by omega⟩
      have he : i = Fold.rightWordIndex S T j := by
        apply Fin.ext
        change i.val = S.length + (i.val - S.length)
        omega
      obtain ⟨k, hk⟩ := hg.2 j
      refine ⟨Fin.natAdd H k, ?_⟩
      simpa only [he, Fold.appendWord_pos_right, Fin.append_right] using hk

theorem append_owners_disjoint {H K J : ℕ} (p : Fin H → Site) (q : Fin K → Site) (r : Fin J → Site)
    (hpr : ∀ i j, p i ≠ r j) (hqr : ∀ i j, q i ≠ r j) :
    ∀ i j, Fin.append p q i ≠ r j := by
  intro i j
  cases i using Fin.addCases with
  | left i => simpa only [Fin.append_left] using hpr i j
  | right i => simpa only [Fin.append_right] using hqr i j

theorem append_owners_disjoint_right {H K J : ℕ} (p : Fin H → Site) (q : Fin K → Site) (r : Fin J → Site)
    (hpq : ∀ i j, p i ≠ q j) (hpr : ∀ i j, p i ≠ r j) :
    ∀ i j, p i ≠ Fin.append q r j := by
  intro i j
  exact Ne.symm (append_owners_disjoint q r p (fun j i => Ne.symm (hpq i j))
    (fun j i => Ne.symm (hpr i j)) j i)

/-- Exterior attachments of a path at height at least z cannot descend
below z-1. This separates all front-wall decorations from deeper P bridges. -/
theorem attached_height_lower {N H : ℕ} (a : Site) (n : ℕ)
    (f : Fold cubicLattice N) (owners : Fin H → Site) (hf : AttachedTo a n f owners)
    (z : ℤ) (hz : ∀ k, z ≤ owners k 2) (i : Fin N) : z - 1 ≤ f.pos i 2 := by
  obtain ⟨k, hk⟩ := hf.2 i
  rcases hk with he | ⟨_, ha⟩
  · rw [he]
    have h := hz k
    omega
  · obtain ⟨d, hd⟩ := adj_step ha.symm
    have hb := (step_coordinate_bounds (owners k) d 2).1
    rw [hd] at hb
    have h := hz k
    omega

end ProteinFolding.CubicPackingLift
