import ProteinFolding.Cubic.Proofs.PackingFaceBulkDisjoint

/-! Every P in an E or F word has an H backbone neighbour. Combined with
the unique interior neighbour of an exterior cube point, disjoint H supports
therefore give disjoint complete decorated components. -/

namespace ProteinFolding.CubicPackingAttachments

open CubicPacking CubicPackingLift CubicPackingGeometry CubicCertificates

theorem edgeWord_P_has_H_neighbour (t : ℕ) (f : Fold cubicLattice (edgeWord t).length)
    (i : Fin (edgeWord t).length) (hi : (edgeWord t).get i = .P) :
    ∃ j, (edgeWord t).get j = .H ∧ cubicLattice.Adj (f.pos i) (f.pos j) := by
  let j := edgeHIndex t (edgeBaseIndex t i)
  have hj : (edgeWord t).get j = .H := (edgeWord_H_iff t j).mpr (by
    dsimp [j, edgeHIndex]
    omega)
  have hmod : i.val % 3 ≠ 1 := by
    intro h
    have hh := (edgeWord_H_iff t i).mpr h
    rw [hi] at hh
    contradiction
  have hm : i.val % 3 = 0 ∨ i.val % 3 = 2 := by omega
  refine ⟨j, hj, ?_⟩
  rcases hm with hm | hm
  · apply f.consecutive
    dsimp [j, edgeHIndex, edgeBaseIndex]
    omega
  · apply (f.consecutive j i ?_).symm
    dsimp [j, edgeHIndex, edgeBaseIndex]
    omega

theorem faceWord_P_has_H_neighbour (t : ℕ) (ht : 2 ∣ t) (f : Fold cubicLattice (faceWord t).length)
    (i : Fin (faceWord t).length) (hi : (faceWord t).get i = .P) :
    ∃ j, (faceWord t).get j = .H ∧ cubicLattice.Adj (f.pos i) (f.pos j) := by
  let j := faceHIndex t ht (faceBaseIndex t ht i)
  have hj : (faceWord t).get j = .H := (faceWord_H_iff t j).mpr
    (faceHeight_HIndex t ht (faceBaseIndex t ht i))
  have hh : faceHeight i.val = -1 := by
    have hr := faceWord_residue_height t i
    by_contra hn
    simp only [if_neg hn] at hr
    rw [hi] at hr
    contradiction
  have hm : i.val % 4 = 0 ∨ i.val % 4 = 3 := by
    unfold faceHeight at hh
    split_ifs at hh <;> omega
  refine ⟨j, hj, ?_⟩
  rcases hm with hm | hm
  · apply f.consecutive
    dsimp [j, faceHIndex, faceBaseIndex]
    split_ifs <;> omega
  · apply (f.consecutive j i ?_).symm
    dsimp [j, faceHIndex, faceBaseIndex]
    split_ifs <;> omega

theorem folds_disjoint_of_H_disjoint {S T : Sequence}
    (f : Fold cubicLattice S.length) (g : Fold cubicLattice T.length) (a : Site) (n : ℕ)
    (hfH : ∀ i, S.get i = .H → f.pos i ∈ cube a n)
    (hgH : ∀ j, T.get j = .H → g.pos j ∈ cube a n)
    (hfP : ∀ i, S.get i = .P → f.pos i ∉ cube a n)
    (hgP : ∀ j, T.get j = .P → g.pos j ∉ cube a n)
    (hfOwner : ∀ i, S.get i = .P → ∃ k, S.get k = .H ∧ cubicLattice.Adj (f.pos i) (f.pos k))
    (hgOwner : ∀ j, T.get j = .P → ∃ k, T.get k = .H ∧ cubicLattice.Adj (g.pos j) (g.pos k))
    (hH : ∀ i j, S.get i = .H → T.get j = .H → f.pos i ≠ g.pos j) :
    ∀ i j, f.pos i ≠ g.pos j := by
  intro i j he
  cases hi : S.get i with
  | H =>
    cases hj : T.get j with
    | H => exact hH i j hi hj he
    | P => exact hgP j hj (he ▸ hfH i hi)
  | P =>
    cases hj : T.get j with
    | H => exact hfP i hi (he.symm ▸ hgH j hj)
    | P =>
      obtain ⟨u, hu, hiu⟩ := hfOwner i hi
      obtain ⟨v, hv, hjv⟩ := hgOwner j hj
      have heq := cube_exterior_neighbour_unique a n (f.pos i) (f.pos u) (g.pos v)
        (hfP i hi) (hfH u hu) (hgH v hv) hiu (he.symm ▸ hjv)
      exact hH u v hu hv heq

def NearCube (d : ℕ) (p : Site) : Prop :=
  p ∈ cube (fun _ => 0) (d + 2) ∨
    ∃ q ∈ cube (fun _ => 0) (d + 2), cubicLattice.Adj p q

theorem edgeWord_near_cube (t d : ℕ) (f : Fold cubicLattice (edgeWord t).length)
    (hH : ∀ i, (edgeWord t).get i = .H → f.pos i ∈ cube (fun _ => 0) (d + 2)) :
    ∀ i, NearCube d (f.pos i) := by
  intro i
  cases hi : (edgeWord t).get i with
  | H => exact Or.inl (hH i hi)
  | P =>
    obtain ⟨j, hj, hij⟩ := edgeWord_P_has_H_neighbour t f i hi
    exact Or.inr ⟨f.pos j, hH j hj, hij⟩

theorem faceWord_near_cube (t d : ℕ) (ht : 2 ∣ t) (f : Fold cubicLattice (faceWord t).length)
    (hH : ∀ i, (faceWord t).get i = .H → f.pos i ∈ cube (fun _ => 0) (d + 2)) :
    ∀ i, NearCube d (f.pos i) := by
  intro i
  cases hi : (faceWord t).get i with
  | H => exact Or.inl (hH i hi)
  | P =>
    obtain ⟨j, hj, hij⟩ := faceWord_P_has_H_neighbour t ht f i hi
    exact Or.inr ⟨f.pos j, hH j hj, hij⟩

end ProteinFolding.CubicPackingAttachments
