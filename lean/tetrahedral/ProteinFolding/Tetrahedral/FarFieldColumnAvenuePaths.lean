import ProteinFolding.Tetrahedral.FarFieldStageB

namespace ProteinFolding.Tetrahedral.FarField.WireData

variable {w : ℕ} (d : WireData w)

theorem column_first (i : Fin w) (k : Fin (columnHeight d.R d.H d.quadrants d.bases i + 1))
    (hk : k.val = 0) : (d.columns i).pos k = quadrantMap d.R d.R_even (d.quadrants i) (d.bases i) := by
  change quadrantArm d.R d.R_even (d.quadrants i) (d.bases i) (0 + k.val) = _
  simp only [hk, Int.natCast_zero, add_zero, quadrantArm, arm_zero]

theorem column_last (i : Fin w) (k : Fin (columnHeight d.R d.H d.quadrants d.bases i + 1))
    (hk : k.val + 1 = columnHeight d.R d.H d.quadrants d.bases i + 1) : (d.columns i).pos k = d.tops i := by
  have hk' : k.val = columnHeight d.R d.H d.quadrants d.bases i := by omega
  change quadrantArm d.R d.R_even (d.quadrants i) (d.bases i) (0 + k.val) = _
  simp only [hk', zero_add, tops, columnTop]

theorem own_column_avenue_intersection (i : Fin w)
    (a : Fin (columnHeight d.R d.H d.quadrants d.bases i + 1))
    (b : Fin ((d.entries i).avenueEdges + 1))
    (heq : (d.columns i).pos a = (d.entries i).avenueFold.pos b) :
    a.val + 1 = columnHeight d.R d.H d.quadrants d.bases i + 1 ∧ b.val = 0 := by
  have ha := a.isLt
  have hb := d.avenue_paths_profile i b
  have hheight := columnHeight_exact d.R d.R_even d.H d.H_odd d.quadrants d.bases i
    (d.positive i) (d.below i)
  change rho d.R (d.bases i) + 2 * (columnHeight d.R d.H d.quadrants d.bases i : ℤ) = d.levels i at hheight
  have hcol := (quadrantArm_rho_alpha d.R d.R_even (d.quadrants i) (d.bases i) a.val (d.positive i) (by omega)).1
  have hρ := congrArg (rho d.R) heq
  change rho d.R (quadrantArm d.R d.R_even (d.quadrants i) (d.bases i) (0 + a.val)) =
    rho d.R ((d.entries i).avenueFold.pos b) at hρ
  simp only [zero_add] at hρ
  have hai : a.val = columnHeight d.R d.H d.quadrants d.bases i := by omega
  have htop := d.column_last i a (by omega)
  rw [htop] at heq
  have hx := congrArg X heq
  change X (d.tops i) = X (wireAvenue d.R d.R_even (d.quadrants i) (d.tops i) (X (d.tops i) + b.val)) at hx
  rw [wireAvenue_x] at hx
  exact ⟨by omega, by omega⟩

theorem column_avenue_join (i : Fin w) :
    (d.columns i).pos ⟨(columnHeight d.R d.H d.quadrants d.bases i + 1) - 1, by omega⟩ =
      (d.entries i).avenueFold.pos ⟨0, by omega⟩ := by
  have hc := d.column_last i ⟨(columnHeight d.R d.H d.quadrants d.bases i + 1) - 1, by omega⟩
    (by change (columnHeight d.R d.H d.quadrants d.bases i + 1 - 1) + 1 = _; omega)
  have ha := (d.entries i).avenueFold_first (d.tops_profile i).1 (d.tops_high i) ⟨0, by omega⟩ rfl
  exact hc.trans ha.symm

noncomputable def columnAvenueSites (i : Fin w) : ℕ :=
  (columnHeight d.R d.H d.quadrants d.bases i + 1) + ((d.entries i).avenueEdges + 1) - 1

noncomputable def columnAvenuePath (i : Fin w) : Fold tetrahedralLattice (d.columnAvenueSites i) :=
  glue (d.columns i) (d.entries i).avenueFold (by omega) (by omega) (d.column_avenue_join i)
    (fun a b heq => d.own_column_avenue_intersection i a b heq)

theorem columnAvenueSites_pos (i : Fin w) : 0 < d.columnAvenueSites i := by
  unfold columnAvenueSites
  omega

theorem columnAvenuePath_first (i : Fin w) (k : Fin (d.columnAvenueSites i)) (hk : k.val = 0) :
    (d.columnAvenuePath i).pos k = quadrantMap d.R d.R_even (d.quadrants i) (d.bases i) := by
  have h := glue_first (d.columns i) (d.entries i).avenueFold (by omega) (by omega)
    (d.column_avenue_join i) (fun a b heq => d.own_column_avenue_intersection i a b heq) k hk
  exact h.trans (d.column_first i ⟨0, by omega⟩ rfl)

theorem columnAvenuePath_last (i : Fin w) (k : Fin (d.columnAvenueSites i))
    (hk : k.val + 1 = d.columnAvenueSites i) : (d.columnAvenuePath i).pos k = (d.entries i).point := by
  have h := glue_last (d.columns i) (d.entries i).avenueFold (by omega) (by omega)
    (d.column_avenue_join i) (fun a b heq => d.own_column_avenue_intersection i a b heq) k hk
  exact h.trans ((d.entries i).avenueFold_last (le_of_lt (d.tops_before_slab i)) _
    (by change (d.entries i).avenueEdges + 1 - 1 = (d.entries i).avenueEdges; omega))

theorem columnAvenuePath_pos_cases (i : Fin w) (k : Fin (d.columnAvenueSites i)) :
    (∃ a, (d.columns i).pos a = (d.columnAvenuePath i).pos k) ∨
      (∃ b, (d.entries i).avenueFold.pos b = (d.columnAvenuePath i).pos k) :=
  glue_pos_cases (d.columns i) (d.entries i).avenueFold (by omega) (by omega)
    (d.column_avenue_join i) (fun a b heq => d.own_column_avenue_intersection i a b heq) k

theorem columnAvenuePath_range (i : Fin w) :
    Set.range (d.columnAvenuePath i).pos ⊆ Set.range (d.columns i).pos ∪ Set.range (d.entries i).avenueFold.pos := by
  rintro p ⟨k, rfl⟩
  rcases d.columnAvenuePath_pos_cases i k with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem columnAvenuePaths_disjoint (i j : Fin w) (hne : i ≠ j) :
    Disjoint (Set.range (d.columnAvenuePath i).pos) (Set.range (d.columnAvenuePath j).pos) := by
  have hcc := columnFolds_disjoint d.R d.R_even d.H d.quadrants d.bases d.positive d.identities i j hne
  have hac := d.avenue_column_disjoint i j hne
  have hca := (d.avenue_column_disjoint j i hne.symm).symm
  have haa := d.avenue_paths_disjoint i j hne
  have hu : Disjoint (Set.range (d.columns i).pos ∪ Set.range (d.entries i).avenueFold.pos)
      (Set.range (d.columns j).pos ∪ Set.range (d.entries j).avenueFold.pos) := by
    rw [Set.disjoint_union_left, Set.disjoint_union_right, Set.disjoint_union_right]
    exact ⟨⟨hcc, hca⟩, ⟨hac, haa⟩⟩
  exact hu.mono (d.columnAvenuePath_range i) (d.columnAvenuePath_range j)

end ProteinFolding.Tetrahedral.FarField.WireData
