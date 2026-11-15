import ProteinFolding.Tetrahedral.Geometry

/-! Further Section 2 facts: reversing a step and uniqueness of a common neighbour.
The latter rules out four-cycles. Sublattice alternation rules out triangles. -/

namespace ProteinFolding.Tetrahedral

@[simp] theorem step_step (p : Site) (d : Fin 4) : step (step p d) d = p := by
  apply Subtype.ext
  by_cases hp : InASublattice p.val
  · have hq : InBSublattice (step p d).val := by
      rw [step_val_of_A p hp d]
      exact add_bondVector_inB p.val hp d
    rw [step_val_of_B _ hq d, step_val_of_A p hp d]
    funext k
    simp
  · have hpB := (inB_iff_not_inA p).mpr hp
    have hq : InASublattice (step p d).val := by
      rw [step_val_of_B p hpB d]
      exact sub_bondVector_inA p.val hpB d
    rw [step_val_of_A _ hq d, step_val_of_B p hpB d]
    funext k
    simp

theorem no_triangle (p q r : Site) :
    ¬ (tetrahedralLattice.Adj p q ∧ tetrahedralLattice.Adj q r ∧
      tetrahedralLattice.Adj r p) := by
  rintro ⟨hpq, hqr, hrp⟩
  have h₁ := adj_not_same_sublattice hpq
  have h₂ := adj_not_same_sublattice hqr
  have h₃ := adj_not_same_sublattice hrp
  by_cases hp : InASublattice p.val
  · have hnq := h₁.mp hp
    have hnr : ¬ InASublattice r.val := fun hr => h₃.mp hr hp
    exact hnq (h₂.mpr hnr)
  · have hr := h₃.mpr hp
    have hnq : ¬ InASublattice q.val := fun hq => h₂.mp hq hr
    exact hp (h₁.mpr hnq)

/-- The twelve nonzero differences t_a - t_b are distinct. This finite vector
identity is used to prove the uniform statement for arbitrary lattice sites. -/
theorem bondVector_difference_unique :
    ∀ a b c d : Fin 4, a ≠ b →
      (fun k => bondVector a k - bondVector b k) =
        (fun k => bondVector c k - bondVector d k) → a = c ∧ b = d := by decide

/-- Two distinct sites have at most one common neighbour. -/
theorem common_neighbour_unique {p r q s : Site} (hne : p ≠ r)
    (hpq : tetrahedralLattice.Adj p q) (hrq : tetrahedralLattice.Adj r q)
    (hps : tetrahedralLattice.Adj p s) (hrs : tetrahedralLattice.Adj r s) : q = s := by
  obtain ⟨a, ha⟩ := (adj_iff_exists_step p q).mp hpq
  obtain ⟨b, hb⟩ := (adj_iff_exists_step r q).mp hrq
  obtain ⟨c, hc⟩ := (adj_iff_exists_step p s).mp hps
  obtain ⟨d, hd⟩ := (adj_iff_exists_step r s).mp hrs
  have hcolour : InASublattice p.val ↔ InASublattice r.val :=
    (adj_not_same_sublattice hpq).trans (adj_not_same_sublattice hrq).symm
  have hab : a ≠ b := by
    intro h
    apply hne
    apply Subtype.ext
    funext k
    have h₁ := congrArg (fun x : Site => x.val k) ha
    have h₂ := congrArg (fun x : Site => x.val k) hb
    by_cases hp : InASublattice p.val
    · simp only [step_val_of_A p hp, step_val_of_A r (hcolour.mp hp), h] at h₁ h₂
      omega
    · have hr : ¬ InASublattice r.val := fun hr => hp (hcolour.mpr hr)
      simp only [step_val_of_B p ((inB_iff_not_inA p).mpr hp),
        step_val_of_B r ((inB_iff_not_inA r).mpr hr), h] at h₁ h₂
      omega
  have hdiff : (fun k => bondVector a k - bondVector b k) =
      (fun k => bondVector c k - bondVector d k) := by
    funext k
    have h₁ := congrArg (fun x : Site => x.val k) ha
    have h₂ := congrArg (fun x : Site => x.val k) hb
    have h₃ := congrArg (fun x : Site => x.val k) hc
    have h₄ := congrArg (fun x : Site => x.val k) hd
    by_cases hp : InASublattice p.val
    · simp only [step_val_of_A p hp, step_val_of_A r (hcolour.mp hp)] at h₁ h₂ h₃ h₄
      omega
    · have hr : ¬ InASublattice r.val := fun hr => hp (hcolour.mpr hr)
      simp only [step_val_of_B p ((inB_iff_not_inA p).mpr hp),
        step_val_of_B r ((inB_iff_not_inA r).mpr hr)] at h₁ h₂ h₃ h₄
      omega
  have hac := (bondVector_difference_unique a b c d hab hdiff).1
  exact ha.symm.trans (hac ▸ hc)

theorem no_four_cycle {p q r s : Site} (hpr : p ≠ r) (hqs : q ≠ s) :
    ¬ (tetrahedralLattice.Adj p q ∧ tetrahedralLattice.Adj q r ∧
      tetrahedralLattice.Adj r s ∧ tetrahedralLattice.Adj s p) := by
  rintro ⟨hpq, hqr, hrs, hsp⟩
  exact hqs (common_neighbour_unique hpr hpq hqr.symm hsp.symm hrs)

end ProteinFolding.Tetrahedral
