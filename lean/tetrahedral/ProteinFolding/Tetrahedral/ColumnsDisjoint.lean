import ProteinFolding.Tetrahedral.Columns

/-! Pairwise disjointness of all dangling columns, Lemma C(iii). -/

namespace ProteinFolding.Tetrahedral
namespace DanglingColumn

private theorem seeds_eq_same_quadrant_le {m : ℕ} (C D : DanglingColumn m)
    (hsy : C.sy = D.sy) (hsz : C.sz = D.sz) {n r : ℕ} (hnr : n ≤ r)
    (heq : C.point n = D.point r) : C.seed = D.seed := by
  have hr : r = (r - n) + n := by omega
  change bulkArmPoint C.sy C.sz C.seed n = bulkArmPoint D.sy D.sz D.seed r at heq
  rw [hsy, hsz, hr, bulkArmPoint_add] at heq
  have hseed : C.seed = D.point (r - n) :=
    bulkArmPoint_seed_injective D.sy D.sz D.sy_unit D.sz_unit n heq
  have hdang : IsDangling m (D.point (r - n)) := by
    rw [← hseed]
    exact C.seed_dangling
  have hzero := (D.point_dangling_iff_zero (r - n)).mp hdang
  rw [hzero] at hseed
  exact hseed

/-- Any intersection forces the columns to have the same starting site. -/
theorem seeds_eq_of_point_eq {m : ℕ} (C D : DanglingColumn m) {n r : ℕ}
    (heq : C.point n = D.point r) : C.seed = D.seed := by
  have hyC := C.point_signed_y n
  have hyD := D.point_signed_y r
  rw [heq] at hyC
  have hsy : C.sy = D.sy := by
    rcases C.sy_unit with hc | hc <;> rcases D.sy_unit with hd | hd
    all_goals simp only [hc, hd] at hyC hyD ⊢
    all_goals omega
  have hzC := C.point_signed_z n
  have hzD := D.point_signed_z r
  change (n : ℤ) ≤ C.sz * bulkZ (C.point n) at hzC
  change (r : ℤ) ≤ D.sz * bulkZ (D.point r) at hzD
  rw [heq] at hzC
  have hsz : C.sz = D.sz ∨ (n = 0 ∧ r = 0) := by
    rcases C.sz_unit with hc | hc <;> rcases D.sz_unit with hd | hd
    all_goals simp only [hc, hd] at hzC hzD ⊢
    all_goals first | exact Or.inl trivial | omega
  rcases hsz with hsz | ⟨rfl, rfl⟩
  · rcases le_total n r with hnr | hrn
    · exact seeds_eq_same_quadrant_le C D hsy hsz hnr heq
    · exact (seeds_eq_same_quadrant_le D C hsy.symm hsz.symm hrn heq.symm).symm
  · exact heq

theorem points_ne_of_seed_ne {m : ℕ} {C D : DanglingColumn m} (hne : C.seed ≠ D.seed)
    (n r : ℕ) : C.point n ≠ D.point r := fun h => hne (seeds_eq_of_point_eq C D h)

/-- The columns belonging to different dangling sites are disjoint sets. -/
theorem sites_disjoint_of_seed_ne {m : ℕ} {C D : DanglingColumn m} (hne : C.seed ≠ D.seed) :
    Disjoint C.sites D.sites := by
  apply Set.disjoint_left.mpr
  rintro q ⟨n, rfl⟩ ⟨r, heq⟩
  exact points_ne_of_seed_ne hne n r heq.symm

end DanglingColumn
end ProteinFolding.Tetrahedral
