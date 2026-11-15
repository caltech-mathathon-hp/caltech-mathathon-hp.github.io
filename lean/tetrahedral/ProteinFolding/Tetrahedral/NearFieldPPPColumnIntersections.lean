import ProteinFolding.Tetrahedral.NearFieldPPPColumns

/-! Any column meeting an O2 PPP belongs to an endpoint or its explicit
second-row face site. This is the exact interface needed by N3 and N5. -/

namespace ProteinFolding.Tetrahedral

theorem DanglingColumn.owner_eq_of_dangling_point_eq {m : ℕ} (C : DanglingColumn m)
    (n : ℕ) {p q : Site} (hp : p ∈ octahedron m) (hq : IsDangling m q)
    (hadj : tetrahedralLattice.Adj p q) (heq : C.point n = q) : C.owner = p := by
  have hdang : IsDangling m (C.point n) := by rw [heq]; exact hq
  have hn := (C.point_dangling_iff_zero n).mp hdang
  subst n
  have hs : C.seed = q := heq
  exact (outside_step_unique_inside m C.owner_mem C.dir C.seed_outside
    (by change tetrahedralLattice.Adj C.seed p; rw [hs]; exact hadj.symm) hp).symm

theorem facePPPFold_column_owner (m : ℕ) (p : Site) (k i l : Fin 4)
    (hil : i ≠ l) (hik : i ≠ k) (hlk : l ≠ k)
    (hface : OctBigFace m k p ∨ OctSmallFace m k p)
    (hq : faceFourStep p k i l ∈ octahedron m) (C : DanglingColumn m)
    (n : ℕ) (r : Fin 3) (heq : C.point n = (facePPPFold p k i l hil).pos r) :
    C.owner = p ∨ C.owner = faceFourStep p k i l ∨
      (C.dir = k ∧ C.owner = step (step p (columnOpposite k)) i) := by
  have hp := hface.elim (fun h => h.1) (fun h => h.1)
  have hout := face_four_bond_internal_sites_outside m p k i l hik hlk hface
  fin_cases r
  · left
    apply DanglingColumn.owner_eq_of_dangling_point_eq C n hp
      (show IsDangling m (step p k) from ⟨hout.1, p, hp, step_adj _ _⟩) (step_adj _ _) heq
  · have hs := facePPPFold_mem_skin_one m p k i l hil hik hlk hface hq (1 : Fin 3)
    change step (step p k) i ∈ skin m 1 at hs
    change C.point n = step (step p k) i at heq
    rw [← heq] at hs
    have hn := (C.point_mem_skin_iff_two_indices n 1 (by decide)).mp hs
    have hn1 : n = 1 := by
      rcases hn with hn | hn
      · have hn0 : n = 0 := by omega
        have hd : IsDangling m (step (step p k) i) := by
          rw [hn0] at heq
          change C.seed = step (step p k) i at heq
          rw [← heq]
          exact C.seed_dangling
        exact (facePPP_middle_not_dangling m k i hik hface hd).elim
      · omega
    right
    right
    apply facePPP_middle_column_owner m k i hface C
    rw [hn1] at heq
    exact heq
  · right
    left
    have hadj : tetrahedralLattice.Adj (faceFourStep p k i l) (step (step (step p k) i) l) :=
      (step_adj _ _).symm
    exact DanglingColumn.owner_eq_of_dangling_point_eq C n hq
      ⟨hout.2.2, faceFourStep p k i l, hq, hadj⟩ hadj heq

theorem facePPPFold_ne_column_of_owner_ne (m : ℕ) (p : Site) (k i l : Fin 4)
    (hil : i ≠ l) (hik : i ≠ k) (hlk : l ≠ k)
    (hface : OctBigFace m k p ∨ OctSmallFace m k p)
    (hq : faceFourStep p k i l ∈ octahedron m) (C : DanglingColumn m)
    (hpne : C.owner ≠ p) (hqne : C.owner ≠ faceFourStep p k i l)
    (hrowne : C.owner ≠ step (step p (columnOpposite k)) i) (n : ℕ) (r : Fin 3) :
    (facePPPFold p k i l hil).pos r ≠ C.point n := by
  intro heq
  rcases facePPPFold_column_owner m p k i l hil hik hlk hface hq C n r heq.symm with h | h | h
  · exact hpne h
  · exact hqne h
  · exact hrowne h.2

end ProteinFolding.Tetrahedral
