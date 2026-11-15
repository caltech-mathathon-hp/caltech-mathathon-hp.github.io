import ProteinFolding.Tetrahedral.FrameForcingTrackHeights
import ProteinFolding.Tetrahedral.FrameForcingOccurrences

/-! Bond-length bounds for the two frame heights.  An exterior P3 link
has an ambient two-bond shortcut, so its height change is at most four. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem path_height_bounds {word : Sequence} {m : ℕ} (P : OctWordPath m word)
    (h : Site → ℤ)
    (hstep : ∀ {x y}, tetrahedralLattice.Adj x y → -2 ≤ h y - h x ∧ h y - h x ≤ 2)
    (a n : ℕ) (hbound : a + n < word.length) :
    -2 * (n : ℤ) ≤ h (P.site (a + n)) - h (P.site a) ∧
      h (P.site (a + n)) - h (P.site a) ≤ 2 * (n : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hb : a + n < word.length := by omega
    have hprev := ih hb
    have hs := hstep (P.adjacent (a + n) (by omega))
    have heq : a + (n + 1) = (a + n) + 1 := by omega
    rw [heq]
    push_cast
    omega

theorem two_face_height_triangular_bounds (m : ℕ) {a b : Fin 4} (hab : a ≠ b) {p q : Site}
    (h : OctTriangularNeighbours m p q) :
    -4 ≤ (tetraCoordinate m q.val a + tetraCoordinate m q.val b) -
      (tetraCoordinate m p.val a + tetraCoordinate m p.val b) ∧
    (tetraCoordinate m q.val a + tetraCoordinate m q.val b) -
      (tetraCoordinate m p.val a + tetraCoordinate m p.val b) ≤ 4 := by
  have hshortcut : ∃ t, tetrahedralLattice.Adj p t ∧ tetrahedralLattice.Adj t q := by
    rcases p.property with hp | hp
    · obtain ⟨i, l, _, rfl⟩ := triangular_neighbours_A_step hp h
      exact ⟨step p l, (adj_iff_exists_step _ _).mpr ⟨l, rfl⟩,
        (adj_iff_exists_step _ _).mpr ⟨i, rfl⟩⟩
    · obtain ⟨i, l, _, rfl⟩ := triangular_neighbours_B_step hp h
      exact ⟨step p l, (adj_iff_exists_step _ _).mpr ⟨l, rfl⟩,
        (adj_iff_exists_step _ _).mpr ⟨i, rfl⟩⟩
  obtain ⟨t, hpt, htq⟩ := hshortcut
  have hp := two_face_height_adj_bounds m hab hpt
  have hq := two_face_height_adj_bounds m hab htq
  omega

theorem frameH2_adj_bounds (m : ℕ) (F : OctEdgeFrame) {p q : Site}
    (h : tetrahedralLattice.Adj p q) :
    -2 ≤ frameH2 m F q - frameH2 m F p ∧ frameH2 m F q - frameH2 m F p ≤ 2 :=
  two_face_height_adj_bounds m F.ab h

theorem frameK2_adj_bounds (m : ℕ) (F : OctEdgeFrame) {p q : Site}
    (h : tetrahedralLattice.Adj p q) :
    -2 ≤ frameK2 m F q - frameK2 m F p ∧ frameK2 m F q - frameK2 m F p ≤ 2 :=
  two_face_height_adj_bounds m (Ne.symm F.ja) h

theorem frameH2_triangular_bounds (m : ℕ) (F : OctEdgeFrame) {p q : Site}
    (h : OctTriangularNeighbours m p q) :
    -4 ≤ frameH2 m F q - frameH2 m F p ∧ frameH2 m F q - frameH2 m F p ≤ 4 :=
  two_face_height_triangular_bounds m F.ab h

theorem frameK2_triangular_bounds (m : ℕ) (F : OctEdgeFrame) {p q : Site}
    (h : OctTriangularNeighbours m p q) :
    -4 ≤ frameK2 m F q - frameK2 m F p ∧ frameK2 m F q - frameK2 m F p ≤ 4 :=
  two_face_height_triangular_bounds m (Ne.symm F.ja) h

theorem quartet_height_bounds (h : Site → ℤ) (a b c d : Site)
    (hab : -2 ≤ h b - h a ∧ h b - h a ≤ 2)
    (hbc : -4 ≤ h c - h b ∧ h c - h b ≤ 4)
    (hcd : -2 ≤ h d - h c ∧ h d - h c ≤ 2) :
    ∀ x ∈ ({a, b, c, d} : Finset Site),
      -8 ≤ h x - h a ∧ h x - h a ≤ 8 ∧
      -8 ≤ h x - h d ∧ h x - h d ≤ 8 := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> omega

end ProteinFolding.Tetrahedral
