import ProteinFolding.Tetrahedral.OctahedralP3LinksHelpers

/-! Section 5.6 (O2): exterior three-P links are exactly face-triangle steps. -/

namespace ProteinFolding.Tetrahedral

/-- A self-avoiding four-bond path with its three internal sites outside. -/
def ExteriorP3Link (m : ℕ) (p q : Site) : Prop :=
  p ∈ octahedron m ∧ q ∈ octahedron m ∧ ∃ a b c : Site,
    tetrahedralLattice.Adj p a ∧ tetrahedralLattice.Adj a b ∧
    tetrahedralLattice.Adj b c ∧ tetrahedralLattice.Adj c q ∧
    a ∉ octahedron m ∧ b ∉ octahedron m ∧ c ∉ octahedron m ∧
    Function.Injective (![p, a, b, c, q] : Fin 5 → Site)

/-- Nearest neighbours in one of the eight triangular face lattices. The
directions i,l differ from the face normal k and from one another. -/
def OctTriangularNeighbours (m : ℕ) (p q : Site) : Prop :=
  ∃ k i l : Fin 4, i ≠ l ∧ i ≠ k ∧ l ≠ k ∧
    ((OctBigFace m k p ∧ OctBigFace m k q ∧
      ∀ a : Fin 3, q.val a = p.val a + bondVector l a - bondVector i a) ∨
     (OctSmallFace m k p ∧ OctSmallFace m k q ∧
      ∀ a : Fin 3, q.val a = p.val a - bondVector l a + bondVector i a))

theorem exterior_P3_link_triangular (m : ℕ) {p q : Site} (h : ExteriorP3Link m p q) :
    OctTriangularNeighbours m p q := by
  obtain ⟨hp, hq, a, b, c, h0, h1, h2, h3, hout, _, _, hinj⟩ := h
  have hpb : p ≠ b := by
    intro he
    have hbad := hinj (show (![p, a, b, c, q] : Fin 5 → Site) 0 =
      (![p, a, b, c, q] : Fin 5 → Site) 2 from he)
    exact (by decide : (0 : Fin 5) ≠ 2) hbad
  have hac : a ≠ c := by
    intro he
    have hbad := hinj (show (![p, a, b, c, q] : Fin 5 → Site) 1 =
      (![p, a, b, c, q] : Fin 5 → Site) 3 from he)
    exact (by decide : (1 : Fin 5) ≠ 3) hbad
  obtain ⟨k, rfl⟩ := (adj_iff_exists_step p a).mp h0
  obtain ⟨i, rfl⟩ := (adj_iff_exists_step (step p k) b).mp h1
  obtain ⟨l, rfl⟩ := (adj_iff_exists_step (step (step p k) i) c).mp h2
  obtain ⟨n, rfl⟩ := (adj_iff_exists_step (step (step (step p k) i) l) q).mp h3
  obtain ⟨hn, hik, hlk, hil⟩ := exterior_four_bond_directions m p k i l n hp hout hq
    (Ne.symm hpb) (Ne.symm hac)
  subst n
  refine ⟨k, i, l, hil, hik, hlk, ?_⟩
  have hsame := faceFourStep_same_face m p k i l hik hlk
  rcases p.property with hpA | hpB
  · have hface := (step_not_mem_octahedron_A m hpA hp k).mp hout
    left
    refine ⟨⟨hp, hpA, hface⟩, ⟨hq,
      step_in_A (step_in_B (step_in_A (step_in_B hpA k) i) l) k, ?_⟩, ?_⟩
    · exact hsame.trans hface
    · exact faceFourStep_A_coordinates hpA k i l
  · have hface := (step_not_mem_octahedron_B m hpB hp k).mp hout
    right
    refine ⟨⟨hp, hpB, hface⟩, ⟨hq,
      step_in_B (step_in_A (step_in_B (step_in_A hpB k) i) l) k, ?_⟩, ?_⟩
    · exact hsame.trans hface
    · exact faceFourStep_B_coordinates hpB k i l

theorem face_four_bond_internal_sites_outside (m : ℕ) (p : Site) (k i l : Fin 4)
    (hik : i ≠ k) (hlk : l ≠ k)
    (hface : OctBigFace m k p ∨ OctSmallFace m k p) :
    step p k ∉ octahedron m ∧ step (step p k) i ∉ octahedron m ∧
      step (step (step p k) i) l ∉ octahedron m := by
  rcases hface with ⟨hp, hpA, hface⟩ | ⟨hp, hpB, hface⟩
  · have h1 := tetraCoordinate_step_A m hpA k k
    have h2 := tetraCoordinate_step_B m (step_in_B hpA k) i k
    have h3 := tetraCoordinate_step_A m (step_in_A (step_in_B hpA k) i) l k
    simp only [if_true, if_neg (Ne.symm hik), if_neg (Ne.symm hlk)] at h1 h2 h3
    refine ⟨?_, ?_, ?_⟩
    all_goals
      intro hin
      have hbound := ((mem_octahedron m _).mp hin k).2
      omega
  · have h1 := tetraCoordinate_step_B m hpB k k
    have h2 := tetraCoordinate_step_A m (step_in_A hpB k) i k
    have h3 := tetraCoordinate_step_B m (step_in_B (step_in_A hpB k) i) l k
    simp only [if_true, if_neg (Ne.symm hik), if_neg (Ne.symm hlk)] at h1 h2 h3
    refine ⟨?_, ?_, ?_⟩
    all_goals
      intro hin
      have hbound := ((mem_octahedron m _).mp hin k).1
      omega

theorem triangular_neighbours_exterior_P3_link (m : ℕ) {p q : Site}
    (h : OctTriangularNeighbours m p q) : ExteriorP3Link m p q := by
  obtain ⟨k, i, l, hil, hik, hlk, hface⟩ := h
  have hp : p ∈ octahedron m := hface.elim (fun h => h.1.1) (fun h => h.1.1)
  have hq : q ∈ octahedron m := hface.elim (fun h => h.2.1.1) (fun h => h.2.1.1)
  have hqeq : faceFourStep p k i l = q := by
    apply Subtype.ext
    funext a
    rcases hface with ⟨hpface, _, hd⟩ | ⟨hpface, _, hd⟩
    · exact (faceFourStep_A_coordinates hpface.2.1 k i l a).trans (hd a).symm
    · exact (faceFourStep_B_coordinates hpface.2.1 k i l a).trans (hd a).symm
  have hout := face_four_bond_internal_sites_outside m p k i l hik hlk
    (hface.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
  refine ⟨hp, hq, step p k, step (step p k) i, step (step (step p k) i) l,
    step_adj p k, step_adj (step p k) i, step_adj (step (step p k) i) l,
    ?_, hout.1, hout.2.1, hout.2.2, ?_⟩
  · rw [← hqeq]
    exact step_adj _ k
  · rw [← hqeq]
    apply four_bond_chain_injective
      (p := p) (a := step p k) (b := step (step p k) i)
      (c := step (step (step p k) i) l) (q := faceFourStep p k i l)
      (step_adj p k) (step_adj (step p k) i) (step_adj (step (step p k) i) l) (step_adj _ k)
    · exact Ne.symm (two_distinct_steps_ne p (Ne.symm hik))
    · exact Ne.symm (two_distinct_steps_ne (step p k) hil)
    · exact Ne.symm (two_distinct_steps_ne (step (step p k) i) hlk)

theorem exterior_P3_link_iff_triangular_neighbours (m : ℕ) (p q : Site) :
    ExteriorP3Link m p q ↔ OctTriangularNeighbours m p q :=
  ⟨exterior_P3_link_triangular m, triangular_neighbours_exterior_P3_link m⟩

end ProteinFolding.Tetrahedral
