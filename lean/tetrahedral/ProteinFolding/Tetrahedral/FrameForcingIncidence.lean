import ProteinFolding.Tetrahedral.FrameForcingCaps

/-! The two possible incidences after the middle frame vertex uses different
big faces: a shared small face, or the opposite configuration. -/

namespace ProteinFolding.Tetrahedral

theorem octEdgeEnd_faces (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) :
    tetraCoordinate m (octEdgeZigzag m F (2 * m - 2)).val F.k = octRadius m ∧
      tetraCoordinate m (octEdgeZigzag m F (2 * m - 2)).val F.j = -octRadius m ∧
      tetraCoordinate m (octEdgeZigzag m F (2 * m - 2)).val F.a = octRadius m ∧
      tetraCoordinate m (octEdgeZigzag m F (2 * m - 2)).val F.b = -octRadius m := by
  obtain ⟨_, hk, hj, ha, hb⟩ := octEdgeZigzag_even hm F (m - 1)
  have hindex : 2 * (m - 1) = 2 * m - 2 := by omega
  rw [hindex] at hk hj ha hb
  refine ⟨hk, hj, ?_, ?_⟩ <;> dsimp [octRadius] at * <;> omega

theorem octEdgeEnd_high_indices (m : ℕ) (hm : 2 ≤ m) (F : OctEdgeFrame) (d : Fin 4)
    (hd : tetraCoordinate m (octEdgeZigzag m F (2 * m - 2)).val d = octRadius m) :
    d = F.k ∨ d = F.a := by
  obtain ⟨_, hj, _, hb⟩ := octEdgeEnd_faces m (by omega) F
  rcases F.index_cases d with h | h | h | h
  · exact Or.inl h
  · rw [h] at hd
    dsimp [octRadius] at hd hj
    omega
  · exact Or.inr h
  · rw [h] at hd
    dsimp [octRadius] at hd hb
    omega

theorem octEdgeEnd_low_indices (m : ℕ) (hm : 2 ≤ m) (F : OctEdgeFrame) (d : Fin 4)
    (hd : tetraCoordinate m (octEdgeZigzag m F (2 * m - 2)).val d = -octRadius m) :
    d = F.j ∨ d = F.b := by
  obtain ⟨hk, _, ha, _⟩ := octEdgeEnd_faces m (by omega) F
  rcases F.index_cases d with h | h | h | h
  · rw [h] at hd
    dsimp [octRadius] at hd hk
    omega
  · exact Or.inl h
  · rw [h] at hd
    dsimp [octRadius] at hd ha
    omega
  · exact Or.inr h

theorem frame_edges_incidence_cases (m : ℕ) (hm : 2 ≤ m) (F₁ F₂ : OctEdgeFrame)
    (hshare : octEdgeZigzag m F₁ (2 * m - 2) = octEdgeStart m F₂)
    (hbig : F₁.k ≠ F₂.k) :
    F₂.k = F₁.a ∧ F₂.b = F₁.k ∧
      ((F₂.j = F₁.j ∧ F₂.a = F₁.b) ∨ (F₂.j = F₁.b ∧ F₂.a = F₁.j)) := by
  obtain ⟨_, hk, hj, ha, hb⟩ := octEdgeStart_spec (show 1 ≤ m by omega) F₂
  rw [← hshare] at hk hj ha hb
  have hk' := octEdgeEnd_high_indices m hm F₁ F₂.k hk
  have hb' := octEdgeEnd_high_indices m hm F₁ F₂.b hb
  have hj' := octEdgeEnd_low_indices m hm F₁ F₂.j hj
  have ha' := octEdgeEnd_low_indices m hm F₁ F₂.a ha
  have hkEq : F₂.k = F₁.a := by
    rcases hk' with h | h
    · exact (hbig h.symm).elim
    · exact h
  have hbEq : F₂.b = F₁.k := by
    rcases hb' with h | h
    · exact h
    · have heq : F₂.k = F₂.b := hkEq.trans h.symm
      exact (F₂.kb heq).elim
  refine ⟨hkEq, hbEq, ?_⟩
  rcases hj' with hjEq | hjEq
  · left
    refine ⟨hjEq, ?_⟩
    rcases ha' with haEq | haEq
    · exact (F₂.ja (hjEq.trans haEq.symm)).elim
    · exact haEq
  · right
    refine ⟨hjEq, ?_⟩
    rcases ha' with haEq | haEq
    · exact haEq
    · exact (F₂.ja (hjEq.trans haEq.symm)).elim

end ProteinFolding.Tetrahedral
