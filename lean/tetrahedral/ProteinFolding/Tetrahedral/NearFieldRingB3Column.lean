import ProteinFolding.Tetrahedral.NearFieldPPPColumnMargins

/-! The last B3 ring column can meet a non-owner PPP only when that
PPP uses the common B corner. The ring omits the closing corner PPP. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem edgeBSecondRow_B3_endpoint (m : ℕ) (hm : 30 ≤ m) (F G : OctEdgeFrame)
    (r : ℕ)
    (hB : InBSublattice (octEdgeZigzag m F r).val)
    (heq : edgeBSecondRowOwner m F r = octEdgeZigzag m G 3) :
    octEdgeZigzag m G 1 = octEdgeZigzag m F r ∨
      octEdgeZigzag m G 1 = octEdgeZigzag m F (r + 2) := by
  have hm1 : 1 ≤ m := by omega
  have hmod := edgeZigzag_B_odd hm1 F r hB
  have hi : r = 2 * (r / 2) + 1 := by omega
  obtain ⟨_, hpk, hpj, hpa, hpb⟩ := octEdgeZigzag_odd hm1 F (r / 2)
  rw [← hi] at hpk hpj hpa hpb
  have hs (d : Fin 4) :
      tetraCoordinate m (edgeBSecondRowOwner m F r).val d =
        tetraCoordinate m (octEdgeZigzag m F r).val d -
          (if d = F.k then 4 else 0) + (if d = F.a then 4 else 0) := by
    unfold edgeBSecondRowOwner
    rw [tetraCoordinate_step_A m (step_in_A hB F.k), tetraCoordinate_step_B m hB]
    split_ifs <;> omega
  have hsk := hs F.k
  have hsj := hs F.j
  have hsa := hs F.a
  have hsb := hs F.b
  simp only [ite_true, if_neg F.ka] at hsk
  simp only [if_neg F.kj.symm, if_neg F.ja] at hsj
  simp only [if_neg F.ka.symm, ite_true] at hsa
  simp only [if_neg F.kb.symm, if_neg F.ab.symm] at hsb
  rw [hpk] at hsk
  rw [hpj] at hsj
  rw [hpa] at hsa
  rw [hpb] at hsb
  rw [heq] at hsk hsj hsa hsb
  obtain ⟨_, hgk, hgj, hga, hgb⟩ := octEdgeZigzag_odd hm1 G 1
  change tetraCoordinate m (octEdgeZigzag m G 3).val G.k = _ at hgk
  change tetraCoordinate m (octEdgeZigzag m G 3).val G.j = _ at hgj
  change tetraCoordinate m (octEdgeZigzag m G 3).val G.a = _ at hga
  change tetraCoordinate m (octEdgeZigzag m G 3).val G.b = _ at hgb
  have hfk : F.k = G.b := by
    rcases G.index_cases F.k with h | h | h | h
    · rw [h] at hsk
      dsimp [octRadius] at hsk hpk hgk
      omega
    · rw [h] at hsk
      dsimp [octRadius] at hsk hpk hgj
      omega
    · rw [h] at hsk
      dsimp [octRadius] at hsk hpk hga
      omega
    · exact h
  have hfj : F.j = G.j := by
    rcases G.index_cases F.j with h | h | h | h
    · rw [h] at hsj
      dsimp [octRadius] at hsj hpj hgk
      omega
    · exact h
    · rw [h] at hsj
      dsimp [octRadius] at hsj hpj hga
      omega
    · rw [h] at hsj
      dsimp [octRadius] at hsj hpj hgb
      omega
  obtain ⟨_, hck, hcj, hca, hcb⟩ := octEdgeZigzag_odd hm1 G 0
  change tetraCoordinate m (octEdgeZigzag m G 1).val G.k = _ at hck
  change tetraCoordinate m (octEdgeZigzag m G 1).val G.j = _ at hcj
  change tetraCoordinate m (octEdgeZigzag m G 1).val G.a = _ at hca
  change tetraCoordinate m (octEdgeZigzag m G 1).val G.b = _ at hcb
  rcases G.index_cases F.a with hfa | hfa | hfa | hfa
  · have hfb : F.b = G.a := by
      rcases G.index_cases F.b with h | h | h | h
      · exact (F.ab (hfa.trans h.symm)).elim
      · exact (F.jb (hfj.trans h.symm)).elim
      · exact h
      · exact (F.kb (hfk.trans h.symm)).elim
    right
    have hnext : r + 2 = 2 * (r / 2 + 1) + 1 := by omega
    obtain ⟨_, hqk, hqj, hqa, hqb⟩ := octEdgeZigzag_odd hm1 F (r / 2 + 1)
    rw [← hnext] at hqk hqj hqa hqb
    rw [hfa] at hsa
    rw [hfk] at hqk
    rw [hfj] at hqj
    rw [hfa] at hqa
    rw [hfb] at hqb
    apply Subtype.ext
    apply tetraCoordinate_injective m
    funext d
    rcases G.index_cases d with rfl | rfl | rfl | rfl
    all_goals dsimp [octRadius] at *
    all_goals push_cast at *
    all_goals omega
  · exact (F.ja (hfj.trans hfa.symm)).elim
  · have hfb : F.b = G.k := by
      rcases G.index_cases F.b with h | h | h | h
      · exact h
      · exact (F.jb (hfj.trans h.symm)).elim
      · exact (F.ab (hfa.trans h.symm)).elim
      · exact (F.kb (hfk.trans h.symm)).elim
    left
    rw [hfa] at hsa
    rw [hfk] at hpk
    rw [hfj] at hpj
    rw [hfa] at hpa
    rw [hfb] at hpb
    apply Subtype.ext
    apply tetraCoordinate_injective m
    funext d
    rcases G.index_cases d with rfl | rfl | rfl | rfl
    all_goals dsimp [octRadius] at *
    all_goals omega
  · exact (F.ka (hfk.trans hfa.symm)).elim

theorem edgePPPFold_ne_B3_column (m : ℕ) (hm : 30 ≤ m) (F G : OctEdgeFrame) (r : ℕ)
    (hr : r + 2 < 2 * m - 1) (C : DanglingColumn m)
    (howner : C.owner = octEdgeZigzag m G 3)
    (hpne : C.owner ≠ octEdgeZigzag m F r)
    (hqne : C.owner ≠ octEdgeZigzag m F (r + 2))
    (hcornerp : octEdgeZigzag m G 1 ≠ octEdgeZigzag m F r)
    (hcornerq : octEdgeZigzag m G 1 ≠ octEdgeZigzag m F (r + 2))
    (s : Fin 3) (n : ℕ) : (edgePPPFold m F r).pos s ≠ C.point n := by
  intro heq
  rcases edgePPPFold_column_owner (by omega : 1 ≤ m) F r hr C n s heq.symm with
    h | h | h | h
  · exact hpne h
  · exact hqne h
  · have hA : InASublattice C.owner.val := by
      rw [h.2.2]
      exact step_in_A (step_in_B h.2.1 F.j) F.b
    have hB : InBSublattice C.owner.val := by
      rw [howner]
      exact (octEdgeZigzag_odd (by omega : 1 ≤ m) G 1).1
    exact sublattices_disjoint _ hA hB
  · have hrow : edgeBSecondRowOwner m F r = octEdgeZigzag m G 3 :=
      h.2.2.symm.trans howner
    rcases edgeBSecondRow_B3_endpoint m hm F G r h.2.1 hrow with h | h
    · exact hcornerp h
    · exact hcornerq h

end ProteinFolding.Tetrahedral.NearField
