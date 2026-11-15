import ProteinFolding.Tetrahedral.NearFieldPPPEdges
import ProteinFolding.Tetrahedral.NearFieldPPPColumnIntersections

/-! Only the four X-plane edge pairs can bring a dimer PPP onto a
non-endpoint column; its owner is the explicit second-row site below. -/

namespace ProteinFolding.Tetrahedral

def edgeASecondRowOwner (m : ℕ) (F : OctEdgeFrame) (r : ℕ) : Site :=
  step (step (octEdgeZigzag m F r) F.j) F.b

def edgeBSecondRowOwner (m : ℕ) (F : OctEdgeFrame) (r : ℕ) : Site :=
  step (step (octEdgeZigzag m F r) F.k) F.a

theorem edgePPPFold_column_owner {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hr : r + 2 < 2 * m - 1) (C : DanglingColumn m) (n : ℕ) (s : Fin 3)
    (heq : C.point n = (edgePPPFold m F r).pos s) :
    C.owner = octEdgeZigzag m F r ∨ C.owner = octEdgeZigzag m F (r + 2) ∨
      (columnOpposite F.k = F.j ∧ InASublattice (octEdgeZigzag m F r).val ∧
        C.owner = edgeASecondRowOwner m F r) ∨
      (columnOpposite F.j = F.k ∧ InBSublattice (octEdgeZigzag m F r).val ∧
        C.owner = edgeBSecondRowOwner m F r) := by
  have hq : faceFourStep (octEdgeZigzag m F r) (edgePPPNormal F (octEdgeZigzag m F r))
      (edgePPPBack F (octEdgeZigzag m F r)) (edgePPPForward F (octEdgeZigzag m F r)) ∈ octahedron m := by
    rw [edgePPP_endpoint]
    rcases octEdgeZigzag_mem hm F hr with h | h
    · exact h.1.1
    · exact h.1.1
  have h := facePPPFold_column_owner m _ _ _ _ (edgePPPLateral_ne F _) (edgePPP_back_ne_normal F _)
    (edgePPP_forward_ne_normal F _) (edgePPP_normal_face hm F r (by omega)) hq C n s heq
  rw [edgePPP_endpoint] at h
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · by_cases hpA : InASublattice (octEdgeZigzag m F r).val
    · have ho : C.owner = step (step (octEdgeZigzag m F r) (columnOpposite F.k)) F.b := by
        simpa only [edgePPPNormal, edgePPPBack, if_pos hpA] using h.2
      rcases F.index_cases (columnOpposite F.k) with hk | hj | ha | hb
      · exact (columnOpposite_ne F.k hk).elim
      · exact Or.inr (Or.inr (Or.inl ⟨hj, hpA, by simpa only [hj, edgeASecondRowOwner] using ho⟩))
      · have hend := edgePPP_endpoint m F r
        simp only [edgePPPNormal, edgePPPBack, edgePPPForward, if_pos hpA,
          faceFourStep_eq_twoStep] at hend
        exact Or.inr (Or.inl (by rw [ha] at ho; exact ho.trans hend))
      · exact Or.inl (by simpa only [hb, step_step] using ho)
    · have hpB := (inB_iff_not_inA _).mpr hpA
      have ho : C.owner = step (step (octEdgeZigzag m F r) (columnOpposite F.j)) F.a := by
        simpa only [edgePPPNormal, edgePPPBack, if_neg hpA] using h.2
      rcases F.index_cases (columnOpposite F.j) with hk | hj | ha | hb
      · exact Or.inr (Or.inr (Or.inr ⟨hk, hpB, by simpa only [hk, edgeBSecondRowOwner] using ho⟩))
      · exact (columnOpposite_ne F.j hj).elim
      · exact Or.inl (by simpa only [ha, step_step] using ho)
      · have hend := edgePPP_endpoint m F r
        simp only [edgePPPNormal, edgePPPBack, edgePPPForward, if_neg hpA,
          faceFourStep_eq_twoStep] at hend
        exact Or.inr (Or.inl (by rw [hb] at ho; exact ho.trans hend))

theorem edgePPPFold_ne_column_of_owner_ne {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hr : r + 2 < 2 * m - 1) (C : DanglingColumn m)
    (hpne : C.owner ≠ octEdgeZigzag m F r) (hqne : C.owner ≠ octEdgeZigzag m F (r + 2))
    (hA : columnOpposite F.k = F.j → C.owner ≠ edgeASecondRowOwner m F r)
    (hB : columnOpposite F.j = F.k → C.owner ≠ edgeBSecondRowOwner m F r)
    (n : ℕ) (s : Fin 3) : (edgePPPFold m F r).pos s ≠ C.point n := by
  intro heq
  rcases edgePPPFold_column_owner hm F r hr C n s heq.symm with h | h | h | h
  · exact hpne h
  · exact hqne h
  · exact hA h.1 h.2.2
  · exact hB h.1 h.2.2

theorem columnOpposite_pair_cases (k j : Fin 4) : columnOpposite k = j ↔
    (k = 0 ∧ j = 1) ∨ (k = 1 ∧ j = 0) ∨ (k = 2 ∧ j = 3) ∨ (k = 3 ∧ j = 2) := by
  revert k j
  decide

end ProteinFolding.Tetrahedral
