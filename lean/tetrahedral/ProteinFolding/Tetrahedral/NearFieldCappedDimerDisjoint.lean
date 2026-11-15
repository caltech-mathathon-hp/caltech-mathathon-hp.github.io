import ProteinFolding.Tetrahedral.NearFieldDimerChainCaps
import ProteinFolding.Tetrahedral.NearFieldDimerChainDisjoint
import ProteinFolding.Tetrahedral.NearFieldCapFoldSites

/-! Distinct physical H intervals separate the complete capped chain units. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem cappedEdgeDimerFold_sites {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse q 1)) :
    foldSites (cappedEdgeDimerFold hm F base q reverse hroom C D hC hD) =
      ({C.seed} ∪ foldSites (edgeDimerFold hm F base q reverse hroom)) ∪ {D.seed} :=
  cappedWordFold_sites _ _ _ _ _ _ _ _ _

theorem cappedDimer_cap_ne_of_disjoint_Hsites (m : ℕ) (F G : OctEdgeFrame)
    (base q base' q' : ℕ)
    (hdis : Disjoint (edgeDimerHsites m F base q) (edgeDimerHsites m G base' q'))
    (C D : DanglingColumn m) (hC : C.owner ∈ edgeDimerHsites m F base q)
    (hD : D.owner ∈ edgeDimerHsites m G base' q') : C.seed ≠ D.seed := by
  apply dangling_caps_ne_of_owner_ne m C.owner D.owner C.dir D.dir C.owner_mem D.owner_mem C.seed_outside
  intro heq
  rw [heq] at hC
  exact Finset.disjoint_left.mp hdis hC hD

theorem cappedEdgeDimerFolds_disjoint {m : ℕ} (hm : 1 ≤ m) (F G : OctEdgeFrame)
    (base q base' q' : ℕ) (reverse reverse' : Bool)
    (hroom : base + 2 * (q + 1) ≤ 2 * m - 1)
    (hroom' : base' + 2 * (q' + 1) ≤ 2 * m - 1)
    (hdis : Disjoint (edgeDimerHsites m F base q) (edgeDimerHsites m G base' q'))
    (C D C' D' : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse q 1))
    (hC' : C'.owner = octEdgeZigzag m G (dimerHIndex base' reverse' 0 0))
    (hD' : D'.owner = octEdgeZigzag m G (dimerHIndex base' reverse' q' 1)) :
    Disjoint (foldSites (cappedEdgeDimerFold hm F base q reverse hroom C D hC hD))
      (foldSites (cappedEdgeDimerFold hm G base' q' reverse' hroom' C' D' hC' hD')) := by
  have hCm : C.owner ∈ edgeDimerHsites m F base q := by rw [hC]; exact dimerHIndex_mem_Hsites m F base q reverse 0 (by omega) 0
  have hDm : D.owner ∈ edgeDimerHsites m F base q := by rw [hD]; exact dimerHIndex_mem_Hsites m F base q reverse q le_rfl 1
  have hC'm : C'.owner ∈ edgeDimerHsites m G base' q' := by rw [hC']; exact dimerHIndex_mem_Hsites m G base' q' reverse' 0 (by omega) 0
  have hD'm : D'.owner ∈ edgeDimerHsites m G base' q' := by rw [hD']; exact dimerHIndex_mem_Hsites m G base' q' reverse' q' le_rfl 1
  have hnot (X : DanglingColumn m) (hX : X.owner ∈ edgeDimerHsites m F base q) : X.owner ∉ edgeDimerHsites m G base' q' :=
    fun hx => Finset.disjoint_left.mp hdis hX hx
  have hnot' (X : DanglingColumn m) (hX : X.owner ∈ edgeDimerHsites m G base' q') : X.owner ∉ edgeDimerHsites m F base q :=
    fun hx => Finset.disjoint_left.mp hdis hx hX
  rw [cappedEdgeDimerFold_sites, cappedEdgeDimerFold_sites]
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  simp only [Finset.mem_union, Finset.mem_singleton] at hp hp'
  rcases hp with (rfl | hp) | rfl
  · rcases hp' with (h | hp') | h
    · exact cappedDimer_cap_ne_of_disjoint_Hsites m F G base q base' q' hdis C C' hCm hC'm h
    · obtain ⟨i, hi⟩ := (mem_foldSites _ _).mp hp'
      exact edgeDimerFold_ne_cap_of_owner_not_mem hm G base' q' reverse' hroom' C (hnot C hCm) i hi
    · exact cappedDimer_cap_ne_of_disjoint_Hsites m F G base q base' q' hdis C D' hCm hD'm h
  · obtain ⟨i, rfl⟩ := (mem_foldSites _ _).mp hp
    rcases hp' with (h | hp') | h
    · exact edgeDimerFold_ne_cap_of_owner_not_mem hm F base q reverse hroom C' (hnot' C' hC'm) i h
    · obtain ⟨i', hi'⟩ := (mem_foldSites _ _).mp hp'
      exact edgeDimerFolds_disjoint hm F G base q base' q' reverse reverse' hroom hroom' hdis i i' hi'.symm
    · exact edgeDimerFold_ne_cap_of_owner_not_mem hm F base q reverse hroom D' (hnot' D' hD'm) i h
  · rcases hp' with (h | hp') | h
    · exact cappedDimer_cap_ne_of_disjoint_Hsites m F G base q base' q' hdis D C' hDm hC'm h
    · obtain ⟨i, hi⟩ := (mem_foldSites _ _).mp hp'
      exact edgeDimerFold_ne_cap_of_owner_not_mem hm G base' q' reverse' hroom' D (hnot D hDm) i hi
    · exact cappedDimer_cap_ne_of_disjoint_Hsites m F G base q base' q' hdis D D' hDm hD'm h

end ProteinFolding.Tetrahedral.NearField
