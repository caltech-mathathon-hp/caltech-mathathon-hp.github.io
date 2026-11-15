import ProteinFolding.Tetrahedral.NearFieldRingPPPSeparation

/-! All six ring-side terminal H sites are distinct. Every one is excluded
from all internal chain-link owners. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def ringTerminalSite (m : ℕ) (F : OctEdgeFrame) (i : Fin 3) (e : Fin 2) : Site :=
  octEdgeZigzag m (ringSideFrame F i) (if e = 0 then 1 else 2 * m - 5)

theorem ringTerminalSite_mem (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) (i : Fin 3) (e : Fin 2) :
    ringTerminalSite m F i e ∈ edgeDimerHsites m (ringSideFrame F i) 1 (m - 3) := by
  apply Finset.mem_image.mpr
  fin_cases e
  · refine ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
    rfl
  · refine ⟨⟨2 * m - 6, by omega⟩, Finset.mem_univ _, ?_⟩
    change octEdgeZigzag m (ringSideFrame F i) (1 + (2 * m - 6)) =
      octEdgeZigzag m (ringSideFrame F i) (2 * m - 5)
    congr 1
    omega

theorem ringTerminalSite_injective (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0) (F : OctEdgeFrame) :
    Function.Injective (fun ie : Fin 3 × Fin 2 => ringTerminalSite m F ie.1 ie.2) := by
  rintro ⟨i, e⟩ ⟨j, e'⟩ heq
  change ringTerminalSite m F i e = ringTerminalSite m F j e' at heq
  have hij : i = j := by
    by_contra hne
    have hdis := ringSideHsites_pairwise m hm F i j hne
    have hmem := ringTerminalSite_mem m hm F i e
    rw [heq] at hmem
    exact Finset.disjoint_left.mp hdis hmem (ringTerminalSite_mem m hm F j e')
  subst j
  have hindices := octEdgeZigzag_injective (by omega : 1 ≤ m) (ringSideFrame F i) heq
  have hee : e = e' := by
    fin_cases e <;> fin_cases e'
    all_goals first
      | rfl
      | (change (1 : ℕ) = 2 * m - 5 at hindices; omega)
      | (change 2 * m - 5 = (1 : ℕ) at hindices; omega)
  subst e'
  rfl

theorem ringTerminal_linkOwnerExcluded (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (i j : Fin 3) (e : Fin 2) :
    DimerLinkOwnerExcluded m (ringSideFrame F i) 1 (m - 3) false
      (ringTerminalSite m F j e) := by
  by_cases hij : i = j
  · subst j
    fin_cases e
    · simpa only [ringTerminalSite, dimerHIndex, dimerFlip] using
        dimerLinkOwnerExcluded_first (by omega : 1 ≤ m) (ringSideFrame F i) 1 (m - 3) false
    · have hidx : dimerHIndex 1 false (m - 3) 1 = 2 * m - 5 := by
        dsimp [dimerHIndex, dimerFlip]
        omega
      simpa only [ringTerminalSite, hidx] using
        dimerLinkOwnerExcluded_last (by omega : 1 ≤ m) (ringSideFrame F i) 1 (m - 3) false
  · apply dimerLinkOwnerExcluded_of_not_mem
    intro hmem
    exact Finset.disjoint_left.mp (ringSideHsites_pairwise m hm F i j hij) hmem
      (ringTerminalSite_mem m hm F j e)

theorem ringSideFrame_succ (F : OctEdgeFrame) (i : Fin 2) :
    ringNextFrame (ringSideFrame F i.castSucc) = ringSideFrame F i.succ := by
  fin_cases i <;> rfl

theorem ringCorner_start_owner (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) (i : Fin 2) :
    octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame F i.castSucc)) 1 =
      ringTerminalSite m F i.succ 0 := by
  change octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame F i.castSucc)) 1 =
    octEdgeZigzag m (ringSideFrame F i.succ) 1
  rw [ringNext_start_corner m (by omega), ringSideFrame_succ]

theorem ringCorner_end_owner (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) (i : Fin 2) :
    octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame F i.castSucc)) 3 =
      ringTerminalSite m F i.castSucc 1 := by
  change octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame F i.castSucc)) 3 =
    octEdgeZigzag m (ringSideFrame F i.castSucc) (2 * m - 5)
  exact (ringSide_last_eq_reverse_three m hm (ringSideFrame F i.castSucc)).symm

end ProteinFolding.Tetrahedral.NearField
