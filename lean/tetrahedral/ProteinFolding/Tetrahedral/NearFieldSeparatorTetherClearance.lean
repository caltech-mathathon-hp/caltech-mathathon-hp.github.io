import ProteinFolding.Tetrahedral.NearFieldDimerTethers
import ProteinFolding.Tetrahedral.NearFieldSeparatorChains
import ProteinFolding.Tetrahedral.NearFieldInnerEdgeSeparation

/-! All three prescribed separator-chain pieces avoid every actual tether. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

theorem tetherSource_owner_inB (p : ConstructionParameters) (t : TetherIndex p) :
    InBSublattice (tetherSourceColumn p t).owner.val := by
  rcases t with ⟨b, k⟩
  cases b
  · change InBSublattice (faceSurfaceCoordinates p.side (entryAnchorA p k.val) (3 * (k.val + 1)) 0)
    exact faceSurfaceCoordinates_inB p.side 0 _ _ _ (entryAnchor_equation p k.val (by omega))
  · change InBSublattice (faceSurfaceCoordinates p.side (p.side - 3 - p.separatorIndex k.val) 0 (p.separatorIndex k.val + 1))
    exact faceSurfaceCoordinates_inB p.side 0 _ _ _ (by have h := p.separator_room k.val (by omega); omega)

theorem tetherTarget_owner_inB (p : ConstructionParameters) (t : TetherIndex p) :
    InBSublattice (tetherTargetColumn p t).owner.val := by
  rcases t with ⟨b, k⟩
  cases b
  · change InBSublattice (faceSurfaceCoordinates p.side (p.side - 2 - p.separatorIndex k.val) 0 (p.separatorIndex k.val))
    exact faceSurfaceCoordinates_inB p.side 0 _ _ _ (by have h := p.separator_room k.val (by omega); omega)
  · change InBSublattice (faceSurfaceCoordinates p.side 0 (5 * p.exitSlot k.val + 3) (p.side - 5 - 5 * p.exitSlot k.val))
    exact faceSurfaceCoordinates_inB p.side 0 _ _ _ (by have h := p.exit_column_triangle_room k.val; omega)

theorem twoDimerEvenBase_Bowner_excluded {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (a : ℕ)
    (x : Site) (hx : InBSublattice x.val) : DimerLinkOwnerExcluded m F (2 * a) 1 true x := by
  intro j hj s heq
  have hj0 : j = 0 := by omega
  subst j
  have hi : dimerLinkIndex (2 * a) true 0 + 2 * s.val = 2 * (a + s.val) := by
    dsimp [dimerLinkIndex, dimerFlip]
    omega
  have hA := (octEdgeZigzag_even hm F (a + s.val)).1
  rw [hi] at heq
  rw [heq] at hx
  exact sublattices_disjoint _ hA hx

theorem dimerLinkOwnerExcluded_inner_other_pair {m : ℕ} (hm : 3 ≤ m) (F : OctEdgeFrame)
    (base q : ℕ) (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1)
    (G : OctEdgeFrame) (i : ℕ) (hilo : 2 ≤ i) (hihi : i + 2 ≤ 2 * m - 2)
    (hpair : F.k ≠ G.k ∨ F.j ≠ G.j) :
    DimerLinkOwnerExcluded m F base q reverse (octEdgeZigzag m G i) := by
  intro j hj a
  have hb := dimerLinkIndex_bounds base reverse j
  have ha := a.isLt
  exact innerEdgePoint_ne_other_pair hm G i hilo hihi F _ (by omega) hpair

theorem separatorExit_source_excluded (p : ConstructionParameters) (k : ℕ) (t : TetherIndex p) :
    DimerLinkOwnerExcluded p.side exitEdgeFrame (10 * p.exitSlot k + 6) 2 true
      (tetherSourceColumn p t).owner := by
  rcases t with ⟨b, l⟩
  have hl : l.val ≤ p.bins := by omega
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  cases b
  · change DimerLinkOwnerExcluded _ _ _ _ _ (faceDanglingColumn _ _ _ _ _).owner
    rw [entrySource_owner p l.val hl]
    apply dimerLinkOwnerExcluded_inner_other_pair hm _ _ _ _ (separatorExit_room p k)
      entryEdgeFrame (6 * (l.val + 1) + 1) (by omega) _ (Or.inl (by decide))
    have h := p.entry_column_triangle_room l.val hl
    omega
  · change DimerLinkOwnerExcluded _ _ _ _ _ (exitSourceColumn p l.val hl).owner
    rw [exitSource_owner p l.val hl]
    apply dimerLinkOwnerExcluded_inner_other_pair hm _ _ _ _ (separatorExit_room p k)
      trackEdgeFrame (2 * p.separatorIndex l.val + 3) _ _ (Or.inl (by decide))
    · have h := separatorIndex_ge_two p l.val; omega
    · have h := p.separator_room l.val hl; have hfill := p.rightFiller_ge; omega

theorem separatorExit_target_excluded (p : ConstructionParameters) (k : ℕ) (t : TetherIndex p) :
    DimerLinkOwnerExcluded p.side exitEdgeFrame (10 * p.exitSlot k + 6) 2 true
      (tetherTargetColumn p t).owner := by
  rcases t with ⟨b, l⟩
  have hl : l.val ≤ p.bins := by omega
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  cases b
  · change DimerLinkOwnerExcluded _ _ _ _ _ (entryTargetColumn p l.val hl).owner
    rw [entryTarget_owner p l.val hl]
    apply dimerLinkOwnerExcluded_inner_other_pair hm _ _ _ _ (separatorExit_room p k)
      trackEdgeFrame (2 * p.separatorIndex l.val + 1) _ _ (Or.inl (by decide))
    · have h := separatorIndex_ge_two p l.val; omega
    · have h := p.separator_room l.val hl; omega
  · change DimerLinkOwnerExcluded _ _ _ _ _ (exitTargetColumn p l.val).owner
    rw [exitTarget_owner p l.val]
    intro j hj a heq
    have hi := octEdgeZigzag_injective (by omega : 1 ≤ p.side) exitEdgeFrame heq
    have hjc : j = 0 ∨ j = 1 := by omega
    rcases hjc with rfl | rfl <;> fin_cases a <;> dsimp [dimerLinkIndex, dimerFlip] at hi <;> omega

theorem separatorEntryChain_ne_tether (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (t : TetherIndex p) (i : Fin (dimerChain 1).length) (j : Fin (tetherCount p t)) :
    (separatorEntryChain p k hk).pos i ≠ (tetherFold p t).pos j := by
  apply edgeDimerFold_ne_tetherFold p t entryEdgeFrame (6 * (k + 1)) 0 false (separatorEntry_room p k hk)
  · omega
  · intro j hj
    omega
  · intro j hj
    omega

theorem separatorCenterChain_ne_tether (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (t : TetherIndex p) (i : Fin (dimerChain 2).length) (j : Fin (tetherCount p t)) :
    (separatorCenterChain p k hk).pos i ≠ (tetherFold p t).pos j := by
  apply edgeDimerFold_ne_tetherFold p t trackEdgeFrame (2 * p.separatorIndex k) 1 true (separatorCenter_room p k hk)
  · intro _
    exact Or.inl (by decide)
  · exact twoDimerEvenBase_Bowner_excluded (by have h := p.side_ge; omega) _ _ _ (tetherSource_owner_inB p t)
  · exact twoDimerEvenBase_Bowner_excluded (by have h := p.side_ge; omega) _ _ _ (tetherTarget_owner_inB p t)

theorem separatorExitChain_ne_tether (p : ConstructionParameters) (k : ℕ)
    (t : TetherIndex p) (i : Fin (dimerChain 3).length) (j : Fin (tetherCount p t)) :
    (separatorExitChain p k).pos i ≠ (tetherFold p t).pos j := by
  apply edgeDimerFold_ne_tetherFold p t exitEdgeFrame (10 * p.exitSlot k + 6) 2 true (separatorExit_room p k)
  · intro _
    exact Or.inl (by decide)
  · exact separatorExit_source_excluded p k t
  · exact separatorExit_target_excluded p k t

end ProteinFolding.Tetrahedral.NearField
