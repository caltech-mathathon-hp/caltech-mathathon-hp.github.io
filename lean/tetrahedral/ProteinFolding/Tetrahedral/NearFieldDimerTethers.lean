import ProteinFolding.Tetrahedral.NearFieldPPPTethers
import ProteinFolding.Tetrahedral.NearFieldCappedDimerDisjoint
import ProteinFolding.Tetrahedral.NearFieldFrameTetherCaps

/-! Literal chains avoid the full tether family; the only owner conditions
are exclusions from internal chain-link endpoints. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

def DimerLinkOwnerExcluded (m : ℕ) (F : OctEdgeFrame) (base q : ℕ) (reverse : Bool) (p : Site) : Prop :=
  ∀ j, j < q → ∀ a : Fin 2, p ≠ octEdgeZigzag m F (dimerLinkIndex base reverse j + 2 * a.val)

theorem dimerLinkOwnerExcluded_of_not_mem (m : ℕ) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (p : Site) (hp : p ∉ edgeDimerHsites m F base q) :
    DimerLinkOwnerExcluded m F base q reverse p := by
  intro j hj a heq
  apply hp
  rw [heq]
  exact dimerLink_endpoint_mem_Hsites m F base q reverse j hj a

theorem dimerLinkOwnerExcluded_first {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (base q : ℕ) (reverse : Bool) :
    DimerLinkOwnerExcluded m F base q reverse (octEdgeZigzag m F (dimerHIndex base reverse 0 0)) := by
  intro j _ a heq
  exact dimerFirst_ne_link_endpoint base reverse j a (octEdgeZigzag_injective hm F heq)

theorem dimerLinkOwnerExcluded_last {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (base q : ℕ) (reverse : Bool) :
    DimerLinkOwnerExcluded m F base q reverse (octEdgeZigzag m F (dimerHIndex base reverse q 1)) := by
  intro j hj a heq
  exact dimerLast_ne_link_endpoint base reverse q j hj a (octEdgeZigzag_injective hm F heq)

theorem edgeDimerFold_ne_tetherFold (p : ConstructionParameters) (t : TetherIndex p)
    (F : OctEdgeFrame) (base q : ℕ) (reverse : Bool)
    (hroom : base + 2 * (q + 1) ≤ 2 * p.side - 1)
    (hpair : 0 < q → F.k ≠ 2 ∨ F.j ≠ 3)
    (hs : DimerLinkOwnerExcluded p.side F base q reverse (tetherSourceColumn p t).owner)
    (ht : DimerLinkOwnerExcluded p.side F base q reverse (tetherTargetColumn p t).owner)
    (i : Fin (dimerChain (q + 1)).length) (j : Fin (tetherCount p t)) :
    (edgeDimerFold (by have h := p.side_ge; omega) F base q reverse hroom).pos i ≠ (tetherFold p t).pos j := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  rcases edgeDimerFold_pos_cases hm F base q reverse hroom i with ⟨k, hk, s, he⟩ | ⟨k, hk, s, he⟩
  · rw [he]
    intro heq
    have hmem := edgeDimerHsites_subset_oct hm F base q hroom
      (dimerHIndex_mem_Hsites p.side F base q reverse k hk s)
    rw [heq] at hmem
    exact tetherFold_outside p t j hmem
  · rw [he]
    have hb := dimerLinkIndex_bounds base reverse k
    exact edgePPPFold_ne_tetherFold p t F _ (by omega) (hpair (by omega))
      (by simpa using hs k hk 0) (by simpa using hs k hk 1)
      (by simpa using ht k hk 0) (by simpa using ht k hk 1) s j

theorem tetherSourceColumn_seed (p : ConstructionParameters) (t : TetherIndex p) :
    (tetherSourceColumn p t).seed = tetherSource p t := by
  rcases t with ⟨b, k⟩
  cases b <;> rfl

theorem tetherTargetColumn_seed (p : ConstructionParameters) (t : TetherIndex p) :
    (tetherTargetColumn p t).seed = tetherTarget p t := by
  rcases t with ⟨b, k⟩
  cases b <;> rfl

theorem danglingCap_ne_tetherFold (p : ConstructionParameters) (t : TetherIndex p)
    (C : DanglingColumn p.side)
    (hs : C.owner ≠ (tetherSourceColumn p t).owner)
    (ht : C.owner ≠ (tetherTargetColumn p t).owner) (i : Fin (tetherCount p t)) :
    C.seed ≠ (tetherFold p t).pos i := by
  intro heq
  have hd : IsDangling p.side ((tetherFold p t).pos i) := by
    rw [← heq]
    exact C.seed_dangling
  rcases tetherFold_dangling_eq_endpoint p t i hd with h | h
  · apply hs
    exact column_owner_eq_of_seed_eq C _ (heq.trans (h.trans (tetherSourceColumn_seed p t).symm))
  · apply ht
    exact column_owner_eq_of_seed_eq C _ (heq.trans (h.trans (tetherTargetColumn_seed p t).symm))

theorem cappedEdgeDimerFold_ne_tetherFold (p : ConstructionParameters) (t : TetherIndex p)
    (F : OctEdgeFrame) (base q : ℕ) (reverse : Bool)
    (hroom : base + 2 * (q + 1) ≤ 2 * p.side - 1)
    (hpair : 0 < q → F.k ≠ 2 ∨ F.j ≠ 3)
    (hs : DimerLinkOwnerExcluded p.side F base q reverse (tetherSourceColumn p t).owner)
    (ht : DimerLinkOwnerExcluded p.side F base q reverse (tetherTargetColumn p t).owner)
    (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag p.side F (dimerHIndex base reverse q 1))
    (hCs : C.owner ≠ (tetherSourceColumn p t).owner) (hCt : C.owner ≠ (tetherTargetColumn p t).owner)
    (hDs : D.owner ≠ (tetherSourceColumn p t).owner) (hDt : D.owner ≠ (tetherTargetColumn p t).owner)
    (i : Fin (capWord (dimerChain (q + 1))).length) (j : Fin (tetherCount p t)) :
    (cappedEdgeDimerFold (by have h := p.side_ge; omega) F base q reverse hroom C D hC hD).pos i ≠
      (tetherFold p t).pos j := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  intro heq
  have hmem := (mem_foldSites (cappedEdgeDimerFold hm F base q reverse hroom C D hC hD) _).mpr ⟨i, heq⟩
  rw [cappedEdgeDimerFold_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · exact danglingCap_ne_tetherFold p t C hCs hCt j h.symm
  · obtain ⟨k, hk⟩ := (mem_foldSites _ _).mp h
    exact edgeDimerFold_ne_tetherFold p t F base q reverse hroom hpair hs ht k j hk
  · exact danglingCap_ne_tetherFold p t D hDs hDt j h.symm

end ProteinFolding.Tetrahedral.NearField
