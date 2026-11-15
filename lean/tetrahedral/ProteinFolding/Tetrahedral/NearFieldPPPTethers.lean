import ProteinFolding.Tetrahedral.NearFieldPPPTetherColumns

/-! Complete N4 tether walks avoid non-frame PPPs with different H endpoints. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

theorem skinOne_ne_entryRow (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (x : Site) (hx : x ∈ skin p.side 1) (i : Fin (entryRowCount p k)) :
    x ≠ (entryRowFold p k hk).pos i := by
  intro heq
  rw [heq] at hx
  exact Finset.disjoint_left.mp (skins_disjoint p.side 1 (p.entrySkin k)
    (by have h := p.tether_skin_bounds k hk; omega)) hx (entryRow_mem_skin p k hk i)

theorem skinOne_ne_exitRow (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (x : Site) (hx : x ∈ skin p.side 1) (i : Fin (exitRowCount p k)) :
    x ≠ (exitRowFold p k hk).pos i := by
  intro heq
  rw [heq] at hx
  exact Finset.disjoint_left.mp (skins_disjoint p.side 1 (p.exitSkin k)
    (by have h := p.tether_skin_bounds k hk; have hpos := p.bins_pos; omega)) hx (exitRow_mem_skin p k hk i)

theorem edgePPPFold_ne_entryTether (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (F : OctEdgeFrame) (r : ℕ) (hr : r + 2 < 2 * p.side - 1)
    (hpair : F.k ≠ 2 ∨ F.j ≠ 3)
    (hp : (entryTargetColumn p k hk).owner ≠ octEdgeZigzag p.side F r)
    (hq : (entryTargetColumn p k hk).owner ≠ octEdgeZigzag p.side F (r + 2))
    (s : Fin 3) (i : Fin (p.entryTether k)) :
    (edgePPPFold p.side F r).pos s ≠ (entryTetherFold p k hk).pos i := by
  apply entryTetherFold_property p k hk (fun x => (edgePPPFold p.side F r).pos s ≠ x) _ _ _ i
  · intro j
    exact edgePPPFold_ne_entryUp p k hk F r hr hpair s j
  · intro j
    exact skinOne_ne_entryRow p k hk _
      (edgePPPFold_mem_skin_one (by have h := p.side_ge; omega) F r hr s) j
  · intro j
    exact edgePPPFold_ne_entryTargetColumn p k hk F r hr hp hq s j.rev.val

theorem edgePPPFold_ne_exitTether (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (F : OctEdgeFrame) (r : ℕ) (hr : r + 2 < 2 * p.side - 1)
    (hsp : (exitSourceColumn p k hk).owner ≠ octEdgeZigzag p.side F r)
    (hsq : (exitSourceColumn p k hk).owner ≠ octEdgeZigzag p.side F (r + 2))
    (htp : (exitTargetColumn p k).owner ≠ octEdgeZigzag p.side F r)
    (htq : (exitTargetColumn p k).owner ≠ octEdgeZigzag p.side F (r + 2))
    (s : Fin 3) (i : Fin (p.exitTether k)) :
    (edgePPPFold p.side F r).pos s ≠ (exitTetherFold p k hk).pos i := by
  apply exitTetherFold_property p k hk (fun x => (edgePPPFold p.side F r).pos s ≠ x) _ _ _ i
  · intro j
    exact edgePPPFold_ne_exitSourceColumn p k hk F r hr hsp hsq s j.val
  · intro j
    exact skinOne_ne_exitRow p k hk _
      (edgePPPFold_mem_skin_one (by have h := p.side_ge; omega) F r hr s) j
  · intro j
    exact edgePPPFold_ne_exitTargetColumn p k F r hr htp htq s j.rev.val

def tetherSourceColumn (p : ConstructionParameters) (t : TetherIndex p) : DanglingColumn p.side :=
  if t.1 then exitSourceColumn p t.2.val (Nat.le_of_lt_succ t.2.isLt)
  else faceDanglingColumn p.side (entryAnchorA p t.2.val) (3 * (t.2.val + 1)) 0
    (entryAnchor_equation p t.2.val (Nat.le_of_lt_succ t.2.isLt))

def tetherTargetColumn (p : ConstructionParameters) (t : TetherIndex p) : DanglingColumn p.side :=
  if t.1 then exitTargetColumn p t.2.val
  else entryTargetColumn p t.2.val (Nat.le_of_lt_succ t.2.isLt)

theorem edgePPPFold_ne_tetherFold (p : ConstructionParameters) (t : TetherIndex p)
    (F : OctEdgeFrame) (r : ℕ) (hr : r + 2 < 2 * p.side - 1)
    (hpair : F.k ≠ 2 ∨ F.j ≠ 3)
    (hsp : (tetherSourceColumn p t).owner ≠ octEdgeZigzag p.side F r)
    (hsq : (tetherSourceColumn p t).owner ≠ octEdgeZigzag p.side F (r + 2))
    (htp : (tetherTargetColumn p t).owner ≠ octEdgeZigzag p.side F r)
    (htq : (tetherTargetColumn p t).owner ≠ octEdgeZigzag p.side F (r + 2))
    (s : Fin 3) (i : Fin (tetherCount p t)) :
    (edgePPPFold p.side F r).pos s ≠ (tetherFold p t).pos i := by
  rcases t with ⟨b, k⟩
  cases b
  · exact edgePPPFold_ne_entryTether p k.val (Nat.le_of_lt_succ k.isLt) F r hr hpair htp htq s i
  · exact edgePPPFold_ne_exitTether p k.val (Nat.le_of_lt_succ k.isLt) F r hr hsp hsq htp htq s i

end ProteinFolding.Tetrahedral.NearField
