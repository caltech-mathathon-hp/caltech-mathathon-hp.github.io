import ProteinFolding.Tetrahedral.OctahedralP3Links
import ProteinFolding.Tetrahedral.OctahedralEdgeParametrization
import ProteinFolding.Tetrahedral.ColumnsSkins

/-! Explicit three-P face links and the links between consecutive edge dimers. -/

namespace ProteinFolding.Tetrahedral

def facePPPSite (p : Site) (k i l : Fin 4) (r : Fin 3) : Site :=
  if r = 0 then step p k else if r = 1 then step (step p k) i
  else step (step (step p k) i) l

theorem facePPPSite_injective (p : Site) (k i l : Fin 4) (hil : i ≠ l) :
    Function.Injective (facePPPSite p k i l) := by
  have h01 := tetrahedralLattice.ne_of_adj (step_adj (step p k) i)
  have h12 := tetrahedralLattice.ne_of_adj (step_adj (step (step p k) i) l)
  have h02 := Ne.symm (two_distinct_steps_ne (step p k) hil)
  intro r s heq
  fin_cases r <;> fin_cases s <;> simp_all [facePPPSite]

def facePPPFold (p : Site) (k i l : Fin 4) (hil : i ≠ l) : Fold tetrahedralLattice 3 where
  pos := facePPPSite p k i l
  injective_pos := facePPPSite_injective p k i l hil
  consecutive r s hrs := by
    fin_cases r <;> fin_cases s <;> simp [facePPPSite] at hrs ⊢
    all_goals exact step_adj _ _

theorem faceFourStep_eq_twoStep (p : Site) (k i l : Fin 4) :
    faceFourStep p k i l = step (step p l) i := by
  apply Subtype.ext
  funext a
  rcases p.property with hpA | hpB
  · rw [faceFourStep_A_coordinates hpA, step_val_of_B _ (step_in_B hpA l), step_val_of_A _ hpA]
  · rw [faceFourStep_B_coordinates hpB, step_val_of_A _ (step_in_A hpB l), step_val_of_B _ hpB]

theorem facePPPFold_first_seam (p : Site) (k i l : Fin 4) (hil : i ≠ l) :
    tetrahedralLattice.Adj p ((facePPPFold p k i l hil).pos 0) := step_adj _ _

theorem facePPPFold_last_seam (p : Site) (k i l : Fin 4) (hil : i ≠ l) :
    tetrahedralLattice.Adj ((facePPPFold p k i l hil).pos 2) (faceFourStep p k i l) := step_adj _ _

theorem facePPPFold_outside (m : ℕ) (p : Site) (k i l : Fin 4)
    (hil : i ≠ l) (hik : i ≠ k) (hlk : l ≠ k)
    (hface : OctBigFace m k p ∨ OctSmallFace m k p) (r : Fin 3) :
    (facePPPFold p k i l hil).pos r ∉ octahedron m := by
  have h := face_four_bond_internal_sites_outside m p k i l hik hlk hface
  fin_cases r
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem facePPPFold_mem_skin_one (m : ℕ) (p : Site) (k i l : Fin 4)
    (hil : i ≠ l) (hik : i ≠ k) (hlk : l ≠ k)
    (hface : OctBigFace m k p ∨ OctSmallFace m k p)
    (hq : faceFourStep p k i l ∈ octahedron m) (r : Fin 3) :
    (facePPPFold p k i l hil).pos r ∈ skin m 1 := by
  have hp := hface.elim (fun h => h.1) (fun h => h.1)
  have hout := facePPPFold_outside m p k i l hil hik hlk hface r
  fin_cases r
  · exact dangling_mem_skin_one m hp (step_adj _ _) hout
  · apply Finset.mem_sdiff.mpr
    refine ⟨?_, ?_⟩
    · rw [mem_skinSolid]
      intro a
      have hb := (mem_octahedron m p).mp hp a
      have hs := twoStep_tetraCoordinate_bounds m p k i a
      change -(2 * ((m + 2 * 1 : ℕ) : ℤ) - 1) ≤ tetraCoordinate m (step (step p k) i).val a ∧
        tetraCoordinate m (step (step p k) i).val a ≤ 2 * ((m + 2 * 1 : ℕ) : ℤ) - 2
      dsimp [octRadius] at hb
      push_cast
      constructor <;> omega
    · simpa only [Nat.sub_self, skinSolid_zero] using hout
  · exact dangling_mem_skin_one m hq (step_adj _ _).symm hout

def edgePPPNormal (F : OctEdgeFrame) (p : Site) : Fin 4 := if InASublattice p.val then F.k else F.j
def edgePPPBack (F : OctEdgeFrame) (p : Site) : Fin 4 := if InASublattice p.val then F.b else F.a
def edgePPPForward (F : OctEdgeFrame) (p : Site) : Fin 4 := if InASublattice p.val then F.a else F.b

theorem edgePPPLateral_ne (F : OctEdgeFrame) (p : Site) : edgePPPBack F p ≠ edgePPPForward F p := by
  unfold edgePPPBack edgePPPForward
  split_ifs
  · exact F.ab.symm
  · exact F.ab

def edgePPPFold (m : ℕ) (F : OctEdgeFrame) (r : ℕ) : Fold tetrahedralLattice 3 :=
  facePPPFold (octEdgeZigzag m F r) (edgePPPNormal F (octEdgeZigzag m F r))
    (edgePPPBack F (octEdgeZigzag m F r)) (edgePPPForward F (octEdgeZigzag m F r))
    (edgePPPLateral_ne F _)

theorem edgePPP_endpoint (m : ℕ) (F : OctEdgeFrame) (r : ℕ) :
    faceFourStep (octEdgeZigzag m F r) (edgePPPNormal F (octEdgeZigzag m F r))
      (edgePPPBack F (octEdgeZigzag m F r)) (edgePPPForward F (octEdgeZigzag m F r)) =
      octEdgeZigzag m F (r + 2) := by
  rw [faceFourStep_eq_twoStep]
  have hind : r + 2 = (r + 1) + 1 := by omega
  rw [hind, octEdgeZigzag_succ, octEdgeZigzag_succ]
  by_cases hpA : InASublattice (octEdgeZigzag m F r).val
  · have hB := (inB_iff_not_inA _).mp (step_in_B hpA F.a)
    simp only [edgePPPBack, edgePPPForward, edgeForwardStep, if_pos hpA, if_neg hB]
  · have hpB := (inB_iff_not_inA _).mpr hpA
    have hA := step_in_A hpB F.b
    simp only [edgePPPBack, edgePPPForward, edgeForwardStep, if_neg hpA, if_pos hA]

end ProteinFolding.Tetrahedral
