import ProteinFolding.Tetrahedral.FrameForcingTrackHeights
import ProteinFolding.Tetrahedral.FrameForcingPairMatching

/-! The complete soundness track: entry a1, its small-face corner, then the
third edge up to the final corner. Its ordinary-edge graph is a finite path. -/

namespace ProteinFolding.Tetrahedral

def frameTrackPoint (m : ℕ) (F : OctEdgeFrame) (r : ℕ) : Site :=
  if r = 0 then octEdgeZigzag m F 2 else octEdgeZigzag m F.smallOtherSide r

def frameTrackSites (m : ℕ) (F : OctEdgeFrame) : Finset Site :=
  (Finset.range (2 * m - 2)).image (frameTrackPoint m F)

theorem entry_a1_H2 (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) :
    frameH2 m F (octEdgeZigzag m F 2) = 0 := by
  have h := octEdgeZigzag_even hm F 1
  simp only [frameH2, h.2.2.2.1, h.2.2.2.2]
  omega

theorem frameTrackPoint_H2 (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ) :
    frameH2 m F (frameTrackPoint m F r) = 2 * (r : ℤ) := by
  by_cases hr : r = 0
  · subst r
    simpa only [frameTrackPoint, if_pos rfl, Nat.cast_zero, mul_zero] using entry_a1_H2 m hm F
  · rw [frameTrackPoint, if_neg hr]
    exact (track_edge_height_data m hm F r).1

theorem frameTrackPoint_injective (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) :
    Function.Injective (frameTrackPoint m F) := by
  intro r s heq
  have h := congrArg (frameH2 m F) heq
  rw [frameTrackPoint_H2 m hm F r, frameTrackPoint_H2 m hm F s] at h
  omega

theorem frameTrackPoint_adj_indices (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (r s : ℕ)
    (hadj : tetrahedralLattice.Adj (frameTrackPoint m F r) (frameTrackPoint m F s)) :
    r + 1 = s ∨ s + 1 = r := by
  have hbound := two_face_height_adj_bounds m F.ab hadj
  change -2 ≤ frameH2 m F (frameTrackPoint m F s) - frameH2 m F (frameTrackPoint m F r) ∧
    frameH2 m F (frameTrackPoint m F s) - frameH2 m F (frameTrackPoint m F r) ≤ 2 at hbound
  rw [frameTrackPoint_H2 m hm F r, frameTrackPoint_H2 m hm F s] at hbound
  have hne : r ≠ s := by intro he; subst s; exact tetrahedralLattice.loopless _ hadj
  omega

theorem start_corner_shared (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) :
    octEdgeZigzag m F 1 = octEdgeZigzag m F.smallOtherSide 1 := by
  have hF := octEdgeZigzag_odd hm F 0
  have hG := octEdgeZigzag_odd hm F.smallOtherSide 0
  have hFk : tetraCoordinate m (octEdgeZigzag m F 1).val F.k = octRadius m - 1 := hF.2.1
  have hFj : tetraCoordinate m (octEdgeZigzag m F 1).val F.j = -octRadius m - 1 := hF.2.2.1
  have hFa : tetraCoordinate m (octEdgeZigzag m F 1).val F.a = -octRadius m + 3 := by simpa using hF.2.2.2.1
  have hFb : tetraCoordinate m (octEdgeZigzag m F 1).val F.b = octRadius m - 1 := by simpa using hF.2.2.2.2
  have hGk : tetraCoordinate m (octEdgeZigzag m F.smallOtherSide 1).val F.k = octRadius m - 1 := by
    change tetraCoordinate m (octEdgeZigzag m F.smallOtherSide 1).val F.smallOtherSide.b = _
    simpa using hG.2.2.2.2
  have hGj : tetraCoordinate m (octEdgeZigzag m F.smallOtherSide 1).val F.j = -octRadius m - 1 := hG.2.2.1
  have hGa : tetraCoordinate m (octEdgeZigzag m F.smallOtherSide 1).val F.a = -octRadius m + 3 := by simpa using hG.2.2.2.1
  have hGb : tetraCoordinate m (octEdgeZigzag m F.smallOtherSide 1).val F.b = octRadius m - 1 := hG.2.1
  apply Subtype.ext
  apply tetraCoordinate_injective m
  funext d
  rcases F.index_cases d with rfl | rfl | rfl | rfl
  · exact hFk.trans hGk.symm
  · exact hFj.trans hGj.symm
  · exact hFa.trans hGa.symm
  · exact hFb.trans hGb.symm

theorem frameTrackPoint_consecutive (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ) :
    tetrahedralLattice.Adj (frameTrackPoint m F r) (frameTrackPoint m F (r + 1)) := by
  by_cases hr : r = 0
  · subst r
    simp only [frameTrackPoint, Nat.zero_add, if_neg (by decide : ¬ (1 : ℕ) = 0)]
    rw [← start_corner_shared m hm F]
    exact (octEdgeZigzag_adj m F 1).symm
  · rw [frameTrackPoint, if_neg hr, frameTrackPoint, if_neg (by omega : ¬ r + 1 = 0)]
    exact octEdgeZigzag_adj m F.smallOtherSide r

noncomputable def frameTrackEquiv (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) :
    Fin (2 * m - 2) ≃ {x : Site // x ∈ frameTrackSites m F} :=
  Equiv.ofBijective (fun r => ⟨frameTrackPoint m F r.val,
    Finset.mem_image.mpr ⟨r.val, Finset.mem_range.mpr r.isLt, rfl⟩⟩) (by
    constructor
    · intro r s heq
      exact Fin.ext (frameTrackPoint_injective m hm F (congrArg Subtype.val heq))
    · intro x
      obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp x.property
      exact ⟨⟨r, Finset.mem_range.mp hr⟩, Subtype.ext heq⟩)

end ProteinFolding.Tetrahedral
