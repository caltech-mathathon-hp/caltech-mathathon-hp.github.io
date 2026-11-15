import ProteinFolding.Tetrahedral.NearFieldFrameHRunData

/-! Distinct retained frame H-runs occupy disjoint edge intervals. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

def frameHRunOnExit {p : ConstructionParameters} : FrameHRunIndex p → Bool
  | .inl c => if c = 3 ∨ c = 4 then true else false
  | .inr (b, _) => b

theorem frameHRun_frame (p : ConstructionParameters) (i : FrameHRunIndex p) :
    (frameHRunData p i).frame = if frameHRunOnExit i then exitEdgeFrame else entryEdgeFrame := by
  rcases i with c | ⟨b, t⟩
  · fin_cases c <;> rfl
  · cases b <;> rfl

theorem frameHRun_exit_room (p : ConstructionParameters) (i : FrameHRunIndex p)
    (hi : frameHRunOnExit i = true) :
    (frameHRunData p i).base + (frameHRunData p i).count ≤ 2 * p.side - 3 := by
  have hm := p.side_ge
  have h2 := p.frameTail2_add
  have hf := p.family_side_bound
  rcases i with c | ⟨b, t⟩
  · fin_cases c <;> dsimp [frameHRunData] <;>
      dsimp [frameHRunOnExit] at hi <;>
      simp only [Bool.false_eq_true, Bool.true_eq_false] at hi <;> omega
  · have ht := t.isLt
    cases b <;> dsimp [frameHRunData] <;>
      dsimp [frameHRunOnExit] at hi <;>
      simp only [Bool.false_eq_true, Bool.true_eq_false] at hi <;> omega

theorem frameHRun_index_unique (p : ConstructionParameters) (i j : FrameHRunIndex p)
    (r s : ℕ) (hr : r < (frameHRunData p i).count) (hs : s < (frameHRunData p j).count)
    (hedge : frameHRunOnExit i = frameHRunOnExit j)
    (heq : (frameHRunData p i).base + r = (frameHRunData p j).base + s) : i = j := by
  have hm := p.side_ge
  have hf := p.family_side_bound
  have h1 := p.frameTail1_add
  have h2 := p.frameTail2_add
  rcases i with c | ⟨b, t⟩ <;> rcases j with d | ⟨e, u⟩
  · fin_cases c <;> fin_cases d <;>
      dsimp [frameHRunData] at hr hs heq <;>
      dsimp [frameHRunOnExit] at hedge <;>
      simp only [Bool.false_eq_true, Bool.true_eq_false] at hedge <;> first | rfl | omega
  · have hu := u.isLt
    fin_cases c <;> cases e <;>
      dsimp [frameHRunData] at hr hs heq <;>
      dsimp [frameHRunOnExit] at hedge <;>
      simp only [Bool.false_eq_true, Bool.true_eq_false] at hedge
    all_goals first | omega | (split_ifs at hs <;> omega)
  · have ht := t.isLt
    fin_cases d <;> cases b <;>
      dsimp [frameHRunData] at hr hs heq <;>
      dsimp [frameHRunOnExit] at hedge <;>
      simp only [Bool.false_eq_true, Bool.true_eq_false] at hedge
    all_goals first | omega | (split_ifs at hr <;> omega)
  · have ht := t.isLt
    have hu := u.isLt
    cases b <;> cases e <;> dsimp [frameHRunData] at hr hs heq <;>
      dsimp [frameHRunOnExit] at hedge <;>
      simp only [Bool.false_eq_true, Bool.true_eq_false] at hedge
    · have htu : t.val = u.val := by
        split_ifs at hr hs <;> omega
      exact congrArg Sum.inr (Prod.ext rfl (Fin.ext htu))
    · have htu : t.val = u.val := by omega
      exact congrArg Sum.inr (Prod.ext rfl (Fin.ext htu))

theorem entryEdge_ne_exitEdge_before_corner {m : ℕ} (hm : 2 ≤ m) (r s : ℕ)
    (hs : s + 2 ≤ 2 * m - 2) :
    octEdgeZigzag m entryEdgeFrame r ≠ octEdgeZigzag m exitEdgeFrame s := by
  intro heq
  have hx := congrArg (fun x : Site => x.val 0) heq
  change (octEdgeZigzag m entryEdgeFrame r).val 0 =
    (octEdgeZigzag m exitEdgeFrame s).val 0 at hx
  rw [entryEdgeZigzag_coordinates (by omega : 1 ≤ m),
    exitEdgeZigzag_coordinates (by omega : 1 ≤ m)] at hx
  change (r % 2 : ℕ) = octRadius m - (s : ℤ) at hx
  dsimp [octRadius] at hx
  omega

theorem frameHRun_blocks_disjoint (p : ConstructionParameters) (i j : FrameHRunIndex p)
    (hne : i ≠ j) :
    Disjoint (edgeBlock p.side (frameHRunData p i).frame (frameHRunData p i).base (frameHRunData p i).count)
      (edgeBlock p.side (frameHRunData p j).frame (frameHRunData p j).base (frameHRunData p j).count) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp hy
  have hrr := Finset.mem_range.mp hr
  have hss := Finset.mem_range.mp hs
  have hm : 2 ≤ p.side := by have h := p.side_ge; omega
  rw [frameHRun_frame p i, frameHRun_frame p j] at heq
  cases hi : frameHRunOnExit i <;> cases hj : frameHRunOnExit j <;>
      simp only [hi, hj, Bool.false_eq_true, if_false, ite_true] at heq
  · have hidx := octEdgeZigzag_injective (by omega : 1 ≤ p.side) entryEdgeFrame heq
    exact hne (frameHRun_index_unique p i j r s hrr hss (by rw [hi, hj]) hidx.symm)
  · have hroom := frameHRun_exit_room p j hj
    exact entryEdge_ne_exitEdge_before_corner hm _ _ (by omega) heq.symm
  · have hroom := frameHRun_exit_room p i hi
    exact entryEdge_ne_exitEdge_before_corner hm _ _ (by omega) heq
  · have hidx := octEdgeZigzag_injective (by omega : 1 ≤ p.side) exitEdgeFrame heq
    exact hne (frameHRun_index_unique p i j r s hrr hss (by rw [hi, hj]) hidx.symm)

theorem frameHRunFolds_disjoint (p : ConstructionParameters) (i j : FrameHRunIndex p) (hne : i ≠ j) :
    Disjoint (foldSites (frameHRunFold p i)) (foldSites (frameHRunFold p j)) := by
  rw [frameHRunFold_sites, frameHRunFold_sites]
  exact frameHRun_blocks_disjoint p i j hne

theorem frameHRunFold_mem_oct (p : ConstructionParameters) (i : FrameHRunIndex p)
    (r : Fin (frameHRunWord p i).length) : (frameHRunFold p i).pos r ∈ octahedron p.side := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  cases hb : (frameHRunData p i).reversed
  · simpa only [frameHRunFold, hb, Bool.false_eq_true, if_false] using
      edgeHRunFold_mem_oct hm _ _ _ (frameHRun_room p i) r
  · simpa only [frameHRunFold, hb, ite_true] using
      edgeHRunFold_mem_oct hm _ _ _ (frameHRun_room p i) r.rev

end ProteinFolding.Tetrahedral.NearField
