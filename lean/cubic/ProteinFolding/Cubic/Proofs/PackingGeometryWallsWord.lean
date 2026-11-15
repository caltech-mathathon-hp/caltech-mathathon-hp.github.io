import ProteinFolding.Cubic.Proofs.PackingGeometryWallsCrossing
import ProteinFolding.Cubic.Proofs.PackingGeometryPaths

/-! The straight-crossing theorem applied to an actual F_d subword. The two
anchor adjacencies are explicit interfaces for the adjoining E blocks. -/

namespace ProteinFolding.CubicPackingGeometry

def anchoredPath {m : ℕ} (u v : Site) (middle : Fin m → Site) (i : ℕ) : Site :=
  if hz : i = 0 then u else if h : i ≤ m then middle ⟨i - 1, by omega⟩ else v

theorem anchoredPath_start {m : ℕ} (u v : Site) (middle : Fin m → Site) :
    anchoredPath u v middle 0 = u := by simp [anchoredPath]

theorem anchoredPath_middle {m : ℕ} (u v : Site) (middle : Fin m → Site) (i : Fin m) :
    anchoredPath u v middle (i.val + 1) = middle i := by
  have hi : i.val + 1 ≤ m := by have := i.isLt; omega
  simp [anchoredPath, hi]

theorem anchoredPath_end {m : ℕ} (u v : Site) (middle : Fin m → Site) :
    anchoredPath u v middle (m + 1) = v := by simp [anchoredPath]

theorem anchoredPath_steps {m : ℕ} (hm : 0 < m) (u v : Site) (middle : Fin m → Site)
    (hfirst : cubicLattice.Adj u (middle ⟨0, hm⟩))
    (hlast : cubicLattice.Adj (middle ⟨m - 1, by omega⟩) v)
    (hstep : ∀ i j : Fin m, i.val + 1 = j.val → cubicLattice.Adj (middle i) (middle j)) :
    ∀ j, j < m + 1 → cubicLattice.Adj (anchoredPath u v middle j) (anchoredPath u v middle (j + 1)) := by
  intro j hj
  by_cases hzero : j = 0
  · subst j
    rw [anchoredPath_start, anchoredPath_middle u v middle ⟨0, hm⟩]
    exact hfirst
  · by_cases hend : j = m
    · subst j
      have he : anchoredPath u v middle m = middle ⟨m - 1, by omega⟩ := by
        have h := anchoredPath_middle u v middle ⟨m - 1, by omega⟩
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ m)] using h
      rw [he, anchoredPath_end]
      exact hlast
    · have hjm : j < m := by omega
      have he : anchoredPath u v middle j = middle ⟨j - 1, by omega⟩ := by
        have h := anchoredPath_middle u v middle ⟨j - 1, by omega⟩
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j)] using h
      rw [he, anchoredPath_middle u v middle ⟨j, hjm⟩]
      exact hstep _ _ (by dsimp; omega)

def faceWallPath (pre post : Sequence) (d : ℕ) (heven : 2 ∣ d)
    (f : Fold cubicLattice (pre ++ CubicPacking.faceWord d ++ post).length) : Fin d → Site :=
  fun i => faceHPath pre post d f ⟨i.val, by have h := Nat.mul_div_cancel' heven; omega⟩

theorem faceWallPath_adjacent (pre post : Sequence) (d : ℕ) (heven : 2 ∣ d)
    (f : Fold cubicLattice (pre ++ CubicPacking.faceWord d ++ post).length)
    (a : Site) (n : ℕ)
    (hpack : hydrophobicSites (pre ++ CubicPacking.faceWord d ++ post) f = cube a n) :
    ∀ i j : Fin d, i.val + 1 = j.val →
      cubicLattice.Adj (faceWallPath pre post d heven f i) (faceWallPath pre post d heven f j) := by
  intro i j hij
  exact faceHPath_adjacent pre post d f a n hpack _ _ hij

theorem faceWallPath_on_surface (pre post : Sequence) (d : ℕ) (heven : 2 ∣ d)
    (f : Fold cubicLattice (pre ++ CubicPacking.faceWord d ++ post).length)
    (a : Site) (n : ℕ)
    (hpack : hydrophobicSites (pre ++ CubicPacking.faceWord d ++ post) f = cube a n) :
    ∀ i : Fin d, Surface a n (faceWallPath pre post d heven f i) := by
  intro i
  exact faceHPath_on_surface pre post d f a n hpack _

/-- A literal wall whose H sites avoid the saturated skeleton connects two
opposite parallel edges of its single supporting face. -/
theorem faceWord_rails_parallel (pre post : Sequence) (d : ℕ) (hd : 0 < d) (heven : 2 ∣ d)
    (f : Fold cubicLattice (pre ++ CubicPacking.faceWord d ++ post).length)
    (a : Site) (hpack : hydrophobicSites (pre ++ CubicPacking.faceWord d ++ post) f = cube a (d + 2))
    (e g : CubeEdge) (r s : Fin d) (hnc : NoCommonCorner e g)
    (hnoedge : ∀ i, ¬ EdgeSkeleton a (d + 2) (faceWallPath pre post d heven f i))
    (hfirst : cubicLattice.Adj (openEdgePoint a d e r) (faceWallPath pre post d heven f ⟨0, hd⟩))
    (hlast : cubicLattice.Adj (faceWallPath pre post d heven f ⟨d - 1, by omega⟩) (openEdgePoint a d g s)) :
    e.axis = g.axis := by
  obtain ⟨normal, upper, hface⟩ := surface_path_in_one_face
    (faceWallPath pre post d heven f) hd
    (faceWallPath_on_surface pre post d heven f a (d + 2) hpack) hnoedge
    (faceWallPath_adjacent pre post d heven f a (d + 2) hpack)
  exact crossing_rails_parallel a d e g r s hnc normal upper
    (faceWallPath pre post d heven f ⟨0, hd⟩)
    (faceWallPath pre post d heven f ⟨d - 1, by omega⟩)
    (hface _) (hface _) hfirst.symm hlast

/-- The H sites of the literal F_d wall fill one complete straight row
between its two nonincident rail anchors, in either orientation. -/
theorem faceWord_wall_straight (pre post : Sequence) (d : ℕ) (hd : 0 < d) (heven : 2 ∣ d)
    (f : Fold cubicLattice (pre ++ CubicPacking.faceWord d ++ post).length)
    (a : Site) (hpack : hydrophobicSites (pre ++ CubicPacking.faceWord d ++ post) f = cube a (d + 2))
    (e g : CubeEdge) (r s : Fin d) (hnc : NoCommonCorner e g)
    (hfirst : cubicLattice.Adj (openEdgePoint a d e r) (faceWallPath pre post d heven f ⟨0, hd⟩))
    (hlast : cubicLattice.Adj (faceWallPath pre post d heven f ⟨d - 1, by omega⟩) (openEdgePoint a d g s)) :
    ∃ axis : Fin 3, axis ≠ e.axis ∧ axis ≠ g.axis ∧
      ((∀ i : Fin d, faceWallPath pre post d heven f i =
        Function.update (openEdgePoint a d e r) axis
          (openEdgePoint a d e r axis + ((i.val + 1 : ℕ) : ℤ))) ∨
       (∀ i : Fin d, faceWallPath pre post d heven f i =
        Function.update (openEdgePoint a d e r) axis
          (openEdgePoint a d e r axis - ((i.val + 1 : ℕ) : ℤ)))) := by
  let middle := faceWallPath pre post d heven f
  let p := anchoredPath (openEdgePoint a d e r) (openEdgePoint a d g s) middle
  have hsteps := anchoredPath_steps hd (openEdgePoint a d e r) (openEdgePoint a d g s) middle
    hfirst hlast (faceWallPath_adjacent pre post d heven f a (d + 2) hpack)
  obtain ⟨axis, hae, hag, hstraight⟩ := nonincident_crossing_straight a d e g r s hnc p
    (anchoredPath_start _ _ middle) (anchoredPath_end _ _ middle) hsteps
  refine ⟨axis, hae, hag, ?_⟩
  rcases hstraight with hstraight | hstraight
  · left
    intro i
    have h := hstraight (i.val + 1) (by have := i.isLt; omega)
    simpa only [p, anchoredPath_middle, anchoredPath_start] using h
  · right
    intro i
    have h := hstraight (i.val + 1) (by have := i.isLt; omega)
    simpa only [p, anchoredPath_middle, anchoredPath_start] using h

end ProteinFolding.CubicPackingGeometry
