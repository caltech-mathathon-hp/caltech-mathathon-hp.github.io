import ProteinFolding.Cubic.Proofs.PackingGeometrySkeleton
import ProteinFolding.Cubic.Proofs.PackingGeometryStraight

/-! The eight corners and twelve open edge interiors of a cubic skeleton.
All coordinates refer to the existing integer-lattice cube. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicCertificates

structure CubeEdge where
  axis : Fin 3
  first : Fin 2
  second : Fin 2
  deriving DecidableEq, Fintype

theorem cubeEdge_card : Fintype.card CubeEdge = 12 := by decide

def endValue (base : ℤ) (d : ℕ) (side : Fin 2) : ℤ :=
  base + (side.val : ℤ) * ((d : ℤ) + 1)

theorem endValue_injective (base : ℤ) (d : ℕ) : Function.Injective (endValue base d) := by
  intro b c h
  have he : (b.val : ℤ) * ((d : ℤ) + 1) = (c.val : ℤ) * ((d : ℤ) + 1) := by
    dsimp only [endValue] at h
    omega
  have he' := mul_right_cancel₀ (by omega : (d : ℤ) + 1 ≠ 0) he
  apply Fin.ext
  omega

theorem endValue_bounds (base : ℤ) (d : ℕ) (side : Fin 2) :
    base ≤ endValue base d side ∧ endValue base d side < base + ((d + 2 : ℕ) : ℤ) := by
  fin_cases side <;> simp only [endValue, Nat.cast_zero, Nat.cast_one,
    zero_mul, one_mul] <;> omega

theorem endValue_boundary (base : ℤ) (d : ℕ) (side : Fin 2) :
    endValue base d side = base ∨ endValue base d side + 1 = base + ((d + 2 : ℕ) : ℤ) := by
  fin_cases side <;> simp only [endValue, Nat.cast_zero, Nat.cast_one,
    zero_mul, one_mul] <;> omega

def cornerPoint (a : Site) (d : ℕ) (bits : Fin 3 → Fin 2) : Site :=
  fun k => endValue (a k) d (bits k)

def Corner (a : Site) (n : ℕ) (p : Site) : Prop :=
  p ∈ cube a n ∧ ∀ k, BoundaryCoordinate a p n k

theorem cornerPoint_corner (a : Site) (d : ℕ) (bits : Fin 3 → Fin 2) :
    Corner a (d + 2) (cornerPoint a d bits) := by
  constructor
  · intro k; exact endValue_bounds (a k) d (bits k)
  · intro k; exact endValue_boundary (a k) d (bits k)

theorem cornerPoint_injective (a : Site) (d : ℕ) :
    Function.Injective (cornerPoint a d) := by
  intro b c h
  funext k
  exact endValue_injective (a k) d (congrFun h k)

def cornerFinset (a : Site) (d : ℕ) : Finset Site :=
  Finset.univ.image (cornerPoint a d)

theorem cornerFinset_card (a : Site) (d : ℕ) : (cornerFinset a d).card = 8 := by
  rw [cornerFinset, Finset.card_image_of_injective _ (cornerPoint_injective a d)]
  simp

def openEdgePoint (a : Site) (d : ℕ) (e : CubeEdge) (r : Fin d) : Site
  | 0 => if e.axis = 0 then a 0 + 1 + r.val else endValue (a 0) d e.first
  | 1 => if e.axis = 1 then a 1 + 1 + r.val else
      if e.axis = 0 then endValue (a 1) d e.first else endValue (a 1) d e.second
  | 2 => if e.axis = 2 then a 2 + 1 + r.val else endValue (a 2) d e.second

theorem openEdgePoint_axis (a : Site) (d : ℕ) (e : CubeEdge) (r : Fin d) :
    openEdgePoint a d e r e.axis = a e.axis + 1 + r.val := by
  obtain ⟨axis, b, c⟩ := e
  fin_cases axis <;> simp [openEdgePoint]

theorem openEdgePoint_axis_strict (a : Site) (d : ℕ) (e : CubeEdge) (r : Fin d) :
    a e.axis < openEdgePoint a d e r e.axis ∧
      openEdgePoint a d e r e.axis + 1 < a e.axis + ((d + 2 : ℕ) : ℤ) := by
  rw [openEdgePoint_axis]
  have hr := r.isLt
  omega

theorem openEdgePoint_other_boundary (a : Site) (d : ℕ) (e : CubeEdge) (r : Fin d)
    (k : Fin 3) (hk : k ≠ e.axis) : BoundaryCoordinate a (openEdgePoint a d e r) (d + 2) k := by
  obtain ⟨axis, b, c⟩ := e
  fin_cases axis <;> fin_cases k
  all_goals simp only [Fin.reduceFinMk] at hk ⊢
  all_goals first
    | exact False.elim (hk rfl)
    | simpa only [BoundaryCoordinate, openEdgePoint, ↓reduceIte] using endValue_boundary (a 0) d b
    | simpa only [BoundaryCoordinate, openEdgePoint, ↓reduceIte] using endValue_boundary (a 1) d b
    | simpa only [BoundaryCoordinate, openEdgePoint, ↓reduceIte] using endValue_boundary (a 1) d c
    | simpa only [BoundaryCoordinate, openEdgePoint, ↓reduceIte] using endValue_boundary (a 2) d c

theorem openEdgePoint_skeleton (a : Site) (d : ℕ) (e : CubeEdge) (r : Fin d) :
    EdgeSkeleton a (d + 2) (openEdgePoint a d e r) := by
  have hc : openEdgePoint a d e r ∈ cube a (d + 2) := by
    intro k
    by_cases hk : k = e.axis
    · subst k
      have h := openEdgePoint_axis_strict a d e r
      omega
    · have hb := openEdgePoint_other_boundary a d e r k hk
      rcases hb with hb | hb <;> omega
  refine ⟨hc, ?_⟩
  obtain ⟨axis, b, c⟩ := e
  fin_cases axis
  · exact ⟨1, 2, by decide, openEdgePoint_other_boundary a d _ r 1 (by simp),
      openEdgePoint_other_boundary a d _ r 2 (by simp)⟩
  · exact ⟨0, 2, by decide, openEdgePoint_other_boundary a d _ r 0 (by simp),
      openEdgePoint_other_boundary a d _ r 2 (by simp)⟩
  · exact ⟨0, 1, by decide, openEdgePoint_other_boundary a d _ r 0 (by simp),
      openEdgePoint_other_boundary a d _ r 1 (by simp)⟩

theorem openEdgePoint_not_corner (a : Site) (d : ℕ) (e : CubeEdge) (r : Fin d) :
    ¬ Corner a (d + 2) (openEdgePoint a d e r) := by
  intro hc
  exact boundary_not_strict (hc.2 e.axis) (openEdgePoint_axis_strict a d e r)

theorem openEdgePoint_equal_axis {a : Site} {d : ℕ} {e f : CubeEdge} {r s : Fin d}
    (h : openEdgePoint a d e r = openEdgePoint a d f s) : e.axis = f.axis := by
  by_contra he
  have hb := openEdgePoint_other_boundary a d f s e.axis he
  rw [← h] at hb
  exact boundary_not_strict hb (openEdgePoint_axis_strict a d e r)

theorem openEdgePoint_injective (a : Site) (d : ℕ) :
    Function.Injective (fun q : CubeEdge × Fin d => openEdgePoint a d q.1 q.2) := by
  rintro ⟨⟨axis, b, c⟩, r⟩ ⟨⟨axis', b', c'⟩, s⟩ h
  have haxis := openEdgePoint_equal_axis h
  change axis = axis' at haxis
  subst axis'
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have hr : r = s := by
    have he := congrFun h axis
    dsimp only at he
    rw [openEdgePoint_axis, openEdgePoint_axis] at he
    change a axis + 1 + (r.val : ℤ) = a axis + 1 + (s.val : ℤ) at he
    apply Fin.ext
    omega
  have hbits : b = b' ∧ c = c' := by
    fin_cases axis
    · exact ⟨endValue_injective (a 1) d (by simpa [openEdgePoint] using h1),
        endValue_injective (a 2) d (by simpa [openEdgePoint] using h2)⟩
    · exact ⟨endValue_injective (a 0) d (by simpa [openEdgePoint] using h0),
        endValue_injective (a 2) d (by simpa [openEdgePoint] using h2)⟩
    · exact ⟨endValue_injective (a 0) d (by simpa [openEdgePoint] using h0),
        endValue_injective (a 1) d (by simpa [openEdgePoint] using h1)⟩
  rcases hbits with ⟨rfl, rfl⟩
  subst s
  rfl

def allOpenEdges (a : Site) (d : ℕ) : Finset Site :=
  Finset.univ.image (fun q : CubeEdge × Fin d => openEdgePoint a d q.1 q.2)

theorem allOpenEdges_card (a : Site) (d : ℕ) : (allOpenEdges a d).card = 12 * d := by
  rw [allOpenEdges, Finset.card_image_of_injective _ (openEdgePoint_injective a d)]
  simp [cubeEdge_card]

theorem cornerFinset_disjoint_open (a : Site) (d : ℕ) :
    Disjoint (cornerFinset a d) (allOpenEdges a d) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨⟨e, r⟩, _, he⟩ := Finset.mem_image.mp hq
  have hc := cornerPoint_corner a d b
  rw [← he] at hc
  exact openEdgePoint_not_corner a d e r hc

theorem skeleton_decomposition (a : Site) (d : ℕ) :
    cornerFinset a d ∪ allOpenEdges a d = skeletonFinset a (d + 2) := by
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    apply (mem_skeletonFinset a (d + 2) p).mpr
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨bits, _, rfl⟩ := Finset.mem_image.mp hp
      have hc := cornerPoint_corner a d bits
      exact ⟨hc.1, 0, 1, by decide, hc.2 0, hc.2 1⟩
    · obtain ⟨⟨e, r⟩, _, rfl⟩ := Finset.mem_image.mp hp
      exact openEdgePoint_skeleton a d e r
  · rw [Finset.card_union_of_disjoint (cornerFinset_disjoint_open a d), cornerFinset_card,
      allOpenEdges_card, skeletonFinset_card a (d + 2) (by omega)]
    omega

theorem corner_iff_mem (a : Site) (d : ℕ) (p : Site) :
    Corner a (d + 2) p ↔ p ∈ cornerFinset a d := by
  constructor
  · intro hc
    have he : p ∈ skeletonFinset a (d + 2) :=
      (mem_skeletonFinset a (d + 2) p).mpr ⟨hc.1, 0, 1, by decide, hc.2 0, hc.2 1⟩
    rw [← skeleton_decomposition] at he
    rcases Finset.mem_union.mp he with h | h
    · exact h
    · obtain ⟨⟨e, r⟩, _, rfl⟩ := Finset.mem_image.mp h
      exact False.elim (openEdgePoint_not_corner a d e r hc)
  · intro hp
    obtain ⟨bits, _, rfl⟩ := Finset.mem_image.mp hp
    exact cornerPoint_corner a d bits

def openEdgeFinset (a : Site) (d : ℕ) (e : CubeEdge) : Finset Site :=
  Finset.univ.image (openEdgePoint a d e)

theorem openEdgeFinset_card (a : Site) (d : ℕ) (e : CubeEdge) :
    (openEdgeFinset a d e).card = d := by
  have hi : Function.Injective (openEdgePoint a d e) := by
    intro r s hrs
    have he : (e, r) = (e, s) := openEdgePoint_injective a d hrs
    exact congrArg Prod.snd he
  rw [openEdgeFinset, Finset.card_image_of_injective _ hi]
  simp

theorem openEdgePoint_adjacent_axis {a : Site} {d : ℕ} {e f : CubeEdge} {r s : Fin d}
    (h : cubicLattice.Adj (openEdgePoint a d e r) (openEdgePoint a d f s)) : e.axis = f.axis := by
  obtain ⟨dir, hdir⟩ := adj_step h
  by_contra he
  by_cases hd : e.axis = directionAxis dir
  · have hf : f.axis ≠ directionAxis dir := by intro hf; exact he (hd.trans hf.symm)
    have hc := congrFun hdir f.axis
    rw [step_unchanged_off_axis _ _ _ hf] at hc
    have hb := openEdgePoint_other_boundary a d e r f.axis (Ne.symm he)
    unfold BoundaryCoordinate at hb
    rw [hc] at hb
    exact boundary_not_strict hb (openEdgePoint_axis_strict a d f s)
  · have hc := congrFun hdir e.axis
    rw [step_unchanged_off_axis _ _ _ hd] at hc
    have hb := openEdgePoint_other_boundary a d f s e.axis he
    unfold BoundaryCoordinate at hb
    rw [← hc] at hb
    exact boundary_not_strict hb (openEdgePoint_axis_strict a d e r)

theorem endValue_close_injective (base : ℤ) (d : ℕ) (b c : Fin 2) (hd : 0 < d)
    (h : endValue base d b - 1 ≤ endValue base d c ∧
      endValue base d c ≤ endValue base d b + 1) : b = c := by
  fin_cases b <;> fin_cases c <;> simp only [endValue, Nat.cast_zero, Nat.cast_one,
    zero_mul, one_mul] at h ⊢ <;> first | rfl | omega

theorem openEdgePoint_adjacent_key {a : Site} {d : ℕ} {e f : CubeEdge} {r s : Fin d}
    (h : cubicLattice.Adj (openEdgePoint a d e r) (openEdgePoint a d f s)) : e = f := by
  have haxis := openEdgePoint_adjacent_axis h
  obtain ⟨axis, b, c⟩ := e
  obtain ⟨axis', b', c'⟩ := f
  change axis = axis' at haxis
  subst axis'
  have h0 := adjacent_coordinate_bounds h 0
  have h1 := adjacent_coordinate_bounds h 1
  have h2 := adjacent_coordinate_bounds h 2
  have hd : 0 < d := by have := r.isLt; omega
  have hbits : b = b' ∧ c = c' := by
    fin_cases axis
    · exact ⟨endValue_close_injective (a 1) d b b' hd (by simpa [openEdgePoint] using h1),
        endValue_close_injective (a 2) d c c' hd (by simpa [openEdgePoint] using h2)⟩
    · exact ⟨endValue_close_injective (a 0) d b b' hd (by simpa [openEdgePoint] using h0),
        endValue_close_injective (a 2) d c c' hd (by simpa [openEdgePoint] using h2)⟩
    · exact ⟨endValue_close_injective (a 0) d b b' hd (by simpa [openEdgePoint] using h0),
        endValue_close_injective (a 1) d c c' hd (by simpa [openEdgePoint] using h1)⟩
  rcases hbits with ⟨rfl, rfl⟩
  rfl

end ProteinFolding.CubicPackingGeometry
