import ProteinFolding.Cubic.Proofs.PackingSnakeRectangle

/-! Stacking a planar Hamiltonian path in alternating directions. Reversing
every other layer makes successive layers meet by a single vertical edge.
For an even number of layers, both endpoints project to the first base vertex.
This supplies the elementary layered interior snake in the packing frame. -/

namespace ProteinFolding.CubicPackingSnake

open CubicCertificates

def atHeight (p : Site) (z : ℤ) : Site
  | 0 => p 0
  | 1 => p 1
  | 2 => z

theorem atHeight_horizontal (p q : Site) (z : ℤ) (hp : p 2 = 0) (hq : q 2 = 0)
    (ha : cubicLattice.Adj p q) : cubicLattice.Adj (atHeight p z) (atHeight q z) := by
  change latticeDistance _ _ = 1 at ha ⊢
  rw [distance_eq] at ha ⊢
  simpa [atHeight, hp, hq] using ha

theorem atHeight_vertical (p : Site) (z : ℤ) :
    cubicLattice.Adj (atHeight p z) (atHeight p (z + 1)) := by
  change latticeDistance _ _ = 1
  rw [distance_eq]
  simp [atHeight]

def layerIndex (layers N : ℕ) (i : Fin (layers * N)) : Fin N := (rectangleCells layers N i).2
def layerHeight (layers N : ℕ) (i : Fin (layers * N)) : ℤ := (rectangleCells layers N i).1.val

theorem layerIndex_val (layers N : ℕ) (i : Fin (layers * N)) :
    (layerIndex layers N i).val =
      if (i.val / N) % 2 = 0 then i.val % N else N - (i.val % N + 1) := by
  unfold layerIndex rectangleCells rowFlip
  dsimp
  split_ifs <;> rfl

theorem layerHeight_eq (layers N : ℕ) (i : Fin (layers * N)) :
    layerHeight layers N i = ((i.val / N : ℕ) : ℤ) := rfl

def layeredPos {N : ℕ} (layers : ℕ) (base : Fold cubicLattice N) (i : Fin (layers * N)) : Site :=
  atHeight (base.pos (layerIndex layers N i)) (layerHeight layers N i)

theorem layeredPos_injective {N : ℕ} (layers : ℕ) (base : Fold cubicLattice N)
    (hplane : ∀ i, base.pos i 2 = 0) : Function.Injective (layeredPos layers base) := by
  intro i j he
  have hx := congrFun he 0
  have hy := congrFun he 1
  have hz := congrFun he 2
  have hrow : (rectangleCells layers N i).1 = (rectangleCells layers N j).1 := by
    apply Fin.ext
    change ((rectangleCells layers N i).1.val : ℤ) = ((rectangleCells layers N j).1.val : ℤ) at hz
    omega
  have hbase : base.pos (layerIndex layers N i) = base.pos (layerIndex layers N j) := by
    apply site_ext
    · exact hx
    · exact hy
    · rw [hplane, hplane]
  apply (rectangleCells layers N).injective
  exact Prod.ext hrow (base.injective_pos hbase)

theorem layeredPos_image {N : ℕ} (layers : ℕ) (base : Fold cubicLattice N) :
    Finset.univ.image (layeredPos layers base) =
      (Finset.univ : Finset (Fin layers × Fin N)).image (fun p => atHeight (base.pos p.2) p.1.val) := by
  ext p
  constructor
  · rintro hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨rectangleCells layers N i, Finset.mem_univ _, rfl⟩
  · rintro hp
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨(rectangleCells layers N).symm c, Finset.mem_univ _, ?_⟩
    simp [layeredPos, layerIndex, layerHeight]

theorem layeredPos_adjacent {N : ℕ} (layers : ℕ) (base : Fold cubicLattice N)
    (hN : 0 < N) (hplane : ∀ i, base.pos i 2 = 0) (i j : Fin (layers * N))
    (hij : i.val + 1 = j.val) : cubicLattice.Adj (layeredPos layers base i) (layeredPos layers base j) := by
  have hr := Nat.mod_lt i.val hN
  obtain ⟨hrow, hcol⟩ | ⟨hrow, hcol, hend⟩ := successor_divmod N i.val hN
  · rw [hij] at hrow hcol
    have hz : layerHeight layers N j = layerHeight layers N i := by
      rw [layerHeight_eq, layerHeight_eq, hrow]
    change cubicLattice.Adj (atHeight _ _) (atHeight _ _)
    rw [hz]
    apply atHeight_horizontal _ _ _ (hplane _) (hplane _)
    by_cases hp : (i.val / N) % 2 = 0
    · apply base.consecutive
      rw [layerIndex_val, layerIndex_val, hrow, hcol, if_pos hp, if_pos hp]
    · have hnext : i.val % N + 1 < N := by
        have hjr := Nat.mod_lt j.val hN
        rw [hcol] at hjr
        exact hjr
      apply (base.consecutive (layerIndex layers N j) (layerIndex layers N i) ?_).symm
      rw [layerIndex_val, layerIndex_val, hrow, hcol, if_neg hp, if_neg hp]
      omega
  · rw [hij] at hrow hcol
    have hidx : layerIndex layers N j = layerIndex layers N i := by
      apply Fin.ext
      rw [layerIndex_val, layerIndex_val, hrow, hcol]
      split_ifs <;> omega
    have hz : layerHeight layers N j = layerHeight layers N i + 1 := by
      rw [layerHeight_eq, layerHeight_eq, hrow]
      omega
    change cubicLattice.Adj (atHeight _ _) (atHeight _ _)
    rw [hidx, hz]
    exact atHeight_vertical _ _

def layeredFold {N : ℕ} (layers : ℕ) (base : Fold cubicLattice N)
    (hN : 0 < N) (hplane : ∀ i, base.pos i 2 = 0) : Fold cubicLattice (layers * N) where
  pos := layeredPos layers base
  injective_pos := layeredPos_injective layers base hplane
  consecutive := fun i j hij => layeredPos_adjacent layers base hN hplane i j hij

theorem layeredPos_first {N : ℕ} (layers : ℕ) (base : Fold cubicLattice N)
    (hl : 0 < layers) (hN : 0 < N) :
    layeredPos layers base (firstIndex layers N hl hN) = atHeight (base.pos ⟨0, hN⟩) 0 := by
  have hcell := rectanglePos_first layers N hl hN
  have hx := congrFun hcell 0
  have hy := congrFun hcell 1
  have hi : layerIndex layers N (firstIndex layers N hl hN) = ⟨0, hN⟩ := by
    apply Fin.ext
    change (layerIndex layers N (firstIndex layers N hl hN)).val = 0
    change ((layerIndex layers N (firstIndex layers N hl hN)).val : ℤ) = 0 at hx
    omega
  have hz : layerHeight layers N (firstIndex layers N hl hN) = 0 := hy
  simp only [layeredPos, hi, hz]

/-- The layered path ends directly above its first base vertex when the
number of layers is even. This is the required bulk-snake endpoint relation. -/
theorem layeredPos_last_even {N : ℕ} (layers : ℕ) (base : Fold cubicLattice N)
    (hl : 0 < layers) (hN : 0 < N) (heven : layers % 2 = 0) :
    layeredPos layers base (lastIndex layers N hl hN) =
      atHeight (base.pos ⟨0, hN⟩) ((layers - 1 : ℕ) : ℤ) := by
  have hcell := rectanglePos_last_even layers N hl hN heven
  have hx := congrFun hcell 0
  have hy := congrFun hcell 1
  have hi : layerIndex layers N (lastIndex layers N hl hN) = ⟨0, hN⟩ := by
    apply Fin.ext
    change (layerIndex layers N (lastIndex layers N hl hN)).val = 0
    change ((layerIndex layers N (lastIndex layers N hl hN)).val : ℤ) = 0 at hx
    omega
  have hz : layerHeight layers N (lastIndex layers N hl hN) = ((layers - 1 : ℕ) : ℤ) := hy
  simp only [layeredPos, hi, hz]

end ProteinFolding.CubicPackingSnake
