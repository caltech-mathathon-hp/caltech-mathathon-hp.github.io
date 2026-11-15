import ProteinFolding.Tetrahedral.Geometry

/-!
# First layer facts for Section 4

Layers are indexed by the first integer coordinate. Every bond joins
consecutive layers, and every site has two neighbours in each adjacent layer.
These facts are the starting point for the later gap/run decomposition.
-/

namespace ProteinFolding.Tetrahedral

def layer (k : ℤ) : Set Site := {p | p.val 0 = k}

theorem bondVector_coordinate (d : Fin 4) (k : Fin 3) :
    bondVector d k = 1 ∨ bondVector d k = -1 := by
  revert d k
  decide

/-- Every coordinate changes by one unit across a bond. -/
theorem adj_coordinate {p q : Site} (h : tetrahedralLattice.Adj p q) (k : Fin 3) :
    q.val k = p.val k + 1 ∨ q.val k = p.val k - 1 := by
  obtain ⟨d, rfl⟩ := (adj_iff_exists_step p q).mp h
  by_cases hp : InASublattice p.val
  · simp only [step_val_of_A p hp]
    rcases bondVector_coordinate d k with hd | hd <;> simp [hd, sub_eq_add_neg]
  · simp only [step_val_of_B p ((inB_iff_not_inA p).mpr hp)]
    rcases bondVector_coordinate d k with hd | hd <;> simp [hd, sub_eq_add_neg]

/-- Every edge joins L_k to L_(k+1), in one orientation or the other. -/
theorem adj_consecutive_layers {p q : Site} (h : tetrahedralLattice.Adj p q) :
    q ∈ layer (p.val 0 + 1) ∨ q ∈ layer (p.val 0 - 1) := adj_coordinate h 0

theorem no_edges_within_layer {p q : Site} {k : ℤ}
    (hp : p ∈ layer k) (hq : q ∈ layer k) : ¬ tetrahedralLattice.Adj p q := by
  intro h
  have hd := adj_coordinate h 0
  change p.val 0 = k at hp
  change q.val 0 = k at hq
  omega

def neighboursAbove (p : Site) : Finset Site :=
  (neighbours p).filter (fun q => q.val 0 = p.val 0 + 1)

def neighboursBelow (p : Site) : Finset Site :=
  (neighbours p).filter (fun q => q.val 0 = p.val 0 - 1)

theorem card_neighboursAbove (p : Site) : (neighboursAbove p).card = 2 := by
  unfold neighboursAbove neighbours
  rw [Finset.filter_image, Finset.card_image_of_injective _ (step_injective p)]
  by_cases hp : InASublattice p.val
  · simp only [step_val_of_A p hp]
    have heq : ∀ d : Fin 4,
        (p.val 0 + bondVector d 0 = p.val 0 + 1) ↔ bondVector d 0 = 1 := by
      intro d
      omega
    simp_rw [heq]
    decide
  · simp only [step_val_of_B p ((inB_iff_not_inA p).mpr hp)]
    have heq : ∀ d : Fin 4,
        (p.val 0 - bondVector d 0 = p.val 0 + 1) ↔ bondVector d 0 = -1 := by
      intro d
      omega
    simp_rw [heq]
    decide

theorem card_neighboursBelow (p : Site) : (neighboursBelow p).card = 2 := by
  unfold neighboursBelow neighbours
  rw [Finset.filter_image, Finset.card_image_of_injective _ (step_injective p)]
  by_cases hp : InASublattice p.val
  · simp only [step_val_of_A p hp]
    have heq : ∀ d : Fin 4,
        (p.val 0 + bondVector d 0 = p.val 0 - 1) ↔ bondVector d 0 = -1 := by
      intro d
      omega
    simp_rw [heq]
    decide
  · simp only [step_val_of_B p ((inB_iff_not_inA p).mpr hp)]
    have heq : ∀ d : Fin 4,
        (p.val 0 - bondVector d 0 = p.val 0 - 1) ↔ bondVector d 0 = 1 := by
      intro d
      omega
    simp_rw [heq]
    decide

end ProteinFolding.Tetrahedral
