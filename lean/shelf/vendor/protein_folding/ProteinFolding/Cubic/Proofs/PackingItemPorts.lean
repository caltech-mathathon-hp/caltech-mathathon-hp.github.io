import ProteinFolding.Cubic.Proofs.PackingItemAllocation

/-! Indexed placement and natural port data for item occurrences in their
original sequence order. Binary source sizes are never used as vertex labels;
these are geometric witnesses extracted from an exact unary packing. -/

namespace ProteinFolding.CubicPackingItems

open CubicPacking

structure Layout (d : ℕ) (items : List ℕ) where
  placement : Fin items.length → Placement
  width_eq : ∀ i, (placement i).width = items.get i
  separate : ∀ i j, i ≠ j → RowsDisjoint (placement i) (placement j)
  bounds : ∀ i, 1 ≤ (placement i).upper - (placement i).width ∧ (placement i).upper ≤ (d : ℤ) - 1
  width_pos : ∀ i, 0 < (placement i).width
  width_even : ∀ i, (placement i).width % 2 = 0
  upper_odd : ∀ i, (placement i).upper % 2 = 1

namespace Layout

variable {d : ℕ} {items : List ℕ} (L : Layout d items)

def startPort (i : Fin items.length) : ℕ := (initialPort (L.placement i)).toNat
def endPort (i : Fin items.length) : ℕ := (finalPort (L.placement i)).toNat

theorem startPort_cast (i : Fin items.length) :
    (L.startPort i : ℤ) = initialPort (L.placement i) := by
  have hb := L.bounds i
  dsimp [startPort, initialPort]
  omega

theorem endPort_cast (i : Fin items.length) :
    (L.endPort i : ℤ) = finalPort (L.placement i) := by
  have hb := L.bounds i
  have hp := L.width_pos i
  dsimp [endPort, finalPort]
  omega

theorem startPort_bounds (i : Fin items.length) : 1 ≤ L.startPort i ∧ L.startPort i ≤ d := by
  have hc := L.startPort_cast i
  have hb := L.bounds i
  have hp := L.width_pos i
  dsimp [initialPort] at hc
  omega

theorem endPort_bounds (i : Fin items.length) : 1 ≤ L.endPort i ∧ L.endPort i ≤ d := by
  have hc := L.endPort_cast i
  have hb := L.bounds i
  have hp := L.width_pos i
  dsimp [finalPort] at hc
  omega

theorem startPort_even (i : Fin items.length) : L.startPort i % 2 = 0 := by
  have hc := L.startPort_cast i
  have hw := L.width_even i
  have hu := L.upper_odd i
  dsimp [initialPort] at hc
  omega

theorem endPort_odd (i : Fin items.length) : L.endPort i % 2 = 1 := by
  have hc := L.endPort_cast i
  have hu := L.upper_odd i
  dsimp [finalPort] at hc
  omega

theorem endPort_ne_startPort (i j : Fin items.length) : L.endPort i ≠ L.startPort j := by
  have hi := L.endPort_odd i
  have hj := L.startPort_even j
  omega

theorem startPort_injective : Function.Injective L.startPort := by
  intro i j he
  by_contra hij
  have hs := (placement_ports_disjoint (L.separate i j hij) (L.width_pos i) (L.width_pos j)).1
  have hi := L.startPort_cast i
  have hj := L.startPort_cast j
  exact hs (by omega)

theorem endPort_injective : Function.Injective L.endPort := by
  intro i j he
  by_contra hij
  have hs := (placement_ports_disjoint (L.separate i j hij) (L.width_pos i) (L.width_pos j)).2.2.2
  have hi := L.endPort_cast i
  have hj := L.endPort_cast j
  exact hs (by omega)

end Layout

/-- Reindex a list allocation by the original item occurrences, preserving
all interval, parity, width and separation proofs. -/
theorem layout_of_placements (d : ℕ) (items : List ℕ) (ps : List Placement)
    (hmap : ps.map Placement.width = items) (hp : ps.Pairwise RowsDisjoint)
    (hb : ∀ p ∈ ps, 1 ≤ p.upper - p.width ∧ p.upper ≤ (d : ℤ) - 1 ∧
      0 < p.width ∧ p.width % 2 = 0 ∧ p.upper % 2 = 1) :
    Nonempty (Layout d items) := by
  have hlen : ps.length = items.length := by simpa only [List.length_map] using congrArg List.length hmap
  let index : Fin items.length → Fin ps.length := fun i => ⟨i.val, by rw [hlen]; exact i.isLt⟩
  let atP : Fin items.length → Placement := fun i => ps.get (index i)
  have hat (i : Fin items.length) := hb (atP i) (List.get_mem ps (index i))
  refine ⟨{
    placement := atP
    width_eq := ?_
    separate := ?_
    bounds := fun i => ⟨(hat i).1, (hat i).2.1⟩
    width_pos := fun i => (hat i).2.2.1
    width_even := fun i => (hat i).2.2.2.1
    upper_odd := fun i => (hat i).2.2.2.2 }⟩
  · intro i
    have he := congrArg (fun xs : List ℕ => xs[i.val]?) hmap
    simp only [List.getElem?_map] at he
    rw [List.getElem?_eq_getElem (index i).isLt, List.getElem?_eq_getElem i.isLt] at he
    simpa only [Option.map_some, Option.some.injEq, atP, index, List.get_eq_getElem] using he
  · intro i j hij
    by_cases hlt : i.val < j.val
    · exact List.pairwise_iff_get.mp hp (index i) (index j) hlt
    · apply rowsDisjoint_symm
      exact List.pairwise_iff_get.mp hp (index j) (index i) (by
        have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
        change j.val < i.val
        omega)

theorem exact_packing_layout (q Q : ℕ) (items : List ℕ) (parts : List (List ℕ))
    (hexact : Packing.Exact ⟨items, 4 * Q, q⟩ parts)
    (hpositive : ∀ a ∈ items, 0 < a) (heven : ∀ a ∈ items, a % 2 = 0) :
    Nonempty (Layout (depth q Q) items) := by
  obtain ⟨ps, hm, hp, hb, _⟩ := exact_packing_placements ⟨items, 4 * Q, q⟩ parts hexact
    hpositive heven (by change (4 * Q) % 2 = 0; omega)
  apply layout_of_placements (depth q Q) items ps hm hp
  intro p hpm
  simpa only [depth, beta] using hb p hpm

end ProteinFolding.CubicPackingItems
