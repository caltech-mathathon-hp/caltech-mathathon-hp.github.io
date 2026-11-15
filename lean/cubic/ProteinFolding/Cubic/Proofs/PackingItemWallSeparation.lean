import ProteinFolding.Cubic.Proofs.PackingItemPorts
import ProteinFolding.Cubic.Proofs.PackingWallUnitFold
import ProteinFolding.Cubic.Proofs.PackingStripAttachments

/-! Exact packing allocations retain their bin-row coverage when reindexed
by the original item occurrences. Those rows avoid every horizontal wall
row, so the compressed item paths are disjoint from all wall H owners. -/

namespace ProteinFolding.CubicPackingItems

open CubicPacking CubicPackingWalls CubicPackingRouting CubicPackingLift

theorem between_periods_avoids (period m t : ℕ) (y : ℤ)
    (hy : (m : ℤ) * period + 1 < y ∧ y < ((m : ℤ) + 1) * period) :
    y ≠ (t : ℤ) * period ∧ y ≠ (t : ℤ) * period + 1 := by
  by_cases ht : t ≤ m
  · have hm : (t : ℤ) * period ≤ (m : ℤ) * period := by
      exact_mod_cast Nat.mul_le_mul_right period ht
    constructor <;> omega
  · have hm : ((m : ℤ) + 1) * period ≤ (t : ℤ) * period := by
      exact_mod_cast Nat.mul_le_mul_right period (show m + 1 ≤ t by omega)
    constructor <;> omega

/-- The two rows surrounding every bin are absent from the allocated item
rows, independently of the order of bins or the item sizes within them. -/
theorem BinRows_avoids_walls (B : ℕ) (parts : List (List ℕ))
    (hsum : ∀ sizes ∈ parts, sizes.sum = B) (y : ℤ)
    (hy : BinRows (B + 2) ((parts.length * (B + 2) : ℕ) - (1 : ℤ)) parts y)
    (t : ℕ) : y ≠ (t : ℤ) * (B + 2) ∧ y ≠ (t : ℤ) * (B + 2) + 1 := by
  induction parts with
  | nil => exact False.elim hy
  | cons sizes parts ih =>
    rcases hy with hy | hy
    · have hs := hsum sizes (by simp)
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.cast_add,
        Nat.cast_mul, Nat.cast_one] at hy
      rw [hs] at hy
      apply between_periods_avoids (B + 2) parts.length t y
      push_cast at hy ⊢
      ring_nf at hy ⊢
      constructor <;> omega
    · apply ih (fun xs hxs => hsum xs (by simp [hxs]))
      have he : (((parts.length + 1) * (B + 2) : ℕ) : ℤ) - 1 - ((B + 2 : ℕ) : ℤ) =
          (parts.length * (B + 2) : ℕ) - (1 : ℤ) := by push_cast; ring
      change BinRows (B + 2) _ parts y at hy
      rw [show ((sizes :: parts).length * (B + 2) : ℕ) = (parts.length + 1) * (B + 2) from rfl, he] at hy
      exact hy

/-- Reindex placements without discarding their exact row coverage. -/
theorem layout_of_placements_with_rows (d : ℕ) (items : List ℕ) (ps : List Placement)
    (hmap : ps.map Placement.width = items) (hp : ps.Pairwise RowsDisjoint)
    (hb : ∀ p ∈ ps, 1 ≤ p.upper - p.width ∧ p.upper ≤ (d : ℤ) - 1 ∧
      0 < p.width ∧ p.width % 2 = 0 ∧ p.upper % 2 = 1) :
    ∃ L : Layout d items, ∀ y : ℤ,
      (∃ i, (L.placement i).upper - (L.placement i).width < y ∧ y ≤ (L.placement i).upper) ↔
      ∃ p ∈ ps, p.upper - p.width < y ∧ y ≤ p.upper := by
  have hlen : ps.length = items.length := by simpa only [List.length_map] using congrArg List.length hmap
  let index : Fin items.length → Fin ps.length := fun i => ⟨i.val, by rw [hlen]; exact i.isLt⟩
  let atP : Fin items.length → Placement := fun i => ps.get (index i)
  have hat (i : Fin items.length) := hb (atP i) (List.get_mem ps (index i))
  let L : Layout d items :=
    { placement := atP
      width_eq := by
        intro i
        have he := congrArg (fun xs : List ℕ => xs[i.val]?) hmap
        simp only [List.getElem?_map] at he
        rw [List.getElem?_eq_getElem (index i).isLt, List.getElem?_eq_getElem i.isLt] at he
        simpa only [Option.map_some, Option.some.injEq, atP, index, List.get_eq_getElem] using he
      separate := by
        intro i j hij
        by_cases hlt : i.val < j.val
        · exact List.pairwise_iff_get.mp hp (index i) (index j) hlt
        · apply rowsDisjoint_symm
          exact List.pairwise_iff_get.mp hp (index j) (index i) (by
            have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
            change j.val < i.val
            omega)
      bounds := fun i => ⟨(hat i).1, (hat i).2.1⟩
      width_pos := fun i => (hat i).2.2.1
      width_even := fun i => (hat i).2.2.2.1
      upper_odd := fun i => (hat i).2.2.2.2 }
  refine ⟨L, fun y => ⟨?_, ?_⟩⟩
  · rintro ⟨i, hi⟩
    exact ⟨atP i, List.get_mem ps (index i), hi⟩
  · rintro ⟨p, hpm, hy⟩
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hpm
    let i : Fin items.length := ⟨j.val, by rw [←hlen]; exact j.isLt⟩
    refine ⟨i, ?_⟩
    have he : atP i = p := by
      change ps.get (index i) = p
      have hij : index i = j := Fin.ext rfl
      rw [hij]
      exact hj
    change (atP i).upper - (atP i).width < y ∧ y ≤ (atP i).upper
    rw [he]
    exact hy

/-- An exact source packing supplies one layout together with the full bin
coverage statement used in the item/wall collision proof. -/
theorem exact_packing_layout_with_rows (q Q : ℕ) (items : List ℕ) (parts : List (List ℕ))
    (hexact : Packing.Exact ⟨items, 4 * Q, q⟩ parts)
    (hpositive : ∀ a ∈ items, 0 < a) (heven : ∀ a ∈ items, a % 2 = 0) :
    ∃ L : Layout (depth q Q) items, ∀ y : ℤ,
      (∃ i, (L.placement i).upper - (L.placement i).width < y ∧ y ≤ (L.placement i).upper) ↔
      BinRows (beta Q) ((depth q Q : ℤ) - 1) parts y := by
  obtain ⟨ps, hm, hp, hb, hc⟩ := exact_packing_placements ⟨items, 4 * Q, q⟩ parts hexact
    hpositive heven (by change (4 * Q) % 2 = 0; omega)
  have hb' : ∀ p ∈ ps, 1 ≤ p.upper - p.width ∧ p.upper ≤ (depth q Q : ℤ) - 1 ∧
      0 < p.width ∧ p.width % 2 = 0 ∧ p.upper % 2 = 1 := by
    intro p hpm
    simpa only [depth, beta] using hb p hpm
  obtain ⟨L, hL⟩ := layout_of_placements_with_rows (depth q Q) items ps hm hp hb'
  refine ⟨L, ?_⟩
  intro y
  rw [hL y]
  simpa only [depth, beta] using hc y

theorem unitOwners_rails_or_rows (d A : ℕ) (top : ℤ)
    (i : Fin (A + (d + ((2 * A + 2) + (d + A))))) :
    unitOwners d A top i 0 = 0 ∨ unitOwners d A top i 0 = (d : ℤ) + 1 ∨
      unitOwners d A top i 1 = top ∨
      unitOwners d A top i 1 = top - (2 * A + 2) + 1 := by
  unfold unitOwners
  cases i using Fin.addCases with
  | left i => simp only [Fin.append_left]; exact Or.inr (Or.inl rfl)
  | right i =>
    simp only [Fin.append_right]
    cases i using Fin.addCases with
    | left i => simp only [Fin.append_left]; exact Or.inr (Or.inr (Or.inl rfl))
    | right i =>
      simp only [Fin.append_right]
      cases i using Fin.addCases with
      | left i => simp only [Fin.append_left]; exact Or.inl rfl
      | right i =>
        simp only [Fin.append_right]
        cases i using Fin.addCases with
        | left i => simp only [Fin.append_left]; exact Or.inr (Or.inr (Or.inr rfl))
        | right i => simp only [Fin.append_right]; exact Or.inr (Or.inl rfl)

theorem wallTop_period (q Q : ℕ) (j : Fin q) :
    wallTop q Q j = ((q - j.val : ℕ) : ℤ) * beta Q := by
  have hj : j.val ≤ q := by omega
  simp only [wallTop, depth, Nat.cast_mul, Nat.cast_sub hj]
  ring

theorem wallBottom_period (q Q : ℕ) (j : Fin q) :
    wallTop q Q j - (2 * (alpha Q : ℤ) + 2) + 1 =
      ((q - j.val - 1 : ℕ) : ℤ) * beta Q + 1 := by
  have hj : j.val ≤ q := by omega
  have hp : 1 ≤ q - j.val := by omega
  have hb : (beta Q : ℤ) = 2 * (alpha Q : ℤ) + 2 := by simp [beta, alpha]; ring
  rw [wallTop_period, Nat.cast_sub hp]
  rw [←hb]
  push_cast
  ring

theorem binRows_avoid_wall_rows (q Q : ℕ) (items : List ℕ) (parts : List (List ℕ))
    (hexact : Packing.Exact ⟨items, 4 * Q, q⟩ parts)
    (y : ℤ) (hy : BinRows (beta Q) ((depth q Q : ℤ) - 1) parts y) (j : Fin q) :
    y ≠ wallTop q Q j ∧ y ≠ wallTop q Q j - (2 * (alpha Q : ℤ) + 2) + 1 := by
  have hrows : BinRows (4 * Q + 2) ((parts.length * (4 * Q + 2) : ℕ) - (1 : ℤ)) parts y := by
    simpa only [hexact.1, beta, depth] using hy
  have hsum : ∀ sizes ∈ parts, sizes.sum = 4 * Q := hexact.2.2
  rw [wallBottom_period, wallTop_period]
  exact ⟨(BinRows_avoids_walls (4 * Q) parts hsum y hrows (q - j.val)).1,
    (BinRows_avoids_walls (4 * Q) parts hsum y hrows (q - j.val - 1)).2⟩

theorem strip_unitOwners_disjoint (q Q width : ℕ) (upper : ℤ)
    (items : List ℕ) (parts : List (List ℕ))
    (hexact : Packing.Exact ⟨items, 4 * Q, q⟩ parts)
    (hrows : ∀ y, upper - width < y ∧ y ≤ upper →
      BinRows (beta Q) ((depth q Q : ℤ) - 1) parts y)
    (i : Fin (depth q Q * width)) (j : Fin q)
    (k : Fin (alpha Q + (depth q Q + ((2 * alpha Q + 2) + (depth q Q + alpha Q))))) :
    stripPos (depth q Q) width upper i ≠
      unitOwners (depth q Q) (alpha Q) (wallTop q Q j) k := by
  intro he
  have hb := (stripPos_image (depth q Q) width upper _).mp ⟨i, rfl⟩
  have hr := hrows _ ⟨hb.2.2.1, hb.2.2.2.1⟩
  have ha := binRows_avoid_wall_rows q Q items parts hexact _ hr j
  have hu := unitOwners_rails_or_rows (depth q Q) (alpha Q) (wallTop q Q j) k
  have hx := congrFun he 0
  have hy := congrFun he 1
  rcases hu with hu | hu | hu | hu
  · omega
  · omega
  · exact ha.1 (hy.trans hu)
  · exact ha.2 (hy.trans hu)

theorem layout_strip_unitOwners_disjoint (q Q : ℕ) (items : List ℕ)
    (parts : List (List ℕ)) (hexact : Packing.Exact ⟨items, 4 * Q, q⟩ parts)
    (L : Layout (depth q Q) items)
    (hrows : ∀ y, (∃ i, (L.placement i).upper - (L.placement i).width < y ∧
      y ≤ (L.placement i).upper) → BinRows (beta Q) ((depth q Q : ℤ) - 1) parts y)
    (i : Fin items.length) (j : Fin q)
    (k : Fin (depth q Q * (L.placement i).width))
    (l : Fin (alpha Q + (depth q Q + ((2 * alpha Q + 2) + (depth q Q + alpha Q))))) :
    stripPos (depth q Q) (L.placement i).width (L.placement i).upper k ≠
      unitOwners (depth q Q) (alpha Q) (wallTop q Q j) l := by
  apply strip_unitOwners_disjoint q Q (L.placement i).width (L.placement i).upper
    items parts hexact _ k j l
  intro y hy
  exact hrows y ⟨i, hy⟩

/-- The item and wall decorations inherit separation from their H paths. -/
theorem layout_strip_wallUnit_disjoint (q Q : ℕ) (items : List ℕ)
    (parts : List (List ℕ)) (hexact : Packing.Exact ⟨items, 4 * Q, q⟩ parts)
    (L : Layout (depth q Q) items)
    (hrows : ∀ y, (∃ i, (L.placement i).upper - (L.placement i).width < y ∧
      y ≤ (L.placement i).upper) → BinRows (beta Q) ((depth q Q : ℤ) - 1) parts y)
    (hd : 0 < depth q Q) (i : Fin items.length) (hprod : 2 ∣ depth q Q * (L.placement i).width)
    (j : Fin q) (f : Fold cubicLattice (wallUnit q Q).length)
    (hf : AttachedTo (fun _ => 0) (side q Q) f
      (unitOwners (depth q Q) (alpha Q) (wallTop q Q j))) :
    ∀ k l, (stripWordFold (depth q Q) (L.placement i).width (L.placement i).upper hd hprod).pos k ≠ f.pos l := by
  apply attached_folds_disjoint (fun _ => 0) (side q Q) _ _
    (stripFold (depth q Q) (L.placement i).width (L.placement i).upper hd).pos
    (unitOwners (depth q Q) (alpha Q) (wallTop q Q j))
    (stripWordFold_attached _ _ _ hd hprod (by have := L.bounds i; omega)
      (by have := L.bounds i; omega)) hf
  exact layout_strip_unitOwners_disjoint q Q items parts hexact L hrows i j

theorem strip_railOwners_disjoint (d width : ℕ) (upper : ℤ)
    (x y : ℤ) (increasing : Bool) (N : ℕ) (hx : x = 0 ∨ x = (d : ℤ) + 1)
    (i : Fin (d * width)) (j : Fin N) :
    stripPos d width upper i ≠ (verticalFold x y increasing N).pos j := by
  intro he
  have hb := (stripPos_image d width upper _).mp ⟨i, rfl⟩
  have hx' : stripPos d width upper i 0 = x := congrFun he 0
  rcases hx with hx | hx <;> omega

/-- The fixed wall bridges and the full gap chain are strictly to the
right of every item residue, including the item P decorations. -/
theorem stripWordFold_outer_disjoint (d width : ℕ) (upper : ℤ) (hd : 0 < d)
    (hprod : 2 ∣ d * width) (p : Site) (hp : (d : ℤ) < p 0)
    (i : Fin (faceWord (d * width)).length) :
    (stripWordFold d width upper hd hprod).pos i ≠ p := by
  intro he
  have hb := stripWordFold_location d width upper hd hprod i
  have hx := congrFun he 0
  omega

theorem stripWordFold_outerFold_disjoint {N : ℕ} (d width : ℕ) (upper : ℤ)
    (hd : 0 < d) (hprod : 2 ∣ d * width) (g : Fold cubicLattice N)
    (hg : ∀ i, (d : ℤ) < g.pos i 0) :
    ∀ i j, (stripWordFold d width upper hd hprod).pos i ≠ g.pos j :=
  fun i j => stripWordFold_outer_disjoint d width upper hd hprod (g.pos j) (hg j) i

end ProteinFolding.CubicPackingItems
