import ProteinFolding.Cubic.Proofs.PackingItemStrips
import ProteinFolding.Cubic.Proofs.PackingSources

/-! Allocate an exact packing to nonoverlapping rectangular face strips.
Allocations are reordered to the original list of item occurrences, so neither
distinct sizes nor a favourable chain order is assumed. -/

namespace ProteinFolding.CubicPackingItems

structure Placement where
  width : ℕ
  upper : ℤ
  deriving DecidableEq, Repr

def RowsDisjoint (p q : Placement) : Prop :=
  p.upper ≤ q.upper - q.width ∨ q.upper ≤ p.upper - p.width

theorem rowsDisjoint_symm {p q : Placement} (h : RowsDisjoint p q) : RowsDisjoint q p :=
  h.symm

def initialPort (p : Placement) : ℤ := p.upper - p.width + 1
def finalPort (p : Placement) : ℤ := p.upper

theorem placement_ports_disjoint {p q : Placement} (h : RowsDisjoint p q)
    (hp : 0 < p.width) (hq : 0 < q.width) :
    initialPort p ≠ initialPort q ∧ initialPort p ≠ finalPort q ∧
    finalPort p ≠ initialPort q ∧ finalPort p ≠ finalPort q := by
  unfold initialPort finalPort RowsDisjoint at *
  rcases h with h | h <;> omega

/-- Consecutive strips, descending from the upper row of one bin. -/
def allocate (upper : ℤ) : List ℕ → List Placement
  | [] => []
  | a :: sizes => ⟨a, upper⟩ :: allocate (upper - a) sizes

theorem allocate_widths (upper : ℤ) (sizes : List ℕ) :
    (allocate upper sizes).map Placement.width = sizes := by
  induction sizes generalizing upper with
  | nil => rfl
  | cons a sizes ih => simp [allocate, ih]

theorem allocate_bounds (upper : ℤ) (sizes : List ℕ) (p : Placement)
    (hp : p ∈ allocate upper sizes) :
    p.upper ≤ upper ∧ upper - sizes.sum ≤ p.upper - p.width := by
  induction sizes generalizing upper with
  | nil => simp [allocate] at hp
  | cons a sizes ih =>
    simp only [allocate, List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp only [List.sum_cons, Nat.cast_add]
      omega
    · have hb := ih (upper - a) hp
      simp only [List.sum_cons, Nat.cast_add]
      omega

theorem allocate_pairwise (upper : ℤ) (sizes : List ℕ) :
    (allocate upper sizes).Pairwise RowsDisjoint := by
  induction sizes generalizing upper with
  | nil => exact .nil
  | cons a sizes ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih _⟩
    intro p hp
    exact Or.inr (allocate_bounds (upper - a) sizes p hp).1

theorem allocate_coverage (upper : ℤ) (sizes : List ℕ) (y : ℤ) :
    (∃ p ∈ allocate upper sizes, p.upper - p.width < y ∧ y ≤ p.upper) ↔
      upper - sizes.sum < y ∧ y ≤ upper := by
  induction sizes generalizing upper with
  | nil => simp [allocate]
  | cons a sizes ih =>
    constructor
    · rintro ⟨p, hp, hlo, hhi⟩
      have hb := allocate_bounds upper (a :: sizes) p hp
      omega
    · rintro ⟨hlo, hhi⟩
      by_cases ha : upper - a < y
      · exact ⟨⟨a, upper⟩, by simp [allocate], ha, hhi⟩
      · have htail : upper - a - sizes.sum < y ∧ y ≤ upper - a := by
          simp only [List.sum_cons, Nat.cast_add] at hlo
          omega
        obtain ⟨p, hp, hpy⟩ := (ih (upper - a)).mpr htail
        exact ⟨p, List.mem_cons_of_mem _ hp, hpy⟩

theorem allocate_upper_parity (upper : ℤ) (sizes : List ℕ)
    (heven : ∀ a ∈ sizes, a % 2 = 0) (hupper : upper % 2 = 1)
    (p : Placement) (hp : p ∈ allocate upper sizes) : p.upper % 2 = 1 := by
  induction sizes generalizing upper with
  | nil => simp [allocate] at hp
  | cons a sizes ih =>
    have ha := heven a (by simp)
    simp only [allocate, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hupper
    · exact ih (upper - a) (fun a ha => heven a (by simp [ha])) (by omega) hp

/-- Each successive bin begins one full period below its predecessor. -/
def allocateBins (period : ℕ) (upper : ℤ) : List (List ℕ) → List Placement
  | [] => []
  | sizes :: parts => allocate upper sizes ++ allocateBins period (upper - period) parts

theorem allocateBins_widths (period : ℕ) (upper : ℤ) (parts : List (List ℕ)) :
    (allocateBins period upper parts).map Placement.width = parts.flatten := by
  induction parts generalizing upper with
  | nil => rfl
  | cons sizes parts ih => simp [allocateBins, allocate_widths, ih]

theorem allocateBins_upper (period : ℕ) (upper : ℤ) (parts : List (List ℕ))
    (p : Placement) (hp : p ∈ allocateBins period upper parts) : p.upper ≤ upper := by
  induction parts generalizing upper with
  | nil => simp [allocateBins] at hp
  | cons sizes parts ih =>
    simp only [allocateBins, List.mem_append] at hp
    rcases hp with hp | hp
    · exact (allocate_bounds upper sizes p hp).1
    · have hb := ih (upper - period) hp
      omega

theorem allocateBins_pairwise (period B : ℕ) (hperiod : B ≤ period) (upper : ℤ)
    (parts : List (List ℕ)) (hsum : ∀ sizes ∈ parts, sizes.sum = B) :
    (allocateBins period upper parts).Pairwise RowsDisjoint := by
  induction parts generalizing upper with
  | nil => exact .nil
  | cons sizes parts ih =>
    rw [allocateBins, List.pairwise_append]
    refine ⟨allocate_pairwise upper sizes, ih _ (fun xs hxs => hsum xs (by simp [hxs])), ?_⟩
    intro p hp q hq
    have hp' := (allocate_bounds upper sizes p hp).2
    have hq' := allocateBins_upper period (upper - period) parts q hq
    have hs := hsum sizes (by simp)
    rw [hs] at hp'
    exact Or.inr (by omega)

theorem allocateBins_lower (period B : ℕ) (upper : ℤ) (parts : List (List ℕ))
    (hsum : ∀ sizes ∈ parts, sizes.sum = B) (p : Placement)
    (hp : p ∈ allocateBins period upper parts) :
    upper + period - (parts.length : ℤ) * period - B ≤ p.upper - p.width := by
  induction parts generalizing upper with
  | nil => simp [allocateBins] at hp
  | cons sizes parts ih =>
    simp only [allocateBins, List.mem_append] at hp
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    rcases hp with hp | hp
    · have hb := (allocate_bounds upper sizes p hp).2
      rw [hsum sizes (by simp)] at hb
      have hn : 0 ≤ (parts.length : ℤ) * period := by positivity
      omega
    · have hb := ih (upper - period) (fun xs hxs => hsum xs (by simp [hxs])) hp
      omega

theorem allocateBins_upper_parity (period : ℕ) (hperiod : period % 2 = 0)
    (upper : ℤ) (hupper : upper % 2 = 1) (parts : List (List ℕ))
    (heven : ∀ a ∈ parts.flatten, a % 2 = 0) (p : Placement)
    (hp : p ∈ allocateBins period upper parts) : p.upper % 2 = 1 := by
  induction parts generalizing upper with
  | nil => simp [allocateBins] at hp
  | cons sizes parts ih =>
    simp only [allocateBins, List.mem_append] at hp
    rcases hp with hp | hp
    · apply allocate_upper_parity upper sizes _ hupper p hp
      intro a ha
      exact heven a (by simp [ha])
    · apply ih (upper - period) (by omega) _ hp
      intro a ha
      exact heven a (by simp [ha])

/-- The union of bin row intervals, retaining their order and two-wall gaps. -/
def BinRows (period : ℕ) (upper : ℤ) : List (List ℕ) → ℤ → Prop
  | [], _ => False
  | sizes :: parts, y => (upper - sizes.sum < y ∧ y ≤ upper) ∨
      BinRows period (upper - period) parts y

theorem allocateBins_coverage (period : ℕ) (upper : ℤ) (parts : List (List ℕ)) (y : ℤ) :
    (∃ p ∈ allocateBins period upper parts, p.upper - p.width < y ∧ y ≤ p.upper) ↔
      BinRows period upper parts y := by
  induction parts generalizing upper with
  | nil => simp [allocateBins, BinRows]
  | cons sizes parts ih =>
    constructor
    · rintro ⟨p, hp, hy⟩
      simp only [allocateBins, List.mem_append] at hp
      rcases hp with hp | hp
      · exact Or.inl ((allocate_coverage upper sizes y).mp ⟨p, hp, hy⟩)
      · exact Or.inr ((ih _).mp ⟨p, hp, hy⟩)
    · intro hy
      rcases hy with hy | hy
      · obtain ⟨p, hp, hy⟩ := (allocate_coverage upper sizes y).mpr hy
        exact ⟨p, List.mem_append_left _ hp, hy⟩
      · obtain ⟨p, hp, hy⟩ := (ih _).mpr hy
        exact ⟨p, List.mem_append_right _ hp, hy⟩

/-- A finite list permutation can carry arbitrary attached placement data.
In particular repeated item sizes remain separate occurrences. -/
theorem reorder_placements (sizes : List ℕ) (placements : List Placement)
    (hperm : sizes.Perm (placements.map Placement.width)) :
    ∃ reordered : List Placement,
      reordered.map Placement.width = sizes ∧ reordered.Perm placements := by
  have h : Relation.Comp (fun a b => a = List.map Placement.width b) List.Perm sizes placements := by
    rw [List.eq_map_comp_perm]
    exact hperm
  obtain ⟨reordered, hmap, hp⟩ := h
  exact ⟨reordered, hmap.symm, hp⟩

/-- Every exact packing yields disjoint strips in the original item order.
The strip rows fill exactly the bins, all initial ports have even row and all
final ports odd row, and all rows lie strictly within the face boundary. -/
theorem exact_packing_placements (I : Packing.Instance) (parts : List (List ℕ))
    (hexact : Packing.Exact I parts)
    (hpositive : ∀ a ∈ I.sizes, 0 < a) (heven : ∀ a ∈ I.sizes, a % 2 = 0)
    (hB : I.capacity % 2 = 0) :
    ∃ placements : List Placement,
      placements.map Placement.width = I.sizes ∧ placements.Pairwise RowsDisjoint ∧
      (∀ p ∈ placements,
        1 ≤ p.upper - p.width ∧ p.upper ≤ (I.bins * (I.capacity + 2) : ℕ) - (1 : ℤ) ∧
        0 < p.width ∧ p.width % 2 = 0 ∧ p.upper % 2 = 1) ∧
      (∀ y : ℤ, (∃ p ∈ placements, p.upper - p.width < y ∧ y ≤ p.upper) ↔
        BinRows (I.capacity + 2) ((I.bins * (I.capacity + 2) : ℕ) - (1 : ℤ)) parts y) := by
  let period := I.capacity + 2
  let d := I.bins * period
  let upper : ℤ := d - 1
  let allocated := allocateBins period upper parts
  have hw : allocated.map Placement.width = parts.flatten := allocateBins_widths _ _ _
  obtain ⟨placements, hmap, hp⟩ := reorder_placements I.sizes allocated (hw ▸ hexact.2.1)
  have hperiod : period % 2 = 0 := by dsimp [period]; omega
  have hd : d % 2 = 0 := by simp only [d, Nat.mul_mod, hperiod, Nat.mul_zero, Nat.zero_mod]
  have hupper : upper % 2 = 1 := by dsimp [upper]; omega
  refine ⟨placements, hmap, ?_, ?_, ?_⟩
  · exact (allocateBins_pairwise period I.capacity (by dsimp [period]; omega) upper parts
      hexact.2.2).perm hp.symm (fun h => rowsDisjoint_symm h)
  · intro p hpm
    have hpa := hp.mem_iff.mp hpm
    have hl := allocateBins_lower period I.capacity upper parts hexact.2.2 p hpa
    have hu := allocateBins_upper period upper parts p hpa
    have hm : p.width ∈ I.sizes := by
      rw [← hmap]
      exact List.mem_map.mpr ⟨p, hpm, rfl⟩
    have hpar := allocateBins_upper_parity period hperiod upper hupper parts
      (fun a ha => heven a (hexact.2.1.mem_iff.mpr ha)) p hpa
    rw [hexact.1] at hl
    have hde : (d : ℤ) = (I.bins : ℤ) * period := by simp [d]
    have hper : (period : ℤ) = I.capacity + 2 := by simp [period]
    dsimp only [upper] at hl hu
    refine ⟨by omega, hu, hpositive _ hm, heven _ hm, hpar⟩
  · intro y
    rw [← allocateBins_coverage]
    constructor
    · rintro ⟨p, hpm, hy⟩
      exact ⟨p, hp.mem_iff.mp hpm, hy⟩
    · rintro ⟨p, hpm, hy⟩
      exact ⟨p, hp.mem_iff.mpr hpm, hy⟩

end ProteinFolding.CubicPackingItems
