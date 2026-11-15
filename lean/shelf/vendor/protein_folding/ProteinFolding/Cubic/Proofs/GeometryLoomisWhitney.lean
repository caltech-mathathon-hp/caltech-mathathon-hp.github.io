import ProteinFolding.Cubic.Statement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# A finite three-dimensional Loomis--Whitney inequality

The ambient coordinate types may be infinite. All cardinalities and sums below
use finite projections of the given finite set of triples.
-/

namespace ProteinFolding.CubicGeometry.LoomisWhitney

open scoped BigOperators

variable {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]

def xyProjection (S : Finset (A × B × C)) : Finset (A × B) :=
  S.image (fun p => (p.1, p.2.1))

def xzProjection (S : Finset (A × B × C)) : Finset (A × C) :=
  S.image (fun p => (p.1, p.2.2))

def yzProjection (S : Finset (A × B × C)) : Finset (B × C) := S.image Prod.snd

def xyFiber (S : Finset (A × B × C)) (xy : A × B) : Finset (A × B × C) :=
  S.filter (fun p => (p.1, p.2.1) = xy)

def xDegree (S : Finset (A × B × C)) (x : A) : ℕ :=
  ((xzProjection S).filter (fun p => p.1 = x)).card

def yDegree (S : Finset (A × B × C)) (y : B) : ℕ :=
  ((yzProjection S).filter (fun p => p.1 = y)).card

theorem xyFiber_card_le_xDegree (S : Finset (A × B × C)) (xy : A × B) :
    (xyFiber S xy).card ≤ xDegree S xy.1 := by
  apply Finset.card_le_card_of_injOn (fun p => (p.1, p.2.2))
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image_of_mem _ hp'.1, congrArg Prod.fst hp'.2⟩
  · intro p hp q hq hpq
    have hxy := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
    have hx : p.1 = q.1 := congrArg (fun z : A × C => z.1) hpq
    have hy : p.2.1 = q.2.1 := congrArg (fun z : A × B => z.2) hxy
    have hz : p.2.2 = q.2.2 := congrArg (fun z : A × C => z.2) hpq
    exact Prod.ext hx (Prod.ext hy hz)

theorem xyFiber_card_le_yDegree (S : Finset (A × B × C)) (xy : A × B) :
    (xyFiber S xy).card ≤ yDegree S xy.2 := by
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image_of_mem _ hp'.1, congrArg Prod.snd hp'.2⟩
  · intro p hp q hq hpq
    have hxy := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
    have hx : p.1 = q.1 := congrArg (fun z : A × B => z.1) hxy
    exact Prod.ext hx hpq

omit [DecidableEq C] in
theorem sum_xyFiber_card (S : Finset (A × B × C)) :
    (∑ xy ∈ xyProjection S, (xyFiber S xy).card) = S.card := by
  exact (Finset.card_eq_sum_card_image (fun p => (p.1, p.2.1)) S).symm

omit [DecidableEq B] in
theorem sum_xDegree (S : Finset (A × B × C)) :
    (∑ x ∈ S.image Prod.fst, xDegree S x) = (xzProjection S).card := by
  symm
  apply Finset.card_eq_sum_card_fiberwise
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  exact Finset.mem_image_of_mem _ hq

omit [DecidableEq A] in
theorem sum_yDegree (S : Finset (A × B × C)) :
    (∑ y ∈ S.image (fun p => p.2.1), yDegree S y) = (yzProjection S).card := by
  symm
  apply Finset.card_eq_sum_card_fiberwise
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  exact Finset.mem_image_of_mem _ hq

/-- The three-dimensional discrete Loomis--Whitney inequality. -/
theorem card_sq_le_projection_product (S : Finset (A × B × C)) :
    S.card ^ 2 ≤ (xyProjection S).card * (xzProjection S).card * (yzProjection S).card := by
  have hCS : (∑ xy ∈ xyProjection S, (xyFiber S xy).card) ^ 2 ≤
      (xyProjection S).card * ∑ xy ∈ xyProjection S, (xyFiber S xy).card ^ 2 := by
    simpa using (Finset.sum_mul_sq_le_sq_mul_sq (R := ℕ) (xyProjection S)
      (fun _ => 1) (fun xy => (xyFiber S xy).card))
  have hFiber : ∑ xy ∈ xyProjection S, (xyFiber S xy).card ^ 2 ≤
      ∑ xy ∈ xyProjection S, xDegree S xy.1 * yDegree S xy.2 := by
    apply Finset.sum_le_sum
    intro xy _
    simpa only [pow_two] using Nat.mul_le_mul
      (xyFiber_card_le_xDegree S xy) (xyFiber_card_le_yDegree S xy)
  have hsubset : xyProjection S ⊆ (S.image Prod.fst) ×ˢ
      (S.image (fun p => p.2.1)) := by
    intro xy hxy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hxy
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  have hproduct : (∑ xy ∈ xyProjection S, xDegree S xy.1 * yDegree S xy.2) ≤
      (xzProjection S).card * (yzProjection S).card := by
    calc
      _ ≤ ∑ xy ∈ (S.image Prod.fst) ×ˢ (S.image (fun p => p.2.1)),
          xDegree S xy.1 * yDegree S xy.2 := Finset.sum_le_sum_of_subset hsubset
      _ = (∑ x ∈ S.image Prod.fst, xDegree S x) *
          (∑ y ∈ S.image (fun p => p.2.1), yDegree S y) := by
        rw [Finset.sum_product, Finset.sum_mul_sum]
      _ = _ := by rw [sum_xDegree, sum_yDegree]
  rw [sum_xyFiber_card] at hCS
  calc
    S.card ^ 2 ≤ (xyProjection S).card *
        (∑ xy ∈ xyProjection S, (xyFiber S xy).card ^ 2) := hCS
    _ ≤ (xyProjection S).card * ((xzProjection S).card * (yzProjection S).card) :=
      Nat.mul_le_mul_left _ (hFiber.trans hproduct)
    _ = _ := (Nat.mul_assoc _ _ _).symm

/-- Equality in the projection inequality saturates the degree-product sum
and each fiber-square inequality. -/
theorem equality_fiber_products (S : Finset (A × B × C)) (hne : S.Nonempty)
    (heq : S.card ^ 2 = (xyProjection S).card * (xzProjection S).card *
      (yzProjection S).card) :
    (∑ xy ∈ xyProjection S, xDegree S xy.1 * yDegree S xy.2) =
      (xzProjection S).card * (yzProjection S).card ∧
    ∀ xy ∈ xyProjection S, (xyFiber S xy).card ^ 2 = xDegree S xy.1 * yDegree S xy.2 := by
  have hCS : S.card ^ 2 ≤ (xyProjection S).card *
      ∑ xy ∈ xyProjection S, (xyFiber S xy).card ^ 2 := by
    simpa [sum_xyFiber_card] using (Finset.sum_mul_sq_le_sq_mul_sq (R := ℕ)
      (xyProjection S) (fun _ => 1) (fun xy => (xyFiber S xy).card))
  have hPoint : ∀ xy ∈ xyProjection S,
      (xyFiber S xy).card ^ 2 ≤ xDegree S xy.1 * yDegree S xy.2 := by
    intro xy _
    simpa only [pow_two] using Nat.mul_le_mul
      (xyFiber_card_le_xDegree S xy) (xyFiber_card_le_yDegree S xy)
  have hFiber := Finset.sum_le_sum hPoint
  have hsubset : xyProjection S ⊆ (S.image Prod.fst) ×ˢ
      (S.image (fun p => p.2.1)) := by
    intro xy hxy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hxy
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  have hproduct : (∑ xy ∈ xyProjection S, xDegree S xy.1 * yDegree S xy.2) ≤
      (xzProjection S).card * (yzProjection S).card := by
    calc
      _ ≤ ∑ xy ∈ (S.image Prod.fst) ×ˢ (S.image (fun p => p.2.1)),
          xDegree S xy.1 * yDegree S xy.2 := Finset.sum_le_sum_of_subset hsubset
      _ = _ := by rw [Finset.sum_product, ← Finset.sum_mul_sum, sum_xDegree, sum_yDegree]
  have hA : 0 < (xyProjection S).card := by
    obtain ⟨p, hp⟩ := hne
    exact Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _ hp⟩
  have hLower : (xzProjection S).card * (yzProjection S).card ≤
      ∑ xy ∈ xyProjection S, (xyFiber S xy).card ^ 2 := by
    apply Nat.le_of_mul_le_mul_left (c := (xyProjection S).card) _ hA
    simpa only [← Nat.mul_assoc, ← heq] using hCS
  have hSquares := Nat.le_antisymm (hFiber.trans hproduct) hLower
  have hDegrees := Nat.le_antisymm hproduct (hSquares ▸ hFiber)
  refine ⟨hDegrees, ?_⟩
  exact (Finset.sum_eq_sum_iff_of_le hPoint).mp (hSquares.trans hDegrees.symm)

omit [DecidableEq B] in
theorem xDegree_pos (S : Finset (A × B × C)) {x : A} (hx : x ∈ S.image Prod.fst) :
    0 < xDegree S x := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  apply Finset.card_pos.mpr
  exact ⟨(p.1, p.2.2), Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hp, rfl⟩⟩

omit [DecidableEq A] in
theorem yDegree_pos (S : Finset (A × B × C)) {y : B}
    (hy : y ∈ S.image (fun p => p.2.1)) : 0 < yDegree S y := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
  apply Finset.card_pos.mpr
  exact ⟨p.2, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hp, rfl⟩⟩

/-- Equality forces the xy projection to be a full rectangle. -/
theorem equality_xy_full (S : Finset (A × B × C)) (hne : S.Nonempty)
    (heq : S.card ^ 2 = (xyProjection S).card * (xzProjection S).card *
      (yzProjection S).card) :
    xyProjection S = (S.image Prod.fst) ×ˢ (S.image (fun p => p.2.1)) := by
  have hsubset : xyProjection S ⊆ (S.image Prod.fst) ×ˢ
      (S.image (fun p => p.2.1)) := by
    intro xy hxy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hxy
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  apply Finset.Subset.antisymm hsubset
  intro xy hxy
  by_contra hnot
  have hpos : 0 < xDegree S xy.1 * yDegree S xy.2 :=
    Nat.mul_pos (xDegree_pos S (Finset.mem_product.mp hxy).1)
      (yDegree_pos S (Finset.mem_product.mp hxy).2)
  have hlt := Finset.sum_lt_sum_of_subset
    (f := fun xy => xDegree S xy.1 * yDegree S xy.2)
    hsubset hxy hnot hpos (fun _ _ _ => Nat.zero_le _)
  have hprod : (∑ xy ∈ (S.image Prod.fst) ×ˢ (S.image (fun p => p.2.1)),
      xDegree S xy.1 * yDegree S xy.2) = (xzProjection S).card * (yzProjection S).card := by
    rw [Finset.sum_product, ← Finset.sum_mul_sum, sum_xDegree, sum_yDegree]
  rw [(equality_fiber_products S hne heq).1, hprod] at hlt
  exact (Nat.lt_irrefl _ hlt)

/-- Every nonempty xy fiber has exactly the size of both incident projection
fibers when Loomis--Whitney is an equality. -/
theorem equality_fiber_cards (S : Finset (A × B × C)) (hne : S.Nonempty)
    (heq : S.card ^ 2 = (xyProjection S).card * (xzProjection S).card *
      (yzProjection S).card) {xy : A × B} (hxy : xy ∈ xyProjection S) :
    (xyFiber S xy).card = xDegree S xy.1 ∧ (xyFiber S xy).card = yDegree S xy.2 := by
  have hsq := (equality_fiber_products S hne heq).2 xy hxy
  rw [pow_two] at hsq
  have hb := xyFiber_card_le_xDegree S xy
  have hc := xyFiber_card_le_yDegree S xy
  have hpos : 0 < (xyFiber S xy).card := by
    obtain ⟨p, hp, hpxy⟩ := Finset.mem_image.mp hxy
    exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hpxy⟩⟩
  have hb' : xDegree S xy.1 ≤ (xyFiber S xy).card := by
    apply Nat.le_of_mul_le_mul_right (c := (xyFiber S xy).card) _ hpos
    exact (Nat.mul_le_mul_left _ hc).trans_eq hsq.symm
  have hc' : yDegree S xy.2 ≤ (xyFiber S xy).card := by
    apply Nat.le_of_mul_le_mul_left (c := (xyFiber S xy).card) _ hpos
    exact (Nat.mul_le_mul_right _ hb).trans_eq hsq.symm
  exact ⟨Nat.le_antisymm hb hb', Nat.le_antisymm hc hc'⟩

theorem equality_fiber_xz_image (S : Finset (A × B × C)) (hne : S.Nonempty)
    (heq : S.card ^ 2 = (xyProjection S).card * (xzProjection S).card *
      (yzProjection S).card) {xy : A × B} (hxy : xy ∈ xyProjection S) :
    (xyFiber S xy).image (fun p => (p.1, p.2.2)) =
      (xzProjection S).filter (fun p => p.1 = xy.1) := by
  have hinj : Set.InjOn (fun p : A × B × C => (p.1, p.2.2)) (xyFiber S xy) := by
    intro p hp q hq hpq
    have hxy' := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
    have hx : p.1 = q.1 := congrArg (fun z : A × C => z.1) hpq
    have hy : p.2.1 = q.2.1 := congrArg (fun z : A × B => z.2) hxy'
    have hz : p.2.2 = q.2.2 := congrArg (fun z : A × C => z.2) hpq
    exact Prod.ext hx (Prod.ext hy hz)
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have hq' := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image_of_mem _ hq'.1, congrArg Prod.fst hq'.2⟩
  · rw [Finset.card_image_of_injOn hinj]
    exact (equality_fiber_cards S hne heq hxy).1.symm.le

theorem equality_fiber_yz_image (S : Finset (A × B × C)) (hne : S.Nonempty)
    (heq : S.card ^ 2 = (xyProjection S).card * (xzProjection S).card *
      (yzProjection S).card) {xy : A × B} (hxy : xy ∈ xyProjection S) :
    (xyFiber S xy).image Prod.snd = (yzProjection S).filter (fun p => p.1 = xy.2) := by
  have hinj : Set.InjOn (Prod.snd : A × B × C → B × C) (xyFiber S xy) := by
    intro p hp q hq hpq
    have hxy' := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
    have hx : p.1 = q.1 := congrArg (fun z : A × B => z.1) hxy'
    exact Prod.ext hx hpq
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have hq' := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image_of_mem _ hq'.1, congrArg Prod.snd hq'.2⟩
  · rw [Finset.card_image_of_injOn hinj]
    exact (equality_fiber_cards S hne heq hxy).2.symm.le

/-- In an equality case, every combination of three occurring coordinates is
present in the finite set. -/
theorem equality_mem_of_coordinate_mem (S : Finset (A × B × C)) (hne : S.Nonempty)
    (heq : S.card ^ 2 = (xyProjection S).card * (xzProjection S).card *
      (yzProjection S).card) {x : A} {y : B} {z : C}
    (hx : x ∈ S.image Prod.fst) (hy : y ∈ S.image (fun p => p.2.1))
    (hz : z ∈ S.image (fun p => p.2.2)) : (x, y, z) ∈ S := by
  obtain ⟨p, hp, hpz⟩ := Finset.mem_image.mp hz
  have hxy0 : (x, p.2.1) ∈ xyProjection S := by
    rw [equality_xy_full S hne heq]
    exact Finset.mem_product.mpr ⟨hx, Finset.mem_image_of_mem _ hp⟩
  have hyz : (p.2.1, z) ∈ (yzProjection S).filter (fun q => q.1 = p.2.1) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨p, hp, Prod.ext rfl hpz⟩, rfl⟩
  rw [← equality_fiber_yz_image S hne heq hxy0] at hyz
  obtain ⟨q, hq, hqyz⟩ := Finset.mem_image.mp hyz
  have hq' := Finset.mem_filter.mp hq
  have hqx : q.1 = x := congrArg (fun r : A × B => r.1) hq'.2
  have hqz : q.2.2 = z := congrArg (fun r : B × C => r.2) hqyz
  have hxz : (x, z) ∈ xzProjection S :=
    Finset.mem_image.mpr ⟨q, hq'.1, Prod.ext hqx hqz⟩
  have hxy : (x, y) ∈ xyProjection S := by
    rw [equality_xy_full S hne heq]
    exact Finset.mem_product.mpr ⟨hx, hy⟩
  have hxz' : (x, z) ∈ (xzProjection S).filter (fun q => q.1 = x) :=
    Finset.mem_filter.mpr ⟨hxz, rfl⟩
  rw [← equality_fiber_xz_image S hne heq hxy] at hxz'
  obtain ⟨r, hr, hrxz⟩ := Finset.mem_image.mp hxz'
  have hr' := Finset.mem_filter.mp hr
  have hrx : r.1 = x := congrArg (fun t : A × B => t.1) hr'.2
  have hry : r.2.1 = y := congrArg (fun t : A × B => t.2) hr'.2
  have hrz : r.2.2 = z := congrArg (fun t : A × C => t.2) hrxz
  have hreq : r = (x, y, z) := Prod.ext hrx (Prod.ext hry hrz)
  exact hreq ▸ hr'.1

/-- Equality in three-dimensional finite Loomis--Whitney forces a Cartesian
product of coordinate sets. Empty sets are included without a side condition. -/
theorem equality_is_product (S : Finset (A × B × C))
    (heq : S.card ^ 2 = (xyProjection S).card * (xzProjection S).card *
      (yzProjection S).card) :
    S = (S.image Prod.fst) ×ˢ ((S.image (fun p => p.2.1)) ×ˢ
      (S.image (fun p => p.2.2))) := by
  by_cases hne : S.Nonempty
  · ext p
    constructor
    · intro hp
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp,
        Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩⟩
    · intro hp
      obtain ⟨hx, hyz⟩ := Finset.mem_product.mp hp
      obtain ⟨hy, hz⟩ := Finset.mem_product.mp hyz
      exact equality_mem_of_coordinate_mem S hne heq hx hy hz
  · have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hS]

end ProteinFolding.CubicGeometry.LoomisWhitney
