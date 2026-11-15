import ProteinFolding.Tetrahedral.FarFieldRouteBounds

namespace ProteinFolding.Tetrahedral.FarField

theorem capParity_swap (p q : Site) (L : ℕ) : CapParity p q L ↔ CapParity q p L := by
  by_cases h : colour p = colour q
  · simp only [CapParity, if_pos h, if_pos h.symm]
  · have h' : colour q ≠ colour p := Ne.symm h
    simp only [CapParity, if_neg h, if_neg h']

abbrev Pairing (w k : ℕ) := Fin w ≃ Fin k × Bool

namespace Pairing

variable {w k : ℕ} (e : Pairing w k)

def first (r : Fin k) : Fin w := e.symm (r, false)
def second (r : Fin k) : Fin w := e.symm (r, true)
def pairIndex (i : Fin w) : Fin k := (e i).1

include e in
theorem card_eq : w = 2 * k := by
  have h := Fintype.card_congr e
  simpa only [Fintype.card_fin, Fintype.card_prod, Fintype.card_bool, Nat.mul_comm] using h

theorem first_ne_second (r : Fin k) : e.first r ≠ e.second r := by
  intro h
  have h' := congrArg e h
  simp [first, second] at h'

@[simp] theorem pairIndex_first (r : Fin k) : e.pairIndex (e.first r) = r := by simp [pairIndex, first]
@[simp] theorem pairIndex_second (r : Fin k) : e.pairIndex (e.second r) = r := by simp [pairIndex, second]

def lower (d : WireData w) (r : Fin k) : Fin w :=
  if d.slabs (e.first r) < d.slabs (e.second r) then e.first r else e.second r

def upper (d : WireData w) (r : Fin k) : Fin w :=
  if d.slabs (e.first r) < d.slabs (e.second r) then e.second r else e.first r

theorem lower_ne_upper (d : WireData w) (r : Fin k) : e.lower d r ≠ e.upper d r := by
  by_cases h : d.slabs (e.first r) < d.slabs (e.second r)
  · simpa only [lower, upper, if_pos h] using e.first_ne_second r
  · simpa only [lower, upper, if_neg h] using (e.first_ne_second r).symm

theorem slab_order (d : WireData w) (r : Fin k) : d.slabs (e.lower d r) < d.slabs (e.upper d r) := by
  by_cases h : d.slabs (e.first r) < d.slabs (e.second r)
  · simpa only [lower, upper, if_pos h] using h
  · simp only [lower, upper, if_neg h]
    have hs := slabValue_separated d.H d.levels (e.first r) (e.second r) (e.first_ne_second r)
    change d.slabs (e.first r) + 60 ≤ d.slabs (e.second r) ∨ d.slabs (e.second r) + 60 ≤ d.slabs (e.first r) at hs
    omega

@[simp] theorem pairIndex_lower (d : WireData w) (r : Fin k) : e.pairIndex (e.lower d r) = r := by
  unfold lower
  split_ifs <;> simp only [pairIndex_first, pairIndex_second]

@[simp] theorem pairIndex_upper (d : WireData w) (r : Fin k) : e.pairIndex (e.upper d r) = r := by
  unfold upper
  split_ifs <;> simp only [pairIndex_first, pairIndex_second]

theorem endpoints_ne (d : WireData w) (r s : Fin k) (hne : r ≠ s) :
    e.lower d r ≠ e.lower d s ∧ e.lower d r ≠ e.upper d s ∧
      e.upper d r ≠ e.lower d s ∧ e.upper d r ≠ e.upper d s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    intro h
    apply hne
    have h' := congrArg e.pairIndex h
    simpa only [pairIndex_lower, pairIndex_upper] using h'

theorem height_lower (d : WireData w) (r : Fin k) :
    (d.defaultPlan e.pairIndex).heights (e.lower d r) = d.H + 4 * w + 8 + 4 * r.val + 4 := by
  simp only [WireData.defaultPlan, WireData.pairedHeight, pairIndex_lower]

theorem height_upper (d : WireData w) (r : Fin k) :
    (d.defaultPlan e.pairIndex).heights (e.upper d r) = d.H + 4 * w + 8 + 4 * r.val + 4 := by
  simp only [WireData.defaultPlan, WireData.pairedHeight, pairIndex_upper]

theorem same_height (d : WireData w) (r : Fin k) :
    (d.defaultPlan e.pairIndex).heights (e.lower d r) = (d.defaultPlan e.pairIndex).heights (e.upper d r) := by
  rw [e.height_lower, e.height_upper]

theorem height_gap (d : WireData w) (r s : Fin k) (hne : r ≠ s) :
    (d.defaultPlan e.pairIndex).heights (e.lower d r) + 4 ≤ (d.defaultPlan e.pairIndex).heights (e.lower d s) ∨
      (d.defaultPlan e.pairIndex).heights (e.lower d s) + 4 ≤ (d.defaultPlan e.pairIndex).heights (e.lower d r) := by
  rw [e.height_lower, e.height_lower]
  have hval : r.val ≠ s.val := fun h => hne (Fin.ext h)
  omega

theorem ordered_capParity (d : WireData w) (r : Fin k) (L : ℕ)
    (hL : CapParity (d.armCaps (e.first r)) (d.armCaps (e.second r)) L) :
    CapParity (d.armCaps (e.lower d r)) (d.armCaps (e.upper d r)) L := by
  by_cases h : d.slabs (e.first r) < d.slabs (e.second r)
  · simpa only [lower, upper, if_pos h] using hL
  · simpa only [lower, upper, if_neg h] using (capParity_swap _ _ L).1 hL

end Pairing

/-- Simultaneous routing of every pairing of the open-arm starts, at every
prescribed length above Lstar with its cap parity. Every returned object is
an actual self-avoiding lattice Fold; no route-existence hypothesis is used. -/
theorem paired_arm_routes {w k : ℕ} (d : WireData w) (e : Pairing w k)
    (m : ℕ) (hH : d.H = 20 * m + 21)
    (hxlow : ∀ i, -d.H ≤ wireBaseXs d.quadrants d.bases i)
    (L : Fin k → ℕ) (hL : ∀ r, uniformLinkerLength m w ≤ L r)
    (hparity : ∀ r, CapParity (d.armCaps (e.first r)) (d.armCaps (e.second r)) (L r)) :
    ∃ f : ∀ r : Fin k, Fold tetrahedralLattice (L r),
      (∀ r i, i.val = 0 → (f r).pos i = d.armCaps (e.lower d r)) ∧
      (∀ r i, i.val + 1 = L r → (f r).pos i = d.armCaps (e.upper d r)) ∧
      (∀ r s, r ≠ s → Disjoint (Set.range (f r).pos) (Set.range (f s).pos)) := by
  let p := d.defaultPlan e.pairIndex
  have hex (r : Fin k) : Nonempty (ExactPairRoute p (e.lower d r) (e.upper d r) (L r)) := by
    apply d.uniform_exactPairRoute_exists e.pairIndex e.card_eq m hH _ _
      (e.lower_ne_upper d r) (e.slab_order d r) _ hxlow (L r) (hL r) (e.ordered_capParity d r (L r) (hparity r))
    simp only [Pairing.pairIndex_lower, Pairing.pairIndex_upper]
  let routes (r : Fin k) := Classical.choice (hex r)
  let f (r : Fin k) := (routes r).fold (e.lower_ne_upper d r)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro r i hi
    exact (routes r).first (e.lower_ne_upper d r) i hi
  · intro r i hi
    exact (routes r).last (e.lower_ne_upper d r) i hi
  · intro r s hrs
    have he := e.endpoints_ne d r s hrs
    exact (routes r).disjoint (routes s) (e.lower_ne_upper d r) (e.lower_ne_upper d s)
      he.1 he.2.1 he.2.2.1 he.2.2.2 (e.same_height d r) (e.same_height d s) (e.height_gap d r s hrs)

end ProteinFolding.Tetrahedral.FarField
