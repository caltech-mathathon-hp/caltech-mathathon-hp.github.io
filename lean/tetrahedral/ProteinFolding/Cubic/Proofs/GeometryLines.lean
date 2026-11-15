import ProteinFolding.Cubic.Proofs.GeometryBasics
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting cubic-lattice edges by coordinate lines

Every occupied coordinate line has an uppermost point, which cannot have an
occupied successor on that line. This gives the line-counting part of Fact 3.1.
-/

namespace ProteinFolding.CubicGeometry

open scoped BigOperators

def stepPlus (k : Fin 3) (p : Site) : Site :=
  Function.update p k (p k + 1)

def lineKey (k : Fin 3) (p : Site) : Site := Function.update p k 0

theorem lineKey_stepPlus (k : Fin 3) (p : Site) :
    lineKey k (stepPlus k p) = lineKey k p := by
  simp [lineKey, stepPlus, Function.update_idem]

def positiveEdges (s : Finset Site) (k : Fin 3) : Finset Site :=
  s.filter (fun p => stepPlus k p ∈ s)

def upperBoundary (s : Finset Site) (k : Fin 3) : Finset Site :=
  s.filter (fun p => stepPlus k p ∉ s)

theorem lineKeys_upperBoundary (s : Finset Site) (k : Fin 3) :
    (upperBoundary s k).image (lineKey k) = s.image (lineKey k) := by
  classical
  apply Finset.Subset.antisymm
  · intro key hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp hp).1
  · intro key hkey
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hkey
    let fiber := s.filter (fun q => lineKey k q = lineKey k p)
    have hne : fiber.Nonempty := ⟨p, by simp [fiber, hp]⟩
    obtain ⟨q, hq, hmax⟩ := Finset.exists_max_image fiber (fun q => q k) hne
    obtain ⟨hqs, hkey⟩ := Finset.mem_filter.mp hq
    have hb : stepPlus k q ∉ s := by
      intro hsucc
      have hmem : stepPlus k q ∈ fiber := by
        exact Finset.mem_filter.mpr ⟨hsucc, (lineKey_stepPlus k q).trans hkey⟩
      have hm := hmax _ hmem
      simp [stepPlus] at hm
    exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hqs, hb⟩, hkey⟩

theorem positiveEdges_add_lineKeys_le (s : Finset Site) (k : Fin 3) :
    (positiveEdges s k).card + (s.image (lineKey k)).card ≤ s.card := by
  have hboundary : (s.image (lineKey k)).card ≤ (upperBoundary s k).card := by
    rw [← lineKeys_upperBoundary s k]
    exact Finset.card_image_le
  have hpart := Finset.filter_card_add_filter_neg_card_eq_card
    (s := s) (fun p => stepPlus k p ∈ s)
  change (positiveEdges s k).card + (upperBoundary s k).card = s.card at hpart
  omega

def positiveEdgeCount (s : Finset Site) : ℕ := ∑ k : Fin 3, (positiveEdges s k).card

theorem positiveEdgeCount_add_lines_le (s : Finset Site) :
    positiveEdgeCount s + (∑ k : Fin 3, (s.image (lineKey k)).card) ≤ 3 * s.card := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun k _ => positiveEdges_add_lineKeys_le s k)
  simpa [positiveEdgeCount, Finset.sum_add_distrib] using h

end ProteinFolding.CubicGeometry
