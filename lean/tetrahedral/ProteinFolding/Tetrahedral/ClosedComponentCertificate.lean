import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Image

/-! A finite connected neighbour-closed set is exactly an ambient component.
Complete local neighbour stars transport such certificates; neither ambient
graph is assumed finite. This supports local segment certificates. -/

namespace ProteinFolding.Tetrahedral

open SimpleGraph

variable {V W : Type} [DecidableEq V] [DecidableEq W]

theorem finset_closed_under_reachable (G : SimpleGraph V) (A : Finset V)
    (hclosed : ∀ x ∈ A, ∀ y, G.Adj x y → y ∈ A)
    {v w : V} (hv : v ∈ A) (hreach : G.Reachable v w) : w ∈ A := by
  obtain ⟨p⟩ := hreach
  induction p with
  | nil => exact hv
  | cons hadj p ih => exact ih (hclosed _ hv _ hadj)

theorem finset_component_iff (G : SimpleGraph V) (A : Finset V) (v : V)
    (hv : v ∈ A) (hclosed : ∀ x ∈ A, ∀ y, G.Adj x y → y ∈ A)
    (hconnected : ∀ w ∈ A, G.Reachable v w) (w : V) :
    w ∈ A ↔ G.Reachable v w :=
  ⟨hconnected w, finset_closed_under_reachable G A hclosed hv⟩

theorem reachable_map_on_closed_finset (G : SimpleGraph V) (H : SimpleGraph W)
    (A : Finset V) (f : V → W)
    (hclosed : ∀ x ∈ A, ∀ y, G.Adj x y → y ∈ A)
    (hmap : ∀ x ∈ A, ∀ y, G.Adj x y → H.Adj (f x) (f y))
    {v w : V} (hv : v ∈ A) (hreach : G.Reachable v w) : H.Reachable (f v) (f w) := by
  obtain ⟨p⟩ := hreach
  induction p with
  | nil => exact Reachable.refl _
  | cons hadj p ih => exact (hmap _ hv _ hadj).reachable.trans (ih (hclosed _ hv _ hadj))

theorem finset_image_component_iff_of_complete_stars (G : SimpleGraph V) (H : SimpleGraph W)
    (A : Finset V) (v : V) (f : V → W)
    (hv : v ∈ A) (hclosed : ∀ x ∈ A, ∀ y, G.Adj x y → y ∈ A)
    (hconnected : ∀ w ∈ A, G.Reachable v w)
    (hmap : ∀ x ∈ A, ∀ y, G.Adj x y → H.Adj (f x) (f y))
    (hcomplete : ∀ x ∈ A, ∀ z, H.Adj (f x) z → ∃ y, G.Adj x y ∧ f y = z)
    (z : W) : z ∈ A.image f ↔ H.Reachable (f v) z := by
  apply finset_component_iff H (A.image f) (f v)
  · exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
  · intro x hx y hadj
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, huw, hw⟩ := hcomplete u hu y hadj
    exact Finset.mem_image.mpr ⟨w, hclosed u hu w huw, hw⟩
  · intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    exact reachable_map_on_closed_finset G H A f hclosed hmap hv (hconnected u hu)

end ProteinFolding.Tetrahedral
