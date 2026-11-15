import ProteinFolding.Cubic.Proofs.GeometryLines
import ProteinFolding.Cubic.Proofs.GeometryLoomisWhitney

/-! Applying the product-type Loomis--Whitney inequality to the frozen `Site`. -/

namespace ProteinFolding.CubicGeometry

def siteTriple (p : Site) : ℤ × ℤ × ℤ := (p 0, p 1, p 2)

theorem siteTriple_injective : Function.Injective siteTriple := by
  intro p q h
  have h0 := congrArg (fun t : ℤ × ℤ × ℤ => t.1) h
  have h1 := congrArg (fun t : ℤ × ℤ × ℤ => t.2.1) h
  have h2 := congrArg (fun t : ℤ × ℤ × ℤ => t.2.2) h
  funext k
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk with rfl | rfl | rfl <;> assumption

def lineProjection (k : Fin 3) (p : Site) : ℤ × ℤ :=
  if k = 0 then (p 1, p 2) else if k = 1 then (p 0, p 2) else (p 0, p 1)

def lineEmbed (k : Fin 3) (u : ℤ × ℤ) : Site :=
  if k = 0 then (fun j => if j = 0 then 0 else if j = 1 then u.1 else u.2)
  else if k = 1 then (fun j => if j = 0 then u.1 else if j = 1 then 0 else u.2)
  else (fun j => if j = 0 then u.1 else if j = 1 then u.2 else 0)

theorem lineProjection_lineEmbed (k : Fin 3) (u : ℤ × ℤ) :
    lineProjection k (lineEmbed k u) = u := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk with rfl | rfl | rfl <;> simp [lineProjection, lineEmbed]

theorem lineEmbed_lineProjection (k : Fin 3) (p : Site) :
    lineEmbed k (lineProjection k p) = lineKey k p := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk with rfl | rfl | rfl <;> funext j <;>
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  all_goals rcases hj with rfl | rfl | rfl <;> simp [lineProjection, lineEmbed, lineKey]

theorem lineEmbed_injective (k : Fin 3) : Function.Injective (lineEmbed k) := by
  intro u v h
  have he := congrArg (lineProjection k) h
  simpa only [lineProjection_lineEmbed] using he

theorem lineKey_card_eq_projection (s : Finset Site) (k : Fin 3) :
    (s.image (lineKey k)).card = (s.image (lineProjection k)).card := by
  classical
  have he : (s.image (lineProjection k)).image (lineEmbed k) = s.image (lineKey k) := by
    simp only [Finset.image_image, Function.comp_def, lineEmbed_lineProjection]
  rw [← he, Finset.card_image_of_injective _ (lineEmbed_injective k)]

theorem card_sq_le_lineKey_product (s : Finset Site) :
    s.card ^ 2 ≤ (s.image (lineKey 0)).card *
      (s.image (lineKey 1)).card * (s.image (lineKey 2)).card := by
  classical
  have h := LoomisWhitney.card_sq_le_projection_product (s.image siteTriple)
  rw [Finset.card_image_of_injective _ siteTriple_injective] at h
  rw [lineKey_card_eq_projection s 0, lineKey_card_eq_projection s 1,
    lineKey_card_eq_projection s 2]
  change s.card ^ 2 ≤ (s.image (fun p => (p 1, p 2))).card *
    (s.image (fun p => (p 0, p 2))).card * (s.image (fun p => (p 0, p 1))).card
  simpa [LoomisWhitney.xyProjection, LoomisWhitney.xzProjection,
    LoomisWhitney.yzProjection, Finset.image_image, Function.comp_def,
    siteTriple, lineProjection, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

end ProteinFolding.CubicGeometry
