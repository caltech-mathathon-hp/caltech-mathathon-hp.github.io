import ProteinFolding.Cubic.Proofs.GeometryProjection
import Mathlib.Data.Int.Interval

/-! Equality-case interfaces: Cartesian support and gapless integer intervals. -/

namespace ProteinFolding.CubicGeometry

/-- Equality in the three projection counts makes the site triples Cartesian. -/
theorem siteTriple_eq_product_of_projection_equality (s : Finset Site)
    (heq : s.card ^ 2 = (s.image (lineKey 0)).card *
      (s.image (lineKey 1)).card * (s.image (lineKey 2)).card) :
    s.image siteTriple = (s.image (fun q => q 0)) ×ˢ
      ((s.image (fun q => q 1)) ×ˢ (s.image (fun q => q 2))) := by
  classical
  have heqT : (s.image siteTriple).card ^ 2 =
      (LoomisWhitney.xyProjection (s.image siteTriple)).card *
      (LoomisWhitney.xzProjection (s.image siteTriple)).card *
      (LoomisWhitney.yzProjection (s.image siteTriple)).card := by
    rw [Finset.card_image_of_injective _ siteTriple_injective]
    rw [lineKey_card_eq_projection s 0, lineKey_card_eq_projection s 1,
      lineKey_card_eq_projection s 2] at heq
    have h0 : lineProjection 0 = (fun p : Site => (p 1, p 2)) := by
      funext p; simp [lineProjection]
    have h1 : lineProjection 1 = (fun p : Site => (p 0, p 2)) := by
      funext p; simp [lineProjection]
    have h2 : lineProjection 2 = (fun p : Site => (p 0, p 1)) := by
      funext p; simp [lineProjection]
    rw [h0, h1, h2] at heq
    simpa [LoomisWhitney.xyProjection, LoomisWhitney.xzProjection,
      LoomisWhitney.yzProjection, Finset.image_image, Function.comp_def,
      siteTriple, lineProjection, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using heq
  have hprod := LoomisWhitney.equality_is_product (s.image siteTriple) heqT
  simpa only [Finset.image_image, Function.comp_def, siteTriple] using hprod

/-- Equality in the three projection counts makes site membership coordinatewise. -/
theorem mem_iff_coordinate_mem_of_projection_equality (s : Finset Site)
    (heq : s.card ^ 2 = (s.image (lineKey 0)).card *
      (s.image (lineKey 1)).card * (s.image (lineKey 2)).card) (p : Site) :
    p ∈ s ↔ ∀ k : Fin 3, p k ∈ s.image (fun q => q k) := by
  classical
  have hprod' := siteTriple_eq_product_of_projection_equality s heq
  constructor
  · intro hp k
    exact Finset.mem_image_of_mem _ hp
  · intro hp
    have hmem : siteTriple p ∈ s.image siteTriple := by
      rw [hprod']
      exact Finset.mem_product.mpr ⟨hp 0, Finset.mem_product.mpr ⟨hp 1, hp 2⟩⟩
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hmem
    exact siteTriple_injective hqp ▸ hq

/-- A nonempty finite set of integers with exactly one upper boundary point
has no gaps. -/
theorem eq_Icc_of_one_upper_boundary (s : Finset ℤ) (hne : s.Nonempty)
    (hboundary : (s.filter (fun x => x + 1 ∉ s)).card = 1) :
    s = Finset.Icc (s.min' hne) (s.max' hne) := by
  have hmaxmem : s.max' hne ∈ s := s.max'_mem hne
  have hmaxout : s.max' hne + 1 ∉ s := by
    intro hsucc
    have hle := s.le_max' _ hsucc
    omega
  have hmaxboundary : s.max' hne ∈ s.filter (fun x => x + 1 ∉ s) :=
    Finset.mem_filter.mpr ⟨hmaxmem, hmaxout⟩
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hboundary
  have hbmax : s.max' hne = b := by simpa only [hb, Finset.mem_singleton] using hmaxboundary
  have hboundaryeq : s.filter (fun x => x + 1 ∉ s) = {s.max' hne} := by
    simpa only [← hbmax] using hb
  have hclosed : ∀ x ∈ s, x < s.max' hne → x + 1 ∈ s := by
    intro x hx hlt
    by_contra hout
    have hxboundary : x ∈ s.filter (fun x => x + 1 ∉ s) :=
      Finset.mem_filter.mpr ⟨hx, hout⟩
    have heq : x = s.max' hne := by
      simpa only [hboundaryeq, Finset.mem_singleton] using hxboundary
    omega
  have hfill : ∀ (z : ℤ), s.min' hne ≤ z → z ≤ s.max' hne → z ∈ s := by
    intro z hz
    induction z, hz using Int.le_induction with
    | base => intro _; exact s.min'_mem hne
    | succ z hz ih =>
      intro hzm
      exact hclosed z (ih (by omega)) (by omega)
  ext z
  constructor
  · intro hz
    exact Finset.mem_Icc.mpr ⟨s.min'_le _ hz, s.le_max' _ hz⟩
  · intro hz
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hz
    exact hfill z hlo hhi

/-- The same gapless interval, with its cardinality as the half-open length. -/
theorem eq_Ico_min_card_of_one_upper_boundary (s : Finset ℤ) (hne : s.Nonempty)
    (hboundary : (s.filter (fun x => x + 1 ∉ s)).card = 1) :
    s = Finset.Ico (s.min' hne) (s.min' hne + (s.card : ℤ)) := by
  have hIcc := eq_Icc_of_one_upper_boundary s hne hboundary
  have hminmax := s.min'_le_max' hne
  have hcard := Int.card_Icc_of_le (s.min' hne) (s.max' hne)
    (show s.min' hne ≤ s.max' hne + 1 by omega)
  rw [← hIcc] at hcard
  ext z
  have hmem : z ∈ s ↔ s.min' hne ≤ z ∧ z ≤ s.max' hne := by
    conv_lhs => rw [hIcc]
    exact Finset.mem_Icc
  rw [hmem, Finset.mem_Ico]
  omega

end ProteinFolding.CubicGeometry
