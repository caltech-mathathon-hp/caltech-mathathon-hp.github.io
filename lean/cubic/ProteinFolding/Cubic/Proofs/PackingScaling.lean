import ProteinFolding.Cubic.Proofs.PackingSources
import Mathlib.Tactic.Ring

/-! Exact packing is invariant under a positive common scale. Doubling a
saturated ordinary packing instance yields the paper's positive-even exact
packing source. These are mathematical reduction equivalences; a TM2 runtime
witness is a separate obligation. -/

namespace ProteinFolding.Packing

def scale (c : ℕ) (I : Instance) : Instance :=
  ⟨I.sizes.map (c * ·), c * I.capacity, I.bins⟩

def scaleParts (c : ℕ) (parts : List (List ℕ)) : List (List ℕ) :=
  parts.map (List.map (c * ·))

theorem sum_scale (c : ℕ) (xs : List ℕ) : (xs.map (c * ·)).sum = c * xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.mul_add]

theorem wellFormed_scale_iff (c : ℕ) (hc : 0 < c) (I : Instance) :
    WellFormed (scale c I) ↔ WellFormed I := by
  constructor
  · rintro ⟨hB, hK, hs⟩
    refine ⟨by dsimp [scale] at hB; nlinarith, hK, ?_⟩
    intro a ha
    have h := hs (c * a) (List.mem_map.mpr ⟨a, ha, rfl⟩)
    nlinarith
  · rintro ⟨hB, hK, hs⟩
    refine ⟨Nat.mul_pos hc hB, hK, ?_⟩
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact Nat.mul_pos hc (hs b hb)

theorem exact_scale {I : Instance} {parts : List (List ℕ)} (c : ℕ)
    (h : Exact I parts) : Exact (scale c I) (scaleParts c parts) := by
  refine ⟨by simpa [scaleParts, scale] using h.1, ?_, ?_⟩
  · simpa [scale, scaleParts, List.map_flatten] using h.2.1.map (c * ·)
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    simpa [scale, sum_scale] using congrArg (c * ·) (h.2.2 q hq)

theorem exact_unscale {I : Instance} {parts : List (List ℕ)} (c : ℕ) (hc : 0 < c)
    (h : Exact (scale c I) parts) : Exact I (parts.map (List.map (· / c))) := by
  have hdiv : ∀ p ∈ parts, ∀ a ∈ p, c ∣ a := by
    intro p hp a ha
    have hm : a ∈ (scale c I).sizes := h.2.1.mem_iff.mpr (List.mem_flatten.mpr ⟨p, hp, ha⟩)
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hm
    exact dvd_mul_right c b
  refine ⟨by simpa using h.1, ?_, ?_⟩
  · have hp := h.2.1.map (· / c)
    have hi : (I.sizes.map (c * ·)).map (· / c) = I.sizes := by
      simp [List.map_map, Function.comp_def, Nat.mul_div_cancel_left _ hc]
    simpa only [scale, hi, List.map_flatten] using hp
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have he : ((q.map (· / c)).map (c * ·)) = q := by
      rw [List.map_map]
      exact (List.map_congr_left (fun a ha => Nat.mul_div_cancel' (hdiv q hq a ha))).trans (List.map_id _)
    have hs := sum_scale c (q.map (· / c))
    rw [he, h.2.2 q hq] at hs
    exact Nat.eq_of_mul_eq_mul_left hc hs.symm

theorem exists_exact_scale_iff (c : ℕ) (hc : 0 < c) (I : Instance) :
    (∃ parts, Exact (scale c I) parts) ↔ ∃ parts, Exact I parts := by
  constructor
  · rintro ⟨parts, h⟩
    exact ⟨_, exact_unscale c hc h⟩
  · rintro ⟨parts, h⟩
    exact ⟨_, exact_scale c h⟩

/-- Doubling does not change exact packability and makes every item even.
The source is the saturated restriction of ordinary BIN PACKING. -/
theorem doubling_iff_modified (I : Instance) :
    SaturatedBinAccepts I ↔ ModifiedAccepts (scale 2 I) := by
  rw [saturated_iff_exact]
  constructor
  · rintro ⟨hw, ht, parts, hp⟩
    refine ⟨(wellFormed_scale_iff 2 (by decide) I).mpr hw, ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
      exact ⟨b, by omega⟩
    · dsimp [scale]
      rw [sum_scale, ht]
      ring
    · exact ⟨_, exact_scale 2 hp⟩
  · rintro ⟨hw, _, ht, parts, hp⟩
    refine ⟨(wellFormed_scale_iff 2 (by decide) I).mp hw, ?_, ?_⟩
    · dsimp [scale] at ht
      rw [sum_scale] at ht
      nlinarith
    · exact (exists_exact_scale_iff 2 (by decide) I).mp ⟨parts, hp⟩

end ProteinFolding.Packing
