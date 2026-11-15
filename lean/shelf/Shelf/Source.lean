import ProteinFolding.Cubic.Proofs.PackingScaling
import ProteinFolding.Cubic.Proofs.PackingPadding

/-!
# The source problem: EXACT PACKING

Section 2.1 of our write-up: given positive integers
`a₁, …, a_k` and `m`, `B` with `∑ aᵢ = m · B`, can the items be split into `m`
classes whose sizes each sum to `B`?

We reuse the instance type `Packing.Instance` and the predicate `Packing.Exact` of
the team's statement library. That library's source problem `Packing.ModifiedAccepts`
is ours plus the requirement that every size be even (`modifiedAccepts_iff`).

Section 3 of our write-up normalises an instance before building the string: all
sizes and the capacity are multiplied by 6, and if the number of bins is even one
item of size `B` is added together with one more bin. Both steps are in the team's
library (`Packing.scale`, `Packing.pad`), with the proofs that they do not change
the answer. This file puts them together: `normalised_normalise` and
`exists_exact_normalise_iff`.
-/

namespace ProteinFolding.Shelf

open ProteinFolding

/-- EXACT PACKING. `I.sizes` are the item sizes `a₁, …, a_k`, `I.bins` is `m` and
`I.capacity` is `B`. All of them must be positive; an input that breaks this rule
is a no-instance. -/
def ExactAccepts (I : Packing.Instance) : Prop :=
  Packing.WellFormed I ∧ ∃ parts, Packing.Exact I parts

/-- If every one of the bins has load exactly `B`, the loads add up to `B` times
the number of bins. -/
theorem sum_flatten_of_sum_eq {B : ℕ} :
    ∀ parts : List (List ℕ), (∀ p ∈ parts, p.sum = B) → parts.flatten.sum = B * parts.length
  | [], _ => by simp
  | p :: ps, h => by
      have hp := h p (by simp)
      have ih := sum_flatten_of_sum_eq ps (fun q hq => h q (by simp [hq]))
      simp only [List.flatten_cons, List.sum_append, List.length_cons, hp, ih]
      ring

/-- If an exact packing exists, then `∑ aᵢ = m · B`. -/
theorem sum_eq_of_exact {I : Packing.Instance} {parts : List (List ℕ)}
    (h : Packing.Exact I parts) : I.sizes.sum = I.capacity * I.bins := by
  rw [h.2.1.sum_eq, sum_flatten_of_sum_eq parts h.2.2, h.1]

/-- The source problem of the team's library is EXACT PACKING restricted to even
sizes. So our source problem contains theirs, as our write-up says. -/
theorem modifiedAccepts_iff (I : Packing.Instance) :
    Packing.ModifiedAccepts I ↔ (∀ s ∈ I.sizes, Even s) ∧ ExactAccepts I := by
  constructor
  · rintro ⟨hw, he, _, hp⟩
    exact ⟨he, hw, hp⟩
  · rintro ⟨he, hw, parts, hp⟩
    exact ⟨hw, he, sum_eq_of_exact hp, parts, hp⟩

/-- What the reduction checks before it builds the string: the numbers are
positive and `∑ aᵢ = m · B`, that is, the input is an instance in the sense of
our write-up. An input that fails the check has no exact packing, and is sent to a
fixed no-instance (`noInstance`). -/
def Guard (I : Packing.Instance) : Prop :=
  Packing.WellFormed I ∧ I.sizes.sum = I.capacity * I.bins

instance : DecidablePred Guard := fun I => by
  unfold Guard Packing.WellFormed
  exact inferInstance

theorem guard_of_exactAccepts {I : Packing.Instance} (h : ExactAccepts I) : Guard I := by
  obtain ⟨hw, parts, hp⟩ := h
  exact ⟨hw, sum_eq_of_exact hp⟩

/-- If the number of bins is even, add one item that fills a bin on its own, and
one bin for it (`Packing.pad`). Afterwards the number of bins is odd. -/
def padOdd (I : Packing.Instance) : Packing.Instance :=
  if Even I.bins then Packing.pad I else I

/-- The normalisation of Section 3: multiply every size and the capacity by 6
(`Packing.scale 6`), then make the number of bins odd. -/
def normalise (I : Packing.Instance) : Packing.Instance :=
  padOdd (Packing.scale 6 I)

/-- A normalised instance: "6 divides `B` and every `aᵢ`, and `m` is odd", with
positive numbers and `∑ aᵢ = m · B`. These are the standing assumptions of
Sections 3 to 5 of our write-up. -/
structure Normalised (J : Packing.Instance) : Prop where
  capacity_pos : 0 < J.capacity
  six_dvd_capacity : 6 ∣ J.capacity
  bins_odd : Odd J.bins
  size_pos : ∀ s ∈ J.sizes, 0 < s
  six_dvd_size : ∀ s ∈ J.sizes, 6 ∣ s
  sum_eq : J.sizes.sum = J.capacity * J.bins

/-- The normalisation produces a normalised instance. -/
theorem normalised_normalise {I : Packing.Instance} (hg : Guard I) :
    Normalised (normalise I) := by
  obtain ⟨⟨hc, -, hs⟩, hsum⟩ := hg
  have hsize : ∀ s ∈ (Packing.scale 6 I).sizes, 0 < s ∧ 6 ∣ s := by
    intro s hs'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs'
    exact ⟨Nat.mul_pos (by norm_num) (hs t ht), dvd_mul_right 6 t⟩
  have hsum' : (Packing.scale 6 I).sizes.sum =
      (Packing.scale 6 I).capacity * (Packing.scale 6 I).bins := by
    show (I.sizes.map (6 * ·)).sum = 6 * I.capacity * I.bins
    rw [Packing.sum_scale, hsum, Nat.mul_assoc]
  have hcap : 0 < (Packing.scale 6 I).capacity := Nat.mul_pos (by norm_num) hc
  have hdvd : 6 ∣ (Packing.scale 6 I).capacity := dvd_mul_right 6 I.capacity
  unfold normalise padOdd
  split_ifs with h
  · refine ⟨hcap, hdvd, h.add_one, ?_, ?_, ?_⟩
    · intro s hs'
      rcases List.mem_cons.mp hs' with rfl | hs'
      · exact hcap
      · exact (hsize s hs').1
    · intro s hs'
      rcases List.mem_cons.mp hs' with rfl | hs'
      · exact hdvd
      · exact (hsize s hs').2
    · show ((Packing.scale 6 I).capacity :: (Packing.scale 6 I).sizes).sum =
        (Packing.scale 6 I).capacity * ((Packing.scale 6 I).bins + 1)
      rw [List.sum_cons, hsum']
      ring
  · exact ⟨hcap, hdvd, Nat.not_even_iff_odd.mp h, fun s hs' => (hsize s hs').1,
      fun s hs' => (hsize s hs').2, hsum'⟩

/-- "Neither step changes the answer": the normalised instance has an exact
packing if and only if the original one has. -/
theorem exists_exact_normalise_iff {I : Packing.Instance} (hw : Packing.WellFormed I) :
    (∃ parts, Packing.Exact (normalise I) parts) ↔ ∃ parts, Packing.Exact I parts := by
  obtain ⟨hc, -, hs⟩ := hw
  have hscale := Packing.exists_exact_scale_iff 6 (by norm_num) I
  unfold normalise padOdd
  split_ifs with h
  · rw [Packing.exists_exact_pad_iff (Packing.scale 6 I) (Nat.mul_pos (by norm_num) hc)]
    · exact hscale
    · intro a ha
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
      exact Nat.mul_pos (by norm_num) (hs t ht)
  · exact hscale

end ProteinFolding.Shelf
