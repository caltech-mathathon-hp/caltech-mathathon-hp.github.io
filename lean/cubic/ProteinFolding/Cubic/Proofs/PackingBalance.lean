import ProteinFolding.Cubic.Proofs.PackingScaling

/-! Completing ordinary bins with unit slack items before doubling. This
gives a total mathematical reduction from ordinary unary BIN PACKING to
MODIFIED BIN PACKING, including malformed raw inputs. Its output has polynomial
unary length; the explicit TM2 implementation remains a separate obligation. -/

namespace ProteinFolding.Packing

def balance (I : Instance) : Instance :=
  ⟨I.sizes ++ List.replicate (I.capacity * I.bins - I.sizes.sum) 1, I.capacity, I.bins⟩

def toModified (I : Instance) : Instance := scale 2 (balance I)

def fillPart (B : ℕ) (p : List ℕ) : List ℕ := p ++ List.replicate (B - p.sum) 1

def fillParts (B : ℕ) (parts : List (List ℕ)) : List (List ℕ) := parts.map (fillPart B)

def deficit (B : ℕ) (parts : List (List ℕ)) : ℕ := (parts.map (fun p => B - p.sum)).sum

theorem sum_sublist_le {xs ys : List ℕ} (h : xs.Sublist ys) : xs.sum ≤ ys.sum := by
  induction h with
  | slnil => rfl
  | cons a h ih => simp only [List.sum_cons]; omega
  | cons₂ a h ih => simp only [List.sum_cons]; omega

/-- A sublist of all packed items can retain the same bins, by deleting
unselected occurrences inside each bin. -/
theorem subpacking (B : ℕ) (parts : List (List ℕ)) (xs : List ℕ)
    (hsub : xs.Sublist parts.flatten) (hfit : ∀ p ∈ parts, p.sum ≤ B) :
    ∃ qs : List (List ℕ), qs.length = parts.length ∧ xs = qs.flatten ∧
      ∀ q ∈ qs, q.sum ≤ B := by
  induction parts generalizing xs with
  | nil =>
    have hx : xs = [] := List.sublist_nil.mp hsub
    subst xs
    exact ⟨[], rfl, rfl, by simp⟩
  | cons p parts ih =>
    obtain ⟨a, b, hxs, ha, hb⟩ := List.sublist_append_iff.mp hsub
    obtain ⟨qs, hlen, hflat, hqs⟩ := ih b hb (fun q hq => hfit q (by simp [hq]))
    refine ⟨a :: qs, by simp [hlen], ?_, ?_⟩
    · simpa [hflat] using hxs
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact (sum_sublist_le ha).trans (hfit p (by simp))
      · exact hqs q hq

theorem deficit_sum (B : ℕ) (parts : List (List ℕ))
    (hfit : ∀ p ∈ parts, p.sum ≤ B) :
    deficit B parts + parts.flatten.sum = B * parts.length := by
  induction parts with
  | nil => simp [deficit]
  | cons p parts ih =>
    have hp := hfit p (by simp)
    have hp' : B - p.sum + p.sum = B := Nat.sub_add_cancel hp
    have ht := ih (fun q hq => hfit q (by simp [hq]))
    simp only [deficit, List.map_cons, List.sum_cons, List.flatten_cons,
      List.sum_append, List.length_cons] at *
    nlinarith

theorem fillParts_perm (B : ℕ) (parts : List (List ℕ)) :
    (fillParts B parts).flatten.Perm
      (parts.flatten ++ List.replicate (deficit B parts) 1) := by
  induction parts with
  | nil => simp [fillParts, deficit]
  | cons p parts ih =>
    change (fillPart B p ++ (fillParts B parts).flatten).Perm _
    apply (ih.append_left (fillPart B p)).trans
    change ((p ++ List.replicate (B - p.sum) 1) ++
      (parts.flatten ++ List.replicate (deficit B parts) 1)).Perm _
    have hswap := (List.perm_append_comm_assoc (List.replicate (B - p.sum) 1)
      parts.flatten (List.replicate (deficit B parts) 1)).append_left p
    simpa [deficit, List.append_assoc, List.replicate_append_replicate] using hswap

theorem fillParts_exact (B : ℕ) (parts : List (List ℕ))
    (hfit : ∀ p ∈ parts, p.sum ≤ B) : ∀ p ∈ fillParts B parts, p.sum = B := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have h := hfit q hq
  simp only [fillPart, List.sum_append, List.sum_replicate]
  simp only [smul_eq_mul, mul_one]
  omega

theorem wellFormed_balance_iff (I : Instance) : WellFormed (balance I) ↔ WellFormed I := by
  constructor
  · rintro ⟨hB, hK, hs⟩
    exact ⟨hB, hK, fun a ha => hs a (List.mem_append_left _ ha)⟩
  · rintro ⟨hB, hK, hs⟩
    refine ⟨hB, hK, ?_⟩
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hs a ha
    · have he : a = 1 := (List.mem_replicate.mp ha).2
      omega

theorem balance_saturated_iff (I : Instance) :
    SaturatedBinAccepts (balance I) ↔ BinAccepts I := by
  constructor
  · rintro ⟨⟨hw, parts, hp⟩, _⟩
    refine ⟨(wellFormed_balance_iff I).mp hw, ?_⟩
    have hprefix : I.sizes.Sublist (balance I).sizes := List.sublist_append_left _ _
    obtain ⟨xs, hperm, hsub⟩ := List.exists_perm_sublist hprefix hp.2.1
    obtain ⟨qs, hlen, hflat, hfit⟩ := subpacking I.capacity parts xs hsub hp.2.2
    refine ⟨qs, hlen.trans hp.1, ?_, hfit⟩
    rw [← hflat]
    exact hperm.symm
  · rintro ⟨hw, parts, hp⟩
    have htotal : I.sizes.sum ≤ I.capacity * I.bins := by
      rw [hp.2.1.sum_eq, ← hp.1]
      exact bin_load_bound I.capacity parts hp.2.2
    have hd : deficit I.capacity parts = I.capacity * I.bins - I.sizes.sum := by
      have he := deficit_sum I.capacity parts hp.2.2
      rw [← hp.2.1.sum_eq, hp.1] at he
      omega
    have hfill := fillParts_perm I.capacity parts
    rw [hd] at hfill
    have hperm : (balance I).sizes.Perm (fillParts I.capacity parts).flatten :=
      (hp.2.1.append_right _).trans hfill.symm
    refine ⟨⟨(wellFormed_balance_iff I).mpr hw, fillParts I.capacity parts,
      ?_, hperm, ?_⟩, ?_⟩
    · simpa [fillParts] using hp.1
    · exact fun p hp' => (fillParts_exact I.capacity parts hp.2.2 p hp').le
    · simp only [balance, List.sum_append, List.sum_replicate, smul_eq_mul, mul_one]
      omega

/-- The ordinary-to-modified packing equivalence, with every original
occurrence retained and exactly the missing capacity filled by size-two items. -/
theorem toModified_correct (I : Instance) : BinAccepts I ↔ ModifiedAccepts (toModified I) := by
  rw [toModified, ← doubling_iff_modified, balance_saturated_iff]

/-- Completing unused capacity adds at most B*K unit items. Measured in the
actual unary encodings, the entire reduction output has a quadratic bound. -/
theorem toModified_encoding_length (I : Instance) :
    (instanceEncoding.encode (toModified I)).length ≤
      3 * (instanceEncoding.encode I).length ^ 2 + 2 * (instanceEncoding.encode I).length := by
  have hB : I.capacity ≤ (instanceEncoding.encode I).length := by
    rw [instanceEncoding_length]
    omega
  have hK : I.bins ≤ (instanceEncoding.encode I).length := by
    rw [instanceEncoding_length]
    omega
  have hd : I.capacity * I.bins - I.sizes.sum ≤ I.capacity * I.bins := Nat.sub_le _ _
  have hprod : I.capacity * I.bins ≤ (instanceEncoding.encode I).length ^ 2 := by
    nlinarith
  rw [instanceEncoding_length]
  simp only [toModified, scale, balance, sum_scale, List.sum_append,
    List.sum_replicate, smul_eq_mul, mul_one, List.length_map, List.length_append,
    List.length_replicate]
  rw [instanceEncoding_length] at hprod ⊢
  nlinarith

end ProteinFolding.Packing
