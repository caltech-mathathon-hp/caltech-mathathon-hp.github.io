import ProteinFolding.Cubic.Proofs.PackingSources

/-! Adding one full-capacity item adds exactly one occupied bin. This lets a
geometric reduction require at least two bins without changing positive-item
packability, including original instances with a single bin. -/

namespace ProteinFolding.Packing

def pad (I : Instance) : Instance :=
  ⟨I.capacity :: I.sizes, I.capacity, I.bins + 1⟩

theorem mem_le_sum {a : ℕ} {xs : List ℕ} (h : a ∈ xs) : a ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons b xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have ht := ih h
      simp only [List.sum_cons]
      omega

theorem singleton_of_full_item {B : ℕ} {p : List ℕ}
    (hpos : ∀ a ∈ p, 0 < a) (hmem : B ∈ p) (hsum : p.sum = B) : p = [B] := by
  cases p with
  | nil => simp at hmem
  | cons a p =>
    rcases List.mem_cons.mp hmem with he | hmem
    · subst a
      have hz : p.sum = 0 := by simpa using hsum
      have hp : p = [] := by
        cases p with
        | nil => rfl
        | cons b p =>
          have hb := hpos b (by simp)
          simp only [List.sum_cons] at hz
          omega
      simp [hp]
    · have hB := mem_le_sum hmem
      have ha := hpos a (by simp)
      simp only [List.sum_cons] at hsum
      omega

/-- A full-capacity new item must occupy a singleton bin because every item
is positive. Deleting that bin recovers an exact packing of the original. -/
theorem exists_exact_pad_iff (I : Instance) (hB : 0 < I.capacity)
    (hs : ∀ a ∈ I.sizes, 0 < a) :
    (∃ parts, Exact (pad I) parts) ↔ ∃ parts, Exact I parts := by
  constructor
  · rintro ⟨parts, hp⟩
    have hmem : I.capacity ∈ parts.flatten := hp.2.1.mem_iff.mp (by simp [pad])
    obtain ⟨p, hpp, hBp⟩ := List.mem_flatten.mp hmem
    have hpos : ∀ a ∈ p, 0 < a := by
      intro a ha
      have hsource : a ∈ (pad I).sizes := hp.2.1.mem_iff.mpr (List.mem_flatten.mpr ⟨p, hpp, ha⟩)
      rcases List.mem_cons.mp hsource with rfl | ha
      · exact hB
      · exact hs a ha
    have he : p = [I.capacity] := singleton_of_full_item hpos hBp (hp.2.2 p hpp)
    subst p
    refine ⟨parts.erase [I.capacity], ?_, ?_, ?_⟩
    · rw [List.length_erase_of_mem hpp, hp.1]
      simp [pad]
    · have hperm := hp.2.1.trans (List.perm_cons_erase hpp).flatten
      change (I.capacity :: I.sizes).Perm
        (I.capacity :: (parts.erase [I.capacity]).flatten) at hperm
      exact hperm.cons_inv
    · intro p hp'
      exact hp.2.2 p (List.mem_of_mem_erase hp')
  · rintro ⟨parts, hp⟩
    refine ⟨[I.capacity] :: parts, ?_, ?_, ?_⟩
    · simpa [pad] using congrArg Nat.succ hp.1
    · simpa [pad] using hp.2.1.cons I.capacity
    · intro p hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · simp [pad]
      · exact hp.2.2 p hmem

theorem pad_total (I : Instance) (ht : I.sizes.sum = I.capacity * I.bins) :
    (pad I).sizes.sum = (pad I).capacity * (pad I).bins := by
  simp only [pad, List.sum_cons, ht, Nat.mul_add, Nat.mul_one]
  omega

theorem pad_encoding_length (I : Instance) :
    (instanceEncoding.encode (pad I)).length =
      (instanceEncoding.encode I).length + I.capacity + 2 := by
  simp only [instanceEncoding_length, pad, List.sum_cons, List.length_cons]
  omega

end ProteinFolding.Packing
