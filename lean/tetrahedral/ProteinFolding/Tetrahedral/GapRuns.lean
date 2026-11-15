import ProteinFolding.Tetrahedral.GapGeometry
import Mathlib.Data.Finset.Max

/-!
# Finite occupied runs along the gap zigzags

A run start has an unoccupied predecessor; a run end has an unoccupied
successor. The orientations strictly increase y, so finite occupied chains
cannot contain cycles. End counting and the adjacent-layer imbalance are
proved directly using the inverse predecessor/successor maps.
-/

namespace ProteinFolding.Tetrahedral

def finiteLayer (S : Finset Site) (k : ℤ) : Finset Site :=
  S.filter (fun p => p.val 0 = k)

def gapSupport (S : Finset Site) (k : ℤ) : Finset Site := S.filter (InGap k)

def gapRunStarts (S : Finset Site) (k : ℤ) : Finset Site :=
  (gapSupport S k).filter (fun p => gapPrev k p ∉ S)

def gapRunEnds (S : Finset Site) (k : ℤ) : Finset Site :=
  (gapSupport S k).filter (fun p => gapNext k p ∉ S)

/-- Number of finite occupied runs in gap k, oriented by increasing y. -/
def gapRunCount (S : Finset Site) (k : ℤ) : ℕ := (gapRunStarts S k).card

theorem gapRunStarts_card_eq_ends (S : Finset Site) (k : ℤ) :
    (gapRunStarts S k).card = (gapRunEnds S k).card := by
  have hi : ((gapSupport S k).filter (fun p => gapNext k p ∈ S)).card =
      ((gapSupport S k).filter (fun p => gapPrev k p ∈ S)).card := by
    apply Finset.card_bij (fun p _ => gapNext k p)
    · intro p hp
      have h := Finset.mem_filter.mp hp
      have hg := Finset.mem_filter.mp h.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨h.2, gapNext_in_gap hg.2⟩, by simpa using hg.1⟩
    · intro p _ q _ heq
      exact gapNext_injective k heq
    · intro q hq
      have h := Finset.mem_filter.mp hq
      have hg := Finset.mem_filter.mp h.1
      refine ⟨gapPrev k q, ?_, gapNext_prev k q⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨h.2, gapPrev_in_gap hg.2⟩, by simpa using hg.1⟩
  have hn := Finset.filter_card_add_filter_neg_card_eq_card
    (s := gapSupport S k) (p := fun p => gapNext k p ∈ S)
  have hp := Finset.filter_card_add_filter_neg_card_eq_card
    (s := gapSupport S k) (p := fun p => gapPrev k p ∈ S)
  change _ + (gapRunEnds S k).card = _ at hn
  change _ + (gapRunStarts S k).card = _ at hp
  omega

theorem gapPrev_x {S : Finset Site} {k : ℤ} {p : Site} (hp : p ∈ gapSupport S k) :
    (gapPrev k p).val 0 = 2 * k + 1 - p.val 0 := by
  have hx := gapOtherX_in_gap (Finset.mem_filter.mp hp).2
  simpa [gapPrev_val] using hx

/-- Both directions of the layer imbalance bound, in natural-number form. -/
theorem layer_imbalance_bound (S : Finset Site) (k : ℤ) :
    (finiteLayer S k).card ≤ (finiteLayer S (k + 1)).card + gapRunCount S k ∧
    (finiteLayer S (k + 1)).card ≤ (finiteLayer S k).card + gapRunCount S k := by
  have hbound : ∀ a b : ℤ, (a = k ∧ b = k + 1) ∨ (a = k + 1 ∧ b = k) →
      (finiteLayer S a).card ≤ (finiteLayer S b).card + gapRunCount S k := by
    intro a b hab
    let T := finiteLayer S a
    have hgap : ∀ p ∈ T, p ∈ gapSupport S k := by
      intro p hp
      have h := Finset.mem_filter.mp hp
      apply Finset.mem_filter.mpr
      refine ⟨h.1, ?_⟩
      rcases hab with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact Or.inl h.2
      · exact Or.inr h.2
    have hstart : (T.filter (fun p => gapPrev k p ∉ S)).card ≤ gapRunCount S k := by
      apply Finset.card_le_card
      intro p hp
      have h := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hgap p h.1, h.2⟩
    have hother : (T.filter (fun p => gapPrev k p ∈ S)).card ≤ (finiteLayer S b).card := by
      apply Finset.card_le_card_of_injOn (gapPrev k)
      · intro p hp
        have h := Finset.mem_filter.mp hp
        have hx := gapPrev_x (hgap p h.1)
        have ha := (Finset.mem_filter.mp h.1).2
        apply Finset.mem_filter.mpr
        refine ⟨h.2, ?_⟩
        rcases hab with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ <;> omega
      · exact (gapPrev_injective k).injOn
    have hpart := Finset.filter_card_add_filter_neg_card_eq_card
      (s := T) (p := fun p => gapPrev k p ∈ S)
    change _ + _ = (finiteLayer S a).card at hpart
    omega
  exact ⟨hbound k (k + 1) (Or.inl ⟨rfl, rfl⟩),
    hbound (k + 1) k (Or.inr ⟨rfl, rfl⟩)⟩

/-- Every occupied zigzag has an occupied run start: choose its least y. -/
theorem gapChainKeys_eq_startKeys (S : Finset Site) (k : ℤ) :
    (gapSupport S k).image (gapChainKey k) =
      (gapRunStarts S k).image (gapChainKey k) := by
  apply Finset.Subset.antisymm
  · intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    let T := (gapSupport S k).filter (fun q => gapChainKey k q = gapChainKey k p)
    have hT : T.Nonempty := ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩
    obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image T (fun q => q.val 1) hT
    have hf := Finset.mem_filter.mp hq
    have hg := Finset.mem_filter.mp hf.1
    apply Finset.mem_image.mpr
    refine ⟨q, Finset.mem_filter.mpr ⟨hf.1, ?_⟩, hf.2⟩
    intro hprev
    have hprevT : gapPrev k q ∈ T := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hprev, gapPrev_in_gap hg.2⟩, by simpa using hf.2⟩
    have hbad := hmin (gapPrev k q) hprevT
    rw [gapPrev_y] at hbad
    omega
  · exact Finset.image_subset_image (Finset.filter_subset _ _)

theorem gapChainKeys_card_le_runs (S : Finset Site) (k : ℤ) :
    ((gapSupport S k).image (gapChainKey k)).card ≤ gapRunCount S k := by
  rw [gapChainKeys_eq_startKeys]
  exact Finset.card_image_le

/-- A site in a fixed layer is determined by the two intersecting zigzag keys. -/
theorem layer_pair_keys_injective (k : ℤ) :
    Set.InjOn (fun p : Site => (gapChainKey (k - 1) p, gapChainKey k p)) (layer k) := by
  intro p hp q hq heq
  have h₁ := congrArg Prod.fst heq
  have h₂ := congrArg Prod.snd heq
  change p.val 0 = k at hp
  change q.val 0 = k at hq
  apply Subtype.ext
  by_cases hk : k % 2 = 0
  · have hk' : ¬ (k - 1) % 2 = 0 := by omega
    simp only [gapChainKey, if_pos hk, if_neg hk'] at h₁ h₂
    funext i
    match i with
    | 0 => exact hp.trans hq.symm
    | 1 => omega
    | 2 => omega
  · have hk' : (k - 1) % 2 = 0 := by omega
    simp only [gapChainKey, if_neg hk, if_pos hk'] at h₁ h₂
    funext i
    match i with
    | 0 => exact hp.trans hq.symm
    | 1 => omega
    | 2 => omega

/-- Section 4(b): s_k ≤ β_(k-1) β_k. -/
theorem layer_card_le_run_product (S : Finset Site) (k : ℤ) :
    (finiteLayer S k).card ≤ gapRunCount S (k - 1) * gapRunCount S k := by
  let A := (gapSupport S (k - 1)).image (gapChainKey (k - 1))
  let B := (gapSupport S k).image (gapChainKey k)
  have hcard : (finiteLayer S k).card ≤ (A ×ˢ B).card := by
    apply Finset.card_le_card_of_injOn
      (fun p => (gapChainKey (k - 1) p, gapChainKey k p))
    · intro p hp
      have h := Finset.mem_filter.mp hp
      apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_image.mpr
        refine ⟨p, Finset.mem_filter.mpr ⟨h.1, Or.inr ?_⟩, rfl⟩
        omega
      · exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨h.1, Or.inl h.2⟩, rfl⟩
    · intro p hp q hq heq
      exact layer_pair_keys_injective k (Finset.mem_filter.mp hp).2
        (Finset.mem_filter.mp hq).2 heq
  rw [Finset.card_product] at hcard
  exact hcard.trans (Nat.mul_le_mul (gapChainKeys_card_le_runs S (k - 1))
    (gapChainKeys_card_le_runs S k))

end ProteinFolding.Tetrahedral
