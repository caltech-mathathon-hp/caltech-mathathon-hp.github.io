import ProteinFolding.Tetrahedral.LayerRigidity

/-! Tight layer imbalance determines the smaller layer by a two-neighbour erosion. -/

namespace ProteinFolding.Tetrahedral

theorem one_start_per_chain_fills_hole (S : Finset Site) (k : ℤ)
    (hinj : Set.InjOn (gapChainKey k) (gapRunStarts S k)) (p : Site) (hp : InGap k p)
    (hprev : gapPrev k p ∈ S) (hnext : gapNext k p ∈ S) : p ∈ S := by
  by_contra hnot
  let T := (gapSupport S k).filter (fun q => gapChainKey k q = gapChainKey k p)
  have hprevT : gapPrev k p ∈ T := Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨hprev, gapPrev_in_gap hp⟩, gapPrev_key k p⟩
  obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image T (fun q => q.val 1) ⟨gapPrev k p, hprevT⟩
  have hf := Finset.mem_filter.mp hq
  have hg := Finset.mem_filter.mp hf.1
  have hqstart : q ∈ gapRunStarts S k := by
    apply Finset.mem_filter.mpr
    refine ⟨hf.1, ?_⟩
    intro hqprev
    have hqprevT : gapPrev k q ∈ T := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hqprev, gapPrev_in_gap hg.2⟩, by simpa using hf.2⟩
    have hbad := hmin (gapPrev k q) hqprevT
    rw [gapPrev_y] at hbad
    omega
  have hnextstart : gapNext k p ∈ gapRunStarts S k := Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨hnext, gapNext_in_gap hp⟩, by simpa only [gapPrev_next] using hnot⟩
  have heq : q = gapNext k p := hinj hqstart hnextstart (by rw [gapNext_key]; exact hf.2)
  have hbelow := hmin (gapPrev k p) hprevT
  rw [heq, gapNext_y, gapPrev_y] at hbelow
  omega

/-- Equality in the signed imbalance puts all run starts in the larger layer
and makes the predecessor map onto the smaller occupied layer. -/
theorem tight_imbalance_smaller_neighbours (S : Finset Site) (k a b : ℤ)
    (hab : (a = k ∧ b = k + 1) ∨ (a = k + 1 ∧ b = k))
    (htight : (finiteLayer S a).card = (finiteLayer S b).card + gapRunCount S k) :
    ∀ p ∈ finiteLayer S b, gapPrev k p ∈ S ∧ gapNext k p ∈ S := by
  let T := finiteLayer S a
  let U := finiteLayer S b
  let starts := T.filter (fun p => gapPrev k p ∉ S)
  let goods := T.filter (fun p => gapPrev k p ∈ S)
  have hgapT : ∀ p ∈ T, p ∈ gapSupport S k := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨h.1, ?_⟩
    rcases hab with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact Or.inl h.2
    · exact Or.inr h.2
  have hgapU : ∀ p ∈ U, p ∈ gapSupport S k := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨h.1, ?_⟩
    rcases hab with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact Or.inr h.2
    · exact Or.inl h.2
  have hstarts : starts ⊆ gapRunStarts S k := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hgapT p h.1, h.2⟩
  have hmap : goods.image (gapPrev k) ⊆ U := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have h := Finset.mem_filter.mp hq
    have hx := gapPrev_x (hgapT q h.1)
    have ha := (Finset.mem_filter.mp h.1).2
    apply Finset.mem_filter.mpr
    refine ⟨h.2, ?_⟩
    rcases hab with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ <;> omega
  have hstartsle := Finset.card_le_card hstarts
  change starts.card ≤ gapRunCount S k at hstartsle
  have hgoodscard : (goods.image (gapPrev k)).card = goods.card :=
    Finset.card_image_of_injective _ (gapPrev_injective k)
  have hgoodsle := Finset.card_le_card hmap
  rw [hgoodscard] at hgoodsle
  have hpart := Finset.filter_card_add_filter_neg_card_eq_card
    (s := T) (p := fun p => gapPrev k p ∈ S)
  change goods.card + starts.card = T.card at hpart
  change T.card = U.card + gapRunCount S k at htight
  have hstartseq : starts.card = gapRunCount S k := by omega
  have hgoodseq : goods.card = U.card := by omega
  have hallstarts : starts = gapRunStarts S k := by
    apply Finset.eq_of_subset_of_card_le hstarts
    change gapRunCount S k ≤ starts.card
    omega
  have hallgoods : goods.image (gapPrev k) = U := by
    apply Finset.eq_of_subset_of_card_le hmap
    rw [hgoodscard, hgoodseq]
  intro p hp
  constructor
  · by_contra hnot
    have hpstart : p ∈ gapRunStarts S k := Finset.mem_filter.mpr ⟨hgapU p hp, hnot⟩
    rw [← hallstarts] at hpstart
    have hpa := (Finset.mem_filter.mp (Finset.mem_filter.mp hpstart).1).2
    have hpb := (Finset.mem_filter.mp hp).2
    rcases hab with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ <;> omega
  · have hpimage : p ∈ goods.image (gapPrev k) := by rw [hallgoods]; exact hp
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hpimage
    have hqS := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    have hnext : gapNext k p = q := by
      have h := congrArg (gapNext k) heq
      simpa only [gapNext_prev] using h.symm
    rw [hnext]
    exact hqS

theorem gap_steps_other_layer (k a b : ℤ) (p : Site)
    (hab : (a = k ∧ b = k + 1) ∨ (a = k + 1 ∧ b = k)) (hp : p.val 0 = b) :
    (gapPrev k p).val 0 = a ∧ (gapNext k p).val 0 = a := by
  have hgap : InGap k p := by rcases hab with ⟨_, rfl⟩ | ⟨_, rfl⟩; exact Or.inr hp; exact Or.inl hp
  have hprev := gapPrev_in_gap hgap
  have hnext := gapNext_in_gap hgap
  have hpa := adj_coordinate (gapPrev_adj k p) 0
  have hna := adj_coordinate (gapNext_adj k p) 0
  unfold InGap at hprev hnext
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> constructor <;> omega

/-- The smaller layer is exactly the two-neighbour erosion of the larger one. -/
theorem tight_imbalance_erosion (S : Finset Site) (k a b : ℤ)
    (hab : (a = k ∧ b = k + 1) ∨ (a = k + 1 ∧ b = k))
    (htight : (finiteLayer S a).card = (finiteLayer S b).card + gapRunCount S k)
    (hinj : Set.InjOn (gapChainKey k) (gapRunStarts S k)) (p : Site) (hp : p.val 0 = b) :
    p ∈ S ↔ gapPrev k p ∈ finiteLayer S a ∧ gapNext k p ∈ finiteLayer S a := by
  have hx := gap_steps_other_layer k a b p hab hp
  constructor
  · intro hpS
    have h := tight_imbalance_smaller_neighbours S k a b hab htight p
      (Finset.mem_filter.mpr ⟨hpS, hp⟩)
    exact ⟨Finset.mem_filter.mpr ⟨h.1, hx.1⟩, Finset.mem_filter.mpr ⟨h.2, hx.2⟩⟩
  · rintro ⟨hprev, hnext⟩
    have hgap : InGap k p := by rcases hab with ⟨_, rfl⟩ | ⟨_, rfl⟩; exact Or.inr hp; exact Or.inl hp
    exact one_start_per_chain_fills_hole S k hinj p hgap
      (Finset.mem_filter.mp hprev).1 (Finset.mem_filter.mp hnext).1

end ProteinFolding.Tetrahedral
