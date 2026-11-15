import ProteinFolding.Tetrahedral.FrameForcingSeparatorBlocks

/-! The bin intervals between sharp separator windows are disjoint from
all separator blocks and from one another, and lie inside the full track. -/

namespace ProteinFolding.Tetrahedral

theorem frameTrackBand_disjoint (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame)
    (a b c d : ℕ) (horder : b ≤ c) :
    Disjoint (frameTrackBand m F a b) (frameTrackBand m F c d) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨r, hr, hrx⟩ := Finset.mem_image.mp hx
  obtain ⟨s, hs, hsx⟩ := Finset.mem_image.mp hy
  have heq := frameTrackPoint_injective m hm F (hrx.trans hsx.symm)
  have hr' := Finset.mem_Ico.mp hr
  have hs' := Finset.mem_Ico.mp hs
  omega

namespace ConstructionParameters

def binLeftIndex (p : ConstructionParameters) (k : Fin p.bins) : Fin (p.bins + 1) :=
  ⟨k.val, by have h := k.isLt; omega⟩

def binRightIndex (p : ConstructionParameters) (k : Fin p.bins) : Fin (p.bins + 1) :=
  ⟨k.val + 1, by have h := k.isLt; omega⟩

def binTrackRegion (p : ConstructionParameters) (F : OctEdgeFrame)
    (starts : Fin (p.bins + 1) → ℕ) (k : Fin p.bins) : Finset Site :=
  frameTrackBand p.side F (2 * starts (p.binLeftIndex k) + 4) (2 * starts (p.binRightIndex k))

theorem separator_starts_mono (p : ConstructionParameters) (starts : Fin (p.bins + 1) → ℕ)
    (hwindow : ∀ k, |(starts k : ℤ) - (p.separatorIndex k.val : ℤ)| ≤ (p.separatorRadius : ℤ)) :
    Monotone starts := by
  intro k l hkl
  by_cases heq : k = l
  · subst l
    exact le_rfl
  · have hval : k.val < l.val := by
      have hne : k.val ≠ l.val := by intro h; exact heq (Fin.ext h)
      have hklnat : k.val ≤ l.val := hkl
      omega
    have horder := p.separator_window_order_of_lt k.val l.val (starts k) (starts l)
      hval (hwindow k) (hwindow l)
    omega

theorem binTrackRegion_margins (p : ConstructionParameters) (F : OctEdgeFrame)
    (starts : Fin (p.bins + 1) → ℕ)
    (hwindow : ∀ k, |(starts k : ℤ) - (p.separatorIndex k.val : ℤ)| ≤ (p.separatorRadius : ℤ))
    (k : Fin p.bins) :
    5 ≤ 2 * starts (p.binLeftIndex k) + 4 ∧
      2 * starts (p.binRightIndex k) + 6 ≤ 2 * p.side ∧
      p.binTrackRegion F starts k ⊆ frameTrackSites p.side F := by
  have hleft := p.separator_window_track_margin (p.binLeftIndex k).val (starts (p.binLeftIndex k))
    (by have h := (p.binLeftIndex k).isLt; omega) (hwindow _)
  have hright := p.separator_window_track_margin (p.binRightIndex k).val (starts (p.binRightIndex k))
    (by have h := (p.binRightIndex k).isLt; omega) (hwindow _)
  refine ⟨by omega, hright.2, ?_⟩
  intro x hx
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
  have hr' := Finset.mem_Ico.mp hr
  exact Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr (by omega), rfl⟩

theorem binTrackRegion_disjoint_separator (p : ConstructionParameters) (F : OctEdgeFrame)
    (starts : Fin (p.bins + 1) → ℕ)
    (hwindow : ∀ k, |(starts k : ℤ) - (p.separatorIndex k.val : ℤ)| ≤ (p.separatorRadius : ℤ))
    (k : Fin p.bins) (l : Fin (p.bins + 1)) :
    Disjoint (p.binTrackRegion F starts k)
      (frameTrackBand p.side F (2 * starts l) (2 * starts l + 4)) := by
  have hm := p.side_ge
  have hmono := p.separator_starts_mono starts hwindow
  by_cases hl : l.val ≤ k.val
  · have hb : l ≤ p.binLeftIndex k := hl
    have hs := hmono hb
    apply Disjoint.symm
    exact frameTrackBand_disjoint p.side (by omega) F _ _ _ _ (by omega)
  · have hb : p.binRightIndex k ≤ l := by change k.val + 1 ≤ l.val; omega
    have hs := hmono hb
    exact frameTrackBand_disjoint p.side (by omega) F _ _ _ _ (by omega)

theorem binTrackRegion_pairwise_disjoint (p : ConstructionParameters) (F : OctEdgeFrame)
    (starts : Fin (p.bins + 1) → ℕ)
    (hwindow : ∀ k, |(starts k : ℤ) - (p.separatorIndex k.val : ℤ)| ≤ (p.separatorRadius : ℤ))
    (k l : Fin p.bins) (hne : k ≠ l) :
    Disjoint (p.binTrackRegion F starts k) (p.binTrackRegion F starts l) := by
  have hm := p.side_ge
  have hmono := p.separator_starts_mono starts hwindow
  have hval : k.val ≠ l.val := by intro h; exact hne (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hkl | hlk
  · have hb : p.binRightIndex k ≤ p.binLeftIndex l := by change k.val + 1 ≤ l.val; omega
    have hs := hmono hb
    exact frameTrackBand_disjoint p.side (by omega) F _ _ _ _ (by omega)
  · have hb : p.binRightIndex l ≤ p.binLeftIndex k := by change l.val + 1 ≤ k.val; omega
    have hs := hmono hb
    apply Disjoint.symm
    exact frameTrackBand_disjoint p.side (by omega) F _ _ _ _ (by omega)

end ConstructionParameters

end ProteinFolding.Tetrahedral
