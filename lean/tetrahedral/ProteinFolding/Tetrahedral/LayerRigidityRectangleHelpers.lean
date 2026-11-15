import ProteinFolding.Tetrahedral.LayerRigidityErosion
import ProteinFolding.Tetrahedral.Normalization

/-! The geometric content of having exactly one run on each gap chain. -/

namespace ProteinFolding.Tetrahedral

theorem site_x_y_parity (p : Site) : p.val 0 % 2 = p.val 1 % 2 := by
  rcases p.property with h | h
  · rw [h.1 0, h.1 1]
  · rw [h.1 0, h.1 1]

theorem gap_key_y_ext {k : ℤ} {p q : Site} (hp : InGap k p) (hq : InGap k q)
    (hkey : gapChainKey k p = gapChainKey k q) (hy : p.val 1 = q.val 1) : p = q := by
  have hpx := site_x_y_parity p
  have hqx := site_x_y_parity q
  have hx : p.val 0 = q.val 0 := by
    unfold InGap at hp hq
    omega
  have hz : p.val 2 = q.val 2 := by
    unfold gapChainKey at hkey
    split_ifs at hkey <;> omega
  apply Subtype.ext
  funext i
  fin_cases i
  · exact hx
  · exact hy
  · exact hz

theorem occupied_chain_start_below (S : Finset Site) (k : ℤ) (p : Site)
    (hp : p ∈ S) (hgap : InGap k p) :
    ∃ q ∈ gapRunStarts S k, gapChainKey k q = gapChainKey k p ∧ q.val 1 ≤ p.val 1 := by
  let T := (gapSupport S k).filter (fun q => gapChainKey k q = gapChainKey k p)
  have hpT : p ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hp, hgap⟩, rfl⟩
  obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image T (fun q => q.val 1) ⟨p, hpT⟩
  have hf := Finset.mem_filter.mp hq
  have hg := Finset.mem_filter.mp hf.1
  refine ⟨q, Finset.mem_filter.mpr ⟨hf.1, ?_⟩, hf.2, hmin p hpT⟩
  intro hprev
  have hprevT : gapPrev k q ∈ T := Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨hprev, gapPrev_in_gap hg.2⟩, by simpa using hf.2⟩
  have hbad := hmin (gapPrev k q) hprevT
  rw [gapPrev_y] at hbad
  omega

/-- The occupied vertices of a chain form an interval when the chain has one start. -/
theorem one_start_per_chain_order_convex (S : Finset Site) (k : ℤ)
    (hinj : Set.InjOn (gapChainKey k) (gapRunStarts S k)) (lo p hi : Site)
    (hlo : lo ∈ S) (hhi : hi ∈ S)
    (hlogap : InGap k lo) (hpgap : InGap k p) (hhigap : InGap k hi)
    (hlokey : gapChainKey k lo = gapChainKey k p)
    (hhikey : gapChainKey k hi = gapChainKey k p)
    (hlop : lo.val 1 ≤ p.val 1) (hphi : p.val 1 ≤ hi.val 1) : p ∈ S := by
  by_contra hnot
  let T := (gapSupport S k).filter
    (fun q => gapChainKey k q = gapChainKey k p ∧ p.val 1 ≤ q.val 1)
  have hhiT : hi ∈ T := Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨hhi, hhigap⟩, hhikey, hphi⟩
  obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image T (fun q => q.val 1) ⟨hi, hhiT⟩
  have hf := Finset.mem_filter.mp hq
  have hg := Finset.mem_filter.mp hf.1
  have hqp : p.val 1 < q.val 1 := by
    have hne : q.val 1 ≠ p.val 1 := by
      intro heq
      have he := gap_key_y_ext hg.2 hpgap hf.2.1 heq
      exact hnot (he ▸ hg.1)
    omega
  have hqstart : q ∈ gapRunStarts S k := by
    apply Finset.mem_filter.mpr
    refine ⟨hf.1, ?_⟩
    intro hprev
    have hprevT : gapPrev k q ∈ T := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hprev, gapPrev_in_gap hg.2⟩,
        by simpa using hf.2.1, by rw [gapPrev_y]; omega⟩
    have hbad := hmin (gapPrev k q) hprevT
    rw [gapPrev_y] at hbad
    omega
  obtain ⟨r, hr, hrkey, hry⟩ := occupied_chain_start_below S k lo hlo hlogap
  have heq : r = q := hinj hr hqstart (hrkey.trans (hlokey.trans hf.2.1.symm))
  rw [heq] at hry
  omega

/-- Integer coordinates in the square grid through a lattice site. -/
def layerGridPoint (c : Site) (u v : ℤ) : Site :=
  ⟨![c.val 0, c.val 1 + 2 * u + 2 * v, c.val 2 + 2 * u - 2 * v], by
    rcases c.property with hc | hc
    · left
      constructor
      · intro i
        fin_cases i
        · exact hc.1 0
        · have h := hc.1 1
          change (c.val 1 + 2 * u + 2 * v) % 2 = 0
          omega
        · have h := hc.1 2
          change (c.val 2 + 2 * u - 2 * v) % 2 = 0
          omega
      · have h := hc.2
        dsimp [coordinateSum] at h ⊢
        omega
    · right
      constructor
      · intro i
        fin_cases i
        · exact hc.1 0
        · have h := hc.1 1
          change (c.val 1 + 2 * u + 2 * v) % 2 = 1
          omega
        · have h := hc.1 2
          change (c.val 2 + 2 * u - 2 * v) % 2 = 1
          omega
      · have h := hc.2
        dsimp [coordinateSum] at h ⊢
        omega⟩

@[simp] theorem layerGridPoint_x (c : Site) (u v : ℤ) :
    (layerGridPoint c u v).val 0 = c.val 0 := rfl

@[simp] theorem layerGridPoint_y (c : Site) (u v : ℤ) :
    (layerGridPoint c u v).val 1 = c.val 1 + 2 * u + 2 * v := rfl

@[simp] theorem layerGridPoint_z (c : Site) (u v : ℤ) :
    (layerGridPoint c u v).val 2 = c.val 2 + 2 * u - 2 * v := rfl

@[simp] theorem layerGridPoint_zero (c : Site) : layerGridPoint c 0 0 = c := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [layerGridPoint]

theorem layerGridPoint_injective (c : Site) :
    Function.Injective (fun uv : ℤ × ℤ => layerGridPoint c uv.1 uv.2) := by
  intro uv wz heq
  have hy := congrArg (fun p : Site => p.val 1) heq
  have hz := congrArg (fun p : Site => p.val 2) heq
  dsimp at hy hz
  exact Prod.ext (by omega) (by omega)

theorem layerGridPoint_left_key (c : Site) (u v : ℤ) (heven : c.val 0 % 2 = 0) :
    gapChainKey (c.val 0 - 1) (layerGridPoint c u v) =
      gapChainKey (c.val 0 - 1) c + 4 * u := by
  have hodd : (c.val 0 - 1) % 2 ≠ 0 := by omega
  simp only [gapChainKey, hodd, if_false, layerGridPoint_y, layerGridPoint_z]
  omega

theorem layerGridPoint_right_key (c : Site) (u v : ℤ) (heven : c.val 0 % 2 = 0) :
    gapChainKey (c.val 0) (layerGridPoint c u v) =
      gapChainKey (c.val 0) c + 4 * v := by
  simp only [gapChainKey, heven, if_true, layerGridPoint_y, layerGridPoint_z]
  omega

theorem exists_layerGridPoint (c p : Site) (hx : p.val 0 = c.val 0) :
    ∃ u v : ℤ, layerGridPoint c u v = p := by
  have hcy := site_x_y_parity c
  have hpy := site_x_y_parity p
  have hzmod : (p.val 1 + p.val 2 - c.val 1 - c.val 2) % 4 = 0 := by
    rcases c.property with hc | hc
    · have hp : InASublattice p.val := (inA_iff_x_even p).mpr (by rw [hx]; exact hc.1 0)
      have hc4 := hc.2
      have hp4 := hp.2
      dsimp [coordinateSum] at hc4 hp4
      omega
    · have hp : InBSublattice p.val := by
        rcases p.property with hp | hp
        · have he := hp.1 0
          have ho := hc.1 0
          omega
        · exact hp
      have hc4 := hc.2
      have hp4 := hp.2
      dsimp [coordinateSum] at hc4 hp4
      omega
  have hwmod : (p.val 1 - p.val 2 - c.val 1 + c.val 2) % 4 = 0 := by omega
  let u := (p.val 1 + p.val 2 - c.val 1 - c.val 2) / 4
  let v := (p.val 1 - p.val 2 - c.val 1 + c.val 2) / 4
  have hu : 4 * u = p.val 1 + p.val 2 - c.val 1 - c.val 2 := by dsimp [u]; omega
  have hv : 4 * v = p.val 1 - p.val 2 - c.val 1 + c.val 2 := by dsimp [v]; omega
  refine ⟨u, v, ?_⟩
  apply Subtype.ext
  funext i
  fin_cases i
  · exact hx.symm
  · change c.val 1 + 2 * u + 2 * v = p.val 1
    omega
  · change c.val 2 + 2 * u - 2 * v = p.val 2
    omega

end ProteinFolding.Tetrahedral
