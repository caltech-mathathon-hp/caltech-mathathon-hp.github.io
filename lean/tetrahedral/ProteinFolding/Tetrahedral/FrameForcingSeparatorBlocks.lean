import ProteinFolding.Tetrahedral.FrameForcingBinChains
import ProteinFolding.Tetrahedral.FrameForcingSeparatorExhaustion

/-! Consecutive physical separator pairs form four-site intervals.
Separated sharp windows make all declared separator blocks disjoint. -/

namespace ProteinFolding.Tetrahedral

theorem twoTrackPairs_eq_band (m : ℕ) (F : OctEdgeFrame) (u v : ℕ)
    (hconsecutive : u + 1 = v ∨ v + 1 = u) :
    twoTrackPairs m F u v = frameTrackBand m F (2 * min u v) (2 * min u v + 4) := by
  ext x
  constructor
  · intro hx
    simp only [twoTrackPairs, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨2 * u, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨2 * u + 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨2 * v, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨2 * v + 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩
  · intro hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact twoTrackPairs_mem m F u v s hconsecutive (Finset.mem_Ico.mp hs)

theorem twoTrackPairs_card (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (u v : ℕ)
    (hconsecutive : u + 1 = v ∨ v + 1 = u) : (twoTrackPairs m F u v).card = 4 := by
  rw [twoTrackPairs_eq_band m F u v hconsecutive, frameTrackBand_card m hm F]
  omega

theorem twoTrackPairs_disjoint (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (u v u' v' : ℕ)
    (hleft : u + 1 = v ∨ v + 1 = u) (hright : u' + 1 = v' ∨ v' + 1 = u')
    (horder : min u v + 2 ≤ min u' v') :
    Disjoint (twoTrackPairs m F u v) (twoTrackPairs m F u' v') := by
  rw [twoTrackPairs_eq_band m F u v hleft, twoTrackPairs_eq_band m F u' v' hright]
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨r, hr, hrx⟩ := Finset.mem_image.mp hx
  obtain ⟨s, hs, hsx⟩ := Finset.mem_image.mp hy
  have hrs := frameTrackPoint_injective m hm F (hrx.trans hsx.symm)
  have hr' := Finset.mem_Ico.mp hr
  have hs' := Finset.mem_Ico.mp hs
  omega

theorem ConstructionParameters.separator_window_order_of_lt (p : ConstructionParameters)
    (k l i j : ℕ) (hkl : k < l)
    (hi : |(i : ℤ) - (p.separatorIndex k : ℤ)| ≤ (p.separatorRadius : ℤ))
    (hj : |(j : ℤ) - (p.separatorIndex l : ℤ)| ≤ (p.separatorRadius : ℤ)) :
    i + 4 ≤ j := by
  have hsep := p.separator_windows_separated k
  have hmono := p.separatorIndex_mono (show k + 1 ≤ l by omega)
  have hbi := abs_le.mp hi
  have hbj := abs_le.mp hj
  omega

end ProteinFolding.Tetrahedral
