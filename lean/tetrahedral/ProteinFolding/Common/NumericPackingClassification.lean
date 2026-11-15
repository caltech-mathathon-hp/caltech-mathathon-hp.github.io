import ProteinFolding.Common.NumericPackingBins
import Mathlib.Data.List.Perm.Basic

/-! Complete local classification of the numerical bins. Neither four items
nor one item of each type is assumed: both follow from the bin's exact load.
This is the soundness interface for recovering a three-dimensional matching.
-/

namespace ProteinFolding.NumericPacking

theorem exists_kind_of_count (ts : List Token) (k : ℕ) (h : kindCount k ts = 1) :
    ∃ t ∈ ts, t.kind = k := by
  have hp : 0 < (ts.filter (fun t => t.kind == k)).length := by
    change 0 < kindCount k ts
    omega
  obtain ⟨t, ht⟩ := List.exists_mem_of_length_pos hp
  obtain ⟨hts, htk⟩ := List.mem_filter.mp ht
  exact ⟨t, hts, by simpa using htk⟩

theorem Token.kind_one (t : Token) : t.kind = 1 ↔ ∃ i r, t = .x i r := by
  cases t <;> simp [Token.kind]

theorem Token.kind_two (t : Token) : t.kind = 2 ↔ ∃ i r, t = .y i r := by
  cases t <;> simp [Token.kind]

theorem Token.kind_four (t : Token) : t.kind = 4 ↔ ∃ i r, t = .z i r := by
  cases t <;> simp [Token.kind]

theorem Token.kind_eight (t : Token) : t.kind = 8 ↔ ∃ i j k, t = .triple i j k := by
  cases t <;> simp [Token.kind]

/-- An arbitrary exact bin is a permutation of one selector with three
coordinate-matching tokens, all real or all dummy. -/
theorem exact_bin_quadruple (n : ℕ) (ts : List Token)
    (hv : ∀ t ∈ ts, t.Valid n) (hsum : (ts.map (Token.value n)).sum = capacity n) :
    ∃ i j k r, ts.Perm [.triple i j k, .x i r, .y j r, .z k r] := by
  obtain ⟨hc1, hc2, hc4, hc8⟩ := exact_bin_kind_counts n ts hv hsum
  obtain ⟨tx, htx, hkx⟩ := exists_kind_of_count ts 1 hc1
  obtain ⟨a, rx, rfl⟩ := (Token.kind_one tx).mp hkx
  obtain ⟨ty, hty, hky⟩ := exists_kind_of_count ts 2 hc2
  obtain ⟨b, ry, rfl⟩ := (Token.kind_two ty).mp hky
  obtain ⟨tz, htz, hkz⟩ := exists_kind_of_count ts 4 hc4
  obtain ⟨c, rz, rfl⟩ := (Token.kind_four tz).mp hkz
  obtain ⟨tt, htt, hkt⟩ := exists_kind_of_count ts 8 hc8
  obtain ⟨i, j, k, rfl⟩ := (Token.kind_eight tt).mp hkt
  have hsub : [.triple i j k, .x a rx, .y b ry, .z c rz].Subperm ts := by
    apply List.subperm_of_subset (by simp)
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact htt
    · exact htx
    · exact hty
    · exact htz
  have hp : ts.Perm [.triple i j k, .x a rx, .y b ry, .z c rz] :=
    (hsub.perm_of_length_le (by simpa using (exact_bin_length n ts hv hsum).le)).symm
  have htbound := hv (.triple i j k) htt
  have hxbound := hv (.x a rx) htx
  have hybound := hv (.y b ry) hty
  have hzbound := hv (.z c rz) htz
  have he : selector n i j k + xToken n a rx + yToken n b ry + zToken n c rz = capacity n := by
    have hm := (hp.map (Token.value n)).sum_eq
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Token.value] at hm
    rw [hsum] at hm
    omega
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :=
    (selector_quad_iff n i j k a b c htbound.1 htbound.2.1 htbound.2.2
      hxbound hybound hzbound rx ry rz).mp he
  exact ⟨_, _, _, _, hp⟩

end ProteinFolding.NumericPacking
