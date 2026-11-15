import ProteinFolding.Tetrahedral.BulkSolidIntersection
import ProteinFolding.Tetrahedral.OctahedralEdgeFacts

/-! The simultaneous rule merges of canon.py, without a sequential update order. -/

namespace ProteinFolding.Tetrahedral

def bulkOnDeletedEdge (m : ℕ) (p : Site) : Prop :=
  ∃ k j : Fin 4, k ≠ j ∧ OctEdgeSite m k j p

instance (m : ℕ) (p : Site) : Decidable (bulkOnDeletedEdge m p) := by
  unfold bulkOnDeletedEdge OctEdgeSite OctAEdgeSite OctBEdgeSite OctBigFace OctSmallFace
  infer_instance

def bulkDeletedEdges (m : ℕ) : Finset Site := (octahedron m).filter (bulkOnDeletedEdge m)
def bulkInterior (m : ℕ) : Finset Site := octahedron m \ bulkDeletedEdges m
def bulkBaseNeighbours (m : ℕ) (p : Site) : Finset Site := bulkRungNeighbours m p ∩ bulkInterior m
def bulkDamaged (m : ℕ) : Finset Site :=
  (bulkInterior m).filter (fun p => (bulkRungNeighbours m p ∩ bulkDeletedEdges m).Nonempty)

def bulkSign (x : ℤ) : ℤ := if 0 < x then 1 else if x < 0 then -1 else 0

theorem bulkSign_unit_of_ne (x : ℤ) (hx : x ≠ 0) : bulkSign x = 1 ∨ bulkSign x = -1 := by
  unfold bulkSign
  split_ifs <;> omega

theorem bulkSign_mul_pos (x : ℤ) (hx : x ≠ 0) : 0 < bulkSign x * x := by
  unfold bulkSign
  split_ifs <;> omega

def bulkRuleNeighbour (m : ℕ) (p q : Site) : Prop :=
  tetrahedralLattice.Adj p q ∧
    ((bulkY m p ≠ 0 ∧ bulkZ p ≠ 0 ∧
        bulkY m q - bulkY m p = bulkSign (bulkZ p) ∧
        bulkZ q - bulkZ p = -bulkSign (bulkY m p)) ∨
     (bulkZ p = 0 ∧ bulkY m p ≠ 0 ∧
        bulkY m q - bulkY m p = -bulkSign (bulkY m p) ∧
        bulkZ q - bulkZ p = 1))

instance (m : ℕ) (p q : Site) : Decidable (bulkRuleNeighbour m p q) := by
  unfold bulkRuleNeighbour
  infer_instance

theorem bulkRuleNeighbour_unique (m : ℕ) {p q r : Site}
    (hq : bulkRuleNeighbour m p q) (hr : bulkRuleNeighbour m p r) : q = r := by
  apply adjacent_yz_ext hq.1 hr.1
  · rcases hq.2 with hq | hq <;> rcases hr.2 with hr | hr
    all_goals dsimp [bulkY] at hq hr
    all_goals omega
  · rcases hq.2 with hq | hq <;> rcases hr.2 with hr | hr
    all_goals dsimp [bulkZ] at hq hr
    all_goals omega

theorem bulkRuleNeighbour_rho (m : ℕ) {p q : Site} (h : bulkRuleNeighbour m p q) :
    bulkRho m q = bulkRho m p := by
  rcases h.2 with ⟨hy0, hz0, hdy, hdz⟩ | ⟨hz0, hy0, hdy, hdz⟩
  · have hsy := bulkSign_unit_of_ne (bulkY m p) hy0
    have hsz := bulkSign_unit_of_ne (bulkZ p) hz0
    have hsypos := bulkSign_mul_pos (bulkY m p) hy0
    have hszpos := bulkSign_mul_pos (bulkZ p) hz0
    have hyabs := abs_add_signed_unit (bulkSign (bulkY m p)) (bulkY m p)
      (bulkSign (bulkZ p)) hsy hsypos hsz
    have hzabs := abs_add_signed_unit (bulkSign (bulkZ p)) (bulkZ p)
      (-bulkSign (bulkY m p)) hsz hszpos (by omega)
    have hqy : bulkY m q = bulkY m p + bulkSign (bulkZ p) := by omega
    have hqz : bulkZ q = bulkZ p + -bulkSign (bulkY m p) := by omega
    unfold bulkRho
    rw [hqy, hqz, hyabs, hzabs]
    ring
  · have hsy := bulkSign_unit_of_ne (bulkY m p) hy0
    have hsypos := bulkSign_mul_pos (bulkY m p) hy0
    have hyabs := abs_add_signed_unit (bulkSign (bulkY m p)) (bulkY m p)
      (-bulkSign (bulkY m p)) hsy hsypos (by omega)
    have hqy : bulkY m q = bulkY m p + -bulkSign (bulkY m p) := by omega
    have hqz : bulkZ q = 1 := by omega
    unfold bulkRho
    rw [hqy, hqz, hz0, abs_zero, hyabs]
    rcases hsy with hs | hs <;> rw [hs] <;> have hOne : |(1 : ℤ)| = 1 := by decide
    all_goals rw [hOne]; ring

def bulkPotentialTarget (m : ℕ) (d w : Site) : Prop :=
  w ∈ bulkInterior m ∧ bulkRuleNeighbour m d w ∧ w ∉ bulkBaseNeighbours m d ∧
    (bulkBaseNeighbours m w).card ≤ 1 ∧ 0 < (octDanglingDirections m w).card

instance (m : ℕ) (d w : Site) : Decidable (bulkPotentialTarget m d w) := by
  unfold bulkPotentialTarget
  infer_instance

def bulkClaimants (m : ℕ) (w : Site) : Finset Site :=
  (bulkDamaged m).filter (fun d => bulkPotentialTarget m d w)

def bulkMerge (m : ℕ) (d w : Site) : Prop :=
  d ∈ bulkDamaged m ∧ bulkPotentialTarget m d w ∧ (bulkClaimants m w).card = 1

instance (m : ℕ) (d w : Site) : Decidable (bulkMerge m d w) := by unfold bulkMerge; infer_instance

theorem bulk_damaged_base_degree (m : ℕ) {d : Site} (hd : d ∈ bulkDamaged m) :
    (bulkBaseNeighbours m d).card ≤ 1 := by
  have hf := Finset.mem_filter.mp hd
  obtain ⟨e, he⟩ := hf.2
  have he' := Finset.mem_inter.mp he
  have heNot : e ∉ bulkInterior m := by
    intro hei
    exact (Finset.mem_sdiff.mp hei).2 he'.2
  have hsub : bulkBaseNeighbours m d ⊆ (bulkRungNeighbours m d).erase e := by
    intro q hq
    have hq' := Finset.mem_inter.mp hq
    apply Finset.mem_erase.mpr
    refine ⟨?_, hq'.1⟩
    intro heq
    exact heNot (heq ▸ hq'.2)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem he'.1, bulkRungNeighbours_card] at hcard
  exact hcard

theorem bulkMerge_target_unique (m : ℕ) {d w z : Site}
    (hw : bulkMerge m d w) (hz : bulkMerge m d z) : w = z :=
  bulkRuleNeighbour_unique m hw.2.1.2.1 hz.2.1.2.1

theorem bulkMerge_claimant_unique (m : ℕ) {d e w : Site}
    (hd : bulkMerge m d w) (he : bulkMerge m e w) : d = e := by
  have hdmem : d ∈ bulkClaimants m w := Finset.mem_filter.mpr ⟨hd.1, hd.2.1⟩
  have hemem : e ∈ bulkClaimants m w := Finset.mem_filter.mpr ⟨he.1, he.2.1⟩
  exact Finset.card_le_one.mp (le_of_eq hd.2.2) d hdmem e hemem

theorem bulkMerge_adj (m : ℕ) {d w : Site} (h : bulkMerge m d w) : tetrahedralLattice.Adj d w :=
  h.2.1.2.1.1

theorem bulkMerge_rho (m : ℕ) {d w : Site} (h : bulkMerge m d w) : bulkRho m w = bulkRho m d :=
  bulkRuleNeighbour_rho m h.2.1.2.1

theorem bulkMerge_mem (m : ℕ) {d w : Site} (h : bulkMerge m d w) :
    d ∈ bulkInterior m ∧ w ∈ bulkInterior m :=
  ⟨(Finset.mem_filter.mp h.1).1, h.2.1.1⟩

end ProteinFolding.Tetrahedral
