import ProteinFolding.Tetrahedral.FarFieldColumnWireData
import ProteinFolding.Tetrahedral.FarFieldObstacleAvoidance
import ProteinFolding.Tetrahedral.NearFieldColumnPieces

namespace ProteinFolding.Tetrahedral.FarField

open NearField

/-- Canonical dangling caps enter their own column through its first bond.
This gives concrete local cap data even when the seed lies on a bend. -/
def columnsCapEntryData {m w : ℕ} (C : Fin w → DanglingColumn m)
    (hseed : Function.Injective (fun i => (C i).seed)) : CapEntryData (columnsWireData C hseed) where
  caps := fun i => (C i).seed
  sites := fun _ => 2
  paths := fun i => columnPrefix (C i) 2
  sites_pos := by intro i; decide
  sites_le_two := by intro i; decide
  first := by intro i a ha; exact columnPrefix_first (C i) 2 a ha
  last := by
    intro i a ha
    have hav : a.val = 1 := by change a.val + 1 = 2 at ha; omega
    change (C i).point a.val = _
    rw [hav, columnsWireData.armCap_eq]
  low := by
    intro i a
    have ha : a.val = 0 ∨ a.val = 1 := by have h := a.isLt; omega
    have hmem : (C i).point a.val ∈ skinSolid m 1 := by
      rcases ha with ha | ha
      · rw [ha]; exact (C i).point_zero_mem_solid_one
      · rw [ha]; exact (C i).point_one_mem_solid_one
    have h := skinSolid_rho_bound m 1 hmem
    change rho (octRadius m) ((C i).point a.val) < 20 * (m : ℤ) + 21
    change rho (octRadius m) ((C i).point a.val) ≤ 2 * ((m + 2 * 1 : ℕ) : ℤ) at h
    push_cast at h
    omega
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro s ⟨a, rfl⟩ ⟨b, heq⟩
    exact hij (hseed (DanglingColumn.seeds_eq_of_point_eq (C i) (C j) heq.symm))
  columns := by
    intro i j a b heq
    change (C i).point a.val = _ at heq
    rw [columnsWireData.column_pos_eq] at heq
    have hij := hseed (DanglingColumn.seeds_eq_of_point_eq (C i) (C j) heq)
    subst j
    have hab := (C i).point_injective heq
    have ha := a.isLt
    change a.val < 2 at ha
    exact ⟨rfl, by change a.val + 1 = 2; omega, by omega⟩

theorem columnsLocalObstacleData {m w : ℕ} (C : Fin w → DanglingColumn m)
    (hseed : Function.Injective (fun i => (C i).seed)) (O : Set Site)
    (hlow : ∀ s ∈ O, rho (octRadius m) s < 20 * (m : ℤ) + 21)
    (hclear : ∀ i n, (C i).point n ∈ O → n = 0) :
    LocalObstacleData (columnsCapEntryData C hseed) O where
  low := hlow
  entries := by
    intro i a ha
    have hzero := hclear i a.val ha
    change (C i).point a.val = (C i).seed
    rw [hzero]
    rfl
  columns := by
    intro i a ha
    have heq := columnsWireData.column_pos_eq C hseed i a
    rw [heq] at ha
    have hbad := hclear i (1 + a.val) ha
    omega

end ProteinFolding.Tetrahedral.FarField
