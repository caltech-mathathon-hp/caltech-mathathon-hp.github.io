import ProteinFolding.Tetrahedral.Skins
import ProteinFolding.Tetrahedral.RoutingBounds
import ProteinFolding.Tetrahedral.FoldAssembly
import ProteinFolding.Tetrahedral.FarFieldAvoidance

/-! The fixed-centre near-field solid lies strictly below the far-field
levels. This turns the numerical height budget into geometric avoidance. -/

namespace ProteinFolding.Tetrahedral

theorem nearSolid_rho_lt_farFieldHeight (m K : ℕ) (hK : K ≤ m) {p : Site}
    (hp : p ∈ skinSolid m (2 * K + 3)) :
    FarField.rho (octRadius m) p < (farFieldHeight m : ℤ) := by
  have hρ := skinSolid_rho_bound m (2 * K + 3) hp
  have hheight := farField_nearField_separation m K hK
  dsimp [FarField.rho, FarField.Y, FarField.Z]
  push_cast at hρ
  omega

theorem high_rho_outside_nearSolid (m K : ℕ) (hK : K ≤ m) {p : Site}
    (hp : (farFieldHeight m : ℤ) ≤ FarField.rho (octRadius m) p) :
    p ∉ skinSolid m (2 * K + 3) := by
  intro hmem
  have h := nearSolid_rho_lt_farFieldHeight m K hK hmem
  omega

theorem high_path_disjoint_nearSolid (m K n : ℕ) (hK : K ≤ m)
    (f : Fold tetrahedralLattice n)
    (hf : ∀ i, (farFieldHeight m : ℤ) ≤ FarField.rho (octRadius m) (f.pos i)) :
    Disjoint (foldSites f) (skinSolid m (2 * K + 3)) := by
  apply Finset.disjoint_left.mpr
  intro p hp hnear
  obtain ⟨i, rfl⟩ := (mem_foldSites f p).mp hp
  exact high_rho_outside_nearSolid m K hK (hf i) hnear

theorem paddingFold_disjoint_nearSolid (m K : ℕ) (hK : K ≤ m)
    (c : Site) (hc : InASublattice c.val) (up : Bool)
    (r b : ℕ) (δ η : Bool) (d : ℕ) (hr : r = 2 ∨ r = 3) (hb : r + 47 ≤ b)
    (hy : 4 ≤ FarField.Y (octRadius m) c) (hz : 4 ≤ FarField.Z c)
    (hlevel : (farFieldHeight m : ℤ) ≤ FarField.privateLevel (octRadius m) c up) :
    Disjoint (foldSites (FarField.paddingFold c hc up r b δ η d hr hb))
      (skinSolid m (2 * K + 3)) := by
  apply high_path_disjoint_nearSolid m K _ hK
  intro i
  have h := FarField.paddingFold_private (octRadius m) c hc up r b δ η d hr hb hy hz i
  rcases h.2.1 with h | h <;> omega

end ProteinFolding.Tetrahedral
