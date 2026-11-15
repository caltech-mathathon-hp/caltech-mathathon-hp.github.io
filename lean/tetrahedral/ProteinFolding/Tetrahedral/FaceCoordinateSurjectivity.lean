import ProteinFolding.Tetrahedral.FaceCoordinates
import ProteinFolding.Tetrahedral.Skins

/-! Every actual F' surface/subsurface site has the nonnegative triangular
coordinates used by the explicit rows and dangling columns. -/

namespace ProteinFolding.Tetrahedral

theorem inSkinSolid_B_upper (m j : ℕ) {p : Site} (hpB : InBSublattice p.val)
    (hp : InSkinSolid m j p) (i : Fin 4) :
    tetraCoordinate m p.val i ≤ 2 * ((m + 2 * j : ℕ) : ℤ) - 3 := by
  have h := (hp i).2
  have hmod := tetraCoordinate_mod_B m hpB i
  push_cast at h ⊢
  omega

theorem faceSurfaceSite_surjective (m j : ℕ) {p : Site}
    (hpB : InBSublattice p.val) (hp : InSkinSolid m j p)
    (hface : tetraCoordinate m p.val 3 = -(2 * ((m + 2 * j : ℕ) : ℤ) - 1)) :
    ∃ a b c : ℕ, ∃ hsum : a + b + c + 2 = m + 2 * j,
      p = faceSurfaceSite m j a b c hsum := by
  have h0 := inSkinSolid_B_upper m j hpB hp 0
  have h1 := inSkinSolid_B_upper m j hpB hp 1
  have h2 := inSkinSolid_B_upper m j hpB hp 2
  dsimp [tetraCoordinate] at h0 h1 h2 hface
  have hx : 1 ≤ p.val 0 := by omega
  have hy : 1 ≤ p.val 1 - octRadius m := by omega
  have hz : p.val 2 ≤ -1 := by omega
  let a := ((-p.val 2 - 1) / 2).toNat
  let b := ((p.val 1 - octRadius m - 1) / 2).toNat
  let c := ((p.val 0 - 1) / 2).toNat
  have hac : (a : ℤ) = (-p.val 2 - 1) / 2 := by
    exact Int.toNat_of_nonneg (by omega)
  have hbc : (b : ℤ) = (p.val 1 - octRadius m - 1) / 2 := by
    exact Int.toNat_of_nonneg (by omega)
  have hcc : (c : ℤ) = (p.val 0 - 1) / 2 := by
    exact Int.toNat_of_nonneg (by omega)
  have hxodd := hpB.1 0
  have hyodd := hpB.1 1
  have hzodd := hpB.1 2
  have hR : octRadius m % 2 = 0 := by unfold octRadius; omega
  have hxa : p.val 0 = 2 * (c : ℤ) + 1 := by omega
  have hya : p.val 1 = octRadius m + 2 * (b : ℤ) + 1 := by omega
  have hza : p.val 2 = -2 * (a : ℤ) - 1 := by omega
  have hsum : a + b + c + 2 = m + 2 * j := by omega
  refine ⟨a, b, c, hsum, ?_⟩
  apply Subtype.ext
  funext i
  fin_cases i <;> dsimp [faceSurfaceSite, faceSurfaceCoordinates] <;> omega

theorem faceSubSite_surjective (m j : ℕ) {p : Site}
    (hpA : InASublattice p.val)
    (hface : tetraCoordinate m p.val 3 = -(2 * ((m + 2 * j : ℕ) : ℤ) - 2))
    (hdepth : ∀ i : Fin 3, tetraCoordinate m p.val i.castSucc ≤
      2 * ((m + 2 * j : ℕ) : ℤ) - 6) :
    ∃ a b c : ℕ, ∃ hsum : a + b + c + 1 = m + 2 * j,
      1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ p = faceSubSite m j a b c hsum := by
  have h0 := hdepth 0
  have h1 := hdepth 1
  have h2 := hdepth 2
  dsimp [tetraCoordinate] at h0 h1 h2 hface
  have hx : 2 ≤ p.val 0 := by omega
  have hy : 2 ≤ p.val 1 - octRadius m := by omega
  have hz : p.val 2 ≤ -2 := by omega
  let a := (-p.val 2 / 2).toNat
  let b := ((p.val 1 - octRadius m) / 2).toNat
  let c := (p.val 0 / 2).toNat
  have hac : (a : ℤ) = -p.val 2 / 2 := by
    exact Int.toNat_of_nonneg (by omega)
  have hbc : (b : ℤ) = (p.val 1 - octRadius m) / 2 := by
    exact Int.toNat_of_nonneg (by omega)
  have hcc : (c : ℤ) = p.val 0 / 2 := by
    exact Int.toNat_of_nonneg (by omega)
  have hxeven := hpA.1 0
  have hyeven := hpA.1 1
  have hzeven := hpA.1 2
  have hR : octRadius m % 2 = 0 := by unfold octRadius; omega
  have hxa : p.val 0 = 2 * (c : ℤ) := by omega
  have hya : p.val 1 = octRadius m + 2 * (b : ℤ) := by omega
  have hza : p.val 2 = -2 * (a : ℤ) := by omega
  have hsum : a + b + c + 1 = m + 2 * j := by omega
  refine ⟨a, b, c, hsum, by omega, by omega, by omega, ?_⟩
  apply Subtype.ext
  funext i
  fin_cases i <;> dsimp [faceSubSite, faceSubCoordinates] <;> omega

theorem smallFace_owner_coordinates (m : ℕ) {p : Site}
    (hpB : InBSublattice p.val) (hp : p ∈ octahedron m)
    (hface : tetraCoordinate m p.val 3 = -(2 * (m : ℤ) - 1)) :
    ∃ a b c : ℕ, ∃ hsum : a + b + c + 2 = m,
      p = faceSurfaceSite m 0 a b c hsum := by
  have hsolid : InSkinSolid m 0 p := by
    apply (mem_skinSolid m 0 p).mp
    simpa only [skinSolid_zero] using hp
  exact faceSurfaceSite_surjective m 0 hpB hsolid hface

end ProteinFolding.Tetrahedral
