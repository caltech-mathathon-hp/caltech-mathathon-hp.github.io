import ProteinFolding.Tetrahedral.FaceRowsPaths
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange

/-! Finite injective row segments, with their exact sizes and skin bounds. -/

namespace ProteinFolding.Tetrahedral

theorem mem_skin_outside_oct (m j : ℕ) {p : Site} (hp : p ∈ skin m j) : p ∉ octahedron m := by
  intro ho
  have hzero : p ∈ skinSolid m 0 := by rw [skinSolid_zero]; exact ho
  exact (Finset.mem_sdiff.mp hp).2 (skinSolid_mono m (Nat.zero_le (j - 1)) hzero)

theorem faceRowA_mem_skin (m j a b c : ℕ) (hs : a + b + c + 2 = m + 2 * j)
    (hj : 1 ≤ j) (ha : 1 ≤ a) (r : ℕ) (hr : r ≤ 2 * c) :
    faceRowPoint 0 m j a b c hs r ∈ skin m j := by
  by_cases hmod : r % 2 = 0
  · have heq : r = 2 * (r / 2) := by omega
    rw [heq, faceRowA_even m j a b c hs (r / 2) (by omega)]
    exact faceSurface_mem_skin m j _ _ _ hj _
  · have heq : r = 2 * (r / 2) + 1 := by omega
    rw [heq, faceRowA_odd m j a b c hs (r / 2) (by omega)]
    exact faceSub_mem_skin m j _ _ _ hj _ ha (by omega) (by omega)

theorem faceRowB_mem_skin (m j a b c : ℕ) (hs : a + b + c + 2 = m + 2 * j)
    (hj : 1 ≤ j) (hb : 1 ≤ b) (r : ℕ) (hr : r ≤ 2 * a) :
    faceRowPoint 1 m j a b c hs r ∈ skin m j := by
  by_cases hmod : r % 2 = 0
  · have heq : r = 2 * (r / 2) := by omega
    rw [heq, faceRowB_even m j a b c hs (r / 2) (by omega)]
    exact faceSurface_mem_skin m j _ _ _ hj _
  · have heq : r = 2 * (r / 2) + 1 := by omega
    rw [heq, faceRowB_odd m j a b c hs (r / 2) (by omega)]
    exact faceSub_mem_skin m j _ _ _ hj _ (by omega) hb (by omega)

theorem faceRowC_mem_skin (m j a b c : ℕ) (hs : a + b + c + 2 = m + 2 * j)
    (hj : 1 ≤ j) (hc : 1 ≤ c) (r : ℕ) (hr : r ≤ 2 * b) :
    faceRowPoint 2 m j a b c hs r ∈ skin m j := by
  by_cases hmod : r % 2 = 0
  · have heq : r = 2 * (r / 2) := by omega
    rw [heq, faceRowC_even m j a b c hs (r / 2) (by omega)]
    exact faceSurface_mem_skin m j _ _ _ hj _
  · have heq : r = 2 * (r / 2) + 1 := by omega
    rw [heq, faceRowC_odd m j a b c hs (r / 2) (by omega)]
    exact faceSub_mem_skin m j _ _ _ hj _ (by omega) (by omega) hc

def faceRowSegment (kind : Fin 3) (m j a b c : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (length : ℕ) : List Site :=
  List.ofFn (fun r : Fin (2 * length + 1) => faceRowPoint kind m j a b c hs r.val)

theorem faceRowSegment_length (kind : Fin 3) (m j a b c : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (length : ℕ) :
    (faceRowSegment kind m j a b c hs length).length = 2 * length + 1 := List.length_ofFn

theorem faceRowSegment_nodup (kind : Fin 3) (m j a b c : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (length : ℕ) :
    (faceRowSegment kind m j a b c hs length).Nodup := by
  apply List.nodup_ofFn.mpr
  intro r s heq
  exact Fin.ext (faceRowPoint_injective kind m j a b c hs heq)

theorem faceRowSegment_isChain (kind : Fin 3) (m j a b c : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (length : ℕ) :
    (faceRowSegment kind m j a b c hs length).IsChain tetrahedralLattice.Adj := by
  apply List.isChain_ofFn.mpr
  intro r hr
  exact faceRowPoint_adj kind m j a b c hs r

theorem faceRowSegment_mem_iff (kind : Fin 3) (m j a b c : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (length : ℕ) (p : Site) :
    p ∈ faceRowSegment kind m j a b c hs length ↔
      ∃ r ≤ 2 * length, faceRowPoint kind m j a b c hs r = p := by
  constructor
  · intro hp
    obtain ⟨r, hr⟩ := List.mem_ofFn.mp hp
    exact ⟨r.val, by have h := r.isLt; omega, hr⟩
  · rintro ⟨r, hr, heq⟩
    exact List.mem_ofFn.mpr ⟨⟨r, by omega⟩, heq⟩

end ProteinFolding.Tetrahedral
