import ProteinFolding.Cubic.Proofs.GeometryLines

/-! Counting positively oriented edges in a finite integer cube. -/

namespace ProteinFolding.CubicGeometry

open scoped BigOperators

abbrev CubeEdgeIndex (k : Fin 3) (n : ℕ) := ∀ j : Fin 3, Fin (if j = k then n - 1 else n)

def cubeEdgePoint (a : Site) {k : Fin 3} {n : ℕ} (q : CubeEdgeIndex k n) : Site :=
  fun j => a j + (q j).val

theorem cubeEdgePoint_injective (a : Site) (k : Fin 3) (n : ℕ) :
    Function.Injective (cubeEdgePoint a : CubeEdgeIndex k n → Site) := by
  intro q r h
  funext j
  apply Fin.ext
  have hj := congrFun h j
  change a j + ((q j).val : ℤ) = a j + ((r j).val : ℤ) at hj
  omega

theorem positiveEdges_cubeFinset (a : Site) (n : ℕ) (k : Fin 3) :
    positiveEdges (cubeFinset a n) k =
      Finset.univ.image (cubeEdgePoint a : CubeEdgeIndex k n → Site) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hp, hs⟩ := Finset.mem_filter.mp hp
    rw [mem_cubeFinset] at hp hs
    let q : CubeEdgeIndex k n := fun j =>
      ⟨(p j - a j).toNat, by
        have hpj := hp j
        by_cases hj : j = k
        · subst j
          have hsk := hs k
          simp [stepPlus] at hsk
          rw [if_pos rfl]
          apply (Int.toNat_lt (by omega)).mpr
          omega
        · rw [if_neg hj]
          exact (Int.toNat_lt (by omega)).mpr (by omega)⟩
    refine Finset.mem_image.mpr ⟨q, Finset.mem_univ _, ?_⟩
    funext j
    have hpj := hp j
    change a j + ((p j - a j).toNat : ℤ) = p j
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  · intro hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
    have hq (j : Fin 3) : (q j).val < n := by
      have h := (q j).isLt
      change (q j).val < (if j = k then n - 1 else n) at h
      split at h <;> omega
    apply Finset.mem_filter.mpr
    constructor
    · rw [mem_cubeFinset]
      intro j
      change a j ≤ a j + ((q j).val : ℤ) ∧
        a j + ((q j).val : ℤ) < a j + (n : ℤ)
      have h := hq j
      omega
    · rw [mem_cubeFinset]
      intro j
      by_cases hj : j = k
      · subst j
        have hk : (q k).val < n - 1 := by simpa using (q k).isLt
        simp only [stepPlus, Function.update_self, cubeEdgePoint]
        omega
      · have h := hq j
        simp only [stepPlus, Function.update_of_ne hj, cubeEdgePoint]
        omega

theorem cubeEdgeIndex_card (k : Fin 3) (n : ℕ) :
    Fintype.card (CubeEdgeIndex k n) = (n - 1) * n ^ 2 := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk with rfl | rfl | rfl <;>
    simp [CubeEdgeIndex, Fintype.card_pi, Fin.prod_univ_succ, pow_two,
      Nat.mul_comm, Nat.mul_assoc]

theorem positiveEdges_cubeFinset_card (a : Site) (n : ℕ) (k : Fin 3) :
    (positiveEdges (cubeFinset a n) k).card = n ^ 2 * (n - 1) := by
  classical
  rw [positiveEdges_cubeFinset, Finset.card_image_of_injective _
    (cubeEdgePoint_injective a k n)]
  simpa [Nat.mul_comm] using cubeEdgeIndex_card k n

theorem positiveEdgeCount_cubeFinset (a : Site) (n : ℕ) :
    positiveEdgeCount (cubeFinset a n) = 3 * n ^ 2 * (n - 1) := by
  simp [positiveEdgeCount, positiveEdges_cubeFinset_card, Nat.mul_assoc]

end ProteinFolding.CubicGeometry
