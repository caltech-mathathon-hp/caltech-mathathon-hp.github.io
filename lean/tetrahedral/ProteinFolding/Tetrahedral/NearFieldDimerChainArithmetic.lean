import ProteinFolding.Tetrahedral.WordPieces

/-! The alternating order of H pairs in a concrete edge dimer chain. -/

namespace ProteinFolding.Tetrahedral.NearField

def dimerFlip (reverse : Bool) (j : ℕ) : ℕ := (j + if reverse then 1 else 0) % 2

def dimerHIndex (base : ℕ) (reverse : Bool) (j : ℕ) (s : Fin 2) : ℕ :=
  base + 2 * j + if s = 0 then dimerFlip reverse j else 1 - dimerFlip reverse j

def dimerLinkIndex (base : ℕ) (reverse : Bool) (j : ℕ) : ℕ :=
  base + 2 * j + (1 - dimerFlip reverse j)

theorem dimerFlip_lt_two (reverse : Bool) (j : ℕ) : dimerFlip reverse j < 2 :=
  Nat.mod_lt _ (by decide)

theorem dimerHIndex_bounds (base : ℕ) (reverse : Bool) (j : ℕ) (s : Fin 2) :
    base + 2 * j ≤ dimerHIndex base reverse j s ∧
      dimerHIndex base reverse j s ≤ base + 2 * j + 1 := by
  have h := dimerFlip_lt_two reverse j
  fin_cases s <;> dsimp [dimerHIndex] <;> omega

theorem dimerLinkIndex_bounds (base : ℕ) (reverse : Bool) (j : ℕ) :
    base + 2 * j ≤ dimerLinkIndex base reverse j ∧
      dimerLinkIndex base reverse j ≤ base + 2 * j + 1 := by
  have h := dimerFlip_lt_two reverse j
  unfold dimerLinkIndex
  omega

theorem dimerHIndex_last (base : ℕ) (reverse : Bool) (j : ℕ) :
    dimerHIndex base reverse j 1 = dimerLinkIndex base reverse j := rfl

theorem dimerLinkIndex_next (base : ℕ) (reverse : Bool) (j : ℕ) :
    dimerHIndex base reverse (j + 1) 0 = dimerLinkIndex base reverse j + 2 := by
  cases reverse <;> dsimp [dimerHIndex, dimerLinkIndex, dimerFlip] <;> omega

theorem dimerHIndex_adjacent (base : ℕ) (reverse : Bool) (j : ℕ) :
    dimerHIndex base reverse j 0 + 1 = dimerHIndex base reverse j 1 ∨
      dimerHIndex base reverse j 1 + 1 = dimerHIndex base reverse j 0 := by
  have h := dimerFlip_lt_two reverse j
  dsimp [dimerHIndex]
  omega

theorem dimerHIndex_injective (base : ℕ) (reverse : Bool) :
    Function.Injective (fun js : ℕ × Fin 2 => dimerHIndex base reverse js.1 js.2) := by
  rintro ⟨j, s⟩ ⟨k, t⟩ heq
  change dimerHIndex base reverse j s = dimerHIndex base reverse k t at heq
  have hjs := dimerHIndex_bounds base reverse j s
  have hkt := dimerHIndex_bounds base reverse k t
  have hjk : j = k := by omega
  subst k
  have hj := dimerFlip_lt_two reverse j
  fin_cases s <;> fin_cases t <;> dsimp [dimerHIndex] at heq
  all_goals first
    | rfl
    | (exfalso; omega)

theorem dimerLink_endpoints_ne (base : ℕ) (reverse : Bool) (j k : ℕ) (hne : j ≠ k)
    (a b : Fin 2) :
    dimerLinkIndex base reverse j + 2 * a.val ≠ dimerLinkIndex base reverse k + 2 * b.val := by
  intro heq
  cases reverse <;> fin_cases a <;> fin_cases b <;> dsimp [dimerLinkIndex, dimerFlip] at heq <;> omega

theorem dimerFirst_ne_link_endpoint (base : ℕ) (reverse : Bool) (j : ℕ) (a : Fin 2) :
    dimerHIndex base reverse 0 0 ≠ dimerLinkIndex base reverse j + 2 * a.val := by
  intro heq
  cases reverse <;> fin_cases a <;> dsimp [dimerHIndex, dimerLinkIndex, dimerFlip] at heq <;> omega

theorem dimerLast_ne_link_endpoint (base : ℕ) (reverse : Bool) (q j : ℕ)
    (hj : j < q) (a : Fin 2) :
    dimerHIndex base reverse q 1 ≠ dimerLinkIndex base reverse j + 2 * a.val := by
  intro heq
  cases reverse <;> fin_cases a <;> dsimp [dimerHIndex, dimerLinkIndex, dimerFlip] at heq <;> omega

theorem dimerFirst_ne_last (base : ℕ) (reverse : Bool) (q : ℕ) :
    dimerHIndex base reverse 0 0 ≠ dimerHIndex base reverse q 1 := by
  intro heq
  cases reverse <;> dsimp [dimerHIndex, dimerFlip] at heq <;> omega

end ProteinFolding.Tetrahedral.NearField
