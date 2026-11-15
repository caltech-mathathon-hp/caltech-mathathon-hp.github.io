import Mathlib.Data.Fintype.Fin
import Lean.Elab.Tactic.Omega

/-! A perfect matching of a finite path is forced by its endpoint. This is
the combinatorial uniqueness used for the soundness track in Section 7. -/

namespace ProteinFolding.Tetrahedral

structure PathMatching (n : ℕ) where
  mate : Fin n → Fin n
  involutive : Function.Involutive mate
  adjacent : ∀ i, (mate i).val + 1 = i.val ∨ i.val + 1 = (mate i).val

namespace PathMatching

theorem mate_even {n : ℕ} (p : PathMatching n) (k : ℕ) (hk : 2 * k < n) :
    (p.mate ⟨2 * k, hk⟩).val = 2 * k + 1 := by
  induction k with
  | zero =>
    rcases p.adjacent ⟨2 * 0, hk⟩ with h | h
    · exact False.elim (Nat.succ_ne_zero _ h)
    · exact h.symm
  | succ k ih =>
    have hprev : 2 * k < n := by omega
    have hp := ih hprev
    rcases p.adjacent ⟨2 * (k + 1), hk⟩ with hlow | hhigh
    · dsimp only at hlow
      have heq : p.mate ⟨2 * (k + 1), hk⟩ = p.mate ⟨2 * k, hprev⟩ := by
        apply Fin.ext
        omega
      have h := congrArg Fin.val (p.involutive.injective heq)
      dsimp only at h
      omega
    · exact hhigh.symm

theorem mate_odd {n : ℕ} (p : PathMatching n) (k : ℕ) (hk : 2 * k + 1 < n) :
    (p.mate ⟨2 * k + 1, hk⟩).val = 2 * k := by
  have heven : 2 * k < n := by omega
  have h := p.mate_even k heven
  have heq : p.mate ⟨2 * k, heven⟩ = ⟨2 * k + 1, hk⟩ := Fin.ext h
  have hinv := p.involutive ⟨2 * k, heven⟩
  rw [heq] at hinv
  exact congrArg Fin.val hinv

theorem mate_val {n : ℕ} (p : PathMatching n) (i : Fin n) :
    (p.mate i).val = if i.val % 2 = 0 then i.val + 1 else i.val - 1 := by
  have hsplit := Nat.mod_add_div i.val 2
  have hmod := Nat.mod_lt i.val (by decide : 0 < 2)
  by_cases hi : i.val % 2 = 0
  · have hival : i.val = 2 * (i.val / 2) := by omega
    have hk : 2 * (i.val / 2) < n := by omega
    have heq : i = ⟨2 * (i.val / 2), hk⟩ := Fin.ext hival
    have h := p.mate_even (i.val / 2) hk
    rw [if_pos hi, heq]
    exact h
  · have hival : i.val = 2 * (i.val / 2) + 1 := by omega
    have hk : 2 * (i.val / 2) + 1 < n := by omega
    have heq : i = ⟨2 * (i.val / 2) + 1, hk⟩ := Fin.ext hival
    have h := p.mate_odd (i.val / 2) hk
    rw [if_neg hi]
    rw [heq] at ⊢
    simpa using h

theorem unique {n : ℕ} (p q : PathMatching n) : p.mate = q.mate := by
  funext i
  apply Fin.ext
  rw [p.mate_val, q.mate_val]

theorem length_even {n : ℕ} (p : PathMatching n) : n % 2 = 0 := by
  have hsplit := Nat.mod_add_div n 2
  have hmod := Nat.mod_lt n (by decide : 0 < 2)
  by_contra hn
  have hnpos : 0 < n := by omega
  let i : Fin n := ⟨n - 1, by omega⟩
  have hi : i.val % 2 = 0 := by dsimp [i]; omega
  have h := p.mate_val i
  rw [if_pos hi] at h
  have hbound := (p.mate i).isLt
  dsimp [i] at h
  omega

end PathMatching

end ProteinFolding.Tetrahedral
