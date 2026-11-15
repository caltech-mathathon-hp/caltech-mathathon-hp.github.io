import ProteinFolding.Tetrahedral.Geometry

/-! Finite self-avoiding paths cut from injective integer curves, and gluing
at a single shared endpoint. No path-existence premise is hidden in these
constructors: their positions and every edge are explicit. -/

namespace ProteinFolding.Tetrahedral.FarField

def intervalFold (F : ℤ → Site) (hF : Function.Injective F)
    (hstep : ∀ t, tetrahedralLattice.Adj (F t) (F (t + 1)))
    (a : ℤ) (edges : ℕ) (forward : Bool) : Fold tetrahedralLattice (edges + 1) where
  pos i := F (if forward then a + i.val else a - i.val)
  injective_pos := by
    intro i j h
    have h' := hF h
    apply Fin.ext
    cases forward <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h' <;> omega
  consecutive i j hij := by
    cases forward
    · simp only [Bool.false_eq_true, ite_false]
      have h : a - (j.val : ℤ) + 1 = a - i.val := by omega
      simpa only [h] using (hstep (a - j.val)).symm
    · simp only [ite_true]
      have h : a + (i.val : ℤ) + 1 = a + j.val := by omega
      simpa only [h] using hstep (a + i.val)

theorem intervalFold_first (F : ℤ → Site) (hF : Function.Injective F)
    (hstep : ∀ t, tetrahedralLattice.Adj (F t) (F (t + 1)))
    (a : ℤ) (edges : ℕ) (forward : Bool) (i : Fin (edges + 1)) (hi : i.val = 0) :
    (intervalFold F hF hstep a edges forward).pos i = F a := by
  cases forward <;> simp [intervalFold, hi]

theorem intervalFold_last (F : ℤ → Site) (hF : Function.Injective F)
    (hstep : ∀ t, tetrahedralLattice.Adj (F t) (F (t + 1)))
    (a : ℤ) (edges : ℕ) (forward : Bool) (i : Fin (edges + 1)) (hi : i.val = edges) :
    (intervalFold F hF hstep a edges forward).pos i =
      F (if forward then a + edges else a - edges) := by
  cases forward <;> simp [intervalFold, hi]

def glue {n m : ℕ} (f : Fold tetrahedralLattice n) (g : Fold tetrahedralLattice m)
    (hn : 0 < n) (hm : 0 < m)
    (hjoin : f.pos ⟨n - 1, by omega⟩ = g.pos ⟨0, hm⟩)
    (hinter : ∀ i j, f.pos i = g.pos j → i.val + 1 = n ∧ j.val = 0) :
    Fold tetrahedralLattice (n + m - 1) where
  pos i := if h : i.val < n then f.pos ⟨i.val, h⟩ else
    g.pos ⟨i.val - n + 1, by have hi := i.isLt; omega⟩
  injective_pos := by
    intro i j hij
    apply Fin.ext
    dsimp only at hij
    split_ifs at hij with hi hj hj
    · have h := f.injective_pos hij
      exact congrArg (fun k : Fin n => k.val) h
    · have h := hinter _ _ hij
      change i.val + 1 = n ∧ j.val - n + 1 = 0 at h
      omega
    · have h := hinter _ _ hij.symm
      change j.val + 1 = n ∧ i.val - n + 1 = 0 at h
      omega
    · have h := g.injective_pos hij
      have h' := congrArg (fun k : Fin m => k.val) h
      change i.val - n + 1 = j.val - n + 1 at h'
      omega
  consecutive i j hij := by
    split_ifs with hi hj hj
    · exact f.consecutive _ _ hij
    · have hi' : i.val = n - 1 := by omega
      have hj' : j.val - n + 1 = 1 := by omega
      have hfi : f.pos ⟨i.val, hi⟩ = g.pos ⟨0, hm⟩ := by
        simpa only [hi'] using hjoin
      rw [hfi]
      apply g.consecutive
      change 0 + 1 = j.val - n + 1
      omega
    · omega
    · apply g.consecutive
      change (i.val - n + 1) + 1 = j.val - n + 1
      omega

theorem glue_first {n m : ℕ} (f : Fold tetrahedralLattice n) (g : Fold tetrahedralLattice m)
    (hn : 0 < n) (hm : 0 < m)
    (hjoin : f.pos ⟨n - 1, by omega⟩ = g.pos ⟨0, hm⟩)
    (hinter : ∀ i j, f.pos i = g.pos j → i.val + 1 = n ∧ j.val = 0)
    (i : Fin (n + m - 1)) (hi : i.val = 0) :
    (glue f g hn hm hjoin hinter).pos i = f.pos ⟨0, hn⟩ := by
  simp [glue, hi, hn]

theorem glue_last {n m : ℕ} (f : Fold tetrahedralLattice n) (g : Fold tetrahedralLattice m)
    (hn : 0 < n) (hm : 0 < m)
    (hjoin : f.pos ⟨n - 1, by omega⟩ = g.pos ⟨0, hm⟩)
    (hinter : ∀ i j, f.pos i = g.pos j → i.val + 1 = n ∧ j.val = 0)
    (i : Fin (n + m - 1)) (hi : i.val + 1 = n + m - 1) :
    (glue f g hn hm hjoin hinter).pos i = g.pos ⟨m - 1, by omega⟩ := by
  dsimp only [glue]
  split_ifs with h
  · have hm' : m = 1 := by omega
    have hi' : i.val = n - 1 := by omega
    subst m
    simpa only [hi', Nat.sub_self] using hjoin
  · apply congrArg g.pos
    apply Fin.ext
    change i.val - n + 1 = m - 1
    omega

end ProteinFolding.Tetrahedral.FarField
