import ProteinFolding.Tetrahedral.FarFieldCanonicalRouting

namespace ProteinFolding.Tetrahedral.FarField

def shortCapFold (p q : Site) (h : tetrahedralLattice.Adj p q) : Fold tetrahedralLattice 2 := by
  have hne : p ≠ q := h.ne
  exact {
    pos := fun i => if i.val = 0 then p else q
    injective_pos := by intro i j he; fin_cases i <;> fin_cases j <;> simp_all
    consecutive := by
      intro i j hij
      have hi : i.val = 0 := by have hj := j.isLt; omega
      have hj : j.val = 1 := by omega
      simpa only [hi, hj, ite_true, ite_false, Nat.one_ne_zero] using h }

theorem shortCapFold_first (p q : Site) (h : tetrahedralLattice.Adj p q) (a : Fin 2) (ha : a.val = 0) :
    (shortCapFold p q h).pos a = p := by simp only [shortCapFold, ha, ite_true]

theorem shortCapFold_last (p q : Site) (h : tetrahedralLattice.Adj p q) (a : Fin 2) (ha : a.val = 1) :
    (shortCapFold p q h).pos a = q := by simp only [shortCapFold, ha, Nat.one_ne_zero, ite_false]

theorem shortCapFold_cases (p q : Site) (h : tetrahedralLattice.Adj p q) (a : Fin 2) :
    (shortCapFold p q h).pos a = p ∨ (shortCapFold p q h).pos a = q := by
  by_cases ha : a.val = 0
  · exact Or.inl (shortCapFold_first p q h a ha)
  · exact Or.inr (shortCapFold_last p q h a (by have hb := a.isLt; omega))

theorem dangling_ne_positive_column {m : ℕ} {p : Site} (hp : IsDangling m p)
    (C : DanglingColumn m) (n : ℕ) (hn : 1 ≤ n) : p ≠ C.point n := by
  intro heq
  have h := (C.point_dangling_iff_zero n).1 (heq ▸ hp)
  omega

theorem dangling_rho_bound {m : ℕ} {p : Site} (hp : IsDangling m p) :
    rho (octRadius m) p ≤ 2 * m + 4 := by
  obtain ⟨_, v, hv, hadj⟩ := hp
  have h := skinSolid_rho_bound m 1 (neighbour_of_oct_mem_skinSolid_one m hv hadj)
  change rho (octRadius m) p ≤ 2 * ((m + 2 * 1 : ℕ) : ℤ) at h
  push_cast at h
  omega

/-- Mixed ordinary and borrowed caps. Any distinct dangling caps adjacent to
the second sites of distinct selected columns give the required entry data.
No extra entry-column or entry-entry avoidance assumptions are needed. -/
def mixedCapEntryData {m w : ℕ} (C : Fin w → DanglingColumn m)
    (hseed : Function.Injective (fun i => (C i).seed)) (caps : Fin w → Site)
    (hdangling : ∀ i, IsDangling m (caps i)) (hcaps : Function.Injective caps)
    (hadj : ∀ i, tetrahedralLattice.Adj (caps i) ((C i).point 1)) : CapEntryData (columnsWireData C hseed) where
  caps := caps
  sites := fun _ => 2
  paths := fun i => shortCapFold (caps i) ((C i).point 1) (hadj i)
  sites_pos := by intro i; decide
  sites_le_two := by intro i; decide
  first := fun i a ha => shortCapFold_first _ _ _ a ha
  last := by
    intro i a ha
    have hav : a.val = 1 := by change a.val + 1 = 2 at ha; omega
    exact (shortCapFold_last _ _ _ a hav).trans (columnsWireData.armCap_eq C hseed i).symm
  low := by
    intro i a
    rcases shortCapFold_cases (caps i) ((C i).point 1) (hadj i) a with ha | ha
    · have h := dangling_rho_bound (hdangling i)
      change rho (octRadius m) ((shortCapFold _ _ _).pos a) < 20 * (m : ℤ) + 21
      rw [ha]
      omega
    · have h := skinSolid_rho_bound m 1 (C i).point_one_mem_solid_one
      change rho (octRadius m) ((shortCapFold _ _ _).pos a) < 20 * (m : ℤ) + 21
      rw [ha]
      change rho (octRadius m) ((C i).point 1) ≤ 2 * ((m + 2 * 1 : ℕ) : ℤ) at h
      push_cast at h
      omega
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro s ⟨a, ha⟩ ⟨b, hb⟩
    have heq := ha.trans hb.symm
    rcases shortCapFold_cases (caps i) ((C i).point 1) (hadj i) a with hai | hai
    all_goals rcases shortCapFold_cases (caps j) ((C j).point 1) (hadj j) b with hbj | hbj
    all_goals rw [hai, hbj] at heq
    · exact hij (hcaps heq)
    · exact dangling_ne_positive_column (hdangling i) (C j) 1 (by decide) heq
    · exact dangling_ne_positive_column (hdangling j) (C i) 1 (by decide) heq.symm
    · exact hij (hseed (DanglingColumn.seeds_eq_of_point_eq (C i) (C j) heq))
  columns := by
    intro i j a b heq
    rw [columnsWireData.column_pos_eq] at heq
    rcases shortCapFold_cases (caps i) ((C i).point 1) (hadj i) a with ha | ha
    · exact False.elim (dangling_ne_positive_column (hdangling i) (C j) (1 + b.val) (by omega) (ha.symm.trans heq))
    · have heq' := ha.symm.trans heq
      have hij := hseed (DanglingColumn.seeds_eq_of_point_eq (C i) (C j) heq')
      subst j
      have hb := (C i).point_injective heq'
      have ha0 : a.val ≠ 0 := by
        intro haz
        have hfirst := shortCapFold_first (caps i) ((C i).point 1) (hadj i) a haz
        exact dangling_ne_positive_column (hdangling i) (C i) 1 (by decide) (hfirst.symm.trans ha)
      have hav := a.isLt
      exact ⟨rfl, by change a.val + 1 = 2; omega, by omega⟩

theorem mixedLocalObstacleData {m w : ℕ} (C : Fin w → DanglingColumn m)
    (hseed : Function.Injective (fun i => (C i).seed)) (caps : Fin w → Site)
    (hdangling : ∀ i, IsDangling m (caps i)) (hcaps : Function.Injective caps)
    (hadj : ∀ i, tetrahedralLattice.Adj (caps i) ((C i).point 1))
    (O : Set Site) (hlow : ∀ s ∈ O, rho (octRadius m) s < 20 * (m : ℤ) + 21)
    (hclear : ∀ i n, 1 ≤ n → (C i).point n ∈ O → False) :
    LocalObstacleData (mixedCapEntryData C hseed caps hdangling hcaps hadj) O where
  low := hlow
  entries := by
    intro i a ha
    change (shortCapFold (caps i) ((C i).point 1) (hadj i)).pos a ∈ O at ha
    rcases shortCapFold_cases (caps i) ((C i).point 1) (hadj i) a with he | he
    · exact he
    · rw [he] at ha
      exact False.elim (hclear i 1 (by decide) ha)
  columns := by
    intro i a ha
    rw [columnsWireData.column_pos_eq] at ha
    exact False.elim (hclear i (1 + a.val) (by omega) ha)

end ProteinFolding.Tetrahedral.FarField
