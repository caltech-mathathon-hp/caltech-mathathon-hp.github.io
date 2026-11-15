import ProteinFolding.Tetrahedral.NearFieldCrossTethers

/-! A uniform family of all 2(K+1) entry and exit tether routes. Each
route is an actual self-avoiding Fold of its prescribed literal P count;
all distinct routes are disjoint and stay outside the H octahedron. -/

namespace ProteinFolding.Tetrahedral.NearField

abbrev TetherIndex (p : ConstructionParameters) := Bool × Fin (p.bins + 1)

def tetherCount (p : ConstructionParameters) (t : TetherIndex p) : ℕ :=
  if t.1 then p.exitTether t.2.val else p.entryTether t.2.val

def tetherFold (p : ConstructionParameters) (t : TetherIndex p) :
    Fold tetrahedralLattice (tetherCount p t) := by
  rcases t with ⟨b, k⟩
  cases b
  · exact entryTetherFold p k.val (Nat.le_of_lt_succ k.isLt)
  · exact exitTetherFold p k.val (Nat.le_of_lt_succ k.isLt)

def tetherSource (p : ConstructionParameters) (t : TetherIndex p) : Site :=
  if t.1 then (exitSourceColumn p t.2.val (Nat.le_of_lt_succ t.2.isLt)).seed
  else (faceDanglingColumn p.side (entryAnchorA p t.2.val) (3 * (t.2.val + 1)) 0
    (entryAnchor_equation p t.2.val (Nat.le_of_lt_succ t.2.isLt))).seed

def tetherTarget (p : ConstructionParameters) (t : TetherIndex p) : Site :=
  if t.1 then (exitTargetColumn p t.2.val).seed
  else (entryTargetColumn p t.2.val (Nat.le_of_lt_succ t.2.isLt)).seed

theorem tetherCount_odd (p : ConstructionParameters) (t : TetherIndex p) :
    tetherCount p t % 2 = 1 := by
  rcases t with ⟨b, k⟩
  cases b
  · exact p.entryTether_odd k.val
  · exact p.exitTether_odd k.val

theorem tetherFold_first (p : ConstructionParameters) (t : TetherIndex p)
    (i : Fin (tetherCount p t)) (hi : i.val = 0) : (tetherFold p t).pos i = tetherSource p t := by
  rcases t with ⟨b, k⟩
  cases b
  · exact entryTetherFold_first p k.val (Nat.le_of_lt_succ k.isLt) i hi
  · exact exitTetherFold_first p k.val (Nat.le_of_lt_succ k.isLt) i hi

theorem tetherFold_last (p : ConstructionParameters) (t : TetherIndex p)
    (i : Fin (tetherCount p t)) (hi : i.val + 1 = tetherCount p t) :
    (tetherFold p t).pos i = tetherTarget p t := by
  rcases t with ⟨b, k⟩
  cases b
  · exact entryTetherFold_last p k.val (Nat.le_of_lt_succ k.isLt) i hi
  · exact exitTetherFold_last p k.val (Nat.le_of_lt_succ k.isLt) i hi

theorem tetherFold_outside (p : ConstructionParameters) (t : TetherIndex p)
    (i : Fin (tetherCount p t)) : (tetherFold p t).pos i ∉ octahedron p.side := by
  rcases t with ⟨b, k⟩
  cases b
  · exact entryTetherFold_outside p k.val (Nat.le_of_lt_succ k.isLt) i
  · exact exitTetherFold_outside p k.val (Nat.le_of_lt_succ k.isLt) i

theorem tetherFold_mem_solid (p : ConstructionParameters) (t : TetherIndex p)
    (i : Fin (tetherCount p t)) : (tetherFold p t).pos i ∈ skinSolid p.side (2 * p.bins + 3) := by
  rcases t with ⟨b, k⟩
  cases b
  · exact entryTetherFold_mem_solid p k.val (Nat.le_of_lt_succ k.isLt) i
  · exact exitTetherFold_mem_solid p k.val (Nat.le_of_lt_succ k.isLt) i

theorem tetherFolds_disjoint (p : ConstructionParameters) (t u : TetherIndex p) (hne : t ≠ u)
    (i : Fin (tetherCount p t)) (j : Fin (tetherCount p u)) :
    (tetherFold p t).pos i ≠ (tetherFold p u).pos j := by
  rcases t with ⟨b, k⟩
  rcases u with ⟨c, l⟩
  have hk : k.val ≤ p.bins := Nat.le_of_lt_succ k.isLt
  have hl : l.val ≤ p.bins := Nat.le_of_lt_succ l.isLt
  cases b <;> cases c
  · exact entryTethers_disjoint p k.val l.val hk hl
      (fun h => hne (by congr 1; exact Fin.ext h)) i j
  · exact entry_exit_tethers_disjoint p k.val l.val hk hl i j
  · exact (entry_exit_tethers_disjoint p l.val k.val hl hk j i).symm
  · exact exitTethers_disjoint p k.val l.val hk hl
      (fun h => hne (by congr 1; exact Fin.ext h)) i j

theorem tetherIndex_card (p : ConstructionParameters) : Fintype.card (TetherIndex p) = 2 * (p.bins + 1) := by
  simp [TetherIndex]

end ProteinFolding.Tetrahedral.NearField
