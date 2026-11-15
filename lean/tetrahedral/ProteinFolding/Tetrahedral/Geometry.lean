import ProteinFolding.Tetrahedral.Statement
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# The four neighbours and the bipartition of the diamond lattice

These are the first geometric facts of Section 2 of the manuscript. The
coordinate congruences, adjacency and neighbour enumeration are proved for
arbitrary sites, including sites with negative coordinates.
-/

namespace ProteinFolding.Tetrahedral

theorem bondVector_parity (d : Fin 4) (k : Fin 3) : bondVector d k % 2 = 1 := by
  revert d k
  decide

theorem bondVector_sum_mod (d : Fin 4) : coordinateSum (bondVector d) % 4 = 3 := by
  revert d
  decide

theorem coordinateSum_add (p q : Coordinates) :
    coordinateSum (fun k => p k + q k) = coordinateSum p + coordinateSum q := by
  simp only [coordinateSum]
  omega

theorem coordinateSum_sub (p q : Coordinates) :
    coordinateSum (fun k => p k - q k) = coordinateSum p - coordinateSum q := by
  simp only [coordinateSum]
  omega

theorem add_bondVector_inB (p : Coordinates) (h : InASublattice p) (d : Fin 4) :
    InBSublattice (fun k => p k + bondVector d k) := by
  constructor
  · intro k
    change (p k + bondVector d k) % 2 = 1
    rw [Int.add_emod, h.1 k, bondVector_parity]
    decide
  · change coordinateSum (fun k => p k + bondVector d k) % 4 = 3
    rw [coordinateSum_add, Int.add_emod, h.2, bondVector_sum_mod]
    decide

theorem sub_bondVector_inA (p : Coordinates) (h : InBSublattice p) (d : Fin 4) :
    InASublattice (fun k => p k - bondVector d k) := by
  constructor
  · intro k
    change (p k - bondVector d k) % 2 = 0
    rw [Int.sub_emod, h.1 k, bondVector_parity]
    decide
  · change coordinateSum (fun k => p k - bondVector d k) % 4 = 0
    rw [coordinateSum_sub, Int.sub_emod, h.2, bondVector_sum_mod]
    decide

/-- A site has exactly one of the two sublattice colours. -/
theorem inB_iff_not_inA (p : Site) : InBSublattice p.val ↔ ¬ InASublattice p.val := by
  constructor
  · intro hB hA
    exact sublattices_disjoint p.val hA hB
  · intro hA
    exact p.property.resolve_left hA

/-- Every edge crosses the A/B bipartition. -/
theorem adj_sublattices {p q : Site} (h : tetrahedralLattice.Adj p q) :
    (InASublattice p.val ∧ InBSublattice q.val) ∨
      (InBSublattice p.val ∧ InASublattice q.val) := by
  rcases h with h | h
  · exact Or.inl ⟨h.1, h.2.1⟩
  · exact Or.inr ⟨h.2.1, h.1⟩

theorem adj_not_same_sublattice {p q : Site} (h : tetrahedralLattice.Adj p q) :
    InASublattice p.val ↔ ¬ InASublattice q.val := by
  rcases adj_sublattices h with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact iff_of_true hp ((inB_iff_not_inA q).mp hq)
  · exact iff_of_false ((inB_iff_not_inA p).mp hp) (not_not_intro hq)

/-- The four actual neighbours, adding t_d at A-sites and subtracting it at B-sites. -/
def step (p : Site) (d : Fin 4) : Site :=
  if h : InASublattice p.val then
    ⟨fun k => p.val k + bondVector d k, Or.inr (add_bondVector_inB p.val h d)⟩
  else
    ⟨fun k => p.val k - bondVector d k,
      Or.inl (sub_bondVector_inA p.val ((inB_iff_not_inA p).mpr h) d)⟩

theorem step_val_of_A (p : Site) (h : InASublattice p.val) (d : Fin 4) :
    (step p d).val = fun k => p.val k + bondVector d k := by
  simp [step, h]

theorem step_val_of_B (p : Site) (h : InBSublattice p.val) (d : Fin 4) :
    (step p d).val = fun k => p.val k - bondVector d k := by
  simp [step, (inB_iff_not_inA p).mp h]

theorem step_adj (p : Site) (d : Fin 4) : tetrahedralLattice.Adj p (step p d) := by
  by_cases h : InASublattice p.val
  · apply Or.inl
    refine ⟨h, ?_, d, ?_⟩
    · rw [step_val_of_A p h d]
      exact add_bondVector_inB p.val h d
    · intro k
      exact congrFun (step_val_of_A p h d) k
  · have hB := (inB_iff_not_inA p).mpr h
    apply Or.inr
    refine ⟨?_, hB, d, ?_⟩
    · rw [step_val_of_B p hB d]
      exact sub_bondVector_inA p.val hB d
    · intro k
      rw [show (step p d).val k = p.val k - bondVector d k from
        congrFun (step_val_of_B p hB d) k]
      omega

theorem bondVector_injective : Function.Injective bondVector := by decide

theorem step_injective (p : Site) : Function.Injective (step p) := by
  intro d e h
  apply bondVector_injective
  funext k
  have hk := congrArg (fun q : Site => q.val k) h
  by_cases hp : InASublattice p.val
  · simp only [step_val_of_A p hp] at hk
    omega
  · have hB := (inB_iff_not_inA p).mpr hp
    simp only [step_val_of_B p hB] at hk
    omega

/-- The enumeration is exhaustive, not merely a list of four possible edges. -/
theorem adj_iff_exists_step (p q : Site) :
    tetrahedralLattice.Adj p q ↔ ∃ d : Fin 4, step p d = q := by
  constructor
  · intro h
    rcases h with ⟨hp, hq, d, hd⟩ | ⟨hq, hp, d, hd⟩
    · refine ⟨d, Subtype.ext ?_⟩
      rw [step_val_of_A p hp d]
      exact (funext hd).symm
    · refine ⟨d, Subtype.ext ?_⟩
      rw [step_val_of_B p hp d]
      funext k
      have hk := hd k
      omega
  · rintro ⟨d, rfl⟩
    exact step_adj p d

/-- The four distinct neighbours as a finite set. -/
def neighbours (p : Site) : Finset Site := Finset.univ.image (step p)

@[simp] theorem mem_neighbours (p q : Site) :
    q ∈ neighbours p ↔ tetrahedralLattice.Adj p q := by
  simp [neighbours, adj_iff_exists_step]

@[simp] theorem card_neighbours (p : Site) : (neighbours p).card = 4 := by
  rw [neighbours, Finset.card_image_of_injective _ (step_injective p)]
  decide

/-- The infinite graph is 4-regular, stated without a local-finiteness instance. -/
noncomputable def neighbourEquiv (p : Site) : Fin 4 ≃ {q : Site // tetrahedralLattice.Adj p q} where
  toFun d := ⟨step p d, step_adj p d⟩
  invFun q := Classical.choose ((adj_iff_exists_step p q.val).mp q.property)
  left_inv d := step_injective p
    (Classical.choose_spec ((adj_iff_exists_step p (step p d)).mp (step_adj p d)))
  right_inv q := Subtype.ext
    (Classical.choose_spec ((adj_iff_exists_step p q.val).mp q.property))

end ProteinFolding.Tetrahedral
