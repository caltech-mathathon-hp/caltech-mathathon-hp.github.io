import ProteinFolding.Common.Statement
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Nat.Find

/-! Finite graphs of maximum degree two have a simple spanning path in each
component. This general lemma does not assume any properties of the unfinished
canonical bulk graph. Acyclicity will additionally identify the true ends. -/

namespace ProteinFolding.Tetrahedral

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem path_adjacent_outside_endpoint (hdegree : ∀ v, G.degree v ≤ 2)
    {u v z w : V} (p : G.Walk u v) (hp : p.IsPath)
    (hz : z ∈ p.support) (hw : w ∉ p.support) (hadj : G.Adj z w) : z = u ∨ z = v := by
  obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hz
  by_cases hi0 : i = 0
  · left
    simpa only [hi0, Walk.getVert_zero] using hi.symm
  by_cases hilast : i = p.length
  · right
    simpa only [hilast, Walk.getVert_length] using hi.symm
  have hiPos : 0 < i := by omega
  have hiLt : i < p.length := by omega
  let l := p.getVert (i - 1)
  let r := p.getVert (i + 1)
  have hl : G.Adj z l := by
    have h := (p.adj_getVert_succ (show i - 1 < p.length by omega)).symm
    rw [show i - 1 + 1 = i by omega, hi] at h
    exact h
  have hr : G.Adj z r := by
    have h := p.adj_getVert_succ hiLt
    rw [hi] at h
    exact h
  have hlr : l ≠ r := by
    intro heq
    have h := hp.getVert_injOn (show i - 1 ≤ p.length by omega)
      (show i + 1 ≤ p.length by omega) heq
    omega
  have hlw : l ≠ w := by
    intro heq
    exact hw (heq ▸ p.getVert_mem_support (i - 1))
  have hrw : r ≠ w := by
    intro heq
    exact hw (heq ▸ p.getVert_mem_support (i + 1))
  have hsub : ({l, r, w} : Finset V) ⊆ G.neighborFinset z := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact (G.mem_neighborFinset z l).mpr hl
    · exact (G.mem_neighborFinset z r).mpr hr
    · exact (G.mem_neighborFinset z _).mpr hadj
  have hcard := Finset.card_le_card hsub
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hcard
  have hsize : ({l, r, w} : Finset V).card = 3 := by simp [hlr, hlw, hrw]
  rw [hsize] at hcard
  have hbound := hdegree z
  omega

structure MaximalComponentPath (c : V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath
  reachable_start : G.Reachable c start
  maximal : ∀ {a b : V} (q : G.Walk a b), G.Reachable c a → q.IsPath → q.length ≤ walk.length

theorem exists_maximalComponentPath (c : V) : Nonempty (MaximalComponentPath G c) := by
  classical
  let P : ℕ → Prop := fun n => ∃ a b : V, ∃ p : G.Walk a b,
    G.Reachable c a ∧ p.IsPath ∧ p.length = n
  have hzero : P 0 := ⟨c, c, .nil, .refl c, by simp, rfl⟩
  have hspec : P (Nat.findGreatest P (Fintype.card V)) :=
    Nat.findGreatest_spec (Nat.zero_le _) hzero
  obtain ⟨a, b, p, hreach, hp, hlen⟩ := hspec
  refine ⟨⟨a, b, p, hp, hreach, ?_⟩⟩
  intro d e q hd hq
  rw [hlen]
  apply Nat.le_findGreatest (le_of_lt hq.length_lt)
  exact ⟨d, e, q, hd, hq, rfl⟩

theorem MaximalComponentPath.neighbour_closed {c : V} (p : MaximalComponentPath G c)
    (hdegree : ∀ v, G.degree v ≤ 2) {z w : V}
    (hz : z ∈ p.walk.support) (hadj : G.Adj z w) : w ∈ p.walk.support := by
  by_contra hw
  rcases path_adjacent_outside_endpoint G hdegree p.walk p.isPath hz hw hadj with h | h
  · subst z
    have hq : (Walk.cons hadj.symm p.walk).IsPath := p.isPath.cons hw
    have hr : G.Reachable c w := p.reachable_start.trans ⟨Walk.cons hadj .nil⟩
    have hmax := p.maximal (Walk.cons hadj.symm p.walk) hr hq
    simp only [Walk.length_cons] at hmax
    omega
  · subst z
    have hq := p.isPath.concat hw hadj
    have hmax := p.maximal (p.walk.concat hadj) p.reachable_start hq
    simp only [Walk.length_concat] at hmax
    omega

theorem MaximalComponentPath.support_iff_reachable {c : V} (p : MaximalComponentPath G c)
    (hdegree : ∀ v, G.degree v ≤ 2) (w : V) :
    w ∈ p.walk.support ↔ G.Reachable c w := by
  constructor
  · intro hw
    obtain ⟨q, _, _⟩ := p.walk.mem_support_iff_exists_append.mp hw
    exact p.reachable_start.trans ⟨q⟩
  · intro hr
    have hclosed : ∀ {a b : V} (q : G.Walk a b), a ∈ p.walk.support → b ∈ p.walk.support := by
      intro a b q
      induction q with
      | nil => exact id
      | cons hadj q ih =>
        intro ha
        exact ih (p.neighbour_closed G hdegree ha hadj)
    obtain ⟨q⟩ := p.reachable_start.symm.trans hr
    exact hclosed q p.walk.start_mem_support

theorem exists_component_spanning_path (hdegree : ∀ v, G.degree v ≤ 2) (c : V) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsPath ∧
      ∀ w, w ∈ p.support ↔ G.Reachable c w := by
  obtain ⟨p⟩ := exists_maximalComponentPath G c
  exact ⟨p.start, p.finish, p.walk, p.isPath, p.support_iff_reachable G hdegree⟩

/-- Convert a checked simple graph path to the same injective finite Fold
used for proteins. All path vertices, including both ends, are retained. -/
def foldOfSimplePath {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    Fold G (p.length + 1) where
  pos i := p.getVert i.val
  injective_pos := by
    intro i j hij
    apply Fin.ext
    have hi : i.val ≤ p.length := by have := i.isLt; omega
    have hj : j.val ≤ p.length := by have := j.isLt; omega
    exact hp.getVert_injOn hi hj hij
  consecutive := by
    intro i j hij
    rw [← hij]
    exact p.adj_getVert_succ (by have := j.isLt; omega)

end ProteinFolding.Tetrahedral
