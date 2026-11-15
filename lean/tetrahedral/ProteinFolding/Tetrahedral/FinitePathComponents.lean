import ProteinFolding.Tetrahedral.FinitePathCoverEnds

/-! One disjoint finite Fold per component, with an exact total vertex count.
These are existence/serialization lemmas; they make no polynomial-time claim. -/

namespace ProteinFolding.Tetrahedral

open SimpleGraph
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def componentRepresentative (c : G.ConnectedComponent) : V :=
  Classical.choose c.exists_rep

theorem componentRepresentative_spec (c : G.ConnectedComponent) :
    G.connectedComponentMk (componentRepresentative G c) = c :=
  Classical.choose_spec c.exists_rep

noncomputable def componentMaxPath (c : G.ConnectedComponent) :
    MaximalComponentPath G (componentRepresentative G c) :=
  Classical.choice (exists_maximalComponentPath G (componentRepresentative G c))

noncomputable def componentVertices (c : G.ConnectedComponent) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => G.connectedComponentMk v = c)

@[simp] theorem mem_componentVertices (c : G.ConnectedComponent) (v : V) :
    v ∈ componentVertices G c ↔ G.connectedComponentMk v = c := by
  classical
  simp [componentVertices]

theorem componentMaxPath_support (hdegree : ∀ v, G.degree v ≤ 2)
    (c : G.ConnectedComponent) (v : V) :
    v ∈ (componentMaxPath G c).walk.support ↔ G.connectedComponentMk v = c := by
  rw [(componentMaxPath G c).support_iff_reachable G hdegree, ← ConnectedComponent.eq,
    componentRepresentative_spec]
  exact eq_comm

theorem componentMaxPath_support_finset (hdegree : ∀ v, G.degree v ≤ 2)
    (c : G.ConnectedComponent) :
    (componentMaxPath G c).walk.support.toFinset = componentVertices G c := by
  ext v
  simp only [List.mem_toFinset, mem_componentVertices]
  exact componentMaxPath_support G hdegree c v

theorem componentMaxPath_vertex_count (hdegree : ∀ v, G.degree v ≤ 2)
    (c : G.ConnectedComponent) :
    (componentMaxPath G c).walk.length + 1 = (componentVertices G c).card := by
  rw [← componentMaxPath_support_finset G hdegree c,
    List.toFinset_card_of_nodup (componentMaxPath G c).isPath.support_nodup,
    Walk.length_support]

theorem foldOfSimplePath_exists_pos {u v : V} (p : G.Walk u v) (hp : p.IsPath) (w : V) :
    (∃ i, (foldOfSimplePath G p hp).pos i = w) ↔ w ∈ p.support := by
  constructor
  · rintro ⟨i, hi⟩
    change p.getVert i.val = w at hi
    exact hi ▸ p.getVert_mem_support i.val
  · intro hw
    obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hw
    exact ⟨⟨i, by omega⟩, hi⟩

noncomputable def componentFold (c : G.ConnectedComponent) :
    Fold G ((componentMaxPath G c).walk.length + 1) :=
  foldOfSimplePath G (componentMaxPath G c).walk (componentMaxPath G c).isPath

theorem componentFold_covers (hdegree : ∀ v, G.degree v ≤ 2)
    (c : G.ConnectedComponent) (v : V) :
    (∃ i, (componentFold G c).pos i = v) ↔ G.connectedComponentMk v = c := by
  rw [componentFold, foldOfSimplePath_exists_pos]
  exact componentMaxPath_support G hdegree c v

theorem componentFolds_disjoint (hdegree : ∀ v, G.degree v ≤ 2)
    {c d : G.ConnectedComponent} (hne : c ≠ d) :
    Disjoint (Set.range (componentFold G c).pos) (Set.range (componentFold G d).pos) := by
  apply Set.disjoint_left.mpr
  rintro v ⟨i, hi⟩ ⟨j, hj⟩
  have hc := (componentFold_covers G hdegree c v).mp ⟨i, hi⟩
  have hd := (componentFold_covers G hdegree d v).mp ⟨j, hj⟩
  exact hne (hc.symm.trans hd)

local instance : Finite G.ConnectedComponent :=
  Finite.of_surjective G.connectedComponentMk (fun c => c.exists_rep)

noncomputable local instance : Fintype G.ConnectedComponent := Fintype.ofFinite _

theorem sum_componentVertices_card :
    (∑ c : G.ConnectedComponent, (componentVertices G c).card) = Fintype.card V := by
  classical
  simp only [componentVertices, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem sum_componentPath_vertex_count (hdegree : ∀ v, G.degree v ≤ 2) :
    (∑ c : G.ConnectedComponent, ((componentMaxPath G c).walk.length + 1)) = Fintype.card V := by
  simp_rw [componentMaxPath_vertex_count G hdegree]
  exact sum_componentVertices_card G

theorem componentFold_end_degrees (hdegree : ∀ v, G.degree v ≤ 2) (hacyclic : G.IsAcyclic)
    (hnonzero : ∀ v, 1 ≤ G.degree v) (c : G.ConnectedComponent) :
    G.degree (componentMaxPath G c).start = 1 ∧
      G.degree (componentMaxPath G c).finish = 1 :=
  (componentMaxPath G c).endpoint_degrees G hdegree hacyclic hnonzero

end ProteinFolding.Tetrahedral
