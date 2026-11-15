import ProteinFolding.Tetrahedral.FinitePathCover

/-! In an acyclic degree-two graph the spanning component paths have the
actual degree-one ends, rather than artificial cuts in a cycle. -/

namespace ProteinFolding.Tetrahedral

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem path_neighbour_in_support_eq_snd (hacyclic : G.IsAcyclic)
    {u v w : V} (p : G.Walk u v) (hp : p.IsPath)
    (hw : w ∈ p.support) (hadj : G.Adj u w) : w = p.snd := by
  obtain ⟨q, r, hq, _, hpqr⟩ := hp.mem_support_iff_exists_append.mp hw
  have hsingle : (Walk.cons hadj (.nil : G.Walk w w)).IsPath := by simp [hadj.ne]
  have hqeq : q = Walk.cons hadj .nil :=
    congrArg Subtype.val (hacyclic.path_unique ⟨q, hq⟩ ⟨_, hsingle⟩)
  rw [hpqr, hqeq]
  simp only [Walk.cons_append, Walk.nil_append, Walk.snd_cons]

theorem MaximalComponentPath.start_degree_le_one {c : V} (p : MaximalComponentPath G c)
    (hdegree : ∀ v, G.degree v ≤ 2) (hacyclic : G.IsAcyclic) :
    G.degree p.start ≤ 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have hax := (G.mem_neighborFinset p.start x).mp hx
  have hay := (G.mem_neighborFinset p.start y).mp hy
  have hxsupport := p.neighbour_closed G hdegree p.walk.start_mem_support hax
  have hysupport := p.neighbour_closed G hdegree p.walk.start_mem_support hay
  exact (path_neighbour_in_support_eq_snd G hacyclic p.walk p.isPath hxsupport hax).trans
    (path_neighbour_in_support_eq_snd G hacyclic p.walk p.isPath hysupport hay).symm

theorem MaximalComponentPath.finish_degree_le_one {c : V} (p : MaximalComponentPath G c)
    (hdegree : ∀ v, G.degree v ≤ 2) (hacyclic : G.IsAcyclic) :
    G.degree p.finish ≤ 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have hax := (G.mem_neighborFinset p.finish x).mp hx
  have hay := (G.mem_neighborFinset p.finish y).mp hy
  have hxsupport : x ∈ p.walk.reverse.support := by
    simpa only [Walk.support_reverse, List.mem_reverse] using
      p.neighbour_closed G hdegree p.walk.end_mem_support hax
  have hysupport : y ∈ p.walk.reverse.support := by
    simpa only [Walk.support_reverse, List.mem_reverse] using
      p.neighbour_closed G hdegree p.walk.end_mem_support hay
  exact (path_neighbour_in_support_eq_snd G hacyclic p.walk.reverse p.isPath.reverse hxsupport hax).trans
    (path_neighbour_in_support_eq_snd G hacyclic p.walk.reverse p.isPath.reverse hysupport hay).symm

theorem MaximalComponentPath.endpoint_degrees {c : V} (p : MaximalComponentPath G c)
    (hdegree : ∀ v, G.degree v ≤ 2) (hacyclic : G.IsAcyclic)
    (hnonzero : ∀ v, 1 ≤ G.degree v) :
    G.degree p.start = 1 ∧ G.degree p.finish = 1 := by
  have hs := p.start_degree_le_one G hdegree hacyclic
  have hf := p.finish_degree_le_one G hdegree hacyclic
  have hs' := hnonzero p.start
  have hf' := hnonzero p.finish
  omega

end ProteinFolding.Tetrahedral
