import ProteinFolding.Tetrahedral.FinitePathCover
import Mathlib.Data.Finset.Max

/-! A degree-two cycle is an entire connected component. Consequently a
finite potential escape certificate rules out every cycle. The potential
may take values in any linear order, including the corrected lexicographic
order of the manuscript; no fixed numerical weighting is used. -/

namespace ProteinFolding.Tetrahedral

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem cycle_support_two_neighbours {v z : V} (p : G.Walk v v) (hp : p.IsCycle)
    (hz : z ∈ p.support) :
    ∃ l ∈ p.support, ∃ r ∈ p.support, l ≠ r ∧ G.Adj z l ∧ G.Adj z r := by
  obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hz
  have hlen := hp.three_le_length
  by_cases hend : i = 0 ∨ i = p.length
  · have hzv : z = v := by
      rcases hend with h | h
      · simpa only [h, Walk.getVert_zero] using hi.symm
      · simpa only [h, Walk.getVert_length] using hi.symm
    exact ⟨p.snd, p.getVert_mem_support 1, p.penultimate,
      p.getVert_mem_support (p.length - 1), hp.snd_ne_penultimate,
      by simpa only [hzv] using p.adj_snd hp.not_nil,
      by simpa only [hzv] using (p.adj_penultimate hp.not_nil).symm⟩
  · have hipos : 0 < i := by omega
    have hilt : i < p.length := by omega
    have hl := (p.adj_getVert_succ (show i - 1 < p.length by omega)).symm
    rw [show i - 1 + 1 = i by omega, hi] at hl
    have hr := p.adj_getVert_succ hilt
    rw [hi] at hr
    exact ⟨p.getVert (i - 1), p.getVert_mem_support _, p.getVert (i + 1),
      p.getVert_mem_support _, hp.getVert_sub_one_ne_getVert_add_one hil, hl, hr⟩

theorem cycle_support_degree_ge_two {v z : V} (p : G.Walk v v) (hp : p.IsCycle)
    (hz : z ∈ p.support) : 2 ≤ G.degree z := by
  obtain ⟨l, _, r, _, hlr, hl, hr⟩ := cycle_support_two_neighbours G p hp hz
  have hsub : ({l, r} : Finset V) ⊆ G.neighborFinset z := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact (G.mem_neighborFinset z _).mpr hl
    · exact (G.mem_neighborFinset z _).mpr hr
  have h := Finset.card_le_card hsub
  simpa only [Finset.card_pair hlr, SimpleGraph.card_neighborFinset_eq_degree] using h

theorem cycle_support_neighbour_closed (hdegree : ∀ v, G.degree v ≤ 2)
    {v z w : V} (p : G.Walk v v) (hp : p.IsCycle)
    (hz : z ∈ p.support) (hadj : G.Adj z w) : w ∈ p.support := by
  obtain ⟨l, hlS, r, hrS, hlr, hl, hr⟩ := cycle_support_two_neighbours G p hp hz
  have hsub : ({l, r} : Finset V) ⊆ G.neighborFinset z := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact (G.mem_neighborFinset z _).mpr hl
    · exact (G.mem_neighborFinset z _).mpr hr
  have heq : G.neighborFinset z = {l, r} := by
    apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
    simpa only [Finset.card_pair hlr, SimpleGraph.card_neighborFinset_eq_degree] using hdegree z
  have hw := (G.mem_neighborFinset z w).mpr hadj
  rw [heq] at hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl
  · exact hlS
  · exact hrS

theorem cycle_support_reachable_closed (hdegree : ∀ v, G.degree v ≤ 2)
    {v z w : V} (p : G.Walk v v) (hp : p.IsCycle)
    (hz : z ∈ p.support) (hreach : G.Reachable z w) : w ∈ p.support := by
  obtain ⟨q⟩ := hreach
  induction q with
  | nil => exact hz
  | cons hadj q ih => exact ih (cycle_support_neighbour_closed G hdegree p hp hz hadj)

/-- Every vertex can escape to an actual end or a strictly larger potential.
At a maximum-potential vertex of a hypothetical cycle, both alternatives
contradict closure of that cycle's support. -/
theorem finite_degree_two_acyclic_of_escape {α : Type} [LinearOrder α]
    (hdegree : ∀ v, G.degree v ≤ 2) (Ω : V → α)
    (hescape : ∀ v, ∃ w, G.Reachable v w ∧ (G.degree w ≤ 1 ∨ Ω v < Ω w)) : G.IsAcyclic := by
  intro v p hp
  have hne : p.support.toFinset.Nonempty := ⟨v, by simp⟩
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image p.support.toFinset Ω hne
  obtain ⟨w, hreach, hcase⟩ := hescape z
  have hzS := List.mem_toFinset.mp hz
  have hwS := cycle_support_reachable_closed G hdegree p hp hzS hreach
  rcases hcase with hleaf | hgreater
  · have hd := cycle_support_degree_ge_two G p hp hwS
    omega
  · exact (not_lt_of_ge (hmax w (List.mem_toFinset.mpr hwS))) hgreater

end ProteinFolding.Tetrahedral
