import ProteinFolding.Tetrahedral.BulkRungs
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! The unmodified bent foliation is an acyclic graph of degree two. -/

namespace ProteinFolding.Tetrahedral

theorem bulkRungNeighbours_upper_pair (m : ℕ) (p : Site) :
    ∃ a b : Site, bulkRungNeighbours m p = {a, b} ∧ bulkRho m p < bulkRho m a := by
  have hne := bulk_coordinates_not_both_zero m p
  by_cases hy : bulkY m p = 0
  · have hz : bulkZ p ≠ 0 := by omega
    let sz : ℤ := if 0 < bulkZ p then 1 else -1
    have hsz : sz = 1 ∨ sz = -1 := by dsimp [sz]; split_ifs <;> omega
    have hzp : 0 < sz * bulkZ p := by dsimp [sz]; split_ifs <;> omega
    refine ⟨bulkArmNext 1 sz p, bulkArmNext (-1) sz p,
      bulkRungNeighbours_bendY m p sz hsz hy hzp, ?_⟩
    have h := (bulkArmPoint_rho_alpha m 1 sz (Or.inl rfl) hsz p (by omega) (by omega) 1).1
    change bulkRho m p < bulkRho m (bulkArmPoint 1 sz p 1)
    omega
  · by_cases hz : bulkZ p = 0
    · let sy : ℤ := if 0 < bulkY m p then 1 else -1
      have hsy : sy = 1 ∨ sy = -1 := by dsimp [sy]; split_ifs <;> omega
      have hyp : 0 < sy * bulkY m p := by dsimp [sy]; split_ifs <;> omega
      refine ⟨bulkArmNext sy 1 p, bulkArmNext sy (-1) p,
        bulkRungNeighbours_bendZ m p sy hsy hz hyp, ?_⟩
      have h := (bulkArmPoint_rho_alpha m sy 1 hsy (Or.inl rfl) p (by omega) (by omega) 1).1
      change bulkRho m p < bulkRho m (bulkArmPoint sy 1 p 1)
      omega
    · let sy : ℤ := if 0 < bulkY m p then 1 else -1
      let sz : ℤ := if 0 < bulkZ p then 1 else -1
      have hsy : sy = 1 ∨ sy = -1 := by dsimp [sy]; split_ifs <;> omega
      have hsz : sz = 1 ∨ sz = -1 := by dsimp [sz]; split_ifs <;> omega
      have hyp : 0 < sy * bulkY m p := by dsimp [sy]; split_ifs <;> omega
      have hzp : 0 < sz * bulkZ p := by dsimp [sz]; split_ifs <;> omega
      refine ⟨bulkArmNext sy sz p, bulkArmNext (-sy) (-sz) p,
        bulkRungNeighbours_open m p sy sz hsy hsz hyp hzp, ?_⟩
      have h := (bulkArmPoint_rho_alpha m sy sz hsy hsz p (by omega) (by omega) 1).1
      change bulkRho m p < bulkRho m (bulkArmPoint sy sz p 1)
      omega

theorem bulk_lower_rung_unique (m : ℕ) (p : Site) {q r : Site}
    (hq : q ∈ bulkRungNeighbours m p) (hr : r ∈ bulkRungNeighbours m p)
    (hqle : bulkRho m q ≤ bulkRho m p) (hrle : bulkRho m r ≤ bulkRho m p) : q = r := by
  obtain ⟨a, b, hpair, hupper⟩ := bulkRungNeighbours_upper_pair m p
  rw [hpair] at hq hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq hr
  have hqb : q = b := hq.resolve_left (by intro he; rw [he] at hqle; omega)
  have hrb : r = b := hr.resolve_left (by intro he; rw [he] at hrle; omega)
  exact hqb.trans hrb.symm

def bulkRungGraph (m : ℕ) : SimpleGraph Site where
  Adj p q := tetrahedralLattice.Adj p q ∧ bulkRho m p ≠ bulkRho m q
  symm := by intro p q h; exact ⟨h.1.symm, Ne.symm h.2⟩
  loopless := by intro p h; exact h.2 rfl

theorem bulkRungGraph_adj_iff (m : ℕ) (p q : Site) :
    (bulkRungGraph m).Adj p q ↔ q ∈ bulkRungNeighbours m p := by
  simp only [bulkRungGraph, bulkRungNeighbours, Finset.mem_filter, mem_neighbours]
  exact and_congr_right (fun _ => ne_comm)

/-- A finite foliation component always has an end; in particular there are
no cycles in the infinite rung graph. -/
theorem bulkRungGraph_acyclic (m : ℕ) : (bulkRungGraph m).IsAcyclic := by
  intro v c hc
  have hnil := hc.not_nil
  have hnonempty : c.support.tail.toFinset.Nonempty :=
    ⟨v, List.mem_toFinset.mpr (c.end_mem_tail_support hnil)⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image c.support.tail.toFinset (bulkRho m) hnonempty
  have hpSupport : p ∈ c.support := List.mem_of_mem_tail (List.mem_toFinset.mp hp)
  let r := c.rotate hpSupport
  have hr : r.IsCycle := hc.rotate hpSupport
  have hrot : ∀ q ∈ r.support.tail, bulkRho m q ≤ bulkRho m p := by
    intro q hq
    apply hmax q
    apply List.mem_toFinset.mpr
    exact (c.support_rotate hpSupport).mem_iff.mp hq
  have hsq := r.adj_snd hr.not_nil
  have hpq := r.adj_penultimate hr.not_nil
  have hsMem : r.snd ∈ r.support.tail := by
    have h := r.getVert_mem_support 1
    rw [← r.cons_support_tail hr.not_nil] at h
    simp only [List.mem_cons] at h
    simpa only [r.support_tail hr.not_nil] using
      h.resolve_left ((bulkRungGraph m).ne_of_adj hsq).symm
  have hpMem : r.penultimate ∈ r.support.tail := by
    have h := r.getVert_mem_support (r.length - 1)
    rw [← r.cons_support_tail hr.not_nil] at h
    simp only [List.mem_cons] at h
    simpa only [r.support_tail hr.not_nil] using
      h.resolve_left ((bulkRungGraph m).ne_of_adj hpq)
  have heq : r.snd = r.penultimate := bulk_lower_rung_unique m p
    ((bulkRungGraph_adj_iff m p r.snd).mp hsq)
    ((bulkRungGraph_adj_iff m p r.penultimate).mp hpq.symm)
    (hrot _ hsMem) (hrot _ hpMem)
  exact hr.snd_ne_penultimate heq

theorem bulk_finite_foliation_has_end (m : ℕ) (S : Finset Site) (hne : S.Nonempty) :
    ∃ p ∈ S, ((bulkRungNeighbours m p) ∩ S).card ≤ 1 := by
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image S (bulkRho m) hne
  refine ⟨p, hp, Finset.card_le_one.mpr ?_⟩
  intro q hq r hr
  have hq' := Finset.mem_inter.mp hq
  have hr' := Finset.mem_inter.mp hr
  exact bulk_lower_rung_unique m p hq'.1 hr'.1 (hmax q hq'.2) (hmax r hr'.2)

end ProteinFolding.Tetrahedral
