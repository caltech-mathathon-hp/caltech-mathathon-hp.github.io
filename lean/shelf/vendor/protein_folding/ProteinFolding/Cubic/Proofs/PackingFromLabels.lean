import ProteinFolding.Cubic.Proofs.PackingSources
import Mathlib.Data.List.FinRange

/-! Recover a packing from a bin label for every item occurrence. Filtering
occurrence indices, rather than item values, preserves repeated sizes exactly. -/

namespace ProteinFolding.Packing

open scoped BigOperators

def labelledBucket (sizes : List ℕ) {K : ℕ} (label : Fin sizes.length → Fin K)
    (b : Fin K) : List ℕ :=
  ((List.finRange sizes.length).filter (fun i => decide (label i = b))).map sizes.get

def labelledParts (sizes : List ℕ) {K : ℕ} (label : Fin sizes.length → Fin K) : List (List ℕ) :=
  (List.finRange K).map (labelledBucket sizes label)

theorem label_indices_perm {N K : ℕ} (label : Fin N → Fin K) :
    ((List.finRange K).flatMap fun b =>
      (List.finRange N).filter (fun i => decide (label i = b))).Perm (List.finRange N) := by
  have hnodup : ((List.finRange K).flatMap fun b =>
      (List.finRange N).filter (fun i => decide (label i = b))).Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨fun b _ => (List.nodup_finRange N).filter _, ?_⟩
    apply (List.nodup_finRange K).imp
    intro b c hbc
    apply List.disjoint_left.mpr
    intro i hi hj
    have hb : label i = b := by simpa only [List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq] using hi
    have hc : label i = c := by simpa only [List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq] using hj
    exact hbc (hb.symm.trans hc)
  apply (List.perm_ext_iff_of_nodup hnodup (List.nodup_finRange N)).mpr
  intro i
  constructor
  · intro _
    exact List.mem_finRange i
  · intro _
    exact List.mem_flatMap.mpr ⟨label i, List.mem_finRange _, by simp⟩

theorem labelledParts_perm (sizes : List ℕ) {K : ℕ} (label : Fin sizes.length → Fin K) :
    sizes.Perm (labelledParts sizes label).flatten := by
  have hp := (label_indices_perm label).map sizes.get
  rw [List.map_flatMap, List.finRange_map_get] at hp
  exact hp.symm

theorem labelledBucket_sum (sizes : List ℕ) {K : ℕ} (label : Fin sizes.length → Fin K)
    (b : Fin K) :
    (labelledBucket sizes label b).sum =
      ∑ i : Fin sizes.length with label i = b, sizes.get i := by
  have he : ((List.finRange sizes.length).filter (fun i => decide (label i = b))).toFinset =
      Finset.univ.filter (fun i => label i = b) := by
    ext i
    simp
  rw [labelledBucket, ← List.sum_toFinset _ ((List.nodup_finRange sizes.length).filter _), he]

/-- Capacity bounds on each labelled bucket give a genuine list partition.
Under the exact total-size condition, every bucket has exact capacity. -/
theorem exact_of_labels (I : Instance) (label : Fin I.sizes.length → Fin I.bins)
    (htotal : I.sizes.sum = I.capacity * I.bins)
    (hbound : ∀ b, (labelledBucket I.sizes label b).sum ≤ I.capacity) :
    Exact I (labelledParts I.sizes label) := by
  apply exact_of_fits_of_total
  · refine ⟨?_, labelledParts_perm I.sizes label, ?_⟩
    · simp [labelledParts]
    · intro p hp
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hp
      exact hbound b
  · exact htotal

theorem exact_of_label_sums (I : Instance) (label : Fin I.sizes.length → Fin I.bins)
    (htotal : I.sizes.sum = I.capacity * I.bins)
    (hbound : ∀ b, (∑ i : Fin I.sizes.length with label i = b, I.sizes.get i) ≤ I.capacity) :
    Exact I (labelledParts I.sizes label) :=
  exact_of_labels I label htotal (fun b => by rw [labelledBucket_sum]; exact hbound b)

/-- Disjoint item-site sets inside finite bins give the required load bounds.
Cancelling the common positive scale d recovers numerical item capacities. -/
theorem label_sums_le_of_disjoint_sites {V : Type*} [DecidableEq V]
    (sizes : List ℕ) {K d B : ℕ} (hd : 0 < d)
    (label : Fin sizes.length → Fin K) (sites : Fin sizes.length → Finset V)
    (regions : Fin K → Finset V)
    (hsize : ∀ i, (sites i).card = d * sizes.get i)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (sites i) (sites j))
    (hinside : ∀ i, sites i ⊆ regions (label i))
    (hcapacity : ∀ b, (regions b).card ≤ d * B) :
    ∀ b, (∑ i : Fin sizes.length with label i = b, sizes.get i) ≤ B := by
  classical
  intro b
  let indices : Finset (Fin sizes.length) := Finset.univ.filter (fun i => label i = b)
  have hp : indices.toSet.PairwiseDisjoint sites := by
    intro i _ j _ hij
    exact hdisjoint i j hij
  have hsub : indices.biUnion sites ⊆ regions b := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
    have he : label i = b := (Finset.mem_filter.mp hi).2
    simpa only [he] using hinside i hpi
  have hc : (indices.biUnion sites).card ≤ d * B :=
    (Finset.card_le_card hsub).trans (hcapacity b)
  rw [Finset.card_biUnion hp] at hc
  have hsum : (∑ i ∈ indices, (sites i).card) = d * ∑ i ∈ indices, sizes.get i := by
    simp only [hsize, Finset.mul_sum]
  rw [hsum] at hc
  exact Nat.le_of_mul_le_mul_left hc hd

end ProteinFolding.Packing
