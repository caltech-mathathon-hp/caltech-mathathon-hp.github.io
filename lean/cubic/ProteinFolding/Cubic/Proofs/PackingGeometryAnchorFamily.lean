import ProteinFolding.Cubic.Proofs.PackingGeometryAnchorIntervals
import ProteinFolding.Cubic.Proofs.PackingAnchorArithmetic

/-! Finite-family anchor forcing on two rails. Every geometric and counting
premise is explicit: intervals are disjoint on each rail, both rails are filled,
there are q long anchors, and every gap anchor lies on rail zero. The modulus
then forces exactly the long anchors onto rail one. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicPacking
open scoped BigOperators

inductive AnchorKind where
  | short | long | gap
  deriving DecidableEq, Fintype

def anchorLength (Q : ℕ) : AnchorKind → ℕ
  | .short => alpha Q
  | .long => beta Q
  | .gap => 2

def anchorSites {ι : Type*} (Q : ℕ) (kind : ι → AnchorKind) (start : ι → ℕ) (i : ι) : Finset ℕ :=
  Finset.Ico (start i) (start i + anchorLength Q (kind i))

def railBlocks {ι : Type*} [DecidableEq ι] (blocks : Finset ι) (rail : ι → Fin 2) (r : Fin 2) : Finset ι :=
  blocks.filter fun i => rail i = r

theorem sum_indicator_constant {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (P : ι → Prop) [DecidablePred P] (c : ℕ) :
    (∑ i ∈ s, if P i then c else 0) = (s.filter P).card * c := by
  rw [← Finset.sum_filter]
  exact Finset.sum_const_nat (fun _ _ => rfl)

theorem rail_anchor_volume {ι : Type*} [DecidableEq ι]
    (Q D : ℕ) (blocks : Finset ι) (kind : ι → AnchorKind) (rail : ι → Fin 2) (start : ι → ℕ)
    (hdisjoint : ∀ i ∈ blocks, ∀ j ∈ blocks, i ≠ j → rail i = rail j →
      Disjoint (anchorSites Q kind start i) (anchorSites Q kind start j))
    (hfill : ∀ r, (railBlocks blocks rail r).biUnion (anchorSites Q kind start) = Finset.Ico 1 (D + 1))
    (r : Fin 2) : (∑ i ∈ railBlocks blocks rail r, anchorLength Q (kind i)) = D := by
  have hp : (railBlocks blocks rail r).toSet.PairwiseDisjoint (anchorSites Q kind start) := by
    intro i hi j hj hij
    obtain ⟨hib, hir⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjb, hjr⟩ := Finset.mem_filter.mp hj
    exact hdisjoint i hib j hjb hij (hir.trans hjr.symm)
  have hc := congrArg Finset.card (hfill r)
  rw [Finset.card_biUnion hp] at hc
  simpa only [anchorSites, Nat.card_Ico, Nat.add_sub_cancel_left, Nat.add_sub_cancel] using hc

theorem anchor_family_rail_forcing {ι : Type*} [DecidableEq ι]
    (q Q : ℕ) (hQ : 0 < Q) (hq : q < Q)
    (blocks : Finset ι) (kind : ι → AnchorKind) (rail : ι → Fin 2) (start : ι → ℕ)
    (hlong : (blocks.filter fun i => kind i = .long).card = q)
    (hgap : ∀ i ∈ blocks, kind i = .gap → rail i = 0)
    (hdisjoint : ∀ i ∈ blocks, ∀ j ∈ blocks, i ≠ j → rail i = rail j →
      Disjoint (anchorSites Q kind start i) (anchorSites Q kind start j))
    (hfill : ∀ r, (railBlocks blocks rail r).biUnion (anchorSites Q kind start) =
      Finset.Ico 1 (depth q Q + 1)) :
    ∀ i ∈ blocks, rail i = 1 ↔ kind i = .long := by
  let R := railBlocks blocks rail 1
  let shorts := R.filter fun i => kind i = .short
  let longs := R.filter fun i => kind i = .long
  have hnogap : ∀ i ∈ R, kind i ≠ .gap := by
    intro i hi hg
    obtain ⟨hib, hir⟩ := Finset.mem_filter.mp hi
    have hr := hgap i hib hg
    have he : (0 : Fin 2) = 1 := hr.symm.trans hir
    exact (by decide : (0 : Fin 2) ≠ 1) he
  have hsplit : (∑ i ∈ R, anchorLength Q (kind i)) = shorts.card * alpha Q + longs.card * beta Q := by
    have he : (∑ i ∈ R, anchorLength Q (kind i)) =
        ∑ i ∈ R, ((if kind i = .short then alpha Q else 0) + (if kind i = .long then beta Q else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      cases hk : kind i with
      | short => simp [anchorLength]
      | long => simp [anchorLength]
      | gap => exact False.elim (hnogap i hi hk)
    rw [he, Finset.sum_add_distrib, sum_indicator_constant, sum_indicator_constant]
  have hvol : shorts.card * alpha Q + longs.card * beta Q = depth q Q := by
    rw [← hsplit]
    exact rail_anchor_volume Q (depth q Q) blocks kind rail start hdisjoint hfill 1
  have hlsub : longs ⊆ blocks.filter fun i => kind i = .long := by
    intro i hi
    obtain ⟨hir, hik⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hir).1, hik⟩
  have hlle : longs.card ≤ q := by simpa only [hlong] using Finset.card_le_card hlsub
  obtain ⟨hlq, hs0⟩ := anchor_length_forcing Q q shorts.card longs.card hQ hq hlle hvol
  have hshortempty : shorts = ∅ := Finset.card_eq_zero.mp hs0
  have hlongall : longs = blocks.filter fun i => kind i = .long := by
    apply Finset.eq_of_subset_of_card_le hlsub
    rw [hlong, hlq]
  intro i hi
  constructor
  · intro hir
    cases hk : kind i with
    | short =>
      have hm : i ∈ shorts := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hi, hir⟩, hk⟩
      rw [hshortempty] at hm
      exact False.elim (Finset.notMem_empty i hm)
    | long => rfl
    | gap =>
      have hr := hgap i hi hk
      have he : (0 : Fin 2) = 1 := hr.symm.trans hir
      exact False.elim ((by decide : (0 : Fin 2) ≠ 1) he)
  · intro hik
    have hm : i ∈ blocks.filter fun i => kind i = .long := Finset.mem_filter.mpr ⟨hi, hik⟩
    rw [← hlongall] at hm
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2

/-- Long-anchor starts are rigid once the two rails are filled. This packages
the modulus step and interval tiling, retaining every family premise visibly. -/
theorem anchor_family_long_starts {ι : Type*} [DecidableEq ι]
    (q Q : ℕ) (hQ : 0 < Q) (hq : q < Q)
    (blocks : Finset ι) (kind : ι → AnchorKind) (rail : ι → Fin 2) (start : ι → ℕ)
    (hlong : (blocks.filter fun i => kind i = .long).card = q)
    (hgap : ∀ i ∈ blocks, kind i = .gap → rail i = 0)
    (hdisjoint : ∀ i ∈ blocks, ∀ j ∈ blocks, i ≠ j → rail i = rail j →
      Disjoint (anchorSites Q kind start i) (anchorSites Q kind start j))
    (hfill : ∀ r, (railBlocks blocks rail r).biUnion (anchorSites Q kind start) =
      Finset.Ico 1 (depth q Q + 1))
    (hbound : ∀ i ∈ blocks, 1 ≤ start i ∧ start i + anchorLength Q (kind i) ≤ depth q Q + 1) :
    (blocks.filter fun i => kind i = .long).image start =
      (Finset.range q).image (fun j => j * beta Q + 1) := by
  have hforce := anchor_family_rail_forcing q Q hQ hq blocks kind rail start hlong hgap hdisjoint hfill
  have hβ : 0 < beta Q := by dsimp [beta]; omega
  apply tiled_interval_starts (beta Q) q hβ
  · intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    exact (hbound i (Finset.mem_filter.mp hi).1).1
  · intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hib, hik⟩ := Finset.mem_filter.mp hi
    have hb := (hbound i hib).2
    simpa only [hik, anchorLength, depth] using hb
  · intro u hu v hv huv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hib, hik⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjb, hjk⟩ := Finset.mem_filter.mp hj
    have hij : i ≠ j := by intro h; subst j; exact huv rfl
    have hri := (hforce i hib).mpr hik
    have hrj := (hforce j hjb).mpr hjk
    have hd := hdisjoint i hib j hjb hij (hri.trans hrj.symm)
    apply interval_separation_of_disjoint _ _ (beta Q) hβ
    simpa only [anchorSites, hik, hjk, anchorLength] using hd
  · intro y hy0 hy1
    have hy : y ∈ Finset.Ico 1 (depth q Q + 1) := Finset.mem_Ico.mpr ⟨hy0, by
      change y < q * beta Q + 1
      omega⟩
    rw [← hfill 1] at hy
    obtain ⟨i, hi, hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨hib, hir⟩ := Finset.mem_filter.mp hi
    have hik := (hforce i hib).mp hir
    refine ⟨start i, Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hib, hik⟩, rfl⟩, ?_⟩
    simpa only [anchorSites, hik, anchorLength, Finset.mem_Ico] using hy

end ProteinFolding.CubicPackingGeometry
