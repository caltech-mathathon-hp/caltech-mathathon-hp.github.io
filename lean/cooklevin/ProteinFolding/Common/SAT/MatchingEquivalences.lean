import ProteinFolding.Common.SAT.ThreeDimensionalMatching
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin.Basic

/-! Equivalent descriptions of a raw perfect three-dimensional matching.
A list witness can be reindexed by its Y coordinate, yielding two permutations
of the explicit finite vertex set. Conversely such permutations select a
duplicate-free sublist of available triples. -/

namespace ProteinFolding.ThreeDimensionalMatching

def tupleAt (I : Instance) (chosen : List Triple) (h : Matches I chosen)
    (i : Fin I.size) : Triple :=
  chosen.get ((finCongr (matches_length h)).symm i)

noncomputable def coordinateEquiv (I : Instance) (chosen : List Triple) (h : Matches I chosen)
    (p : Triple → ℕ) (hp : (chosen.map p).Perm (List.range I.size)) :
    Equiv.Perm (Fin I.size) := by
  let f : Fin I.size → Fin I.size := fun i => ⟨p (tupleAt I chosen h i), by
    have ht : tupleAt I chosen h i ∈ chosen := List.get_mem ..
    exact List.mem_range.mp (hp.mem_iff.mp (List.mem_map.mpr ⟨_, ht, rfl⟩))⟩
  have hinj : Function.Injective f := by
    intro i j he
    have hcoord := congrArg Fin.val he
    have hmap : (chosen.map p).Nodup := hp.nodup_iff.mpr List.nodup_range
    have htuple : tupleAt I chosen h i = tupleAt I chosen h j :=
      List.inj_on_of_nodup_map hmap (List.get_mem ..) (List.get_mem ..) hcoord
    have hpos := (List.nodup_iff_injective_get.mp (matches_nodup h)) htuple
    exact (finCongr (matches_length h)).symm.injective hpos
  exact Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩

theorem coordinateEquiv_val (I : Instance) (chosen : List Triple) (h : Matches I chosen)
    (p : Triple → ℕ) (hp : (chosen.map p).Perm (List.range I.size)) (i : Fin I.size) :
    (coordinateEquiv I chosen h p hp i).val = p (tupleAt I chosen h i) := rfl

def EquivMatching (I : Instance) : Prop :=
  ∃ mx mz : Equiv.Perm (Fin I.size),
    ∀ y : Fin I.size, ((mx y).val, y.val, (mz y).val) ∈ I.triples

theorem equivMatching_of_matches (I : Instance) (chosen : List Triple) (h : Matches I chosen) :
    EquivMatching I := by
  let fx := coordinateEquiv I chosen h Prod.fst h.2.1
  let fy := coordinateEquiv I chosen h (fun t => t.2.1) h.2.2.1
  let fz := coordinateEquiv I chosen h (fun t => t.2.2) h.2.2.2
  let mx := fy.symm.trans fx
  let mz := fy.symm.trans fz
  refine ⟨mx, mz, ?_⟩
  intro y
  have hy : (tupleAt I chosen h (fy.symm y)).2.1 = y.val := by
    exact (coordinateEquiv_val I chosen h _ h.2.2.1 (fy.symm y)).symm.trans
      (congrArg Fin.val (fy.apply_symm_apply y))
  have he : ((mx y).val, y.val, (mz y).val) = tupleAt I chosen h (fy.symm y) := by
    apply Prod.ext
    · exact coordinateEquiv_val I chosen h _ h.2.1 (fy.symm y)
    · apply Prod.ext
      · exact hy.symm
      · exact coordinateEquiv_val I chosen h _ h.2.2.2 (fy.symm y)
  rw [he]
  exact h.1.subset (List.get_mem ..)

theorem ofFn_val_perm (n : ℕ) (e : Equiv.Perm (Fin n)) :
    (List.ofFn (fun i => (e i).val)).Perm (List.range n) := by
  have h := e.ofFn_comp_perm (fun i : Fin n => i.val)
  simpa only [Function.comp_def, List.ofFn_eq_map, List.map_coe_finRange] using h

theorem matches_of_equivMatching (I : Instance) (h : EquivMatching I) :
    ∃ chosen, Matches I chosen := by
  obtain ⟨mx, mz, hm⟩ := h
  let chosen : List Triple := List.ofFn fun i : Fin I.size => ((mx i).val, i.val, (mz i).val)
  have hnodup : chosen.Nodup := by
    apply List.nodup_ofFn_ofInjective
    intro i j he
    exact Fin.ext (congrArg (fun t : Triple => t.2.1) he)
  refine ⟨chosen, hnodup.subperm ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
    exact hm i
  · simpa only [chosen, List.map_ofFn, Function.comp_def] using ofFn_val_perm I.size mx
  · simpa only [chosen, List.map_ofFn, Function.comp_def] using
      ofFn_val_perm I.size (Equiv.refl _)
  · simpa only [chosen, List.map_ofFn, Function.comp_def] using ofFn_val_perm I.size mz

theorem accepts_iff_equivMatching (I : Instance) :
    Accepts I ↔ WellFormed I ∧ EquivMatching I := by
  constructor
  · rintro ⟨hw, chosen, h⟩
    exact ⟨hw, equivMatching_of_matches I chosen h⟩
  · rintro ⟨hw, h⟩
    exact ⟨hw, matches_of_equivMatching I h⟩

end ProteinFolding.ThreeDimensionalMatching
