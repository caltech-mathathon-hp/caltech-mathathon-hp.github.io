import Shelf.LayoutPlain

/-!
# The sites of the fold are different

Part (a) of Theorem 16. The sites are of four kinds: the core, the tokens, the
plain `P`'s, and the inner sites of the linkers.
-/

namespace ProteinFolding.Shelf

open ProteinFolding Residue Layout

namespace LayoutNodup

/-- The sites of the tokens of a `flatMap` are the `flatMap` of their sites. -/
theorem tokSites_flatMap {α : Type*} (l : List α) (f : α → List Token) :
    tokSites (l.flatMap f) = l.flatMap fun a => tokSites (f a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, tokSites_append, ih]

/-- The sites of the fold, sorted by kind: the core, the plain `P`'s, the tokens, and the
inner sites of the linkers. -/
theorem layout_perm {J : Packing.Instance} (P : Parts J) :
    (layout P).Perm (P.core ++ plain J ++ tokSites (P.aT ++ shelfTokens J P.lo) ++
      (List.finRange (J.sizes.length + 1)).flatMap P.mid) := by
  have h1 := sepPart_perm J
  have h2 := List.flatMap_append_perm (List.finRange J.sizes.length) (fun i => P.mid i.succ)
    (fun i => tokSites (itemTokens P.lo i))
  rw [List.perm_iff_count] at h1 h2 ⊢
  intro a
  have e1 := h1 a
  have e2 := h2 a
  simp only [layout, plain, shelfTokens, tokSites_append, tokSites_flatMap, List.finRange_succ,
    List.flatMap_cons, List.flatMap_map, List.count_append, List.count_cons, List.count_nil] at e1 e2 ⊢
  omega

end LayoutNodup

open LayoutNodup

theorem layout_nodup {J : Packing.Instance} (hJ : Normalised J) {P : Parts J} (hP : P.Good) :
    (layout P).Nodup := by
  have hN : (2 : ℤ) ≤ N J := by
    have := ten_le_side hJ
    unfold N; omega
  have hlo := hP.placed
  have hv : ∀ t ∈ P.aT ++ shelfTokens J P.lo, t.Valid (side J) := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hP.a_valid t ht
    · exact shelfTokens_valid hlo t ht
  have hsk : ∀ t ∈ P.aT ++ shelfTokens J P.lo, CubicPackingGeometry.EdgeSkeleton 0 (side J) t.c := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact (hP.a_centres t ht).1
    · exact shelfTokens_skeleton hlo t ht
  -- the tokens
  have hC : (tokSites (P.aT ++ shelfTokens J P.lo)).Nodup := by
    refine tokSites_nodup hv ?_
    rw [List.map_append, List.nodup_append]
    refine ⟨hP.a_nodup, shelfTokens_nodup hlo, ?_⟩
    intro x hx y hy hxy
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hy
    have h1 := (hP.a_centres t ht).2
    have h2 := shelfTokens_c hlo t' ht'
    rw [hxy] at h1
    omega
  -- the linkers
  have hD : ((List.finRange (J.sizes.length + 1)).flatMap P.mid).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun i _ => hP.mid_nodup i, ?_⟩
    exact (List.nodup_finRange _).imp fun {i j} hij s hi hj => hP.mid_disjoint i j hij s hi hj
  have hD_out : ∀ s ∈ (List.finRange (J.sizes.length + 1)).flatMap P.mid, ¬ InBox J s := by
    intro s hs
    obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hs
    exact hP.mid_out i s hi
  refine (layout_perm P).nodup_iff.mpr ?_
  rw [List.nodup_append, List.nodup_append, List.nodup_append]
  refine ⟨⟨⟨hP.core_nodup, plain_nodup hJ, ?_⟩, hC, ?_⟩, hD, ?_⟩
  · -- core against plain
    rintro a ha b hb rfl
    exact plain_not_mem_Q J a hb (hP.core_mem a ha).1
  · -- core and plain against tokens
    rintro a ha b hb rfl
    rcases List.mem_append.mp ha with ha | ha
    · exact not_mem_tokSites_of_off hv hsk
        (offTokens_of_core (hP.core_mem a ha).1 (hP.core_mem a ha).2) hb
    · exact not_mem_tokSites_of_off hv hsk (plain_off J a ha) hb
  · -- the rest against the linkers
    rintro a ha b hb rfl
    refine hD_out a hb ?_
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact inBox_of_mem_Q (hP.core_mem a ha).1
      · exact plain_inBox J a ha
    · exact inBox_of_tokSites hv ha

end ProteinFolding.Shelf
