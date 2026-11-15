import ProteinFolding.Cubic.Proofs.PackingFrameLargeFaces

/-! All sufficiently large F blocks after the prefix occupy the same sixth
face. An H in PHHP has an H neighbour, so it cannot be one of the selected
PHP centres; skeleton saturation excludes it from cube edges. The five large
prefix blocks leave only two sites elsewhere on the surface. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicPacking

theorem FaceOccurrence.not_PHP {S : Sequence} {t : ℕ} (o : FaceOccurrence S t)
    (j : Fin (2 * (t / 2))) : ¬ PHPAt S (o.index j).val := by
  have hr (r : Fin 4) : S[o.pre.length + 4 * (j.val / 2) + r.val]? =
      some (if r = 1 ∨ r = 2 then .H else .P) := by
    have he := congrArg (fun w : Sequence => w[o.pre.length + 4 * (j.val / 2) + r.val]?) o.word_eq
    refine he.trans ?_
    change (o.pre ++ faceWord t ++ o.post)[(faceIndex o.pre o.post t (faceBlock j) r).val]? = _
    rw [List.getElem?_eq_getElem (faceIndex o.pre o.post t (faceBlock j) r).isLt]
    exact congrArg some (faceIndex_residue o.pre o.post t (faceBlock j) r)
  have h1 : S[o.pre.length + 4 * (j.val / 2) + 1]? = some .H := by simpa using hr 1
  have h2 : S[o.pre.length + 4 * (j.val / 2) + 2]? = some .H := by simpa using hr 2
  rintro ⟨_, _, hprev, _, hnext⟩
  by_cases he : j.val % 2 = 0
  · have hi : (o.index j).val + 1 = o.pre.length + 4 * (j.val / 2) + 2 := by
      rw [o.index_val]
      omega
    rw [hi, h2] at hnext
    cases hnext
  · have hi : (o.index j).val - 1 = o.pre.length + 4 * (j.val / 2) + 1 := by
      rw [o.index_val]
      omega
    rw [hi, h1] at hprev
    cases hprev

theorem frameFaceOccurrence_not_anchor (q Q : ℕ) (items : List ℕ) {t : ℕ}
    (o : FaceOccurrence (frameWord q Q items) t) (j : Fin (2 * (t / 2))) :
    o.index j ∉ frameAnchors q Q items := by
  intro h
  exact o.not_PHP j ((markedFrame q Q items).indices_php (o.index j) h)

theorem frameFaceOccurrence_noedge (q Q : ℕ) (items : List ℕ) (hq : 0 < q)
    (f : Fold cubicLattice (frameWord q Q items).length) (a : Site)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q)) {t : ℕ}
    (o : FaceOccurrence (frameWord q Q items) t) (j : Fin (2 * (t / 2))) :
    ¬ EdgeSkeleton a (side q Q) (o.path f j) :=
  nonanchor_not_edge f a (side q Q) (frameAnchors q Q items)
    (frame_skeleton_saturated q Q items hq f a hpack) _
    (frameFaceOccurrence_not_anchor q Q items o j)

theorem frameLargeFace_end_le_prefix (q Q : ℕ) (items : List ℕ) (i : Fin 5) :
    (frameLargeFace q Q items i).pre.length + (faceWord (largeFaceSize q Q i)).length ≤
      (prefixWord q Q).length := by
  have h := frameLargeFace_interval q Q items i
  rcases h with h | h
  · have hp : (edgeWord (9 * depth q Q + 8)).length + (faceWord (depth q Q ^ 2)).length ≤
        (prefixWord q Q).length := by
      simp only [prefixWord, List.length_append, List.length_replicate]
      omega
    omega
  · exact h.2

theorem frameFaceOccurrence_disjoint_large (q Q : ℕ) (items : List ℕ) {t : ℕ}
    (o : FaceOccurrence (frameWord q Q items) t)
    (hafter : (prefixWord q Q).length ≤ o.pre.length)
    (f : Fold cubicLattice (frameWord q Q items).length) (i : Fin 5) :
    Disjoint (o.sites f) ((frameLargeFace q Q items i).sites f) :=
  (FaceOccurrence.sites_disjoint_of_before _ o f
    ((frameLargeFace_end_le_prefix q Q items i).trans hafter)).symm

/-- There is one common face for every post-prefix F fragment having more
than two H residues. This applies to the actual wall and item words, in every
perfect fold, independently of their shapes and ordering. -/
theorem frame_remaining_face_confines (q Q : ℕ) (items : List ℕ) (hq : 0 < q)
    (hd : 4 < depth q Q ^ 2)
    (f : Fold cubicLattice (frameWord q Q items).length) (a : Site)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q)) :
    ∃ packingFace : CubeFace,
      ∀ (t : ℕ) (o : FaceOccurrence (frameWord q Q items) t),
        (prefixWord q Q).length ≤ o.pre.length → 2 < 2 * (t / 2) →
        ∀ p ∈ o.sites f, FaceInterior a (side q Q) packingFace.1 packingFace.2 p := by
  classical
  obtain ⟨packingFace, htwo⟩ := frame_remaining_face q Q items hq hd f a hpack
  refine ⟨packingFace, ?_⟩
  intro t o hafter hsize
  obtain ⟨face, hface⟩ := o.in_one_face f a (side q Q) hpack (by omega)
    (frameFaceOccurrence_noedge q Q items hq f a hpack o)
  have heq : face = packingFace := by
    by_contra hne
    have hsub : o.sites f ⊆
        (((Finset.univ : Finset CubeFace) \ {packingFace}).biUnion
            (faceInteriorFinset a (depth q Q)) \
          Finset.univ.biUnion (fun i => (frameLargeFace q Q items i).sites f)) := by
      intro p hp
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, ?_⟩
      · apply Finset.mem_biUnion.mpr
        refine ⟨face, ?_, ?_⟩
        · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simpa only [Finset.mem_singleton] using hne⟩
        · exact (mem_faceInteriorFinset a (depth q Q) face p).mpr (hface p hp)
      · intro hfilled
        obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hfilled
        exact Finset.disjoint_left.mp (frameFaceOccurrence_disjoint_large q Q items o hafter f i) hp hi
    have hc := Finset.card_le_card hsub
    rw [htwo, o.sites_card f] at hc
    omega
  simpa only [heq] using hface

end ProteinFolding.CubicPackingGeometry
