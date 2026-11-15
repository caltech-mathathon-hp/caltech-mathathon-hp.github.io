import ProteinFolding.Cubic.Proofs.PackingGeometryBins
import ProteinFolding.Cubic.Proofs.GeometryBasics

/-! Finite face interiors and large-word uniqueness. Different large F words
cannot occupy the same face interior; four full faces and one face missing two
sites leave exactly two sites in those five faces. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicGeometry

abbrev CubeFace := Fin 3 × Bool

theorem cubeFace_card : Fintype.card CubeFace = 6 := by decide

noncomputable def faceInteriorFinset (a : Site) (d : ℕ) (face : CubeFace) : Finset Site := by
  classical
  exact (cubeFinset a (d + 2)).filter fun p => FaceInterior a (d + 2) face.1 face.2 p

theorem mem_faceInteriorFinset (a : Site) (d : ℕ) (face : CubeFace) (p : Site) :
    p ∈ faceInteriorFinset a d face ↔ FaceInterior a (d + 2) face.1 face.2 p := by
  classical
  constructor
  · intro h; exact (Finset.mem_filter.mp h).2
  · intro h; exact Finset.mem_filter.mpr ⟨(mem_cubeFinset a (d + 2) p).mpr h.1, h⟩

theorem faceInterior_face_unique {a p : Site} {n : ℕ} {f g : CubeFace}
    (hf : FaceInterior a n f.1 f.2 p) (hg : FaceInterior a n g.1 g.2 p) : f = g := by
  obtain ⟨i, upper⟩ := f
  obtain ⟨j, lower⟩ := g
  have hij : i = j := by
    by_contra hn
    exact boundary_not_strict (faceInterior_boundary hf) (hg.2.2 i hn)
  subst j
  have hn := faceInterior_side_ge_three hf
  have h0 := hf.2.1
  have h1 := hg.2.1
  have hs : upper = lower := by
    cases upper <;> cases lower <;> simp only [Bool.false_eq_true, ↓reduceIte] at h0 h1 ⊢ <;> omega
  subst lower
  rfl

theorem faceInteriorFinsets_disjoint (a : Site) (d : ℕ) (f g : CubeFace) (hfg : f ≠ g) :
    Disjoint (faceInteriorFinset a d f) (faceInteriorFinset a d g) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact hfg (faceInterior_face_unique ((mem_faceInteriorFinset a d f p).mp hp)
    ((mem_faceInteriorFinset a d g p).mp hq))

theorem rectanglePoint_in_face (a : Site) (d : ℕ) (normal : Fin 3) (upper : Bool)
    (x y : Fin 3) (hxy : x ≠ y) (hx : x ≠ normal) (hy : y ≠ normal) (q : Fin d × Fin d) :
    FaceInterior a (d + 2) normal upper
      (rectanglePoint (Function.update a normal (endValue (a normal) d (faceSide upper)))
        x y (a x + 1) (a y + 1) q) := by
  let base := Function.update a normal (endValue (a normal) d (faceSide upper))
  let p := rectanglePoint base x y (a x + 1) (a y + 1) q
  have hp0 : p normal = endValue (a normal) d (faceSide upper) := by
    have h := rectanglePoint_other base x y normal (Ne.symm hx) (Ne.symm hy) (a x + 1) (a y + 1) q
    simpa only [base, Function.update_self] using h
  have hpx := rectanglePoint_x base x y hxy (a x + 1) (a y + 1) q
  have hpy := rectanglePoint_y base x y (a x + 1) (a y + 1) q
  have hstrict : ∀ k : Fin 3, k ≠ normal → a k < p k ∧ p k + 1 < a k + ((d + 2 : ℕ) : ℤ) := by
    intro k hk
    have he : k = x ∨ k = y := by omega
    rcases he with he | he
    · subst k
      have hq := q.1.isLt
      change a x < rectanglePoint base x y (a x + 1) (a y + 1) q x ∧
        rectanglePoint base x y (a x + 1) (a y + 1) q x + 1 < a x + ((d + 2 : ℕ) : ℤ)
      rw [hpx]
      omega
    · subst k
      have hq := q.2.isLt
      change a y < rectanglePoint base x y (a x + 1) (a y + 1) q y ∧
        rectanglePoint base x y (a x + 1) (a y + 1) q y + 1 < a y + ((d + 2 : ℕ) : ℤ)
      rw [hpy]
      omega
  refine ⟨?_, ?_, hstrict⟩
  · intro k
    by_cases hk : k = normal
    · subst k
      change a normal ≤ p normal ∧ p normal < a normal + ((d + 2 : ℕ) : ℤ)
      rw [hp0]
      exact endValue_bounds (a normal) d (faceSide upper)
    · have h := hstrict k hk
      change a k ≤ p k ∧ p k < a k + ((d + 2 : ℕ) : ℤ)
      omega
  · change if upper then p normal + 1 = a normal + ((d + 2 : ℕ) : ℤ) else p normal = a normal
    cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte, faceSide, endValue] at hp0 ⊢ <;> omega

theorem faceInteriorFinset_card_axes (a : Site) (d : ℕ) (face : CubeFace)
    (x y : Fin 3) (hxy : x ≠ y) (hx : x ≠ face.1) (hy : y ≠ face.1) :
    (faceInteriorFinset a d face).card = d ^ 2 := by
  classical
  apply Nat.le_antisymm
  · exact faceInterior_occupancy_bound a d face.1 face.2 (faceInteriorFinset a d face)
      id (fun _ _ h => h) (fun p hp => (mem_faceInteriorFinset a d face p).mp hp)
  · let base := Function.update a face.1 (endValue (a face.1) d (faceSide face.2))
    have hsub : rectangleFinset base x y (a x + 1) (a y + 1) d d ⊆ faceInteriorFinset a d face := by
      intro p hp
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
      exact (mem_faceInteriorFinset a d face _).mpr (rectanglePoint_in_face a d face.1 face.2 x y hxy hx hy q)
    have h := Finset.card_le_card hsub
    rw [rectangleFinset_card base x y hxy (a x + 1) (a y + 1), ← Nat.pow_two] at h
    exact h

theorem faceInteriorFinset_card (a : Site) (d : ℕ) (face : CubeFace) :
    (faceInteriorFinset a d face).card = d ^ 2 := by
  obtain ⟨normal, upper⟩ := face
  fin_cases normal
  · exact faceInteriorFinset_card_axes a d (0, upper) 1 2 (by decide) (by simp) (by simp)
  · exact faceInteriorFinset_card_axes a d (1, upper) 0 2 (by decide) (by simp) (by simp)
  · exact faceInteriorFinset_card_axes a d (2, upper) 0 1 (by decide) (by simp) (by simp)

/-- Two disjoint sets each exceeding half a face's capacity cannot receive
the same face label. This applies to the five large F blocks of the prefix. -/
theorem large_disjoint_face_assignment_injective {ι : Type*}
    (a : Site) (d : ℕ) (occupied : ι → Finset Site) (face : ι → CubeFace)
    (hlarge : ∀ i, d ^ 2 < 2 * (occupied i).card)
    (hface : ∀ i p, p ∈ occupied i → FaceInterior a (d + 2) (face i).1 (face i).2 p)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (occupied i) (occupied j)) : Function.Injective face := by
  intro i j hlabel
  by_contra hij
  have hbound := faceInterior_occupancy_bound a d (face i).1 (face i).2
    (occupied i ∪ occupied j) id (fun _ _ h => h) (by
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact hface i p hp
      · simpa only [hlabel] using hface j p hp)
  rw [Finset.card_union_of_disjoint (hdisjoint i j hij)] at hbound
  have hi := hlarge i
  have hj := hlarge j
  omega

theorem five_face_labels_card (face : Fin 5 → CubeFace) (hinj : Function.Injective face) :
    (Finset.univ.image face).card = 5 := by
  rw [Finset.card_image_of_injective _ hinj]
  simp

theorem five_faces_exhaust_other_faces (face : Fin 5 → CubeFace) (hinj : Function.Injective face)
    (packingFace : CubeFace) (havoid : ∀ i, face i ≠ packingFace) :
    Finset.univ.image face = Finset.univ \ {packingFace} := by
  apply Finset.eq_of_subset_of_card_le
  · intro f hf
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simpa only [Finset.mem_singleton] using havoid i⟩
  · rw [five_face_labels_card face hinj, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, cubeFace_card, Finset.card_singleton]

/-- Five disjoint large words occupy five different face interiors. Given
their exact total H count, precisely two sites remain in those five faces. -/
theorem five_large_faces_left_two (a : Site) (d : ℕ) (hd : 4 < d ^ 2)
    (occupied : Fin 5 → Finset Site) (face : Fin 5 → CubeFace)
    (hsize : ∀ i, d ^ 2 - 2 ≤ (occupied i).card)
    (htotal : (∑ i : Fin 5, (occupied i).card) = 5 * d ^ 2 - 2)
    (hface : ∀ i p, p ∈ occupied i → FaceInterior a (d + 2) (face i).1 (face i).2 p)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (occupied i) (occupied j)) :
    Function.Injective face ∧
      ((Finset.univ.image face).biUnion (faceInteriorFinset a d) \
        Finset.univ.biUnion occupied).card = 2 := by
  classical
  have hlarge : ∀ i, d ^ 2 < 2 * (occupied i).card := by
    intro i
    have h := hsize i
    omega
  have hinj := large_disjoint_face_assignment_injective a d occupied face hlarge hface hdisjoint
  refine ⟨hinj, ?_⟩
  let regions := (Finset.univ.image face).biUnion (faceInteriorFinset a d)
  let filled := Finset.univ.biUnion occupied
  have hpairs : (Finset.univ.image face).toSet.PairwiseDisjoint (faceInteriorFinset a d) := by
    intro f hf g hg hfg
    exact faceInteriorFinsets_disjoint a d f g hfg
  have hregion : regions.card = 5 * d ^ 2 := by
    change ((Finset.univ.image face).biUnion (faceInteriorFinset a d)).card = 5 * d ^ 2
    rw [Finset.card_biUnion hpairs]
    have hsum := Finset.sum_const_nat (s := Finset.univ.image face)
      (fun f _ => faceInteriorFinset_card a d f)
    rw [five_face_labels_card face hinj] at hsum
    exact hsum
  have hpairfilled : (Finset.univ : Finset (Fin 5)).toSet.PairwiseDisjoint occupied := by
    intro i hi j hj hij
    exact hdisjoint i j hij
  have hfilled : filled.card = 5 * d ^ 2 - 2 := by
    change (Finset.univ.biUnion occupied).card = 5 * d ^ 2 - 2
    rw [Finset.card_biUnion hpairfilled]
    exact htotal
  have hsub : filled ⊆ regions := by
    intro p hp
    obtain ⟨i, _, hip⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_biUnion.mpr ⟨face i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
      (mem_faceInteriorFinset a d (face i) p).mpr (hface i p hip)⟩
  change (regions \ filled).card = 2
  rw [Finset.card_sdiff_of_subset hsub, hregion, hfilled]
  omega

end ProteinFolding.CubicPackingGeometry
