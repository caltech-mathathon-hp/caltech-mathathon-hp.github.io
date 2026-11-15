import ProteinFolding.Cubic.Proofs.PackingGeometryLocal
import ProteinFolding.Cubic.Proofs.GeometryBasics

/-! Exact finite skeleton counting and the saturation principle. A cube of
side n≥2 has 12(n−2)+8 edge sites. Hence an injective family of that many
edge-forced residues occupies every edge site. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicCertificates CubicGeometry

def endCoordinates (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun x => x.val = 0 ∨ x.val + 1 = n

theorem endCoordinates_card (n : ℕ) (hn : 2 ≤ n) : (endCoordinates n).card = 2 := by
  let lo : Fin n := ⟨0, by omega⟩
  let hi : Fin n := ⟨n - 1, by omega⟩
  have he : endCoordinates n = {lo, hi} := by
    ext x
    simp only [endCoordinates, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    simp only [lo, hi, Fin.ext_iff]
    omega
  rw [he, Finset.card_pair]
  intro h
  have h' := congrArg Fin.val h
  dsimp [lo, hi] at h'
  omega

abbrev Triple (n : ℕ) := Fin n × Fin n × Fin n

def edgeTriples (n : ℕ) : Finset (Triple n) :=
  (endCoordinates n ×ˢ (endCoordinates n ×ˢ Finset.univ)) ∪
    (endCoordinates n ×ˢ (Finset.univ ×ˢ endCoordinates n)) ∪
    (Finset.univ ×ˢ (endCoordinates n ×ˢ endCoordinates n))

theorem edgeTriples_card (n : ℕ) (hn : 2 ≤ n) :
    (edgeTriples n).card = 12 * (n - 2) + 8 := by
  let b := endCoordinates n
  let u : Finset (Fin n) := Finset.univ
  let s := b ×ˢ (b ×ˢ u)
  let t := b ×ˢ (u ×ˢ b)
  let v := u ×ˢ (b ×ˢ b)
  let c := b ×ˢ (b ×ˢ b)
  have hb : b.card = 2 := endCoordinates_card n hn
  have hu : u.card = n := by simp [u]
  have hst : s ∩ t = c := by
    ext q
    simp [s, t, c, u, and_assoc, and_left_comm, and_comm]
  have hsv : (s ∪ t) ∩ v = c := by
    ext q
    simp [s, t, v, c, u]
    tauto
  have hc : c.card = 8 := by simp [c, Finset.card_product, hb]
  have hs : s.card = 4 * n := by simp [s, Finset.card_product, hb, hu]; omega
  have ht : t.card = 4 * n := by simp [t, Finset.card_product, hb, hu]; omega
  have hv : v.card = 4 * n := by simp [v, Finset.card_product, hb, hu]; omega
  have h1 := Finset.card_union_add_card_inter s t
  have h2 := Finset.card_union_add_card_inter (s ∪ t) v
  rw [hst, hc, hs, ht] at h1
  rw [hsv, hc, hv] at h2
  change ((s ∪ t) ∪ v).card = 12 * (n - 2) + 8
  omega

def triplePoint (a : Site) {n : ℕ} (q : Triple n) : Site
  | 0 => a 0 + q.1.val
  | 1 => a 1 + q.2.1.val
  | 2 => a 2 + q.2.2.val

theorem triplePoint_injective (a : Site) (n : ℕ) :
    Function.Injective (triplePoint a : Triple n → Site) := by
  intro q r h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  apply Prod.ext
  · apply Fin.ext
    change a 0 + (q.1.val : ℤ) = a 0 + (r.1.val : ℤ) at h0
    omega
  · apply Prod.ext
    · apply Fin.ext
      change a 1 + (q.2.1.val : ℤ) = a 1 + (r.2.1.val : ℤ) at h1
      omega
    · apply Fin.ext
      change a 2 + (q.2.2.val : ℤ) = a 2 + (r.2.2.val : ℤ) at h2
      omega

theorem triplePoint_in_cube (a : Site) (n : ℕ) (q : Triple n) : triplePoint a q ∈ cube a n := by
  intro k
  fin_cases k <;> simp only [Fin.reduceFinMk, triplePoint]
  all_goals have h0 := q.1.isLt; have h1 := q.2.1.isLt; have h2 := q.2.2.isLt; omega

theorem triplePoint_boundary_zero (a : Site) (n : ℕ) (q : Triple n) :
    BoundaryCoordinate a (triplePoint a q) n 0 ↔ q.1 ∈ endCoordinates n := by
  simp only [BoundaryCoordinate, triplePoint, endCoordinates, Finset.mem_filter,
    Finset.mem_univ, true_and]
  omega

theorem triplePoint_boundary_one (a : Site) (n : ℕ) (q : Triple n) :
    BoundaryCoordinate a (triplePoint a q) n 1 ↔ q.2.1 ∈ endCoordinates n := by
  simp only [BoundaryCoordinate, triplePoint, endCoordinates, Finset.mem_filter,
    Finset.mem_univ, true_and]
  omega

theorem triplePoint_boundary_two (a : Site) (n : ℕ) (q : Triple n) :
    BoundaryCoordinate a (triplePoint a q) n 2 ↔ q.2.2 ∈ endCoordinates n := by
  simp only [BoundaryCoordinate, triplePoint, endCoordinates, Finset.mem_filter,
    Finset.mem_univ, true_and]
  omega

theorem triplePoint_edge_iff (a : Site) (n : ℕ) (q : Triple n) :
    EdgeSkeleton a n (triplePoint a q) ↔ q ∈ edgeTriples n := by
  simp only [edgeTriples, Finset.mem_union, Finset.mem_product, Finset.mem_univ, and_true,
    true_and]
  constructor
  · rintro ⟨_, i, j, hij, hi, hj⟩
    fin_cases i <;> fin_cases j
    all_goals simp only [Fin.reduceFinMk] at hij hi hj
    all_goals first
      | exact False.elim (hij rfl)
      | simp only [triplePoint_boundary_zero, triplePoint_boundary_one, triplePoint_boundary_two] at hi hj
        tauto
  · intro h
    refine ⟨triplePoint_in_cube a n q, ?_⟩
    rcases h with (h | h) | h
    · exact ⟨0, 1, by decide, (triplePoint_boundary_zero a n q).mpr h.1,
        (triplePoint_boundary_one a n q).mpr h.2⟩
    · exact ⟨0, 2, by decide, (triplePoint_boundary_zero a n q).mpr h.1,
        (triplePoint_boundary_two a n q).mpr h.2⟩
    · exact ⟨1, 2, by decide, (triplePoint_boundary_one a n q).mpr h.1,
        (triplePoint_boundary_two a n q).mpr h.2⟩

def skeletonFinset (a : Site) (n : ℕ) : Finset Site := (edgeTriples n).image (triplePoint a)

theorem mem_skeletonFinset (a : Site) (n : ℕ) (p : Site) :
    p ∈ skeletonFinset a n ↔ EdgeSkeleton a n p := by
  constructor
  · rintro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (triplePoint_edge_iff a n q).mpr hq
  · intro hp
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp ((mem_cubeFinset a n p).mpr hp.1)
    let q : Triple n := (r 0, r 1, r 2)
    have he : triplePoint a q = p := by
      rw [← hr]
      apply site_ext <;> rfl
    refine Finset.mem_image.mpr ⟨q, ?_, he⟩
    apply (triplePoint_edge_iff a n q).mp
    simpa only [he] using hp

theorem skeletonFinset_card (a : Site) (n : ℕ) (hn : 2 ≤ n) :
    (skeletonFinset a n).card = 12 * (n - 2) + 8 := by
  rw [skeletonFinset, Finset.card_image_of_injective _ (triplePoint_injective a n)]
  exact edgeTriples_card n hn

/-- Counting edge-forced residues suffices to prove complete edge saturation. -/
theorem skeleton_saturated {S : Sequence} (f : Fold cubicLattice S.length)
    (a : Site) (n : ℕ) (anchors : Finset (Fin S.length))
    (hanchor : ∀ i ∈ anchors, EdgeSkeleton a n (f.pos i))
    (hcard : anchors.card = (skeletonFinset a n).card) :
    anchors.image f.pos = skeletonFinset a n := by
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact (mem_skeletonFinset a n _).mpr (hanchor i hi)
  · rw [Finset.card_image_of_injective _ f.injective_pos, hcard]

theorem nonanchor_not_edge {S : Sequence} (f : Fold cubicLattice S.length)
    (a : Site) (n : ℕ) (anchors : Finset (Fin S.length))
    (hsaturated : anchors.image f.pos = skeletonFinset a n)
    (j : Fin S.length) (hj : j ∉ anchors) : ¬ EdgeSkeleton a n (f.pos j) := by
  intro he
  have hmem := (mem_skeletonFinset a n (f.pos j)).mpr he
  rw [← hsaturated] at hmem
  obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hmem
  exact hj ((f.injective_pos hij) ▸ hi)

end ProteinFolding.CubicPackingGeometry
