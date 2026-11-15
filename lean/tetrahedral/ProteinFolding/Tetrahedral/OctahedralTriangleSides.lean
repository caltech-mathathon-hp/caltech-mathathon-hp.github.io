import ProteinFolding.Tetrahedral.OctahedralTriangleSteps

/-! Section 5.6(O5): triangular neighbours on the same or different sides. -/

namespace ProteinFolding.Tetrahedral

theorem big_face_same_side_neighbours {m i j : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (hi : i < m) (hj : j < m) :
    OctTriangularNeighbours m (octEdgeZigzag m F (2 * i)) (octEdgeZigzag m F (2 * j)) ↔
      i + 1 = j ∨ j + 1 = i := by
  constructor
  · intro h
    have hb := triangular_neighbours_coordinate_bounds h F.a
    have hpi := (octEdgeZigzag_even hm F i).2.2.2.1
    have hpj := (octEdgeZigzag_even hm F j).2.2.2.1
    rw [hpi, hpj] at hb
    have hne : i ≠ j := by
      intro heq
      subst j
      exact triangular_neighbours_ne h rfl
    omega
  · have forward : ∀ u v : ℕ, u < m → v < m → u + 1 = v →
        OctTriangularNeighbours m (octEdgeZigzag m F (2 * u)) (octEdgeZigzag m F (2 * v)) := by
      intro u v hu hv huv
      subst v
      exact big_face_twoStep_triangular (octEdgeZigzag_even_mem hm F hu).1
        (octEdgeZigzag_even_mem hm F hv).1 (Ne.symm F.ab) (Ne.symm F.kb)
        (Ne.symm F.ka) (octEdgeZigzag_even_twoStep hm F u)
    rintro (h | h)
    · exact forward i j hi hj h
    · exact triangular_neighbours_symm (forward j i hj hi h)

theorem small_face_same_side_neighbours {m i j : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (hi : i < m - 1) (hj : j < m - 1) :
    OctTriangularNeighbours m (octEdgeZigzag m F (2 * i + 1))
      (octEdgeZigzag m F (2 * j + 1)) ↔ i + 1 = j ∨ j + 1 = i := by
  constructor
  · intro h
    have hb := triangular_neighbours_coordinate_bounds h F.a
    have hpi := (octEdgeZigzag_odd hm F i).2.2.2.1
    have hpj := (octEdgeZigzag_odd hm F j).2.2.2.1
    rw [hpi, hpj] at hb
    have hne : i ≠ j := by
      intro heq
      subst j
      exact triangular_neighbours_ne h rfl
    omega
  · have forward : ∀ u v : ℕ, u < m - 1 → v < m - 1 → u + 1 = v →
        OctTriangularNeighbours m (octEdgeZigzag m F (2 * u + 1))
          (octEdgeZigzag m F (2 * v + 1)) := by
      intro u v hu hv huv
      subst v
      exact small_face_twoStep_triangular (octEdgeZigzag_odd_mem hm F hu).1
        (octEdgeZigzag_odd_mem hm F hv).1 F.ab F.ja.symm F.jb.symm
        (octEdgeZigzag_odd_twoStep hm F u)
    rintro (h | h)
    · exact forward i j hi hj h
    · exact triangular_neighbours_symm (forward j i hj hi h)

theorem big_face_different_sides_neighbours {m i j : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (hi0 : 1 ≤ i) (hj0 : 1 ≤ j) (hi : i < m) (hj : j < m) :
    OctTriangularNeighbours m (octEdgeZigzag m F (2 * i))
      (octEdgeZigzag m F.bigOtherSide (2 * j)) ↔ i = 1 ∧ j = 1 := by
  constructor
  · intro h
    have hba := triangular_neighbours_coordinate_bounds h F.a
    have hbj := triangular_neighbours_coordinate_bounds h F.j
    obtain ⟨_, _, hpj, hpa, _⟩ := octEdgeZigzag_even hm F i
    have hqa : tetraCoordinate m (octEdgeZigzag m F.bigOtherSide (2 * j)).val F.a =
        -octRadius m := (octEdgeZigzag_even hm F.bigOtherSide j).2.2.1
    have hqj : tetraCoordinate m (octEdgeZigzag m F.bigOtherSide (2 * j)).val F.j =
        -octRadius m + 4 * (j : ℤ) := (octEdgeZigzag_even hm F.bigOtherSide j).2.2.2.1
    rw [hpa, hqa] at hba
    rw [hpj, hqj] at hbj
    omega
  · rintro ⟨rfl, rfl⟩
    have hpface := (octEdgeZigzag_even_mem hm F hi).1
    have hqface : OctBigFace m F.k (octEdgeZigzag m F.bigOtherSide (2 * 1)) :=
      (octEdgeZigzag_even_mem hm F.bigOtherSide hj).1
    apply big_face_twoStep_triangular hpface hqface F.ja.symm F.ka.symm F.kj.symm
    obtain ⟨hpA, hpk, hpj, hpa, hpb⟩ := octEdgeZigzag_even hm F 1
    have hqk : tetraCoordinate m (octEdgeZigzag m F.bigOtherSide (2 * 1)).val F.k =
        octRadius m := (octEdgeZigzag_even hm F.bigOtherSide 1).2.1
    have hqa : tetraCoordinate m (octEdgeZigzag m F.bigOtherSide (2 * 1)).val F.a =
        -octRadius m := (octEdgeZigzag_even hm F.bigOtherSide 1).2.2.1
    have hqj : tetraCoordinate m (octEdgeZigzag m F.bigOtherSide (2 * 1)).val F.j =
        -octRadius m + 4 * (1 : ℤ) := (octEdgeZigzag_even hm F.bigOtherSide 1).2.2.2.1
    have hqb : tetraCoordinate m (octEdgeZigzag m F.bigOtherSide (2 * 1)).val F.b =
        octRadius m - 4 * (1 : ℤ) := (octEdgeZigzag_even hm F.bigOtherSide 1).2.2.2.2
    have hkj := F.kj
    have hka := F.ka
    have hkb := F.kb
    have hja := F.ja
    have hjb := F.jb
    have hab := F.ab
    apply Subtype.ext
    apply tetraCoordinate_injective m
    funext r
    rw [tetraCoordinate_twoStep_A m hpA]
    rcases F.index_cases r with rfl | rfl | rfl | rfl
    all_goals split_ifs <;> omega

theorem small_face_different_sides_neighbours {m i j : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (hi0 : 1 ≤ i) (hj0 : 1 ≤ j) (hi : i < m - 1) (hj : j < m - 1) :
    OctTriangularNeighbours m (octEdgeZigzag m F (2 * i + 1))
      (octEdgeZigzag m F.smallOtherSide (2 * j + 1)) ↔ i = 1 ∧ j = 1 := by
  constructor
  · intro h
    have hbk := triangular_neighbours_coordinate_bounds h F.k
    have hbb := triangular_neighbours_coordinate_bounds h F.b
    obtain ⟨_, hpk, _, _, hpb⟩ := octEdgeZigzag_odd hm F i
    have hqk : tetraCoordinate m (octEdgeZigzag m F.smallOtherSide (2 * j + 1)).val F.k =
        octRadius m - 1 - 4 * (j : ℤ) := (octEdgeZigzag_odd hm F.smallOtherSide j).2.2.2.2
    have hqb : tetraCoordinate m (octEdgeZigzag m F.smallOtherSide (2 * j + 1)).val F.b =
        octRadius m - 1 := (octEdgeZigzag_odd hm F.smallOtherSide j).2.1
    rw [hpk, hqk] at hbk
    rw [hpb, hqb] at hbb
    omega
  · rintro ⟨rfl, rfl⟩
    have hpface := (octEdgeZigzag_odd_mem hm F hi).1
    have hqface : OctSmallFace m F.j (octEdgeZigzag m F.smallOtherSide (2 * 1 + 1)) :=
      (octEdgeZigzag_odd_mem hm F.smallOtherSide hj).1
    apply small_face_twoStep_triangular hpface hqface F.kb.symm F.jb.symm F.kj
    obtain ⟨hpB, hpk, hpj, hpa, hpb⟩ := octEdgeZigzag_odd hm F 1
    have hqk : tetraCoordinate m (octEdgeZigzag m F.smallOtherSide (2 * 1 + 1)).val F.k =
        octRadius m - 1 - 4 * (1 : ℤ) := (octEdgeZigzag_odd hm F.smallOtherSide 1).2.2.2.2
    have hqj : tetraCoordinate m (octEdgeZigzag m F.smallOtherSide (2 * 1 + 1)).val F.j =
        -octRadius m - 1 := (octEdgeZigzag_odd hm F.smallOtherSide 1).2.2.1
    have hqa : tetraCoordinate m (octEdgeZigzag m F.smallOtherSide (2 * 1 + 1)).val F.a =
        -octRadius m + 3 + 4 * (1 : ℤ) := (octEdgeZigzag_odd hm F.smallOtherSide 1).2.2.2.1
    have hqb : tetraCoordinate m (octEdgeZigzag m F.smallOtherSide (2 * 1 + 1)).val F.b =
        octRadius m - 1 := (octEdgeZigzag_odd hm F.smallOtherSide 1).2.1
    have hkj := F.kj
    have hka := F.ka
    have hkb := F.kb
    have hja := F.ja
    have hjb := F.jb
    have hab := F.ab
    apply Subtype.ext
    apply tetraCoordinate_injective m
    funext r
    rw [tetraCoordinate_twoStep_B m hpB]
    rcases F.index_cases r with rfl | rfl | rfl | rfl
    all_goals split_ifs <;> omega

theorem exterior_P3_big_same_side {m i j : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (hi : i < m) (hj : j < m) :
    ExteriorP3Link m (octEdgeZigzag m F (2 * i)) (octEdgeZigzag m F (2 * j)) ↔
      i + 1 = j ∨ j + 1 = i := by
  rw [exterior_P3_link_iff_triangular_neighbours]
  exact big_face_same_side_neighbours hm F hi hj

theorem exterior_P3_small_same_side {m i j : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (hi : i < m - 1) (hj : j < m - 1) :
    ExteriorP3Link m (octEdgeZigzag m F (2 * i + 1)) (octEdgeZigzag m F (2 * j + 1)) ↔
      i + 1 = j ∨ j + 1 = i := by
  rw [exterior_P3_link_iff_triangular_neighbours]
  exact small_face_same_side_neighbours hm F hi hj

theorem exterior_P3_big_different_sides {m i j : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (hi0 : 1 ≤ i) (hj0 : 1 ≤ j) (hi : i < m) (hj : j < m) :
    ExteriorP3Link m (octEdgeZigzag m F (2 * i))
      (octEdgeZigzag m F.bigOtherSide (2 * j)) ↔ i = 1 ∧ j = 1 := by
  rw [exterior_P3_link_iff_triangular_neighbours]
  exact big_face_different_sides_neighbours hm F hi0 hj0 hi hj

theorem exterior_P3_small_different_sides {m i j : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (hi0 : 1 ≤ i) (hj0 : 1 ≤ j) (hi : i < m - 1) (hj : j < m - 1) :
    ExteriorP3Link m (octEdgeZigzag m F (2 * i + 1))
      (octEdgeZigzag m F.smallOtherSide (2 * j + 1)) ↔ i = 1 ∧ j = 1 := by
  rw [exterior_P3_link_iff_triangular_neighbours]
  exact small_face_different_sides_neighbours hm F hi0 hj0 hi hj

end ProteinFolding.Tetrahedral
