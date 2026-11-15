import ProteinFolding.Cubic.Proofs.PackingPrefixSeparation
import ProteinFolding.Cubic.Proofs.PackingWallBridges
import ProteinFolding.Cubic.Proofs.PackingGeometryStraight

/-! Global separation of the actual prefix components from the front-wall
components. Front E/F decorations are separated by their H owners; the deep
P bridges are separated by their height and their upper row bound. -/

namespace ProteinFolding.CubicPackingPrefixWallsDisjoint

open CubicPacking CubicCertificates CubicPackingGeometry CubicPackingLift
open CubicPackingRouting CubicPackingPrefix CubicPackingBulk CubicPackingAttachments
open CubicPackingInitialDisjoint CubicPackingPrefixComponents CubicPackingPrefixBridges
open CubicPackingPrefixSeparation CubicPackingFaceBulkDisjoint CubicPackingWalls

theorem owned_front_height (d : ℕ) (p owner : Site)
    (hin : owner ∈ cube (fun _ => 0) (d + 2)) (hz : owner 2 = 0)
    (howned : OwnedBy (fun _ => 0) (d + 2) p owner) : -1 ≤ p 2 ∧ p 2 ≤ 0 := by
  rcases howned with rfl | ⟨hout, ha⟩
  · omega
  · have hb := adjacent_coordinate_bounds ha.symm 2
    have hlo : -1 ≤ p 2 := by omega
    refine ⟨hlo, ?_⟩
    by_contra hp
    have he : p 2 = owner 2 + 1 := by omega
    apply hout
    intro k
    by_cases hk : k = 2
    · subst k
      change 0 ≤ p 2 ∧ p 2 < 0 + ((d + 2 : ℕ) : ℤ)
      omega
    · rw [adjacent_max_axis_other_eq 2 k ha.symm he hk]
      exact hin k

theorem attached_front_bounds {N H : ℕ} (d : ℕ) (f : Fold cubicLattice N)
    (owner : Fin H → Site) (ha : AttachedTo (fun _ => 0) (d + 2) f owner)
    (hfront : ∀ k, owner k 2 = 0 ∧ 1 ≤ owner k 1 ∧ owner k 1 ≤ (d : ℤ)) (i : Fin N) :
    (-1 ≤ f.pos i 2 ∧ f.pos i 2 ≤ 0) ∧ (0 ≤ f.pos i 1 ∧ f.pos i 1 ≤ (d : ℤ) + 1) := by
  obtain ⟨k, hk⟩ := ha.2 i
  refine ⟨owned_front_height d _ _ (ha.1 k) (hfront k).1 hk, ?_⟩
  rcases hk with he | ⟨_, hadj⟩
  · rw [he]
    have h := hfront k
    omega
  · have hb := adjacent_coordinate_bounds hadj.symm 1
    have h := hfront k
    omega

theorem attached_front_near {N H : ℕ} (d : ℕ) (f : Fold cubicLattice N)
    (owner : Fin H → Site) (ha : AttachedTo (fun _ => 0) (d + 2) f owner) (i : Fin N) :
    NearCube d (f.pos i) := by
  obtain ⟨k, hk⟩ := ha.2 i
  rcases hk with he | ⟨_, hadj⟩
  · exact Or.inl (he ▸ ha.1 k)
  · exact Or.inr ⟨owner k, ha.1 k, hadj⟩

theorem near_height_lower {d : ℕ} {p : Site} (hp : NearCube d p) : -1 ≤ p 2 := by
  rcases hp with hp | ⟨q, hq, hadj⟩
  · have hz := (hp 2).1
    change 0 ≤ p 2 at hz
    omega
  · have hz := (hq 2).1
    have hb := adjacent_coordinate_bounds hadj.symm 2
    change 0 ≤ q 2 at hz
    omega

theorem far_attached_disjoint {N H : ℕ} (d : ℕ) (b : CubicPackingComponentChain.Block)
    (hf : IsFar d b) (f : Fold cubicLattice N) (owner : Fin H → Site)
    (ha : AttachedTo (fun _ => 0) (d + 2) f owner) : ∀ i j, b.fold.pos i ≠ f.pos j := by
  intro i j he
  have hn := attached_front_near d f owner ha j
  rw [← he] at hn
  rcases hn with hn | ⟨p, hp, hadj⟩
  · exact (hf i).1 hn
  · exact (hf i).2 p hp hadj

theorem initial_front_attached_disjoint {N H : ℕ} (d : ℕ) (hd : 0 < d)
    (initial : Fold cubicLattice (edgeWord (9 * d + 8)).length)
    (hH : hydrophobicSites (edgeWord (9 * d + 8)) initial = Set.range (skeletonPrefixFold d hd).pos)
    (hP : ∀ i, (edgeWord (9 * d + 8)).get i = .P → initial.pos i ∉ cube (fun _ => 0) (d + 2))
    (front : Fold cubicLattice N) (owner : Fin H → Site)
    (ha : AttachedTo (fun _ => 0) (d + 2) front owner)
    (hfront : ∀ k, owner k 2 = 0 ∧ 1 ≤ owner k 1 ∧ owner k 1 ≤ (d : ℤ)) :
    ∀ i j, initial.pos i ≠ front.pos j := by
  have hi : AttachedTo (fun _ => 0) (d + 2) initial (skeletonPrefixFold d hd).pos :=
    edgeWord_fold_attached _ initial (skeletonPrefixFold d hd) _ _ hH
      (fun k => (skeletonPrefixFold_skeleton d hd k).1) hP
  apply attached_folds_disjoint (fun _ => 0) (d + 2) initial front
    (skeletonPrefixFold d hd).pos owner hi ha
  intro i k he
  have hy := congrFun he 1
  have hz := congrFun he 2
  have hf := hfront k
  rcases skeletonPrefixFold_coordinate_cases d hd i with (hy0 | hyd) | hback <;> omega

theorem face_height_positive (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0)
    (face : CubicPackingFrameFaces.Face) (i : Fin (faceWord (d * d)).length) :
    1 ≤ (CubicPackingFrameFaces.faceFold d hd heven face).pos i 2 := by
  have hf := CubicPackingFrameFaces.faceFold_region d hd heven face i
  cases face <;> dsimp [CubicPackingFrameFaces.Region] at hf <;> omega

theorem back_edge_height_positive (d : ℕ) (i : Fin (edgeWord d).length) :
    1 ≤ (CubicPackingBackEdge.edgeFold d).pos i 2 := by
  have he := CubicPackingBackEdge.edgeFold_region d i
  dsimp [CubicPackingBackEdge.Region] at he
  omega

theorem farBlock_height_positive (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0) :
    ∀ b ∈ farBlocks d hd heven, ∀ i, 1 ≤ b.fold.pos i 2 := by
  intro b hb i
  simp only [farBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact (fourPos_bounds d (castPIndex i)).2.2.1.trans' (by omega)
  · have hb := leftLinkPos_bounds d heven (castPIndex i)
    change 1 ≤ leftLinkPos d (castPIndex i) 2
    omega
  · have hb := rightLinkFold_bounds d heven (castPIndex i)
    change 1 ≤ (rightLinkFold d).pos (castPIndex i) 2
    omega
  · exact (topLinkPos_bounds d hd (castPIndex i)).2.2.1

theorem approach_row_lower (d A : ℕ) (i : Fin (A + 8)) :
    (d : ℤ) + 1 - A ≤ approachPos d A i 1 := by
  have hi := i.isLt
  unfold approachPos approachPoint
  split_ifs <;> dsimp only [point] <;> omega

theorem bulk_front_attached_disjoint {N H : ℕ} (d A : ℕ) (hd : 0 < d) (heven : d % 2 = 0)
    (front : Fold cubicLattice N) (owner : Fin H → Site)
    (ha : AttachedTo (fun _ => 0) (d + 2) front owner)
    (hfront : ∀ k, owner k 2 = 0 ∧ 1 ≤ owner k 1 ∧ owner k 1 ≤ (d : ℤ)) :
    ∀ i j, (bulkApproachWordFold d A hd heven).pos i ≠ front.pos j := by
  intro i j he
  have hb := attached_front_bounds d front owner ha hfront j
  have hdis : front.pos j ≠ (bulkApproachWordFold d A hd heven).pos i := by
    apply disjoint_bulkApproachWord_of d A hd heven (front.pos j)
    · intro k hek
      have hk := bulk_bounds d hd heven k
      have hz := congrFun hek 2
      omega
    · intro k hek
      have hk := approachPos_exterior d A k
      have hy := congrFun hek 1
      have hz := congrFun hek 2
      change front.pos j 1 = approachPos d A k 1 at hy
      change front.pos j 2 = approachPos d A k 2 at hz
      omega
  exact hdis he.symm

theorem bulk_deep_front_disjoint {N : ℕ} (d A : ℕ) (hd : 0 < d) (heven : d % 2 = 0)
    (front : Fold cubicLattice N)
    (hz : ∀ j, front.pos j 2 ≤ -2) (hy : ∀ j, front.pos j 1 ≤ (d : ℤ) - A) :
    ∀ i j, (bulkApproachWordFold d A hd heven).pos i ≠ front.pos j := by
  intro i j he
  have hdis : front.pos j ≠ (bulkApproachWordFold d A hd heven).pos i := by
    apply disjoint_bulkApproachWord_of d A hd heven (front.pos j)
    · intro k hek
      have hk := bulk_bounds d hd heven k
      have hez := congrFun hek 2
      have hfj := hz j
      omega
    · intro k hek
      have hk := approach_row_lower d A k
      have hey := congrFun hek 1
      have hfj := hy j
      change front.pos j 1 = approachPos d A k 1 at hey
      omega
  exact hdis he.symm

theorem ordinary_after_initial_height (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0)
    (initial : Fold cubicLattice (edgeWord (9 * d + 8)).length) (hlast) :
    ∀ b ∈ (ordinaryBlocks d hd heven initial hlast).tail, ∀ i, 1 ≤ b.fold.pos i 2 := by
  intro b hb i
  simp only [ordinaryBlocks, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact back_edge_height_positive d i
  · change 1 ≤ point d ((d : ℤ) + 2) d 2
    dsimp [point]
    omega
  · exact (CubicPackingTopFace.topFold_bounds d hd heven i).2.1.1
  all_goals exact face_height_positive d (by omega) heven _ i

/-- Every actual prefix component avoids any complete E/F component attached
to interior rows of the front face. The arbitrary initial greedy lift is
included; its exterior P decorations need no prescribed normal choices. -/
theorem prefix_components_front_attached_disjoint {N H : ℕ} (d A : ℕ)
    (hd : 2 ≤ d) (heven : d % 2 = 0)
    (initial : Fold cubicLattice (edgeWord (9 * d + 8)).length) (hlast)
    (hH : hydrophobicSites (edgeWord (9 * d + 8)) initial =
      Set.range (skeletonPrefixFold d (by omega)).pos)
    (hP : ∀ i, (edgeWord (9 * d + 8)).get i = .P → initial.pos i ∉ cube (fun _ => 0) (d + 2))
    (front : Fold cubicLattice N) (owner : Fin H → Site)
    (ha : AttachedTo (fun _ => 0) (d + 2) front owner)
    (hfront : ∀ k, owner k 2 = 0 ∧ 1 ≤ owner k 1 ∧ owner k 1 ≤ (d : ℤ)) :
    ∀ b ∈ initialBlock d initial hlast :: tailBlocks d A hd heven, ∀ i j, b.fold.pos i ≠ front.pos j := by
  intro b hb i j
  have hm := (regroup_perm d A hd heven initial hlast).mem_iff.mpr hb
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · rcases List.mem_cons.mp hm with hb | hb
      · subst b
        exact initial_front_attached_disjoint d (by omega) initial hH hP front owner ha hfront i j
      · have hp := ordinary_after_initial_height d hd heven initial hlast b hb i
        have hq := attached_front_bounds d front owner ha hfront j
        intro he
        have hz := congrFun he 2
        omega
    · exact far_attached_disjoint d b (far_isFar d hd heven b hm) front owner ha i j
  · have hb := List.mem_singleton.mp hm
    subst b
    exact bulk_front_attached_disjoint d A (by omega) heven front owner ha hfront i j

/-- Every actual prefix component avoids every sufficiently low front P
bridge. Its z coordinate is at most -2 and its y coordinate is below the
bulk approach's final row; these bounds cover both kinds of wall bridges. -/
theorem prefix_components_deep_front_disjoint {N : ℕ} (d A : ℕ)
    (hd : 2 ≤ d) (heven : d % 2 = 0)
    (initial : Fold cubicLattice (edgeWord (9 * d + 8)).length) (hlast)
    (hH : hydrophobicSites (edgeWord (9 * d + 8)) initial =
      Set.range (skeletonPrefixFold d (by omega)).pos)
    (front : Fold cubicLattice N)
    (hz : ∀ j, front.pos j 2 ≤ -2) (hy : ∀ j, front.pos j 1 ≤ (d : ℤ) - A) :
    ∀ b ∈ initialBlock d initial hlast :: tailBlocks d A hd heven, ∀ i j, b.fold.pos i ≠ front.pos j := by
  intro b hb i j he
  have hm := (regroup_perm d A hd heven initial hlast).mem_iff.mpr hb
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · have hp := near_height_lower (ordinary_isNear d hd heven initial hlast hH b hm i)
      have hq := hz j
      have hez := congrFun he 2
      omega
    · have hp := farBlock_height_positive d hd heven b hm i
      have hq := hz j
      have hez := congrFun he 2
      omega
  · have hb := List.mem_singleton.mp hm
    subst b
    exact bulk_deep_front_disjoint d A (by omega) heven front hz hy i j he

theorem append_owners_rows {H K : ℕ} (d : ℕ) (p : Fin H → Site) (q : Fin K → Site)
    (hp : ∀ i, 1 ≤ p i 1 ∧ p i 1 ≤ (d : ℤ))
    (hq : ∀ i, 1 ≤ q i 1 ∧ q i 1 ≤ (d : ℤ)) :
    ∀ i, 1 ≤ Fin.append p q i 1 ∧ Fin.append p q i 1 ≤ (d : ℤ) := by
  intro i
  cases i using Fin.addCases with
  | left i => simpa only [Fin.append_left] using hp i
  | right i => simpa only [Fin.append_right] using hq i

theorem unitOwners_rows (d A : ℕ) (top : ℤ) (hTop : (2 * A + 2 : ℕ) ≤ top ∧ top ≤ d) :
    ∀ i, 1 ≤ unitOwners d A top i 1 ∧ unitOwners d A top i 1 ≤ (d : ℤ) := by
  apply append_owners_rows
  · intro i
    have hi := i.isLt
    change 1 ≤ top - (A : ℤ) + 1 + i.val ∧ top - (A : ℤ) + 1 + i.val ≤ (d : ℤ)
    omega
  · apply append_owners_rows
    · intro i
      change 1 ≤ top ∧ top ≤ (d : ℤ)
      omega
    · apply append_owners_rows
      · intro i
        have hi := i.isLt
        change 1 ≤ top - i.val ∧ top - i.val ≤ (d : ℤ)
        omega
      · apply append_owners_rows
        · intro i
          change 1 ≤ top - ((2 * A + 2 : ℕ) : ℤ) + 1 ∧ top - ((2 * A + 2 : ℕ) : ℤ) + 1 ≤ (d : ℤ)
          omega
        · intro i
          have hi := i.isLt
          change 1 ≤ top - ((2 * A + 2 : ℕ) : ℤ) + 1 + i.val ∧
            top - ((2 * A + 2 : ℕ) : ℤ) + 1 + i.val ≤ (d : ℤ)
          omega

theorem unitPBridge_deep_bounds (d A : ℕ) (top : ℤ) (htop : top ≤ d)
    (i : Fin (List.replicate (2 * A) Residue.P).length) :
    (unitPBridge d A top).pos i 2 ≤ -2 ∧ (unitPBridge d A top).pos i 1 ≤ (d : ℤ) - A := by
  change (-2 : ℤ) ≤ -2 ∧ lineRow (top - A - 2) false (Fin.cast (List.length_replicate ..) i).val ≤ (d : ℤ) - A
  dsimp [lineRow]
  omega

theorem gapPBridge_deep_bounds (d A : ℕ) (y : ℤ) (hy : y + 2 * A + 1 ≤ (d : ℤ) - A)
    (i : Fin (List.replicate (2 * A + 4) Residue.P).length) :
    (gapPBridge d A y).pos i 2 ≤ -2 ∧ (gapPBridge d A y).pos i 1 ≤ (d : ℤ) - A := by
  have h := gapPBridge_location d A y i
  omega

theorem wallTop_bounds (q Q : ℕ) (j : Fin q) :
    ((2 * alpha Q + 2 : ℕ) : ℤ) ≤ wallTop q Q j ∧ wallTop q Q j ≤ depth q Q := by
  have hj : j.val + 1 ≤ q := by omega
  have hm := Nat.mul_le_mul_right (beta Q) hj
  have hb : beta Q = 2 * alpha Q + 2 := by dsimp [alpha, beta]; omega
  have he : (depth q Q : ℤ) = (q : ℤ) * beta Q := by simp [depth]
  have hm' : (j.val : ℤ) * beta Q + beta Q ≤ (q : ℤ) * beta Q := by
    have hm'' : j.val * beta Q + beta Q ≤ q * beta Q := by
      simpa only [Nat.add_mul, Nat.one_mul] using hm
    exact_mod_cast hm''
  have hnon : 0 ≤ (j.val : ℤ) * beta Q := by positivity
  unfold wallTop
  rw [he]
  have hb' : (beta Q : ℤ) = ((2 * alpha Q + 2 : ℕ) : ℤ) := congrArg (fun n : ℕ => (n : ℤ)) hb
  omega

/-- The actual wall-unit owner paths satisfy exactly the front-support
premises needed by the complete prefix collision matrix. -/
theorem wallUnitOwners_front (q Q : ℕ) (j : Fin q) :
    ∀ k, unitOwners (depth q Q) (alpha Q) (wallTop q Q j) k 2 = 0 ∧
      1 ≤ unitOwners (depth q Q) (alpha Q) (wallTop q Q j) k 1 ∧
      unitOwners (depth q Q) (alpha Q) (wallTop q Q j) k 1 ≤ (depth q Q : ℤ) := by
  intro k
  exact ⟨unitOwners_plane _ _ _ k, unitOwners_rows _ _ _ (wallTop_bounds q Q j) k⟩

theorem unitPBridge_wallTop_deep (q Q : ℕ) (j : Fin q)
    (i : Fin (List.replicate (2 * alpha Q) Residue.P).length) :
    (unitPBridge (depth q Q) (alpha Q) (wallTop q Q j)).pos i 2 ≤ -2 ∧
      (unitPBridge (depth q Q) (alpha Q) (wallTop q Q j)).pos i 1 ≤
        (depth q Q : ℤ) - alpha Q :=
  unitPBridge_deep_bounds _ _ _ (wallTop_bounds q Q j).2 i

theorem result_disjoint_front {a : CubicPackingComponentChain.Block} {xs : List CubicPackingComponentChain.Block}
    (result : CubicPackingComponentChain.Result a xs) {N : ℕ} (front : Fold cubicLattice N)
    (hsep : ∀ b ∈ a :: xs, ∀ i j, b.fold.pos i ≠ front.pos j) :
    ∀ i j, result.block.fold.pos i ≠ front.pos j := by
  intro i j he
  obtain ⟨b, hb, k, hk⟩ := (result.sites (result.block.fold.pos i)).mp ⟨i, rfl⟩
  exact hsep b hb k j (hk.trans he)

end ProteinFolding.CubicPackingPrefixWallsDisjoint
