import ProteinFolding.Cubic.Proofs.PackingPrefixWallsDisjoint
import ProteinFolding.Cubic.Proofs.PackingPrefixFold
import ProteinFolding.Cubic.Proofs.PackingItemConnectors
import ProteinFolding.Cubic.Proofs.PackingGapFold

/-! Separation of the exterior item routes from the complete prefix and
the front decorations. The statements concern every visited site, including
the inserted P words and the arbitrary greedy lift of the initial edge. -/

namespace ProteinFolding.CubicPackingFrameRoutingDisjoint

open CubicPacking CubicCertificates CubicPackingGeometry CubicPackingLift
open CubicPackingRouting CubicPackingPrefix CubicPackingBulk CubicPackingAttachments
open CubicPackingInitialDisjoint CubicPackingPrefixComponents CubicPackingPrefixBridges
open CubicPackingPrefixSeparation CubicPackingFaceBulkDisjoint CubicPackingWalls
open CubicPackingPrefixWallsDisjoint

theorem approach_height_lower (d A : ℕ) (i : Fin (A + 8)) :
    -2 ≤ approachPos d A i 2 := by
  unfold approachPos approachPoint
  split_ifs <;> dsimp only [point] <;> omega

theorem bulk_low_front_disjoint {N : ℕ} (d A : ℕ) (hd : 0 < d) (heven : d % 2 = 0)
    (front : Fold cubicLattice N)
    (hz : ∀ j, front.pos j 2 ≤ -2)
    (hlow : ∀ j, (front.pos j 0 = d ∧ front.pos j 1 ≤ (d : ℤ)) ∨
      front.pos j 2 ≤ -3 ∨ front.pos j 1 ≤ (d : ℤ) - A) :
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
      have hey := congrFun hek 1
      have hex := congrFun hek 0
      have hez := congrFun hek 2
      change front.pos j 1 = approachPos d A k 1 at hey
      change front.pos j 0 = approachPos d A k 0 at hex
      change front.pos j 2 = approachPos d A k 2 at hez
      rcases hlow j with ⟨hx, hy⟩ | hdeep | hrow
      · have hk := approachPos_above_or_outer d A k
        omega
      · have hk := approach_height_lower d A k
        omega
      · have hk := approach_row_lower d A k
        omega
  exact hdis he.symm

/-- A uniform low-route criterion for all thirteen actual prefix pieces. -/
theorem prefix_components_low_disjoint {N : ℕ} (d A : ℕ)
    (hd : 2 ≤ d) (heven : d % 2 = 0)
    (initial : Fold cubicLattice (edgeWord (9 * d + 8)).length) (hlast)
    (hH : hydrophobicSites (edgeWord (9 * d + 8)) initial =
      Set.range (skeletonPrefixFold d (by omega)).pos)
    (front : Fold cubicLattice N)
    (hz : ∀ j, front.pos j 2 ≤ -2)
    (hlow : ∀ j, (front.pos j 0 = d ∧ front.pos j 1 ≤ (d : ℤ)) ∨
      front.pos j 2 ≤ -3 ∨ front.pos j 1 ≤ (d : ℤ) - A) :
    ∀ b ∈ initialBlock d initial hlast :: tailBlocks d A hd heven,
      ∀ i j, b.fold.pos i ≠ front.pos j := by
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
    exact bulk_low_front_disjoint d A (by omega) heven front hz hlow i j he

theorem portConnector_low (d A u v h r n : ℕ) (hh : 3 ≤ h) (hr : 0 < r)
    (huv : u ≠ v) (hu : u ≤ d) (hv : v ≤ d)
    (hlen : routeSteps h r (portWidth u v) = 4 * n + 3) (i : Fin (4 * n)) :
    ((portConnector d u v h r n (by omega) hr huv hlen).pos i 0 = d ∧
      (portConnector d u v h r n (by omega) hr huv hlen).pos i 1 ≤ (d : ℤ)) ∨
    (portConnector d u v h r n (by omega) hr huv hlen).pos i 2 ≤ -3 ∨
    (portConnector d u v h r n (by omega) hr huv hlen).pos i 1 ≤ (d : ℤ) - A := by
  have hp := portConnector_pillar_or_depth d u v h r n (by omega) hr huv hlen i
  rcases hp with ⟨hx, hy | hy⟩ | ⟨_, hz⟩
  · exact Or.inl ⟨hx, by omega⟩
  · exact Or.inl ⟨hx, by omega⟩
  · exact Or.inr (Or.inl (by omega))

theorem prefix_components_portConnector_disjoint (d A u v h r n : ℕ)
    (hd : 2 ≤ d) (heven : d % 2 = 0)
    (initial : Fold cubicLattice (edgeWord (9 * d + 8)).length) (hlast)
    (hH : hydrophobicSites (edgeWord (9 * d + 8)) initial =
      Set.range (skeletonPrefixFold d (by omega)).pos)
    (hh : 3 ≤ h) (hr : 0 < r) (huv : u ≠ v) (hu : u ≤ d) (hv : v ≤ d)
    (hlen : routeSteps h r (portWidth u v) = 4 * n + 3) :
    ∀ b ∈ initialBlock d initial hlast :: tailBlocks d A hd heven,
      ∀ i j, b.fold.pos i ≠ (portConnector d u v h r n (by omega) hr huv hlen).pos j := by
  apply prefix_components_low_disjoint d A hd heven initial hlast hH
  · exact portConnector_below d u v h r n (by omega) hr huv hlen
  · exact portConnector_low d A u v h r n hh hr huv hu hv hlen

/-- The first route has only its starting pillar at depth two or three;
its transfer is at depth four and its remaining rectangle is at depth five. -/
theorem initialConnector_region (d : ℤ) (h r Y v n : ℕ)
    (hh : 5 ≤ h) (hr : 0 < r) (hv : 0 < v)
    (hlen : initialSteps h r Y v = 4 * n + 3) (i : Fin (4 * n)) :
    ((initialConnector d h r Y v n hh hr hv hlen).pos i 0 = d + 1 ∧
      (initialConnector d h r Y v n hh hr hv hlen).pos i 1 = Y) ∨
    (initialConnector d h r Y v n hh hr hv hlen).pos i 2 ≤ -4 ∨
    ((initialConnector d h r Y v n hh hr hv hlen).pos i 0 = d ∧
      ((initialConnector d h r Y v n hh hr hv hlen).pos i 1 = 0 ∨
        (initialConnector d h r Y v n hh hr hv hlen).pos i 1 = v)) := by
  have hi := i.isLt
  unfold initialSteps routeSteps at hlen
  change (initialPoint d h r Y v (i.val + 2) 0 = d + 1 ∧
    initialPoint d h r Y v (i.val + 2) 1 = Y) ∨
    initialPoint d h r Y v (i.val + 2) 2 ≤ -4 ∨
    (initialPoint d h r Y v (i.val + 2) 0 = d ∧
      (initialPoint d h r Y v (i.val + 2) 1 = 0 ∨
        initialPoint d h r Y v (i.val + 2) 1 = v))
  unfold initialPoint routePoint
  split_ifs <;> dsimp only [point] <;> omega

theorem prefix_components_initialConnector_disjoint (d A h r Y v n : ℕ)
    (hd : 2 ≤ d) (heven : d % 2 = 0)
    (initial : Fold cubicLattice (edgeWord (9 * d + 8)).length) (hlast)
    (hH : hydrophobicSites (edgeWord (9 * d + 8)) initial =
      Set.range (skeletonPrefixFold d (by omega)).pos)
    (hh : 5 ≤ h) (hr : 0 < r) (hv : 0 < v) (hvd : v ≤ d)
    (hY : (Y : ℤ) ≤ (d : ℤ) - A)
    (hlen : initialSteps h r Y v = 4 * n + 3) :
    ∀ b ∈ initialBlock d initial hlast :: tailBlocks d A hd heven,
      ∀ i j, b.fold.pos i ≠ (initialConnector d h r Y v n hh hr hv hlen).pos j := by
  apply prefix_components_low_disjoint d A hd heven initial hlast hH
  · exact initialConnector_below_face_P d h r Y v n hh hr hv hlen
  · intro j
    have hp := initialConnector_region d h r Y v n hh hr hv hlen j
    rcases hp with ⟨_, hy⟩ | hz | ⟨hx, hy | hy⟩
    · exact Or.inr (Or.inr (by omega))
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inl ⟨hx, by omega⟩
    · exact Or.inl ⟨hx, by omega⟩

theorem attached_deep_disjoint {N H M : ℕ} (d : ℕ)
    (front : Fold cubicLattice N) (owner : Fin H → Site)
    (ha : AttachedTo (fun _ => 0) (d + 2) front owner)
    (deep : Fold cubicLattice M) (hz : ∀ j, deep.pos j 2 ≤ -2) :
    ∀ i j, front.pos i ≠ deep.pos j := by
  intro i j he
  have hp := near_height_lower (attached_front_near d front owner ha i)
  have hq := hz j
  have hez := congrFun he 2
  omega

theorem attached_portConnector_disjoint {N H : ℕ} (d u v h r n : ℕ)
    (front : Fold cubicLattice N) (owner : Fin H → Site)
    (ha : AttachedTo (fun _ => 0) (d + 2) front owner)
    (hh : 2 ≤ h) (hr : 0 < r) (huv : u ≠ v)
    (hlen : routeSteps h r (portWidth u v) = 4 * n + 3) :
    ∀ i j, front.pos i ≠ (portConnector d u v h r n (by omega) hr huv hlen).pos j :=
  attached_deep_disjoint d front owner ha _ (portConnector_below d u v h r n hh hr huv hlen)

theorem attached_initialConnector_disjoint {N H : ℕ} (d h r Y v n : ℕ)
    (front : Fold cubicLattice N) (owner : Fin H → Site)
    (ha : AttachedTo (fun _ => 0) (d + 2) front owner)
    (hh : 5 ≤ h) (hr : 0 < r) (hv : 0 < v)
    (hlen : initialSteps h r Y v = 4 * n + 3) :
    ∀ i j, front.pos i ≠ (initialConnector d h r Y v n hh hr hv hlen).pos j :=
  attached_deep_disjoint d front owner ha _ (initialConnector_below_face_P d h r Y v n hh hr hv hlen)

theorem shallow_outer_portConnector_disjoint {N : ℕ} (d u v h r n : ℕ)
    (front : Fold cubicLattice N)
    (hx : ∀ i, front.pos i 0 = (d : ℤ) + 1)
    (hz : ∀ i, -3 ≤ front.pos i 2)
    (hh : 4 ≤ h) (hr : 0 < r) (huv : u ≠ v)
    (hlen : routeSteps h r (portWidth u v) = 4 * n + 3) :
    ∀ i j, front.pos i ≠ (portConnector d u v h r n (by omega) hr huv hlen).pos j := by
  intro i j he
  have hxi := hx i
  have hzi := hz i
  have hex := congrFun he 0
  have hez := congrFun he 2
  have hp := portConnector_pillar_or_depth d u v h r n (by omega) hr huv hlen j
  rcases hp with ⟨hpx, _⟩ | ⟨_, hpz⟩ <;> omega

theorem shallow_outer_initialConnector_disjoint {N : ℕ} (d h r Y v n : ℕ)
    (front : Fold cubicLattice N)
    (hx : ∀ i, front.pos i 0 = (d : ℤ) + 1)
    (hz : ∀ i, -3 ≤ front.pos i 2)
    (hy : ∀ i, front.pos i 1 < (Y : ℤ))
    (hh : 5 ≤ h) (hr : 0 < r) (hv : 0 < v)
    (hlen : initialSteps h r Y v = 4 * n + 3) :
    ∀ i j, front.pos i ≠ (initialConnector d h r Y v n hh hr hv hlen).pos j := by
  intro i j he
  have hxi := hx i
  have hzi := hz i
  have hyi := hy i
  have hex := congrFun he 0
  have hey := congrFun he 1
  have hez := congrFun he 2
  have hp := initialConnector_region d h r Y v n hh hr hv hlen j
  rcases hp with ⟨_, hpy⟩ | hpz | ⟨hpx, _⟩ <;> omega

theorem unitPBridge_shallow (d A : ℕ) (top : ℤ)
    (i : Fin (List.replicate (2 * A) Residue.P).length) :
    (unitPBridge d A top).pos i 0 = (d : ℤ) + 1 ∧
      -3 ≤ (unitPBridge d A top).pos i 2 := by
  constructor <;> change _
  · rfl
  · change (-3 : ℤ) ≤ -2
    omega

theorem unitPBridge_row_strict (d A : ℕ) (top : ℤ) (htop : top ≤ d)
    (i : Fin (List.replicate (2 * A) Residue.P).length) :
    (unitPBridge d A top).pos i 1 < (d : ℤ) - A := by
  change lineRow (top - A - 2) false (Fin.cast (List.length_replicate ..) i).val < (d : ℤ) - A
  dsimp [lineRow]
  omega

theorem unitPBridge_portConnector_disjoint (d A u v h r n : ℕ) (top : ℤ)
    (hh : 4 ≤ h) (hr : 0 < r) (huv : u ≠ v)
    (hlen : routeSteps h r (portWidth u v) = 4 * n + 3) :
    ∀ i j, (unitPBridge d A top).pos i ≠
      (portConnector d u v h r n (by omega) hr huv hlen).pos j :=
  shallow_outer_portConnector_disjoint d u v h r n _
    (fun i => (unitPBridge_shallow d A top i).1)
    (fun i => (unitPBridge_shallow d A top i).2) hh hr huv hlen

theorem unitPBridge_initialConnector_disjoint (d A h r Y v n : ℕ) (top : ℤ)
    (htop : top ≤ d) (hY : (Y : ℤ) = (d : ℤ) - A)
    (hh : 5 ≤ h) (hr : 0 < r) (hv : 0 < v)
    (hlen : initialSteps h r Y v = 4 * n + 3) :
    ∀ i j, (unitPBridge d A top).pos i ≠
      (initialConnector d h r Y v n hh hr hv hlen).pos j := by
  apply shallow_outer_initialConnector_disjoint d h r Y v n _
  · exact fun i => (unitPBridge_shallow d A top i).1
  · exact fun i => (unitPBridge_shallow d A top i).2
  · intro i
    rw [hY]
    exact unitPBridge_row_strict d A top htop i

theorem gapPBridge_portConnector_disjoint (d A u v h r n : ℕ) (y : ℤ)
    (hh : 4 ≤ h) (hr : 0 < r) (huv : u ≠ v)
    (hlen : routeSteps h r (portWidth u v) = 4 * n + 3) :
    ∀ i j, (gapPBridge d A y).pos i ≠
      (portConnector d u v h r n (by omega) hr huv hlen).pos j := by
  apply shallow_outer_portConnector_disjoint d u v h r n _ ?_ ?_ hh hr huv hlen
  · exact fun i => (gapPBridge_location d A y i).1
  · intro i
    have hi := gapPBridge_location d A y i
    omega

theorem gapPBridge_initialConnector_disjoint (d A h r Y v n : ℕ) (y : ℤ)
    (hy : y + 2 * A + 1 < (Y : ℤ))
    (hh : 5 ≤ h) (hr : 0 < r) (hv : 0 < v)
    (hlen : initialSteps h r Y v = 4 * n + 3) :
    ∀ i j, (gapPBridge d A y).pos i ≠
      (initialConnector d h r Y v n hh hr hv hlen).pos j := by
  apply shallow_outer_initialConnector_disjoint d h r Y v n _
  · exact fun i => (gapPBridge_location d A y i).1
  · intro i
    have hi := gapPBridge_location d A y i
    omega

  · intro i
    have hi := gapPBridge_location d A y i
    omega

theorem gap_bridge_row_strict (q Q k : ℕ) (hk : k + 1 < q) :
    gapLast (alpha Q) ((alpha Q : ℤ) + 1) k + 2 * alpha Q + 1 <
      (depth q Q : ℤ) - alpha Q := by
  have hm := Nat.mul_le_mul_right (beta Q) (show k + 2 ≤ q by omega)
  have hm' : ((k : ℤ) + 2) * beta Q ≤ (depth q Q : ℤ) := by
    exact_mod_cast hm
  have hb : (beta Q : ℤ) = 2 * (alpha Q : ℤ) + 2 := by dsimp [beta, alpha]; omega
  unfold gapLast
  rw [add_mul, hb] at hm'
  omega

/-- The full gap chain's only sites on its last row are shallow. Thus the
exceptional initial pillar clears that row as well as every earlier row. -/
theorem gapRegion_initialConnector_disjoint {N : ℕ} (d A h r Y v n k : ℕ) (start : ℤ)
    (front : Fold cubicLattice N)
    (hregion : ∀ i, GapRegion d A start k (front.pos i))
    (hY : gapLast A start k = (Y : ℤ))
    (hh : 5 ≤ h) (hr : 0 < r) (hv : 0 < v)
    (hlen : initialSteps h r Y v = 4 * n + 3) :
    ∀ i j, front.pos i ≠ (initialConnector d h r Y v n hh hr hv hlen).pos j := by
  intro i j he
  have hi := hregion i
  have hj := initialConnector_region d h r Y v n hh hr hv hlen j
  have hzb := initialConnector_below_face_P d h r Y v n hh hr hv hlen j
  have hx := congrFun he 0
  have hy := congrFun he 1
  have hz := congrFun he 2
  dsimp only [GapRegion] at hi
  rcases hj with ⟨_, hjy⟩ | hjz | ⟨hjx, _⟩
  · have heq : front.pos i 1 = gapLast A start k := by omega
    have hs := hi.2.2.1 heq
    omega
  · omega
  · omega

theorem gapRegion_portConnector_disjoint {N : ℕ} (d A u v h r n k : ℕ) (start : ℤ)
    (front : Fold cubicLattice N)
    (hregion : ∀ i, GapRegion d A start k (front.pos i))
    (hh : 4 ≤ h) (hr : 0 < r) (huv : u ≠ v)
    (hlen : routeSteps h r (portWidth u v) = 4 * n + 3) :
    ∀ i j, front.pos i ≠ (portConnector d u v h r n (by omega) hr huv hlen).pos j := by
  intro i j he
  have hi := hregion i
  have hj := portConnector_pillar_or_depth d u v h r n (by omega) hr huv hlen j
  have hx := congrFun he 0
  have hz := congrFun he 2
  dsimp only [GapRegion] at hi
  rcases hj with ⟨hjx, _⟩ | ⟨_, hjz⟩ <;> omega

/-- Transfer the component collision matrix through the assembled prefix's
exact visited-site decomposition. -/
theorem witness_disjoint {q Q N : ℕ} {hd : 2 ≤ depth q Q} {heven : depth q Q % 2 = 0}
    (w : CubicPackingPrefixFold.Witness q Q hd heven) (front : Fold cubicLattice N)
    (hsep : ∀ b ∈ initialBlock (depth q Q) w.initial w.initial_last ::
        tailBlocks (depth q Q) (alpha Q) hd heven, ∀ i j, b.fold.pos i ≠ front.pos j) :
    ∀ i j, w.fold.pos i ≠ front.pos j := by
  intro i j he
  obtain ⟨k, hk⟩ | ⟨b, hb, k, hk⟩ := (w.sites (w.fold.pos i)).mp ⟨i, rfl⟩
  · exact hsep _ (List.mem_cons_self) k j (hk.trans he)
  · exact hsep b (List.mem_cons_of_mem _ hb) k j (hk.trans he)

theorem witness_front_attached_disjoint {q Q N H : ℕ}
    {hd : 2 ≤ depth q Q} {heven : depth q Q % 2 = 0}
    (w : CubicPackingPrefixFold.Witness q Q hd heven)
    (front : Fold cubicLattice N) (owner : Fin H → Site)
    (ha : AttachedTo (fun _ => 0) (depth q Q + 2) front owner)
    (hfront : ∀ k, owner k 2 = 0 ∧ 1 ≤ owner k 1 ∧ owner k 1 ≤ (depth q Q : ℤ)) :
    ∀ i j, w.fold.pos i ≠ front.pos j := by
  apply witness_disjoint w front
  exact prefix_components_front_attached_disjoint (depth q Q) (alpha Q) hd heven
    w.initial w.initial_last w.initial_H w.initial_P front owner ha hfront

theorem witness_deep_front_disjoint {q Q N : ℕ}
    {hd : 2 ≤ depth q Q} {heven : depth q Q % 2 = 0}
    (w : CubicPackingPrefixFold.Witness q Q hd heven)
    (front : Fold cubicLattice N)
    (hz : ∀ j, front.pos j 2 ≤ -2)
    (hy : ∀ j, front.pos j 1 ≤ (depth q Q : ℤ) - alpha Q) :
    ∀ i j, w.fold.pos i ≠ front.pos j := by
  apply witness_disjoint w front
  exact prefix_components_deep_front_disjoint (depth q Q) (alpha Q) hd heven
    w.initial w.initial_last w.initial_H front hz hy

theorem witness_portConnector_disjoint {q Q : ℕ}
    {hd : 2 ≤ depth q Q} {heven : depth q Q % 2 = 0}
    (w : CubicPackingPrefixFold.Witness q Q hd heven) (u v h r n : ℕ)
    (hh : 3 ≤ h) (hr : 0 < r) (huv : u ≠ v)
    (hu : u ≤ depth q Q) (hv : v ≤ depth q Q)
    (hlen : routeSteps h r (portWidth u v) = 4 * n + 3) :
    ∀ i j, w.fold.pos i ≠
      (portConnector (depth q Q) u v h r n (by omega) hr huv hlen).pos j := by
  apply witness_disjoint w _
  exact prefix_components_portConnector_disjoint (depth q Q) (alpha Q) u v h r n hd heven
    w.initial w.initial_last w.initial_H hh hr huv hu hv hlen

theorem witness_initialConnector_disjoint {q Q : ℕ}
    {hd : 2 ≤ depth q Q} {heven : depth q Q % 2 = 0}
    (w : CubicPackingPrefixFold.Witness q Q hd heven) (h r Y v n : ℕ)
    (hh : 5 ≤ h) (hr : 0 < r) (hv : 0 < v) (hvd : v ≤ depth q Q)
    (hY : (Y : ℤ) ≤ (depth q Q : ℤ) - alpha Q)
    (hlen : initialSteps h r Y v = 4 * n + 3) :
    ∀ i j, w.fold.pos i ≠
      (initialConnector (depth q Q) h r Y v n hh hr hv hlen).pos j := by
  apply witness_disjoint w _
  exact prefix_components_initialConnector_disjoint (depth q Q) (alpha Q) h r Y v n hd heven
    w.initial w.initial_last w.initial_H hh hr hv hvd hY hlen

end ProteinFolding.CubicPackingFrameRoutingDisjoint
