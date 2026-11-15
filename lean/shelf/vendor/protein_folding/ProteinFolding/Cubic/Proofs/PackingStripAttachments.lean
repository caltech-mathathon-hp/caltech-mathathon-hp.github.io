import ProteinFolding.Cubic.Proofs.PackingItemStrips
import ProteinFolding.Cubic.Proofs.PackingPrefixWallsDisjoint
import ProteinFolding.Cubic.Proofs.PackingPrefixInterfaces

/-! The complete item strip is attached to its own H path. The generic
prefix separation theorem therefore also separates every item strip, including
its P residues, without a separate collision check for each prefix component. -/

namespace ProteinFolding.CubicPackingItems

open CubicPacking CubicPackingLift CubicPackingGeometry CubicCertificates

theorem stripPos_front_bounds (d width : ℕ) (upper : ℤ)
    (hlower : 0 ≤ upper - width) (hupper : upper ≤ d) (k : Fin (d * width)) :
    stripPos d width upper k ∈ cube (fun _ => 0) (d + 2) ∧
      stripPos d width upper k 2 = 0 ∧
      1 ≤ stripPos d width upper k 1 ∧ stripPos d width upper k 1 ≤ (d : ℤ) := by
  have hb := (stripPos_image d width upper (stripPos d width upper k)).mp ⟨k, rfl⟩
  refine ⟨?_, hb.2.2.2.2, by omega, by omega⟩
  intro axis
  match axis with
  | 0 =>
    change (0 : ℤ) ≤ stripPos d width upper k 0 ∧
      stripPos d width upper k 0 < 0 + ((d + 2 : ℕ) : ℤ)
    omega
  | 1 =>
    change (0 : ℤ) ≤ stripPos d width upper k 1 ∧
      stripPos d width upper k 1 < 0 + ((d + 2 : ℕ) : ℤ)
    omega
  | 2 =>
    change (0 : ℤ) ≤ stripPos d width upper k 2 ∧
      stripPos d width upper k 2 < 0 + ((d + 2 : ℕ) : ℤ)
    omega

theorem stripWordFold_attached (d width : ℕ) (upper : ℤ) (hd : 0 < d)
    (heven : 2 ∣ d * width) (hlower : 0 ≤ upper - width) (hupper : upper ≤ d) :
    AttachedTo (fun _ => 0) (d + 2) (stripWordFold d width upper hd heven)
      (stripFold d width upper hd).pos :=
  faceLift_attached (d * width) heven (stripFold d width upper hd)
    (stripPos_plane d width upper) (d + 2)
    (fun k => (stripPos_front_bounds d width upper hlower hupper k).1)

theorem prefix_components_strip_disjoint (d A width : ℕ) (upper : ℤ)
    (hd : 2 ≤ d) (heven : d % 2 = 0) (hprod : 2 ∣ d * width)
    (hlower : 0 ≤ upper - width) (hupper : upper ≤ d)
    (initial : Fold cubicLattice (edgeWord (9 * d + 8)).length) (hlast)
    (hH : hydrophobicSites (edgeWord (9 * d + 8)) initial =
      Set.range (CubicPackingPrefix.skeletonPrefixFold d (by omega)).pos)
    (hP : ∀ i, (edgeWord (9 * d + 8)).get i = .P → initial.pos i ∉ cube (fun _ => 0) (d + 2)) :
    ∀ b ∈ CubicPackingPrefixComponents.initialBlock d initial hlast ::
      CubicPackingPrefixComponents.tailBlocks d A hd heven,
      ∀ i j, b.fold.pos i ≠ (stripWordFold d width upper (by omega) hprod).pos j := by
  apply CubicPackingPrefixWallsDisjoint.prefix_components_front_attached_disjoint d A hd heven
    initial hlast hH hP (stripWordFold d width upper (by omega) hprod)
    (stripFold d width upper (by omega)).pos
    (stripWordFold_attached d width upper (by omega) hprod hlower hupper)
  intro k
  exact (stripPos_front_bounds d width upper hlower hupper k).2

theorem prefixFold_strip_disjoint {q Q : ℕ} {hd : 2 ≤ depth q Q}
    {heven : depth q Q % 2 = 0} (w : CubicPackingPrefixFold.Witness q Q hd heven)
    (width : ℕ) (upper : ℤ) (hprod : 2 ∣ depth q Q * width)
    (hlower : 0 ≤ upper - width) (hupper : upper ≤ depth q Q) :
    ∀ i j, w.fold.pos i ≠ (stripWordFold (depth q Q) width upper (by omega) hprod).pos j := by
  apply w.disjoint_of_components
  exact prefix_components_strip_disjoint (depth q Q) (alpha Q) width upper hd heven hprod
    hlower hupper w.initial w.initial_last w.initial_H w.initial_P

end ProteinFolding.CubicPackingItems
