import ProteinFolding.Cubic.Proofs.PackingFrameRoutingDisjoint
import ProteinFolding.Cubic.Proofs.PackingWallsFold
import ProteinFolding.Cubic.Proofs.PackingWallGapDisjoint

/-! Full-site separation of the completed prefix and literal wall chain. -/

namespace ProteinFolding.CubicPackingPrefixWallsAssembly

open CubicPacking CubicCertificates CubicPackingLift CubicPackingRouting
open CubicPackingWalls CubicPackingPrefixWallsDisjoint CubicPackingFrameRoutingDisjoint

theorem prefixFold_wallUnit_disjoint {q Q : ℕ} {hd : 2 ≤ depth q Q}
    {heven : depth q Q % 2 = 0} (w : CubicPackingPrefixFold.Witness q Q hd heven)
    (hq : 0 < q) (hQ : 0 < Q) (j : Fin q) :
    ∀ i k, w.fold.pos i ≠ (wallFold q Q hq hQ j).pos k :=
  witness_front_attached_disjoint w _ _ (wallFold_spec q Q hq hQ j).1
    (wallUnitOwners_front q Q j)

theorem prefixFold_unitBridge_disjoint {q Q : ℕ} {hd : 2 ≤ depth q Q}
    {heven : depth q Q % 2 = 0} (w : CubicPackingPrefixFold.Witness q Q hd heven)
    (j : Fin q) : ∀ i k, w.fold.pos i ≠
      (unitPBridge (depth q Q) (alpha Q) (wallTop q Q j)).pos k :=
  witness_deep_front_disjoint w _
    (fun k => (unitPBridge_wallTop_deep q Q j k).1)
    (fun k => (unitPBridge_wallTop_deep q Q j k).2)

theorem prefixFold_gapEdge_disjoint {q Q : ℕ} {hd : 2 ≤ depth q Q}
    {heven : depth q Q % 2 = 0} (w : CubicPackingPrefixFold.Witness q Q hd heven)
    (j : Fin q) : ∀ i k, w.fold.pos i ≠
      (gapEdgeFold (depth q Q) (alpha Q + 1 + (j.val : ℤ) * beta Q)).pos k := by
  have hy := gapRow_bounds q Q j
  apply witness_front_attached_disjoint w _ _ (gapEdgeFold_attached _ _ hy)
  intro e
  have he := e.isLt
  dsimp only [gapOwners, point]
  exact ⟨rfl, by omega, by omega⟩

theorem prefixFold_gapBridge_disjoint {q Q : ℕ} {hd : 2 ≤ depth q Q}
    {heven : depth q Q % 2 = 0} (w : CubicPackingPrefixFold.Witness q Q hd heven)
    (k : ℕ) (hk : k + 1 < q) : ∀ i l, w.fold.pos i ≠
      (gapPBridge (depth q Q) (alpha Q) (gapLast (alpha Q) (alpha Q + 1) k)).pos l := by
  have hy := gap_bridge_row_strict q Q k hk
  apply witness_deep_front_disjoint w _
  · exact fun l => (gapPBridge_deep_bounds _ _ _ (by omega) l).1
  · exact fun l => (gapPBridge_deep_bounds _ _ _ (by omega) l).2

theorem prefixFold_walls_disjoint {q Q : ℕ} {hd : 2 ≤ depth q Q}
    {heven : depth q Q % 2 = 0} (w : CubicPackingPrefixFold.Witness q Q hd heven)
    (hq : 0 < q) (hQ : 0 < Q) (wall : Fold cubicLattice (walls q Q).length)
    (hpos : ∀ i, WallSites q Q hq hQ (wall.pos i)) :
    ∀ i j, w.fold.pos i ≠ wall.pos j := by
  intro i j he
  rcases hpos j with hu | hg
  · rcases hu with ⟨a, _, k, hk⟩ | ⟨a, _, k, hk⟩
    · exact prefixFold_wallUnit_disjoint w hq hQ a i k (he.trans hk.symm)
    · exact prefixFold_unitBridge_disjoint w a i k (he.trans hk.symm)
  · rcases hg.2 with ⟨a, ha, k, hk⟩ | ⟨a, ha, k, hk⟩
    · let af : Fin q := ⟨a, by omega⟩
      have hb : (beta Q : ℤ) = 2 * (alpha Q : ℤ) + 2 := by dsimp [beta, alpha]; omega
      have hsite : (gapEdgeFold (depth q Q) (alpha Q + 1 + (af.val : ℤ) * beta Q)).pos k = wall.pos j := by
        dsimp only [gapEdgeFold, af]
        rw [hb]
        exact hk
      exact prefixFold_gapEdge_disjoint w af i k (he.trans hsite.symm)
    · exact prefixFold_gapBridge_disjoint w a (by omega) i k (he.trans hk.symm)

end ProteinFolding.CubicPackingPrefixWallsAssembly
