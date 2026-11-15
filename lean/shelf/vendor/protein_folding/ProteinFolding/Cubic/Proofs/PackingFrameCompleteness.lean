import ProteinFolding.Cubic.Proofs.PackingPrefixWallsAssembly
import ProteinFolding.Cubic.Proofs.PackingWallsItemsDisjoint

/-! Constructive completeness of the actual cubic packing frame. An exact
packing chooses disjoint strips in the original item order. The complete
prefix, wall and item folds have disjoint full images and meet at their
prescribed P endpoints. Equal hydrophobic volume then fills the entire cube. -/

namespace ProteinFolding.CubicPacking

open CubicCertificates CubicPackingLift CubicPackingRouting CubicPackingItems
open CubicPackingPrefixFold CubicPackingPrefixWallsAssembly CubicPackingFrameAssemblyHelpers
open CubicPackingWallsItemsDisjoint

/-- Every exact positive-even packing has a perfect fold of the complete
literal frame, including all exterior P residues and connectors. -/
theorem frameWord_complete (q Q : ℕ) (items : List ℕ)
    (hq : 2 ≤ q) (hQ : q < Q) (hpositive : ∀ a ∈ items, 0 < a)
    (heven : ∀ a ∈ items, Even a) (parts : List (List ℕ))
    (hexact : Packing.Exact ⟨items, 4 * Q, q⟩ parts) :
    PerfectHPStringFold (frameWord q Q items) (side q Q) := by
  classical
  have hq0 : 0 < q := by omega
  have hQ0 : 0 < Q := by omega
  have hdeven : depth q Q % 2 = 0 := Nat.mod_eq_zero_of_dvd (depth_even q Q)
  have hd2 : 2 ≤ depth q Q := depth_two_le q Q hq0
  have heven' : ∀ a ∈ items, a % 2 = 0 := by
    intro a ha
    obtain ⟨t, ht⟩ := heven a ha
    omega
  have hsum : items.sum = q * (4 * Q) := by
    simpa only [Nat.mul_comm] using exact_item_total q Q items parts hexact
  obtain ⟨hd, hlen, hnonempty⟩ := exact_item_parameters q Q items parts hexact hpositive hq hQ
  obtain ⟨L, hrows⟩ := exact_packing_layout_with_rows q Q items parts hexact hpositive heven'
  let prefixWitness := buildWithParity q Q hd2 hdeven
  obtain ⟨wall, heWall, hWallSites, hWallH⟩ :=
    CubicPackingWalls.walls_fold_exists q Q hq0 hQ0
  let Y := depth q Q - alpha Q
  have hYbound := initial_transfer_parameters q Q hq
  have hAle : alpha Q ≤ depth q Q := by
    dsimp [alpha, depth, beta]
    nlinarith
  have hY : (Y : ℤ) = (depth q Q : ℤ) - alpha Q := by
    dsimp [Y]
    exact Nat.cast_sub hAle
  let chain := L.buildChain q Q Y rfl hd hlen hnonempty hYbound.1 hYbound.2
  have hpi := prefixFold_itemChain_disjoint prefixWitness L chain (by rw [hY])
  have hpw := prefixFold_walls_disjoint prefixWitness hq0 hQ0 wall hWallSites
  have hwi := walls_itemChain_disjoint q Q Y items parts hexact L
    (fun y hy => (hrows y).mp hy) hd chain wall hq0 hQ0 hWallSites hY
  have hwall : 0 < (walls q Q).length := by
    rw [walls_length]
    have hb : 2 ≤ beta Q := by dsimp [beta]; omega
    omega
  apply frameWord_perfect_of_three_folds q Q items hq0 hsum prefixWitness.fold wall chain.fold
    hwall hpw hpi hwi
  · intro i j hi hj
    rw [prefixWitness.last i hi, heWall.1 j hj]
    change latticeDistance _ _ = 1
    rw [distance_eq]
    simp [point]
  · intro i j hi hj
    rw [heWall.2 i hi]
    simpa only [hY] using chain.first_seam j hj
  · exact prefixWitness.H_inside
  · intro i hi
    exact hWallH ⟨i, hi, rfl⟩
  · exact chain.H_inside

end ProteinFolding.CubicPacking
