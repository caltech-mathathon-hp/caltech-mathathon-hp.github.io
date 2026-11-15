import ProteinFolding.Cubic.Proofs.PackingWallsFold
import ProteinFolding.Cubic.Proofs.PackingItemWallSeparation
import ProteinFolding.Cubic.Proofs.PackingFrameAssemblyHelpers

/-! Every wall residue is separated from every item residue. The proof uses
the actual complete wall-site classification and the item chain's exact
connector/strip decomposition, including all inserted P residues. -/

namespace ProteinFolding.CubicPackingWallsItemsDisjoint

open CubicCertificates CubicPacking CubicPackingLift CubicPackingRouting
open CubicPackingItems CubicPackingWalls CubicPackingFrameRoutingDisjoint
open CubicPackingFrameAssemblyHelpers

theorem wallUnit_routingConnector_disjoint {q Q Y : ℕ} {items : List ℕ}
    (hq : 0 < q) (hQ : 0 < Q) (L : Layout (depth q Q) items) (R : L.Routing Y)
    (a : Fin q) (b : Fin items.length) :
    ∀ i k, (wallFold q Q hq hQ a).pos i ≠ (R.connector b).pos k := by
  intro i k he
  have hi := wallFold_height q Q hq hQ a i
  have hk := R.connector_below b k
  have hz := congrFun he 2
  omega

theorem wallTop_le_depth (q Q : ℕ) (a : Fin q) :
    wallTop q Q a ≤ (depth q Q : ℤ) := by
  have hn : 0 ≤ (a.val : ℤ) * beta Q := by positivity
  dsimp only [wallTop]
  omega

theorem unitPBridge_routingConnector_disjoint {q Q Y : ℕ} {items : List ℕ}
    (L : Layout (depth q Q) items) (R : L.Routing Y)
    (hY : (Y : ℤ) = (depth q Q : ℤ) - alpha Q)
    (a : Fin q) (b : Fin items.length) :
    ∀ i k, (unitPBridge (depth q Q) (alpha Q) (wallTop q Q a)).pos i ≠
      (R.connector b).pos k := by
  unfold Layout.Routing.connector
  split_ifs with hb
  · exact unitPBridge_initialConnector_disjoint (depth q Q) (alpha Q) 5 R.initialRadius
      Y (L.startPort b) (depth q Q + 2) (wallTop q Q a) (wallTop_le_depth q Q a) hY
      (by decide) R.initialPositive (by have := L.startPort_bounds b; omega) (R.initialLength b hb)
  · exact unitPBridge_portConnector_disjoint (depth q Q) (alpha Q)
      (L.endPort (L.previous b (by omega))) (L.startPort b) (5 + b.val)
      (R.radius b (by omega)) (depth q Q + 2) (wallTop q Q a) (by omega)
      (R.radiusPositive b (by omega)) (L.endPort_ne_startPort _ _) (R.radiusLength b (by omega))

theorem gapRegion_routingConnector_disjoint {q Q Y : ℕ} {items : List ℕ}
    (hq : 0 < q) (L : Layout (depth q Q) items) (R : L.Routing Y)
    (hY : (Y : ℤ) = (depth q Q : ℤ) - alpha Q) (p : Site)
    (hp : GapRegion (depth q Q) (alpha Q) (alpha Q + 1) (q - 1) p)
    (b : Fin items.length) (k : Fin (4 * (depth q Q + 2))) : p ≠ (R.connector b).pos k := by
  have hlast : gapLast (alpha Q) (alpha Q + 1) (q - 1) = (Y : ℤ) :=
    (gap_last_literal q Q hq).trans hY.symm
  unfold Layout.Routing.connector
  split_ifs with hb
  · intro he
    have hj := initialConnector_region (depth q Q) 5 R.initialRadius Y (L.startPort b)
      (depth q Q + 2) (by decide) R.initialPositive (by have := L.startPort_bounds b; omega)
      (R.initialLength b hb) k
    have hzbelow := initialConnector_below_face_P (depth q Q) 5 R.initialRadius Y (L.startPort b)
      (depth q Q + 2) (by decide) R.initialPositive (by have := L.startPort_bounds b; omega)
      (R.initialLength b hb) k
    have hx := congrFun he 0
    have hy := congrFun he 1
    have hz := congrFun he 2
    dsimp only [GapRegion] at hp
    rcases hj with ⟨_, hjy⟩ | hjz | ⟨hjx, _⟩
    · have heq : p 1 = gapLast (alpha Q) (alpha Q + 1) (q - 1) := by omega
      have hs := hp.2.2.1 heq
      omega
    · omega
    · omega
  · intro he
    have hj := portConnector_pillar_or_depth (depth q Q)
      (L.endPort (L.previous b (by omega))) (L.startPort b) (5 + b.val)
      (R.radius b (by omega)) (depth q Q + 2) (by omega) (R.radiusPositive b (by omega))
      (L.endPort_ne_startPort _ _) (R.radiusLength b (by omega)) k
    have hx := congrFun he 0
    have hz := congrFun he 2
    dsimp only [GapRegion] at hp
    rcases hj with ⟨hjx, _⟩ | ⟨_, hjz⟩ <;> omega

theorem wallSites_routingConnector_disjoint {q Q Y : ℕ} {items : List ℕ}
    (hq : 0 < q) (hQ : 0 < Q) (L : Layout (depth q Q) items) (R : L.Routing Y)
    (hY : (Y : ℤ) = (depth q Q : ℤ) - alpha Q)
    (p : Site) (hp : WallSites q Q hq hQ p)
    (b : Fin items.length) (k : Fin (4 * (depth q Q + 2))) : p ≠ (R.connector b).pos k := by
  rcases hp with (⟨a, _, i, hi⟩ | ⟨a, _, i, hi⟩) | ⟨hg, _⟩
  · rw [← hi]
    exact wallUnit_routingConnector_disjoint hq hQ L R a b i k
  · rw [← hi]
    exact unitPBridge_routingConnector_disjoint L R hY a b i k
  · exact gapRegion_routingConnector_disjoint hq L R hY p hg b k

theorem wallSites_strip_disjoint (q Q : ℕ) (items : List ℕ) (parts : List (List ℕ))
    (hexact : Packing.Exact ⟨items, 4 * Q, q⟩ parts)
    (L : Layout (depth q Q) items)
    (hrows : ∀ y, (∃ i, (L.placement i).upper - (L.placement i).width < y ∧
      y ≤ (L.placement i).upper) → BinRows (beta Q) ((depth q Q : ℤ) - 1) parts y)
    (hd : 0 < depth q Q) (hq : 0 < q) (hQ : 0 < Q)
    (p : Site) (hp : WallSites q Q hq hQ p) (b : Fin items.length)
    (k : Fin (faceWord (depth q Q * (L.placement b).width)).length) :
    p ≠ (L.strip hd b).pos k := by
  rcases hp with (⟨a, _, i, hi⟩ | ⟨a, _, i, hi⟩) | ⟨hg, _⟩
  · rw [← hi]
    exact Ne.symm (layout_strip_wallUnit_disjoint q Q items parts hexact L hrows hd b
      (L.stripEven b) a (wallFold q Q hq hQ a) (wallFold_spec q Q hq hQ a).1 k i)
  · rw [← hi]
    exact Ne.symm (stripWordFold_outer_disjoint (depth q Q) (L.placement b).width
      (L.placement b).upper hd (L.stripEven b) _ (by
        have hx := (unitPBridge_shallow (depth q Q) (alpha Q) (wallTop q Q a) i).1
        omega) k)
  · exact Ne.symm (stripWordFold_outer_disjoint (depth q Q) (L.placement b).width
      (L.placement b).upper hd (L.stripEven b) p (by
        rcases hg.2.2.2.1 with hx | hx <;> omega) k)

/-- The final wall/item collision matrix, for the complete literal words.
The supplied wall fold may be any fold with the established WallSites data. -/
theorem walls_itemChain_disjoint (q Q Y : ℕ) (items : List ℕ) (parts : List (List ℕ))
    (hexact : Packing.Exact ⟨items, 4 * Q, q⟩ parts)
    (L : Layout (depth q Q) items)
    (hrows : ∀ y, (∃ i, (L.placement i).upper - (L.placement i).width < y ∧
      y ≤ (L.placement i).upper) → BinRows (beta Q) ((depth q Q : ℤ) - 1) parts y)
    (hd : 0 < depth q Q) (chain : L.ChainWitness q Q Y hd)
    (wall : Fold cubicLattice (walls q Q).length) (hq : 0 < q) (hQ : 0 < Q)
    (hWallSites : ∀ i, WallSites q Q hq hQ (wall.pos i))
    (hY : (Y : ℤ) = (depth q Q : ℤ) - alpha Q) :
    ∀ i j, wall.pos i ≠ chain.fold.pos j := by
  apply itemChain_disjoint_of_parts wall L chain
  · intro b i k
    exact wallSites_routingConnector_disjoint hq hQ L chain.routes hY _ (hWallSites i) b k
  · intro b i k
    exact wallSites_strip_disjoint q Q items parts hexact L hrows hd hq hQ _ (hWallSites i) b k

end ProteinFolding.CubicPackingWallsItemsDisjoint
