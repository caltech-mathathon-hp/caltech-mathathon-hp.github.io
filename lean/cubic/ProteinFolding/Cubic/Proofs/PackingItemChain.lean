import ProteinFolding.Cubic.Proofs.PackingItemPorts
import ProteinFolding.Cubic.Proofs.PackingItemConnectors
import ProteinFolding.Cubic.Proofs.PackingComponentChain
import Mathlib.Data.List.OfFn

/-! Assemble the item occurrences in their original order. Each full strip
is preceded by its literal exterior P connector. -/

namespace ProteinFolding.CubicPackingItems

open CubicCertificates CubicPacking CubicPackingLift CubicPackingRouting
open CubicPackingComponentChain

namespace Layout

variable {d : ℕ} {items : List ℕ} (L : Layout d items)

def previous (_L : Layout d items) (i : Fin items.length) (hi : 0 < i.val) : Fin items.length :=
  ⟨i.val - 1, by have := i.isLt; omega⟩

theorem previous_injective {i j : Fin items.length} (hi : 0 < i.val) (hj : 0 < j.val)
    (he : L.previous i hi = L.previous j hj) : i = j := by
  have he' := congrArg Fin.val he
  apply Fin.ext
  change i.val - 1 = j.val - 1 at he'
  omega

def stripEven (i : Fin items.length) : 2 ∣ d * (L.placement i).width := by
  exact Nat.dvd_mul_left_of_dvd (Nat.dvd_of_mod_eq_zero (L.width_even i)) d

def strip (hd : 0 < d) (i : Fin items.length) : Fold cubicLattice
    (faceWord (d * (L.placement i).width)).length :=
  stripWordFold d (L.placement i).width (L.placement i).upper hd (L.stripEven i)

theorem strip_first (hd : 0 < d) (i : Fin items.length) :
    ∀ k, k.val = 0 → (L.strip hd i).pos k = point d (L.startPort i) (-1) := by
  intro k hk
  have he : k = faceFirstIndex (d * (L.placement i).width) (L.stripEven i)
      (Nat.mul_pos hd (L.width_pos i)) := Fin.ext hk
  rw [he]
  change (stripWordFold _ _ _ _ _).pos _ = _
  rw [stripWordFold_first _ _ _ hd (L.width_pos i) (L.width_even i) (L.stripEven i)]
  rw [L.startPort_cast]
  apply site_ext <;> rfl

theorem strip_last (hd : 0 < d) (i : Fin items.length) :
    ∀ k, k.val + 1 = (faceWord (d * (L.placement i).width)).length →
      (L.strip hd i).pos k = point d (L.endPort i) (-1) := by
  intro k hk
  have he : k = faceLastIndex (d * (L.placement i).width) (L.stripEven i)
      (Nat.mul_pos hd (L.width_pos i)) := by
    apply Fin.ext
    simp only [faceLastIndex]
    omega
  rw [he]
  change (stripWordFold _ _ _ _ _).pos _ = _
  rw [stripWordFold_last _ _ _ hd (L.width_pos i) (L.stripEven i), L.endPort_cast]
  apply site_ext <;> rfl

def stripBlock (hd : 0 < d) (i : Fin items.length) : Block where
  word := faceWord (d * (L.placement i).width)
  fold := L.strip hd i
  first := point d (L.startPort i) (-1)
  last := point d (L.endPort i) (-1)
  positive := by rw [faceWord_length _ (L.stripEven i)]; have := L.width_pos i; positivity
  ends := ⟨L.strip_first hd i, L.strip_last hd i⟩

structure Routing (Y : ℕ) where
  initialRadius : ℕ
  initialPositive : 0 < initialRadius
  initialLength : ∀ i : Fin items.length, i.val = 0 →
    initialSteps 5 initialRadius Y (L.startPort i) = 4 * (d + 2) + 3
  radius : (i : Fin items.length) → 0 < i.val → ℕ
  radiusPositive : ∀ i hi, 0 < radius i hi
  radiusLength : ∀ i hi, routeSteps (5 + i.val) (radius i hi)
    (portWidth (L.endPort (L.previous i hi)) (L.startPort i)) = 4 * (d + 2) + 3

noncomputable def routing (Y : ℕ) (hd : 0 < d) (hlen : items.length ≤ d)
    (hne : 0 < items.length) (hY : Y ≤ d) (hYe : Y % 2 = 0) : L.Routing Y := by
  classical
  let first : Fin items.length := ⟨0, hne⟩
  let hInit := exists_initial_frame_radius d Y (L.startPort first) hd hY
    (L.startPort_bounds first).2 hYe (L.startPort_even first)
  let r := Classical.choose hInit
  have hr := (Classical.choose_spec hInit).1
  have hl := (Classical.choose_spec hInit).2
  have hOrd (i : Fin items.length) (hi : 0 < i.val) := exists_ordinary_frame_radius d items.length i.val
    (L.endPort (L.previous i hi)) (L.startPort i) hlen i.isLt
    (L.endPort_bounds _) (L.startPort_bounds _) (L.endPort_odd _) (L.startPort_even _)
  refine ⟨r, hr, ?_, (fun i hi => Classical.choose (hOrd i hi)),
    (fun i hi => (Classical.choose_spec (hOrd i hi)).1),
    (fun i hi => (Classical.choose_spec (hOrd i hi)).2)⟩
  intro i hi
  have he : i = first := Fin.ext hi
  simpa only [he] using hl

namespace Routing

variable {L} {Y : ℕ} (R : L.Routing Y)

def connector (i : Fin items.length) : Fold cubicLattice (4 * (d + 2)) :=
  if hi : i.val = 0 then
    initialConnector d 5 R.initialRadius Y (L.startPort i) (d + 2) (by decide)
      R.initialPositive (by have := L.startPort_bounds i; omega) (R.initialLength i hi)
  else portConnector d (L.endPort (L.previous i (by omega))) (L.startPort i)
    (5 + i.val) (R.radius i (by omega)) (d + 2) (by omega) (R.radiusPositive i (by omega))
    (L.endPort_ne_startPort _ _) (R.radiusLength i (by omega))

def incoming (_R : L.Routing Y) (i : Fin items.length) : Site :=
  if hi : i.val = 0 then point ((d : ℤ) + 1) Y (-1)
  else point d (L.endPort (L.previous i (by omega))) (-1)

theorem connector_below (i : Fin items.length) (k : Fin (4 * (d + 2))) :
    (R.connector i).pos k 2 ≤ -2 := by
  unfold connector
  split_ifs with hi
  · exact initialConnector_below_face_P ..
  · exact portConnector_below _ _ _ _ _ _ (by omega) _ _ _ _

theorem connector_left (i : Fin items.length) (k : Fin (4 * (d + 2))) (hk : k.val = 0) :
    cubicLattice.Adj (R.incoming i) ((R.connector i).pos k) := by
  unfold incoming connector
  split_ifs with hi
  · exact initialConnector_left_seam _ _ _ _ _ _ _ _ _ _ k hk
  · exact portConnector_left_seam _ _ _ _ _ _ _ _ _ _ k hk

theorem connector_right (i : Fin items.length) (k : Fin (4 * (d + 2)))
    (hk : k.val + 1 = 4 * (d + 2)) :
    cubicLattice.Adj ((R.connector i).pos k) (point d (L.startPort i) (-1)) := by
  unfold connector
  split_ifs with hi
  · exact initialConnector_right_seam _ _ _ _ _ _ _ _ _ _ k hk
  · exact portConnector_right_seam _ _ _ _ _ _ _ _ _ _ k hk

theorem connectors_disjoint (i j : Fin items.length) (hij : i ≠ j)
    (k l : Fin (4 * (d + 2))) : (R.connector i).pos k ≠ (R.connector j).pos l := by
  classical
  unfold connector
  split_ifs with hi hj hj
  · exact False.elim (hij (Fin.ext (hi.trans hj.symm)))
  · exact initial_portConnectors_disjoint d Y (L.startPort i)
      (L.endPort (L.previous j (by omega))) (L.startPort j) (5 + j.val)
      R.initialRadius (R.radius j (by omega)) (d + 2) (by omega) (by omega)
      R.initialPositive (R.radiusPositive j (by omega))
      (by have := L.startPort_bounds i; omega)
      (by have := L.endPort_bounds (L.previous j (by omega)); omega)
      (by have := L.startPort_bounds j; omega) (L.endPort_ne_startPort _ _)
      (Ne.symm (L.endPort_ne_startPort _ _)) (fun he => hij (L.startPort_injective he))
      (R.initialLength i hi) (R.radiusLength j (by omega)) k l
  · exact Ne.symm (initial_portConnectors_disjoint d Y (L.startPort j)
      (L.endPort (L.previous i (by omega))) (L.startPort i) (5 + i.val)
      R.initialRadius (R.radius i (by omega)) (d + 2) (by omega) (by omega)
      R.initialPositive (R.radiusPositive i (by omega))
      (by have := L.startPort_bounds j; omega)
      (by have := L.endPort_bounds (L.previous i (by omega)); omega)
      (by have := L.startPort_bounds i; omega) (L.endPort_ne_startPort _ _)
      (Ne.symm (L.endPort_ne_startPort _ _)) (fun he => hij (L.startPort_injective he).symm)
      (R.initialLength j hj) (R.radiusLength i (by omega)) l k)
  · exact portConnectors_disjoint d
      (L.endPort (L.previous i (by omega))) (L.startPort i)
      (L.endPort (L.previous j (by omega))) (L.startPort j)
      (5 + i.val) (5 + j.val) (R.radius i (by omega)) (R.radius j (by omega)) (d + 2)
      (by omega) (by omega) (R.radiusPositive i (by omega)) (R.radiusPositive j (by omega))
      (L.endPort_ne_startPort _ _) (L.endPort_ne_startPort _ _)
      (by intro he; apply hij; apply Fin.ext; omega)
      (fun he => hij (L.previous_injective (by omega) (by omega) (L.endPort_injective he)))
      (L.endPort_ne_startPort _ _) (Ne.symm (L.endPort_ne_startPort _ _))
      (fun he => hij (L.startPort_injective he))
      (R.radiusLength i (by omega)) (R.radiusLength j (by omega)) k l

def connectorWord (i : Fin items.length) : Fold cubicLattice
    (List.replicate (4 * (d + 2)) Residue.P).length :=
  (R.connector i).onLength (List.length_replicate ..)

def connectorBlock (i : Fin items.length) : Block where
  word := List.replicate (4 * (d + 2)) .P
  fold := R.connectorWord i
  first := (R.connector i).pos ⟨0, by omega⟩
  last := (R.connector i).pos ⟨4 * (d + 2) - 1, by omega⟩
  positive := by simp
  ends := by
    apply hasEnds_of_indices _ (by simp)
    · change (R.connector i).pos _ = _
      apply congrArg (R.connector i).pos
      apply Fin.ext
      simp only [Fin.coe_cast]
    · change (R.connector i).pos _ = _
      apply congrArg (R.connector i).pos
      apply Fin.ext
      simp only [Fin.coe_cast, List.length_replicate]

theorem connector_strip_disjoint (hd : 0 < d) (i j : Fin items.length) :
    Disjoint (R.connectorBlock i) (L.stripBlock hd j) := by
  intro k l he
  have hz := congrFun he 2
  have hc := R.connector_below i (Fin.cast (List.length_replicate ..) k)
  have hs := stripWordFold_location d (L.placement j).width (L.placement j).upper hd (L.stripEven j) l
  change (R.connector i).pos _ 2 = (L.strip hd j).pos l 2 at hz
  change _ ∧ _ ∧ _ ∧ _ ∧ ((L.strip hd j).pos l 2 = 0 ∨ (L.strip hd j).pos l 2 = -1) at hs
  rcases hs.2.2.2.2 with hs | hs <;> omega

def itemBlock (hd : 0 < d) (i : Fin items.length) : Block :=
  (R.connectorBlock i).append (L.stripBlock hd i) (R.connector_strip_disjoint hd i i) (by
    exact R.connector_right i _ (by change 4 * (d + 2) - 1 + 1 = 4 * (d + 2); omega))

theorem itemBlock_sites (hd : 0 < d) (i : Fin items.length) (p : Site) :
    (∃ k, (R.itemBlock hd i).fold.pos k = p) ↔
      (∃ k, (R.connector i).pos k = p) ∨ ∃ k, (L.strip hd i).pos k = p := by
  rw [itemBlock, append_sites]
  change (∃ k, ((R.connector i).onLength _).pos k = p) ∨ _ ↔ _
  rw [CubicPackingBulk.onLength_sites]
  rfl

theorem itemBlocks_disjoint (hd : 0 < d) (i j : Fin items.length) (hij : i ≠ j) :
    Disjoint (R.itemBlock hd i) (R.itemBlock hd j) := by
  intro k l he
  obtain (⟨a,ha⟩ | ⟨a,ha⟩) := (R.itemBlock_sites hd i _).mp ⟨k,rfl⟩
  all_goals obtain (⟨b,hb⟩ | ⟨b,hb⟩) := (R.itemBlock_sites hd j _).mp ⟨l,rfl⟩
  · exact R.connectors_disjoint i j hij a b (ha.trans (he.trans hb.symm))
  · exact R.connector_strip_disjoint hd i j (Fin.cast (List.length_replicate ..).symm a) b
      (ha.trans (he.trans hb.symm))
  · exact R.connector_strip_disjoint hd j i (Fin.cast (List.length_replicate ..).symm b) a
      (hb.trans (he.symm.trans ha.symm))
  · exact stripWordFolds_disjoint d _ _ _ _ hd (L.stripEven i) (L.stripEven j)
      (L.separate i j hij) a b (ha.trans (he.trans hb.symm))

theorem itemBlocks_seam (hd : 0 < d) (i j : Fin items.length) (hij : i.val + 1 = j.val) :
    cubicLattice.Adj (R.itemBlock hd i).last (R.itemBlock hd j).first := by
  change cubicLattice.Adj (point d (L.endPort i) (-1)) ((R.connector j).pos _)
  have hj : j.val ≠ 0 := by omega
  have hp : L.previous j (by omega) = i := by apply Fin.ext; change j.val - 1 = i.val; omega
  have he : R.incoming j = point d (L.endPort i) (-1) := by simp only [incoming, dif_neg hj, hp]
  rw [← he]
  exact R.connector_left j _ rfl

end Routing

theorem seams_ofFn {n : ℕ} (f : Fin n → Block)
    (hs : ∀ i j, i.val + 1 = j.val → cubicLattice.Adj (f i).last (f j).first) :
    Seams (List.ofFn f) := by
  induction n with
  | zero => simp [Seams]
  | succ n ih =>
    cases n with
    | zero => simp [List.ofFn_succ, Seams]
    | succ n =>
      rw [List.ofFn_succ, List.ofFn_succ]
      change cubicLattice.Adj (f 0).last (f (Fin.succ 0)).first ∧
        Seams (f (Fin.succ 0) :: List.ofFn (fun i => f i.succ.succ))
      refine ⟨hs _ _ rfl, ?_⟩
      have ht := ih (fun i => f i.succ) (fun i j hij => hs i.succ j.succ (by
        simpa only [Fin.val_succ] using congrArg Nat.succ hij))
      simpa only [List.ofFn_succ] using ht

theorem onWord_hsites {S T : Sequence} (f : Fold cubicLattice S.length) (h : T = S) :
    hydrophobicSites T (f.onLength (congrArg List.length h)) = hydrophobicSites S f := by
  subst T
  rfl

theorem onLength_hasEnds {N M : ℕ} (f : Fold cubicLattice N) (h : M = N)
    {p q : Site} (hf : HasEnds f p q) : HasEnds (f.onLength h) p q := by
  constructor
  · intro i hi
    exact hf.1 (Fin.cast h i) hi
  · intro i hi
    exact hf.2 (Fin.cast h i) (by simpa only [Fin.coe_cast, ← h] using hi)

theorem connector_no_H {Y : ℕ} (R : L.Routing Y) (i : Fin items.length) (p : Site) :
    p ∉ hydrophobicSites (R.connectorBlock i).word (R.connectorBlock i).fold := by
  rintro ⟨k,hk,_⟩
  have he : (R.connectorBlock i).word.get k = .P := by simp [Routing.connectorBlock]
  rw [he] at hk
  cases hk

theorem itemBlock_hsites {Y : ℕ} (R : L.Routing Y) (hd : 0 < d)
    (i : Fin items.length) (p : Site) :
    p ∈ hydrophobicSites (R.itemBlock hd i).word (R.itemBlock hd i).fold ↔
      p ∈ hydrophobicSites (faceWord (d * (L.placement i).width)) (L.strip hd i) := by
  rw [Routing.itemBlock, append_hsites, Set.mem_union]
  exact or_iff_right (L.connector_no_H R i p)

/-- The positive-depth parameter is retained explicitly, keeping all strip
components definitionally identical in the visited-site formula. -/
structure ChainWitness (q Q Y : ℕ) (hd : 0 < d) where
  routes : L.Routing Y
  fold : Fold cubicLattice (itemWords q Q items).length
  first_seam : ∀ i, i.val = 0 →
    cubicLattice.Adj (point ((d : ℤ) + 1) Y (-1)) (fold.pos i)
  H_inside : ∀ i, (itemWords q Q items).get i = .H →
    fold.pos i ∈ cube (fun _ => 0) (d + 2)
  sites : ∀ p, (∃ i, fold.pos i = p) ↔
    ∃ j : Fin items.length,
      (∃ k, (routes.connector j).pos k = p) ∨ ∃ k, (L.strip hd j).pos k = p
  hsites : ∀ p, p ∈ hydrophobicSites (itemWords q Q items) fold ↔
    ∃ j : Fin items.length,
      p ∈ hydrophobicSites (faceWord (d * (L.placement j).width)) (L.strip hd j)

set_option maxHeartbeats 2000000 in
noncomputable def buildChainWithRouting (q Q Y : ℕ) (hdepth : d = depth q Q) (hd : 0 < d)
    (hne : 0 < items.length) (R : L.Routing Y) :
    L.ChainWitness q Q Y hd := by
  classical
  let bs := List.ofFn (R.itemBlock hd)
  have hnon : bs ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [bs, List.length_ofFn, List.length_nil] at hh
    omega
  let a := bs.head hnon
  let xs := bs.tail
  have hbs : a :: xs = bs := List.cons_head_tail hnon
  have ha : a = R.itemBlock hd ⟨0,hne⟩ := List.head_ofFn hnon
  have hp : (a :: xs).Pairwise Disjoint := by
    rw [hbs]
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact R.itemBlocks_disjoint hd i j (by intro he; subst j; exact (lt_irrefl _) hij)
  have hs : Seams (a :: xs) := by
    rw [hbs]
    exact seams_ofFn _ (R.itemBlocks_seam hd)
  let r := assemble a xs hp hs
  have hw : r.block.word = itemWords q Q items := by
    rw [r.word_eq, hbs]
    have hm : bs.map Block.word = items.map (fun w => List.replicate (4 * (d + 2)) .P ++ faceWord (d * w)) := by
      rw [List.map_ofFn]
      change List.ofFn (fun i => List.replicate (4 * (d + 2)) .P ++ faceWord (d * (L.placement i).width)) = _
      simp_rw [L.width_eq]
      simpa only [List.get_eq_getElem] using List.ofFn_getElem_eq_map items
        (fun w => List.replicate (4 * (d + 2)) .P ++ faceWord (d * w))
    change (bs.map Block.word).flatten = _
    simpa only [List.flatMap, itemWords, side, ← hdepth] using congrArg List.flatten hm
  let ff := r.block.fold.onLength (congrArg List.length hw.symm)
  have hv (p : Site) : (∃ i, ff.pos i = p) ↔ ∃ j : Fin items.length,
      (∃ k, (R.connector j).pos k = p) ∨ ∃ k, (L.strip hd j).pos k = p := by
    change (∃ i, (r.block.fold.onLength _).pos i = p) ↔ _
    rw [CubicPackingBulk.onLength_sites, r.sites, hbs]
    simp only [bs, List.mem_ofFn]
    constructor
    · rintro ⟨b, ⟨j,rfl⟩,h⟩
      exact ⟨j,(R.itemBlock_sites hd j p).mp h⟩
    · rintro ⟨j,h⟩
      exact ⟨R.itemBlock hd j,⟨j,rfl⟩,(R.itemBlock_sites hd j p).mpr h⟩
  have hh (p : Site) : p ∈ hydrophobicSites (itemWords q Q items) ff ↔
      ∃ j : Fin items.length, p ∈ hydrophobicSites (faceWord (d * (L.placement j).width)) (L.strip hd j) := by
    change p ∈ hydrophobicSites _ (r.block.fold.onLength _) ↔ _
    rw [onWord_hsites _ hw.symm, r.hsites, hbs]
    simp only [bs,List.mem_ofFn]
    constructor
    · rintro ⟨b,⟨j,rfl⟩,h⟩
      exact ⟨j,(L.itemBlock_hsites R hd j p).mp h⟩
    · rintro ⟨j,h⟩
      exact ⟨R.itemBlock hd j,⟨j,rfl⟩,(L.itemBlock_hsites R hd j p).mpr h⟩
  refine { routes := R, fold := ff, sites := hv, hsites := hh, first_seam := ?_, H_inside := ?_ }
  · intro i hi
    have he := onLength_hasEnds r.block.fold (congrArg List.length hw.symm) r.block.ends
    rw [he.1 i hi, r.first_eq, ha]
    simpa only [Routing.itemBlock, Block.append, Routing.connectorBlock, Routing.incoming,
      dif_pos rfl] using R.connector_left ⟨0,hne⟩ ⟨0,by omega⟩ rfl
  · intro i hi
    obtain ⟨j,hj⟩ := (hh (ff.pos i)).mp ⟨i,hi,rfl⟩
    exact stripWordFold_H_in_cube d _ _ hd (L.stripEven j) (by have := L.bounds j; omega)
      (by have := L.bounds j; omega) (ff.pos i) hj

noncomputable def buildChain (q Q Y : ℕ) (hdepth : d = depth q Q) (hd : 0 < d)
    (hlen : items.length ≤ d) (hne : 0 < items.length) (hY : Y ≤ d) (hYe : Y % 2 = 0) :
    L.ChainWitness q Q Y hd :=
  L.buildChainWithRouting q Q Y hdepth hd hne (L.routing Y hd hlen hne hY hYe)
end Layout

theorem exact_item_total (q Q : ℕ) (items : List ℕ) (parts : List (List ℕ))
    (hexact : Packing.Exact ⟨items, 4 * Q, q⟩ parts) : items.sum = 4 * Q * q := by
  have hh : ∀ ps : List (List ℕ), (∀ p ∈ ps, p.sum = 4 * Q) →
      ps.flatten.sum = 4 * Q * ps.length := by
    intro ps
    induction ps with
    | nil => simp
    | cons p ps ih =>
      intro hs
      have hp := hs p (by simp)
      have ht := ih (fun p hp => hs p (by simp [hp]))
      simp only [List.flatten_cons, List.sum_append, List.length_cons]
      rw [hp,ht]
      ring
  exact hexact.2.1.sum_eq.trans (by simpa only [hexact.1] using hh parts hexact.2.2)

theorem exact_item_parameters (q Q : ℕ) (items : List ℕ) (parts : List (List ℕ))
    (hexact : Packing.Exact ⟨items, 4 * Q, q⟩ parts)
    (hpositive : ∀ a ∈ items, 0 < a) (hq : 2 ≤ q) (hQ : q < Q) :
    0 < depth q Q ∧ items.length ≤ depth q Q ∧ 0 < items.length := by
  have ht := exact_item_total q Q items parts hexact
  have hl := List.length_le_sum_of_one_le items (fun a ha => hpositive a ha)
  have hsum : 0 < items.sum := by nlinarith
  have hn : 0 < items.length := by
    by_contra he
    have hz : items = [] := List.length_eq_zero_iff.mp (by omega)
    simp only [hz, List.sum_nil] at hsum
    omega
  dsimp [depth,beta]
  constructor
  · positivity
  constructor
  · nlinarith
  · exact hn

theorem initial_transfer_parameters (q Q : ℕ) (hq : 2 ≤ q) :
    depth q Q - alpha Q ≤ depth q Q ∧ (depth q Q - alpha Q) % 2 = 0 := by
  have he := Nat.mod_eq_zero_of_dvd (depth_even q Q)
  have ha : alpha Q % 2 = 0 := by dsimp [alpha]; omega
  have hle : alpha Q ≤ depth q Q := by
    dsimp [alpha,depth,beta]
    nlinarith
  omega

end ProteinFolding.CubicPackingItems
