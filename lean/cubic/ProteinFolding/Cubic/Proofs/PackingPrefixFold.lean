import ProteinFolding.Cubic.Proofs.PackingPrefixPairwise

/-! The complete literal prefix has an injective cubic-lattice fold. The
construction assembles all thirteen explicit components with their proved
collision matrix and seams. Every H remains in the target cube, and the
visited-site decomposition is retained for later prefix/wall separation. -/

namespace ProteinFolding.CubicPackingPrefixFold

open CubicPacking CubicPackingComponentChain CubicPackingPrefixComponents
open CubicPackingPrefixSeparation CubicPackingPrefixPairwise CubicPackingPrefix
open CubicPackingInitialDisjoint CubicPackingPrefixBridges CubicPackingBulk CubicPackingRouting

theorem pBlock_no_H {N : ℕ} (f : Fold cubicLattice N) (hN : 0<N) (p q : Site)
    (he : CubicPackingLift.HasEnds f p q) (r : Site) :
    r∉hydrophobicSites (pBlock f hN p q he).word (pBlock f hN p q he).fold := by
  change r∉hydrophobicSites (pWord N) (asPWord f)
  rw [asPWord_hydrophobicSites]
  exact Set.notMem_empty r

theorem blocks_H_inside (d alpha : ℕ) (hd : 2≤d) (heven : d%2=0)
    (f : Fold cubicLattice (edgeWord (9*d+8)).length) (hlast)
    (hH : hydrophobicSites (edgeWord (9*d+8)) f=Set.range (skeletonPrefixFold d (by omega)).pos) :
    ∀ b∈initialBlock d f hlast::tailBlocks d alpha hd heven,
      ∀ p∈hydrophobicSites b.word b.fold, p∈cube (fun _=>0) (d+2) := by
  intro b hb p hp
  simp only [tailBlocks,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · change p∈hydrophobicSites (edgeWord (9*d+8)) f at hp
    rw [hH] at hp
    obtain ⟨i,rfl⟩ := hp
    exact (skeletonPrefixFold_skeleton d (by omega) i).1
  · exact face_H_inside d .back p ((CubicPackingFrameFaces.faceFold_hydrophobicSites d (by omega) heven .back p).mp hp)
  · exact edge_H_inside d p ((CubicPackingBackEdge.edgeFold_hydrophobicSites d p).mp hp)
  · exact False.elim (pBlock_no_H _ _ _ _ _ p hp)
  · exact face_H_inside d .left p ((CubicPackingFrameFaces.faceFold_hydrophobicSites d (by omega) heven .left p).mp hp)
  · exact False.elim (pBlock_no_H _ _ _ _ _ p hp)
  · exact face_H_inside d .bottom p ((CubicPackingFrameFaces.faceFold_hydrophobicSites d (by omega) heven .bottom p).mp hp)
  · exact False.elim (pBlock_no_H _ _ _ _ _ p hp)
  · exact face_H_inside d .right p ((CubicPackingFrameFaces.faceFold_hydrophobicSites d (by omega) heven .right p).mp hp)
  · exact False.elim (pBlock_no_H _ _ _ _ _ p hp)
  · exact top_H_inside d p ((CubicPackingTopFace.topFold_hydrophobicSites d hd heven p).mp hp)
  · have hPH : Residue.P≠Residue.H := by decide
    have hf : hydrophobicSites (singleBlock d).word (singleBlock d).fold=∅ := by
      ext r
      simp [singleBlock,hydrophobicSites,List.get_eq_getElem,hPH]
    rw [hf] at hp
    exact False.elim hp
  · change p∈hydrophobicSites (bulkApproachWord d alpha) (bulkApproachWordFold d alpha (by omega) heven) at hp
    rw [bulkApproachWord_hydrophobicSites] at hp
    obtain ⟨i,hi⟩ := (bulkFold_sites d (by omega) heven p).mpr hp
    rw [←hi]
    exact bulkFold_in_cube d (by omega) heven i

theorem onWord_hsites {S T : Sequence} (f : Fold cubicLattice S.length) (h : T=S) :
    hydrophobicSites T (f.onLength (congrArg List.length h)) = hydrophobicSites S f := by
  subst T
  rfl

structure Witness (q Q : ℕ) (hd : 2≤depth q Q) (heven : depth q Q%2=0) where
  initial : Fold cubicLattice (edgeWord (9*depth q Q+8)).length
  initial_H : hydrophobicSites (edgeWord (9*depth q Q+8)) initial=
    Set.range (skeletonPrefixFold (depth q Q) (by omega)).pos
  initial_P : ∀ i, (edgeWord (9*depth q Q+8)).get i=.P →
    initial.pos i∉cube (fun _=>0) (depth q Q+2)
  initial_last : ∀ i, i.val+1=(edgeWord (9*depth q Q+8)).length →
    initial.pos i=point (depth q Q) 0 ((depth q Q : ℤ)+2)
  fold : Fold cubicLattice (prefixWord q Q).length
  last : ∀ i, i.val+1=(prefixWord q Q).length →
    fold.pos i=point ((depth q Q : ℤ)+1) ((depth q Q : ℤ)+1-alpha Q) (-2)
  H_inside : ∀ i, (prefixWord q Q).get i=.H → fold.pos i∈cube (fun _=>0) (depth q Q+2)
  sites : ∀ p, (∃ i, fold.pos i=p) ↔ (∃ i, initial.pos i=p) ∨
    ∃ b∈tailBlocks (depth q Q) (alpha Q) hd heven, ∃ i, b.fold.pos i=p
  hsites : ∀ p, p∈hydrophobicSites (prefixWord q Q) fold ↔
    p∈hydrophobicSites (edgeWord (9*depth q Q+8)) initial ∨
      ∃ b∈tailBlocks (depth q Q) (alpha Q) hd heven, p∈hydrophobicSites b.word b.fold

/-- A concrete fold of the exact existing prefix word, retaining its component
decomposition for later global disjointness proofs. -/
noncomputable def buildWithParity (q Q : ℕ) (hd : 2≤depth q Q) (heven : depth q Q%2=0) : Witness q Q hd heven := by
  classical
  let d := depth q Q
  let hLift := skeletonPrefix_edgeWord_back_lift_exists d (by omega)
  let f := Classical.choose hLift
  obtain ⟨hH,hP,hl⟩ := Classical.choose_spec hLift
  have hlast : ∀ i, i.val+1=(edgeWord (9*d+8)).length → f.pos i=point d 0 ((d : ℤ)+2) := by
    intro i hi
    have hi' : i=CubicPackingLift.edgeLastIndex (9*d+8) (by omega) := by
      apply Fin.ext
      simp only [CubicPackingLift.edgeLastIndex]
      omega
    rw [hi',hl]
    apply CubicCertificates.site_ext <;> simp [point]
  let a := initialBlock d f hlast
  let xs := tailBlocks d (alpha Q) hd heven
  have hD : (a::xs).Pairwise CubicPackingComponentChain.Disjoint := blocks_pairwise d (alpha Q) hd heven f hlast hH hP
  have hS : Seams (a::xs) := by
    change cubicLattice.Adj (point d 0 ((d : ℤ)+2)) (CubicPackingFrameFaces.firstP d .back) ∧ Seams xs
    refine ⟨?_,tailBlocks_seams d (alpha Q) hd heven⟩
    change latticeDistance _ _=1
    rw [CubicCertificates.distance_eq]
    dsimp only [point,CubicPackingFrameFaces.firstP,CubicPackingTopFace.point]
    omega
  let r := assemble a xs hD hS
  have hw : r.block.word=prefixWord q Q := r.word_eq.trans (blocks_word q Q hd heven f hlast)
  let ff : Fold cubicLattice (prefixWord q Q).length := r.block.fold.onLength (congrArg List.length hw.symm)
  have hv : ∀ p, (∃ i, ff.pos i=p) ↔ (∃ i, f.pos i=p) ∨ ∃ b∈xs, ∃ i, b.fold.pos i=p := by
    intro p
    change (∃ i, (r.block.fold.onLength _).pos i=p) ↔ _
    rw [onLength_sites,r.sites,members_cons]
    rfl
  have hh : ∀ p, p∈hydrophobicSites (prefixWord q Q) ff ↔
      p∈hydrophobicSites (edgeWord (9*d+8)) f ∨ ∃ b∈xs, p∈hydrophobicSites b.word b.fold := by
    intro p
    change p∈hydrophobicSites _ (r.block.fold.onLength _) ↔ _
    rw [onWord_hsites r.block.fold hw.symm,r.hsites,members_cons]
    rfl
  have hend : r.block.last=point ((d : ℤ)+1) ((d : ℤ)+1-alpha Q) (-2) := by
    rw [r.last_eq]
    simp [xs,tailBlocks,bulkBlock,List.getLastD]
  have he := onLength_hasEnds r.block.fold (congrArg List.length hw.symm) r.block.ends
  rw [hend] at he
  refine
    { initial := f
      initial_H := hH
      initial_P := hP
      initial_last := hlast
      fold := ff
      last := he.2
      H_inside := ?_
      sites := hv
      hsites := hh }
  intro i hi
  have hm : ff.pos i∈hydrophobicSites (prefixWord q Q) ff := ⟨i,hi,rfl⟩
  change ff.pos i∈hydrophobicSites _ (r.block.fold.onLength _) at hm
  rw [onWord_hsites r.block.fold hw.symm] at hm
  obtain ⟨b,hb,hp⟩ := (r.hsites (ff.pos i)).mp hm
  exact blocks_H_inside d (alpha Q) hd heven f hlast hH b hb (ff.pos i) hp

/-- Under the numerical frame parameters the entire prefix has an injective
fold whose H sites lie in the target cube and whose last P joins the wall. -/
theorem prefixFold_exists (q Q : ℕ) (hq : 2≤q) (_hQ : q<Q) :
    ∃ f : Fold cubicLattice (prefixWord q Q).length,
      (∀ i, (prefixWord q Q).get i=.H → f.pos i∈cube (fun _=>0) (side q Q)) ∧
      ∀ i, i.val+1=(prefixWord q Q).length →
        f.pos i=point ((depth q Q : ℤ)+1) ((depth q Q : ℤ)+1-alpha Q) (-2) := by
  have hd : 2≤depth q Q := by
    have hb : 2≤beta Q := by unfold beta;omega
    unfold depth
    nlinarith
  have heven : depth q Q%2=0 := Nat.mod_eq_zero_of_dvd (depth_even q Q)
  let w := buildWithParity q Q hd heven
  exact ⟨w.fold,w.H_inside,w.last⟩

end ProteinFolding.CubicPackingPrefixFold
