import ProteinFolding.Cubic.Proofs.PackingComponentChain
import ProteinFolding.Cubic.Proofs.PackingPrefixBridges
import ProteinFolding.Cubic.Proofs.PackingBackEdge
import ProteinFolding.Cubic.Proofs.PackingSkeletonPrefix

/-! Endpoint-labelled literal components of the complete prefix. This file
packages the already proved geometric folds; global separation and assembly
are handled separately. -/

namespace ProteinFolding.CubicPackingPrefixComponents

open CubicPacking CubicPackingLift CubicPackingComponentChain CubicPackingRouting
open CubicPackingPrefixBridges CubicPackingBulk

theorem onLength_hasEnds {N M : ℕ} (f : Fold cubicLattice N) (h : M=N)
    {p q : Site} (he : HasEnds f p q) : HasEnds (f.onLength h) p q := by
  subst M
  exact he

def pBlock {N : ℕ} (f : Fold cubicLattice N) (hN : 0<N) (p q : Site) (he : HasEnds f p q) : Block where
  word := pWord N
  fold := asPWord f
  first := p
  last := q
  positive := by simpa only [pWord, List.length_replicate] using hN
  ends := onLength_hasEnds f _ he

def faceBlock (d : ℕ) (hd : 0<d) (heven : d%2=0) (f : CubicPackingFrameFaces.Face) : Block where
  word := faceWord (d*d)
  fold := CubicPackingFrameFaces.faceFold d hd heven f
  first := CubicPackingFrameFaces.firstP d f
  last := CubicPackingFrameFaces.lastP d f
  positive := by
    rw [faceWord_length _ (CubicPackingFrameFaces.faceLength_even d heven)]
    have hp := Nat.mul_pos hd hd
    omega
  ends := ⟨CubicPackingFrameFaces.faceFold_first_of_val d hd heven f,
    CubicPackingFrameFaces.faceFold_last_of_end d hd heven f⟩

def edgeBlock (d : ℕ) (hd : 0<d) (heven : d%2=0) : Block where
  word := edgeWord d
  fold := CubicPackingBackEdge.edgeFold d
  first := point 0 1 ((d : ℤ)+2)
  last := point 0 d ((d : ℤ)+2)
  positive := by rw [edgeWord_length]; omega
  ends := ⟨CubicPackingBackEdge.edgeFold_first_of_val d hd,
    CubicPackingBackEdge.edgeFold_last_of_end d hd heven⟩

def fourBlock (d : ℕ) : Block := pBlock (fourFold d) (by omega)
  (point (-1) d ((d : ℤ)+2)) (point (-2) d d) ⟨fourPos_first d,fourPos_last d⟩

def leftLinkBlock (d : ℕ) (heven : d%2=0) : Block := pBlock (leftLinkFold d) (by omega)
  (point (-2) 1 d) (point 1 (-2) d) ⟨leftLinkPos_first d,leftLinkPos_last d heven⟩

def rightLinkBlock (d : ℕ) (heven : d%2=0) : Block := pBlock (rightLinkFold d) (by omega)
  (point d (-2) d) (point ((d : ℤ)+3) 1 d) ⟨rightLinkFold_first d,rightLinkFold_last d heven⟩

def topLinkBlock (d : ℕ) (hd : 2≤d) : Block := pBlock (topLinkFold d hd) (by omega)
  (point ((d : ℤ)+3) d d) (point ((d : ℤ)-1) ((d : ℤ)+3) 1) ⟨topLinkPos_first d,topLinkPos_last d hd⟩

def topBlock (d : ℕ) (hd : 2≤d) (heven : d%2=0) : Block where
  word := faceWord (d*d-2)
  fold := CubicPackingTopFace.topFold d hd heven
  first := point ((d : ℤ)-1) ((d : ℤ)+2) 1
  last := point ((d : ℤ)-1) ((d : ℤ)+2) d
  positive := by
    rw [faceWord_length _ (CubicPackingTopFace.topLength_even d heven)]
    have hp := CubicPackingTopFace.topLength_pos d hd
    omega
  ends := ⟨CubicPackingTopFace.topFold_first_of_val d hd heven,
    CubicPackingTopFace.topFold_last_of_end d hd heven⟩

def singleBlock (d : ℕ) : Block where
  word := [.P]
  fold := singleFold (point d ((d : ℤ)+2) d)
  first := point d ((d : ℤ)+2) d
  last := point d ((d : ℤ)+2) d
  positive := by decide
  ends := ⟨fun _ _=>rfl,fun _ _=>rfl⟩

def bulkBlock (d alpha : ℕ) (hd : 0<d) (heven : d%2=0) : Block where
  word := bulkApproachWord d alpha
  fold := bulkApproachWordFold d alpha hd heven
  first := upperHole d
  last := point ((d : ℤ)+1) ((d : ℤ)+1-alpha) (-2)
  positive := by simp only [bulkApproachWord, bulkWord, approachWord, List.length_append, List.length_replicate]; omega
  ends := ⟨bulkApproachWordFold_first d alpha hd heven,bulkApproachWordFold_last d alpha hd heven⟩

def initialBlock (d : ℕ) (f : Fold cubicLattice (edgeWord (9*d+8)).length)
    (hlast : ∀ i, i.val+1=(edgeWord (9*d+8)).length → f.pos i=point d 0 ((d : ℤ)+2)) : Block where
  word := edgeWord (9*d+8)
  fold := f
  first := f.pos ⟨0,by rw [edgeWord_length];omega⟩
  last := point d 0 ((d : ℤ)+2)
  positive := by rw [edgeWord_length];omega
  ends := ⟨fun i hi=>by congr 1;exact Fin.ext hi,hlast⟩

def tailBlocks (d alpha : ℕ) (hd : 2≤d) (heven : d%2=0) : List Block :=
  [faceBlock d (by omega) heven .back, edgeBlock d (by omega) heven,
   fourBlock d, faceBlock d (by omega) heven .left, leftLinkBlock d heven,
   faceBlock d (by omega) heven .bottom, rightLinkBlock d heven,
   faceBlock d (by omega) heven .right, topLinkBlock d hd,
   topBlock d hd heven, singleBlock d, bulkBlock d alpha (by omega) heven]

theorem tailBlocks_seams (d alpha : ℕ) (hd : 2≤d) (heven : d%2=0) : Seams (tailBlocks d alpha hd heven) := by
  simp only [tailBlocks, Seams, faceBlock, edgeBlock, fourBlock, leftLinkBlock,
    rightLinkBlock, topLinkBlock, topBlock, singleBlock, bulkBlock, pBlock,
    CubicPackingFrameFaces.firstP, CubicPackingFrameFaces.lastP, upperHole]
  repeat' constructor
  all_goals change latticeDistance _ _=1
  all_goals rw [CubicCertificates.distance_eq]; dsimp only [point, CubicPackingTopFace.point]; omega

theorem blocks_word (q Q : ℕ) (hd : 2≤depth q Q) (heven : depth q Q%2=0)
    (f : Fold cubicLattice (edgeWord (9*depth q Q+8)).length) (hlast) :
    ((initialBlock (depth q Q) f hlast)::tailBlocks (depth q Q) (alpha Q) hd heven).flatMap Block.word = prefixWord q Q := by
  simp [initialBlock, tailBlocks, faceBlock, edgeBlock, fourBlock, leftLinkBlock,
    rightLinkBlock, topLinkBlock, topBlock, singleBlock, bulkBlock, pBlock,
    pWord, bulkApproachWord, bulkWord, approachWord, prefixWord, repeatWord,
    pow_two, List.append_assoc]

end ProteinFolding.CubicPackingPrefixComponents
