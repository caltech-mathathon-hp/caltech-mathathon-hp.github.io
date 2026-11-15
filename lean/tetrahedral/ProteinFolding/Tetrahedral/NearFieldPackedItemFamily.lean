import ProteinFolding.Tetrahedral.NearFieldItemFamily
import ProteinFolding.Tetrahedral.NearFieldReorderPieces
import Mathlib.Data.List.FinRange

/-! The packing witness determines actual, pairwise disjoint item pieces.
Their occurrence order is then restored to the literal input word. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

structure PackedBins (p : ConstructionParameters) (items : List ℕ) where
  parts : List (List ℕ)
  length_eq : parts.length = p.bins
  perm : items.Perm parts.flatten
  loads : ∀ part ∈ parts, part.sum = p.capacity
  positive : ∀ s ∈ items, 0 < s

theorem PackedBins.part_positive {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) (k : Fin d.parts.length) : ∀ s ∈ d.parts.get k, 0 < s := by
  intro s hs
  apply d.positive s
  apply d.perm.mem_iff.mpr
  exact List.mem_flatten.mpr ⟨d.parts.get k, List.get_mem _ _, hs⟩

theorem PackedBins.part_load {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) (k : Fin d.parts.length) : (d.parts.get k).sum = p.capacity :=
  d.loads _ (List.get_mem _ _)

theorem PackedBins.bin_lt {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) (k : Fin d.parts.length) : k.val < p.bins := by
  rw [← d.length_eq]
  exact k.isLt

def PackedBins.binPieces {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) (k : Fin d.parts.length) : List PositionedWord :=
  List.ofFn (packedItemPiece p k.val (d.bin_lt k) (d.parts.get k) (d.part_positive k) (d.part_load k))

theorem PackedBins.binPieces_words {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) (k : Fin d.parts.length) :
    (d.binPieces k).map PositionedWord.word = (d.parts.get k).map (fun s => capWord (dimerChain (p.itemDimers s))) := by
  have he := congrArg (List.map (fun s => capWord (dimerChain (p.itemDimers s))))
    (List.ofFn_get (d.parts.get k))
  rw [List.map_ofFn] at he
  rw [binPieces, List.map_ofFn]
  change List.ofFn (fun i : Fin (d.parts.get k).length =>
    capWord (dimerChain (p.itemDimers ((d.parts.get k).get i)))) = _
  simpa only [Function.comp_def] using he

def PackedBins.placedPieces {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) : List PositionedWord :=
  (List.finRange d.parts.length).flatMap d.binPieces

theorem PackedBins.placedPieces_words {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) :
    d.placedPieces.map PositionedWord.word =
      d.parts.flatten.map (fun s => capWord (dimerChain (p.itemDimers s))) := by
  simp only [placedPieces, List.map_flatMap, binPieces_words]
  have he := congrArg
    (fun parts : List (List ℕ) => parts.flatMap (fun part => part.map (fun s => capWord (dimerChain (p.itemDimers s)))))
    (List.finRange_map_get d.parts)
  dsimp only at he
  rw [List.flatMap_map] at he
  simpa only [List.flatMap_def, List.map_flatten] using he

theorem PackedBins.placedPieces_pairwise {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) : d.placedPieces.Pairwise WordsDisjoint := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro k _
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact packedItemPieces_disjoint_same_bin p k.val (d.bin_lt k) (d.parts.get k)
      (d.part_positive k) (d.part_load k) i j (ne_of_lt hij)
  · apply (List.pairwise_lt_finRange d.parts.length).imp
    intro k l hkl x hx y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    exact packedItemPieces_disjoint_bins p k.val l.val (d.bin_lt k) (d.bin_lt l) hkl
      (d.parts.get k) (d.parts.get l) (d.part_positive k) (d.part_positive l)
      (d.part_load k) (d.part_load l) i j

theorem PackedBins.placedPiece_hSupport {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) (q : PositionedWord) (hq : q ∈ d.placedPieces) :
    hSupport q.word q.fold ⊆ octahedron p.side := by
  obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp hq
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
  exact canonicalItemPiece_hSupport p k.val (itemPrefix (d.parts.get k) i) ((d.parts.get k).get i)
    (d.bin_lt k) (d.part_positive k _ (List.get_mem _ _))
    (by rw [← d.part_load k]; exact itemPrefix_load (d.parts.get k) i)

noncomputable def PackedBins.reordered {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) : ReorderedPieces d.placedPieces
      (items.map (fun s => capWord (dimerChain (p.itemDimers s)))) :=
  reorderPieces d.placedPieces _ (by rw [d.placedPieces_words]; exact d.perm.map _)

noncomputable def PackedBins.itemPieces {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) : List PositionedWord := d.reordered.pieces

theorem PackedBins.itemPieces_words {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) :
    d.itemPieces.map PositionedWord.word = items.map (fun s => capWord (dimerChain (p.itemDimers s))) :=
  d.reordered.words_eq

theorem PackedBins.itemPieces_pairwise {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) : d.itemPieces.Pairwise WordsDisjoint :=
  d.reordered.pairwise d.placedPieces_pairwise

theorem PackedBins.itemPiece_hSupport {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) (q : PositionedWord) (hq : q ∈ d.itemPieces) :
    hSupport q.word q.fold ⊆ octahedron p.side := by
  exact d.placedPiece_hSupport q (d.reordered.perm.subset hq)

end ProteinFolding.Tetrahedral.NearField
