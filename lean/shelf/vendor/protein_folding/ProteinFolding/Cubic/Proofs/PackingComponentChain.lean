import ProteinFolding.Cubic.Proofs.PackingBlockAssembly
import ProteinFolding.Cubic.Proofs.PackingBulkWord

/-! A nonempty finite chain of literal word components. Pairwise separation
and adjacency of consecutive endpoints yield one fold of the exact flattened
word, with precise visited-site and H-support union formulas. -/

namespace ProteinFolding.CubicPackingComponentChain

open CubicPackingLift

structure Block where
  word : Sequence
  fold : Fold cubicLattice word.length
  first : Site
  last : Site
  positive : 0<word.length
  ends : HasEnds fold first last

def Disjoint (a b : Block) : Prop := ∀ i j, a.fold.pos i ≠ b.fold.pos j

def Seams : List Block → Prop
  | [] => True
  | [_] => True
  | a::b::xs => cubicLattice.Adj a.last b.first ∧ Seams (b::xs)

def Block.append (a b : Block) (hD : Disjoint a b) (hS : cubicLattice.Adj a.last b.first) : Block where
  word := a.word++b.word
  fold := Fold.appendWord a.fold b.fold hD (hasEnds_seam a.fold b.fold a.ends b.ends hS)
  first := a.first
  last := b.last
  positive := by simp only [List.length_append]; have := a.positive; omega
  ends := appendWord_hasEnds a.fold b.fold hD _ a.positive b.positive a.ends b.ends

theorem append_sites (a b : Block) (hD : Disjoint a b) (hS : cubicLattice.Adj a.last b.first) (p : Site) :
    (∃ i, (a.append b hD hS).fold.pos i=p) ↔
      (∃ i, a.fold.pos i=p) ∨ ∃ i, b.fold.pos i=p := by
  change (∃ i, ((Fold.append _ _ _ _).onLength _).pos i=p) ↔ _
  rw [CubicPackingBulk.onLength_sites, Fold.append_exists_pos]

theorem append_hsites (a b : Block) (hD : Disjoint a b) (hS : cubicLattice.Adj a.last b.first) :
    hydrophobicSites (a.append b hD hS).word (a.append b hD hS).fold =
      hydrophobicSites a.word a.fold ∪ hydrophobicSites b.word b.fold :=
  appendWord_hydrophobicSites _ _ _ _

theorem members_cons (a : Block) (xs : List Block) (P : Block → Prop) :
    (∃ c∈a::xs, P c) ↔ P a ∨ ∃ c∈xs, P c := by
  constructor
  · rintro ⟨c, hc, hp⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Or.inl hp
    · exact Or.inr ⟨c,hc,hp⟩
  · rintro (ha | ⟨c,hc,hp⟩)
    · exact ⟨a,by simp,ha⟩
    · exact ⟨c,by simp [hc],hp⟩

structure Result (a : Block) (xs : List Block) where
  block : Block
  word_eq : block.word = (a::xs).flatMap Block.word
  first_eq : block.first = a.first
  last_eq : block.last = (xs.getLastD a).last
  sites : ∀ p, (∃ i, block.fold.pos i=p) ↔ ∃ c∈a::xs, ∃ i, c.fold.pos i=p
  hsites : ∀ p, p∈hydrophobicSites block.word block.fold ↔
    ∃ c∈a::xs, p∈hydrophobicSites c.word c.fold

/-- Assemble a nonempty chain without weakening any word, collision, or seam
condition. The endpoint metadata is propagated by the generic append lemmas. -/
def assemble (a : Block) : (xs : List Block) → (a::xs).Pairwise Disjoint → Seams (a::xs) → Result a xs
  | [], _, _ =>
    { block := a
      word_eq := by simp
      first_eq := rfl
      last_eq := rfl
      sites := fun p => by simp
      hsites := fun p => by simp }
  | b::xs, hD, hS => by
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp hD
    let tail := assemble b xs ht hS.2
    have hsep : Disjoint a tail.block := by
      intro i j he
      have hp : ∃ k, tail.block.fold.pos k=a.fold.pos i := ⟨j,he.symm⟩
      obtain ⟨c,hc,k,hk⟩ := (tail.sites (a.fold.pos i)).mp hp
      exact ha c hc i k hk.symm
    have hjoin : cubicLattice.Adj a.last tail.block.first := by
      rw [tail.first_eq]
      exact hS.1
    let joined := a.append tail.block hsep hjoin
    refine
      { block := joined
        word_eq := ?_
        first_eq := rfl
        last_eq := ?_
        sites := ?_
        hsites := ?_ }
    · change a.word++tail.block.word=(a::b::xs).flatMap Block.word
      rw [tail.word_eq]
      rfl
    · change tail.block.last=((b::xs).getLastD a).last
      rw [List.getLastD_cons]
      exact tail.last_eq
    · intro p
      change (∃ i, (a.append tail.block hsep hjoin).fold.pos i=p) ↔ _
      rw [append_sites, tail.sites]
      simp only [members_cons]
    · intro p
      change p∈hydrophobicSites (a.append tail.block hsep hjoin).word (a.append tail.block hsep hjoin).fold ↔ _
      rw [append_hsites, Set.mem_union, tail.hsites]
      simp only [members_cons]

end ProteinFolding.CubicPackingComponentChain
