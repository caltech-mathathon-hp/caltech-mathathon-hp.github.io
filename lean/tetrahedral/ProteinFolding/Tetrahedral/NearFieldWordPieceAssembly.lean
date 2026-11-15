import ProteinFolding.Tetrahedral.NearFieldWordFoldAppend

/-! Concatenating a finite ordered family of actual nonempty word folds. -/

namespace ProteinFolding.Tetrahedral.NearField

def castWordFold {S T : Sequence} (f : Fold tetrahedralLattice S.length) (h : T = S) :
    Fold tetrahedralLattice T.length := f.onLength (congrArg List.length h)

theorem castWordFold_hSupport {S T : Sequence} (f : Fold tetrahedralLattice S.length) (h : T = S) :
    hSupport T (castWordFold f h) = hSupport S f := by cases h; rfl

theorem castWordFold_sites {S T : Sequence} (f : Fold tetrahedralLattice S.length) (h : T = S) :
    foldSites (castWordFold f h) = foldSites f := by cases h; rfl

structure PositionedWord where
  word : Sequence
  fold : Fold tetrahedralLattice word.length
  length_pos : 0 < word.length
  first : Site
  last : Site
  first_eq : ∀ i, i.val = 0 → fold.pos i = first
  last_eq : ∀ i, i.val + 1 = word.length → fold.pos i = last

def PositionedWord.append (a b : PositionedWord) (hdis : Disjoint (foldSites a.fold) (foldSites b.fold))
    (hseam : tetrahedralLattice.Adj a.last b.first) : PositionedWord where
  word := a.word ++ b.word
  fold := Fold.appendWord a.fold b.fold ((foldSites_disjoint_iff _ _).mp hdis)
    (fun i j hi hj => by rw [a.last_eq i hi, b.first_eq j hj]; exact hseam)
  length_pos := by have h := a.length_pos; simp only [List.length_append]; omega
  first := a.first
  last := b.last
  first_eq := appendWord_first _ _ _ _ a.length_pos a.first a.first_eq
  last_eq := appendWord_last _ _ _ _ b.length_pos b.last b.last_eq

theorem PositionedWord.append_sites (a b : PositionedWord) hdis hseam :
    foldSites (a.append b hdis hseam).fold = foldSites a.fold ∪ foldSites b.fold :=
  foldSites_appendWord _ _ _ _

theorem PositionedWord.append_hSupport (a b : PositionedWord) hdis hseam :
    hSupport (a.append b hdis hseam).word (a.append b hdis hseam).fold =
      hSupport a.word a.fold ∪ hSupport b.word b.fold := hSupport_appendWord _ _ _ _

def pieceWords (ps : List PositionedWord) : Sequence := ps.flatMap PositionedWord.word

def pieceSites : List PositionedWord → Finset Site
  | [] => ∅
  | p :: ps => foldSites p.fold ∪ pieceSites ps

def pieceHsupport : List PositionedWord → Finset Site
  | [] => ∅
  | p :: ps => hSupport p.word p.fold ∪ pieceHsupport ps

theorem mem_pieceSites (ps : List PositionedWord) (x : Site) :
    x ∈ pieceSites ps ↔ ∃ p ∈ ps, x ∈ foldSites p.fold := by
  induction ps with
  | nil => simp [pieceSites]
  | cons p ps ih => simp [pieceSites, ih]

def piecesFirst : List PositionedWord → Option Site
  | [] => none
  | p :: _ => some p.first

def piecesLast : List PositionedWord → Option Site
  | [] => none
  | [p] => some p.last
  | _ :: q :: ps => piecesLast (q :: ps)

def piecesSeams : List PositionedWord → Prop
  | [] => True
  | [_] => True
  | p :: q :: ps => tetrahedralLattice.Adj p.last q.first ∧ piecesSeams (q :: ps)

structure PieceAssembly (ps : List PositionedWord) where
  piece : PositionedWord
  word_eq : piece.word = pieceWords ps
  sites_eq : foldSites piece.fold = pieceSites ps
  hSupport_eq : hSupport piece.word piece.fold = pieceHsupport ps
  first_eq : some piece.first = piecesFirst ps
  last_eq : some piece.last = piecesLast ps

theorem pieceAssembly_exists (ps : List PositionedWord) : ps ≠ [] →
    ps.Pairwise (fun a b => Disjoint (foldSites a.fold) (foldSites b.fold)) →
    piecesSeams ps → Nonempty (PieceAssembly ps) := by
  induction ps with
  | nil => intro hne; exact False.elim (hne rfl)
  | cons a ps ih =>
    intro hne hpair hseams
    cases ps with
    | nil =>
      exact ⟨{
        piece := a
        word_eq := by simp [pieceWords]
        sites_eq := by simp [pieceSites]
        hSupport_eq := by simp [pieceHsupport]
        first_eq := rfl
        last_eq := rfl }⟩
    | cons b ps =>
      obtain ⟨tail⟩ := ih (by simp) (List.pairwise_cons.mp hpair).2 hseams.2
      have hdis : Disjoint (foldSites a.fold) (foldSites tail.piece.fold) := by
        apply Finset.disjoint_left.mpr
        intro x hx hy
        rw [tail.sites_eq] at hy
        obtain ⟨p, hp, hxp⟩ := (mem_pieceSites _ x).mp hy
        exact Finset.disjoint_left.mp ((List.pairwise_cons.mp hpair).1 p hp) hx hxp
      have hfirst : tail.piece.first = b.first := Option.some.inj tail.first_eq
      have hseam : tetrahedralLattice.Adj a.last tail.piece.first := by
        rw [hfirst]
        exact hseams.1
      exact ⟨{
        piece := a.append tail.piece hdis hseam
        word_eq := by change a.word ++ tail.piece.word = a.word ++ pieceWords (b :: ps); rw [tail.word_eq]
        sites_eq := by rw [PositionedWord.append_sites, tail.sites_eq]; rfl
        hSupport_eq := by rw [PositionedWord.append_hSupport, tail.hSupport_eq]; rfl
        first_eq := rfl
        last_eq := tail.last_eq }⟩

noncomputable def assemblePieces (ps : List PositionedWord) (hne : ps ≠ [])
    (hpair : ps.Pairwise (fun a b => Disjoint (foldSites a.fold) (foldSites b.fold)))
    (hseams : piecesSeams ps) : PieceAssembly ps :=
  Classical.choice (pieceAssembly_exists ps hne hpair hseams)

end ProteinFolding.Tetrahedral.NearField
