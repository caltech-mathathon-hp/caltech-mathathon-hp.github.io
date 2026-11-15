import ProteinFolding.Tetrahedral.Normalization
import ProteinFolding.Tetrahedral.Encodings
import ProteinFolding.Common.Complexity
import Mathlib.Data.List.OfFn

/-!
# Direction-word certificates for tetrahedral HP folding

There is one Fin 4 symbol per residue; the last symbol is unused padding.
The verifier is a total Boolean function. The semantic certificate theorem
and its linear length bound are proved here. The actual polynomial-time TM2
implementation remains an explicit proof obligation, not an axiom.
-/

namespace ProteinFolding.Tetrahedral

abbrev DirectionWord := List (Fin 4)

def directionEncoding : Computability.FinEncoding DirectionWord := wordEncoding (Fin 4)

def walkPosition (ds : DirectionWord) : ℕ → Site
  | 0 => origin
  | k + 1 => step (walkPosition ds k) (ds[k]?.getD 0)

def directionPosition (S : Sequence) (ds : DirectionWord) : Fin S.length → Site :=
  fun i => walkPosition ds i.val

def ValidDirectionWord (S : Sequence) (ds : DirectionWord) : Prop :=
  ds.length = S.length ∧ Function.Injective (directionPosition S ds) ∧
    ∀ i j : Fin S.length, i.val + 1 = j.val →
      tetrahedralLattice.Adj (directionPosition S ds i) (directionPosition S ds j)

instance decidableValidDirectionWord (S : Sequence) (ds : DirectionWord) :
    Decidable (ValidDirectionWord S ds) :=
  inferInstanceAs (Decidable (_ ∧ (∀ _ _, _ → _) ∧ _))

def certificateFold (S : Sequence) (ds : DirectionWord) :
    Option (Fold tetrahedralLattice S.length) :=
  if h : ValidDirectionWord S ds then some ⟨directionPosition S ds, h.2.1, h.2.2⟩ else none

def DirectionAccepts (input : HPInstance × DirectionWord) : Prop :=
  match certificateFold input.1.sequence input.2 with
  | none => False
  | some f => input.1.minBonds ≤ (bondCount input.1.sequence f : ℤ)

instance decidableDirectionAccepts (input : HPInstance × DirectionWord) :
    Decidable (DirectionAccepts input) := by
  unfold DirectionAccepts
  split <;> infer_instance

def directionVerifier (input : HPInstance × DirectionWord) : Bool := decide (DirectionAccepts input)

theorem directionVerifier_spec (input : HPInstance × DirectionWord) :
    directionVerifier input = true ↔ DirectionAccepts input := by simp [directionVerifier]

noncomputable def edgeDirection {p q : Site} (h : tetrahedralLattice.Adj p q) : Fin 4 :=
  Classical.choose ((adj_iff_exists_step p q).mp h)

theorem step_edgeDirection {p q : Site} (h : tetrahedralLattice.Adj p q) :
    step p (edgeDirection h) = q := Classical.choose_spec ((adj_iff_exists_step p q).mp h)

noncomputable def foldDirections {S : Sequence} (f : Fold tetrahedralLattice S.length) :
    DirectionWord :=
  List.ofFn fun i : Fin S.length =>
    if h : i.val + 1 < S.length then
      edgeDirection (f.consecutive i ⟨i.val + 1, h⟩ rfl)
    else 0

theorem foldDirections_length {S : Sequence} (f : Fold tetrahedralLattice S.length) :
    (foldDirections f).length = S.length := by simp [foldDirections]

theorem foldDirections_step {S : Sequence} (f : Fold tetrahedralLattice S.length)
    (i j : Fin S.length) (hij : i.val + 1 = j.val) :
    step (f.pos i) ((foldDirections f)[i.val]?.getD 0) = f.pos j := by
  have hlt : i.val + 1 < S.length := by omega
  simp only [foldDirections, List.getElem?_ofFn]
  simp only [i.isLt, ↓reduceDIte, Option.getD_some, hlt]
  convert step_edgeDirection (f.consecutive i ⟨i.val + 1, hlt⟩ rfl) using 1
  congr 1
  exact Fin.ext hij.symm

theorem walkPosition_foldDirections {S : Sequence} (f : Fold tetrahedralLattice S.length)
    (hf : IsNormalized f) (k : ℕ) (hk : k < S.length) :
    walkPosition (foldDirections f) k = f.pos ⟨k, hk⟩ := by
  induction k with
  | zero => exact (hf ⟨0, hk⟩ rfl).symm
  | succ k ih =>
    have hk' : k < S.length := by omega
    rw [walkPosition, ih hk']
    exact foldDirections_step f ⟨k, hk'⟩ ⟨k + 1, hk⟩ rfl

theorem foldDirections_valid {S : Sequence} (f : Fold tetrahedralLattice S.length)
    (hf : IsNormalized f) : ValidDirectionWord S (foldDirections f) := by
  refine ⟨foldDirections_length f, ?_, ?_⟩
  · intro i j heq
    change walkPosition _ i.val = walkPosition _ j.val at heq
    rw [walkPosition_foldDirections f hf _ i.isLt,
      walkPosition_foldDirections f hf _ j.isLt] at heq
    exact f.injective_pos heq
  · intro i j hij
    change tetrahedralLattice.Adj (walkPosition _ i.val) (walkPosition _ j.val)
    rw [← hij, walkPosition]
    exact step_adj _ _

theorem tetrahedral_fold_ext {n : ℕ} {f g : Fold tetrahedralLattice n}
    (h : f.pos = g.pos) : f = g := by
  cases f
  cases g
  cases h
  rfl

theorem certificateFold_complete {S : Sequence} (f : Fold tetrahedralLattice S.length) :
    ∃ g, certificateFold S (foldDirections (normalizedFold f)) = some g ∧
      bondCount S g = bondCount S f := by
  have hv := foldDirections_valid (normalizedFold f) (normalizedFold_normalized f)
  let g : Fold tetrahedralLattice S.length :=
    ⟨directionPosition S (foldDirections (normalizedFold f)), hv.2.1, hv.2.2⟩
  refine ⟨g, by simp [certificateFold, hv, g], ?_⟩
  have heq : g = normalizedFold f := by
    apply tetrahedral_fold_ext
    funext i
    exact walkPosition_foldDirections _ (normalizedFold_normalized f) i.val i.isLt
  rw [heq, normalizedFold_bondCount]

theorem directionAccepts_sound (I : HPInstance) (ds : DirectionWord)
    (h : DirectionAccepts (I, ds)) : I.Accepts := by
  unfold DirectionAccepts at h
  split at h
  · exact False.elim h
  · exact ⟨_, h⟩

/-- Sound and complete certificates over a fixed four-symbol alphabet, with
exactly one direction symbol per residue, including the empty-word case. -/
theorem hp_certificate_iff (I : HPInstance) :
    I.Accepts ↔ ∃ ds : DirectionWord,
      ds.length = I.sequence.length ∧ DirectionAccepts (I, ds) := by
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨g, hg, he⟩ := certificateFold_complete f
    refine ⟨foldDirections (normalizedFold f), foldDirections_length _, ?_⟩
    simp only [DirectionAccepts]
    rw [hg]
    simpa [he] using hf
  · rintro ⟨ds, _, hd⟩
    exact directionAccepts_sound I ds hd

theorem sequence_length_le_hpEncoding (I : HPInstance) :
    I.sequence.length ≤ (hpEncoding.encode I).length := by
  simp [hpEncoding, pairEncoding, sequenceEncoding, wordEncoding]

/-- A remaining machine-level proof target. Executability alone does not prove it. -/
def HPVerifierPolyTime : Prop :=
  PolyTimeDecidable (pairEncoding hpEncoding directionEncoding) DirectionAccepts

theorem hp_inNP_of_verifier_polyTime (h : HPVerifierPolyTime) :
    InNP hpEncoding HPInstance.Accepts := by
  refine ⟨DirectionWord, directionEncoding, ?_, Polynomial.X, DirectionAccepts, h, ?_⟩
  · exact fun ds => ⟨ds, rfl⟩
  · intro I
    constructor
    · intro hI
      obtain ⟨ds, hlen, hd⟩ := (hp_certificate_iff I).1 hI
      refine ⟨ds, ?_, hd⟩
      simpa [directionEncoding, wordEncoding, hlen] using sequence_length_le_hpEncoding I
    · rintro ⟨ds, _, hd⟩
      exact directionAccepts_sound I ds hd

end ProteinFolding.Tetrahedral
