import ProteinFolding.Square.Normalization
import ProteinFolding.Square.Counting
import ProteinFolding.Square.Encodings
import ProteinFolding.Common.Complexity
import Mathlib.Data.List.OfFn

/-!
Direction-word certificates: a total, executable verifier and the semantic
certificate theorem. The last direction is padding; there is exactly one symbol
per residue. No claim of a polynomial-time TM2 implementation follows merely
from these definitions being executable.
-/

namespace ProteinFolding.Square

abbrev DirectionWord := List (Fin 4)

def directionEncoding : Computability.FinEncoding DirectionWord := wordEncoding (Fin 4)

def walkPosition (ds : DirectionWord) : ℕ → Site
  | 0 => fun _ => 0
  | k + 1 => step (walkPosition ds k) (ds[k]?.getD 0)

def directionPosition (S : Sequence) (ds : DirectionWord) : Fin S.length → Site :=
  fun i => walkPosition ds i.val

def ValidDirectionWord (S : Sequence) (ds : DirectionWord) : Prop :=
  ds.length = S.length ∧ Function.Injective (directionPosition S ds) ∧
    ∀ i j : Fin S.length, i.val + 1 = j.val →
      squareLattice.Adj (directionPosition S ds i) (directionPosition S ds j)

instance decidableValidDirectionWord (S : Sequence) (ds : DirectionWord) : Decidable (ValidDirectionWord S ds) :=
  inferInstanceAs (Decidable (_ ∧ (∀ _ _, _ → _) ∧ _))

def certificateFold (S : Sequence) (ds : DirectionWord) : Option (Fold squareLattice S.length) :=
  if h : ValidDirectionWord S ds then some ⟨directionPosition S ds, h.2.1, h.2.2⟩ else none

def DirectionAccepts (input : LossInstance × DirectionWord) : Prop :=
  match certificateFold input.1.sequence input.2 with
  | none => False
  | some f => (lossCount input.1.sequence f : ℤ) ≤ input.1.maxLosses

instance decidableDirectionAccepts (input : LossInstance × DirectionWord) : Decidable (DirectionAccepts input) := by
  unfold DirectionAccepts
  split <;> infer_instance

def directionVerifier (input : LossInstance × DirectionWord) : Bool := decide (DirectionAccepts input)

theorem directionVerifier_spec (input : LossInstance × DirectionWord) :
    directionVerifier input = true ↔ DirectionAccepts input := by simp [directionVerifier]

noncomputable def foldDirections {S : Sequence} (f : Fold squareLattice S.length) : DirectionWord :=
  List.ofFn fun i : Fin S.length =>
    if h : i.val + 1 < S.length then
      edgeDirection (f.consecutive i ⟨i.val + 1, h⟩ rfl)
    else 0

theorem foldDirections_length {S : Sequence} (f : Fold squareLattice S.length) :
    (foldDirections f).length = S.length := by simp [foldDirections]

theorem foldDirections_step {S : Sequence} (f : Fold squareLattice S.length)
    (i j : Fin S.length) (hij : i.val + 1 = j.val) :
    step (f.pos i) ((foldDirections f)[i.val]?.getD 0) = f.pos j := by
  have hlt : i.val + 1 < S.length := by omega
  simp only [foldDirections, List.getElem?_ofFn]
  simp only [i.isLt, ↓reduceDIte, Option.getD_some, hlt]
  convert step_edgeDirection (f.consecutive i ⟨i.val + 1, hlt⟩ rfl) using 1
  congr 1
  exact Fin.ext hij.symm

theorem walkPosition_foldDirections {S : Sequence} (f : Fold squareLattice S.length)
    (h : 0 < S.length) (k : ℕ) (hk : k < S.length) :
    walkPosition (foldDirections f) k = shift (f.pos ⟨0, h⟩) (f.pos ⟨k, hk⟩) := by
  induction k with
  | zero => funext t; simp [walkPosition, shift]
  | succ k ih =>
    have hk' : k < S.length := by omega
    rw [walkPosition, ih hk', step_shift]
    congr 1
    exact foldDirections_step f ⟨k, hk'⟩ ⟨k + 1, hk⟩ rfl

theorem foldDirections_valid {S : Sequence} (f : Fold squareLattice S.length) :
    ValidDirectionWord S (foldDirections f) := by
  refine ⟨foldDirections_length f, ?_, ?_⟩
  · intro i j he
    have h : 0 < S.length := by have := i.isLt; omega
    change walkPosition _ i.val = walkPosition _ j.val at he
    rw [walkPosition_foldDirections f h _ i.isLt, walkPosition_foldDirections f h _ j.isLt] at he
    exact f.injective_pos (shift_inj _ he)
  · intro i j hij
    change squareLattice.Adj (walkPosition _ i.val) (walkPosition _ j.val)
    rw [← hij, walkPosition]
    exact step_adj _ _

theorem certificateFold_complete {S : Sequence} (f : Fold squareLattice S.length) :
    ∃ g, certificateFold S (foldDirections f) = some g ∧ lossCount S g = lossCount S f := by
  have hv := foldDirections_valid f
  let g : Fold squareLattice S.length := ⟨directionPosition S (foldDirections f), hv.2.1, hv.2.2⟩
  refine ⟨g, by simp [certificateFold, hv, g], ?_⟩
  by_cases h : 0 < S.length
  · have he : g = shiftFold f (f.pos ⟨0, h⟩) := by
      apply fold_ext
      funext i
      exact walkPosition_foldDirections f h i.val i.isLt
    rw [he, lossCount_shift]
  · have he : g = f := by
      apply fold_ext
      funext i
      have := i.isLt
      omega
    rw [he]

theorem directionAccepts_sound (I : LossInstance) (ds : DirectionWord)
    (h : DirectionAccepts (I, ds)) : I.Accepts := by
  unfold DirectionAccepts at h
  split at h
  · exact False.elim h
  · exact ⟨_, h⟩

theorem loss_certificate_iff (I : LossInstance) :
    I.Accepts ↔ ∃ ds : DirectionWord, ds.length = I.sequence.length ∧ DirectionAccepts (I, ds) := by
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨g, hg, he⟩ := certificateFold_complete f
    refine ⟨foldDirections f, foldDirections_length f, ?_⟩
    simp only [DirectionAccepts]
    rw [hg]
    simpa [he] using hf
  · rintro ⟨ds, _, hd⟩
    exact directionAccepts_sound I ds hd

theorem sequence_length_le_lossEncoding (I : LossInstance) :
    I.sequence.length ≤ (lossEncoding.encode I).length := by
  simp [lossEncoding, pairEncoding, sequenceEncoding, wordEncoding]

/-- The remaining machine-level verifier obligation, isolated explicitly. -/
def LossVerifierPolyTime : Prop :=
  PolyTimeDecidable (pairEncoding lossEncoding directionEncoding) DirectionAccepts

theorem loss_inNP_of_verifier_polyTime (h : LossVerifierPolyTime) :
    InNP lossEncoding LossInstance.Accepts := by
  refine ⟨DirectionWord, directionEncoding, ?_, Polynomial.X, DirectionAccepts, h, ?_⟩
  · exact fun ds => ⟨ds, rfl⟩
  · intro I
    constructor
    · intro hI
      obtain ⟨ds, hlen, hd⟩ := (loss_certificate_iff I).1 hI
      refine ⟨ds, ?_, hd⟩
      simpa [directionEncoding, wordEncoding, hlen] using sequence_length_le_lossEncoding I
    · rintro ⟨ds, _, hd⟩
      exact directionAccepts_sound I ds hd

end ProteinFolding.Square
