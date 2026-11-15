import ProteinFolding.Cubic.Encodings
import ProteinFolding.Common.Complexity
import Mathlib.Data.List.OfFn

/-! Cubic direction certificates. These executable semantic verifiers are not
claimed to have a polynomial-time TM2 implementation merely from executability.
The final direction is padding, so there is one direction per residue. -/

namespace ProteinFolding.CubicCertificates

def step (p : Site) (d : Fin 6) : Site :=
  fun k => if k = 0 then
    if d = 0 then p 0 + 1 else if d = 1 then p 0 - 1 else p 0
  else if k = 1 then
    if d = 2 then p 1 + 1 else if d = 3 then p 1 - 1 else p 1
  else
    if d = 4 then p 2 + 1 else if d = 5 then p 2 - 1 else p 2

theorem distance_eq (p q : Site) : latticeDistance p q =
    (p 0 - q 0).natAbs + (p 1 - q 1).natAbs + (p 2 - q 2).natAbs := by
  have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  simp [latticeDistance, hu, Nat.add_assoc]

theorem site_ext {p q : Site}
    (h₀ : p 0 = q 0) (h₁ : p 1 = q 1) (h₂ : p 2 = q 2) : p = q := by
  funext k
  match k with
  | 0 => exact h₀
  | 1 => exact h₁
  | 2 => exact h₂

theorem step_adj (p : Site) (d : Fin 6) : cubicLattice.Adj p (step p d) := by
  change latticeDistance p (step p d) = 1
  rw [distance_eq]
  match d with
  | 0 => simp [step]
  | 1 => simp [step]
  | 2 => simp [step]
  | 3 => simp [step]
  | 4 => simp [step]
  | 5 => simp [step]

theorem step_coordinate_bounds (p : Site) (d : Fin 6) (k : Fin 3) :
    p k - 1 ≤ step p d k ∧ step p d k ≤ p k + 1 := by
  match k with
  | 0 => simp only [step]; split_ifs <;> omega
  | 1 => simp only [step]; split_ifs <;> omega
  | 2 => simp only [step]; split_ifs <;> omega

theorem adj_step {p q : Site} (h : cubicLattice.Adj p q) : ∃ d : Fin 6, step p d = q := by
  change latticeDistance p q = 1 at h
  rw [distance_eq] at h
  have hx : p 0 - q 0 = 0 ∨ p 0 - q 0 = 1 ∨ p 0 - q 0 = -1 := by omega
  have hy : p 1 - q 1 = 0 ∨ p 1 - q 1 = 1 ∨ p 1 - q 1 = -1 := by omega
  rcases hx with hx | hx | hx
  · rcases hy with hy | hy | hy
    · have hz : p 2 - q 2 = 1 ∨ p 2 - q 2 = -1 := by simp [hx, hy] at h; omega
      rcases hz with hz | hz
      · exact ⟨5, site_ext (by simp [step]; omega) (by simp [step]; omega) (by simp [step]; omega)⟩
      · exact ⟨4, site_ext (by simp [step]; omega) (by simp [step]; omega) (by simp [step]; omega)⟩
    · have hz : p 2 = q 2 := by simp [hx, hy] at h; omega
      exact ⟨3, site_ext (by simp [step]; omega) (by simp [step]; omega) (by simp [step]; omega)⟩
    · have hz : p 2 = q 2 := by simp [hx, hy] at h; omega
      exact ⟨2, site_ext (by simp [step]; omega) (by simp [step]; omega) (by simp [step]; omega)⟩
  · have hyz : p 1 = q 1 ∧ p 2 = q 2 := by simp [hx] at h; omega
    exact ⟨1, site_ext (by simp [step]; omega) (by simp [step]; omega) (by simp [step]; omega)⟩
  · have hyz : p 1 = q 1 ∧ p 2 = q 2 := by simp [hx] at h; omega
    exact ⟨0, site_ext (by simp [step]; omega) (by simp [step]; omega) (by simp [step]; omega)⟩

noncomputable def edgeDirection {p q : Site} (h : cubicLattice.Adj p q) : Fin 6 :=
  Classical.choose (adj_step h)

theorem step_edgeDirection {p q : Site} (h : cubicLattice.Adj p q) :
    step p (edgeDirection h) = q := Classical.choose_spec (adj_step h)

def shift (a p : Site) : Site := fun k => p k - a k

theorem shift_inj (a : Site) : Function.Injective (shift a) := by
  intro p q he
  funext k
  have hk := congrFun he k
  simp only [shift] at hk
  omega

theorem step_shift (a p : Site) (d : Fin 6) : step (shift a p) d = shift a (step p d) := by
  apply site_ext <;> simp only [step, shift]
  all_goals split_ifs <;> omega

theorem distance_shift (a p q : Site) : latticeDistance (shift a p) (shift a q) =
    latticeDistance p q := by
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  simp only [shift]
  omega

def shiftFold {n : ℕ} (f : Fold cubicLattice n) (a : Site) : Fold cubicLattice n where
  pos := shift a ∘ f.pos
  injective_pos := (shift_inj a).comp f.injective_pos
  consecutive := by
    intro i j hij
    change latticeDistance (shift a (f.pos i)) (shift a (f.pos j)) = 1
    rw [distance_shift]
    exact f.consecutive i j hij

theorem bondCount_shift {S : Sequence} (f : Fold cubicLattice S.length) (a : Site) :
    bondCount S (shiftFold f a) = bondCount S f := by
  unfold bondCount
  congr 1
  ext ij
  simp only [hhBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
  change (_ ∧ _ ∧ _ ∧ latticeDistance (shift a (f.pos ij.1)) (shift a (f.pos ij.2)) = 1) ↔ _
  rw [distance_shift]
  rfl

theorem fold_ext {n : ℕ} {f g : Fold cubicLattice n} (h : f.pos = g.pos) : f = g := by
  cases f
  cases g
  cases h
  rfl

abbrev DirectionWord := List (Fin 6)

def walkPosition (ds : DirectionWord) : ℕ → Site
  | 0 => fun _ => 0
  | k + 1 => step (walkPosition ds k) (ds[k]?.getD 0)

def directionPosition (S : Sequence) (ds : DirectionWord) : Fin S.length → Site :=
  fun i => walkPosition ds i.val

theorem walkPosition_coordinate_bounds (ds : DirectionWord) (n : ℕ) (k : Fin 3) :
    -(n : ℤ) ≤ walkPosition ds n k ∧ walkPosition ds n k ≤ (n : ℤ) := by
  induction n with
  | zero => simp [walkPosition]
  | succ n ih =>
    have hs := step_coordinate_bounds (walkPosition ds n) (ds[n]?.getD 0) k
    change -(↑(n + 1) : ℤ) ≤ step (walkPosition ds n) (ds[n]?.getD 0) k ∧
      step (walkPosition ds n) (ds[n]?.getD 0) k ≤ (↑(n + 1) : ℤ)
    omega

def ValidDirectionWord (S : Sequence) (ds : DirectionWord) : Prop :=
  ds.length = S.length ∧ Function.Injective (directionPosition S ds) ∧
    ∀ i j : Fin S.length, i.val + 1 = j.val →
      cubicLattice.Adj (directionPosition S ds i) (directionPosition S ds j)

instance (S : Sequence) (ds : DirectionWord) : Decidable (ValidDirectionWord S ds) :=
  inferInstanceAs (Decidable (_ ∧ (∀ _ _, _ → _) ∧ _))

def certificateFold (S : Sequence) (ds : DirectionWord) : Option (Fold cubicLattice S.length) :=
  if h : ValidDirectionWord S ds then some ⟨directionPosition S ds, h.2.1, h.2.2⟩ else none

def DirectionAccepts (input : HPInstance × DirectionWord) : Prop :=
  match certificateFold input.1.sequence input.2 with
  | none => False
  | some f => input.1.minBonds ≤ (bondCount input.1.sequence f : ℤ)

instance (input : HPInstance × DirectionWord) : Decidable (DirectionAccepts input) := by
  unfold DirectionAccepts
  split <;> infer_instance

def directionVerifier (input : HPInstance × DirectionWord) : Bool := decide (DirectionAccepts input)

theorem directionVerifier_spec (input : HPInstance × DirectionWord) :
    directionVerifier input = true ↔ DirectionAccepts input := by simp [directionVerifier]

noncomputable def foldDirections {S : Sequence} (f : Fold cubicLattice S.length) : DirectionWord :=
  List.ofFn fun i : Fin S.length =>
    if h : i.val + 1 < S.length then
      edgeDirection (f.consecutive i ⟨i.val + 1, h⟩ rfl)
    else 0

theorem foldDirections_length {S : Sequence} (f : Fold cubicLattice S.length) :
    (foldDirections f).length = S.length := by simp [foldDirections]

theorem foldDirections_step {S : Sequence} (f : Fold cubicLattice S.length)
    (i j : Fin S.length) (hij : i.val + 1 = j.val) :
    step (f.pos i) ((foldDirections f)[i.val]?.getD 0) = f.pos j := by
  have hlt : i.val + 1 < S.length := by omega
  simp only [foldDirections, List.getElem?_ofFn]
  simp only [i.isLt, ↓reduceDIte, Option.getD_some, hlt]
  convert step_edgeDirection (f.consecutive i ⟨i.val + 1, hlt⟩ rfl) using 1
  congr 1
  exact Fin.ext hij.symm

theorem walkPosition_foldDirections {S : Sequence} (f : Fold cubicLattice S.length)
    (h : 0 < S.length) (k : ℕ) (hk : k < S.length) :
    walkPosition (foldDirections f) k = shift (f.pos ⟨0, h⟩) (f.pos ⟨k, hk⟩) := by
  induction k with
  | zero => funext t; simp [walkPosition, shift]
  | succ k ih =>
    have hk' : k < S.length := by omega
    rw [walkPosition, ih hk', step_shift]
    congr 1
    exact foldDirections_step f ⟨k, hk'⟩ ⟨k + 1, hk⟩ rfl

theorem foldDirections_valid {S : Sequence} (f : Fold cubicLattice S.length) :
    ValidDirectionWord S (foldDirections f) := by
  refine ⟨foldDirections_length f, ?_, ?_⟩
  · intro i j he
    have h : 0 < S.length := by have := i.isLt; omega
    change walkPosition _ i.val = walkPosition _ j.val at he
    rw [walkPosition_foldDirections f h _ i.isLt, walkPosition_foldDirections f h _ j.isLt] at he
    exact f.injective_pos (shift_inj _ he)
  · intro i j hij
    change cubicLattice.Adj (walkPosition _ i.val) (walkPosition _ j.val)
    rw [← hij, walkPosition]
    exact step_adj _ _

theorem certificateFold_complete {S : Sequence} (f : Fold cubicLattice S.length) :
    ∃ g, certificateFold S (foldDirections f) = some g ∧ bondCount S g = bondCount S f := by
  have hv := foldDirections_valid f
  let g : Fold cubicLattice S.length := ⟨directionPosition S (foldDirections f), hv.2.1, hv.2.2⟩
  refine ⟨g, by simp [certificateFold, hv, g], ?_⟩
  by_cases h : 0 < S.length
  · have he : g = shiftFold f (f.pos ⟨0, h⟩) := by
      apply fold_ext
      funext i
      exact walkPosition_foldDirections f h i.val i.isLt
    rw [he, bondCount_shift]
  · have he : g = f := by
      apply fold_ext
      funext i
      have := i.isLt
      omega
    rw [he]

theorem directionAccepts_sound (I : HPInstance) (ds : DirectionWord)
    (h : DirectionAccepts (I, ds)) : I.Accepts := by
  unfold DirectionAccepts at h
  split at h
  · exact False.elim h
  · exact ⟨_, h⟩

theorem directionAccepts_length (I : HPInstance) (ds : DirectionWord)
    (h : DirectionAccepts (I, ds)) : ds.length = I.sequence.length := by
  by_cases hv : ValidDirectionWord I.sequence ds
  · exact hv.1
  · simp [DirectionAccepts, certificateFold, hv] at h

theorem hp_direction_certificate_iff (I : HPInstance) :
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

end ProteinFolding.CubicCertificates
