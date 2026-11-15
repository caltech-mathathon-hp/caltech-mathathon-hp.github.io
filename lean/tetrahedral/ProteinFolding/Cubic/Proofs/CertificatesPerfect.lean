import ProteinFolding.Cubic.Proofs.CertificatesBits
import ProteinFolding.Cubic.Proofs.GeometryBasics

/-! A finite perfect-packing verifier. At positive side length the lower corner
is occupied by H, so only the finitely many residue positions need be tried as
corners. Side zero is treated separately. The cube itself is enumerated by the
finite interface in `CubicGeometry`; no infinite set equality is decided. -/

namespace ProteinFolding.CubicCertificates

open CubicGeometry

theorem packsCube_shift {S : Sequence} (f : Fold cubicLattice S.length)
    (a : Site) (n : ℕ) (hp : PacksCube S f n) : PacksCube S (shiftFold f a) n := by
  obtain ⟨b, hb⟩ := hp
  refine ⟨shift a b, ?_⟩
  ext p
  constructor
  · rintro ⟨i, hi, he⟩
    have hmem : f.pos i ∈ cube b n := by rw [← hb]; exact ⟨i, hi, rfl⟩
    intro k
    have hk := hmem k
    have he' := congrFun he k
    change f.pos i k - a k = p k at he'
    change b k - a k ≤ p k ∧ p k < b k - a k + (n : ℤ)
    omega
  · intro hmem
    let q : Site := fun k => p k + a k
    have hq : q ∈ cube b n := by
      intro k
      have hk := hmem k
      change b k - a k ≤ p k ∧ p k < b k - a k + (n : ℤ) at hk
      change b k ≤ p k + a k ∧ p k + a k < b k + (n : ℤ)
      omega
    rw [← hb] at hq
    obtain ⟨i, hi, he⟩ := hq
    refine ⟨i, hi, ?_⟩
    funext k
    have hk := congrFun he k
    change f.pos i k = p k + a k at hk
    change f.pos i k - a k = p k
    omega

def FinitePacksCube (S : Sequence) (f : Fold cubicLattice S.length) (n : ℕ) : Prop :=
  if n = 0 then hydrophobicCount S = 0 else
    ∃ i : Fin S.length, S.get i = Residue.H ∧ hSupport S f = cubeFinset (f.pos i) n

instance (S : Sequence) (f : Fold cubicLattice S.length) (n : ℕ) :
    Decidable (FinitePacksCube S f n) := by
  unfold FinitePacksCube
  split <;> infer_instance

theorem finitePacksCube_iff (S : Sequence) (f : Fold cubicLattice S.length) (n : ℕ) :
    FinitePacksCube S f n ↔ PacksCube S f n := by
  by_cases hn : n = 0
  · subst n
    simp only [FinitePacksCube]
    exact ⟨packsCube_zero_of_count_zero S f,
      fun h => by simpa using packsCube_count S f 0 h⟩
  · simp only [FinitePacksCube, if_neg hn]
    constructor
    · rintro ⟨i, _, he⟩
      exact (packsCube_iff_finset S f n).2 ⟨f.pos i, he⟩
    · rintro ⟨a, ha⟩
      have hcorner : a ∈ cube a n := by
        intro k
        have hn' : 0 < n := Nat.pos_of_ne_zero hn
        constructor <;> omega
      rw [← ha] at hcorner
      obtain ⟨i, hi, hpos⟩ := hcorner
      refine ⟨i, hi, ?_⟩
      ext p
      rw [mem_hSupport, mem_cubeFinset, ha, hpos]

theorem certificateFold_preserves_packing {S : Sequence}
    (f : Fold cubicLattice S.length) (n : ℕ) (hp : PacksCube S f n) :
    ∃ g, certificateFold S (foldDirections f) = some g ∧ PacksCube S g n := by
  have hv := foldDirections_valid f
  let g : Fold cubicLattice S.length := ⟨directionPosition S (foldDirections f), hv.2.1, hv.2.2⟩
  refine ⟨g, by simp [certificateFold, hv, g], ?_⟩
  by_cases h : 0 < S.length
  · have he : g = shiftFold f (f.pos ⟨0, h⟩) := by
      apply fold_ext
      funext i
      exact walkPosition_foldDirections f h i.val i.isLt
    rw [he]
    exact packsCube_shift f _ n hp
  · have he : g = f := by
      apply fold_ext
      funext i
      have := i.isLt
      omega
    rwa [he]

def PerfectDirectionAccepts (input : PerfectInput × DirectionWord) : Prop :=
  hydrophobicCount input.1.1 = input.1.2 ^ 3 ∧
    match certificateFold input.1.1 input.2 with
    | none => False
    | some f => FinitePacksCube input.1.1 f input.1.2

instance (input : PerfectInput × DirectionWord) : Decidable (PerfectDirectionAccepts input) := by
  unfold PerfectDirectionAccepts
  split <;> infer_instance

theorem perfectDirectionAccepts_sound (I : PerfectInput) (ds : DirectionWord)
    (h : PerfectDirectionAccepts (I, ds)) : PerfectHPStringFold I.1 I.2 := by
  obtain ⟨hc, h⟩ := h
  refine ⟨hc, ?_⟩
  split at h
  · exact False.elim h
  · exact ⟨_, (finitePacksCube_iff _ _ _).1 h⟩

theorem perfect_direction_certificate_iff (I : PerfectInput) :
    PerfectHPStringFold I.1 I.2 ↔ ∃ ds : DirectionWord,
      ds.length = I.1.length ∧ PerfectDirectionAccepts (I, ds) := by
  constructor
  · rintro ⟨hc, f, hf⟩
    obtain ⟨g, hg, hpack⟩ := certificateFold_preserves_packing f I.2 hf
    refine ⟨foldDirections f, foldDirections_length f, hc, ?_⟩
    rw [hg]
    exact (finitePacksCube_iff _ _ _).2 hpack
  · rintro ⟨ds, _, hd⟩
    exact perfectDirectionAccepts_sound I ds hd

def PerfectBitsAccepts (input : PerfectInput × List Bool) : Prop :=
  match decodeDirections input.2 with
  | none => False
  | some ds => PerfectDirectionAccepts (input.1, ds)

instance (input : PerfectInput × List Bool) : Decidable (PerfectBitsAccepts input) := by
  unfold PerfectBitsAccepts
  split <;> infer_instance

def perfectBitsVerifier (input : PerfectInput × List Bool) : Bool := decide (PerfectBitsAccepts input)

theorem perfectBitsVerifier_spec (input : PerfectInput × List Bool) :
    perfectBitsVerifier input = true ↔ PerfectBitsAccepts input := by simp [perfectBitsVerifier]

theorem perfectBitsAccepts_sound (I : PerfectInput) (w : List Bool)
    (h : PerfectBitsAccepts (I, w)) : PerfectHPStringFold I.1 I.2 := by
  unfold PerfectBitsAccepts at h
  split at h
  · exact False.elim h
  · exact perfectDirectionAccepts_sound I _ h

theorem perfect_bits_certificate_iff (I : PerfectInput) :
    PerfectHPStringFold I.1 I.2 ↔ ∃ w : List Bool,
      w.length = 3 * I.1.length ∧ PerfectBitsAccepts (I, w) := by
  constructor
  · intro hI
    obtain ⟨ds, hlen, hd⟩ := (perfect_direction_certificate_iff I).1 hI
    refine ⟨encodeDirections ds, ?_, ?_⟩
    · rw [encodeDirections_length, hlen]
    · simpa only [PerfectBitsAccepts, decode_encodeDirections] using hd
  · rintro ⟨w, _, hw⟩
    exact perfectBitsAccepts_sound I w hw

theorem sequence_length_le_perfectEncoding (I : PerfectInput) :
    I.1.length ≤ (perfectEncoding.encode I).length := by
  simp [perfectEncoding, pairEncoding, sequenceEncoding, wordEncoding]

/-- This explicit hypothesis remains to be discharged by an actual TM2 verifier. -/
def PerfectBitsVerifierPolyTime : Prop :=
  PolyTimeDecidable (pairEncoding perfectEncoding (wordEncoding Bool)) PerfectBitsAccepts

theorem perfect_inNP_of_bits_verifier_polyTime (h : PerfectBitsVerifierPolyTime) :
    InNP perfectEncoding (fun I => PerfectHPStringFold I.1 I.2) := by
  refine ⟨List Bool, wordEncoding Bool, ?_, Polynomial.C 3 * Polynomial.X, PerfectBitsAccepts, h, ?_⟩
  · exact fun w => ⟨w, rfl⟩
  · intro I
    constructor
    · intro hI
      obtain ⟨w, hlen, hw⟩ := (perfect_bits_certificate_iff I).1 hI
      refine ⟨w, ?_, hw⟩
      simpa [wordEncoding, hlen] using Nat.mul_le_mul_left 3 (sequence_length_le_perfectEncoding I)
    · rintro ⟨w, _, hw⟩
      exact perfectBitsAccepts_sound I w hw

end ProteinFolding.CubicCertificates
