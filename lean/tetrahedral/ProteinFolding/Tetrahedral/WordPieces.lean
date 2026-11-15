import ProteinFolding.Tetrahedral.ConstructionParameters
import ProteinFolding.Tetrahedral.Statement
import Mathlib.Data.Fintype.Fin

/-! Literal dimer and separator words from Section 6. Separator indices are
zero based, as in ConstructionParameters. The complete reduction additionally
requires the frame and bulk-cover words and their geometric proofs. -/

namespace ProteinFolding.Tetrahedral

theorem hydrophobicCount_eq_count (S : Sequence) :
    hydrophobicCount S = S.count Residue.H := by
  simpa [hydrophobicCount, hydrophobicIndices, List.Vector.get] using
    Fin.card_filter_univ_eq_vector_get_eq_count Residue.H
      (⟨S, rfl⟩ : List.Vector Residue S.length)

theorem hydrophobicCount_append (u v : Sequence) :
    hydrophobicCount (u ++ v) = hydrophobicCount u + hydrophobicCount v := by
  simp only [hydrophobicCount_eq_count, List.count_append]

theorem hydrophobicCount_replicate (n : ℕ) (r : Residue) :
    hydrophobicCount (List.replicate n r) = if r = .H then n else 0 := by
  rw [hydrophobicCount_eq_count, List.count_replicate]
  split_ifs <;> simp_all

def repeatWord (w : Sequence) : ℕ → Sequence
  | 0 => []
  | n + 1 => w ++ repeatWord w n

theorem repeatWord_length (w : Sequence) (n : ℕ) :
    (repeatWord w n).length = n * w.length := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih => simp [repeatWord, ih, Nat.succ_mul, Nat.add_comm]

theorem hydrophobicCount_repeatWord (w : Sequence) (n : ℕ) :
    hydrophobicCount (repeatWord w n) = n * hydrophobicCount w := by
  induction n with
  | zero => simp [repeatWord, hydrophobicCount_eq_count]
  | succ n ih =>
    simp [repeatWord, hydrophobicCount_append, ih, Nat.succ_mul, Nat.add_comm]

/-- `(HH PPP)^(q-1) HH`, with the empty word at q=0. -/
def dimerChain : ℕ → Sequence
  | 0 => []
  | q + 1 => repeatWord [.H, .H, .P, .P, .P] q ++ [.H, .H]

theorem dimerChain_count (q : ℕ) : hydrophobicCount (dimerChain q) = 2 * q := by
  cases q with
  | zero => simp [dimerChain, hydrophobicCount_eq_count]
  | succ q =>
    rw [dimerChain, hydrophobicCount_append, hydrophobicCount_repeatWord]
    have h₁ : hydrophobicCount [.H, .H, .P, .P, .P] = 2 := by decide
    have h₂ : hydrophobicCount [.H, .H] = 2 := by decide
    rw [h₁, h₂]
    omega

theorem dimerChain_length (q : ℕ) (hq : 0 < q) :
    (dimerChain q).length + 3 = 5 * q := by
  cases q with
  | zero => omega
  | succ q => simp [dimerChain, repeatWord_length]; omega

namespace ConstructionParameters

def entryTether (p : ConstructionParameters) (k : ℕ) : ℕ :=
  2 * p.separatorIndex k + 3 + p.entrySlack k

def exitTether (p : ConstructionParameters) (k : ℕ) : ℕ :=
  2 * (p.side - 2 - p.separatorIndex k) + 3 + p.exitSlack k

/-- Entry anchor, two-dimer separator, exit anchor, with the exact P-runs. -/
def separatorWord (p : ConstructionParameters) (k : ℕ) : Sequence :=
  dimerChain 1 ++ List.replicate (p.entryTether k) .P ++ dimerChain 2 ++
    List.replicate (p.exitTether k) .P ++ dimerChain 3

theorem separatorIndex_add_two_le (p : ConstructionParameters) (k : ℕ)
    (hk : k ≤ p.bins) : p.separatorIndex k + 2 ≤ p.side := by
  have h := p.separator_room k hk
  omega

theorem entryTether_odd (p : ConstructionParameters) (k : ℕ) :
    p.entryTether k % 2 = 1 := by
  have h := p.entrySlack_even k
  unfold entryTether
  omega

theorem exitTether_odd (p : ConstructionParameters) (k : ℕ) :
    p.exitTether k % 2 = 1 := by
  have h := p.exitSlack_even k
  unfold exitTether
  omega

theorem tether_total (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    p.entryTether k + p.exitTether k =
      2 * p.side + 2 + p.entrySlack k + p.exitSlack k := by
  have h := p.separatorIndex_add_two_le k hk
  unfold entryTether exitTether
  omega

theorem separatorWord_count (p : ConstructionParameters) (k : ℕ) :
    hydrophobicCount (p.separatorWord k) = 12 := by
  simp [separatorWord, hydrophobicCount_append, hydrophobicCount_replicate,
    dimerChain_count]

theorem separatorWord_length (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    (p.separatorWord k).length = 2 * p.side + 23 + p.entrySlack k + p.exitSlack k := by
  have h := p.tether_total k hk
  have h₁ := dimerChain_length 1 (by decide)
  have h₂ := dimerChain_length 2 (by decide)
  have h₃ := dimerChain_length 3 (by decide)
  simp only [separatorWord, List.length_append, List.length_replicate]
  omega

/-- The subword between the two anchor H's, excluding those anchor H's.
Its endpoints are dangling P sites in the soundness distance argument. -/
def separatorBridge (p : ConstructionParameters) (k : ℕ) : Sequence :=
  List.replicate (p.entryTether k) .P ++ dimerChain 2 ++
    List.replicate (p.exitTether k) .P

theorem separatorBridge_length (p : ConstructionParameters) (k : ℕ)
    (hk : k ≤ p.bins) :
    (p.separatorBridge k).length = 2 * p.side + 9 + p.entrySlack k + p.exitSlack k := by
  have h := p.tether_total k hk
  have h₂ := dimerChain_length 2 (by decide)
  simp only [separatorBridge, List.length_append, List.length_replicate]
  omega

theorem separatorBridge_span_bound (p : ConstructionParameters) (k : ℕ)
    (hk : k ≤ p.bins) :
    (p.separatorBridge k).length - 1 ≤ 2 * p.side + 10 + 2 * p.sigma := by
  rw [separatorBridge_length p k hk]
  have h := p.tether_slack_bounds k hk
  omega

end ConstructionParameters

end ProteinFolding.Tetrahedral
