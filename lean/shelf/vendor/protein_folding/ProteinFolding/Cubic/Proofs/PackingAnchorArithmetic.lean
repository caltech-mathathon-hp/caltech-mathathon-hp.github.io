import ProteinFolding.Cubic.Proofs.PackingWords

/-! Arithmetic forcing for the alternative frame. The anchor modulus Q is
strictly larger than the number q of bins. This is the general forcing lemma
needed by the current construction, independently of the older special-case
arithmetic in `Cubic/PackingArithmetic.lean`. -/

namespace ProteinFolding.CubicPacking

/-- The rail without gap blocks contains every long anchor and no short one. -/
theorem anchor_modulus_forcing (Q q i j : ℕ) (hQ : 0 < Q) (hq : q < Q) (hj : j ≤ q)
    (hfill : Q * i + (2 * Q + 1) * j = q * (2 * Q + 1)) : j = q ∧ i = 0 := by
  have he : Q * (i + 2 * j) + j = Q * (2 * q) + q := by nlinarith [hfill]
  have hm := congrArg (fun k => k % Q) he
  have hjQ : j < Q := lt_of_le_of_lt hj hq
  have heq : j = q := by
    simpa only [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hjQ, Nat.mod_eq_of_lt hq] using hm
  subst j
  exact ⟨rfl, by nlinarith⟩

theorem anchor_length_forcing (Q q i j : ℕ) (hQ : 0 < Q) (hq : q < Q) (hj : j ≤ q)
    (hfill : i * alpha Q + j * beta Q = depth q Q) : j = q ∧ i = 0 := by
  apply anchor_modulus_forcing Q q i j hQ hq hj
  dsimp [alpha, beta, depth] at hfill
  nlinarith

/-- Consecutive gap blocks cannot jump between the two nonincident rails. -/
theorem gap_link_shorter_than_rail_distance (q Q : ℕ) (hq : 2 ≤ q) (hQ : q < Q) :
    4 * Q + 7 < depth q Q + 1 := by
  dsimp [depth, beta]
  nlinarith

/-- The large face words cannot fit inside a packing bin, even the face word
with two omitted H residues. -/
theorem bin_smaller_than_large_face (q Q : ℕ) (hq : 2 ≤ q) (hQ : q < Q) :
    4 * Q * depth q Q < depth q Q ^ 2 - 2 := by
  have hd : 2 * (4 * Q + 2) ≤ depth q Q := by
    dsimp [depth, beta]
    nlinarith
  have hQpos : 0 < Q := by omega
  have hdpos : 0 < depth q Q := by omega
  have hlarge : 4 * Q * depth q Q + 2 < depth q Q ^ 2 := by nlinarith
  omega

theorem item_larger_than_two_sites (q Q a : ℕ) (hq : 2 ≤ q) (ha : 0 < a) :
    2 < depth q Q * a := by
  have hd : 4 ≤ depth q Q := by dsimp [depth, beta]; nlinarith
  nlinarith

end ProteinFolding.CubicPacking
