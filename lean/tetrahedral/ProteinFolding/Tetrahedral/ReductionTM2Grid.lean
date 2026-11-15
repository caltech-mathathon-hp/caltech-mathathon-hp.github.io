import ProteinFolding.Tetrahedral.ReductionTM2Division
import ProteinFolding.Tetrahedral.Octahedron

/-! A deterministic natural index for a box containing the entire octahedron.
The scan includes nonlattice and deleted sites; the explicit graph predicate
will filter them. The generous existing coordinate box avoids a new geometric
assumption, and has cubic size in the construction parameter. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.Grid

open Computability Turing TM2CompositionPoly TM2ProductMap

def base (m : ℕ) : ℕ := 4 * m + 3
def count (m : ℕ) : ℕ := base m * base m * base m

def digits (b i : ℕ) : Fin 3 → ℕ := ![i / (b * b), (i / b) % b, i % b]

def index (b x y z : ℕ) : ℕ := (x * b + y) * b + z

def point (m i : ℕ) : Coordinates :=
  ![(digits (base m) i 0 : ℤ) - (2 * (m : ℤ) + 1),
    (digits (base m) i 1 : ℤ) - 3,
    (digits (base m) i 2 : ℤ) - (2 * (m : ℤ) + 1)]

theorem base_positive (m : ℕ) : 0 < base m := by unfold base; omega

theorem digits_reconstruct (b i : ℕ) :
    index b (digits b i 0) (digits b i 1) (digits b i 2) = i := by
  simp only [index, digits, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  have hq := Nat.div_add_mod (i / b) b
  have hi := Nat.div_add_mod i b
  calc
    (i / (b * b) * b + i / b % b) * b + i % b =
        (b * (i / b / b) + i / b % b) * b + i % b := by
          rw [Nat.div_div_eq_div_mul]
          ring
    _ = (i / b) * b + i % b := by rw [hq]
    _ = i := by simpa only [Nat.mul_comm] using hi

theorem digits_index (b x y z : ℕ) (hb : 0 < b) (_hx : x < b) (hy : y < b) (hz : z < b) :
    digits b (index b x y z) = ![x, y, z] := by
  have hd : index b x y z / b = x * b + y := by
    unfold index
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hz]
    omega
  have hz' : index b x y z % b = z := by
    simp only [index, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hz]
  have hx' : index b x y z / (b * b) = x := by
    rw [← Nat.div_div_eq_div_mul, hd]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hy]
    omega
  have hy' : (index b x y z / b) % b = y := by
    rw [hd]
    simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hy]
  funext k
  fin_cases k <;> simp [digits, hx', hy', hz']

theorem index_bound (b x y z : ℕ) (hx : x < b) (hy : y < b) (hz : z < b) :
    index b x y z < b * b * b := by
  have hxmul := Nat.mul_le_mul_right b (show x + 1 ≤ b by omega)
  have hxy : x * b + y < b * b := by
    rw [Nat.add_mul, Nat.one_mul] at hxmul
    omega
  have hxymul := Nat.mul_le_mul_right b (show x * b + y + 1 ≤ b * b by omega)
  rw [Nat.add_mul, Nat.one_mul] at hxymul
  unfold index
  omega

theorem digits_bound (m i : ℕ) (hi : i < count m) (k : Fin 3) : digits (base m) i k < base m := by
  have hb := base_positive m
  fin_cases k
  · change i / (base m * base m) < base m
    apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos hb hb)).2
    simpa only [count, Nat.mul_assoc] using hi
  · exact Nat.mod_lt _ hb
  · exact Nat.mod_lt _ hb

theorem point_injective (m : ℕ) : Function.Injective (point m) := by
  intro i j hij
  have hx := congrFun hij 0
  have hy := congrFun hij 1
  have hz := congrFun hij 2
  simp only [point, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hx hy hz
  have hdx : digits (base m) i 0 = digits (base m) j 0 := by omega
  have hdy : digits (base m) i 1 = digits (base m) j 1 := by omega
  have hdz : digits (base m) i 2 = digits (base m) j 2 := by omega
  rw [← digits_reconstruct (base m) i, ← digits_reconstruct (base m) j, hdx, hdy, hdz]

theorem octahedron_has_index {m : ℕ} {p : Site} (hp : InOctahedron m p) :
    ∃ i < count m, point m i = p.val := by
  let x := (p.val 0 + (2 * (m : ℤ) + 1)).toNat
  let y := (p.val 1 + 3).toNat
  let z := (p.val 2 + (2 * (m : ℤ) + 1)).toNat
  have hx0 := inOctahedron_coordinate_bound hp 0
  have hy0 := inOctahedron_coordinate_bound hp 1
  have hz0 := inOctahedron_coordinate_bound hp 2
  simp [octCentre, octRadius] at hx0 hy0 hz0
  have hx : x < base m := by dsimp [x, base]; omega
  have hy : y < base m := by dsimp [y, base]; omega
  have hz : z < base m := by dsimp [z, base]; omega
  refine ⟨index (base m) x y z, index_bound _ _ _ _ hx hy hz, ?_⟩
  have hd := digits_index (base m) x y z (base_positive m) hx hy hz
  unfold point
  rw [hd]
  funext k
  fin_cases k <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] <;> dsimp [x, y, z] <;> omega

noncomputable def baseComputable :
    TM2ComputableInPolyTime unaryFinEncodingNat unaryFinEncodingNat base :=
  add (mul (natConstant _ 4) (idComputableInPolyTime _)) (natConstant _ 3)

noncomputable def countComputable :
    TM2ComputableInPolyTime unaryFinEncodingNat unaryFinEncodingNat count :=
  mul (mul baseComputable baseComputable) baseComputable

noncomputable def inputMComputable :
    TM2ComputableInPolyTime Division.inputEncoding unaryFinEncodingNat (fun x : ℕ × ℕ => x.1) :=
  TM2PairProjections.fstComputable unaryFinEncodingNat unaryFinEncodingNat

noncomputable def inputIndexComputable :
    TM2ComputableInPolyTime Division.inputEncoding unaryFinEncodingNat (fun x : ℕ × ℕ => x.2) :=
  TM2PairProjections.sndComputable unaryFinEncodingNat unaryFinEncodingNat

noncomputable def inputBaseComputable :
    TM2ComputableInPolyTime Division.inputEncoding unaryFinEncodingNat (fun x : ℕ × ℕ => base x.1) :=
  compose (g := base) inputMComputable baseComputable

set_option maxHeartbeats 1200000 in
noncomputable def digitComputable : (k : Fin 3) →
    TM2ComputableInPolyTime Division.inputEncoding unaryFinEncodingNat
      (fun x : ℕ × ℕ => digits (base x.1) x.2 k)
  | ⟨0, _⟩ => by
    let h := compose (pairComputable inputIndexComputable (mul inputBaseComputable inputBaseComputable))
      Division.quotientComputable
    exact changeFunction h (fun x => rfl)
  | ⟨1, _⟩ => by
    let h := compose (pairComputable (compose (pairComputable inputIndexComputable inputBaseComputable)
      Division.quotientComputable) inputBaseComputable) Division.remainderComputable
    exact changeFunction h (fun x => rfl)
  | ⟨2, _⟩ => by
    let h := compose (pairComputable inputIndexComputable inputBaseComputable) Division.remainderComputable
    exact changeFunction h (fun x => rfl)
  | ⟨k + 3, hk⟩ => False.elim (by omega)

end ProteinFolding.Tetrahedral.ReductionTM2.Grid
