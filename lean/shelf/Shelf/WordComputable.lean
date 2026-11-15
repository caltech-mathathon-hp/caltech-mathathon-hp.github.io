import ProteinFolding.Cubic.Proofs.PackingWordComputableSource
import Shelf.Word

/-!
# A Turing machine for the string

"The string has polynomial length and can be written down in polynomial time"
(proof of Theorem 1 in the paper). Here this is a statement about Turing
machines: from an instance with numbers in unary, a machine writes the string
`S` and the side `n` of the cube (in binary, as the team's statement of the
folding problem wants it) in polynomial time.

The machine writes `machineWord J`, which is `shelfWord J` whenever every size
is positive. For an item of size `0` the two differ (the machine writes the
linker two letters shorter), and the reduction never meets such an item.

We write the dense runs as `H (PPH)^(r-1)` with `repeatWord`, and each item as
`P^(λ-2) (PPH)^a`, which is `P^λ D(a)` when `a ≥ 1`. The machine is assembled
from the team's combinators (`add`, `mul`, `concat`, `repeatSequence`,
`residuePower`) and the template machine that replaces each letter of a code
word for the sizes by one of two words.
-/

namespace ProteinFolding.Shelf

open ProteinFolding Computability Turing Residue List

/-- The string as the machine writes it. -/
def machineWord (J : Packing.Instance) : Sequence :=
  replicate (coreLength (side J)) H ++
  ([P, P] ++
  (([H] ++ CubicPacking.repeatWord [P, P, H] (9 * (J.bins * (J.capacity + 1)) + 16)) ++
  (replicate (linkerLength J) P ++
  (([H] ++ CubicPacking.repeatWord [P, P, H] (J.bins * (J.capacity + 1))) ++
  (replicate (side J) P ++
  (([H] ++ CubicPacking.repeatWord (replicate (J.capacity + 6) P ++ [H]) J.bins) ++
  (replicate (side J) P ++
  (([H] ++ CubicPacking.repeatWord [P, P, H] (J.bins * (J.capacity + 1))) ++
  ((J.sizes.flatMap fun a =>
      replicate (linkerLength J - 2) P ++ CubicPacking.repeatWord [P, P, H] a) ++
  [P])))))))))

/-- `repeatWord u r` is `r` copies of `u` written one after another. -/
theorem repeatWord_eq_flatten (u : Sequence) (r : ℕ) :
    CubicPacking.repeatWord u r = (replicate r u).flatten := by
  induction r with
  | zero => rfl
  | succ r ih => simp [CubicPacking.repeatWord, replicate_succ, ih]

/-- A dense run with at least one `H`, written with `repeatWord`. -/
theorem denseRun_succ (r : ℕ) :
    denseRun (r + 1) = [H] ++ CubicPacking.repeatWord [P, P, H] r := by
  simp [denseRun, repeatWord_eq_flatten]

/-- `P^λ D(a) = P^(λ-2) (PPH)^a` when `λ ≥ 2` and `a ≥ 1`. -/
theorem item_eq (l a : ℕ) (hl : 2 ≤ l) (ha : 0 < a) :
    replicate l P ++ denseRun a = replicate (l - 2) P ++ CubicPacking.repeatWord [P, P, H] a := by
  obtain ⟨a, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ c, l = c + 2 := ⟨l - 2, by omega⟩
  rw [denseRun_succ]
  simp [CubicPacking.repeatWord, replicate_add]

/-- When every size is positive, the machine writes the string `S` of Section 3. -/
theorem machineWord_eq {J : Packing.Instance} (h : ∀ a ∈ J.sizes, 0 < a) :
    machineWord J = shelfWord J := by
  have h9 : 9 * side J - 10 = 9 * (J.bins * (J.capacity + 1)) + 16 + 1 := by
    simp only [side]; omega
  have h2 : side J - 2 = J.bins * (J.capacity + 1) + 1 := by simp only [side]; omega
  have hl : 2 ≤ linkerLength J := by simp only [linkerLength, side]; omega
  have hitems : itemsWord J = J.sizes.flatMap fun a =>
      replicate (linkerLength J - 2) P ++ CubicPacking.repeatWord [P, P, H] a := by
    rw [itemsWord, ← List.flatMap_def]
    exact List.flatMap_congr fun a ha => item_eq _ _ hl (h a ha)
  simp only [machineWord, shelfWord, shelfPieces, separators, h9, h2, denseRun_succ, hitems,
    repeatWord_eq_flatten, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.nil_append, List.cons_append]

namespace Machine

open TM2CompositionPoly TM2ProductMap CubicPacking.WordGenerator

/-- `m (B + 1)` in unary. -/
noncomputable def binsTimesCapacity :
    TM2ComputableInPolyTime Packing.instanceEncoding unaryFinEncodingNat
      (fun J : Packing.Instance => J.bins * (J.capacity + 1)) :=
  mul Packing.binsComputable (add Packing.capacityComputable (natConstant _ 1))

/-- The side `n` of the cube in unary. -/
noncomputable def sideUnary :
    TM2ComputableInPolyTime Packing.instanceEncoding unaryFinEncodingNat side :=
  add binsTimesCapacity (natConstant _ 3)

/-- Each letter of the code of the sizes becomes one letter of the unary code of `k`
(the terminators) or nothing (the unary digits). -/
def lengthLetter : Bool → List Bool
  | true => []
  | false => [true]

theorem lengthLetter_items (xs : List ℕ) :
    (Packing.itemEncoding.encode xs).flatMap lengthLetter = unaryEncodeNat xs.length := by
  have hu (n : ℕ) : (unaryEncodeNat n).flatMap lengthLetter = [] := by
    induction n with
    | zero => rfl
    | succ n ih => simpa [unaryEncodeNat, lengthLetter] using ih
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [Packing.itemEncoding, SAT.encTerminated, List.flatMap_cons] at *
    simp [List.flatMap_append, hu, lengthLetter, ih, unaryEncodeNat]

/-- The number `k` of items in unary. -/
noncomputable def lengthUnary :
    TM2ComputableInPolyTime Packing.instanceEncoding unaryFinEncodingNat
      (fun J : Packing.Instance => J.sizes.length) := by
  apply Packing.ofCode (f := fun J : Packing.Instance => J.sizes.length)
  simpa only [Function.comp_def, unaryFinEncodingNat, lengthLetter_items] using
    compose (Packing.toCode Packing.sizesComputable)
      (TM2WordSubstitution.flatMapComputable lengthLetter 1 (by intro b; cases b <;> decide))

/-- The linker length `λ = 4 n + 2 k` in unary. -/
noncomputable def linkerUnary :
    TM2ComputableInPolyTime Packing.instanceEncoding unaryFinEncodingNat linkerLength :=
  add (mul (natConstant _ 4) sideUnary) (mul (natConstant _ 2) lengthUnary)

/-- The core length `N₀ = n³ + 16 - 12 n` in unary. -/
noncomputable def coreUnary :
    TM2ComputableInPolyTime Packing.instanceEncoding unaryFinEncodingNat
      (fun J => coreLength (side J)) :=
  compose (f := fun J => (side J ^ 3 + 16, 12 * side J)) (g := fun p : ℕ × ℕ => p.1 - p.2)
    (pairComputable
      (add (compose (f := side) (g := fun n : ℕ => n ^ 3) sideUnary
        PerfectVerifierArithmetic.unaryCubeComputable) (natConstant _ 16))
      (mul (natConstant _ 12) sideUnary))
    TM2UnarySubtraction.subtractionComputable

/-- A dense run `H (PPH)^r`, for `r` computed by a machine. -/
noncomputable def denseWord {g : Packing.Instance → ℕ}
    (hg : TM2ComputableInPolyTime Packing.instanceEncoding unaryFinEncodingNat g) :
    TM2ComputableInPolyTime Packing.instanceEncoding sequenceEncoding
      (fun J => [H] ++ CubicPacking.repeatWord [P, P, H] (g J)) :=
  concat (wordConstant _ [H]) (repeatSequence (wordConstant _ [P, P, H]) hg)

/-- A word `x^r` of one letter, for `r` computed by a machine. -/
noncomputable def powerWord (x : Residue) {g : Packing.Instance → ℕ}
    (hg : TM2ComputableInPolyTime Packing.instanceEncoding unaryFinEncodingNat g) :
    TM2ComputableInPolyTime Packing.instanceEncoding sequenceEncoding
      (fun J => replicate (g J) x) :=
  compose (f := g) (g := fun n => replicate n x) hg (residuePower x)

/-- A word `P^r`, for `r` computed by a machine. -/
noncomputable def pWord {g : Packing.Instance → ℕ}
    (hg : TM2ComputableInPolyTime Packing.instanceEncoding unaryFinEncodingNat g) :
    TM2ComputableInPolyTime Packing.instanceEncoding sequenceEncoding
      (fun J => replicate (g J) P) :=
  powerWord P hg

/-- The separators `H (P^(B+6) H)^m`. -/
noncomputable def separatorsWord :
    TM2ComputableInPolyTime Packing.instanceEncoding sequenceEncoding
      (fun J : Packing.Instance =>
        [H] ++ CubicPacking.repeatWord (replicate (J.capacity + 6) P ++ [H]) J.bins) :=
  concat (wordConstant _ [H])
    (repeatSequence
      (concat (pWord (add Packing.capacityComputable (natConstant _ 6))) (wordConstant _ [H]))
      Packing.binsComputable)

/-- The code word `false 1^{a₁} false 1^{a₂} … false 1^{a_k}` of the sizes. -/
def itemCode (J : Packing.Instance) : List Bool :=
  CubicPacking.WordGenerator.prefixItems J.sizes

theorem itemCode_eq (J : Packing.Instance) :
    itemCode J = (false :: Packing.itemEncoding.encode J.sizes).dropLast := by
  rw [← CubicPacking.WordGenerator.prefixItems_append_false, List.dropLast_concat]
  rfl

/-- The instance's own code of the sizes, as a word of booleans. -/
def sizesCode (J : Packing.Instance) : List Bool := Packing.itemEncoding.encode J.sizes

/-- The code word of the sizes: put `false` in front of the instance's code of the
sizes and drop its last letter. -/
noncomputable def itemCodeWord :
    TM2ComputableInPolyTime Packing.instanceEncoding (wordEncoding Bool) itemCode := by
  let h := compose
    (f := fun J : Packing.Instance => [false] ++ sizesCode J)
    (g := fun u : List Bool => u.dropLast)
    (compose (f := fun J : Packing.Instance => ([false], sizesCode J))
      (g := fun p : List Bool × List Bool => p.1 ++ p.2) (pairComputable
      (TM2Constants.constantComputable Packing.instanceEncoding (wordEncoding Bool) [false])
      (Packing.toCode Packing.sizesComputable))
      (TM2PairProjections.concatComputable Bool))
    (TM2WordInit.computable Bool)
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun J => by
        simpa only [Function.comp_apply, itemCode_eq, sizesCode, List.singleton_append] using h.outputsFun J }

theorem items_from_templates (u v : Sequence) (xs : List ℕ) :
    (CubicPacking.WordGenerator.prefixItems xs).flatMap (fun b => if b then u else v) =
      xs.flatMap fun a => v ++ CubicPacking.repeatWord u a := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [CubicPacking.WordGenerator.prefixItems, List.flatMap_cons, List.flatMap_append,
      Bool.false_eq_true, if_false, CubicPacking.WordGenerator.unary_flatMap_templates] at *
    rw [ih, List.append_assoc]

/-- The items `∏ᵢ P^(λ-2) (PPH)^{aᵢ}`: the letters of the code word of the sizes
are replaced by `PPH` and `P^(λ-2)`. -/
noncomputable def itemsMachine :
    TM2ComputableInPolyTime Packing.instanceEncoding sequenceEncoding
      (fun J : Packing.Instance => J.sizes.flatMap fun a =>
        replicate (linkerLength J - 2) P ++ CubicPacking.repeatWord [P, P, H] a) := by
  let h := compose
    (f := fun J => (([P, P, H], replicate (linkerLength J - 2) P), itemCode J))
    (g := TM2WordTemplates.substitute)
    (pairComputable (pairComputable (wordConstant _ [P, P, H])
      (pWord (compose (f := linkerLength) (g := fun n : ℕ => n - 2) linkerUnary subtractTwo)))
      itemCodeWord)
    (TM2WordTemplates.computable Residue)
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun J => by
        simpa only [Function.comp_apply, TM2WordTemplates.substitute, TM2WordTemplates.words,
          itemCode, items_from_templates] using h.outputsFun J }

/-- The whole string `machineWord J`. -/
noncomputable def wordMachine :
    TM2ComputableInPolyTime Packing.instanceEncoding sequenceEncoding machineWord :=
  concat (powerWord H coreUnary) <|
  concat (wordConstant _ [P, P]) <|
  concat (denseWord (add (mul (natConstant _ 9) binsTimesCapacity) (natConstant _ 16))) <|
  concat (pWord linkerUnary) <|
  concat (denseWord binsTimesCapacity) <|
  concat (pWord sideUnary) <|
  concat separatorsWord <|
  concat (pWord sideUnary) <|
  concat (denseWord binsTimesCapacity) <|
  concat itemsMachine (wordConstant _ [P])

/-- The side `n` of the cube in binary. -/
noncomputable def sideBinary :
    TM2ComputableInPolyTime Packing.instanceEncoding finEncodingNatBool side :=
  compose (f := side) (g := id) sideUnary TM2UnaryToBinary.unaryToBinaryComputable

end Machine

/-- A Turing machine writes the string and the side of the cube in polynomial
time. -/
noncomputable def shelfPairComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding perfectEncoding
      (fun J => (machineWord J, side J)) :=
  TM2ProductMap.pairComputable Machine.wordMachine Machine.sideBinary

end ProteinFolding.Shelf
