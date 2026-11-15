import ProteinFolding.Cubic.Proofs.ThresholdCertificateUnarySide

/-! A total finite TM2 parser for the unary-side certificate frame. Missing
delimiters produce an explicit false flag, rather than an implicit promise. -/

namespace ProteinFolding.PerfectCertificateParser

open Computability Turing TM2

abbrev OutputSymbol := PairSymbol Bool (PairSymbol Bool Bool)
abbrev Result := Bool × (ℕ × List Bool)

def resultEncoding : FinEncoding Result :=
  pairEncoding finEncodingBoolBool (pairEncoding unaryFinEncodingNat (wordEncoding Bool))

def parseSide : List Bool → Result
  | [] => (false, (0, []))
  | false :: w => (true, (0, w))
  | true :: w => let p := parseSide w; (p.1, (p.2.1 + 1, p.2.2))

inductive Slot where
  | input | side | geometry | output
  deriving DecidableEq, Fintype

inductive Phase where
  | side | geometry | drainGeometry | separator | drainSide | finish
  deriving DecidableEq, Fintype

def Alphabet : Slot → Type
  | .output => OutputSymbol
  | _ => Bool

instance : Inhabited (Alphabet Slot.geometry) := inferInstanceAs (Inhabited Bool)
instance : Inhabited (Alphabet Slot.side) := inferInstanceAs (Inhabited Bool)

def contents (w side geometry : List Bool) (out : List OutputSymbol) :
    ∀ k, List (Alphabet k)
  | .input => w
  | .side => side
  | .geometry => geometry
  | .output => out

theorem update_input (w w' s g : List Bool) (out : List OutputSymbol) :
    Function.update (contents w s g out) .input w' = contents w' s g out := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_side (w s s' g : List Bool) (out : List OutputSymbol) :
    Function.update (contents w s g out) .side s' = contents w s' g out := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_geometry (w s g g' : List Bool) (out : List OutputSymbol) :
    Function.update (contents w s g out) .geometry g' = contents w s g' out := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_output (w s g : List Bool) (out out' : List OutputSymbol) :
    Function.update (contents w s g out) .output out' = contents w s g out' := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

def sideTag (b : Bool) : OutputSymbol := .right (.left b)
def geometryTag (b : Bool) : OutputSymbol := .right (.right b)

def program : Phase → Stmt Alphabet Phase (Bool × Option Bool)
  | .side => .pop .input (fun st x => (st.1, x))
      (.branch (fun st => st.2.isSome)
        (.branch (fun st => st.2.getD false)
          (.push .side (fun _ => true) (.goto (fun _ => .side)))
          (.load (fun st => (true, st.2)) (.goto (fun _ => .geometry))))
        (.goto (fun _ => .drainGeometry)))
  | .geometry => .pop .input (fun st x => (st.1, x))
      (.branch (fun st => st.2.isSome)
        (.push .geometry (fun st => st.2.getD false) (.goto (fun _ => .geometry)))
        (.goto (fun _ => .drainGeometry)))
  | .drainGeometry => TM2Transfer.transferStmt (Γ := Alphabet) (Λ := Phase) (σ := Bool)
      .geometry .output geometryTag .drainGeometry .separator
  | .separator => .push .output (fun _ => .right .sep) (.goto (fun _ => .drainSide))
  | .drainSide => TM2Transfer.transferStmt (Γ := Alphabet) (Λ := Phase) (σ := Bool)
      .side .output sideTag .drainSide .finish
  | .finish => .push .output (fun _ => .sep)
      (.push .output (fun st => .left st.1) (.load (fun _ => (false, none)) .halt))

def cfg (label : Phase) (found : Bool) (reg : Option Bool)
    (w s g : List Bool) (out : List OutputSymbol) : Cfg Alphabet Phase (Bool × Option Bool) :=
  ⟨some label, (found, reg), contents w s g out⟩

abbrev advance : Option (Cfg Alphabet Phase (Bool × Option Bool)) →
    Option (Cfg Alphabet Phase (Bool × Option Bool)) := fun c => c.bind (step program)

theorem geometry_step_cons (found : Bool) (reg : Option Bool) (a : Bool)
    (w s g : List Bool) (out : List OutputSymbol) :
    advance (some (cfg .geometry found reg (a :: w) s g out)) =
      some (cfg .geometry found (some a) w s (a :: g) out) := by
  simp [advance, cfg, program, step, stepAux, contents, update_input, update_geometry]

theorem geometry_step_nil (found : Bool) (reg : Option Bool) (s g : List Bool)
    (out : List OutputSymbol) :
    advance (some (cfg .geometry found reg [] s g out)) =
      some (cfg .drainGeometry found none [] s g out) := by
  simp [advance, cfg, program, step, stepAux, contents, update_input]

theorem geometry_run (found : Bool) (reg : Option Bool) (w s g : List Bool)
    (out : List OutputSymbol) :
    advance^[w.length + 1] (some (cfg .geometry found reg w s g out)) =
      some (cfg .drainGeometry found none [] s (w.reverse ++ g) out) := by
  induction w generalizing reg g with
  | nil => simpa using geometry_step_nil found reg s g out
  | cons a w ih =>
    rw [List.length_cons, Function.iterate_succ_apply, geometry_step_cons]
    simpa [List.reverse_cons, List.append_assoc] using ih (some a) (a :: g)

theorem side_step_true (reg : Option Bool) (w s g : List Bool) (out : List OutputSymbol) :
    advance (some (cfg .side false reg (true :: w) s g out)) =
      some (cfg .side false (some true) w (true :: s) g out) := by
  simp [advance, cfg, program, step, stepAux, contents, update_input, update_side]

theorem side_step_false (reg : Option Bool) (w s g : List Bool) (out : List OutputSymbol) :
    advance (some (cfg .side false reg (false :: w) s g out)) =
      some (cfg .geometry true (some false) w s g out) := by
  simp [advance, cfg, program, step, stepAux, contents, update_input]

theorem side_step_nil (reg : Option Bool) (s g : List Bool) (out : List OutputSymbol) :
    advance (some (cfg .side false reg [] s g out)) =
      some (cfg .drainGeometry false none [] s g out) := by
  simp [advance, cfg, program, step, stepAux, contents, update_input]

theorem side_run (reg : Option Bool) (w : List Bool) (n : ℕ) (out : List OutputSymbol) :
    advance^[w.length + 1] (some (cfg .side false reg w (unaryEncodeNat n) [] out)) =
      some (cfg .drainGeometry (parseSide w).1 none []
        (unaryEncodeNat (n + (parseSide w).2.1)) (parseSide w).2.2.reverse out) := by
  induction w generalizing reg n with
  | nil => simpa [parseSide] using side_step_nil reg (unaryEncodeNat n) [] out
  | cons a w ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    cases a with
    | false =>
      rw [side_step_false]
      simpa [parseSide] using geometry_run true (some false) w (unaryEncodeNat n) [] out
    | true =>
      rw [side_step_true]
      simpa [parseSide, unaryEncodeNat, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (some true) (n + 1)

theorem geometryTransferCfg (label : Phase) (found : Bool) (reg : Option Bool)
    (w s g : List Bool) (out : List OutputSymbol) :
    TM2Transfer.transferCfg (Γ := Alphabet) (Λ := Phase) .geometry .output
      label found reg (contents w s [] []) g out = cfg label found reg w s g out := by
  unfold TM2Transfer.transferCfg cfg
  congr 1
  funext k
  cases k <;> simp [TM2Transfer.setStacks, contents, Function.update_of_ne]

theorem sideTransferCfg (label : Phase) (found : Bool) (reg : Option Bool)
    (w s g : List Bool) (out : List OutputSymbol) :
    TM2Transfer.transferCfg (Γ := Alphabet) (Λ := Phase) .side .output
      label found reg (contents w [] g []) s out = cfg label found reg w s g out := by
  unfold TM2Transfer.transferCfg cfg
  congr 1
  funext k
  cases k <;> simp [TM2Transfer.setStacks, contents, Function.update_of_ne]

theorem drainGeometry_run (found : Bool) (reg : Option Bool) (w s g : List Bool)
    (out : List OutputSymbol) :
    advance^[g.length + 1] (some (cfg .drainGeometry found reg w s g out)) =
      some (cfg .separator found none w s [] ((g.map geometryTag).reverse ++ out)) := by
  have h := TM2Transfer.transfer_run (Γ := Alphabet) (Λ := Phase) (σ := Bool)
    .geometry .output (by decide) geometryTag .drainGeometry .separator program rfl
    found reg (contents w s [] []) g out
  simp only [geometryTransferCfg] at h
  exact h

theorem drainSide_run (found : Bool) (reg : Option Bool) (w s g : List Bool)
    (out : List OutputSymbol) :
    advance^[s.length + 1] (some (cfg .drainSide found reg w s g out)) =
      some (cfg .finish found none w [] g ((s.map sideTag).reverse ++ out)) := by
  have h := TM2Transfer.transfer_run (Γ := Alphabet) (Λ := Phase) (σ := Bool)
    .side .output (by decide) sideTag .drainSide .finish program rfl
    found reg (contents w [] g []) s out
  simp only [sideTransferCfg] at h
  exact h

theorem unary_reverse (n : ℕ) : (unaryEncodeNat n).reverse = unaryEncodeNat n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [unaryEncodeNat, List.reverse_cons, ih] using PerfectUnaryMultiplication.unary_slide n []

theorem resultEncoding_encode (found : Bool) (n : ℕ) (rest : List Bool) :
    resultEncoding.encode (found, (n, rest)) =
      .left found :: .sep :: ((unaryEncodeNat n).map sideTag ++ .right .sep :: rest.map geometryTag) := by
  simp [resultEncoding, pairEncoding, finEncodingBoolBool, encodeBool, unaryFinEncodingNat,
    wordEncoding, List.map_append, List.map_map, Function.comp_def]
  rfl

theorem separator_step (found : Bool) (reg : Option Bool) (w s g : List Bool)
    (out : List OutputSymbol) :
    advance (some (cfg .separator found reg w s g out)) =
      some (cfg .drainSide found reg w s g (.right .sep :: out)) := by
  simp [advance, cfg, program, step, stepAux, contents, update_output]

theorem finish_step (found : Bool) (reg : Option Bool) (w s g : List Bool)
    (out : List OutputSymbol) :
    advance (some (cfg .finish found reg w s g out)) =
      some ⟨none, (false, none), contents w s g (.left found :: .sep :: out)⟩ := by
  simp [advance, cfg, program, step, stepAux, contents, update_output]

theorem parseSide_length (w : List Bool) :
    w.length = (parseSide w).2.1 + (parseSide w).2.2.length +
      (if (parseSide w).1 then 1 else 0) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b <;> simp [parseSide] at *
    omega

theorem parseSide_size (w : List Bool) :
    (parseSide w).2.1 + (parseSide w).2.2.length ≤ w.length := by
  have h := parseSide_length w
  omega

theorem program_run (w : List Bool) :
    advance^[w.length + (parseSide w).2.1 + (parseSide w).2.2.length + 5]
      (some (cfg .side false none w [] [] [])) =
        some ⟨none, (false, none), contents [] [] [] (resultEncoding.encode (parseSide w))⟩ := by
  let p := parseSide w
  have hscan := side_run none w 0 []
  simp only [Nat.zero_add, unaryEncodeNat] at hscan
  change advance^[w.length + p.2.1 + p.2.2.length + 5]
      (some (cfg .side false none w [] [] [])) =
        some ⟨none, (false, none), contents [] [] [] (resultEncoding.encode p)⟩
  rw [show w.length + p.2.1 + p.2.2.length + 5 =
      (p.2.1 + p.2.2.length + 4) + (w.length + 1) by omega,
    Function.iterate_add_apply, hscan]
  rw [show p.2.1 + p.2.2.length + 4 = (p.2.1 + 3) + (p.2.2.reverse.length + 1) by simp; omega,
    Function.iterate_add_apply, drainGeometry_run]
  simp only [List.map_reverse, List.reverse_reverse, List.append_nil]
  rw [show p.2.1 + 3 = (p.2.1 + 2) + 1 by omega,
    Function.iterate_succ_apply, separator_step]
  rw [show p.2.1 + 2 = (p.2.1 + 1) + 1 by omega, Function.iterate_succ_apply']
  have hside := drainSide_run p.1 none [] (unaryEncodeNat p.2.1) []
    (.right .sep :: p.2.2.map geometryTag)
  simp only [PerfectUnaryMultiplication.unary_length] at hside
  rw [hside, finish_step]
  simp only [← List.map_reverse, unary_reverse]
  rw [← resultEncoding_encode]

def machine : FinTM2 where
  K := Slot
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Phase
  main := .side
  σ := Bool × Option Bool
  initialState := (false, none)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program

def machine_outputs (w : List Bool) : TM2OutputsInTime machine w
    (some (resultEncoding.encode (parseSide w))) (2 * w.length + 5) := by
  have hi : initList machine w = cfg .side false none w [] [] [] := by
    apply congrArg (fun S => (⟨some .side, (false, none), S⟩ : Cfg Alphabet Phase (Bool × Option Bool)))
    funext k; cases k <;> rfl
  have ho : haltList machine (resultEncoding.encode (parseSide w)) =
      (⟨none, (false, none), contents [] [] [] (resultEncoding.encode (parseSide w))⟩ :
        Cfg Alphabet Phase (Bool × Option Bool)) := by
    apply congrArg (fun S => (⟨none, (false, none), S⟩ : Cfg Alphabet Phase (Bool × Option Bool)))
    funext k; cases k <;> rfl
  refine ⟨⟨w.length + (parseSide w).2.1 + (parseSide w).2.2.length + 5, ?_⟩, ?_⟩
  · change advance^[_] (some (initList machine w)) = some (haltList machine _)
    rw [hi, ho]
    exact program_run w
  · change w.length + (parseSide w).2.1 + (parseSide w).2.2.length + 5 ≤ 2 * w.length + 5
    have h := parseSide_size w
    omega

/-- The total flagged parser, including malformed words, runs in `2*X+5`. -/
noncomputable def parserComputable : TM2ComputableInPolyTime
    (wordEncoding Bool) resultEncoding parseSide where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 5
  outputsFun w := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    change TM2OutputsInTime machine (List.map id w)
      (some (List.map id (resultEncoding.encode (parseSide w)))) (2 * w.length + 5)
    simpa only [List.map_id] using machine_outputs w

theorem parseSide_frame (n : ℕ) (w : List Bool) :
    parseSide (CubicCertificates.frameUnarySide n w) = (true, (n, w)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [CubicCertificates.frameUnarySide, unaryEncodeNat, parseSide] using
      (congrArg (fun p : Result => (p.1, (p.2.1 + 1, p.2.2))) ih)

/-- The total parser's success flag exactly represents the existing partial
frame decoder; failure never supplies an accepted certificate implicitly. -/
theorem splitUnarySide_eq_parseSide (w : List Bool) :
    CubicCertificates.splitUnarySide w =
      if (parseSide w).1 then some (parseSide w).2 else none := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | false => rfl
    | true =>
      cases hf : (parseSide w).1 <;>
        simp [CubicCertificates.splitUnarySide, parseSide, ih, hf]

theorem unarySideBitsAccepts_iff_parser (input : PerfectInput × List Bool) :
    CubicCertificates.UnarySideBitsAccepts input ↔
      (parseSide input.2).1 = true ∧
      (parseSide input.2).2.1 = input.1.2 ∧
      (parseSide input.2).2.1 ≤ input.1.1.length ∧
      CubicCertificates.ThresholdBitsAccepts (input.1, (parseSide input.2).2.2) := by
  unfold CubicCertificates.UnarySideBitsAccepts
  rw [splitUnarySide_eq_parseSide]
  cases (parseSide input.2).1 <;> simp

end ProteinFolding.PerfectCertificateParser
