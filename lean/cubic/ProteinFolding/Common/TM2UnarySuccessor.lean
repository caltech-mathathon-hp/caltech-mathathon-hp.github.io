import ProteinFolding.Common.Complexity

/-! One-step successor on the existing unary natural encoding. The input and
output stack are the same, so prepending true already gives the canonical
output and requires no auxiliary stack. -/

namespace ProteinFolding.TM2UnarySuccessor

open Computability Turing TM2

def machine : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  Γk₀Fin := inferInstance
  m _ := .push () (fun _ => true) .halt

def singleCfg (label : Option Unit) (w : List Bool) : Cfg (fun _ : Unit => Bool) Unit Unit :=
  ⟨label, (), fun _ => w⟩

def machine_outputs (n : ℕ) :
    TM2OutputsInTime machine (unaryEncodeNat n) (some (unaryEncodeNat (n + 1))) 1 := by
  have hi : initList machine (unaryEncodeNat n) = singleCfg (some ()) (unaryEncodeNat n) := by
    apply congrArg (fun S => (⟨some (), (), S⟩ : Cfg (fun _ : Unit => Bool) Unit Unit))
    funext k; cases k; rfl
  have ho : haltList machine (unaryEncodeNat (n + 1)) = singleCfg none (unaryEncodeNat (n + 1)) := by
    apply congrArg (fun S => (⟨none, (), S⟩ : Cfg (fun _ : Unit => Bool) Unit Unit))
    funext k; cases k; rfl
  refine ⟨⟨1, ?_⟩, le_rfl⟩
  change machine.step (initList machine (unaryEncodeNat n)) = some (haltList machine (unaryEncodeNat (n + 1)))
  rw [hi, ho]
  change some (⟨none, (), Function.update (fun _ : Unit => unaryEncodeNat n) ()
    (true :: unaryEncodeNat n)⟩ : Cfg (fun _ : Unit => Bool) Unit Unit) = _
  apply congrArg (fun S => some (⟨none, (), S⟩ : Cfg (fun _ : Unit => Bool) Unit Unit))
  funext k
  cases k
  rfl

noncomputable def successorComputable :
    TM2ComputableInPolyTime unaryFinEncodingNat unaryFinEncodingNat (fun n => n + 1) where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 1
  outputsFun n := by
    simpa only [Polynomial.eval_C, Equiv.refl, List.map_id, unaryFinEncodingNat] using machine_outputs n

end ProteinFolding.TM2UnarySuccessor
