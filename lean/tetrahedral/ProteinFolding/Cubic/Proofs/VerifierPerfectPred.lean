import ProteinFolding.Cubic.Proofs.VerifierPerfectUnary

/-! A constant-time predecessor machine for the unary side witness. -/

namespace ProteinFolding.PerfectUnaryPredecessor

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
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m _ := .pop () (fun _ _ => ()) .halt

def singleCfg (label : Option Unit) (w : List Bool) : Cfg (fun _ : Unit => Bool) Unit Unit :=
  ⟨label, (), fun _ => w⟩

theorem unary_tail (n : ℕ) : (unaryEncodeNat n).tail = unaryEncodeNat (n - 1) := by
  cases n <;> rfl

def machine_outputs (n : ℕ) : TM2OutputsInTime machine (unaryEncodeNat n)
    (some (unaryEncodeNat (n - 1))) 1 := by
  have hi : initList machine (unaryEncodeNat n) = singleCfg (some ()) (unaryEncodeNat n) := by
    apply congrArg (fun S => (⟨some (), (), S⟩ : Cfg (fun _ : Unit => Bool) Unit Unit))
    funext k; cases k; rfl
  have ho : haltList machine (unaryEncodeNat (n - 1)) = singleCfg none (unaryEncodeNat (n - 1)) := by
    apply congrArg (fun S => (⟨none, (), S⟩ : Cfg (fun _ : Unit => Bool) Unit Unit))
    funext k; cases k; rfl
  refine ⟨⟨1, ?_⟩, le_rfl⟩
  change machine.step (initList machine (unaryEncodeNat n)) =
    some (haltList machine (unaryEncodeNat (n - 1)))
  rw [hi, ho]
  change some (⟨none, (), Function.update (fun _ : Unit => unaryEncodeNat n) ()
    (unaryEncodeNat n).tail⟩ : Cfg (fun _ : Unit => Bool) Unit Unit) = _
  apply congrArg (fun S => some (⟨none, (), S⟩ : Cfg (fun _ : Unit => Bool) Unit Unit))
  funext k
  cases k
  simpa using unary_tail n

noncomputable def predecessorComputable : TM2ComputableInPolyTime
    unaryFinEncodingNat unaryFinEncodingNat (fun n : ℕ => n - 1) where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 1
  outputsFun n := by
    simp only [Polynomial.eval_C]
    change TM2OutputsInTime machine (List.map id (unaryEncodeNat n))
      (some (List.map id (unaryEncodeNat (n - 1)))) 1
    simpa only [List.map_id] using machine_outputs n

end ProteinFolding.PerfectUnaryPredecessor
