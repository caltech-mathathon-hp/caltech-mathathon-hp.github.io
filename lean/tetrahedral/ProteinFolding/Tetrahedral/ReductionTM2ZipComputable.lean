import ProteinFolding.Tetrahedral.ReductionTM2ZipRuns

namespace ProteinFolding.Tetrahedral.ReductionTM2.Zip

open Computability Turing TM2

def inputWord (us : List Sequence) (fs : List Bool) : List Symbol :=
  (bodyCode us).map .left ++ .sep :: fs.map .right
def halted (o : List Letter) : Cfg Alphabet Phase Reg := ⟨none, initial, contents [] [] [] [] o⟩
def steps (fs : List Bool) (us : List Sequence) : ℕ :=
  ((bodyCode us).length + 1) + (((bodyCode us).length + 1) +
    (((bodyCode us).length + us.length + 1) + (((fs.drop us.length).length + 1) +
      (((flaggedCode fs us).length + 1) + 1))))

theorem finish_step (o : List Letter) : Turing.TM2.step program (cfg .finish [] [] [] [] o) = some (halted o) := rfl

theorem program_run (fs : List Bool) (us : List Sequence) :
    run (steps fs us) (cfg .read (inputWord us fs) [] [] [] []) = some (halted (flaggedCode fs us)) := by
  have hread := read_run (bodyCode us) (fs.map .right) [] [] [] []
  simp only [List.append_nil] at hread
  rw [steps, inputWord, run_add hread]
  have hrestore := restore_body_run (fs.map .right) (bodyCode us).reverse [] [] []
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hrestore
  rw [run_add hrestore]
  have hzip := zip_run fs us [] []
  simp only [List.append_nil] at hzip
  rw [run_add hzip]
  have hdrain := drain_run ((fs.drop us.length).map .right) (flaggedCode fs us).reverse []
  simp only [List.length_map] at hdrain
  rw [run_add hdrain]
  have houtput := restore_output_run (flaggedCode fs us).reverse []
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at houtput
  rw [run_add houtput]
  exact finish_step _

theorem bodyCode_length (us : List Sequence) : us.length ≤ (bodyCode us).length := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    have hc : bodyCode (u :: us) = u.map some ++ none :: bodyCode us := rfl
    rw [hc, List.length_append, List.length_map, List.length_cons, List.length_cons]
    omega
theorem flaggedCode_length (fs : List Bool) (us : List Sequence) :
    (flaggedCode fs us).length = (bodyCode us).length + 2 * us.length := by
  induction us generalizing fs with
  | nil => rfl
  | cons u us ih =>
    have hc : bodyCode (u :: us) = u.map some ++ none :: bodyCode us := rfl
    have hf : flaggedCode fs (u :: us) = recordWord (fs[0]?.getD false) u ++ flaggedCode (fs.drop 1) us := by
      simp only [flaggedCode, zipFields, TM2ListMap.encodeFields, recordWord, List.append_assoc, List.singleton_append]
    rw [hc, hf, recordWord_explicit]
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil, ih]
    omega
theorem inputWord_length (us : List Sequence) (fs : List Bool) :
    (inputWord us fs).length = (bodyCode us).length + fs.length + 1 := by simp [inputWord]; omega
theorem steps_bound (fs : List Bool) (us : List Sequence) : steps fs us ≤ 8 * (inputWord us fs).length + 10 := by
  have hb := bodyCode_length us
  have hf : (fs.drop us.length).length ≤ fs.length := by rw [List.length_drop]; omega
  rw [steps, flaggedCode_length, inputWord_length]
  omega

def machine : FinTM2 where
  K := Slot
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Phase
  main := .read
  σ := Reg
  initialState := initial
  Γk₀Fin := inferInstanceAs (Fintype Symbol)
  m := program

def machine_outputs (us : List Sequence) (fs : List Bool) :
    TM2OutputsInTime machine (inputWord us fs) (some (flaggedCode fs us)) (8 * (inputWord us fs).length + 10) := by
  have hi : initList machine (inputWord us fs) = cfg .read (inputWord us fs) [] [] [] [] := by
    apply congrArg (fun S => (⟨some .read, initial, S⟩ : Cfg Alphabet Phase Reg))
    funext k; cases k <;> rfl
  have ho : haltList machine (flaggedCode fs us) = halted (flaggedCode fs us) := by
    apply congrArg (fun S => (⟨none, initial, S⟩ : Cfg Alphabet Phase Reg))
    funext k; cases k <;> rfl
  refine ⟨⟨steps fs us, ?_⟩, steps_bound fs us⟩
  change run (steps fs us) (initList machine _) = some (haltList machine _)
  rw [hi, ho]
  exact program_run fs us

def encoding := pairEncoding bodyListEncoding (wordEncoding Bool)

noncomputable def zipFieldsComputable :
    TM2ComputableInPolyTime encoding (TM2ListMap.listEncoding flaggedBodyEncoding)
      (fun x : List Sequence × List Bool => zipFields x.2 x.1) where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 8 * Polynomial.X + Polynomial.C 10
  outputsFun x := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    simpa only [Equiv.refl, List.map_id, encoding, pairEncoding, bodyListEncoding, TM2ListMap.listEncoding,
      wordEncoding, id_eq, inputWord, bodyCode, flaggedCode] using machine_outputs x.1 x.2

theorem flagBodiesAt_eq (fs : List Bool) (i : ℕ) (us : List Sequence) :
    flagBodiesAt fs i us = zipFields (fs.drop i) us := by
  induction us generalizing i with
  | nil => rfl
  | cons u us ih =>
    simp only [flagBodiesAt, zipFields, ih, List.getElem?_drop, Nat.add_zero, List.drop_drop]

noncomputable def zipComputable :
    TM2ComputableInPolyTime encoding (TM2ListMap.listEncoding flaggedBodyEncoding)
      (fun x : List Sequence × List Bool => flagBodiesAt x.2 0 x.1) :=
  changeFunction zipFieldsComputable (fun x => by simpa only [List.drop_zero] using (flagBodiesAt_eq x.2 0 x.1).symm)

end ProteinFolding.Tetrahedral.ReductionTM2.Zip
