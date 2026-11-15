import ProteinFolding.Tetrahedral.ReductionTM2Zip

namespace ProteinFolding.Tetrahedral.ReductionTM2.Zip

open Computability Turing TM2

theorem read_cons_step (a : Token) (raw : List Symbol) (buf body : List Token) (rev out : List Letter) :
    Turing.TM2.step program (cfg .read (.left a :: raw) buf body rev out) =
      some (cfg .read raw (a :: buf) body rev out) := by
  simp [program, cfg, initial, contents, Turing.TM2.step, stepAux, readBody, update_input, update_bodyBuffer]
theorem read_sep_step (raw : List Symbol) (buf body : List Token) (rev out : List Letter) :
    Turing.TM2.step program (cfg .read (.sep :: raw) buf body rev out) =
      some (cfg .restoreBodies raw buf body rev out) := by
  simp [program, cfg, initial, contents, Turing.TM2.step, stepAux, readBody, update_input]
theorem read_run (u : List Token) (raw : List Symbol) (buf body : List Token) (rev out : List Letter) :
    run (u.length + 1) (cfg .read (u.map .left ++ .sep :: raw) buf body rev out) =
      some (cfg .restoreBodies raw (u.reverse ++ buf) body rev out) := by
  induction u generalizing buf with
  | nil => exact read_sep_step raw buf body rev out
  | cons a u ih =>
    rw [List.length_cons, List.map_cons, List.cons_append, run_step (read_cons_step a _ buf body rev out)]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih (a :: buf)

theorem restore_body_cons_step (a : Token) (raw : List Symbol) (buf body : List Token) (rev out : List Letter) :
    Turing.TM2.step program (cfg .restoreBodies raw (a :: buf) body rev out) =
      some (cfg .restoreBodies raw buf (a :: body) rev out) := by
  simp [program, cfg, initial, contents, Turing.TM2.step, stepAux, update_bodyBuffer, update_bodies]
theorem restore_body_nil_step (raw : List Symbol) (body : List Token) (rev out : List Letter) :
    Turing.TM2.step program (cfg .restoreBodies raw [] body rev out) = some (cfg .start raw [] body rev out) := by
  simp [program, cfg, initial, contents, Turing.TM2.step, stepAux, update_bodyBuffer]
theorem restore_body_run (raw : List Symbol) (buf body : List Token) (rev out : List Letter) :
    run (buf.length + 1) (cfg .restoreBodies raw buf body rev out) =
      some (cfg .start raw [] (buf.reverse ++ body) rev out) := by
  induction buf generalizing body with
  | nil => exact restore_body_nil_step raw body rev out
  | cons a buf ih =>
    rw [List.length_cons, run_step (restore_body_cons_step a raw buf body rev out)]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih (a :: body)

theorem start_cons_step (fs : List Bool) (a : Token) (body : List Token) (rev out : List Letter) :
    Turing.TM2.step program (cfg .start (fs.map .right) [] (a :: body) rev out) =
      some (cfg .body ((fs.drop 1).map .right) [] (a :: body)
        (some .sep :: some (.left (fs[0]?.getD false)) :: rev) out) := by
  cases fs <;> simp [program, cfg, initial, contents, Turing.TM2.step, stepAux, readFlag,
    update_input, update_outputBuffer]
theorem start_nil_step (raw : List Symbol) (rev out : List Letter) :
    Turing.TM2.step program (cfg .start raw [] [] rev out) = some (cfg .drain raw [] [] rev out) := by
  simp [program, cfg, initial, contents, Turing.TM2.step, stepAux]
theorem body_cons_step (r : Residue) (raw : List Symbol) (body : List Token) (rev out : List Letter) :
    Turing.TM2.step program (cfg .body raw [] (some r :: body) rev out) =
      some (cfg .body raw [] body (some (.right r) :: rev) out) := by
  simp [program, cfg, initial, contents, Turing.TM2.step, stepAux, update_bodies, update_outputBuffer]
theorem body_end_step (raw : List Symbol) (body : List Token) (rev out : List Letter) :
    Turing.TM2.step program (cfg .body raw [] (none :: body) rev out) =
      some (cfg .start raw [] body (none :: rev) out) := by
  simp [program, cfg, initial, contents, Turing.TM2.step, stepAux, update_bodies, update_outputBuffer]
theorem body_run (u : Sequence) (raw : List Symbol) (body : List Token) (rev out : List Letter) :
    run (u.length + 1) (cfg .body raw [] (u.map some ++ none :: body) rev out) =
      some (cfg .start raw [] body (none :: (u.reverse.map (fun r => some (.right r)) ++ rev)) out) := by
  induction u generalizing rev with
  | nil => exact body_end_step raw body rev out
  | cons a u ih =>
    rw [List.length_cons, List.map_cons, List.cons_append, run_step (body_cons_step a raw _ rev out)]
    simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.singleton_append] using ih (some (.right a) :: rev)

def recordWord (b : Bool) (u : Sequence) : List Letter := (flaggedBodyEncoding.encode (b, u)).map some ++ [none]
theorem recordWord_explicit (b : Bool) (u : Sequence) :
    recordWord b u = some (.left b) :: some .sep :: (u.map (fun r => some (.right r)) ++ [none]) := by
  simp [recordWord, flaggedBodyEncoding, pairEncoding, finEncodingBoolBool, encodeBool,
    sequenceEncoding, wordEncoding, List.map_map, Function.comp_def]
theorem recordWord_reverse (b : Bool) (u : Sequence) :
    (recordWord b u).reverse = none :: (u.reverse.map (fun r => some (.right r)) ++ [some .sep, some (.left b)]) := by
  rw [recordWord_explicit]
  simp [List.reverse_cons, List.reverse_append, List.map_reverse, List.append_assoc]

def bodyCode (us : List Sequence) : List Token := TM2ListMap.encodeFields sequenceEncoding us
def flaggedCode (fs : List Bool) (us : List Sequence) : List Letter :=
  TM2ListMap.encodeFields flaggedBodyEncoding (zipFields fs us)

theorem zip_run (fs : List Bool) (us : List Sequence) (rev out : List Letter) :
    run ((bodyCode us).length + us.length + 1) (cfg .start (fs.map .right) [] (bodyCode us) rev out) =
      some (cfg .drain ((fs.drop us.length).map .right) [] [] ((flaggedCode fs us).reverse ++ rev) out) := by
  induction us generalizing fs rev with
  | nil => simpa only [bodyCode, TM2ListMap.encodeFields, List.length_nil, Nat.zero_add, List.drop_zero,
      flaggedCode, zipFields, List.reverse_nil, List.nil_append] using start_nil_step (fs.map .right) rev out
  | cons u us ih =>
    have hc : bodyCode (u :: us) = u.map some ++ none :: bodyCode us := rfl
    rw [hc, List.length_append, List.length_map, List.length_cons]
    simp only [List.length_cons]
    have heq : u.length + ((bodyCode us).length + 1) + (us.length + 1) + 1 =
        ((u.length + 1) + ((bodyCode us).length + us.length + 1)) + 1 := by omega
    rw [heq]
    have hstart : Turing.TM2.step program (cfg .start (fs.map .right) [] (u.map some ++ none :: bodyCode us) rev out) =
        some (cfg .body ((fs.drop 1).map .right) [] (u.map some ++ none :: bodyCode us)
          (some .sep :: some (.left (fs[0]?.getD false)) :: rev) out) := by
      cases u <;> exact start_cons_step fs _ _ rev out
    rw [run_step hstart]
    have hb := body_run u ((fs.drop 1).map .right) (bodyCode us)
      (some .sep :: some (.left (fs[0]?.getD false)) :: rev) out
    rw [run_add hb]
    have hr := ih (fs.drop 1) ((recordWord (fs[0]?.getD false) u).reverse ++ rev)
    have hrev : none :: (u.reverse.map (fun r => some (.right r)) ++
        some .sep :: some (.left (fs[0]?.getD false)) :: rev) =
        (recordWord (fs[0]?.getD false) u).reverse ++ rev := by rw [recordWord_reverse]; simp [List.append_assoc]
    rw [hrev]
    have hcode : flaggedCode fs (u :: us) = recordWord (fs[0]?.getD false) u ++ flaggedCode (fs.drop 1) us := by
      simp only [flaggedCode, zipFields, TM2ListMap.encodeFields, recordWord, List.append_assoc, List.singleton_append]
    rw [hcode, List.reverse_append]
    simpa only [List.drop_drop, Nat.add_comm 1 us.length, List.append_assoc] using hr

theorem drain_run (raw : List Symbol) (rev out : List Letter) :
    run (raw.length + 1) (cfg .drain raw [] [] rev out) = some (cfg .restoreOutput [] [] [] rev out) := by
  induction raw with
  | nil => simp [run, cfg, program, initial, contents, Turing.TM2.step, stepAux, update_input]
  | cons a raw ih =>
    have h : Turing.TM2.step program (cfg .drain (a :: raw) [] [] rev out) = some (cfg .drain raw [] [] rev out) := by
      simp [cfg, program, initial, contents, Turing.TM2.step, stepAux, update_input]
    rw [List.length_cons, run_step h]
    exact ih
theorem restore_output_run (rev out : List Letter) :
    run (rev.length + 1) (cfg .restoreOutput [] [] [] rev out) = some (cfg .finish [] [] [] [] (rev.reverse ++ out)) := by
  induction rev generalizing out with
  | nil => simp [run, cfg, program, initial, contents, Turing.TM2.step, stepAux, update_outputBuffer]
  | cons a rev ih =>
    have h : Turing.TM2.step program (cfg .restoreOutput [] [] [] (a :: rev) out) =
        some (cfg .restoreOutput [] [] [] rev (a :: out)) := by
      simp [cfg, program, initial, contents, Turing.TM2.step, stepAux, update_outputBuffer, update_output]
    rw [List.length_cons, run_step h]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih (a :: out)

end ProteinFolding.Tetrahedral.ReductionTM2.Zip
