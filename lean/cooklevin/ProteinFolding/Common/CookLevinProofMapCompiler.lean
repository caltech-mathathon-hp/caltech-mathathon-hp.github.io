import ProteinFolding.Common.TM2ListMap
import ProteinFolding.Common.CookLevin

/-! An actual polynomial-time compiler for concatenated CNF fragments. The
shared record-loop machine calls each given child CNF machine, preserves its
parameter, concatenates the exact frozen CNF codes and cleans up all stacks.
The generic record-loop implementation is reused from Common/TM2ListMap.
-/

namespace ProteinFolding.SAT.CookLevinMapCompiler

open Computability Turing TM2ListMap

theorem cnfEncoding_append (φ ψ : CNF) :
    cnfEncoding.encode (φ ++ ψ) = cnfEncoding.encode φ ++ cnfEncoding.encode ψ := by
  simp only [cnfEncoding, encTerminated, List.flatMap_append]

theorem cnfEncoding_flatMap {A : Type*} (xs : List A) (f : A → CNF) :
    cnfEncoding.encode (xs.flatMap f) = xs.flatMap (fun x => cnfEncoding.encode (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.flatMap_cons, cnfEncoding_append, ih, List.flatMap_cons]

noncomputable def cnfWordComputable {X : Type} {ex : FinEncoding X} {f : X → CNF}
    (h : TM2ComputableInPolyTime ex cnfEncoding f) :
    TM2ComputableInPolyTime ex (wordEncoding Sym) (fun x => cnfEncoding.encode (f x)) where
  toTM2ComputableAux := h.toTM2ComputableAux
  time := h.time
  outputsFun x := h.outputsFun x

/-- Given actual polynomial child machines for individual CNF fragments,
compile their parameterized concatenation into an actual polynomial TM2. -/
noncomputable def parameterizedCNFCompiler {P A : Type} {ep : FinEncoding P} {ea : FinEncoding A}
    {f : P × A → CNF} (h : TM2ComputableInPolyTime (pairEncoding ep ea) cnfEncoding f) :
    TM2ComputableInPolyTime (pairEncoding ep (TM2ListMap.listEncoding ea)) cnfEncoding
      (fun z : P × List A => z.2.flatMap (fun a => f (z.1, a))) := by
  let hl := TM2ListMap.flatMapComputable (cnfWordComputable h)
  exact
    { toTM2ComputableAux := hl.toTM2ComputableAux
      time := hl.time
      outputsFun z := by
        have hz := hl.outputsFun z
        change TM2OutputsInTime hl.tm _
          (some ((cnfEncoding.encode (z.2.flatMap (fun a => f (z.1, a)))).map hl.outputAlphabet.symm)) _
        rw [cnfEncoding_flatMap]
        exact hz }

end ProteinFolding.SAT.CookLevinMapCompiler
