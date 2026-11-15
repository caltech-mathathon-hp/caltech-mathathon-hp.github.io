import ProteinFolding.Common.TM2Fanout

/-! Swapping encoded pair fields by actual duplication and symbol filtering.
The first copy supplies its right field, the second its left field; the outer
separator is retained. No independent-function pairing assumption is used. -/

namespace ProteinFolding.TM2PairSwap

open Computability Turing

variable {A B C D : Type}

def selectCross : PairSymbol (PairSymbol A B) (PairSymbol C D) → Option (PairSymbol B C)
  | .left (.right b) => some (.left b)
  | .sep => some .sep
  | .right (.left c) => some (.right c)
  | _ => none

theorem selectCross_word (u : List A) (v : List B) (x : List C) (y : List D) :
    List.filterMap selectCross
      (((u.map PairSymbol.left ++ PairSymbol.sep :: v.map PairSymbol.right).map PairSymbol.left) ++
        PairSymbol.sep :: (x.map PairSymbol.left ++ PairSymbol.sep :: y.map PairSymbol.right).map PairSymbol.right) =
      v.map PairSymbol.left ++ PairSymbol.sep :: x.map PairSymbol.right := by
  simp [List.map_append, List.filterMap_append, List.filterMap_map, Function.comp_def,
    selectCross, TM2PairProjections.discard_all]

noncomputable def crossSelectComputable {W X Y Z : Type}
    (ew : FinEncoding W) (ex : FinEncoding X) (ey : FinEncoding Y) (ez : FinEncoding Z) :
    TM2ComputableInPolyTime (pairEncoding (pairEncoding ew ex) (pairEncoding ey ez))
      (pairEncoding ex ey) (fun p => (p.1.2, p.2.1)) := by
  letI := ew.ΓFin
  letI := ex.ΓFin
  letI := ey.ΓFin
  letI := ez.ΓFin
  let ein := pairEncoding (pairEncoding ew ex) (pairEncoding ey ez)
  let eout := pairEncoding ex ey
  let h := TM2PairProjections.filterMapComputable ein.Γ eout.Γ selectCross
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun p => by
        have hw : (ein.encode p).filterMap selectCross = eout.encode (p.1.2, p.2.1) :=
          selectCross_word (ew.encode p.1.1) (ex.encode p.1.2) (ey.encode p.2.1) (ez.encode p.2.2)
        have hout := h.outputsFun (ein.encode p)
        change TM2OutputsInTime h.tm ((ein.encode p).map h.inputAlphabet.symm)
          (some (((ein.encode p).filterMap selectCross).map h.outputAlphabet.symm))
          (h.time.eval (ein.encode p).length) at hout
        rw [hw] at hout
        exact hout }

noncomputable def swapComputable {W X : Type} (ew : FinEncoding W) (ex : FinEncoding X) :
    TM2ComputableInPolyTime (pairEncoding ew ex) (pairEncoding ex ew)
      (fun p => (p.2, p.1)) :=
  TM2CompositionPoly.compose (TM2Fanout.diagonalComputable (pairEncoding ew ex))
    (crossSelectComputable ew ex ew ex)

end ProteinFolding.TM2PairSwap
