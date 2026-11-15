import ProteinFolding.Tetrahedral.NearFieldFrameData
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange

/-! The Appendix C lists are actual injective lattice paths. -/

namespace ProteinFolding.Tetrahedral

theorem nearFrameLength_ge_five (kind : Fin 6) : 5 ≤ nearFrameLength kind := by revert kind; decide

theorem nearFramePoint_inA (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (i : Fin (nearFrameLength kind)) (hi : nearFrameIsA kind i.val) :
    InASublattice (nearFramePoint m q kind hq i).val := by
  have h := nearFrameCoordinates_colour m q kind hq i
  rw [if_pos hi] at h
  exact h

theorem nearFramePoint_inB (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (i : Fin (nearFrameLength kind)) (hi : ¬ nearFrameIsA kind i.val) :
    InBSublattice (nearFramePoint m q kind hq i).val := by
  have h := nearFrameCoordinates_colour m q kind hq i
  rw [if_neg hi] at h
  exact h

theorem nearFramePoint_step (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (i : Fin (nearFrameLength kind - 1)) :
    nearFramePoint m q kind hq ⟨i.val + 1, by have h := i.isLt; omega⟩ =
      step (nearFramePoint m q kind hq ⟨i.val, by have h := i.isLt; omega⟩)
        (nearFrameDirection kind i.val) := by
  by_cases hi : nearFrameIsA kind i.val
  · have hpA := nearFramePoint_inA m q kind hq ⟨i.val, by have h := i.isLt; omega⟩ hi
    apply Subtype.ext
    rw [step_val_of_A _ hpA]
    funext k
    rw [bondVector_eq_bondComponent]
    have h := nearFrameOffset_step kind i k
    rw [if_pos hi] at h
    change nearFrameReference m q kind k + nearFrameOffset kind (i.val + 1) k =
      nearFrameReference m q kind k + nearFrameOffset kind i.val k + _
    omega
  · have hpB := nearFramePoint_inB m q kind hq ⟨i.val, by have h := i.isLt; omega⟩ hi
    apply Subtype.ext
    rw [step_val_of_B _ hpB]
    funext k
    rw [bondVector_eq_bondComponent]
    have h := nearFrameOffset_step kind i k
    rw [if_neg hi] at h
    change nearFrameReference m q kind k + nearFrameOffset kind (i.val + 1) k =
      nearFrameReference m q kind k + nearFrameOffset kind i.val k - _
    omega

theorem nearFramePoint_adj (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (i : Fin (nearFrameLength kind - 1)) :
    tetrahedralLattice.Adj
      (nearFramePoint m q kind hq ⟨i.val, by have h := i.isLt; omega⟩)
      (nearFramePoint m q kind hq ⟨i.val + 1, by have h := i.isLt; omega⟩) := by
  rw [nearFramePoint_step]
  exact step_adj _ _

theorem nearFramePoint_injective (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1) :
    Function.Injective (nearFramePoint m q kind hq) := by
  intro i j heq
  apply nearFrameOffset_injective kind
  funext k
  change nearFrameOffset kind i.val k = nearFrameOffset kind j.val k
  have h := congrArg (fun p : Site => p.val k) heq
  change nearFrameReference m q kind k + nearFrameOffset kind i.val k =
    nearFrameReference m q kind k + nearFrameOffset kind j.val k at h
  omega

def nearFramePath (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1) : List Site :=
  List.ofFn (nearFramePoint m q kind hq)

def nearFramePList (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1) : List Site :=
  List.ofFn (fun i : Fin (nearFrameLength kind - 2) =>
    nearFramePoint m q kind hq ⟨i.val + 1, by have h := i.isLt; omega⟩)

theorem nearFramePath_length (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1) :
    (nearFramePath m q kind hq).length = nearFrameLength kind := List.length_ofFn

theorem nearFramePList_length (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1) :
    (nearFramePList m q kind hq).length = nearFrameLength kind - 2 := List.length_ofFn

theorem nearFramePath_nodup (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1) :
    (nearFramePath m q kind hq).Nodup := List.nodup_ofFn.mpr (nearFramePoint_injective m q kind hq)

theorem nearFramePList_nodup (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1) :
    (nearFramePList m q kind hq).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j heq
  have h := nearFramePoint_injective m q kind hq heq
  have hv := congrArg Fin.val h
  change i.val + 1 = j.val + 1 at hv
  exact Fin.ext (by omega)

theorem nearFramePath_isChain (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1) :
    (nearFramePath m q kind hq).IsChain tetrahedralLattice.Adj := by
  apply List.isChain_ofFn.mpr
  intro i hi
  exact nearFramePoint_adj m q kind hq ⟨i, by omega⟩

end ProteinFolding.Tetrahedral
