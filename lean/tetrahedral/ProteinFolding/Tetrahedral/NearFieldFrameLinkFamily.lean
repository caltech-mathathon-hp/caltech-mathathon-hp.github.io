import ProteinFolding.Tetrahedral.NearFieldFrameFolds
import ProteinFolding.Tetrahedral.ConstructionParameters

/-! A finite, source-only index of every actual Appendix C frame P-link. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

abbrev FrameLinkIndex (p : ConstructionParameters) := Fin 4 ⊕ (Bool × Fin (p.bins + 1))

def frameLinkKind {p : ConstructionParameters} : FrameLinkIndex p → Fin 6
  | .inl c => if c = 0 then 0 else if c = 1 then 2 else if c = 2 then 3 else 5
  | .inr (false, _) => 1
  | .inr (true, _) => 4

def frameLinkParameter {p : ConstructionParameters} : FrameLinkIndex p → ℕ
  | .inl _ => 5
  | .inr (false, t) => 6 * t.val + 5
  | .inr (true, t) => 10 * t.val + 5

theorem frameLinkParameter_odd (p : ConstructionParameters) (i : FrameLinkIndex p) :
    frameLinkParameter i % 2 = 1 := by
  rcases i with c | ⟨b, t⟩
  · exact (by decide : (5 : ℕ) % 2 = 1)
  · cases b <;> dsimp [frameLinkParameter] <;> omega

theorem frameLinkParameter_ge (p : ConstructionParameters) (i : FrameLinkIndex p) :
    5 ≤ frameLinkParameter i := by
  rcases i with c | ⟨b, t⟩
  · exact (by decide : (5 : ℕ) ≤ 5)
  · cases b <;> dsimp [frameLinkParameter] <;> omega

theorem frameLinkParameter_room (p : ConstructionParameters) (i : FrameLinkIndex p) :
    (frameLinkParameter i : ℤ) + 10 ≤ octRadius p.side := by
  have hm := p.side_ge
  have hfamily := p.family_side_bound
  rcases i with c | ⟨b, t⟩
  · dsimp [frameLinkParameter, octRadius]
    omega
  · have ht := t.isLt
    cases b <;> dsimp [frameLinkParameter, octRadius] <;> omega

theorem frameLink_entry_residue (p : ConstructionParameters) (i : FrameLinkIndex p)
    (hi : frameLinkKind i = 1) : frameLinkParameter i % 6 = 5 := by
  rcases i with c | ⟨b, t⟩
  · fin_cases c <;>
      (have hv := congrArg Fin.val hi
       dsimp [frameLinkKind] at hv
       omega)
  · cases b
    · dsimp [frameLinkParameter]
      omega
    · have hv := congrArg Fin.val hi
      dsimp [frameLinkKind] at hv
      omega

theorem frameLink_exit_residue (p : ConstructionParameters) (i : FrameLinkIndex p)
    (hi : frameLinkKind i = 4) : frameLinkParameter i % 10 = 5 := by
  rcases i with c | ⟨b, t⟩
  · fin_cases c <;>
      (have hv := congrArg Fin.val hi
       dsimp [frameLinkKind] at hv
       omega)
  · cases b
    · have hv := congrArg Fin.val hi
      dsimp [frameLinkKind] at hv
      omega
    · dsimp [frameLinkParameter]
      omega

theorem frameLink_routes_separated (p : ConstructionParameters) (i j : FrameLinkIndex p) (hne : i ≠ j) :
    NearFrameRoutesSeparated (frameLinkKind i) (frameLinkParameter i) (frameLinkKind j) (frameLinkParameter j) := by
  rcases i with c | ⟨b, t⟩ <;> rcases j with d | ⟨e, u⟩
  · apply Or.inl
    intro heq
    apply hne
    congr 1
    fin_cases c <;> fin_cases d <;> dsimp [frameLinkKind] at heq <;> simp_all
  · apply Or.inl
    fin_cases c <;> cases e <;> dsimp [frameLinkKind] <;> decide
  · apply Or.inl
    cases b <;> fin_cases d <;> dsimp [frameLinkKind] <;> decide
  · cases b <;> cases e
    · have hvals : t.val ≠ u.val := by
        intro heq
        apply hne
        apply congrArg Sum.inr
        exact Prod.ext rfl (Fin.ext heq)
      apply Or.inr
      apply Or.inl
      refine ⟨rfl, rfl, ?_⟩
      dsimp [frameLinkParameter]
      omega
    · exact Or.inl (by dsimp [frameLinkKind]; decide)
    · exact Or.inl (by dsimp [frameLinkKind]; decide)
    · have hvals : t.val ≠ u.val := by
        intro heq
        apply hne
        apply congrArg Sum.inr
        exact Prod.ext rfl (Fin.ext heq)
      apply Or.inr
      apply Or.inr
      refine ⟨rfl, rfl, ?_⟩
      dsimp [frameLinkParameter]
      omega

def frameLinkFold (p : ConstructionParameters) (i : FrameLinkIndex p) :
    Fold tetrahedralLattice (nearFrameLength (frameLinkKind i) - 2) :=
  framePFold p.side (frameLinkParameter i) (frameLinkKind i) (frameLinkParameter_odd p i)

theorem frameLinkFolds_disjoint (p : ConstructionParameters) (i j : FrameLinkIndex p) (hne : i ≠ j)
    (r : Fin (nearFrameLength (frameLinkKind i) - 2)) (s : Fin (nearFrameLength (frameLinkKind j) - 2)) :
    (frameLinkFold p i).pos r ≠ (frameLinkFold p j).pos s := by
  exact nearFramePoints_ne_of_routes_separated p.side (frameLinkParameter i) (frameLinkParameter j)
    (frameLinkKind i) (frameLinkKind j) (frameLinkParameter_odd p i) (frameLinkParameter_odd p j)
    (frameLinkParameter_ge p i) (frameLinkParameter_ge p j) (frameLinkParameter_room p i) (frameLinkParameter_room p j)
    (frameLink_routes_separated p i j hne)
    ⟨r.val + 1, by have h := r.isLt; omega⟩ ⟨s.val + 1, by have h := s.isLt; omega⟩
    (by change 0 < r.val + 1; omega)
    (by change r.val + 1 + 1 < nearFrameLength (frameLinkKind i); have h := r.isLt; omega)
    (by change 0 < s.val + 1; omega)
    (by change s.val + 1 + 1 < nearFrameLength (frameLinkKind j); have h := s.isLt; omega)

theorem frameLinkFold_mem_skin_one (p : ConstructionParameters) (i : FrameLinkIndex p)
    (r : Fin (nearFrameLength (frameLinkKind i) - 2)) : (frameLinkFold p i).pos r ∈ skin p.side 1 :=
  framePFold_mem_skin_one _ _ _ _ (frameLinkParameter_ge p i) (frameLinkParameter_room p i) r

end ProteinFolding.Tetrahedral.NearField
