import ProteinFolding.Tetrahedral.NearFieldPPPPairwiseFacts

/-! Any two valid O2 links with disjoint H endpoints have disjoint P-sites. -/

namespace ProteinFolding.Tetrahedral

private theorem facePPP_caps_pairs_ne (m : ℕ) (p p' : Site) (k i l k' i' l' : Fin 4)
    (hp : p ∈ octahedron m) (hp' : p' ∈ octahedron m)
    (hq : faceFourStep p k i l ∈ octahedron m) (hq' : faceFourStep p' k' i' l' ∈ octahedron m)
    (hout : step p k ∉ octahedron m ∧ step (step (step p k) i) l ∉ octahedron m)
    (hpp : p ≠ p') (hpq : p ≠ faceFourStep p' k' i' l')
    (hqp : faceFourStep p k i l ≠ p') (hqq : faceFourStep p k i l ≠ faceFourStep p' k' i' l') :
    (step p k ≠ step p' k') ∧ (step p k ≠ step (step (step p' k') i') l') ∧
    (step (step (step p k) i) l ≠ step p' k') ∧
    (step (step (step p k) i) l ≠ step (step (step p' k') i') l') := by
  have hqout : step (faceFourStep p k i l) k ∉ octahedron m := by
    rw [← facePPP_last_eq_endpoint_cap]
    exact hout.2
  refine ⟨dangling_caps_ne_of_owner_ne m p p' k k' hp hp' hout.1 hpp, ?_, ?_, ?_⟩
  · rw [facePPP_last_eq_endpoint_cap]
    exact dangling_caps_ne_of_owner_ne m p _ k k' hp hq' hout.1 hpq
  · rw [facePPP_last_eq_endpoint_cap]
    exact dangling_caps_ne_of_owner_ne m _ p' k k' hq hp' hqout hqp
  · rw [facePPP_last_eq_endpoint_cap p k i l, facePPP_last_eq_endpoint_cap p' k' i' l']
    exact dangling_caps_ne_of_owner_ne m _ _ k k' hq hq' hqout hqq

theorem facePPP_middles_ne_of_endpoints_disjoint (m : ℕ) (p p' : Site) (k i l k' i' l' : Fin 4)
    (hil : i ≠ l) (hik : i ≠ k) (hlk : l ≠ k)
    (hi'l' : i' ≠ l') (hi'k' : i' ≠ k') (hl'k' : l' ≠ k')
    (hface : OctBigFace m k p ∨ OctSmallFace m k p)
    (hface' : OctBigFace m k' p' ∨ OctSmallFace m k' p')
    (hq : faceFourStep p k i l ∈ octahedron m) (hq' : faceFourStep p' k' i' l' ∈ octahedron m)
    (hpp : p ≠ p') (hpq : p ≠ faceFourStep p' k' i' l')
    (hqp : faceFourStep p k i l ≠ p') (hqq : faceFourStep p k i l ≠ faceFourStep p' k' i' l') :
    step (step p k) i ≠ step (step p' k') i' := by
  intro hmid
  have hp := hface.elim (fun h => h.1) (fun h => h.1)
  have hp' := hface'.elim (fun h => h.1) (fun h => h.1)
  have hout := face_four_bond_internal_sites_outside m p k i l hik hlk hface
  have hout' := face_four_bond_internal_sites_outside m p' k' i' l' hi'k' hl'k' hface'
  obtain ⟨h00, h01, h10, h11⟩ := facePPP_caps_pairs_ne m p p' k i l k' i' l' hp hp' hq hq'
    ⟨hout.1, hout.2.2⟩ hpp hpq hqp hqq
  have ha : step (step (step p k) i) i = step p k := step_step _ _
  have ha' : step (step (step p k) i) i' = step p' k' := by rw [hmid]; exact step_step _ _
  have hc' : step (step (step p k) i) l' = step (step (step p' k') i') l' := by rw [hmid]
  have hii : i ≠ i' := by
    intro hd
    have he := congrArg (fun d => step (step (step p k) i) d) hd
    dsimp only at he
    rw [ha, ha'] at he
    exact h00 he
  have hil' : i ≠ l' := by
    intro hd
    have he := congrArg (fun d => step (step (step p k) i) d) hd
    dsimp only at he
    rw [ha, hc'] at he
    exact h01 he
  have hli : l ≠ i' := by
    intro hd
    have he := congrArg (fun d => step (step (step p k) i) d) hd
    dsimp only at he
    rw [ha'] at he
    exact h10 he
  have hll : l ≠ l' := by
    intro hd
    have he := congrArg (fun d => step (step (step p k) i) d) hd
    dsimp only at he
    rw [hc'] at he
    exact h11 he
  have hnot := facePPP_middle_normal_not_dangling m k i hik hface
  have hi'k : i' ≠ k := by
    intro hd
    have he : step (step (step p k) i) k = step p' k' := by
      calc
        _ = step (step (step p k) i) i' := congrArg (fun d => step (step (step p k) i) d) hd.symm
        _ = _ := ha'
    apply hnot
    rw [he]
    exact ⟨hout'.1, p', hp', step_adj _ _⟩
  have hl'k : l' ≠ k := by
    intro hd
    have he : step (step (step p k) i) k = step (step (step p' k') i') l' := by
      calc
        _ = step (step (step p k) i) l' := congrArg (fun d => step (step (step p k) i) d) hd.symm
        _ = _ := hc'
    apply hnot
    rw [he]
    exact ⟨hout'.2.2, faceFourStep p' k' i' l', hq', (step_adj _ _).symm⟩
  exact no_four_distinct_directions_avoiding k i l i' l' hil hii hil' hli hll hi'l' hik hlk hi'k hl'k

theorem facePPPFolds_disjoint_of_endpoints_disjoint (m : ℕ) (p p' : Site) (k i l k' i' l' : Fin 4)
    (hil : i ≠ l) (hik : i ≠ k) (hlk : l ≠ k)
    (hi'l' : i' ≠ l') (hi'k' : i' ≠ k') (hl'k' : l' ≠ k')
    (hface : OctBigFace m k p ∨ OctSmallFace m k p)
    (hface' : OctBigFace m k' p' ∨ OctSmallFace m k' p')
    (hq : faceFourStep p k i l ∈ octahedron m) (hq' : faceFourStep p' k' i' l' ∈ octahedron m)
    (hpp : p ≠ p') (hpq : p ≠ faceFourStep p' k' i' l')
    (hqp : faceFourStep p k i l ≠ p') (hqq : faceFourStep p k i l ≠ faceFourStep p' k' i' l')
    (r s : Fin 3) : (facePPPFold p k i l hil).pos r ≠ (facePPPFold p' k' i' l' hi'l').pos s := by
  have hp := hface.elim (fun h => h.1) (fun h => h.1)
  have hp' := hface'.elim (fun h => h.1) (fun h => h.1)
  have hout := face_four_bond_internal_sites_outside m p k i l hik hlk hface
  have hout' := face_four_bond_internal_sites_outside m p' k' i' l' hi'k' hl'k' hface'
  obtain ⟨h00, h01, h10, h11⟩ := facePPP_caps_pairs_ne m p p' k i l k' i' l' hp hp' hq hq'
    ⟨hout.1, hout.2.2⟩ hpp hpq hqp hqq
  have hA : IsDangling m (step p k) := ⟨hout.1, p, hp, step_adj _ _⟩
  have hC : IsDangling m (step (step (step p k) i) l) :=
    ⟨hout.2.2, faceFourStep p k i l, hq, (step_adj _ _).symm⟩
  have hA' : IsDangling m (step p' k') := ⟨hout'.1, p', hp', step_adj _ _⟩
  have hC' : IsDangling m (step (step (step p' k') i') l') :=
    ⟨hout'.2.2, faceFourStep p' k' i' l', hq', (step_adj _ _).symm⟩
  have hM := facePPP_middle_not_dangling m k i hik hface
  have hM' := facePPP_middle_not_dangling m k' i' hi'k' hface'
  fin_cases r <;> fin_cases s
  all_goals dsimp [facePPPFold, facePPPSite]
  · exact h00
  · intro heq; apply hM'; rw [← heq]; exact hA
  · exact h01
  · intro heq; apply hM; rw [heq]; exact hA'
  · exact facePPP_middles_ne_of_endpoints_disjoint m p p' k i l k' i' l' hil hik hlk hi'l' hi'k' hl'k'
      hface hface' hq hq' hpp hpq hqp hqq
  · intro heq; apply hM; rw [heq]; exact hC'
  · exact h10
  · intro heq; apply hM'; rw [← heq]; exact hC
  · exact h11

end ProteinFolding.Tetrahedral
