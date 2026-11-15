import ProteinFolding.Tetrahedral.FrameForcingActual
import ProteinFolding.Tetrahedral.OctahedralP3LinksHelpers

/-! A three-P frame link uses the same dangling direction at both ends. -/

namespace ProteinFolding.Tetrahedral

theorem OctWordPath.P3_caps_direction {m : ℕ} {word : Sequence} (P : OctWordPath m word)
    (a : ℕ) (hlen : a + 4 < word.length)
    (hstart : word[a]? = some .H) (hend : word[a + 4]? = some .H)
    (hP : ∀ r, 0 < r → r < 4 → word[a + r]? = some .P) :
    ∃ d : Fin 4, P.site (a + 1) = step (P.site a) d ∧
      P.site (a + 3) = step (P.site (a + 4)) d := by
  have h0 := P.adjacent a (by omega)
  have h1 : tetrahedralLattice.Adj (P.site (a + 1)) (P.site (a + 2)) := by
    simpa only [Nat.add_assoc] using P.adjacent (a + 1) (by omega)
  have h2 : tetrahedralLattice.Adj (P.site (a + 2)) (P.site (a + 3)) := by
    simpa only [Nat.add_assoc] using P.adjacent (a + 2) (by omega)
  have h3 : tetrahedralLattice.Adj (P.site (a + 3)) (P.site (a + 4)) := by
    simpa only [Nat.add_assoc] using P.adjacent (a + 3) (by omega)
  obtain ⟨k, hk⟩ := (adj_iff_exists_step _ _).mp h0
  obtain ⟨i, hi⟩ := (adj_iff_exists_step _ _).mp h1
  obtain ⟨l, hl⟩ := (adj_iff_exists_step _ _).mp h2
  obtain ⟨n, hn⟩ := (adj_iff_exists_step _ _).mp h3
  have hp := P.H_mem a (by omega) hstart
  have hout : step (P.site a) k ∉ octahedron m := by
    rw [hk]
    exact P.P_out (a + 1) (by omega) (hP 1 (by decide) (by decide))
  have he : step (step (step (step (P.site a) k) i) l) n ∈ octahedron m := by
    rw [hk, hi, hl, hn]
    exact P.H_mem (a + 4) hlen hend
  have hb0 : step (step (P.site a) k) i ≠ P.site a := by
    rw [hk, hi]
    intro heq
    have h := P.injective (a + 2) (by omega) a (by omega) heq
    omega
  have hb1 : step (step (step (P.site a) k) i) l ≠ step (P.site a) k := by
    rw [hk, hi, hl]
    intro heq
    have h := P.injective (a + 3) (by omega) (a + 1) (by omega) heq
    omega
  have hnk := (exterior_four_bond_directions m (P.site a) k i l n hp hout he hb0 hb1).1
  subst n
  refine ⟨k, hk.symm, ?_⟩
  have h := congrArg (fun q => step q k) hn
  simpa only [step_step] using h

theorem inner_A_edge_dangling_direction (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (n : ℕ) (hnlo : 0 < n) (hnhi : n < m - 1) (d : Fin 4)
    (hout : step (octEdgeZigzag m F (2 * n)) d ∉ octahedron m) : d = F.k := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨hpA, hk, hj, ha, hb⟩ := octEdgeZigzag_even hm1 F n
  have hp := (octEdgeZigzag_even_mem hm1 F (by omega : n < m)).1.1
  have hface := (step_not_mem_octahedron_A m hpA hp d).mp hout
  rcases F.index_cases d with hd | hd | hd | hd
  · exact hd
  · rw [hd] at hface
    dsimp [octRadius] at hface hj
    omega
  · rw [hd] at hface
    dsimp [octRadius] at hface ha
    omega
  · rw [hd] at hface
    dsimp [octRadius] at hface hb
    omega

theorem sum_map_take_succ {α : Type*} (f : α → ℕ) (xs : List α) (j : ℕ) (hj : j < xs.length) :
    ((xs.take (j + 1)).map f).sum = ((xs.take j).map f).sum + f xs[j] := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero => simp
    | succ j =>
      have hj' : j < xs.length := by simp only [List.length_cons] at hj; omega
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ]
      rw [ih j hj']
      omega

end ProteinFolding.Tetrahedral
