import ProteinFolding.Tetrahedral.FinitePathCoverEnds

/-! Translate the existing finite component folds into exact local path
neighbour descriptions needed by the deterministic index walker. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem neighbour_of_degree_le_one {u x w : V} (hd : G.degree u ≤ 1)
    (hx : G.Adj u x) (hw : G.Adj u w) : w = x := by
  have hc : (G.neighborFinset u).card ≤ 1 := by simpa only [G.card_neighborFinset_eq_degree] using hd
  exact Finset.card_le_one.mp hc w ((G.mem_neighborFinset u w).2 hw) x ((G.mem_neighborFinset u x).2 hx)

theorem neighbour_of_degree_le_two {u x y w : V} (hd : G.degree u ≤ 2)
    (hx : G.Adj u x) (hy : G.Adj u y) (hxy : x ≠ y) (hw : G.Adj u w) : w = x ∨ w = y := by
  have hs : ({x, y} : Finset V) ⊆ G.neighborFinset u := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact (G.mem_neighborFinset u v).2 hx
    · have he : v = y := Finset.mem_singleton.mp hv
      simpa only [he] using (G.mem_neighborFinset u y).2 hy
  have hc : ({x, y} : Finset V).card = 2 := by simp [hxy]
  have he : ({x, y} : Finset V) = G.neighborFinset u :=
    Finset.eq_of_subset_of_card_le hs (by
      rw [hc, G.card_neighborFinset_eq_degree]
      exact hd)
  have hmem := (G.mem_neighborFinset u w).2 hw
  rw [← he] at hmem
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem

theorem fold_neighbours_iff {L : ℕ} (hL : 2 ≤ L) (f : Fold G L)
    (hd : ∀ u, G.degree u ≤ 2)
    (hfirst : G.degree (f.pos ⟨0, by omega⟩) ≤ 1)
    (hlast : G.degree (f.pos ⟨L - 1, by omega⟩) ≤ 1)
    (i : Fin L) (w : V) :
    G.Adj (f.pos i) w ↔
      (∃ j : Fin L, j.val + 1 = i.val ∧ f.pos j = w) ∨
      (∃ j : Fin L, i.val + 1 = j.val ∧ f.pos j = w) := by
  constructor
  · intro hw
    by_cases hi0 : i.val = 0
    · let j : Fin L := ⟨1, by omega⟩
      have hij : G.Adj (f.pos i) (f.pos j) := f.consecutive i j (by dsimp [j]; omega)
      have hi : i = ⟨0, by omega⟩ := Fin.ext hi0
      have hdeg : G.degree (f.pos i) ≤ 1 := by rw [hi]; exact hfirst
      have he := neighbour_of_degree_le_one G hdeg hij hw
      exact Or.inr ⟨j, by dsimp [j]; omega, he.symm⟩
    · by_cases hilast : i.val + 1 = L
      · let j : Fin L := ⟨i.val - 1, by omega⟩
        have hij : G.Adj (f.pos i) (f.pos j) := (f.consecutive j i (by dsimp [j]; omega)).symm
        have hi : i = ⟨L - 1, by omega⟩ := by
          apply Fin.ext
          change i.val = L - 1
          omega
        have hdeg : G.degree (f.pos i) ≤ 1 := by rw [hi]; exact hlast
        have he := neighbour_of_degree_le_one G hdeg hij hw
        exact Or.inl ⟨j, by dsimp [j]; omega, he.symm⟩
      · let j : Fin L := ⟨i.val - 1, by omega⟩
        let k : Fin L := ⟨i.val + 1, by omega⟩
        have hij : G.Adj (f.pos i) (f.pos j) := (f.consecutive j i (by dsimp [j]; omega)).symm
        have hik : G.Adj (f.pos i) (f.pos k) := f.consecutive i k rfl
        have hjk : f.pos j ≠ f.pos k := by
          intro he
          have hev := congrArg Fin.val (f.injective_pos he)
          dsimp [j, k] at hev
          omega
        rcases neighbour_of_degree_le_two G (hd _) hij hik hjk hw with he | he
        · exact Or.inl ⟨j, by dsimp [j]; omega, he.symm⟩
        · exact Or.inr ⟨k, rfl, he.symm⟩
  · rintro (⟨j, hji, rfl⟩ | ⟨j, hij, rfl⟩)
    · exact (f.consecutive j i hji).symm
    · exact f.consecutive i j hij

end ProteinFolding.Tetrahedral.ReductionTM2
