import Shelf.LayoutPlain

/-!
# Consecutive sites of the fold are adjacent

Part (b) of Theorem 16: each piece of Table 1 is a path, and the last site of a
piece is next to the first site of the following one.
-/

namespace ProteinFolding.Shelf

open ProteinFolding Residue Layout

namespace LayoutChain

variable {α : Type*} {R : α → α → Prop}

/-- A chain ending at `x`, followed by a chain that `x` can be put in front of, is a chain,
and it ends where the second one (with `x` in front) ends. -/
theorem glue {l₁ l₂ : List α} {x : α} (h₁ : l₁.IsChain R) (hx : l₁.getLast? = some x)
    (h₂ : (x :: l₂).IsChain R) :
    (l₁ ++ l₂).IsChain R ∧ (l₁ ++ l₂).getLast? = (x :: l₂).getLast? := by
  obtain ⟨l, rfl⟩ := List.getLast?_eq_some_iff.1 hx
  have h := List.isChain_append.1 h₁
  refine ⟨?_, ?_⟩
  · rw [List.append_assoc, List.singleton_append]
    exact List.isChain_append.2 ⟨h.1, h₂, fun a ha b hb => by
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
      subst hb; exact h.2.2 a ha x (by simp)⟩
  · rw [List.append_assoc, List.singleton_append, List.getLast?_append_of_ne_nil _ (by simp)]

/-- Putting `x` in front of a chain whose first element is related to `x`. -/
theorem cons_of_head {l : List α} {x y : α} (h : l.IsChain R) (hy : l.head? = some y)
    (hxy : R x y) : (x :: l).IsChain R :=
  List.isChain_cons'.2 ⟨fun b hb => by rw [hy] at hb; cases hb; exact hxy, h⟩

/-- One step of Table 1: a chain ending at `x`, then a chain from `y` to `z` with `x ~ y`. -/
theorem step {l₁ l₂ : List α} {x y z : α} (h₁ : l₁.IsChain R) (hx : l₁.getLast? = some x)
    (h₂ : l₂.IsChain R) (hy : l₂.head? = some y) (hxy : R x y) (hz : l₂.getLast? = some z) :
    (l₁ ++ l₂).IsChain R ∧ (l₁ ++ l₂).getLast? = some z := by
  obtain ⟨h, h'⟩ := glue h₁ hx (cons_of_head h₂ hy hxy)
  refine ⟨h, ?_⟩
  rw [h', List.getLast?_cons, hz]
  rfl

/-- Chains through a sequence of blocks: if block `r`, with the end of the previous
block (or `s₀`) in front, is a chain ending at `out r`, then all the blocks together,
with `s₀` in front, form a chain. -/
theorem blocks (g : ℕ → List α) (out : ℕ → α) (s₀ : α) (k : ℕ)
    (h : ∀ r < k, ((if r = 0 then s₀ else out (r - 1)) :: g r).IsChain R ∧
      ((if r = 0 then s₀ else out (r - 1)) :: g r).getLast? = some (out r)) :
    (s₀ :: (List.range k).flatMap g).IsChain R ∧
      (s₀ :: (List.range k).flatMap g).getLast? = some (if k = 0 then s₀ else out (k - 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih fun r hr => h r (by omega)
    obtain ⟨hk1, hk2⟩ := h k (by omega)
    obtain ⟨g1, g2⟩ := glue ih1 ih2 hk1
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ← List.cons_append]
    refine ⟨g1, ?_⟩
    rw [g2, hk2]
    simp

end LayoutChain

open LayoutChain

/-- One item block, with the site before it in front, is a chain ending at the last
site of the item. -/
theorem item_block_chain {J : Packing.Instance} (hJ : Normalised J) {P : Parts J}
    (hP : P.Good) (i : Fin J.sizes.length) :
    (prevOut P.lo i :: (P.mid i.succ ++ tokSites (itemTokens P.lo i))).IsChain
        cubicLattice.Adj ∧
      (prevOut P.lo i :: (P.mid i.succ ++ tokSites (itemTokens P.lo i))).getLast? =
        some (itemOut P.lo i) := by
  have hm := hP.mid_succ_chain i
  have hh := item_head? hJ P.lo i
  have hc := item_isChain hP.placed i
  obtain ⟨rest, hr⟩ : ∃ rest, tokSites (itemTokens P.lo i) = itemIn P.lo i :: rest := by
    cases e : tokSites (itemTokens P.lo i) with
    | nil => rw [e] at hh; cases hh
    | cons a l => rw [e] at hh; cases hh; exact ⟨l, rfl⟩
  have hl : (prevOut P.lo i :: (P.mid i.succ ++ [itemIn P.lo i])).getLast? =
      some (itemIn P.lo i) := by
    rw [← List.cons_append, List.getLast?_append]; simp
  have := glue hm hl (hr ▸ hc)
  rw [← List.cons_append, List.append_assoc, List.singleton_append] at this
  rw [hr, ← List.cons_append]
  refine ⟨this.1, ?_⟩
  rw [this.2, ← hr, ← item_getLast? hJ P.lo i]

/-- The item blocks, with the last site of `F₂` in front, form a chain. -/
theorem items_chain {J : Packing.Instance} (hJ : Normalised J) {P : Parts J}
    (hP : P.Good) :
    (pt 1 (-1) (N J) :: (List.finRange J.sizes.length).flatMap fun i =>
      P.mid i.succ ++ tokSites (itemTokens P.lo i)).IsChain cubicLattice.Adj := by
  set L := J.sizes.length
  let g : ℕ → List Site := fun r =>
    if h : r < L then P.mid (Fin.succ ⟨r, h⟩) ++ tokSites (itemTokens P.lo ⟨r, h⟩) else []
  let out : ℕ → Site := fun r => if h : r < L then itemOut P.lo ⟨r, h⟩ else pt 0 0 0
  have e : ((List.finRange L).flatMap fun i =>
      P.mid i.succ ++ tokSites (itemTokens P.lo i)) = (List.range L).flatMap g := by
    rw [← List.map_coe_finRange, List.flatMap_map]
    congr 1
    funext i
    simp [g]
    rfl
  rw [e]
  refine (blocks g out _ L fun r hr => ?_).1
  have hpre : (if r = 0 then pt 1 (-1) (N J) else out (r - 1)) = prevOut P.lo ⟨r, hr⟩ := by
    unfold prevOut
    by_cases h0 : r = 0
    · simp [h0]
    · simp [h0, out, show r - 1 < L by omega]
  rw [hpre]
  have hg : g r = P.mid (Fin.succ ⟨r, hr⟩) ++ tokSites (itemTokens P.lo ⟨r, hr⟩) := by
    simp [g, hr]
  have ho : out r = itemOut P.lo ⟨r, hr⟩ := by simp [out, hr]
  rw [hg, ho]
  exact item_block_chain hJ hP ⟨r, hr⟩

/-- Theorem 16 (b): consecutive sites of the fold of Table 1 are adjacent. -/
theorem layout_isChain {J : Packing.Instance} (hJ : Normalised J) {P : Parts J}
    (hP : P.Good) : (layout P).IsChain cubicLattice.Adj := by
  unfold layout
  -- the core and the first `P`
  have s1 := step (z := firstP J) hP.core_chain hP.core_last (List.isChain_singleton (firstP J)) rfl
    (by simp only [coreEnd, firstP, adj_pt]; omega) rfl
  -- the run `A`
  have s2 := step s1.1 s1.2 (tokSites_isChain hP.a_valid hP.a_linked) hP.a_head
    (by simp only [firstP, aIn, adj_pt]; omega) hP.a_last
  -- the first linker
  have hmid : ([p₀ J] ++ P.mid 0 ++ [q₀ J, q₀' J]).IsChain cubicLattice.Adj ∧
      ([p₀ J] ++ P.mid 0 ++ [q₀ J, q₀' J]).getLast? = some (q₀' J) := by
    have hl : (p₀ J :: (P.mid 0 ++ [q₀ J])).getLast? = some (q₀ J) := by
      rw [← List.cons_append, List.getLast?_append]; simp
    have := step hP.mid_zero_chain hl (List.isChain_singleton (q₀' J)) rfl
      (by simp only [q₀, q₀', adj_pt]; omega) rfl
    simpa using this
  have s3 := step (y := p₀ J) s2.1 s2.2 hmid.1 (by simp) (by simp only [aOut, p₀, adj_pt]; omega) hmid.2
  -- `F₁`, the tethers, the separators, `F₂`
  have s4 := step s3.1 s3.2 (f₁_isChain J) (f₁_head? J)
    (by simp only [q₀', adj_pt]; omega) (f₁_getLast? hJ)
  have s5 := step s4.1 s4.2 (tether₁_isChain J) (tether₁_head? J)
    (by simp only [adj_pt]; omega) (tether₁_getLast? J)
  have s6 := step s5.1 s5.2 (sepPart_isChain J) (sepPart_head? J)
    (by simp only [adj_pt]; omega) (sepPart_getLast? J)
  have s7 := step s6.1 s6.2 (tether₂_isChain J) (tether₂_head? J)
    (by simp only [adj_pt]; omega) (tether₂_getLast? J)
  have s8 := step s7.1 s7.2 (f₂_isChain J) (f₂_head? J)
    (by simp only [adj_pt]; omega) (f₂_getLast? hJ)
  -- the items
  exact (glue s8.1 s8.2 (items_chain hJ hP)).1

end ProteinFolding.Shelf
