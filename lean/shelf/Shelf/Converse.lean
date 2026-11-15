import Mathlib
import ProteinFolding.Cubic.Proofs.PackingGeometryAnchorIntervals
import Shelf.Tether
import Shelf.LongPath
import Shelf.EdgeDistance
import Shelf.ShelfLine
import Shelf.WordAnatomy
import Shelf.MainTheorem

/-!
# From a perfect fold to a packing

Steps 1 to 4 of the proof of Theorem 12. The long run `A` takes nine edges, the
fillers `F₁` and `F₂` take two of the three free edges, and the separators and the
items all sit on the third one, the shelf; the first and the last separator are at
its two ends. Reading the shelf as the row of nodes `1, …, n - 2` gives the
hypotheses of `packing_of_shelf_line` (Steps 5 to 7).
-/

namespace ProteinFolding.Shelf

open ProteinFolding ProteinFolding.CubicPackingGeometry Residue

variable {S : Sequence} {J : Packing.Instance} {f : Fold cubicLattice S.length}

/-! ## Small facts -/

theorem RunAt.H {o r t : ℕ} (h : RunAt S o r) (ht : t < r) : S[o + 3 * t]? = some H :=
  (h t ht).2.2.1

theorem RunAt.lt {o r t : ℕ} (h : RunAt S o r) (ht : t < r) : o + 3 * t < S.length :=
  lt_length_of_getElem? (h.H ht)

/-- A letter whose site is a site of a run is a letter of the run. -/
theorem index_of_mem_runSites {o r k : ℕ} (h : RunAt S o r) (hk : k < S.length)
    (hm : site f k ∈ runSites f o r) : ∃ t < r, k = o + 3 * t := by
  obtain ⟨t, ht, he⟩ := mem_runSites.mp hm
  exact ⟨t, ht, (site_inj f (h.lt ht) hk he).symm⟩

/-- The `H`'s of a run, as a function on `Fin r`, are injective. -/
theorem RunAt.inj {o r : ℕ} (h : RunAt S o r) :
    Function.Injective (fun t : Fin r => site f (o + 3 * t.val)) := by
  intro a b hab
  have := site_inj f (h.lt a.isLt) (h.lt b.isLt) hab
  exact Fin.ext (by omega)

/-- Consecutive `H`'s of a run, as a function on `Fin r`, are adjacent. -/
theorem RunAt.step {n o r : ℕ} (hf : Fills S f n) (h : RunAt S o r) :
    ∀ i j : Fin r, i.val + 1 = j.val →
      cubicLattice.Adj (site f (o + 3 * i.val)) (site f (o + 3 * j.val)) := by
  intro i j hij
  rw [← hij]
  exact h.adj hf (by omega)

/-- Separators are `B + 7` letters apart. -/
theorem oSep_add (A : Anatomy S J) (j : ℕ) :
    ∀ k, j + k ≤ J.bins → A.oSep (j + k) = A.oSep j + k * (J.capacity + 7)
  | 0, _ => by simp
  | k + 1, h => by
    rw [← add_assoc, A.tetherSep (j + k) (by omega), oSep_add A j k (by omega)]
    ring

theorem oSep_le (A : Anatomy S J) {j : ℕ} (hj : j ≤ J.bins) :
    A.oSep 0 + j ≤ A.oSep j ∧ A.oSep j + (J.bins - j) ≤ A.oSep J.bins := by
  have h1 := oSep_add A 0 j (by omega)
  have h2 := oSep_add A j (J.bins - j) (by omega)
  rw [zero_add] at h1
  rw [show j + (J.bins - j) = J.bins by omega] at h2
  have := Nat.le_mul_of_pos_right j (show 0 < J.capacity + 7 by omega)
  have := Nat.le_mul_of_pos_right (J.bins - j) (show 0 < J.capacity + 7 by omega)
  omega

/-- Two nodes of edges that do not touch, at distance at most `d + 1`, have the same number. -/
theorem node_eq_of_far {d : ℕ} {e e' : CubeEdge} (h : NoCommonCorner e e') {r s : Fin d}
    (hle : latticeDistance (openEdgePoint 0 d e r) (openEdgePoint 0 d e' s) ≤ d + 1) : r = s :=
  far_edges_eq d h r s (le_antisymm hle (far_edges d h r s))

/-- A node of an edge is determined by its rail coordinate. -/
theorem node_eq_of_rail {d : ℕ} {e : CubeEdge} {p q : Site} (hp : p ∈ openEdgeFinset 0 d e)
    (hq : q ∈ openEdgeFinset 0 d e)
    (h : railCoordinate 0 e.axis p = railCoordinate 0 e.axis q) : p = q := by
  obtain ⟨r, rfl⟩ := (mem_openEdgeFinset_iff d e p).mp hp
  obtain ⟨s, rfl⟩ := (mem_openEdgeFinset_iff d e q).mp hq
  rw [railCoordinate_openEdgePoint, railCoordinate_openEdgePoint] at h
  rw [show r = s from Fin.ext (by omega)]

/-- An edge whose nodes avoid a longest path is free. -/
theorem free_of_avoid {d : ℕ} (hd : 0 < d) {ps : List Site} {free : Finset CubeEdge}
    (hmem : ∀ p, p ∈ ps ↔ p ∈ cornerFinset 0 d ∨ ∃ e, e ∉ free ∧ p ∈ openEdgeFinset 0 d e)
    {e : CubeEdge} (he : ∀ p ∈ openEdgeFinset 0 d e, p ∉ ps) : e ∈ free := by
  by_contra h
  have hp : openEdgePoint 0 d e ⟨0, hd⟩ ∈ openEdgeFinset 0 d e :=
    (mem_openEdgeFinset_iff d e _).mpr ⟨_, rfl⟩
  exact he _ hp ((hmem _).mpr (Or.inr ⟨e, h, hp⟩))

/-- Three free edges, two of them known: the third one. -/
theorem third_edge {free : Finset CubeEdge} (hc : free.card = 3) {e₁ e₂ : CubeEdge}
    (h1 : e₁ ∈ free) (h2 : e₂ ∈ free) (hne : e₁ ≠ e₂) :
    ∃ e ∈ free, e ≠ e₁ ∧ e ≠ e₂ ∧ ∀ x ∈ free, x = e₁ ∨ x = e₂ ∨ x = e := by
  have hc' : ((free.erase e₁).erase e₂).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne.symm, h2⟩),
      Finset.card_erase_of_mem h1, hc]
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hc'
  have hmem : e ∈ (free.erase e₁).erase e₂ := by rw [he]; simp
  simp only [Finset.mem_erase] at hmem
  refine ⟨e, hmem.2.2, hmem.2.1, hmem.1, fun x hx => ?_⟩
  by_cases a : x = e₁
  · exact Or.inl a
  by_cases b : x = e₂
  · exact Or.inr (Or.inl b)
  have : x ∈ (free.erase e₁).erase e₂ := by simp [a, b, hx]
  rw [he] at this
  exact Or.inr (Or.inr (Finset.mem_singleton.mp this))

/-- A filler on an edge starts and ends at the two end nodes. -/
theorem filler_ends {d o : ℕ} (hd : 0 < d) (hf : Fills S f (d + 2)) (hrun : RunAt S o d)
    {e : CubeEdge} (hedge : ∀ t < d, site f (o + 3 * t) ∈ openEdgeFinset 0 d e) :
    (site f o = openEdgePoint 0 d e ⟨0, hd⟩ ∧
        site f (o + 3 * (d - 1)) = openEdgePoint 0 d e ⟨d - 1, by omega⟩) ∨
      (site f o = openEdgePoint 0 d e ⟨d - 1, by omega⟩ ∧
        site f (o + 3 * (d - 1)) = openEdgePoint 0 d e ⟨0, hd⟩) := by
  rcases fills_edge_direction d e _ hrun.inj (hrun.step hf) (fun t => hedge t t.isLt) with h | h
  · left
    have h0 := h ⟨0, hd⟩
    have h1 := h ⟨d - 1, by omega⟩
    simp only [Nat.mul_zero, Nat.add_zero] at h0 h1
    exact ⟨h0, h1⟩
  · right
    have h0 := h ⟨0, hd⟩
    have h1 := h ⟨d - 1, by omega⟩
    simp only [Nat.mul_zero, Nat.add_zero] at h0 h1
    refine ⟨h0.trans (congrArg _ (Fin.ext ?_)), h1.trans (congrArg _ (Fin.ext ?_))⟩
    · simp only [Fin.val_rev]
    · simp only [Fin.val_rev]; omega

/-! ## Steps 1 to 3: the shelf -/

/-- Steps 1 to 3 of the proof of Theorem 12. `F₁` fills an edge `e₁`, `F₂` an edge `e₂`, and the
separators and the items lie on a third edge `e`, the shelf, which touches neither. -/
theorem shelf_edges (hJ : Normalised J) (A : Anatomy S J) {d : ℕ} (hd : side J = d + 2)
    (hf : Fills S f (d + 2)) :
    ∃ e₁ e₂ e : CubeEdge, NoCommonCorner e₁ e ∧ NoCommonCorner e e₂ ∧
      (∀ t < d, site f (A.oF₁ + 3 * t) ∈ openEdgeFinset 0 d e₁) ∧
      (∀ t < d, site f (A.oF₂ + 3 * t) ∈ openEdgeFinset 0 d e₂) ∧
      (∀ j ≤ J.bins, site f (A.oSep j) ∈ openEdgeFinset 0 d e) ∧
      (∀ i, ∀ t < J.sizes.get i, site f (A.oItem i + 3 * t) ∈ openEdgeFinset 0 d e) := by
  have hd0 : 0 < d := by unfold side at hd; omega
  have hAF := A.A_before_F₁
  have hsep0 := A.tetherF₁
  have hF₂s := A.tetherF₂
  have hitems := A.F₂_before_items
  have hF₁ : RunAt S A.oF₁ d := by have := A.runF₁; rwa [show side J - 2 = d by omega] at this
  have hF₂ : RunAt S A.oF₂ d := by have := A.runF₂; rwa [show side J - 2 = d by omega] at this
  set psA := runSites f A.oA (9 * side J - 10) with hpsA
  have hAnd := A.runA.nodup f
  have hAch := A.runA.isChain hf
  have hAsk := A.runA.on_skeleton hf
  have hAlen : psA.length = 9 * (d + 2) - 10 := by rw [runSites_length]; omega
  obtain ⟨free, hcard, hpair, hmem⟩ := longPath_free_edges d hd0 psA hAnd hAch hAsk hAlen
  have havoid : ∀ k, k < S.length → A.oF₁ ≤ k → site f k ∉ psA := by
    intro k hk hk1 hm
    obtain ⟨t, ht, rfl⟩ := index_of_mem_runSites A.runA hk hm
    omega
  have hrunavoid : ∀ o, RunAt S o d → A.oF₁ ≤ o → ∀ p ∈ runSites f o d, p ∉ psA := by
    intro o h ho p hp
    obtain ⟨t, ht, rfl⟩ := mem_runSites.mp hp
    exact havoid _ (h.lt ht) (by omega)
  obtain ⟨e₁, he₁, he₁a⟩ := filler_fills_free_edge d hd0 psA _ hAnd hAch hAsk hAlen
    (hF₁.nodup f) (hF₁.isChain hf) (hF₁.on_skeleton hf) (runSites_length _ _ _)
    (hrunavoid _ hF₁ le_rfl)
  obtain ⟨e₂, he₂, he₂a⟩ := filler_fills_free_edge d hd0 psA _ hAnd hAch hAsk hAlen
    (hF₂.nodup f) (hF₂.isChain hf) (hF₂.on_skeleton hf) (runSites_length _ _ _)
    (hrunavoid _ hF₂ (by have := (oSep_le A le_rfl).1; omega))
  have hfree₁ := free_of_avoid hd0 hmem he₁a
  have hfree₂ := free_of_avoid hd0 hmem he₂a
  have hne : e₁ ≠ e₂ := by
    rintro rfl
    have hp : openEdgePoint 0 d e₁ ⟨0, hd0⟩ ∈ openEdgeFinset 0 d e₁ :=
      (mem_openEdgeFinset_iff d e₁ _).mpr ⟨_, rfl⟩
    obtain ⟨t, ht, h1⟩ := mem_runSites.mp ((he₁ _).mpr hp)
    obtain ⟨t', ht', h2⟩ := mem_runSites.mp ((he₂ _).mpr hp)
    have := site_inj f (hF₁.lt ht) (hF₂.lt ht') (h1.trans h2.symm)
    have := (oSep_le A le_rfl).1
    omega
  obtain ⟨e, hfree, hne₁, hne₂, hcl⟩ := third_edge hcard hfree₁ hfree₂ hne
  -- a path of letters after `F₁` that are not letters of `F₁` or `F₂` lies on `e`
  have hon : ∀ qs : List Site, qs.Nodup → qs.IsChain cubicLattice.Adj →
      (∀ p ∈ qs, EdgeSkeleton 0 (d + 2) p) → qs ≠ [] →
      (∀ p ∈ qs, ∃ k, k < S.length ∧ A.oF₁ ≤ k ∧ (∀ t < d, k ≠ A.oF₁ + 3 * t) ∧
        (∀ t < d, k ≠ A.oF₂ + 3 * t) ∧ site f k = p) →
      ∀ p ∈ qs, p ∈ openEdgeFinset 0 d e := by
    intro qs hnd hch hsk hne hidx
    have hav : ∀ p ∈ qs, p ∉ psA := by
      intro p hp
      obtain ⟨k, hk, hk1, -, -, rfl⟩ := hidx p hp
      exact havoid k hk hk1
    obtain ⟨e', hq, hav'⟩ := path_in_free_edge d hd0 psA qs hAnd hAch hAsk hAlen hnd hch hsk hne hav
    obtain ⟨q, hqm⟩ := List.exists_mem_of_ne_nil qs hne
    obtain ⟨k, hk, -, h1, h2, rfl⟩ := hidx q hqm
    rcases hcl e' (free_of_avoid hd0 hmem hav') with rfl | rfl | rfl
    · obtain ⟨t, ht, h⟩ := index_of_mem_runSites hF₁ hk ((he₁ _).mpr (hq _ hqm))
      exact absurd h (h1 t ht)
    · obtain ⟨t, ht, h⟩ := index_of_mem_runSites hF₂ hk ((he₂ _).mpr (hq _ hqm))
      exact absurd h (h2 t ht)
    · exact hq
  refine ⟨e₁, e₂, e, hpair _ hfree₁ _ hfree hne₁.symm, hpair _ hfree _ hfree₂ hne₂, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact (he₁ _).mp (mem_runSites.mpr ⟨t, ht, rfl⟩)
  · intro t ht
    exact (he₂ _).mp (mem_runSites.mpr ⟨t, ht, rfl⟩)
  · intro j hj
    have hS := A.sep j hj
    have hb := oSep_le A hj
    refine hon [site f (A.oSep j)] (List.nodup_singleton _) (List.isChain_singleton _)
      (by simpa using hS.on_skeleton hf) (by simp) ?_ _ (List.mem_singleton_self _)
    intro p hp
    rw [List.mem_singleton] at hp
    exact ⟨_, lt_length_of_getElem? hS.2.2.1, by omega, fun t ht => by omega,
      fun t ht => by omega, hp.symm⟩
  · intro i t ht
    have hI := A.runItem i
    have hpos : 0 < J.sizes.get i := hJ.size_pos _ (List.get_mem _ _)
    refine hon _ (hI.nodup f) (hI.isChain hf) (hI.on_skeleton hf) ?_ ?_ _
      (mem_runSites.mpr ⟨t, ht, rfl⟩)
    · rw [← List.length_pos_iff, runSites_length]; exact hpos
    · intro p hp
      obtain ⟨u, hu, rfl⟩ := mem_runSites.mp hp
      have := hitems i
      have := (oSep_le A le_rfl).1
      exact ⟨_, hI.lt hu, by omega, fun t ht => by omega, fun t ht => by omega, rfl⟩

/-! ## Step 4: the end tethers are taut -/

theorem node_eq_of_tether {d k : ℕ} {e e' : CubeEdge} (h : NoCommonCorner e e') {r s : Fin d}
    (hle : latticeDistance (openEdgePoint 0 d e r) (openEdgePoint 0 d e' s) + 2 ≤ k)
    (hk : k ≤ d + 3) : r = s :=
  node_eq_of_far h (by omega)

/-- Step 4 of the proof of Theorem 12: the first and the last separator sit at the two end nodes
of the shelf. -/
theorem sep_ends (A : Anatomy S J) {d : ℕ} (hd : side J = d + 2) (hd2 : 2 ≤ d) (hm : 1 ≤ J.bins)
    (hf : Fills S f (d + 2)) {e₁ e₂ e : CubeEdge} (h1 : NoCommonCorner e₁ e)
    (h2 : NoCommonCorner e e₂)
    (hF₁e : ∀ t < d, site f (A.oF₁ + 3 * t) ∈ openEdgeFinset 0 d e₁)
    (hF₂e : ∀ t < d, site f (A.oF₂ + 3 * t) ∈ openEdgeFinset 0 d e₂)
    {s₀ s₁ : Fin d} (hs₀ : site f (A.oSep 0) = openEdgePoint 0 d e s₀)
    (hs₁ : site f (A.oSep J.bins) = openEdgePoint 0 d e s₁) :
    (s₀.val = 0 ∧ s₁.val = d - 1) ∨ (s₀.val = d - 1 ∧ s₁.val = 0) := by
  have hd0 : 0 < d := by omega
  have hF₁ : RunAt S A.oF₁ d := by have := A.runF₁; rwa [show side J - 2 = d by omega] at this
  have hF₂ : RunAt S A.oF₂ d := by have := A.runF₂; rwa [show side J - 2 = d by omega] at this
  have hsep0 := A.tetherF₁
  have hF₂s := A.tetherF₂
  have hb := (oSep_le A (le_refl J.bins)).1
  have hS0 := (A.sep 0 (Nat.zero_le _)).2.2.1
  have hSm := (A.sep J.bins le_rfl).2.2.1
  have hend₀ : s₀.val = 0 ∨ s₀.val = d - 1 := by
    have ht := tether hf (i := A.oF₁ + 3 * (d - 1)) (j := A.oSep 0) (by omega)
      (hF₁.H (by omega)) hS0 (fun t h1 h2 => A.tetherF₁_P t (by omega) h2)
    rw [hs₀] at ht
    rcases filler_ends hd0 hf hF₁ hF₁e with ⟨-, hl⟩ | ⟨-, hl⟩ <;> rw [hl] at ht
    · right; rw [← node_eq_of_tether h1 ht (by omega)]
    · left; rw [← node_eq_of_tether h1 ht (by omega)]
  have hend₁ : s₁.val = 0 ∨ s₁.val = d - 1 := by
    have hH : S[A.oF₂]? = some H := by simpa using hF₂.H hd0
    have ht := tether hf (i := A.oSep J.bins) (j := A.oF₂) (by omega) hSm hH A.tetherF₂_P
    rw [hs₁] at ht
    rcases filler_ends hd0 hf hF₂ hF₂e with ⟨hl, -⟩ | ⟨hl, -⟩ <;> rw [hl] at ht
    · left; rw [node_eq_of_tether h2 ht (by omega)]
    · right; rw [node_eq_of_tether h2 ht (by omega)]
  have hne : s₀.val ≠ s₁.val := by
    intro h
    rw [show s₀ = s₁ from Fin.ext h, ← hs₁] at hs₀
    have := site_inj f (lt_length_of_getElem? hS0) (lt_length_of_getElem? hSm) hs₀
    omega
  omega

/-! ## Steps 1 to 4 together, and Theorem 12 -/

/-- Steps 1 to 4 of the proof of Theorem 12. If the `H`'s of a string with the anatomy of `J`
fill the cube, then the separators and the items sit on one edge, read as the row of nodes
`1, …, n - 2`: the first and the last separator are at its two ends, consecutive separators are at
most `B + 5` apart, and each item is a block of consecutive nodes, disjoint from the other items
and from the separators. These are the hypotheses of `packing_of_shelf_line`. -/
theorem shelf_of_fills (J : Packing.Instance) (hJ : Normalised J) {S : Sequence}
    (A : Anatomy S J) {f : Fold cubicLattice S.length} (hf : Fills S f (side J)) :
    ∃ (sep : Fin (J.bins + 1) → ℕ) (start : Fin J.sizes.length → ℕ),
      ((sep 0 = 1 ∧ sep (Fin.last J.bins) = side J - 2) ∨
        (sep 0 = side J - 2 ∧ sep (Fin.last J.bins) = 1)) ∧
      (∀ j : Fin J.bins,
        sep j.succ ≤ sep j.castSucc + (J.capacity + 5) ∧
          sep j.castSucc ≤ sep j.succ + (J.capacity + 5)) ∧
      (∀ i, 1 ≤ start i ∧ start i + J.sizes.get i ≤ side J - 2 + 1) ∧
      (∀ i i', i ≠ i' →
        Disjoint (Finset.Ico (start i) (start i + J.sizes.get i))
          (Finset.Ico (start i') (start i' + J.sizes.get i'))) ∧
      (∀ i j, sep j ∉ Finset.Ico (start i) (start i + J.sizes.get i)) := by
  obtain ⟨d, hd⟩ : ∃ d, side J = d + 2 := ⟨side J - 2, by unfold side; omega⟩
  have hm : 1 ≤ J.bins := by obtain ⟨k, hk⟩ := hJ.bins_odd; omega
  have hd2 : 2 ≤ d := by
    have hB := hJ.capacity_pos
    have := Nat.mul_le_mul hm (show 2 ≤ J.capacity + 1 by omega)
    unfold side at hd
    omega
  have hf' : Fills S f (d + 2) := hd ▸ hf
  obtain ⟨e₁, e₂, e, h1, h2, hF₁e, hF₂e, hSe, hIe⟩ := shelf_edges hJ A hd hf'
  have hnode : ∀ j ≤ J.bins, ∃ r : Fin d, site f (A.oSep j) = openEdgePoint 0 d e r :=
    fun j hj => (mem_openEdgeFinset_iff d e _).mp (hSe j hj)
  have hSH : ∀ j ≤ J.bins, A.oSep j < S.length :=
    fun j hj => lt_length_of_getElem? (A.sep j hj).2.2.1
  have hitem : ∀ i, ∃ st, 1 ≤ st ∧ st + J.sizes.get i ≤ d + 1 ∧
      Finset.univ.image (fun t : Fin (J.sizes.get i) =>
        railCoordinate 0 e.axis (site f (A.oItem i + 3 * t.val))) =
        Finset.Ico st (st + J.sizes.get i) := fun i =>
    openEdge_path_coordinate_image 0 d _ (hJ.size_pos _ (List.get_mem _ _)) e _
      (A.runItem i).inj ((A.runItem i).step hf') (fun t => hIe i t t.isLt)
  choose start hst1 hst2 himg using hitem
  have hmemI : ∀ i x, x ∈ Finset.Ico (start i) (start i + J.sizes.get i) →
      ∃ t < J.sizes.get i, railCoordinate 0 e.axis (site f (A.oItem i + 3 * t)) = x := by
    intro i x hx
    rw [← himg i, Finset.mem_image] at hx
    obtain ⟨t, -, ht⟩ := hx
    exact ⟨t, t.isLt, ht⟩
  refine ⟨fun j => railCoordinate 0 e.axis (site f (A.oSep j.val)), start, ?_, ?_,
    fun i => ⟨hst1 i, by have := hst2 i; omega⟩, ?_, ?_⟩
  · obtain ⟨s₀, hs₀⟩ := hnode 0 (Nat.zero_le _)
    obtain ⟨s₁, hs₁⟩ := hnode J.bins le_rfl
    have := sep_ends A hd hd2 hm hf' h1 h2 hF₁e hF₂e hs₀ hs₁
    simp only [Fin.val_zero, Fin.val_last, hs₀, hs₁, railCoordinate_openEdgePoint]
    omega
  · intro j
    have hj := j.isLt
    obtain ⟨r, hr⟩ := hnode j (by omega)
    obtain ⟨s, hs⟩ := hnode (j + 1) (by omega)
    have hstep := A.tetherSep j hj
    have ht := tether hf (i := A.oSep j) (j := A.oSep (j + 1)) (by omega)
      (A.sep j (by omega)).2.2.1 (A.sep (j + 1) (by omega)).2.2.1 (A.tetherSep_P j hj)
    rw [hr, hs, openEdgePoint_distance] at ht
    simp only [Fin.val_succ, Fin.coe_castSucc, hr, hs, railCoordinate_openEdgePoint]
    omega
  · intro i i' hii'
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨t, ht, rfl⟩ := hmemI i x hx
    obtain ⟨t', ht', he⟩ := hmemI i' _ hx'
    have := site_inj f ((A.runItem i').lt ht') ((A.runItem i).lt ht)
      (node_eq_of_rail (hIe i' t' ht') (hIe i t ht) he)
    rcases lt_or_gt_of_ne hii' with h | h
    · have := A.items_in_order i i' h; omega
    · have := A.items_in_order i' i h; omega
  · intro i j hx
    have hj := j.isLt
    obtain ⟨t, ht, he⟩ := hmemI i _ hx
    have := site_inj f ((A.runItem i).lt ht) (hSH j (by omega))
      (node_eq_of_rail (hIe i t ht) (hSe j (by omega)) he)
    have := (oSep_le A (show j.val ≤ J.bins by omega)).2
    have := A.F₂_before_items i
    have := A.tetherF₂
    omega

/-- **Theorem 12.** If the string of a normalised instance has a perfect fold, the
instance has an exact packing. -/
theorem foldGivesPacking : FoldGivesPacking := by
  intro J hJ hperf
  obtain ⟨-, f, hf⟩ := (perfect_iff_exists_fills _ _).mp hperf
  obtain ⟨sep, start, hends, htether, hrange, hdisj, hsep⟩ :=
    shelf_of_fills J hJ (shelfAnatomy J) hf
  exact packing_of_shelf_line J hJ (side J - 2) sep start hends htether hrange hdisj hsep

end ProteinFolding.Shelf
