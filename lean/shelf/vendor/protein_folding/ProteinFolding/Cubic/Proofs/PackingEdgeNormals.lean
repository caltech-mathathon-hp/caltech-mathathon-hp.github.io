import ProteinFolding.Cubic.Proofs.PackingEdgeLift
import ProteinFolding.Cubic.Proofs.PackingGeometryOutward
import ProteinFolding.Common.GreedyLabels

/-! Greedy exterior-normal choices for an arbitrary simple cube-skeleton
path. The last outward direction may be prescribed. Every compressed edge
offers at least two shared outward normals, so a backward greedy labelling
avoids equal P directions at every H. All geometric prerequisites are proved
in the imported exterior/outward modules. -/

namespace ProteinFolding.CubicPackingLift

open CubicPacking CubicPackingGeometry CubicCertificates

def outwardDirections (a p : Site) (n : ℕ) : Finset (Fin 6) :=
  Finset.univ.filter fun d => step p d ∉ cube a n

theorem mem_outwardDirections (a p : Site) (n : ℕ) (d : Fin 6) :
    d ∈ outwardDirections a p n ↔ step p d ∉ cube a n := by simp [outwardDirections]

theorem two_le_card_of_members {D : Type} [DecidableEq D] (s : Finset D) (d e : D)
    (hd : d ∈ s) (he : e ∈ s) (hne : d ≠ e) : 2 ≤ s.card := by
  have hs : {d, e} ⊆ s := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hd
    · have hxe := Finset.mem_singleton.mp hx
      subst x
      exact he
  have hc := Finset.card_le_card hs
  simpa [hne] using hc

theorem outwardDirections_card (a p : Site) (n : ℕ) (hp : EdgeSkeleton a n p) :
    2 ≤ (outwardDirections a p n).card := by
  obtain ⟨d, e, hne, hd, he⟩ := skeleton_two_outward a p n hp
  exact two_le_card_of_members _ d e ((mem_outwardDirections a p n d).mpr hd)
    ((mem_outwardDirections a p n e).mpr he) hne

theorem commonOutward_card (a p q : Site) (n : ℕ)
    (hp : EdgeSkeleton a n p) (hq : EdgeSkeleton a n q) (hadj : cubicLattice.Adj p q) :
    2 ≤ (outwardDirections a p n ∩ outwardDirections a q n).card := by
  obtain ⟨d, e, hne, hpd, hqd, hpe, hqe⟩ := adjacent_skeleton_common_outward a p q n hp hq hadj
  apply two_le_card_of_members _ d e
  · simp only [Finset.mem_inter, mem_outwardDirections]
    exact ⟨hpd, hqd⟩
  · simp only [Finset.mem_inter, mem_outwardDirections]
    exact ⟨hpe, hqe⟩
  · exact hne

def pathAllowed {t : ℕ} (base : Fold cubicLattice t) (a : Site) (n : ℕ) (i : Fin t) : Finset (Fin 6) :=
  if hi : i.val = 0 then outwardDirections a (base.pos i) n else
    outwardDirections a (base.pos ⟨i.val - 1, by have := i.isLt; omega⟩) n ∩
      outwardDirections a (base.pos i) n

theorem pathAllowed_card {t : ℕ} (base : Fold cubicLattice t) (a : Site) (n : ℕ)
    (hskeleton : ∀ i, EdgeSkeleton a n (base.pos i)) (i : Fin t) : 2 ≤ (pathAllowed base a n i).card := by
  unfold pathAllowed
  split_ifs with hi
  · exact outwardDirections_card a (base.pos i) n (hskeleton i)
  · let prev : Fin t := ⟨i.val - 1, by have := i.isLt; omega⟩
    exact commonOutward_card a (base.pos prev) (base.pos i) n (hskeleton prev) (hskeleton i)
      (base.consecutive prev i (by dsimp [prev]; omega))

theorem pathAllowed_current {t : ℕ} (base : Fold cubicLattice t) (a : Site) (n : ℕ)
    (i : Fin t) (d : Fin 6) (hd : d ∈ pathAllowed base a n i) : step (base.pos i) d ∉ cube a n := by
  unfold pathAllowed at hd
  split_ifs at hd with hi
  · exact (mem_outwardDirections a (base.pos i) n d).mp hd
  · exact (mem_outwardDirections a (base.pos i) n d).mp (Finset.mem_inter.mp hd).2

theorem pathAllowed_previous {t : ℕ} (base : Fold cubicLattice t) (a : Site) (n : ℕ)
    (i j : Fin t) (hij : i.val + 1 = j.val) (d : Fin 6) (hd : d ∈ pathAllowed base a n j) :
    step (base.pos i) d ∉ cube a n := by
  have hj : j.val ≠ 0 := by omega
  unfold pathAllowed at hd
  rw [dif_neg hj] at hd
  have hm := (Finset.mem_inter.mp hd).1
  have he : (⟨j.val - 1, by have := j.isLt; omega⟩ : Fin t) = i := by
    apply Fin.ext
    change j.val - 1 = i.val
    omega
  rw [he] at hm
  exact (mem_outwardDirections a (base.pos i) n d).mp hm

theorem step_direction_injective (p : Site) : Function.Injective (step p) := by
  intro d e he
  fin_cases d <;> fin_cases e
  all_goals first
    | rfl
    | have h0 := congrFun he 0
      have h1 := congrFun he 1
      have h2 := congrFun he 2
      simp only [step, Fin.reduceFinMk, ↓reduceIte] at h0 h1 h2
      omega

theorem latticeDistance_step_same (p q : Site) (d : Fin 6) :
    latticeDistance (step p d) (step q d) = latticeDistance p q := by
  unfold latticeDistance
  apply Finset.sum_congr rfl
  intro k hk
  simp only [CubicVerifier.step_increment]
  congr 1
  ring

theorem step_preserves_adj (p q : Site) (d : Fin 6) (ha : cubicLattice.Adj p q) :
    cubicLattice.Adj (step p d) (step q d) := by
  change latticeDistance _ _ = 1
  rw [latticeDistance_step_same]
  exact ha

theorem edge_attachments_exist (t : ℕ) (ht : 0 < t) (base : Fold cubicLattice t)
    (a : Site) (n : ℕ) (hskeleton : ∀ i, EdgeSkeleton a n (base.pos i))
    (terminal : Fin 6) (hout : step (base.pos ⟨t - 1, by omega⟩) terminal ∉ cube a n) :
    ∃ before after : Fin t → Site,
      (∀ i, before i ∉ cube a n) ∧ (∀ i, after i ∉ cube a n) ∧
      (∀ i, cubicLattice.Adj (before i) (base.pos i)) ∧
      (∀ i, cubicLattice.Adj (base.pos i) (after i)) ∧
      (∀ i, before i ≠ after i) ∧
      (∀ i j : Fin t, i.val + 1 = j.val → cubicLattice.Adj (after i) (before j)) ∧
      after ⟨t - 1, by omega⟩ = step (base.pos ⟨t - 1, by omega⟩) terminal := by
  classical
  obtain ⟨labels, hlast, hallowed, hneighbours⟩ := GreedyLabels.finite_labels t
    (pathAllowed base a n) (pathAllowed_card base a n hskeleton) terminal
  let before : Fin t → Site := fun i => step (base.pos i) (labels i.castSucc)
  let after : Fin t → Site := fun i => step (base.pos i) (labels i.succ)
  refine ⟨before, after, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact pathAllowed_current base a n i _ (hallowed i)
  · intro i
    by_cases hend : i.val + 1 = t
    · have hei : i = ⟨t - 1, by omega⟩ := by apply Fin.ext; change i.val = t - 1; omega
      have hel : i.succ = ⟨t, by omega⟩ := Fin.ext hend
      change step (base.pos i) (labels i.succ) ∉ cube a n
      rw [hel, hlast, hei]
      exact hout
    · have hnext : i.val + 1 < t := by have := i.isLt; omega
      let j : Fin t := ⟨i.val + 1, hnext⟩
      have hel : i.succ = j.castSucc := Fin.ext rfl
      have hm := hallowed j
      rw [← hel] at hm
      exact pathAllowed_previous base a n i j rfl _ hm
  · intro i
    exact (step_adj _ _).symm
  · intro i
    exact step_adj _ _
  · intro i he
    exact hneighbours i (step_direction_injective (base.pos i) he)
  · intro i j hij
    have hel : i.succ = j.castSucc := Fin.ext hij
    dsimp only [before, after]
    rw [hel]
    exact step_preserves_adj _ _ _ (base.consecutive i j hij)
  · let last : Fin t := ⟨t - 1, by omega⟩
    have hel : last.succ = ⟨t, by omega⟩ := by apply Fin.ext; dsimp [last]; omega
    change step (base.pos last) (labels last.succ) = step (base.pos last) terminal
    rw [hel, hlast]

/-- Any simple cube-skeleton path lifts to E_t. One final outward P direction
is prescribed; the first P direction remains free, as required by the prefix. -/
theorem edgeWord_lift_exists (t : ℕ) (ht : 0 < t) (base : Fold cubicLattice t)
    (a : Site) (n : ℕ) (hskeleton : ∀ i, EdgeSkeleton a n (base.pos i))
    (terminal : Fin 6) (hout : step (base.pos ⟨t - 1, by omega⟩) terminal ∉ cube a n) :
    ∃ lifted : Fold cubicLattice (edgeWord t).length,
      hydrophobicSites (edgeWord t) lifted = Set.range base.pos ∧
      (∀ i, (edgeWord t).get i = .P → lifted.pos i ∉ cube a n) ∧
      lifted.pos (edgeLastIndex t ht) = step (base.pos ⟨t - 1, by omega⟩) terminal := by
  obtain ⟨before, after, hb, ha, hba, haa, hsep, hlink, hend⟩ :=
    edge_attachments_exist t ht base a n hskeleton terminal hout
  let lifted := edgeLift t base before after a n (fun i => (hskeleton i).1) hb ha hba haa hsep hlink
  refine ⟨lifted, edgeLift_H_occupation t base before after lifted (fun _ => rfl), ?_, ?_⟩
  · intro i hi
    exact edgeLiftPos_P_outside t base before after a n hb ha i hi
  · change edgeLiftPos t base before after (edgeLastIndex t ht) = _
    rw [edgeLiftPos_last]
    exact hend

def alternatingDirection (d e : Fin 6) (i : ℕ) : Fin 6 := if i % 2 = 0 then d else e

theorem alternatingDirection_ne (d e : Fin 6) (hne : d ≠ e) (i : ℕ) :
    alternatingDirection d e i ≠ alternatingDirection d e (i + 1) := by
  by_cases hi : i % 2 = 0
  · have hj : (i + 1) % 2 ≠ 0 := by omega
    simpa [alternatingDirection, hi, hj] using hne
  · have hj : (i + 1) % 2 = 0 := by omega
    simpa [alternatingDirection, hi, hj] using Ne.symm hne

/-- If two exterior normals work along the whole path, an even E block can
use the same prescribed normal at both endpoint P sites. This is the straight
anchor-block case needed for the wall and gap constructions. -/
theorem edgeWord_even_lift_exists (t : ℕ) (ht : 0 < t) (heven : t % 2 = 0)
    (base : Fold cubicLattice t) (a : Site) (n : ℕ) (hinside : ∀ i, base.pos i ∈ cube a n)
    (d e : Fin 6) (hne : d ≠ e)
    (hd : ∀ i, step (base.pos i) d ∉ cube a n) (he : ∀ i, step (base.pos i) e ∉ cube a n) :
    ∃ lifted : Fold cubicLattice (edgeWord t).length,
      hydrophobicSites (edgeWord t) lifted = Set.range base.pos ∧
      (∀ i, (edgeWord t).get i = .P → lifted.pos i ∉ cube a n) ∧
      lifted.pos (edgeFirstIndex t ht) = step (base.pos ⟨0, ht⟩) d ∧
      lifted.pos (edgeLastIndex t ht) = step (base.pos ⟨t - 1, by omega⟩) d := by
  let before : Fin t → Site := fun i => step (base.pos i) (alternatingDirection d e i.val)
  let after : Fin t → Site := fun i => step (base.pos i) (alternatingDirection d e (i.val + 1))
  have hb : ∀ i, before i ∉ cube a n := by
    intro i
    dsimp only [before, alternatingDirection]
    split_ifs
    · exact hd i
    · exact he i
  have ha : ∀ i, after i ∉ cube a n := by
    intro i
    dsimp only [after, alternatingDirection]
    split_ifs
    · exact hd i
    · exact he i
  have hba : ∀ i, cubicLattice.Adj (before i) (base.pos i) := fun i => (step_adj _ _).symm
  have haa : ∀ i, cubicLattice.Adj (base.pos i) (after i) := fun i => step_adj _ _
  have hsep : ∀ i, before i ≠ after i := by
    intro i hip
    exact alternatingDirection_ne d e hne i.val (step_direction_injective (base.pos i) hip)
  have hlink : ∀ i j : Fin t, i.val + 1 = j.val → cubicLattice.Adj (after i) (before j) := by
    intro i j hij
    dsimp only [before, after]
    rw [hij]
    exact step_preserves_adj _ _ _ (base.consecutive i j hij)
  let lifted := edgeLift t base before after a n hinside hb ha hba haa hsep hlink
  refine ⟨lifted, edgeLift_H_occupation t base before after lifted (fun _ => rfl), ?_, ?_, ?_⟩
  · intro i hi
    exact edgeLiftPos_P_outside t base before after a n hb ha i hi
  · change edgeLiftPos t base before after (edgeFirstIndex t ht) = _
    rw [edgeLiftPos_first]
    simp [before, alternatingDirection]
  · change edgeLiftPos t base before after (edgeLastIndex t ht) = _
    rw [edgeLiftPos_last]
    dsimp only [after]
    have ht' : t - 1 + 1 = t := by omega
    simp only [ht', alternatingDirection, if_pos heven]

end ProteinFolding.CubicPackingLift
