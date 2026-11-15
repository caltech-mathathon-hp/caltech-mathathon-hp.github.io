import ProteinFolding.Cubic.Proofs.PackingEdgeNormals
import ProteinFolding.Cubic.Proofs.PackingFaceLift

/-! Disjointness of exterior decorations follows from disjoint H owners.
Every exterior cube site has at most one cube neighbour, so this statement
handles all P/P comparisons between independently lifted E and F blocks. -/

namespace ProteinFolding.CubicPackingLift

open CubicCertificates CubicPacking CubicPackingGeometry CubicPackingSnake

def OwnedBy (a : Site) (n : ℕ) (p owner : Site) : Prop :=
  p = owner ∨ (p ∉ cube a n ∧ cubicLattice.Adj p owner)

def AttachedTo {N H : ℕ} (a : Site) (n : ℕ) (f : Fold cubicLattice N)
    (owners : Fin H → Site) : Prop :=
  (∀ k, owners k ∈ cube a n) ∧ ∀ i, ∃ k, OwnedBy a n (f.pos i) (owners k)

theorem ownedBy_owner_unique (a : Site) (n : ℕ) (p x y : Site)
    (hx : x ∈ cube a n) (hy : y ∈ cube a n)
    (hpx : OwnedBy a n p x) (hpy : OwnedBy a n p y) : x = y := by
  rcases hpx with rfl | ⟨hp, hpx⟩
  · rcases hpy with he | ⟨hout, _⟩
    · exact he
    · exact False.elim (hout hx)
  · rcases hpy with rfl | ⟨_, hpy⟩
    · exact False.elim (hp hy)
    · exact cube_exterior_neighbour_unique a n p x y hp hx hy hpx hpy

/-- Independent complete blocks are disjoint as soon as their compressed
H paths are disjoint; no further P attachment collision hypotheses remain. -/
theorem attached_folds_disjoint {N M H K : ℕ} (a : Site) (n : ℕ)
    (f : Fold cubicLattice N) (g : Fold cubicLattice M)
    (p : Fin H → Site) (q : Fin K → Site)
    (hf : AttachedTo a n f p) (hg : AttachedTo a n g q)
    (hdisjoint : ∀ i j, p i ≠ q j) (i : Fin N) (j : Fin M) : f.pos i ≠ g.pos j := by
  intro he
  obtain ⟨k, hk⟩ := hf.2 i
  obtain ⟨l, hl⟩ := hg.2 j
  rw [← he] at hl
  exact hdisjoint k l (ownedBy_owner_unique a n (f.pos i) (p k) (q l)
    (hf.1 k) (hg.1 l) hk hl)

theorem edgeLift_attached (t : ℕ) (base : Fold cubicLattice t) (before after : Fin t → Site)
    (a : Site) (n : ℕ) (f : Fold cubicLattice (edgeWord t).length)
    (hpos : ∀ i, f.pos i = edgeLiftPos t base before after i)
    (hinside : ∀ k, base.pos k ∈ cube a n)
    (hbefore : ∀ k, before k ∉ cube a n) (hafter : ∀ k, after k ∉ cube a n)
    (hbeforeAdj : ∀ k, cubicLattice.Adj (before k) (base.pos k))
    (hafterAdj : ∀ k, cubicLattice.Adj (base.pos k) (after k)) :
    AttachedTo a n f base.pos := by
  refine ⟨hinside, ?_⟩
  intro i
  refine ⟨edgeBaseIndex t i, ?_⟩
  rw [hpos i]
  by_cases hr : edgeRole i = 1
  · exact Or.inl (by simp only [edgeLiftPos, hr, decoration])
  · exact Or.inr ⟨decoration_outside base before after a n hbefore hafter _ _ hr,
      decoration_adj_owner base before after hbeforeAdj hafterAdj _ _ hr⟩

/-- The literal PHP word itself supplies the attachment owner, even when
the fold was obtained existentially from the greedy lifting theorem. -/
theorem edgeWord_fold_attached (t : ℕ) (f : Fold cubicLattice (edgeWord t).length)
    (base : Fold cubicLattice t) (a : Site) (n : ℕ)
    (hsites : hydrophobicSites (edgeWord t) f = Set.range base.pos)
    (hinside : ∀ k, base.pos k ∈ cube a n)
    (hout : ∀ i, (edgeWord t).get i = .P → f.pos i ∉ cube a n) :
    AttachedTo a n f base.pos := by
  refine ⟨hinside, ?_⟩
  intro i
  let j := edgeHIndex t (edgeBaseIndex t i)
  have hj : (edgeWord t).get j = .H := by
    apply (edgeWord_H_iff t j).mpr
    dsimp [j, edgeHIndex]
    omega
  have hmem : f.pos j ∈ hydrophobicSites (edgeWord t) f := ⟨j, hj, rfl⟩
  rw [hsites] at hmem
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, ?_⟩
  rw [hk]
  have hjv : j.val = 3 * (i.val / 3) + 1 := rfl
  by_cases hi : i.val % 3 = 1
  · left
    congr 1
    apply Fin.ext
    omega
  · right
    refine ⟨hout i ?_, ?_⟩
    · rw [edgeWord_residue_role, if_neg hi]
    · have hm : i.val % 3 = 0 ∨ i.val % 3 = 2 := by omega
      rcases hm with hm | hm
      · exact f.consecutive i j (by omega)
      · exact (f.consecutive j i (by omega)).symm

theorem faceLift_attached (t : ℕ) (ht : 2 ∣ t) (base : Fold cubicLattice t)
    (hplane : ∀ k, base.pos k 2 = 0) (n : ℕ)
    (hinside : ∀ k, base.pos k ∈ cube (fun _ => 0) n) :
    AttachedTo (fun _ => 0) n (faceLift t ht base hplane) base.pos := by
  refine ⟨hinside, ?_⟩
  intro i
  refine ⟨faceBaseIndex t ht i, ?_⟩
  change OwnedBy _ _ (faceLiftPos t ht base i) _
  by_cases hz : faceHeight i.val = 0
  · left
    rw [faceLiftPos, hz]
    exact atHeight_zero_of_plane _ (hplane _)
  · have hz' : faceHeight i.val = -1 := by
      unfold faceHeight at hz ⊢
      split_ifs <;> simp_all
    right
    constructor
    · intro hp
      have hb := (hp 2).1
      change (0 : ℤ) ≤ faceHeight i.val at hb
      omega
    · unfold faceLiftPos
      rw [hz']
      have hv := atHeight_vertical (base.pos (faceBaseIndex t ht i)) (-1)
      simpa only [Int.reduceNeg, Int.reduceAdd,
        atHeight_zero_of_plane _ (hplane _)] using hv

end ProteinFolding.CubicPackingLift
