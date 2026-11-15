import ProteinFolding.Cubic.Proofs.PackingPrefixFold

/-! Transfer component separation and H containment to the already assembled
literal prefix. Its witness retains precisely the site decomposition needed
for these global concatenations. -/

namespace ProteinFolding.CubicPackingPrefixFold

open CubicPacking CubicPackingPrefixComponents

theorem Witness.disjoint_of_components {q Q : ℕ} {hd : 2 ≤ depth q Q}
    {heven : depth q Q % 2 = 0} (w : Witness q Q hd heven) {N : ℕ}
    (g : Fold cubicLattice N)
    (hsep : ∀ b ∈ initialBlock (depth q Q) w.initial w.initial_last ::
      tailBlocks (depth q Q) (alpha Q) hd heven, ∀ i j, b.fold.pos i ≠ g.pos j) :
    ∀ i j, w.fold.pos i ≠ g.pos j := by
  intro i j he
  have hm := (w.sites (w.fold.pos i)).mp ⟨i, rfl⟩
  rcases hm with ⟨k, hk⟩ | ⟨b, hb, k, hk⟩
  · exact hsep (initialBlock (depth q Q) w.initial w.initial_last) (by simp) k j (hk.trans he)
  · exact hsep b (by simp [hb]) k j (hk.trans he)

theorem Witness.hydrophobicSites_inside {q Q : ℕ} {hd : 2 ≤ depth q Q}
    {heven : depth q Q % 2 = 0} (w : Witness q Q hd heven) :
    hydrophobicSites (prefixWord q Q) w.fold ⊆ cube (fun _ => 0) (side q Q) := by
  rintro p ⟨i, hi, rfl⟩
  exact w.H_inside i hi

end ProteinFolding.CubicPackingPrefixFold
