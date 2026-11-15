import ProteinFolding.Tetrahedral.NearFieldCanonicalRingTrackSeparation
import ProteinFolding.Tetrahedral.NearFieldCanonicalBasePieces
import ProteinFolding.Tetrahedral.NearFieldExitCapFamily
import ProteinFolding.Tetrahedral.FaceRowsColumnOwners

/-! Every actual separator tether and capped separator avoids all six ring
columns at every height. Their Y/Z quadrant forces a B column's direction 3. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem Bcolumn_ne_positiveY_nonpositiveZ {m : ℕ} (C : DanglingColumn m)
    (hB : InBSublattice C.owner.val) (hdir : C.dir ≠ 3) (x : Site)
    (hy : 1 ≤ bulkY m x) (hz : x.val 2 ≤ 0) (n : ℕ) : x ≠ C.point n := by
  intro heq
  have hcy := C.point_signed_y n
  have hcz := C.point_signed_z n
  rw [← heq] at hcy hcz
  change (n : ℤ) ≤ C.sz * (x.val 2 - 1) at hcz
  have hsy : C.sy = 1 := by
    rcases C.sy_unit with h | h
    · exact h
    · rw [h] at hcy
      omega
  have hsz : C.sz = -1 := by
    rcases C.sz_unit with h | h
    · rw [h] at hcz
      omega
    · exact h
  exact hdir (column_small_owner_dir C hB hsy hsz)

theorem entryTetherFold_ne_canonicalRingColumn (p : ConstructionParameters) (i : Fin 3) (e : Fin 2)
    (k : ℕ) (hk : k ≤ p.bins) (s : Fin (p.entryTether k)) (n : ℕ) :
    (entryTetherFold p k hk).pos s ≠ (canonicalRingColumn p i e).point n :=
  Bcolumn_ne_positiveY_nonpositiveZ (canonicalRingColumn p i e) (canonicalRingColumn_owner_inB p i e)
    (by rw [canonicalRingColumn_dir]; exact canonicalRingFrame_small_ne_reserved i)
    _ (entryTetherFold_positive p k hk s).2 (entryTetherFold_nonpositiveZ p k hk s) n

theorem exitTetherFold_ne_canonicalRingColumn (p : ConstructionParameters) (i : Fin 3) (e : Fin 2)
    (k : ℕ) (hk : k ≤ p.bins) (s : Fin (p.exitTether k)) (n : ℕ) :
    (exitTetherFold p k hk).pos s ≠ (canonicalRingColumn p i e).point n :=
  Bcolumn_ne_positiveY_nonpositiveZ (canonicalRingColumn p i e) (canonicalRingColumn_owner_inB p i e)
    (by rw [canonicalRingColumn_dir]; exact canonicalRingFrame_small_ne_reserved i)
    _ (exitTetherFold_positive p k hk s).2 (exitTetherFold_nonpositiveZ p k hk s) n

theorem tetherFold_ne_canonicalRingColumn (p : ConstructionParameters) (i : Fin 3) (e : Fin 2)
    (t : TetherIndex p) (s : Fin (tetherCount p t)) (n : ℕ) :
    (tetherFold p t).pos s ≠ (canonicalRingColumn p i e).point n := by
  rcases t with ⟨b, k⟩
  cases b
  · exact entryTetherFold_ne_canonicalRingColumn p i e k.val (Nat.le_of_lt_succ k.isLt) s n
  · exact exitTetherFold_ne_canonicalRingColumn p i e k.val (Nat.le_of_lt_succ k.isLt) s n

theorem separatorFold_ne_canonicalRingColumn (p : ConstructionParameters) (i : Fin 3) (e : Fin 2)
    (k : ℕ) (hk : k ≤ p.bins) (s : Fin (p.separatorWord k).length) (n : ℕ) :
    (separatorFold p k hk).pos s ≠ (canonicalRingColumn p i e).point n := by
  have hm : 30 ≤ p.side := by have h := p.side_ge; omega
  apply separatorFold_property p k hk (fun x => x ≠ (canonicalRingColumn p i e).point n) _ _ _ _ _ s
  · intro j
    exact edgeDimerFold_ne_other_ringTerminalColumn p.side hm (canonicalRingFrame i) entryEdgeFrame
      (canonicalRingFrame_small_ne_reserved i) (6 * (k + 1)) 0 false (separatorEntry_room p k hk)
      (canonicalRingColumn p i e) (canonicalRingColumn_owner_alternative p i e) j n
  · intro j
    rw [entryTetherWordFold_pos]
    exact entryTetherFold_ne_canonicalRingColumn p i e k hk _ n
  · intro j
    exact edgeDimerFold_ne_other_ringTerminalColumn p.side hm (canonicalRingFrame i) trackEdgeFrame
      (canonicalRingFrame_small_ne_reserved i) (2 * p.separatorIndex k) 1 true (separatorCenter_room p k hk)
      (canonicalRingColumn p i e) (canonicalRingColumn_owner_alternative p i e) j n
  · intro j
    rw [exitTetherWordFold_pos]
    exact exitTetherFold_ne_canonicalRingColumn p i e k hk _ n
  · intro j
    exact edgeDimerFold_ne_other_ringTerminalColumn p.side hm (canonicalRingFrame i) exitEdgeFrame
      (canonicalRingFrame_small_ne_reserved i) (10 * p.exitSlot k + 6) 2 true (separatorExit_room p k)
      (canonicalRingColumn p i e) (canonicalRingColumn_owner_alternative p i e) j n

private theorem capped_positions {a b : ℕ} (f : Fold tetrahedralLattice a) (g : Fold tetrahedralLattice b)
    (c d : Site) (hsites : foldSites f = ({c} ∪ foldSites g) ∪ {d}) (P : Site → Prop)
    (hc : P c) (hg : ∀ i, P (g.pos i)) (hd : P d) (i : Fin a) : P (f.pos i) := by
  have hmem := (mem_foldSites f _).mpr ⟨i, rfl⟩
  rw [hsites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · rw [h]
    exact hc
  · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
    rw [← hj]
    exact hg j
  · rw [h]
    exact hd

theorem canonicalSeparatorPiece_ne_ringColumn (p : ConstructionParameters) (i : Fin 3) (e : Fin 2)
    (k : Fin (p.bins + 1)) (s : Fin (canonicalSeparatorPiece p k).word.length) (n : ℕ) :
    (canonicalSeparatorPiece p k).fold.pos s ≠ (canonicalRingColumn p i e).point n := by
  have hk : k.val ≤ p.bins := by have h := k.isLt; omega
  apply capped_positions
    (cappedSeparatorFold p k.val hk (entryLocalColumn p (some k)) (exitCapColumn p k.val hk) rfl
      (exitCapColumn_owner p k.val hk))
    (separatorFold p k.val hk) (entryLocalColumn p (some k)).seed (exitCapColumn p k.val hk).seed
    (cappedSeparatorFold_sites p k.val hk _ _ rfl (exitCapColumn_owner p k.val hk))
    (fun x => x ≠ (canonicalRingColumn p i e).point n) _ _ _ s
  · exact (ringTerminalColumn_ne_other_edge_column p.side (by have h := p.side_ge; omega)
      (canonicalRingFrame i) entryEdgeFrame (canonicalRingFrame_small_ne_reserved i)
      (canonicalRingColumn p i e) (entryLocalColumn p (some k)) (canonicalRingColumn_owner_alternative p i e)
      (6 * (k.val + 1)) rfl n 0).symm
  · intro j
    exact separatorFold_ne_canonicalRingColumn p i e k.val hk j n
  · exact (ringTerminalColumn_ne_other_edge_column p.side (by have h := p.side_ge; omega)
      (canonicalRingFrame i) exitEdgeFrame (canonicalRingFrame_small_ne_reserved i)
      (canonicalRingColumn p i e) (exitCapColumn p k.val hk) (canonicalRingColumn_owner_alternative p i e)
      _ (exitCapColumn_owner p k.val hk) n 0).symm

end ProteinFolding.Tetrahedral.NearField
