import ProteinFolding.Tetrahedral.NearFieldTerminalColumn
import ProteinFolding.Tetrahedral.NearFieldTetherFamily
import ProteinFolding.Tetrahedral.NearFieldPPPCanonicalColumns
import ProteinFolding.Tetrahedral.BulkEdgeReversal

/-! The terminal corner's complete column avoids both actual tether families.
Its reversed-entry description also supplies the B-corner PPP interface. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem terminalColumn_reverse_entry_owner (p : ConstructionParameters) :
    (terminalColumn p).owner = octEdgeZigzag p.side (bulkReverseEdgeFrame entryEdgeFrame) 1 := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have h := bulkEdgeAnchor_odd_reverse hm entryEdgeFrame (p.side - 2) (by have h := p.side_ge; omega)
  rw [bulkEdgeAnchor_next, bulkEdgeAnchor_next] at h
  have hi : 2 * (p.side - 2) + 1 = 2 * p.side - 3 := by have h := p.side_ge; omega
  have hr : p.side - 2 - (p.side - 2) = 0 := Nat.sub_self _
  rw [hi, hr] at h
  exact (terminalColumn_owner p).trans h

theorem edgePPPFold_ne_terminalColumn (p : ConstructionParameters) (F : OctEdgeFrame) (r : ℕ)
    (hr : r + 2 < 2 * p.side - 1)
    (hp : (terminalColumn p).owner ≠ octEdgeZigzag p.side F r)
    (hq : (terminalColumn p).owner ≠ octEdgeZigzag p.side F (r + 2)) (s : Fin 3) (n : ℕ) :
    (edgePPPFold p.side F r).pos s ≠ (terminalColumn p).point n :=
  edgePPPFold_ne_Bcorner_column p.side (by have h := p.side_ge; omega) F
    (bulkReverseEdgeFrame entryEdgeFrame) r hr (terminalColumn p) (terminalColumn_reverse_entry_owner p) hp hq s n

private theorem faceColumn_ne_terminalColumn (p : ConstructionParameters) (a b c : ℕ)
    (hs : a + b + c + 2 = p.side) (hpositive : 1 ≤ a ∨ 1 ≤ c) (n r : ℕ) :
    (faceDanglingColumn p.side a b c hs).point n ≠ (terminalColumn p).point r := by
  intro heq
  have hseed := DanglingColumn.seeds_eq_of_point_eq
    (faceDanglingColumn p.side a b c hs) (terminalColumn p) heq
  have howner := column_owner_eq_of_seed_eq (faceDanglingColumn p.side a b c hs) (terminalColumn p) hseed
  rcases hpositive with ha | hc
  · have hz := congrArg (fun x : Site => x.val 2) howner
    dsimp [terminalColumn, faceDanglingColumn, faceSurfaceSite, faceSurfaceCoordinates] at hz
    omega
  · have hx := congrArg (fun x : Site => x.val 0) howner
    dsimp [terminalColumn, faceDanglingColumn, faceSurfaceSite, faceSurfaceCoordinates] at hx
    omega

theorem borrowedPoint_ne_terminalColumn (p : ConstructionParameters) (a b : ℕ)
    (hs : a + b + 0 + 2 = p.side) (ha : 1 ≤ a) (n r : ℕ) :
    borrowedPoint p.side a b 0 hs ha n ≠ (terminalColumn p).point r := by
  cases n with
  | zero => exact faceColumn_ne_terminalColumn p a b 0 hs (Or.inl ha) 0 r
  | succ n => exact faceColumn_ne_terminalColumn p (a - 1) b 1 (by omega) (Or.inr (by omega)) (n + 1) r

theorem entryRow_ne_terminalColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (entryRowCount p k)) (n : ℕ) :
    (entryRowFold p k hk).pos i ≠ (terminalColumn p).point n := by
  have hj := p.tether_skin_bounds k hk
  have ht := p.entry_column_triangle_room k hk
  have hf := p.family_side_bound
  unfold entryRowFold rowCBFold
  apply glue_property _ _ _ _ _ _ (fun x => x ≠ (terminalColumn p).point n) _ _ i
  · intro r heq
    have hy := congrArg (fun x : Site => x.val 1) heq
    have hterminal := (terminalColumn_point_bounds p n).2.2.1
    dsimp [rowFold, faceRowPoint, faceRowCoordinates, octRadius] at hy
    dsimp [octRadius] at hterminal
    omega
  · intro r heq
    have hfree := faceRowB_avoids_columns p.side (p.entrySkin k)
      (p.side - 3 - 3 * (k + 1) + p.entrySkin k + (3 * (k + 1) + 1))
      (3 * (k + 1) + p.entrySkin k - (3 * (k + 1) + 1)) 1
      (by have h := entryRow_faceEquation p k hk; omega) (by omega) (by omega) (by omega)
      r.val (by have h := r.isLt; have hr := p.separator_room k hk; omega)
    exact hfree ⟨terminalColumn p, n, heq.symm⟩

theorem entryTetherFold_ne_terminalColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.entryTether k)) (n : ℕ) :
    (entryTetherFold p k hk).pos i ≠ (terminalColumn p).point n := by
  apply entryTetherFold_property p k hk (fun x => x ≠ (terminalColumn p).point n) _ _ _ i
  · intro r
    exact borrowedPoint_ne_terminalColumn p (entryAnchorA p k) (3 * (k + 1))
      (entryAnchor_equation p k hk) (entryAnchor_positive p k hk) r.val n
  · exact fun r => entryRow_ne_terminalColumn p k hk r n
  · intro r
    exact faceColumn_ne_terminalColumn p (p.side - 2 - p.separatorIndex k) 0 (p.separatorIndex k)
      (by have h := p.separator_room k hk; omega)
      (Or.inr (by have h := separatorIndex_ge_two p k; omega)) r.rev.val n

theorem exitTetherFold_ne_terminalColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.exitTether k)) (n : ℕ) :
    (exitTetherFold p k hk).pos i ≠ (terminalColumn p).point n := by
  apply exitTetherFold_property p k hk (fun x => x ≠ (terminalColumn p).point n) _ _ _ i
  · intro r
    exact faceColumn_ne_terminalColumn p (p.side - 3 - p.separatorIndex k) 0 (p.separatorIndex k + 1)
      (by have h := p.separator_room k hk; omega) (Or.inr (by omega)) r.val n
  · intro r
    exact exitRow_ne_column p k hk (terminalColumn p) r n
  · intro r
    exact faceColumn_ne_terminalColumn p 0 (5 * p.exitSlot k + 3) (p.side - 5 - 5 * p.exitSlot k)
      (by have h := p.exit_column_triangle_room k; omega)
      (Or.inr (by have h := p.exit_column_triangle_room k; omega)) r.rev.val n

theorem tetherFold_ne_terminalColumn (p : ConstructionParameters) (t : TetherIndex p)
    (i : Fin (tetherCount p t)) (n : ℕ) : (tetherFold p t).pos i ≠ (terminalColumn p).point n := by
  rcases t with ⟨b, k⟩
  cases b
  · exact entryTetherFold_ne_terminalColumn p k.val (Nat.le_of_lt_succ k.isLt) i n
  · exact exitTetherFold_ne_terminalColumn p k.val (Nat.le_of_lt_succ k.isLt) i n

end ProteinFolding.Tetrahedral.NearField
