import ProteinFolding.Tetrahedral.ReductionTM2BulkPredicateCorrect
import ProteinFolding.Tetrahedral.PathCoverExtraction

/-! An explicit coordinate inverse used only in the semantic proof of the
index walk. The machine scans natural indices directly and never receives a
component, a fold, or this inverse as an oracle. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkIndexModel

def coordinateIndex (m : ℕ) (p : Coordinates) : ℕ :=
  Grid.index (Grid.base m) (p 0 + (2 * (m : ℤ) + 1)).toNat (p 1 + 3).toNat
    (p 2 + (2 * (m : ℤ) + 1)).toNat

theorem coordinateIndex_spec {m : ℕ} {p : Site} (hp : InOctahedron m p) :
    coordinateIndex m p.val < Grid.count m ∧ Grid.point m (coordinateIndex m p.val) = p.val := by
  let x := (p.val 0 + (2 * (m : ℤ) + 1)).toNat
  let y := (p.val 1 + 3).toNat
  let z := (p.val 2 + (2 * (m : ℤ) + 1)).toNat
  have hx0 := inOctahedron_coordinate_bound hp 0
  have hy0 := inOctahedron_coordinate_bound hp 1
  have hz0 := inOctahedron_coordinate_bound hp 2
  simp [octCentre, octRadius] at hx0 hy0 hz0
  have hx : x < Grid.base m := by dsimp [x, Grid.base]; omega
  have hy : y < Grid.base m := by dsimp [y, Grid.base]; omega
  have hz : z < Grid.base m := by dsimp [z, Grid.base]; omega
  refine ⟨Grid.index_bound _ _ _ _ hx hy hz, ?_⟩
  have hd := Grid.digits_index (Grid.base m) x y z (Grid.base_positive m) hx hy hz
  change Grid.point m (Grid.index (Grid.base m) x y z) = p.val
  unfold Grid.point
  rw [hd]
  funext k
  fin_cases k <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals dsimp [x, y, z]; omega

def index (m : ℕ) (p : BulkVertex m) : ℕ := coordinateIndex m p.val.val

theorem point_index (m : ℕ) (p : BulkVertex m) : Grid.point m (index m p) = p.val.val :=
  (coordinateIndex_spec ((mem_octahedron m p.val).1 (Finset.mem_sdiff.mp p.property).1)).2

theorem index_bound (m : ℕ) (p : BulkVertex m) : index m p < Grid.count m :=
  (coordinateIndex_spec ((mem_octahedron m p.val).1 (Finset.mem_sdiff.mp p.property).1)).1

theorem index_injective (m : ℕ) : Function.Injective (index m) := by
  intro p q he
  apply Subtype.ext
  apply Subtype.ext
  rw [← point_index m p, ← point_index m q, he]

theorem graph_model (m : ℕ) (u : BulkVertex m) (k : ℕ) (_hk : k < Grid.count m) :
    BulkPredicate.predicate (m, (index m u, k)) = true ↔
      ∃ w : BulkVertex m, (bulkFiniteGraph m).Adj u w ∧ index m w = k := by
  constructor
  · intro h
    obtain ⟨hs, ht, hadj⟩ := (BulkPredicate.guarded_correct m (index m u) k).1 h
    have hu : (⟨Grid.point m (index m u), hs⟩ : Site) = u.val := Subtype.ext (point_index m u)
    rw [hu] at hadj
    let w : BulkVertex m := ⟨⟨Grid.point m k, ht⟩, (bulkCoverGraph_support m hadj).2⟩
    refine ⟨w, hadj, ?_⟩
    apply Grid.point_injective m
    exact point_index m w
  · rintro ⟨w, hw, he⟩
    apply (BulkPredicate.correct m (index m u) k u.val w.val (point_index m u) ?_).2 hw
    rw [← he]
    exact point_index m w

end ProteinFolding.Tetrahedral.ReductionTM2.BulkIndexModel
