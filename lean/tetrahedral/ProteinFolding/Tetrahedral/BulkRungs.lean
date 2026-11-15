import ProteinFolding.Tetrahedral.BulkFoliation
import ProteinFolding.Tetrahedral.Layers

/-! The rung graph has degree two, including its bends. -/

namespace ProteinFolding.Tetrahedral

theorem bondVector_yz_injective :
    Function.Injective (fun d : Fin 4 => (bondVector d 1, bondVector d 2)) := by decide

theorem adjacent_yz_ext {p q r : Site} (hq : tetrahedralLattice.Adj p q)
    (hr : tetrahedralLattice.Adj p r) (hy : q.val 1 = r.val 1) (hz : q.val 2 = r.val 2) : q = r := by
  obtain ⟨d, rfl⟩ := (adj_iff_exists_step p q).mp hq
  obtain ⟨e, rfl⟩ := (adj_iff_exists_step p r).mp hr
  have hde : d = e := by
    apply bondVector_yz_injective
    change (bondVector d 1, bondVector d 2) = (bondVector e 1, bondVector e 2)
    by_cases hp : InASublattice p.val
    · rw [step_val_of_A p hp d, step_val_of_A p hp e] at hy hz
      exact Prod.ext (by dsimp at hy; omega) (by dsimp at hz; omega)
    · have hpB := (inB_iff_not_inA p).mpr hp
      rw [step_val_of_B p hpB d, step_val_of_B p hpB e] at hy hz
      exact Prod.ext (by dsimp at hy; omega) (by dsimp at hz; omega)
  rw [hde]

theorem abs_add_signed_unit (s x d : ℤ) (hs : s = 1 ∨ s = -1)
    (hx : 0 < s * x) (hd : d = 1 ∨ d = -1) :
    |x + d| = |x| + s * d := by
  rcases hs with rfl | rfl <;> rcases hd with rfl | rfl
  · rw [abs_of_nonneg (by omega : 0 ≤ x + 1), abs_of_nonneg (by omega : 0 ≤ x)]
    omega
  · rw [abs_of_nonneg (by omega : 0 ≤ x + -1), abs_of_nonneg (by omega : 0 ≤ x)]
    omega
  · rw [abs_of_nonpos (by omega : x + 1 ≤ 0), abs_of_nonpos (by omega : x ≤ 0)]
    omega
  · rw [abs_of_nonpos (by omega : x + -1 ≤ 0), abs_of_nonpos (by omega : x ≤ 0)]
    omega

def bulkRungNeighbours (m : ℕ) (p : Site) : Finset Site :=
  (neighbours p).filter (fun q => bulkRho m q ≠ bulkRho m p)

theorem bulk_adj_deltas (m : ℕ) {p q : Site} (hq : tetrahedralLattice.Adj p q) :
    (bulkY m q - bulkY m p = 1 ∨ bulkY m q - bulkY m p = -1) ∧
      (bulkZ q - bulkZ p = 1 ∨ bulkZ q - bulkZ p = -1) := by
  have hy := adj_coordinate hq 1
  have hz := adj_coordinate hq 2
  dsimp [bulkY, bulkZ]
  constructor <;> omega

theorem bulkRungNeighbours_open (m : ℕ) (p : Site) (sy sz : ℤ)
    (hsy : sy = 1 ∨ sy = -1) (hsz : sz = 1 ∨ sz = -1)
    (hy : 0 < sy * bulkY m p) (hz : 0 < sz * bulkZ p) :
    bulkRungNeighbours m p = {bulkArmNext sy sz p, bulkArmNext (-sy) (-sz) p} := by
  have hnegsy : -sy = 1 ∨ -sy = -1 := by omega
  have hnegsz : -sz = 1 ∨ -sz = -1 := by omega
  ext q
  simp only [bulkRungNeighbours, Finset.mem_filter, mem_neighbours,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hq, hrung⟩
    have hd := bulk_adj_deltas m hq
    let dy := bulkY m q - bulkY m p
    let dz := bulkZ q - bulkZ p
    have hdy : dy = 1 ∨ dy = -1 := hd.1
    have hdz : dz = 1 ∨ dz = -1 := hd.2
    have hyabs := abs_add_signed_unit sy (bulkY m p) dy hsy hy hdy
    have hzabs := abs_add_signed_unit sz (bulkZ p) dz hsz hz hdz
    have hqy : bulkY m q = bulkY m p + dy := by dsimp [dy]; omega
    have hqz : bulkZ q = bulkZ p + dz := by dsimp [dz]; omega
    have hdelta : (dy = sy ∧ dz = sz) ∨ (dy = -sy ∧ dz = -sz) := by
      unfold bulkRho at hrung
      rw [hqy, hqz, hyabs, hzabs] at hrung
      rcases hsy with rfl | rfl <;> rcases hsz with rfl | rfl <;> omega
    rcases hdelta with ⟨hdy, hdz⟩ | ⟨hdy, hdz⟩
    · left
      have hc := bulkArmNext_coordinates sy sz hsy hsz p
      apply adjacent_yz_ext hq (bulkArmNext_adj sy sz p)
      · dsimp [dy, bulkY] at hdy
        rw [hc.1]
        omega
      · dsimp [dz, bulkZ] at hdz
        rw [hc.2.1]
        omega
    · right
      have hc := bulkArmNext_coordinates (-sy) (-sz) hnegsy hnegsz p
      apply adjacent_yz_ext hq (bulkArmNext_adj (-sy) (-sz) p)
      · dsimp [dy, bulkY] at hdy
        rw [hc.1]
        omega
      · dsimp [dz, bulkZ] at hdz
        rw [hc.2.1]
        omega
  · rintro (rfl | rfl)
    · refine ⟨bulkArmNext_adj sy sz p, ?_⟩
      have hc := bulkArmPoint_rho_alpha m sy sz hsy hsz p (by omega) (by omega) 1
      change bulkRho m (bulkArmPoint sy sz p 1) ≠ bulkRho m p
      omega
    · refine ⟨bulkArmNext_adj (-sy) (-sz) p, ?_⟩
      have hc := bulkArmNext_coordinates (-sy) (-sz) hnegsy hnegsz p
      have hyabs := abs_add_signed_unit sy (bulkY m p) (-sy) hsy hy hnegsy
      have hzabs := abs_add_signed_unit sz (bulkZ p) (-sz) hsz hz hnegsz
      have hY : bulkY m (bulkArmNext (-sy) (-sz) p) = bulkY m p + -sy := by
        dsimp [bulkY]
        rw [hc.1]
        omega
      have hZ : bulkZ (bulkArmNext (-sy) (-sz) p) = bulkZ p + -sz := by
        dsimp [bulkZ]
        rw [hc.2.1]
        omega
      unfold bulkRho
      rw [hY, hZ, hyabs, hzabs]
      rcases hsy with rfl | rfl <;> rcases hsz with rfl | rfl <;> omega

theorem bulkRungNeighbours_bendY (m : ℕ) (p : Site) (sz : ℤ)
    (hsz : sz = 1 ∨ sz = -1) (hy : bulkY m p = 0) (hz : 0 < sz * bulkZ p) :
    bulkRungNeighbours m p = {bulkArmNext 1 sz p, bulkArmNext (-1) sz p} := by
  ext q
  simp only [bulkRungNeighbours, Finset.mem_filter, mem_neighbours,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hq, hrung⟩
    have hd := bulk_adj_deltas m hq
    let dz := bulkZ q - bulkZ p
    have hdz : dz = 1 ∨ dz = -1 := hd.2
    have hzabs := abs_add_signed_unit sz (bulkZ p) dz hsz hz hdz
    have hqz : bulkZ q = bulkZ p + dz := by dsimp [dz]; omega
    have hqabs : |bulkY m q| = 1 := by
      rcases hd.1 with h | h
      · have he : bulkY m q = 1 := by omega
        rw [he]
        decide
      · have he : bulkY m q = -1 := by omega
        rw [he]
        decide
    have hdz' : dz = sz := by
      unfold bulkRho at hrung
      rw [hy, abs_zero, hqabs, hqz, hzabs] at hrung
      rcases hsz with rfl | rfl <;> omega
    rcases hd.1 with hdy | hdy
    · left
      have hc := bulkArmNext_coordinates 1 sz (Or.inl rfl) hsz p
      apply adjacent_yz_ext hq (bulkArmNext_adj 1 sz p)
      · dsimp [bulkY] at hdy
        rw [hc.1]
        omega
      · dsimp [dz, bulkZ] at hdz'
        rw [hc.2.1]
        omega
    · right
      have hc := bulkArmNext_coordinates (-1) sz (Or.inr rfl) hsz p
      apply adjacent_yz_ext hq (bulkArmNext_adj (-1) sz p)
      · dsimp [bulkY] at hdy
        rw [hc.1]
        omega
      · dsimp [dz, bulkZ] at hdz'
        rw [hc.2.1]
        omega
  · rintro (rfl | rfl)
    · refine ⟨bulkArmNext_adj 1 sz p, ?_⟩
      have hc := (bulkArmPoint_rho_alpha m 1 sz (Or.inl rfl) hsz p (by omega) (by omega) 1).1
      change bulkRho m (bulkArmPoint 1 sz p 1) ≠ bulkRho m p
      omega
    · refine ⟨bulkArmNext_adj (-1) sz p, ?_⟩
      have hc := (bulkArmPoint_rho_alpha m (-1) sz (Or.inr rfl) hsz p (by omega) (by omega) 1).1
      change bulkRho m (bulkArmPoint (-1) sz p 1) ≠ bulkRho m p
      omega

theorem bulkRungNeighbours_bendZ (m : ℕ) (p : Site) (sy : ℤ)
    (hsy : sy = 1 ∨ sy = -1) (hz : bulkZ p = 0) (hy : 0 < sy * bulkY m p) :
    bulkRungNeighbours m p = {bulkArmNext sy 1 p, bulkArmNext sy (-1) p} := by
  ext q
  simp only [bulkRungNeighbours, Finset.mem_filter, mem_neighbours,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hq, hrung⟩
    have hd := bulk_adj_deltas m hq
    let dy := bulkY m q - bulkY m p
    have hdy : dy = 1 ∨ dy = -1 := hd.1
    have hyabs := abs_add_signed_unit sy (bulkY m p) dy hsy hy hdy
    have hqy : bulkY m q = bulkY m p + dy := by dsimp [dy]; omega
    have hqabs : |bulkZ q| = 1 := by
      rcases hd.2 with h | h
      · have he : bulkZ q = 1 := by omega
        rw [he]
        decide
      · have he : bulkZ q = -1 := by omega
        rw [he]
        decide
    have hdy' : dy = sy := by
      unfold bulkRho at hrung
      rw [hz, abs_zero, hqabs, hqy, hyabs] at hrung
      rcases hsy with rfl | rfl <;> omega
    rcases hd.2 with hdz | hdz
    · left
      have hc := bulkArmNext_coordinates sy 1 hsy (Or.inl rfl) p
      apply adjacent_yz_ext hq (bulkArmNext_adj sy 1 p)
      · dsimp [dy, bulkY] at hdy'
        rw [hc.1]
        omega
      · dsimp [bulkZ] at hdz
        rw [hc.2.1]
        omega
    · right
      have hc := bulkArmNext_coordinates sy (-1) hsy (Or.inr rfl) p
      apply adjacent_yz_ext hq (bulkArmNext_adj sy (-1) p)
      · dsimp [dy, bulkY] at hdy'
        rw [hc.1]
        omega
      · dsimp [bulkZ] at hdz
        rw [hc.2.1]
        omega
  · rintro (rfl | rfl)
    · refine ⟨bulkArmNext_adj sy 1 p, ?_⟩
      have hc := (bulkArmPoint_rho_alpha m sy 1 hsy (Or.inl rfl) p (by omega) (by omega) 1).1
      change bulkRho m (bulkArmPoint sy 1 p 1) ≠ bulkRho m p
      omega
    · refine ⟨bulkArmNext_adj sy (-1) p, ?_⟩
      have hc := (bulkArmPoint_rho_alpha m sy (-1) hsy (Or.inr rfl) p (by omega) (by omega) 1).1
      change bulkRho m (bulkArmPoint sy (-1) p 1) ≠ bulkRho m p
      omega

theorem bulkRungNeighbours_card (m : ℕ) (p : Site) : (bulkRungNeighbours m p).card = 2 := by
  have hne := bulk_coordinates_not_both_zero m p
  by_cases hy : bulkY m p = 0
  · have hz : bulkZ p ≠ 0 := by omega
    let sz : ℤ := if 0 < bulkZ p then 1 else -1
    have hsz : sz = 1 ∨ sz = -1 := by dsimp [sz]; split_ifs <;> omega
    have hzp : 0 < sz * bulkZ p := by dsimp [sz]; split_ifs <;> omega
    rw [bulkRungNeighbours_bendY m p sz hsz hy hzp]
    have hc1 := (bulkArmNext_coordinates 1 sz (Or.inl rfl) hsz p).1
    have hc2 := (bulkArmNext_coordinates (-1) sz (Or.inr rfl) hsz p).1
    have hdiff : bulkArmNext 1 sz p ≠ bulkArmNext (-1) sz p := by
      intro he
      have hh := congrArg (fun q : Site => q.val 1) he
      dsimp only at hh
      rw [hc1, hc2] at hh
      omega
    simp [hdiff]
  · by_cases hz : bulkZ p = 0
    · let sy : ℤ := if 0 < bulkY m p then 1 else -1
      have hsy : sy = 1 ∨ sy = -1 := by dsimp [sy]; split_ifs <;> omega
      have hyp : 0 < sy * bulkY m p := by dsimp [sy]; split_ifs <;> omega
      rw [bulkRungNeighbours_bendZ m p sy hsy hz hyp]
      have hc1 := (bulkArmNext_coordinates sy 1 hsy (Or.inl rfl) p).2.1
      have hc2 := (bulkArmNext_coordinates sy (-1) hsy (Or.inr rfl) p).2.1
      have hdiff : bulkArmNext sy 1 p ≠ bulkArmNext sy (-1) p := by
        intro he
        have hh := congrArg (fun q : Site => q.val 2) he
        dsimp only at hh
        rw [hc1, hc2] at hh
        omega
      simp [hdiff]
    · let sy : ℤ := if 0 < bulkY m p then 1 else -1
      let sz : ℤ := if 0 < bulkZ p then 1 else -1
      have hsy : sy = 1 ∨ sy = -1 := by dsimp [sy]; split_ifs <;> omega
      have hsz : sz = 1 ∨ sz = -1 := by dsimp [sz]; split_ifs <;> omega
      have hyp : 0 < sy * bulkY m p := by dsimp [sy]; split_ifs <;> omega
      have hzp : 0 < sz * bulkZ p := by dsimp [sz]; split_ifs <;> omega
      rw [bulkRungNeighbours_open m p sy sz hsy hsz hyp hzp]
      have hc1 := (bulkArmNext_coordinates sy sz hsy hsz p).1
      have hc2 := (bulkArmNext_coordinates (-sy) (-sz) (by omega) (by omega) p).1
      have hdiff : bulkArmNext sy sz p ≠ bulkArmNext (-sy) (-sz) p := by
        intro he
        have hh := congrArg (fun q : Site => q.val 1) he
        dsimp only at hh
        rw [hc1, hc2] at hh
        rcases hsy with hs | hs <;> rw [hs] at hh <;> omega
      simp [hdiff]

end ProteinFolding.Tetrahedral
