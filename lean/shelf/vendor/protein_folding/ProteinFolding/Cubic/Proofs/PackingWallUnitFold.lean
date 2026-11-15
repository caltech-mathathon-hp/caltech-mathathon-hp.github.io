import ProteinFolding.Cubic.Proofs.PackingWallBlocks

/-! A complete self-avoiding fold of one literal U wall unit. Its two face
rows cross between the rails; its three E paths occupy the prescribed rail
intervals. Exterior P disjointness is derived from distinct H owners. -/

namespace ProteinFolding.CubicPackingWalls

open CubicCertificates CubicPacking CubicPackingLift CubicPackingRouting

def unitWord (d A : ℕ) : Sequence :=
  edgeWord A ++ (faceWord d ++ (edgeWord (2 * A + 2) ++ (faceWord d ++ edgeWord A)))

def unitOwners (d A : ℕ) (top : ℤ) :
    Fin (A + (d + ((2 * A + 2) + (d + A)))) → Site :=
  Fin.append (verticalFold (d + 1) (top - A + 1) true A).pos
    (Fin.append (horizontalFold d top false).pos
      (Fin.append (verticalFold 0 top false (2 * A + 2)).pos
        (Fin.append (horizontalFold d (top - (2 * A + 2) + 1) true).pos
          (verticalFold (d + 1) (top - (2 * A + 2) + 1) true A).pos)))

theorem unitWord_fold_exists (d A : ℕ) (hd : 0 < d) (hA : 0 < A)
    (hdeven : 2 ∣ d) (hAeven : A % 2 = 0) (top : ℤ)
    (hTop : (2 * A + 2 : ℕ) ≤ top ∧ top ≤ d) :
    ∃ f : Fold cubicLattice (unitWord d A).length,
      AttachedTo (fun _ => 0) (d + 2) f (unitOwners d A top) ∧
      hydrophobicSites (unitWord d A) f = Set.range (unitOwners d A top) ∧
      HasEnds f (point (d + 1) (top - A + 1) (-1))
        (point (d + 1) (top - A - 2) (-1)) := by
  let B := 2 * A + 2
  let bottom : ℤ := top - B + 1
  let p₁ := (verticalFold (d + 1) (top - A + 1) true A).pos
  let p₂ := (horizontalFold d top false).pos
  let p₃ := (verticalFold 0 top false B).pos
  let p₄ := (horizontalFold d bottom true).pos
  let p₅ := (verticalFold (d + 1) bottom true A).pos
  have hB : 0 < B := by dsimp [B]; omega
  have hBeven : B % 2 = 0 := by dsimp [B]; omega
  have hrows₁ : ∀ i : Fin A,
      0 ≤ lineRow (top - A + 1) true i.val ∧ lineRow (top - A + 1) true i.val ≤ d + 1 := by
    intro i
    have hi := i.isLt
    dsimp [lineRow]
    omega
  have hrows₃ : ∀ i : Fin B, 0 ≤ lineRow top false i.val ∧ lineRow top false i.val ≤ d + 1 := by
    intro i
    have hi := i.isLt
    dsimp [B] at hi
    dsimp [lineRow]
    omega
  have hrows₅ : ∀ i : Fin A,
      0 ≤ lineRow bottom true i.val ∧ lineRow bottom true i.val ≤ d + 1 := by
    intro i
    have hi := i.isLt
    dsimp [lineRow, bottom, B]
    omega
  obtain ⟨f₁, ha₁, hs₁, he₁⟩ := railWord_ends_exists d A true true (top - A + 1) hA hAeven hrows₁
  obtain ⟨f₃, ha₃, hs₃, he₃⟩ := railWord_ends_exists d B false false top hB hBeven hrows₃
  obtain ⟨f₅, ha₅, hs₅, he₅⟩ := railWord_ends_exists d A true true bottom hA hAeven hrows₅
  let f₂ := faceLineWordFold d top false hdeven
  let f₄ := faceLineWordFold d bottom true hdeven
  have ha₂ := faceLineWord_attached d top false hdeven (by omega)
  have ha₄ := faceLineWord_attached d bottom true hdeven (by dsimp [bottom, B]; omega)
  have hs₂ : hydrophobicSites (faceWord d) f₂ = Set.range p₂ :=
    faceLift_hydrophobicSites_eq d hdeven (horizontalFold d top false) (fun _ => rfl)
  have hs₄ : hydrophobicSites (faceWord d) f₄ = Set.range p₄ :=
    faceLift_hydrophobicSites_eq d hdeven (horizontalFold d bottom true) (fun _ => rfl)
  have he₂ := faceLineWord_hasEnds d top false hd hdeven
  have he₄ := faceLineWord_hasEnds d bottom true hd hdeven
  have hend₁ : lineRow (top - A + 1) true (A - 1) = top := by dsimp [lineRow]; omega
  have hend₃ : lineRow top false (B - 1) = bottom := by dsimp [lineRow, bottom]; omega
  have hend₅ : lineRow bottom true (A - 1) = top - A - 2 := by dsimp [lineRow, bottom, B]; omega
  rw [hend₁] at he₁
  rw [hend₃] at he₃
  rw [hend₅] at he₅
  have h₁₂ : ∀ i j, p₁ i ≠ p₂ j := vertical_horizontal_disjoint d A (d + 1) _ _ true false (Or.inr rfl)
  have h₁₃ : ∀ i j, p₁ i ≠ p₃ j := vertical_rails_disjoint A B (d + 1) 0 _ _ true false (by omega)
  have h₁₄ : ∀ i j, p₁ i ≠ p₄ j := vertical_horizontal_disjoint d A (d + 1) _ _ true true (Or.inr rfl)
  have h₁₅ : ∀ i j, p₁ i ≠ p₅ j := by
    intro i j he
    have hi := i.isLt
    have hj := j.isLt
    have hy := congrFun he 1
    change top - A + 1 + i.val = bottom + j.val at hy
    dsimp [bottom, B] at hy
    omega
  have h₂₃ : ∀ i j, p₂ i ≠ p₃ j := fun i j => Ne.symm
    (vertical_horizontal_disjoint d B 0 _ _ false false (Or.inl rfl) j i)
  have h₂₄ : ∀ i j, p₂ i ≠ p₄ j := horizontal_rows_disjoint d top bottom false true (by dsimp [bottom]; omega)
  have h₂₅ : ∀ i j, p₂ i ≠ p₅ j := fun i j => Ne.symm
    (vertical_horizontal_disjoint d A (d + 1) _ _ true false (Or.inr rfl) j i)
  have h₃₄ : ∀ i j, p₃ i ≠ p₄ j := vertical_horizontal_disjoint d B 0 _ _ false true (Or.inl rfl)
  have h₃₅ : ∀ i j, p₃ i ≠ p₅ j := vertical_rails_disjoint B A 0 (d + 1) _ _ false true (by omega)
  have h₄₅ : ∀ i j, p₄ i ≠ p₅ j := fun i j => Ne.symm
    (vertical_horizontal_disjoint d A (d + 1) _ _ true true (Or.inr rfl) j i)
  have hlenE : 0 < (edgeWord A).length := by rw [edgeWord_length]; omega
  have hlenB : 0 < (edgeWord B).length := by rw [edgeWord_length]; omega
  have hlenF : 0 < (faceWord d).length := by rw [faceWord_length d hdeven]; omega
  have adj₁₂ : cubicLattice.Adj (point (railX d true) top (-1)) (point d top (-1)) := by
    change latticeDistance _ _ = 1
    rw [distance_eq]
    dsimp [point, railX]
    omega
  have adj₂₃ : cubicLattice.Adj (point 1 top (-1)) (point (railX d false) top (-1)) := by
    change latticeDistance _ _ = 1
    rw [distance_eq]
    dsimp [point, railX]
    simp
  have adj₃₄ : cubicLattice.Adj (point (railX d false) bottom (-1)) (point 1 bottom (-1)) := by
    change latticeDistance _ _ = 1
    rw [distance_eq]
    dsimp [point, railX]
    simp
  have adj₄₅ : cubicLattice.Adj (point d bottom (-1)) (point (railX d true) bottom (-1)) := by
    change latticeDistance _ _ = 1
    rw [distance_eq]
    dsimp [point, railX]
    omega
  let dis₄₅ := attached_folds_disjoint (fun _ => 0) (d + 2) f₄ f₅ p₄ p₅ ha₄ ha₅ h₄₅
  let seam₄₅ := hasEnds_seam f₄ f₅ he₄ he₅ adj₄₅
  let f₄₅ := Fold.appendWord f₄ f₅ dis₄₅ seam₄₅
  have ha₄₅ := appendWord_attached (fun _ => 0) (d + 2) f₄ f₅ dis₄₅ seam₄₅ p₄ p₅ ha₄ ha₅
  have hs₄₅ := appendWord_H_support f₄ f₅ dis₄₅ seam₄₅ p₄ p₅ hs₄ hs₅
  have he₄₅ := appendWord_hasEnds f₄ f₅ dis₄₅ seam₄₅ hlenF hlenE he₄ he₅
  let dis₃₄₅ := attached_folds_disjoint (fun _ => 0) (d + 2) f₃ f₄₅ p₃ (Fin.append p₄ p₅) ha₃ ha₄₅
    (append_owners_disjoint_right p₃ p₄ p₅ h₃₄ h₃₅)
  let seam₃₄₅ := hasEnds_seam f₃ f₄₅ he₃ he₄₅ adj₃₄
  let f₃₄₅ := Fold.appendWord f₃ f₄₅ dis₃₄₅ seam₃₄₅
  have ha₃₄₅ := appendWord_attached (fun _ => 0) (d + 2) f₃ f₄₅ dis₃₄₅ seam₃₄₅ _ _ ha₃ ha₄₅
  have hs₃₄₅ := appendWord_H_support f₃ f₄₅ dis₃₄₅ seam₃₄₅ _ _ hs₃ hs₄₅
  have he₃₄₅ := appendWord_hasEnds f₃ f₄₅ dis₃₄₅ seam₃₄₅ hlenB (by simp only [List.length_append]; omega) he₃ he₄₅
  let dis₂₃₄₅ := attached_folds_disjoint (fun _ => 0) (d + 2) f₂ f₃₄₅ p₂ (Fin.append p₃ (Fin.append p₄ p₅)) ha₂ ha₃₄₅
    (append_owners_disjoint_right p₂ p₃ _ h₂₃ (append_owners_disjoint_right p₂ p₄ p₅ h₂₄ h₂₅))
  let seam₂₃₄₅ := hasEnds_seam f₂ f₃₄₅ he₂ he₃₄₅ adj₂₃
  let f₂₃₄₅ := Fold.appendWord f₂ f₃₄₅ dis₂₃₄₅ seam₂₃₄₅
  have ha₂₃₄₅ := appendWord_attached (fun _ => 0) (d + 2) f₂ f₃₄₅ dis₂₃₄₅ seam₂₃₄₅ _ _ ha₂ ha₃₄₅
  have hs₂₃₄₅ := appendWord_H_support f₂ f₃₄₅ dis₂₃₄₅ seam₂₃₄₅ _ _ hs₂ hs₃₄₅
  have he₂₃₄₅ := appendWord_hasEnds f₂ f₃₄₅ dis₂₃₄₅ seam₂₃₄₅ hlenF (by simp only [List.length_append]; omega) he₂ he₃₄₅
  let dis := attached_folds_disjoint (fun _ => 0) (d + 2) f₁ f₂₃₄₅ p₁
    (Fin.append p₂ (Fin.append p₃ (Fin.append p₄ p₅))) ha₁ ha₂₃₄₅
    (append_owners_disjoint_right p₁ p₂ _ h₁₂
      (append_owners_disjoint_right p₁ p₃ _ h₁₃ (append_owners_disjoint_right p₁ p₄ p₅ h₁₄ h₁₅)))
  let seam := hasEnds_seam f₁ f₂₃₄₅ he₁ he₂₃₄₅ adj₁₂
  let f := Fold.appendWord f₁ f₂₃₄₅ dis seam
  refine ⟨f, ?_, ?_, ?_⟩
  · exact appendWord_attached (fun _ => 0) (d + 2) f₁ f₂₃₄₅ dis seam _ _ ha₁ ha₂₃₄₅
  · exact appendWord_H_support f₁ f₂₃₄₅ dis seam _ _ hs₁ hs₂₃₄₅
  · exact appendWord_hasEnds f₁ f₂₃₄₅ dis seam hlenE (by simp only [List.length_append]; omega) he₁ he₂₃₄₅

theorem unitWord_eq_wallUnit (q Q : ℕ) : unitWord (depth q Q) (alpha Q) = wallUnit q Q := by
  have hb : beta Q = 2 * alpha Q + 2 := by dsimp [beta, alpha]; omega
  simp only [unitWord, wallUnit, hb, List.append_assoc]

def wallTop (q Q : ℕ) (j : Fin q) : ℤ := (depth q Q : ℤ) - (j.val : ℤ) * beta Q

/-- The literal source wall unit in bin j, with no remaining attachment,
seam, or local collision hypotheses. -/
theorem wallUnit_fold_exists (q Q : ℕ) (hq : 0 < q) (hQ : 0 < Q) (j : Fin q) :
    ∃ f : Fold cubicLattice (wallUnit q Q).length,
      AttachedTo (fun _ => 0) (side q Q) f (unitOwners (depth q Q) (alpha Q) (wallTop q Q j)) ∧
      hydrophobicSites (wallUnit q Q) f = Set.range (unitOwners (depth q Q) (alpha Q) (wallTop q Q j)) ∧
      HasEnds f (point (depth q Q + 1) (wallTop q Q j - alpha Q + 1) (-1))
        (point (depth q Q + 1) (wallTop q Q j - alpha Q - 2) (-1)) := by
  rw [← unitWord_eq_wallUnit]
  apply unitWord_fold_exists
  · have h := depth_two_le q Q hq
    omega
  · dsimp [alpha]
    omega
  · exact depth_even q Q
  · dsimp [alpha]
    omega
  · have hj : j.val + 1 ≤ q := by omega
    have hm := Nat.mul_le_mul_right (beta Q) hj
    simp only [Nat.add_mul, Nat.one_mul] at hm
    have hb : beta Q = 2 * alpha Q + 2 := by dsimp [beta, alpha]; omega
    have hb' : (beta Q : ℤ) = 2 * (alpha Q : ℤ) + 2 := by exact_mod_cast hb
    have hm' : (j.val : ℤ) * beta Q + beta Q ≤ (q : ℤ) * beta Q := by exact_mod_cast hm
    have hnon : 0 ≤ (j.val : ℤ) * beta Q := by positivity
    have hd : (depth q Q : ℤ) = (q : ℤ) * beta Q := by simp [depth]
    dsimp [wallTop]
    constructor <;> omega

theorem append_owners_plane {H K : ℕ} (p : Fin H → Site) (q : Fin K → Site)
    (hp : ∀ i, p i 2 = 0) (hq : ∀ i, q i 2 = 0) : ∀ i, Fin.append p q i 2 = 0 := by
  intro i
  cases i using Fin.addCases with
  | left i => simpa only [Fin.append_left] using hp i
  | right i => simpa only [Fin.append_right] using hq i

theorem unitOwners_plane (d A : ℕ) (top : ℤ) : ∀ i, unitOwners d A top i 2 = 0 := by
  apply append_owners_plane
  · intro i; rfl
  · apply append_owners_plane
    · intro i; rfl
    · apply append_owners_plane
      · intro i; rfl
      · apply append_owners_plane <;> intro i <;> rfl

end ProteinFolding.CubicPackingWalls
