import ProteinFolding.Tetrahedral.NearFieldPPPFrameLong

namespace ProteinFolding.Tetrahedral.NearField

theorem framePortFrame_0 : nearFrameRouteFrame (⟨0, by decide⟩ : Fin 6) = entryEdgeFrame := by
  norm_num [nearFrameRouteFrame, Fin.ext_iff]
theorem framePortStart_0 (m q : ℕ) : nearFrameStartIndex m q (⟨0, by decide⟩ : Fin 6) = 0 := by
  norm_num [nearFrameStartIndex, Fin.ext_iff]
theorem framePortEnd_0 (m q : ℕ) : nearFrameEndIndex m q (⟨0, by decide⟩ : Fin 6) = 3 := by
  norm_num [nearFrameEndIndex, Fin.ext_iff]
theorem frameStartH_0 (m q : ℕ) : frameStartH m q (⟨0, by decide⟩ : Fin 6) = octEdgeZigzag m entryEdgeFrame (0) := by
  unfold frameStartH
  rw [framePortFrame_0, framePortStart_0]
theorem frameEndH_0 (m q : ℕ) : frameEndH m q (⟨0, by decide⟩ : Fin 6) = octEdgeZigzag m entryEdgeFrame (3) := by
  unfold frameEndH
  rw [framePortFrame_0, framePortEnd_0]

theorem framePortFrame_1 : nearFrameRouteFrame (⟨1, by decide⟩ : Fin 6) = entryEdgeFrame := by
  norm_num [nearFrameRouteFrame, Fin.ext_iff]
theorem framePortStart_1 (m q : ℕ) : nearFrameStartIndex m q (⟨1, by decide⟩ : Fin 6) = q := by
  norm_num [nearFrameStartIndex, Fin.ext_iff]
theorem framePortEnd_1 (m q : ℕ) : nearFrameEndIndex m q (⟨1, by decide⟩ : Fin 6) = q + 3 := by
  norm_num [nearFrameEndIndex, Fin.ext_iff]
theorem frameStartH_1 (m q : ℕ) : frameStartH m q (⟨1, by decide⟩ : Fin 6) = octEdgeZigzag m entryEdgeFrame (q) := by
  unfold frameStartH
  rw [framePortFrame_1, framePortStart_1]
theorem frameEndH_1 (m q : ℕ) : frameEndH m q (⟨1, by decide⟩ : Fin 6) = octEdgeZigzag m entryEdgeFrame (q + 3) := by
  unfold frameEndH
  rw [framePortFrame_1, framePortEnd_1]

theorem framePortFrame_2 : nearFrameRouteFrame (⟨2, by decide⟩ : Fin 6) = entryEdgeFrame := by
  norm_num [nearFrameRouteFrame, Fin.ext_iff]
theorem framePortStart_2 (m q : ℕ) : nearFrameStartIndex m q (⟨2, by decide⟩ : Fin 6) = 2 * m - 4 := by
  norm_num [nearFrameStartIndex, Fin.ext_iff]
theorem framePortEnd_2 (m q : ℕ) : nearFrameEndIndex m q (⟨2, by decide⟩ : Fin 6) = 2 * m - 2 := by
  norm_num [nearFrameEndIndex, Fin.ext_iff]
theorem frameStartH_2 (m q : ℕ) : frameStartH m q (⟨2, by decide⟩ : Fin 6) = octEdgeZigzag m entryEdgeFrame (2 * m - 4) := by
  unfold frameStartH
  rw [framePortFrame_2, framePortStart_2]
theorem frameEndH_2 (m q : ℕ) : frameEndH m q (⟨2, by decide⟩ : Fin 6) = octEdgeZigzag m entryEdgeFrame (2 * m - 2) := by
  unfold frameEndH
  rw [framePortFrame_2, framePortEnd_2]

theorem framePortFrame_3 : nearFrameRouteFrame (⟨3, by decide⟩ : Fin 6) = exitEdgeFrame := by
  norm_num [nearFrameRouteFrame, Fin.ext_iff]
theorem framePortStart_3 (m q : ℕ) : nearFrameStartIndex m q (⟨3, by decide⟩ : Fin 6) = 2 * m - 2 := by
  norm_num [nearFrameStartIndex, Fin.ext_iff]
theorem framePortEnd_3 (m q : ℕ) : nearFrameEndIndex m q (⟨3, by decide⟩ : Fin 6) = 2 * m - 4 := by
  norm_num [nearFrameEndIndex, Fin.ext_iff]
theorem frameStartH_3 (m q : ℕ) : frameStartH m q (⟨3, by decide⟩ : Fin 6) = octEdgeZigzag m exitEdgeFrame (2 * m - 2) := by
  unfold frameStartH
  rw [framePortFrame_3, framePortStart_3]
theorem frameEndH_3 (m q : ℕ) : frameEndH m q (⟨3, by decide⟩ : Fin 6) = octEdgeZigzag m exitEdgeFrame (2 * m - 4) := by
  unfold frameEndH
  rw [framePortFrame_3, framePortEnd_3]

theorem framePortFrame_4 : nearFrameRouteFrame (⟨4, by decide⟩ : Fin 6) = exitEdgeFrame := by
  norm_num [nearFrameRouteFrame, Fin.ext_iff]
theorem framePortStart_4 (m q : ℕ) : nearFrameStartIndex m q (⟨4, by decide⟩ : Fin 6) = q + 7 := by
  norm_num [nearFrameStartIndex, Fin.ext_iff]
theorem framePortEnd_4 (m q : ℕ) : nearFrameEndIndex m q (⟨4, by decide⟩ : Fin 6) = q := by
  norm_num [nearFrameEndIndex, Fin.ext_iff]
theorem frameStartH_4 (m q : ℕ) : frameStartH m q (⟨4, by decide⟩ : Fin 6) = octEdgeZigzag m exitEdgeFrame (q + 7) := by
  unfold frameStartH
  rw [framePortFrame_4, framePortStart_4]
theorem frameEndH_4 (m q : ℕ) : frameEndH m q (⟨4, by decide⟩ : Fin 6) = octEdgeZigzag m exitEdgeFrame (q) := by
  unfold frameEndH
  rw [framePortFrame_4, framePortEnd_4]

theorem framePortFrame_5 : nearFrameRouteFrame (⟨5, by decide⟩ : Fin 6) = exitEdgeFrame := by
  norm_num [nearFrameRouteFrame, Fin.ext_iff]
theorem framePortStart_5 (m q : ℕ) : nearFrameStartIndex m q (⟨5, by decide⟩ : Fin 6) = 2 := by
  norm_num [nearFrameStartIndex, Fin.ext_iff]
theorem framePortEnd_5 (m q : ℕ) : nearFrameEndIndex m q (⟨5, by decide⟩ : Fin 6) = 0 := by
  norm_num [nearFrameEndIndex, Fin.ext_iff]
theorem frameStartH_5 (m q : ℕ) : frameStartH m q (⟨5, by decide⟩ : Fin 6) = octEdgeZigzag m exitEdgeFrame (2) := by
  unfold frameStartH
  rw [framePortFrame_5, framePortStart_5]
theorem frameEndH_5 (m q : ℕ) : frameEndH m q (⟨5, by decide⟩ : Fin 6) = octEdgeZigzag m exitEdgeFrame (0) := by
  unfold frameEndH
  rw [framePortFrame_5, framePortEnd_5]

end ProteinFolding.Tetrahedral.NearField

