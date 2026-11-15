import ProteinFolding.Common.TM2ListMapRuns

/-! Physical record/parameter transfer and child-machine simulation stages. -/

namespace ProteinFolding.TM2ListMap

open Computability Turing TM2

variable {P A B : Type} {ep : FinEncoding P} {ea : FinEncoding A}
  {f : P × A → List B} [Fintype B]
  (h : TM2ComputableInPolyTime (pairEncoding ep ea) (wordEncoding B) f)

theorem recordTransferContents (S : ∀ k, List (h.tm.Γ k))
    (raw : List (RawSymbol (ep := ep) (ea := ea))) (p r b : List (InLetter h))
    (acc : List (OutLetter h)) (out : List B) (w : List (InLetter h)) :
    TM2Transfer.setStacks (Γ := Alphabet h) (.inr .record) (.inl h.tm.k₀)
      (contents h S raw p [] b acc out) r w =
      contents h (Function.update S h.tm.k₀ w) raw p r b acc out := by
  simp only [TM2Transfer.setStacks]
  rw [update_record, update_child]

theorem recordTransferCfg (phase : Phase h) (s : h.tm.σ) (cin : Option (InLetter h))
    (cout : Option (OutLetter h)) (S : ∀ k, List (h.tm.Γ k))
    (raw : List (RawSymbol (ep := ep) (ea := ea))) (p r b : List (InLetter h))
    (acc : List (OutLetter h)) (out : List B) (w : List (InLetter h)) :
    TM2Renaming.mapCfg (inputEquiv h)
      (TM2Transfer.transferCfg (Γ := Alphabet h) (.inr .record) (.inl h.tm.k₀) phase (s, cout) cin
        (contents h S raw p [] b acc out) r w) =
      cfg h phase (s, (cin, cout)) (Function.update S h.tm.k₀ w) raw p r b acc out := by
  simp only [TM2Renaming.mapCfg, TM2Transfer.transferCfg, recordTransferContents, cfg, inputEquiv]
  rfl

section Inhabited
variable [Inhabited B]

theorem restoreRecord_rule : program h .restoreRecord =
    TM2Renaming.relabelStmt (inputEquiv h)
      (letI : Inhabited (Alphabet h (.inr .record)) := ⟨separator h⟩
       TM2Transfer.transferStmt (Γ := Alphabet h) (Λ := Phase h)
         (σ := h.tm.σ × Option (OutLetter h))
         (.inr .record) (.inl h.tm.k₀) id .restoreRecord .separator) := by
  simp [program, inputTransfer, Equiv.prodCongr, Equiv.optionCongr, Equiv.cast,
    Equiv.trans, TM2Renaming.relabelStmt, TM2Transfer.transferStmt]
  constructor
  · funext t o
    cases o <;> rfl
  · funext t
    obtain ⟨s, cin, cout⟩ := t
    cases cin <;> rfl

theorem restoreRecord_run (s : h.tm.σ) (cin : Option (InLetter h)) (cout : Option (OutLetter h))
    (S : ∀ k, List (h.tm.Γ k)) (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (p r b : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) (w : List (InLetter h)) :
    run h (r.length + 1)
      (cfg h .restoreRecord (s, (cin, cout)) (Function.update S h.tm.k₀ w) raw p r b acc out) =
      some (cfg h .separator (s, (none, cout))
        (Function.update S h.tm.k₀ (r.reverse ++ w)) raw p [] b acc out) := by
  letI : Inhabited (Alphabet h (.inr .record)) := ⟨separator h⟩
  have ht := TM2Renaming.transfer_run (Γ := Alphabet h) (Λ := Phase h)
    (.inr .record) (.inl h.tm.k₀) (by intro he; cases he)
    (inputEquiv h) id .restoreRecord .separator (program h) (restoreRecord_rule h)
    (s, cout) cin (contents h S raw p [] b acc out) r w
  simp only [List.map_id] at ht
  rw [recordTransferCfg h .restoreRecord s cin cout S raw p r b acc out w,
    recordTransferCfg h .separator s none cout S raw p [] b acc out (r.reverse ++ w)] at ht
  exact ht

omit [Inhabited B] in
theorem parameterTransferCfg (phase : Phase h) (s : h.tm.σ) (cin : Option (InLetter h))
    (cout : Option (OutLetter h)) (S : ∀ k, List (h.tm.Γ k))
    (raw : List (RawSymbol (ep := ep) (ea := ea))) (p r b : List (InLetter h))
    (acc : List (OutLetter h)) (out : List B) :
    TM2Renaming.mapCfg (inputEquiv h)
      (TM2Transfer.transferCfg (Γ := Alphabet h) (.inr .parameterBuffer) (.inr .parameter)
        phase (s, cout) cin (contents h S raw [] r [] acc out) b p) =
      cfg h phase (s, (cin, cout)) S raw p r b acc out := by
  simp only [TM2Renaming.mapCfg, TM2Transfer.transferCfg, TM2Transfer.setStacks,
    update_parameterBuffer, update_parameter, cfg]
  rfl

theorem restoreParameter_rule : program h .restoreParameter =
    TM2Renaming.relabelStmt (inputEquiv h)
      (letI : Inhabited (Alphabet h (.inr .parameterBuffer)) := ⟨separator h⟩
       TM2Transfer.transferStmt (Γ := Alphabet h) (Λ := Phase h)
         (σ := h.tm.σ × Option (OutLetter h))
         (.inr .parameterBuffer) (.inr .parameter) id .restoreParameter (.child h.tm.main)) := by
  simp [program, inputTransfer, Equiv.prodCongr, Equiv.optionCongr, Equiv.cast,
    Equiv.trans, TM2Renaming.relabelStmt, TM2Transfer.transferStmt]
  constructor
  · funext t o; cases o <;> rfl
  · funext t; obtain ⟨s, cin, cout⟩ := t; cases cin <;> rfl

theorem restoreParameter_run (s : h.tm.σ) (cin : Option (InLetter h)) (cout : Option (OutLetter h))
    (S : ∀ k, List (h.tm.Γ k)) (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (p r b : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) :
    run h (b.length + 1) (cfg h .restoreParameter (s, (cin, cout)) S raw p r b acc out) =
      some (cfg h (.child h.tm.main) (s, (none, cout)) S raw (b.reverse ++ p) r [] acc out) := by
  letI : Inhabited (Alphabet h (.inr .parameterBuffer)) := ⟨separator h⟩
  have ht := TM2Renaming.transfer_run (Γ := Alphabet h) (Λ := Phase h)
    (.inr .parameterBuffer) (.inr .parameter) (by intro he; cases he)
    (inputEquiv h) id .restoreParameter (.child h.tm.main) (program h) (restoreParameter_rule h)
    (s, cout) cin (contents h S raw [] r [] acc out) b p
  simp only [List.map_id] at ht
  rw [parameterTransferCfg h .restoreParameter s cin cout S raw p r b acc out,
    parameterTransferCfg h (.child h.tm.main) s none cout S raw (b.reverse ++ p) r [] acc out] at ht
  exact ht

omit [Inhabited B] in
theorem parameterCopyCfg (phase : Phase h) (s : h.tm.σ) (cin : Option (InLetter h))
    (cout : Option (OutLetter h)) (S : ∀ k, List (h.tm.Γ k))
    (raw : List (RawSymbol (ep := ep) (ea := ea))) (p r b : List (InLetter h))
    (acc : List (OutLetter h)) (out : List B) (w : List (InLetter h)) :
    TM2Renaming.mapCfg (inputEquiv h)
      (TM2WalkCopy.cfg (Γ := Alphabet h) (.inr .parameter) (.inr .parameterBuffer) (.inl h.tm.k₀)
        phase (s, cout) cin (contents h S raw [] r [] acc out) p b w) =
      cfg h phase (s, (cin, cout)) (Function.update S h.tm.k₀ w) raw p r b acc out := by
  simp only [TM2Renaming.mapCfg, TM2WalkCopy.cfg, TM2WalkCopy.contents,
    update_parameter, update_parameterBuffer, update_child, cfg]
  rfl

theorem copyParameter_run (s : h.tm.σ) (cin : Option (InLetter h)) (cout : Option (OutLetter h))
    (S : ∀ k, List (h.tm.Γ k)) (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (p r b : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) (w : List (InLetter h)) :
    run h (p.length + 1)
      (cfg h .copyParameter (s, (cin, cout)) (Function.update S h.tm.k₀ w) raw p r b acc out) =
      some (cfg h .restoreParameter (s, (none, cout))
        (Function.update S h.tm.k₀ (p.reverse ++ w)) raw [] r (p.reverse ++ b) acc out) := by
  letI : Inhabited (Alphabet h (.inr .parameter)) := ⟨separator h⟩
  have ht := TM2Renaming.duplicate_run (Γ := Alphabet h) (Λ := Phase h)
    (.inr .parameter) (.inr .parameterBuffer) (.inl h.tm.k₀)
    (by intro he; cases he) (by intro he; cases he) (by intro he; cases he)
    (inputEquiv h) id id .copyParameter .restoreParameter (program h) rfl
    (s, cout) cin (contents h S raw [] r [] acc out) p b w
  simp only [List.map_id] at ht
  rw [parameterCopyCfg h .copyParameter s cin cout S raw p r b acc out w,
    parameterCopyCfg h .restoreParameter s none cout S raw [] r (p.reverse ++ b) acc out
      (p.reverse ++ w)] at ht
  exact ht

omit [Inhabited B] in
theorem childTransferCfg (phase : Phase h) (s : h.tm.σ) (cin : Option (InLetter h))
    (cout : Option (OutLetter h)) (S : ∀ k, List (h.tm.Γ k))
    (raw : List (RawSymbol (ep := ep) (ea := ea))) (p r b : List (InLetter h))
    (acc : List (OutLetter h)) (out : List B) (w : List (OutLetter h)) :
    TM2Renaming.mapCfg (outputEquiv h)
      (TM2Transfer.transferCfg (Γ := Alphabet h) (.inl h.tm.k₁) (.inr .accumulator)
        phase (s, cin) cout (contents h S raw p r b [] out) w acc) =
      cfg h phase (s, (cin, cout)) (Function.update S h.tm.k₁ w) raw p r b acc out := by
  simp only [TM2Renaming.mapCfg, TM2Transfer.transferCfg, TM2Transfer.setStacks,
    update_child, update_accumulator, cfg]
  rfl

theorem drainChild_rule : program h .drainChild =
    TM2Renaming.relabelStmt (outputEquiv h)
      (letI : Inhabited (Alphabet h (.inl h.tm.k₁)) := ⟨h.outputAlphabet.symm (default : B)⟩
       TM2Transfer.transferStmt (Γ := Alphabet h) (Λ := Phase h)
         (σ := h.tm.σ × Option (InLetter h))
         (.inl h.tm.k₁) (.inr .accumulator) id .drainChild .record) := by
  simp [program, outputTransfer, Equiv.prodCongr, Equiv.optionCongr, Equiv.cast,
    Equiv.trans, TM2Renaming.relabelStmt, TM2Transfer.transferStmt]
  constructor
  · funext t o; cases o <;> rfl
  · funext t; obtain ⟨s, cin, cout⟩ := t; cases cout <;> rfl

theorem drainChild_run (s : h.tm.σ) (cin : Option (InLetter h)) (cout : Option (OutLetter h))
    (S : ∀ k, List (h.tm.Γ k)) (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (p r b : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) (w : List (OutLetter h)) :
    run h (w.length + 1)
      (cfg h .drainChild (s, (cin, cout)) (Function.update S h.tm.k₁ w) raw p r b acc out) =
      some (cfg h .record (s, (cin, none)) (Function.update S h.tm.k₁ []) raw p r b (w.reverse ++ acc) out) := by
  letI : Inhabited (Alphabet h (.inl h.tm.k₁)) := ⟨h.outputAlphabet.symm (default : B)⟩
  have ht := TM2Renaming.transfer_run (Γ := Alphabet h) (Λ := Phase h)
    (.inl h.tm.k₁) (.inr .accumulator) (by intro he; cases he)
    (outputEquiv h) id .drainChild .record (program h) (drainChild_rule h)
    (s, cin) cout (contents h S raw p r b [] out) w acc
  simp only [List.map_id] at ht
  rw [childTransferCfg h .drainChild s cin cout S raw p r b acc out w,
    childTransferCfg h .record s cin none S raw p r b (w.reverse ++ acc) out []] at ht
  exact ht

omit [Inhabited B] in
theorem outputTransferCfg (phase : Phase h) (s : h.tm.σ) (cin : Option (InLetter h))
    (cout : Option (OutLetter h)) (S : ∀ k, List (h.tm.Γ k))
    (raw : List (RawSymbol (ep := ep) (ea := ea))) (p r b : List (InLetter h))
    (acc : List (OutLetter h)) (out : List B) :
    TM2Renaming.mapCfg (outputEquiv h)
      (TM2Transfer.transferCfg (Γ := Alphabet h) (.inr .accumulator) (.inr .output)
        phase (s, cin) cout (contents h S raw p r b [] []) acc out) =
      cfg h phase (s, (cin, cout)) S raw p r b acc out := by
  simp only [TM2Renaming.mapCfg, TM2Transfer.transferCfg, TM2Transfer.setStacks,
    update_accumulator, update_output, cfg]
  rfl

theorem output_rule : program h .output =
    TM2Renaming.relabelStmt (outputEquiv h)
      (letI : Inhabited (Alphabet h (.inr .accumulator)) := ⟨h.outputAlphabet.symm (default : B)⟩
       TM2Transfer.transferStmt (Γ := Alphabet h) (Λ := Phase h)
         (σ := h.tm.σ × Option (InLetter h))
         (.inr .accumulator) (.inr .output) h.outputAlphabet .output .finish) := by
  simp [program, outputTransfer, Equiv.prodCongr, Equiv.optionCongr, Equiv.cast,
    Equiv.trans, TM2Renaming.relabelStmt, TM2Transfer.transferStmt]
  constructor
  · funext t o; cases o <;> rfl
  · funext t; obtain ⟨s, cin, cout⟩ := t; cases cout <;> rfl

theorem output_run (s : h.tm.σ) (cin : Option (InLetter h)) (cout : Option (OutLetter h))
    (S : ∀ k, List (h.tm.Γ k)) (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (p r b : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) :
    run h (acc.length + 1) (cfg h .output (s, (cin, cout)) S raw p r b acc out) =
      some (cfg h .finish (s, (cin, none)) S raw p r b [] ((acc.map (outputSymbol h)).reverse ++ out)) := by
  letI : Inhabited (Alphabet h (.inr .accumulator)) := ⟨h.outputAlphabet.symm (default : B)⟩
  have ht := TM2Renaming.transfer_run (Γ := Alphabet h) (Λ := Phase h)
    (.inr .accumulator) (.inr .output) (by intro he; cases he)
    (outputEquiv h) h.outputAlphabet .output .finish (program h) (output_rule h)
    (s, cin) cout (contents h S raw p r b [] []) acc out
  rw [outputTransferCfg h .output s cin cout S raw p r b acc out] at ht
  exact ht.trans (congrArg some (outputTransferCfg h .finish s cin none S raw p r b []
    ((acc.map (outputSymbol h)).reverse ++ out)))

end Inhabited
end ProteinFolding.TM2ListMap
