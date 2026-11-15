/-! A made-up vendored library (test fixture): the tests copy it to vendor/lib/ in a copy
of lean-cubic, to check that count_exclude leaves it out of the counts. -/

namespace ProteinFolding.Lib

/-- A vendored definition. -/
def binCount : ℕ := 3

/-- A vendored theorem, used by the project. -/
theorem binCount_pos : 0 < binCount := by
  decide

end ProteinFolding.Lib
