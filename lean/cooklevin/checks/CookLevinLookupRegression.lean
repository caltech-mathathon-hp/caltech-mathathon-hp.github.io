import ProteinFolding.Common.CookLevinProofWordLookup

open ProteinFolding.SAT.CookLevinWordLookup

example : lookupTest (some true) ([false, true, false], 1) = true := by decide
example : lookupTest (some true) ([false, true, false], 0) = false := by decide
example : lookupTest (none : Option Bool) ([], 0) = true := by decide
example : lookupTest (none : Option Bool) ([false, true], 2) = true := by decide
example : lookupTest (some true) ([true], 100) = false := by decide
example : lookupTest (none : Option Empty) ([], 10) = true := by decide
example : headTest (some false) [false, true, true] = true := by decide
example : @encodedLookupTest Bool Computability.finEncodingBoolBool
    (inferInstanceAs (DecidableEq Bool)) (some false) (true, 0) = false := by
  decide
