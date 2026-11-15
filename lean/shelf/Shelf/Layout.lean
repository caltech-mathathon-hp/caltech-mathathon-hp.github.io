import Shelf.Walk
import Shelf.Count

/-!
# The fold of Table 1

Section 5.2 of the paper (`proof/paper/paper.tex`) lists the sites of the fold,
piece by piece. This file writes that table down. Throughout, `n = side J`,
`N = n - 1`, the shelf is the edge `(x, 0, 0)`, the separator number `j`
(from 0) is in the column `sepCol j = 1 + j (B + 1)`.

Four parts of the fold are not written down here but taken as data (`Parts`):

* `core`, the path of the Core Lemma (Lemma 14);
* `aT`, the tokens of the long run `A`;
* `lo`, the lowest column of every item, which comes from the packing;
* `mid`, the inner sites of the linkers, which come from the Routing Lemma.

`Parts.Good` says what the rest of the proof needs to know about them. The
theorems about `layout` are proved for any good parts, in the files
`LayoutFits`, `LayoutChain` and `LayoutNodup`; `Forward.lean` shows that good
parts exist when the instance has an exact packing.

Each isolated `H` is taken together with the `P` before it and the `P` after
it, as a token (`Shelf/Walk.lean`). So the string is read as

  `H^N₀ · P · T(9n-10) · P^(λ-2) · T(n-2) · P^(n-2) · T(1) · (P^(B+4) T(1))^m
     · P^(n-2) · T(n-2) · ∏ᵢ (P^(λ-2) T(aᵢ))`,  with `T(r) = (PHP)^r`

(`layoutWord`), and the `P`'s that the table gives to a tether or a linker but
that stand next to an `H` belong to the token of that `H` here.
-/

namespace ProteinFolding.Shelf

open ProteinFolding Residue

/-- The parts of the fold that Table 1 does not give by a formula. -/
structure Parts (J : Packing.Instance) where
  /-- the sites of the core `H^N₀` -/
  core : List Site
  /-- the tokens of the run `A` -/
  aT : List Token
  /-- the lowest column of each item -/
  lo : Fin J.sizes.length → ℕ
  /-- the inner sites of the linkers: number `0` joins `A` to `F₁`, number `i + 1`
  leads to the item `i` -/
  mid : Fin (J.sizes.length + 1) → List Site

namespace Layout

section Fixed

variable (J : Packing.Instance)

/-- `N = n - 1`, as an integer. -/
def N : ℤ := (side J : ℤ) - 1

/-- The last site of the core. -/
def coreEnd : Site := pt 1 (N J) (N J - 1)

/-- The first `P` of the string, above the end of the core. -/
def firstP : Site := pt 1 (N J + 1) (N J - 1)

/-- The first site of the tokens of `A`: the `P` above `u₁ = (0, N, N - 1)`. -/
def aIn : Site := pt 0 (N J + 1) (N J - 1)

/-- The last site of the tokens of `A`: the `P` beside `(N, N, N - 1)`. -/
def aOut : Site := pt (N J + 1) (N J) (N J - 1)

/-- The ports `p₀`, `q₀` of the first linker, and the site after `q₀`. -/
def p₀ : Site := pt (N J + 2) (N J) (N J - 1)
def q₀ : Site := pt (N J - 1) (N J) (-3)
def q₀' : Site := pt (N J - 1) (N J) (-2)

/-- `F₁` on the edge `(x, N, 0)`, from `x = N - 1` down to `x = 1`; the `P`'s hang
in front (`-z`) and above (`+y`). -/
def f₁Tokens : List Token :=
  altRun (pt (N J - 1) (N J) 0) (pt (-1) 0 0) (side J - 2) (pt 0 0 (-1)) (pt 0 1 0)

/-- The tether from `F₁` to the first separator: `(1, y, -1)` for `y = N - 1, …, 1`. -/
def tether₁ : List Site := line (pt 1 (N J - 1) (-1)) (pt 0 (-1) 0) (side J - 2)

/-- The column of the separator number `j`, for `j = 0, …, m`. -/
def sepCol (j : ℕ) : ℤ := 1 + (j : ℤ) * ((J.capacity : ℤ) + 1)

/-- A separator: the `P` before it is in front of it, the `P` after it below it. -/
def sepToken (j : ℕ) : Token := ⟨pt (sepCol J j) 0 0, pt 0 0 (-1), pt 0 (-1) 0⟩

/-- The tether from the separator `j` to the separator `j + 1`, without its first and
last site: along `(x, -1, -1)` and then round the next separator. -/
def innerMid (j : ℕ) : List Site :=
  line (pt (sepCol J j) (-1) (-1)) (pt 1 0 0) (J.capacity + 1) ++
    [pt (sepCol J (j + 1) - 1) (-1) (-2), pt (sepCol J (j + 1)) (-1) (-2),
      pt (sepCol J (j + 1)) 0 (-2)]

/-- The separators with the tethers between them. -/
def sepPart : List Site :=
  tokSites [sepToken J 0] ++
    (List.range J.bins).flatMap fun j => innerMid J j ++ tokSites [sepToken J (j + 1)]

/-- The tether from the last separator to `F₂`: `(N - 1, -1, z)` for `z = 1, …, N - 1`. -/
def tether₂ : List Site := line (pt (N J - 1) (-1) 1) (pt 0 0 1) (side J - 2)

/-- `F₂` on the edge `(x, 0, N)`, from `x = N - 1` down to `x = 1`; the `P`'s hang
below (`-y`) and behind (`+z`). -/
def f₂Tokens : List Token :=
  altRun (pt (N J - 1) 0 (N J)) (pt (-1) 0 0) (side J - 2) (pt 0 (-1) 0) (pt 0 0 1)

/-- Where everything except the inner sites of the linkers lies: `x ≤ N + 1`, `y ≥ -1`,
`z ≥ -2`, or one of the two ports `p₀`, `q₀`. The linkers stay outside this set. -/
def InBox (s : Site) : Prop :=
  (s 0 ≤ N J + 1 ∧ -1 ≤ s 1 ∧ -2 ≤ s 2) ∨ s = p₀ J ∨ s = q₀ J

end Fixed

section Items

variable {J : Packing.Instance} (lo : Fin J.sizes.length → ℕ)

/-- The column of the first node of the item `i`. An item runs in direction `+x` if its
lowest column is odd and in direction `-x` if it is even, so that it starts in an odd
column and ends in an even one. -/
def firstCol (i : Fin J.sizes.length) : ℤ :=
  if lo i % 2 = 1 then (lo i : ℤ) else (lo i : ℤ) + (J.sizes.get i : ℤ) - 1

/-- The column of the last node of the item `i`. -/
def lastCol (i : Fin J.sizes.length) : ℤ :=
  if lo i % 2 = 1 then (lo i : ℤ) + (J.sizes.get i : ℤ) - 1 else (lo i : ℤ)

/-- The item `i` on the shelf; the `P`'s hang below (`-y`) and in front (`-z`). -/
def itemTokens (i : Fin J.sizes.length) : List Token :=
  altRun (pt (firstCol lo i) 0 0) (pt (if lo i % 2 = 1 then 1 else -1) 0 0) (J.sizes.get i)
    (pt 0 (-1) 0) (pt 0 0 (-1))

/-- The first site of the item `i`: below its first node. -/
def itemIn (i : Fin J.sizes.length) : Site := pt (firstCol lo i) (-1) 0

/-- The last site of the item `i`: below its last node. -/
def itemOut (i : Fin J.sizes.length) : Site := pt (lastCol lo i) (-1) 0

/-- The site where the linker of the item `i` starts: the last site of `F₂` for the
first item, and the last site of the item before it otherwise. -/
def prevOut (i : Fin J.sizes.length) : Site :=
  if h : i.val = 0 then pt 1 (-1) (N J)
  else itemOut lo ⟨i.val - 1, by have := i.isLt; omega⟩

end Items

end Layout

open Layout

/-- The sites of the fold, in the order of the string (Table 1 of the paper). -/
def layout {J : Packing.Instance} (P : Parts J) : List Site :=
  P.core ++ [firstP J] ++ tokSites P.aT ++ ([p₀ J] ++ P.mid 0 ++ [q₀ J, q₀' J]) ++
    tokSites (f₁Tokens J) ++ tether₁ J ++ sepPart J ++ tether₂ J ++ tokSites (f₂Tokens J) ++
    (List.finRange J.sizes.length).flatMap fun i =>
      P.mid i.succ ++ tokSites (itemTokens P.lo i)

/-- `T(r) = (PHP)^r`. -/
def tokWord (r : ℕ) : Sequence := (List.replicate r [P, H, P]).flatten

/-- The string, read with every isolated `H` grouped with the two `P`'s next to it. -/
def layoutWord (J : Packing.Instance) : Sequence :=
  List.replicate (coreLength (side J)) H ++ [P] ++ tokWord (9 * side J - 10) ++
    List.replicate (linkerLength J - 2) P ++ tokWord (side J - 2) ++
    List.replicate (side J - 2) P ++
    (tokWord 1 ++ (List.range J.bins).flatMap fun _ =>
      List.replicate (J.capacity + 4) P ++ tokWord 1) ++
    List.replicate (side J - 2) P ++ tokWord (side J - 2) ++
    (List.finRange J.sizes.length).flatMap fun i =>
      List.replicate (linkerLength J - 2) P ++ tokWord (J.sizes.get i)

/-- The columns `lo` put every item inside one bin of the shelf, and different items on
different columns. The bin number `b` (from 0) is the set of the columns
`2 + b (B + 1), …, 2 + b (B + 1) + B - 1`, between the separators `b` and `b + 1`. -/
structure Placed (J : Packing.Instance) (lo : Fin J.sizes.length → ℕ) : Prop where
  bin : ∀ i, ∃ b, b < J.bins ∧ 2 + b * (J.capacity + 1) ≤ lo i ∧
    lo i + J.sizes.get i ≤ 2 + b * (J.capacity + 1) + J.capacity
  disjoint : ∀ i i', i ≠ i' →
    Disjoint (Finset.Ico (lo i) (lo i + J.sizes.get i))
      (Finset.Ico (lo i') (lo i' + J.sizes.get i'))

/-- What the proof of Theorem 16 uses about the four parts. -/
structure Parts.Good {J : Packing.Instance} (P : Parts J) : Prop where
  -- the core (Lemma 14)
  core_length : P.core.length = coreLength (side J)
  core_nodup : P.core.Nodup
  core_chain : P.core.IsChain cubicLattice.Adj
  core_mem : ∀ p ∈ P.core, p ∈ Q (side J) ∧ ¬ CubicPackingGeometry.EdgeSkeleton 0 (side J) p
  core_last : P.core.getLast? = some (coreEnd J)
  -- the run `A`
  a_length : P.aT.length = 9 * side J - 10
  a_valid : ∀ t ∈ P.aT, t.Valid (side J)
  a_linked : P.aT.IsChain Linked
  a_nodup : (P.aT.map Token.c).Nodup
  a_centres : ∀ t ∈ P.aT, CubicPackingGeometry.EdgeSkeleton 0 (side J) t.c ∧
    ((t.c 0 = 0 ∨ t.c 0 = N J) ∨ (t.c 1 = N J ∧ t.c 2 = N J))
  a_head : (tokSites P.aT).head? = some (aIn J)
  a_last : (tokSites P.aT).getLast? = some (aOut J)
  -- the columns of the items (from the packing)
  placed : Placed J P.lo
  -- the linkers (Lemma 15)
  mid_zero_length : (P.mid 0).length + 5 = linkerLength J
  mid_succ_length : ∀ i : Fin J.sizes.length, (P.mid i.succ).length + 2 = linkerLength J
  mid_zero_chain : (p₀ J :: (P.mid 0 ++ [q₀ J])).IsChain cubicLattice.Adj
  mid_succ_chain : ∀ i : Fin J.sizes.length,
    (prevOut P.lo i :: (P.mid i.succ ++ [itemIn P.lo i])).IsChain cubicLattice.Adj
  mid_nodup : ∀ i, (P.mid i).Nodup
  mid_disjoint : ∀ i j, i ≠ j → ∀ s ∈ P.mid i, s ∉ P.mid j
  mid_out : ∀ i, ∀ s ∈ P.mid i, ¬ InBox J s

end ProteinFolding.Shelf
