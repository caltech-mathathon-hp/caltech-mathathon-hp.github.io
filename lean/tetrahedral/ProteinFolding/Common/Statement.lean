import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Basic

/-!
# Shared HP words, folds, and bond scoring

Definitions from Section 2 of Berger and Leighton, *Protein Folding in the
Hydrophobic-Hydrophilic (HP) Model is NP-Complete*, RECOMB 1998, pp. 30-39,
DOI: 10.1145/279069.279080.

Positions use zero-based `Fin S.length` in place of the paper's 1,...,N.
The paper counts ALL H-H lattice bonds, including consecutive sequence positions.
Each unordered bond is counted once by requiring i < j.

This file defines the problems. It does not assert NP-completeness or assume
any of the paper's geometric or complexity-theoretic results as axioms.
-/

namespace ProteinFolding

open scoped BigOperators

/-- Hydrophobic (H) and hydrophilic (P) residues. -/
inductive Residue where
  | H
  | P
  deriving DecidableEq, Repr

/-- An input protein is a finite word over {H,P}; the empty word is allowed. -/
abbrev Sequence := List Residue

/-- A self-avoiding walk of length N vertices in an arbitrary simple graph.
Only consecutive positions must be adjacent; other positions may also touch. -/
structure Fold {V : Type*} (G : SimpleGraph V) (N : ℕ) where
  pos : Fin N → V
  injective_pos : Function.Injective pos
  consecutive : ∀ i j : Fin N, i.val + 1 = j.val → G.Adj (pos i) (pos j)

/-- The hydrophobic sequence positions. -/
def hydrophobicIndices (S : Sequence) : Finset (Fin S.length) :=
  Finset.univ.filter (fun i => S.get i = Residue.H)

def hydrophobicCount (S : Sequence) : ℕ := (hydrophobicIndices S).card

section GeneralGraph

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]

/-- H-H bonds, represented by ordered indices i < j to avoid double counting.
In particular, we do NOT exclude pairs with j = i + 1. -/
def hhBonds (S : Sequence) (f : Fold G S.length) :
    Finset (Fin S.length × Fin S.length) :=
  (Finset.univ ×ˢ Finset.univ).filter fun ij =>
    ij.1 < ij.2 ∧ S.get ij.1 = Residue.H ∧ S.get ij.2 = Residue.H ∧
      G.Adj (f.pos ij.1) (f.pos ij.2)

def bondCount (S : Sequence) (f : Fold G S.length) : ℕ :=
  (hhBonds S f).card

/-- Integer-valued energy, with the sign convention in the paper. -/
def energy (S : Sequence) (f : Fold G S.length) : ℤ :=
  -(bondCount S f : ℤ)

/-- The optimisation problem: find a valid fold with minimum energy. -/
def IsOptimal (S : Sequence) (f : Fold G S.length) : Prop :=
  ∀ g : Fold G S.length, energy S f ≤ energy S g

/-- HP STRING-FOLD on a specified graph, with the paper's integer threshold. -/
def HPStringFold (S : Sequence) (m : ℤ) : Prop :=
  ∃ f : Fold G S.length, m ≤ (bondCount S f : ℤ)

end GeneralGraph

end ProteinFolding
