# Paper-to-Lean index (test fixture)

Names are prefixed by `ProteinFolding.` unless another prefix is shown.

| Paper concept | Declaration | Source / status |
| --- | --- | --- |
| Section 2: words and folds | `Residue`, `Sequence`, `Fold` | [Common/Statement](../ProteinFolding/Common/Statement.lean), definitions |
| Bond count and the empty fold | `bondCount`; `emptyFold` | [Statement](../ProteinFolding/Common/Statement.lean); [Main](../ProteinFolding/Main.lean) |
| The bond bound | `bondCount_le` | [Main](../ProteinFolding/Main.lean#L5), unconditional proof |
| Main theorem | `main_conditional` | Same file; proof with Cook–Levin |
| Explicit premise | `SAT.CookLevin` | [Main](../ProteinFolding/Main.lean), proposition only |

The audit is in [CubicHardness](../checks/CubicHardness.lean).
