# Supplementary material

Notes, manuscripts and checking programs that the team's report cites. The website does not use
these files; the Lean projects are in `lean/`.

| Path | Content |
| --- | --- |
| `edge_packing_proof.md` | Full write-up of the one-edge reduction (Section 4 of the report) |
| `check_edge_packing.mjs`, `edge_packing_verification.json` | Its checking program and the program's output |
| `tetrahedral/` | The diamond-lattice manuscript (`fable_review_v3_2026_11_14/HP_tetrahedral_review/HP_tetrahedral_proof.md`), the review audits (`Fable_review*_audit.md`, `routing_transfer_audit.txt`) and their checking programs. The theorem itself is checked in Lean in `lean/tetrahedral` |
| `fcc_three_partition/` | Notes on the face-centred cubic lattice (`REPORT.md`) with their checking programs. Partial results only |
| `fcc_hp_attempt/` | A second set of notes on the face-centred cubic lattice (see its `README.md`). Completeness of a reduction is proved there; soundness is open |

`../background/HP_tetrahedral_proof_Astra.md` is read by one of the checking programs in `tetrahedral/`.

Hardness of ordinary HP folding on the face-centred cubic lattice is not established by any of these
notes. Some notes contain absolute paths of the machines they were written on.
