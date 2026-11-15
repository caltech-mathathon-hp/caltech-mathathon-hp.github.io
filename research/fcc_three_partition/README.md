# FCC / unary 3-Partition continuation

The further attempt is in [CONTINUATION.md](CONTINUATION.md): a smaller
two-layer all-(111)-face template and a complete ordinary-chain false positive
for the explicit all-H-scaffold reduction candidate. Its no-instance certificate
and P routing are checked by [thin_container.py](thin_container.py).

Read [REPORT.md](REPORT.md) for proofs, failed constructions, experimental scope,
and the precise remaining global forcing obligation.

The main new result is an explicit **counterexample for every even-length
programmed word** from notebook Section 45. Four compatible tiles fold a program
of length 2m with `51m-15` contacts, exceeding the intended ribbon score
`50m-15`. The H-occupied set is independent of the program. The proof accounts
for all P routing and all contacts.

- [Four coordinate tables](universal_tiles.md)
- [Arbitrary-program construction and independent checker](universal_competitor.py)
- [Example ordinary fold](universal_example.json)
- [Robust soundness and perturbed-scaffold lemmas](REPORT.md#4-robust-partition-extraction-without-exact-item-paths)
- [General-spacing item routing](routing.py)

The robust lemmas show how small scaffold/displacement errors could still yield
an exact partition after scaling and separating the bins. A binary prefix
forcing those error bounds remains missing. This directory does not claim an
ordinary FCC NP-hardness reduction.

There is also a sharp `25L+floor(L/2)-15` bound over all one-marker variants
within the original ribbon family, with an attaining alternative word and a
counterexample to planar registration of its individual modules. All nine
deterministic checks pass; run `python check_all.py` to reproduce them.
