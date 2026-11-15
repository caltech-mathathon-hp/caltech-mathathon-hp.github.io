# Original workspace proof records

These files are unchanged copies of the completed workspace's verification
records. They document original kernel checks, not a clean build of this
exported package or a GitHub Actions result.

| Record | Scope |
| --- | --- |
| [final-verification.json](final-verification.json) | Successful exact-theorem gate: 884 tetrahedral modules in the target closure, 681 matching source/artifact receipts, 203 modules checked through the established recorded-source/legacy-artifact policy, and zero stale dependency source edges |
| [final-source-snapshot.json](final-source-snapshot.json) | Target source hashes captured before the final exact-type audit and rechecked afterward |
| [final-axioms-v2.log](final-axioms-v2.log) | Successful exact-type check and four final axiom reports, all using only the standard three axioms |
| [verification-summary.json](verification-summary.json) | Completed broader checkpoint: 921 tetrahedral modules, 153 examples and 6,867 public declaration audits; 706 matching receipts and 215 legacy modules; final theorem marked proved only after revalidating its independent gate |
| [integration-axioms-final-v1.log](integration-axioms-final-v1.log) | Successful broader tetrahedral declaration audit |

The original checks used Lean 4.24.0, compiled mathlib/Common dependencies and
folder-local artifacts. Those binaries and caches are not distributed. The
original Windows workspace check scripts are not a portable package build
interface and are not included. Use the package's pinned Lake configuration
and checks/verify.py for a fresh build and verification.

The source manifest records byte-exact hashes for all shipped Lean modules
and pinned configuration. Its provenance section also hashes these five
records. Paths inside the historical records retain their original scope;
the two closure counts above describe tetrahedral modules, whereas the source
distribution also contains every required shared Common/Cubic/Square module.
