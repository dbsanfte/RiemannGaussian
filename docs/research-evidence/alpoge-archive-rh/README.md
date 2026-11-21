# Shorter geometric proof of RH

Lean 4.33.1 checked `RiemannGaussian.AlpogeWindow.rh_of_principal_archived_geometry : RiemannHypothesis` with `--trust=0` and `-DwarningAsError=true`. The theorem has no hypotheses and the axiom audit reports `propext`, `Classical.choice`, and `Quot.sound`. [Proof source](../../../scripts/CheckAlpogePrincipalArchivedGeometryRH.lean)

The proof uses the principal height-401 arithmetic window and one selected family of reciprocity-based bundles. The bundle witness supplies the lift-rank bound and group and Hecke comparisons. The weighted, irreducibility, divisibility and spectral comparisons refer to the same family. The selected period grid uses the theta identities and the Hodge covolume bound. The local assembly uses 165,070 archived source modules and 31 local modules. It saves 10,104 archive modules compared with the previously replayed 175,174-module principal route, or 10,079 modules including local code.

The dedicated GitHub Actions workflow uses the archive's Lean and Mathlib pins. It verifies the source parts and the public compiled archive by SHA-256, mounts the compiled objects as a compressed read-only filesystem, and exposes only the pinned import closure through `LEAN_PATH`. Actions caches the packed filesystem under a key tied to the public archive checksum. Later runs verify and mount the restored image. Lean elaborates the local proof files and runs standalone kernel replay on the endpoint. [Workflow](../../../.github/workflows/alpoge_archive_ci.yml) · [Pinned public cache](https://huggingface.co/datasets/JackMcCarthy/riemann-hypothesis-build/tree/9036e64326acf4acfae159b96664e9708445c1d1)

To run the same verifier on x86-64 Linux, prepare the hashed source parts from [Alpöge's archive](https://alpo.ge/remark.pdf), then run `lake exe cache get` in the extracted `lean` directory for its pinned Mathlib dependencies. Pass the public archive's `.lake/build/lib/lean` directory or the mounted compressed equivalent. The verifier has no archive build path.

```sh
python3 scripts/verify_alpoge_archive_rh.py /path/to/extracted/lean /path/to/public/objects --sandbox
```
