# Independent final strict and combined audit

**PASS, all 11 modules.** No source edits or root object overwrites were made by this audit.

`strict_recheck.py` independently recompiled every module listed in `new-modules.json` using absolute lake, Lean 4.34.1, `autoImplicit=false`, and `warningAsError=true`. Outputs are isolated in `strict-objects/`. Every isolated .olean is byte-for-byte identical to the corresponding ordinary root .olean used for dependencies. The 141 recursively imported local dependency sources/objects were pinned before compilation and remained unchanged through both recompilation and the combined audit.

`CombinedBitCounterAudit.lean` imports the ordinary `RiemannGaussian` root and all 11 modules. All 15 linters passed in each namespace. The auditor inspects every generated constant owned by those modules, rejects project axioms, and checks every constant's transitive axioms against exactly `propext`, `Classical.choice`, `Quot.sound`.

| Module suffix (Semiprime prefix) | Declarations | Theorem constants |
|---|---:|---:|
| RationalBits | 129 | 67 |
| DotBits | 20 | 13 |
| CounterPacketHeight | 54 | 43 |
| FibreAccumulatorHeight | 34 | 25 |
| LocalPrefixHeight | 16 | 14 |
| HermiteArrayHeight | 205 | 150 |
| MacroEntryExecution | 117 | 87 |
| MacroEntryBitPrimitives | 180 | 89 |
| MacroEntryBitCheck | 301 | 231 |
| SubdividedEntry | 10 | 7 |
| PublicConstructedCount | 15 | 13 |
| **Total** | **1081** | **739** |

Reproduction:

```
python3 /tmp/semiprime-bit-counter-20261027/strict_recheck.py
cd /home/dbsanfte/riemann/formal
/home/dbsanfte/.elan/bin/lake env lean -DautoImplicit=false -DwarningAsError=true /tmp/semiprime-bit-counter-20261027/CombinedBitCounterAudit.lean
```

Machine-readable artifacts: `strict-recheck.json`, `strict-dependency-snapshot.json`, `combined-audit-result.json`, `new-modules.json`. Logs: `strict-recheck-run.log`, each `Semiprime*-strict.log`, `CombinedBitCounterAudit.log`. Exact toolchain recorded in `strict-toolchain.txt`.

This gate establishes strict source/object consistency, namespace linting, and the stated standard-axiom proof audit. It does not itself prove a whole counter machine runtime/space theorem, a Python extraction correspondence, or the sixth-rate factoring goal. The public constructed count endpoint remains an exact finite semantic equality under its executable layout guard, with separate future resource composition.
