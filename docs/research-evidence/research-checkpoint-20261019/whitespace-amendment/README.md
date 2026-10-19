# Additive publication whitespace amendment

The staged publication check found one redundant final LF in each of four
new audit leaves. Root removed only those four bytes. This packet preserves
both versions and the exact normalization record. It does not change a Lean
token, statement, proof, import, or audit command, and no old producer was
rerun as a new proof claim.

The parent archive remains byte-for-byte immutable:

- Base manifest SHA256: `acb9908a9bf43b89bd4939a4871dca411e09f27a9547ef2f291426618947a9f0`.
- Base index SHA256: `3d4c54cde75b6c7966a4416f770ddb6b45d20be9704e245df0f5189fe4991369`.

The originals remain in its objects, and this additive packet also preserves
the four root-created original snapshots. The four current normalized source
copies, the normalization record and the advanced consolidated checkpoint
are separate deterministic gzip objects. All older research manifests keep
their historical source hashes.

The current consolidated checkpoint has **1,550 pins** and SHA256
`94aa92aa57c8571df15f35c9163ccb55730e2866f63e15239de42271019c2a97`.
Three source pins were updated, the fourth source pin was added where it was
previously absent, and five pins cover the new normalization record and
original snapshots. The change is publication hygiene, not new arithmetic.

The base `restore.py --verify` continues to verify its original archived
bytes. Its frozen live-source audit describes the pre-cleanup snapshot;
for the current source/checkpoint use the combined read-only verifier:

```sh
python3 docs/research-evidence/research-checkpoint-20261019/whitespace-amendment/verify.py
```

This checks base metadata and all1,772 base payloads, amendment metadata and
all10 new payloads, the exact four one-LF relations, portable current-pin
coverage, and all91 source snapshots. It does not need omitted papers,
compiler outputs or a local Lean build. Add `--check-live` only in the
original populated research checkout to verify every current source pin
against its actual local input; the excluded papers and compiled artifacts
must then be present. The verifier never rewrites historical records.

| Source | Original SHA prefix | Current SHA prefix |
| --- | --- | --- |
| `ArithmeticOperatorDigitalSourceGate.lean` | `dd0519af79a5` | `55380db6c59e` |
| `ArithmeticOperatorSexticRateAudit.lean` | `eabede10b4a3` | `6318a2a253e2` |
| `QuasiRHAllSquarePartition.lean` | `1017777790ab` | `fe1b30aae320` |
| `QuasiRHSquareGaussIdealNorm.lean` | `e28640e7fbfb` | `02a1f861180a` |

The byte payload is107,604 compressed bytes before metadata. Base and
amendment together preserve history and the current publication source
without duplicating full papers, shipping oleans, or changing the whole
`Probe−F_all` source status. Semiprime research remains paused; no optional
numerical certificate replay was performed here.
