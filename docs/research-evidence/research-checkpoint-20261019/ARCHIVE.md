# Arithmetic-operator research evidence, 19 October 2026

This publication checkpoint preserves accumulated research reports, exact
probes, compiler/axiom/linter logs, independent reviews and historical pin
manifests that lived in ignored research directories. It follows the
content-addressed deterministic-gzip format of the 12 October checkpoint.
Original bytes and hashes are preserved; historical success/failure and
paper-level/formal distinctions are not rewritten as new proof claims.

`index.json` maps original absolute paths and portable repository-relative
paths to gzip objects named by the SHA256 of their uncompressed bytes.
Identical payloads share an object. The current isolated `scripts/*.lean`
leaves and new documents remain ordinary publication sources; the archive
also snapshots their exact bytes. `inventory.json` distinguishes those
snapshots from live tracked paths, which the publication owner may update
later. Historical pin references to older shared-note bytes remain historical.

Full third-party paper bodies are excluded, including cached PDF, extracted
text, HTML and Markdown. Their available hashes, sizes and original paths
are retained in `excluded-primary-fingerprints.json`; original source pins
and `primary-url-catalog.json` retain URLs/versions. Compiler outputs,
bootstrap oleans, nested Git/package caches and Python bytecode are omitted.
The external goal roadmap, outside the formal repository, is snapshotted at
`external/riemann/arithmetic_operator_research_roadmap.md` on restoration;
its original absolute path remains in the index. Publication-owner browser
outputs and transient publication logs are outside this research snapshot.

The omission is deliberate: an archived manifest mentioning such a file does
not mean its payload is shipped or that its historical check was rerun.

Verify every archived payload with:

```sh
python3 docs/research-evidence/research-checkpoint-20261019/restore.py --verify
```

Restore into a **separate** repository root, preserving original `.lake/`
and `scripts/` paths beneath it, with:

```sh
python3 docs/research-evidence/research-checkpoint-20261019/restore.py \
  --destination /path/to/restored-research
```

Existing files with different bytes are refused. `--select` accepts a glob
of repository-relative paths, for example
`'.lake/arithmetic-operator-joined-mark-recovery/*'`. Original absolute paths
are provenance only and are not used as write destinations.

`replay-dependencies.json` records every currently untracked audit leaf,
its local imports and a topological source-build order. Source closure is
complete: all isolated imports have source publication candidates. Two
historical imports use root module aliases rather than `scripts.*`:
`QuasiRHFiniteSquareGaussAudit` and `QuasiRHPattersonModelLocalAudit`.
Their built oleans must be exposed at those aliases in a private bootstrap
root, as the original successful producer commands show. Prefix private
`LEAN_PATH` **after** `lake env`. The tracked vendored OAI closure, root
`lean-toolchain` and `lake-manifest.json` fix the other dependencies.

A clean replay should use a separate fresh checkout/worktree. Audit modules'
`run_cmd` blocks write their original per-leaf axiom JSON paths; replaying
in the frozen working tree would overwrite historical evidence. Create the
output directories documented in the archived producer commands first.
`leaf-evidence-map.json` and `leaf-hash-reference-map.json` locate historical
validation metadata but do not mistake a textual reference for a successful
terminal check. Failed development logs remain failed development logs.
No broad build was rerun merely to inventory this checkpoint.

The mathematical status is unchanged: the imported strict greater-than-7/8
baseline is separate from the still-open independent arithmetic estimate.
The newer square-sector payment and finite obstruction leaves retain their
precise formal scopes; unproved analytic/source bridges remain paper-level.
The whole source is the original signed `Probe−F_all`, not an individual
subset. The semiprime research goal remains paused. The exhaustive optional
numerical certificate was not rerun for this preservation task.

Final archival validation covered **1,772 original paths / 1,643 distinct
objects**, with **5,230,274 compressed object bytes** (22,182,700 original
entry bytes, before deduplication). All **1,544 current canonical pins**
match their live research sources. Their portable coverage is1,014 exact
archived payloads,307 tracked sources/documents,112 excluded primary
fingerprints,90 excluded compiled artifacts and21 locked Mathlib source
files. No portable reference is unresolved. All91 isolated leaf sources
are preserved; all25 distinct `scripts.*` dependencies and the two root
aliases have source coverage. This is source/hash coverage, not a new
collective Lean build or mathematical re-review.

The snapshot inventories146 normal untracked research sources:91 Lean
leaves and55 documents. Two modified research paths (AGENTS and the research
journal) are snapshotted as historical bytes; the third observed modified
path was publication-owned explorer metadata and is intentionally outside
the payload. Later publication asset changes are owned by the parent task.

Against the original populated research checkout, recheck object and canonical
source coverage read-only with
`python3 docs/research-evidence/research-checkpoint-20261019/audit_checkpoint.py`.
On a fresh checkout, only `restore.py --verify` is self-contained; the full
live-source audit additionally needs the excluded primary inputs and rebuilt
compiled dependencies when checking their historical hashes.
`manifest.json` pins this checkpoint's metadata and helper bytes; object
hashes are pinned by `index.json`. No old evidence packet was edited.
