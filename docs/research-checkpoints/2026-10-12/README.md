# Portable research evidence, 12 October 2026

This snapshot preserves local arithmetic-operator and semiprime research
evidence referenced by the repository's audit records, along with the
authored notes, probes, reviews, logs and historical registration snapshots
that those records otherwise leave in ignored Lake directories or `/tmp`.
The external active roadmap is included as
`workspace/arithmetic_operator_research_roadmap.md`.

The archive retains repository-relative `.lake/` paths. External semiprime
artifacts are mapped to `tmp/`; their exact original absolute paths appear
in `manifest.json`. Historical audit files and their hashes are unchanged.
Where a historical pin differs from the preserved current artifact, the
manifest records that difference. Missing historical references and omitted
compiled/dependency evidence are recorded explicitly.

This is a publication snapshot, not a new proof. Exploratory Lean sources
and numerical probes are research records; their inclusion does not assert
that every draft compiles or that numerical diagnostics certify a bound.
Imported project checkouts, build caches, compiled Lean/native products,
environment executables, PDF downloads and imported paper-source subtrees
are excluded. The pinned vendor and Mathlib revisions remain the source of
imported proof dependencies.

Verify all archive members and hashes without writing anything:

```sh
python3 docs/research-checkpoints/2026-10-12/verify.py
```

Optionally restore into an explicitly chosen directory:

```sh
python3 docs/research-checkpoints/2026-10-12/verify.py --restore-to /tmp/research-evidence
```

Restoration validates the complete archive first and refuses to overwrite
any mismatched destination. `--overwrite` explicitly permits replacement.
It does not automatically restore external files to their original `/tmp`
locations or change the live worktree.

`snapshot.py --create` rebuilds the snapshot from the live local environment;
it is not needed to verify or read the published evidence. Rebuilding creates
a new current snapshot and cannot recreate missing historical bytes.
