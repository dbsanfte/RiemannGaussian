# Research evidence checkpoint, 2026-10-12

This directory preserves accumulated research that previously lived outside
the Git tree, including the semiprime proof reports, independent reviews,
source manifests, reproducible scripts, historical registration snapshots,
literature provenance and exploratory notes.

The original bytes and absolute references in frozen reports are unchanged.
`index.json` maps each original file to a deterministic gzip object named by
the SHA256 of its uncompressed bytes. Identical files share an object. The
`latest-semiprime` directory provides readable copies of the latest three
reports and their manifests and reviews.

This is an archival checkpoint. Reviewed results remain reviewed; exploratory
notes remain unreviewed; historical validation remains historical. Neither RH
nor the guaranteed one-sixth semiprime factorization goal is established by
this snapshot. The faithful ANY-zero carrier has near-linear construction;
its long scalar evaluation and guaranteed arithmetic coverage remain open.

Verify every object and readable copy with:

```sh
python3 docs/research-evidence/research-checkpoint-20261012/restore.py --verify
```

To restore files under a separate directory, use:

```sh
python3 docs/research-evidence/research-checkpoint-20261012/restore.py \
  --destination /path/to/restored-evidence
```

Restored paths retain the original hierarchy beneath that destination. For
example, an original `/tmp/example/report.md` becomes
`/path/to/restored-evidence/tmp/example/report.md`. Existing files with different
bytes are refused. Use `--select '*/semiprime-any-zero-frontier-20261008/*'`
to verify or restore a subset. Missing old references are recorded explicitly
in the index; they are not represented as preserved or verified evidence.

Compiler caches, Git metadata and Python bytecode are excluded. Historical
source and journal snapshots preserve the old audit hashes across the later
root registration and toolchain migration.
