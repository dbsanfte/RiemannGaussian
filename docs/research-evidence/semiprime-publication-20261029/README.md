# Semiprime proof publication checkpoint — 2026-10-29

The research goal is **paused and incomplete**. This packet publishes the current
proof sources and available validation records; it does not announce a complete
kernel-checked total-bit factoring algorithm. The target remains
`2^(C*ell/sqrt(log(ell+2)))*(ell+1)^d`, with fixed constants before all semiprime
inputs. The existing public algorithm correctness theorem is separate from that
whole primitive-bit running-time theorem.

[inventory.json](inventory.json) indexes every current canonical semiprime source
by repository path and SHA256. [progress.json](progress.json) gives curated
algorithm stages, source/declaration anchors and remaining obligations. The stage
order is explanatory: it is **not** an extracted semantic or import dependency
graph. [validation-index.json](validation-index.json) indexes copied evidence.

At this checkpoint there are 3,160 current semiprime Lean files, comprising
439,184 source lines and approximately 24.6 MB. The authoritative latest checkpoint
contains 82 historical FINAL component records: the 80 groups named by the
preservation snapshot, plus Factory115/Ready258 and KernelLinear29. Their 1,410
group memberships cover 1,398 distinct source files (about 8.55 MB). Memberships
overlap, so their declaration/theorem totals must not be added as unique totals.
The index also retains 58 supplementary historical reports outside this selected
checkpoint set.

The module labels mean:

- `finalized-machine`: a source belongs to one of the historically finalized
  physical-machine components. Its prepared-input boundary and outstanding caller
  joins still matter; the label does not establish the whole public bit-time goal.
- `proved-math`: a historically checked mathematical component, without an
  independent runtime completion claim.
- `draft`: the nine unsealed OldVertexStream files. A publication-only repair and
  successful fresh compilation would not by themselves confer final review,
  source execution/resource closure or a FINAL group designation.
- `legacy-unclassified`: a source lies outside the latest checkpoint's status
  classification. This is **not** an assertion that its mathematics is unproved
  or that it failed compilation.

The initial classification is 1,380 finalized-machine files, 18 proved-math files,
nine draft files and 1,753 legacy-unclassified files. Three unchanged historical
external bridge snapshots appear separately under
[external-bridges](external-bridges/manifest.json). They are outside the current
ordinary-build source set; the parent-owned archive manifest records their
original locations, upstream dependencies and reason for archival.

The `manifests`, `reviews`, `audits`, `controls` and `pins` directories contain
byte-identical copies of available scratch records. These are **historical sealing
evidence**. In particular, their generated `.olean` hashes, ordinary-root audits,
independent-object comparisons and control runs describe the historical component
checks, not a new run made by this packaging task. Generated objects and bulk
dependency snapshots are not copied. Twenty convention-matching component audit
log files were not located by the packager; the corresponding sealing manifests
are retained and the omissions are explicit in the validation index. An absent
copied log is not reported as a failed audit. Earlier records lost before the
scratch directory was recreated are not reconstructed or invented.

The packager freshly checks current source hashes against the retained FINAL
source pins and hashes every copied evidence file. It runs **no Lean builds or
controls** and makes no research changes. The parent runs the separate fresh
ordinary-library publication build and publication gates. Those results must be
reported separately. A fresh build may legitimately regenerate objects with
different hashes or compiler options; equality to historical `.olean` hashes is
not assumed. Historical source reviews remain historical even when the source
hash is still current.

The [fresh publication verification](fresh-publication/README.md) now records a
successful ordinary build and all 23 publication gates, with exact log hashes
and the setup, documentation and generated-asset repairs retained separately.
The compiled audit found zero project axioms and zero placeholder-dependent
declarations. Remote CI and deployment are checked against the pushed revision;
these local records do not assert their result.

The main remaining boundaries are literal child-record/recursive-child producer
joins, complete current-node mode/phase/grid callers, whole recovery input and
numerator construction, and one scalar-producing finite machine with a single
original-input total-bit bound. Several prepared sources and mathematical
identities are finalized independently; their existence is not silently promoted
to a completed end-to-end controller.

`package_inventory.py` regenerates these indexes and copies available compact
records from the scratch checkpoint. It writes only inside this packet, leaves
the parent-owned external bridge archive untouched, and never reads live
generated-object hashes during a publication rebuild. No existing Lean source,
old journal or Git state is modified by it.

Publication guidance was read from `AGENTS.md`: the current theorem-push gate
(lines 1603–1624) requires ordinary registration/publication checks and honest
open-premise reporting; the latest semiprime target (from line 26949) distinguishes
the requested total-bit rate from retained-report milestones. The explicit new
publication authorization supersedes older local-only publication holds. This
packet does not resume the paused research goal.

The publication whitespace gate preserves existing audited source/evidence
bytes. [preserved-whitespace.json](preserved-whitespace.json) lists the exact
staged SHA256 and existing trailing-whitespace or blank-final-line findings
for each exception. The checker accepts only those findings with matching
bytes; changed files, new findings and conflict markers still fail. This is
separate from compilation, source pinning and the axiom audit.
