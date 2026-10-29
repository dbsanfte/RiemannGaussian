#!/usr/bin/env python3
"""Package historical proof evidence and current source hashes; never run Lean.

Only files below this publication packet are written. Historical generated
objects are referenced by their recorded hashes, never inspected during the
parent's separate publication rebuild. The external-bridges subdirectory is
parent-owned and is only read here.
"""
from pathlib import Path
import collections
import datetime
import hashlib
import json
import re

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[2]
SCRATCH = Path('/tmp/semiprime-explicit-rate-20261027')
PREFIX = str(PACKET.relative_to(ROOT))
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
read = lambda p: json.loads(Path(p).read_text())
write = lambda name, data: (PACKET / name).write_text(json.dumps(data, indent=2) + '\n')
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
evidence = []
copied = {}
missing = []


def retain(path, kind, group=None):
    path = Path(path)
    if not path.is_absolute():
        path = SCRATCH / path
    if not path.is_file():
        missing.append({'path': str(path), 'kind': kind, 'group': group, 'reason': 'historical referenced file unavailable'})
        return None
    if str(path) in copied:
        return copied[str(path)]
    if path.stat().st_size > 600_000:
        missing.append({'path': str(path), 'sha256': sha(path), 'bytes': path.stat().st_size,
                        'kind': kind, 'group': group, 'reason': 'not copied: compact packet excludes large dependency maps/logs'})
        return None
    folder = {'manifest': 'manifests', 'review': 'reviews', 'audit': 'audits',
              'control': 'controls', 'pins': 'pins', 'checkpoint': 'checkpoints'}.get(kind, 'support')
    target = PACKET / folder / (((group + '--') if group and kind != 'manifest' else '') + path.name)
    target.parent.mkdir(parents=True, exist_ok=True)
    original = path.read_bytes()
    target.write_bytes(original)
    assert target.read_bytes() == original
    item = {'id': str(target.relative_to(PACKET)), 'path': str(target.relative_to(ROOT)),
            'sha256': sha(target), 'bytes': len(original), 'kind': kind,
            'status': 'historical-record', 'validation_epoch': 'historical',
            'original_path': str(path), 'copy': 'byte-identical', 'group': group}
    evidence.append(item)
    copied[str(path)] = item
    return item


def refs(value):
    if isinstance(value, dict):
        for key, child in value.items():
            yield key, child
            yield from refs(child)
    elif isinstance(value, list):
        for child in value:
            yield from refs(child)


def module_pins(record, report):
    if isinstance(record.get('modules'), dict):
        return record['modules']
    if isinstance(record.get('files'), dict) and 'source' in record['files']:
        return {report: record['files']}
    for key in ('pins', 'source_object_pins', 'source_canonical_pins'):
        ptr = record.get(key)
        if isinstance(ptr, str):
            path = Path(ptr)
            path = path if path.is_absolute() else SCRATCH / path
            if path.is_file():
                retain(path, 'pins', report.removesuffix('-verification.json'))
                data = read(path)
                if isinstance(data, dict):
                    return data
    return {}


checkpoint = read(SCRATCH / 'root-current-preservation.json')
authoritative = list(checkpoint['new_closed_groups'])
for name, count in [('child-group-factory-verification.json', 172), ('kernel-linear-verification.json', 25)]:
    if not any(row['report'] == name for row in authoritative):
        authoritative.append({'report': name, 'modules': count})
assert len(authoritative) == 82
retain(SCRATCH / 'root-current-preservation.json', 'checkpoint')
math_groups = {'packed-moment', 'packed-network-semantics', 'packed-network-original',
               'root-record-coordinates', 'all-descriptor-root-envelope', 'child-vertex-endpoint'}
groups = []
by_source = collections.defaultdict(list)
group_evidence = {}
for entry in authoritative:
    report = entry['report']
    record = read(SCRATCH / report)
    gid = report.removesuffix('-verification.json')
    manifest = retain(SCRATCH / report, 'manifest', gid)
    pins = module_pins(record, report)
    assert len(pins) == entry['modules'], (gid, len(pins), entry['modules'])
    source_rows = []
    for _, row in pins.items():
        source = row['source']
        path = Path(source['path'])
        assert sha(path) == source['sha256'], ('historical FINAL source changed', gid, str(path))
        canonical = row.get('canonical', {})
        rel = str(path.relative_to(ROOT))
        item = {'module': 'RiemannGaussian.' + path.stem, 'path': rel,
                'sha256': source['sha256'], 'historical_object': canonical,
                'historical_object_scope': 'recorded at component seal; publication rebuild may replace generated objects'}
        source_rows.append(item)
        by_source[rel].append((gid, manifest, 'proved-math' if gid in math_groups else 'finalized-machine', item))
    support = []
    for key, val in refs(record):
        candidate = val.get('path') if isinstance(val, dict) else val if isinstance(val, str) else None
        if candidate and 'review' in candidate.lower() and Path(candidate).suffix in ('.txt', '.md', '.json'):
            # Several historical records use prose such as "PASS; see foo.txt".
            # Resolve the literal filename, not the whole prose as a path.
            if not Path(candidate).is_file() and not (SCRATCH / candidate).is_file():
                named = re.search(r'([A-Za-z0-9_.-]*review[A-Za-z0-9_.-]*\.(?:txt|md|json))', candidate)
                if named:
                    candidate = str(SCRATCH / named.group(1))
            ev = retain(candidate, 'review', gid)
            if ev and ev not in support:
                support.append(ev)
    audit = SCRATCH / (gid + '-frozen') / 'audit.log'
    if audit.exists():
        ev = retain(audit, 'audit', gid)
        if ev:
            support.append(ev)
    else:
        missing.append({'path': str(audit), 'kind': 'audit', 'group': gid,
                        'reason': 'No convention-matching compact audit log located; historical manifest retained. This does not assert an audit failure.'})
    for control in record.get('controls', []) if isinstance(record.get('controls'), list) else []:
        if isinstance(control, dict):
            for key in ('source', 'log'):
                val = control.get(key)
                p = val.get('path') if isinstance(val, dict) else val if isinstance(val, str) else None
                if p:
                    ev = retain(p, 'control', gid)
                    if ev:
                        support.append(ev)
    groups.append({'id': gid, 'status': 'finalized-component', 'checkpoint_set': 'authoritative-latest-82',
                   'reported_status': record.get('status'), 'path': manifest['path'], 'sha256': manifest['sha256'],
                   'validation_epoch': 'historical', 'fresh_publication_build': False,
                   'module_count': len(source_rows), 'counts': record.get('counts'),
                   'scope': record.get('scope', record.get('stage', 'See the original historical manifest.')),
                   'modules': source_rows, 'evidence': [{'path': ev['path'], 'sha256': ev['sha256']} for ev in support]})
    group_evidence[gid] = manifest

# Other scratch records are preserved without silently promoting them to the
# latest sealed checkpoint or claiming a fresh build. Some are partial helpers.
known = {entry['report'] for entry in authoritative}
supplementary = []
for path in sorted(SCRATCH.glob('*verification.json')):
    if path.name in known:
        continue
    try:
        record = read(path)
    except (ValueError, OSError):
        continue
    if str(record.get('status', '')).startswith('FINAL'):
        ev = retain(path, 'manifest', path.stem)
        if ev:
            supplementary.append({'id': path.stem, 'path': ev['path'], 'sha256': ev['sha256'],
                                  'reported_status': record.get('status'), 'status': 'historical-supporting-record',
                                  'scope_note': 'Outside the authoritative latest-82 set; not used to infer a finalized current machine boundary.'})

modules = []
for path in sorted((ROOT / 'RiemannGaussian').glob('Semiprime*.lean')):
    rel = str(path.relative_to(ROOT))
    memberships = by_source.get(rel, [])
    is_draft = path.stem.startswith('SemiprimeD1StackOldVertexStream')
    status = 'draft' if is_draft else ('finalized-machine' if any(row[2] == 'finalized-machine' for row in memberships)
                                     else 'proved-math' if memberships else 'legacy-unclassified')
    modules.append({'module': 'RiemannGaussian.' + path.stem, 'path': rel, 'sha256': sha(path),
                    'bytes': path.stat().st_size, 'lines': len(path.read_text().splitlines()),
                    'status': status, 'groups': [row[0] for row in memberships],
                    'evidence': [{'path': row[1]['path'], 'sha256': row[1]['sha256']} for row in memberships],
                    'validation': {'basis': 'historical-final-source-pins' if memberships else 'unsealed-current-source' if is_draft else 'outside-latest-checkpoint-classification',
                                   'fresh_lean_build': False, 'current_source_hash_checked': True},
                    'scope_note': 'Unsealed OldVertexStream work; a publication-only compilation repair does not confer FINAL review.' if is_draft
                                  else 'Member of a historically finalized physical-machine component; does not imply a completed public factoring runtime.' if status == 'finalized-machine'
                                  else 'Historically checked mathematical component; no independent runtime certificate inferred.' if status == 'proved-math'
                                  else 'Legacy source; status not classified by this latest-checkpoint inventory. This does not assert a failed or missing proof.'})

archive_manifest = PACKET / 'external-bridges' / 'manifest.json'
archived = []
if archive_manifest.exists():
    for path in sorted((PACKET / 'external-bridges').glob('*.lean.txt')):
        archived.append({'path': str(path.relative_to(ROOT)), 'sha256': sha(path), 'bytes': path.stat().st_size,
                         'status': 'archived-external-bridge', 'validation_epoch': 'historical',
                         'scope_note': 'Unchanged historical external bridge; not a current ordinary-build Lean module.',
                         'provenance': str(archive_manifest.relative_to(ROOT))})

root_source = ROOT / 'RiemannGaussian.lean'
root_text = root_source.read_text()
registered = set(re.findall(r'^import\s+(RiemannGaussian\.[A-Za-z0-9_.]+)', root_text, re.M))
for module in modules:
    module['root_registered_at_inventory_scan'] = module['module'] in registered
stats = {'current_semiprime_sources': len(modules), 'current_source_bytes': sum(row['bytes'] for row in modules),
         'current_source_lines': sum(row['lines'] for row in modules), 'module_status_counts': dict(collections.Counter(row['status'] for row in modules)),
         'authoritative_final_groups': len(groups), 'final_group_memberships': sum(row['module_count'] for row in groups),
         'unique_final_source_files': len(by_source), 'historical_final_source_bytes': sum((ROOT / p).stat().st_size for p in by_source),
         'supplementary_historical_records': len(supplementary), 'archived_source_snapshots': len(archived)}
inventory = {'schema_version': 1, 'generated_at_utc': now,
             'research_goal': {'status': 'paused', 'full_goal_complete': False,
                               'target': 'deterministic ALL-semiprime factoring from binary N; 2^(C*ell/sqrt(log(ell+2)))*(ell+1)^d total bit time, fixed C,d',
                               'ell': 'ceil(log2(N+1))', 'publication_is_not_goal_completion': True},
             'validation_policy': {'historical': 'Copied sealing manifests/reviews/audits are historical evidence, byte-identical to scratch originals. Their recorded generated-object hashes are not fresh-build claims.',
                                   'fresh_by_packager': 'Read-only source/evidence SHA256 checks only; no Lean, Lake, controls, or research actions.',
                                   'fresh_publication_build': {'status': 'parent-run-separate-evidence-pending', 'historical_object_equality_not_assumed': True},
                                   'legacy_unclassified': 'Outside latest-82 classification; not an assertion of unproved mathematics.'},
             'root_registration_snapshot': {'path': 'RiemannGaussian.lean', 'sha256': sha(root_source), 'direct_imports': len(registered)},
             'summary': stats, 'modules': modules, 'groups': groups, 'evidence': evidence,
             'supplementary_historical_records': supplementary, 'archived_sources': archived,
             'missing_or_intentionally_uncopied_records': missing}
write('inventory.json', inventory)
write('validation-index.json', {'schema_version': 1, 'generated_at_utc': now, 'evidence': evidence,
                              'missing_or_intentionally_uncopied_records': missing,
                              'fresh_build_status': 'parent-run-separate-evidence-pending', 'no_fresh_Lean_build_by_packager': True})

def anchors(*names):
    present = {row['module'] for row in modules}
    return [{'module': 'RiemannGaussian.' + name} for name in names if 'RiemannGaussian.' + name in present]

stage_rows = [
 ('algorithm-correctness','Mathematical factoring correctness','proved','The public native algorithm has a correctness theorem; this is separate from a whole primitive-bit running-time certificate.',[],['The full original-input finite-machine time theorem remains open.'],['SemiprimeD1PublicCorrectness','SemiprimeD1PackedMomentRecovery']),
 ('root-records','Acquire the original network from binary N','finalized','Real owner/factor sources produce exact original records, with actual acquisition clocks and all allocated tapes counted.',['root-network-records','full-factor-catalogue-final','root-owner-index'],[],['SemiprimeD1StackRootNetworkRecordsOriginal','SemiprimeD1StackFullFactorCatalogueOriginal']),
 ('selection-and-packets','Acquire selection and packet metadata','finalized','Original-N sources acquire rows, incidences, colour selection, keys, padding and packet inventory; no supplied topology answers.',['root-selection-acquire','root-packet-padding','root-packet-inventory'],[],['SemiprimeD1StackRootPacketInventoryOriginal','SemiprimeD1StackRootSelectionAcquireOriginal']),
 ('packed-root','Build the marked root and retain its caches','finalized','Packed-moment algebra, marked tables, binary 2ell context and actual weighted root-record input are available; structural caches are reused separately from table payloads.',['packed-moment','marked-root-records','packed-root-input','packed-root-cache-reuse'],[],['SemiprimeD1StackPackedRootInputOriginal','SemiprimeD1PackedRootFactoryInputs']),
 ('weighted-modes','Enumerate feasible weighted modes','partial','A fixed finite controller and catalogue frontend enumerate feasible tuples with real frames and own costs on their prepared physical inputs.',['weighted-mode-core','weighted-mode-catalogue'],['Literal current-node caller and original packet-to-mode input handoff remain to be joined.'],['SemiprimeD1StackWeightedModeExecution','SemiprimeD1StackWeightedModeCatalogueExecution']),
 ('phase-caches','Acquire and restore phase contexts','finalized','Actual phase/fresh records, chronological heap references and full cache restoration are checked, including rejected phases and distinct old/new contexts.',['root-phase-fresh-records','fresh-bank-restore','cache-phase'],[],['SemiprimeD1StackRootPhaseFreshRecordsOriginal','SemiprimeD1StackCachePhaseLineage']),
 ('child-factory','Acquire activation, endpoints and ordered ports','finalized','Core115/Ready258 physically compute exact native activation, ordered endpoint buckets and all old-vertex scope/order streams, including isolated vertices and empty/repeated buckets.',['child-group-factory'],['The literal enclosing N-only call and context-header installation remain separate caller work.'],['SemiprimeD1StackChildGroupFactoryOriginal','SemiprimeD1StackChildGroupFactoryReadyResources']),
 ('child-tables','Construct active and inactive child vertices','mixed','Real Entry61/Table134, active136, inactive32 and literal Choice169 constructors are finalized on prepared physical operands.',['child-table-entry','child-lift-table','child-lift-vertex','child-unit-vertex','child-vertex-choice','child-vertex-endpoint'],['Complete chronological parent-record/activation/scope/order zip and complete child-network assembly remain open.'],['SemiprimeD1StackChildVertexChoiceOriginal','SemiprimeD1StackChildLiftVertexMeaning']),
 ('old-vertex-stream','Join all old child-vertex records','draft','Nine OldVertexStream source files are current work in progress. Publication compilation checks do not constitute a FINAL reviewed group.',[],['Whole execution/resource/original ordered-stream closure and final independent review are not recorded as FINAL.'],['SemiprimeD1StackOldVertexStream','SemiprimeD1StackOldVertexStreamSpec']),
 ('recursive-counter','Run the complete physical recursive counter','open','Many finite source components exist, but one literal original-input controller supplying recursive child answers and the final scalar is unfinished.',[],['Actual recursive child production; mode/phase/grid caller joins; complete scalar-producing machine; one whole original-input clock.'],['SemiprimeD1WordTapeRecursiveCounter','SemiprimeD1WordTapeRecursivePhase']),
 ('phase-folds','Fold child jets and log phase blocks','mixed','Exact right-fold JetFold, block extraction and chronological CachePhaseBank246 are finalized with own costs on actual prepared child-result bytes.',['jet-fold','jet-blocks','cache-phase-bank'],['Recursive child-result production and enclosing original-N joins remain open.'],['SemiprimeD1StackJetFoldOriginal','SemiprimeD1StackCachePhaseBankOriginal']),
 ('recovery-geometry','Acquire recovery geometry and local weights','mixed','Grid104, affine112, normalized inverse58, powers47, weights60, Node141 and KernelLinear29 are checked physical sources with explicit input boundaries.',['recovery-grid','recovery-affine','normalized-inverse','recovery-powers','recovery-weights','recovery-node','kernel-linear'],['Whole canonical-row/kernel-product/fresh-jet construction and the literal caller are not yet assembled.'],['SemiprimeD1StackRecoveryNodeOriginal','SemiprimeD1StackKernelLinearOriginal']),
 ('recovery-data','Acquire coordinate/entry data and denominator','mixed','Physical phase-bank coordinate extraction, two-level entry lookup, common-denominator product and signed recovery finish are finalized on their actual tapes.',['recovery-coordinate','recovery-entries','recovery-denominator','recovery-finish'],['Canonical-row producer, full numerator construction and whole recovery caller still need literal source joins.'],['SemiprimeD1StackRecoveryEntriesOriginal','SemiprimeD1StackRecoveryDenominatorOriginal','SemiprimeD1StackRecoveryFinishOriginal']),
 ('factor-readout','Decode factors from the actual packed scalar','mixed','Mathematical packed channels and physical scalar readout/square root/factor recovery are checked; the scalar word remains a prepared input.',['packed-network-original','packed-moment-readout','binary-square-root','packed-factor-recovery'],['The original-N scalar-producing recursive counter remains open.'],['SemiprimeD1PackedNetworkOriginal','SemiprimeD1StackPackedFactorRecoveryOriginal']),
 ('whole-bit-target','Close the deterministic total-bit theorem','open','The complete kernel-checked original-input bound at the requested exponent is not proved.',[],['Combine all actual acquisition, addressing, recursion, coefficient and recovery clocks for one fixed finite program before deriving the global rate.'],[]),
]
stages = []
for sid,title,status,summary,gids,remaining,names in stage_rows:
    stages.append({'id': sid, 'title': title, 'status': status, 'summary': summary,
                   'remaining': remaining, 'groups': gids, 'proof_anchors': anchors(*names),
                   'scope_note': 'Curated algorithm-stage description; not an extracted Lean dependency edge or a claim that all caller joins are closed.'})
stages[0]['proof_anchors'] = [{'module': 'RiemannGaussian.SemiprimeD1PublicCorrectness', 'declaration': 'RiemannGaussian.SemiprimeD1PublicCorrectness.factorBits_complete'},
                              {'module': 'RiemannGaussian.SemiprimeD1PackedMomentRecovery', 'declaration': 'RiemannGaussian.SemiprimeD1PackedMomentRecovery.factorization'}]
write('progress.json', {'schema_version': 1, 'generated_at_utc': now, 'research_goal': inventory['research_goal'],
                       'curated_stage_order_not_lean_dependencies': True,
                       'dependency_edges': 'No extracted semantic/import dependency graph is claimed. The explorer provides current source and declaration-location links; stage order is curated.',
                       'validation_epoch': 'historical component records plus fresh source/evidence hash scan; parent publication build separate',
                       'summary': stats, 'stages': stages})
print(json.dumps(stats, sort_keys=True))
print('PACKET_BYTES', sum(p.stat().st_size for p in PACKET.rglob('*') if p.is_file()))
