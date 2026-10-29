#!/usr/bin/env python3
"""Refresh only this integration packet's explorer inputs; never invokes Lean.

The historical publication packet and its 82 groups are immutable inputs.
Run after all source writers stop, then run this packet's check_inventory.py.
Fresh compiled audits are maintained separately by the integration owner.
"""
from __future__ import annotations
import collections
import copy
import datetime
import hashlib
import json
from pathlib import Path
import re

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[2]
BASE = ROOT / 'docs/research-evidence/semiprime-publication-20261029'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def anchor(module, declaration=None):
    result = {'module': 'RiemannGaussian.' + module}
    if declaration:
        result['declaration'] = 'RiemannGaussian.' + declaration
    return result

SCOPE = ('Current native mathematical correctness and retained operation-report scope. '
         'This is not a finalized primitive-machine implementation or a complete original-input bit-time theorem. '
         'This inventory performs source-hash checks only; compiled verification is separate integration evidence.')
NEW_STAGES = [
    {'id': 'boundary-partition', 'title': 'Acquire a deterministic boundary partition', 'status': 'proved',
     'summary': 'The actual integer colour search, local conditional averaging and occurrence-covariance bound close simultaneously. The executed partition has width at most M/2 + 3*cuberoot(M^2*Delta), with no supplied good colouring.',
     'remaining': ['Physical finite-machine realization and its complete primitive-bit costs remain open.'],
     'groups': [], 'proof_anchors': [
         anchor('SemiprimeD1BoundaryConditionalAverage', 'SemiprimeD1BoundaryConditionalAverage.acquire_potential_le'),
         anchor('SemiprimeD1BoundaryPartitionWidthRate', 'SemiprimeD1BoundaryPartitionWidthRate.acquired_width_cuberoot'),
         anchor('SemiprimeD1BoundaryPartitionReachRate', 'SemiprimeD1BoundaryPartitionReachRate.eventually_reach_stopped_width_half')],
     'scope_note': 'Native executed partition and proof-only finite expectation identities. The uniform stopped-leaf half exponent includes empty graphs; the zero-fuel companion requires the original scheduled depth/fuel condition.'},
    {'id': 'boundary-record-leaf', 'title': 'Contract full jets through sorted boundary records', 'status': 'proved',
     'summary': 'The concrete leaf contracts full jet tensors through sorted occurrence records and preserves the complete canonical leaf bytes. Under the stated original context and degree caps, its complete checked native report, including paid validation, fits 2^((1/2 + epsilon)*s/sqrt(logarithm s)).',
     'remaining': ['The native operation report is not a complete primitive-machine bit-time certificate.'],
     'groups': [], 'proof_anchors': [
         anchor('SemiprimeD1BoundaryLeafValue', 'SemiprimeD1BoundaryLeaf.run_words'),
         anchor('SemiprimeD1BoundaryLeafPolynomial', 'SemiprimeD1BoundaryLeafPolynomial.run_clock_polynomial'),
         anchor('SemiprimeD1BoundaryCheckedOriginalRate', 'SemiprimeD1BoundaryCheckedOriginalRate.eventually_checked_uniform_half'),
         anchor('SemiprimeD1BoundaryLeafOriginalReachRate', 'SemiprimeD1BoundaryLeafOriginalReachRate.eventually_original_stopped_half')],
     'scope_note': 'Full-jet native semantics, actual sorted-record costs and the complete checked leaf retained report. The original-input Reach corollary derives all context, size and degree caps. Its zero-fuel companion requires scheduled original fuel exhaustion; no arbitrary zero-fuel root or physical-stack cost promotion is claimed.'},
    {'id': 'hybrid-public-correctness', 'title': 'Return exact factors with a closed native report', 'status': 'proved',
     'summary': 'The changed hybrid recursion and public decoder return the exact original binary factor bytes. Its actual own mixed native report now has a closed eventual bound 2^(C*inputScale(ell)), paying acquired prefixes, changed recursion, checked partition/contraction leaves and decoding, with no supplied prefix-clock premise.',
     'remaining': ['A fixed primitive-machine realization must still pay every bit operation, address, tape and coefficient cost before the complete total-bit theorem follows.'],
     'groups': [], 'proof_anchors': [
         anchor('SemiprimeD1HybridAlgorithm', 'SemiprimeD1HybridAlgorithm.factor_complete'),
         anchor('SemiprimeD1HybridCorrectness', 'SemiprimeD1HybridPublicExecution.run_factors_eq_tape'),
         anchor('SemiprimeD1HybridOriginalRate', 'SemiprimeD1HybridOriginalRate.eventually_public_report_rate'),
         anchor('SemiprimeD1HybridAlgorithm', 'SemiprimeD1HybridAlgorithm.report_rate')],
     'scope_note': 'Exact changed-algorithm correctness and its closed mixed native retained-report rate. The constant precedes all sufficiently large bit lengths and compact positive inputs. This report mixes native operations and existing component allowances; it is not one complete primitive bit-machine simulation, and it does not substitute the old WordTape counter budget for changed recursion.'},
    {'id': 'tighter-original-call-envelope', 'title': 'Tighten the original controller call envelope', 'status': 'proved',
     'summary': 'The sharper child shrink gives a summable call-count envelope and smaller leading constant. Its public-report rate transport applies explicitly to the existing WordTapePublicReport controller and budget.',
     'remaining': ['This result supplies no new whole-counter budget for the changed hybrid recursion.'],
     'groups': [], 'proof_anchors': [
         anchor('SemiprimeD1HybridCallOriginal', 'SemiprimeD1HybridCallOriginal.eventually_original_call_rate'),
         anchor('SemiprimeD1HybridCallReport', 'SemiprimeD1HybridCallReport.eventually_public_report_rate')],
     'scope_note': 'Improved actual original call count and the old WordTapePublicReport rate scope. Theorem/file naming does not assert that the new hybrid public report has the same complete counter budget.'}
]

def refresh():
    inventory = copy.deepcopy(json.loads((BASE / 'inventory.json').read_text()))
    progress = copy.deepcopy(json.loads((BASE / 'progress.json').read_text()))
    original = {row['path']: row for row in inventory['modules']}
    root_source = ROOT / 'RiemannGaussian.lean'
    registered = set(re.findall(r'^import\s+(\S+)', root_source.read_text(), re.M))
    modules = []
    for path in sorted((ROOT / 'RiemannGaussian').glob('Semiprime*.lean')):
        rel = path.relative_to(ROOT).as_posix()
        raw = path.read_bytes()
        if rel in original:
            row = copy.deepcopy(original[rel])
            assert sha(path) == row['sha256'], ('historical current source changed', rel)
        else:
            row = {'module': 'RiemannGaussian.' + path.stem, 'path': rel,
                   'status': 'proved-math', 'groups': [], 'evidence': [],
                   'validation': {'basis': 'new-native-integration-source-scan', 'fresh_lean_build': False,
                                  'current_source_hash_checked': True,
                                  'validation_scope': 'Source inventory scan only; parent compiled audits and focused source/object evidence are separate.'},
                   'scope_note': SCOPE}
        row.update(sha256=sha(path), bytes=len(raw), lines=len(raw.decode().splitlines()),
                   root_registered_at_inventory_scan=row['module'] in registered)
        modules.append(row)
    assert set(original) <= {row['path'] for row in modules}, 'Historical current module disappeared'
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    inventory['generated_at_utc'] = progress['generated_at_utc'] = now
    inventory['modules'] = modules
    inventory['root_registration_snapshot'] = {'path': 'RiemannGaussian.lean', 'sha256': sha(root_source), 'direct_imports': len(registered)}
    inventory['validation_policy']['fresh_by_packager'] = 'Current source and retained evidence SHA256 scan only; this refresh script invokes no Lean or Lake. Separate parent integration compilation/audits are not claimed by the inventory.'
    inventory['validation_policy']['new_native_scope'] = SCOPE
    inventory['validation_policy']['fresh_publication_build'] = {'status': 'parent-integration-evidence-separate', 'historical_object_equality_not_assumed': True}
    summary = inventory['summary']
    summary.update(current_semiprime_sources=len(modules), current_source_bytes=sum(r['bytes'] for r in modules),
                   current_source_lines=sum(r['lines'] for r in modules),
                   module_status_counts=dict(collections.Counter(r['status'] for r in modules)))
    progress['summary'] = copy.deepcopy(summary)
    progress['validation_epoch'] = 'Preserved historical groups plus fresh current source/evidence hash scan; native integration compiled audits are separate parent evidence.'
    stages = progress['stages']
    correctness = next(s for s in stages if s['id'] == 'algorithm-correctness')
    correctness['summary'] = 'The mathematical factoring algorithm and the changed boundary hybrid have exact original-binary factor-byte correctness proofs. Complete primitive-bit running time remains open.'
    correctness['proof_anchors'].append(anchor('SemiprimeD1HybridCorrectness', 'SemiprimeD1HybridPublicExecution.run_complete'))
    physical = next(s for s in stages if s['id'] == 'recursive-counter')
    physical['scope_note'] += ' This historical physical-counter frontier is distinct from the newly closed native hybrid correctness and own-report joins.'
    readout = next(s for s in stages if s['id'] == 'factor-readout')
    readout['remaining'] = ['The complete primitive-machine original-N scalar-producing recursive counter remains open; new native hybrid factor-byte correctness is recorded separately.']
    index = next(i for i, s in enumerate(stages) if s['id'] == 'whole-bit-target')
    stages[index:index] = copy.deepcopy(NEW_STAGES)
    for filename, value in [('inventory.json', inventory), ('progress.json', progress)]:
        (PACKET / filename).write_text(json.dumps(value, indent=2) + '\n')
    print(json.dumps({'status': 'REFRESHED_SOURCE_SCAN_NOT_LEAN_BUILD', 'current_sources': len(modules),
                      'new_native_sources': len(modules)-len(original), 'historical_groups': len(inventory['groups']),
                      'stages': len(stages), 'writers_must_stop_before_final_refresh': True}, sort_keys=True))

if __name__ == '__main__':
    refresh()
