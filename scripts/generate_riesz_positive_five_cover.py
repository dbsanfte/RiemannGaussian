#!/usr/bin/env python3
"""Generate an optional, exhaustive positive-five interior certificate.

Floats choose subdivisions and proposed bounds. All cuts and totals are
rational; Lean checks both harmonic cap bounds, every leaf, every cut, and
the complete integral inequality. Generation alone certifies nothing.
"""

import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
import hashlib
import heapq
import json
import math
from pathlib import Path


@dataclass
class Node:
    box: tuple
    path: tuple
    lower: Q = Q(0)
    bound: Q = Q(0)
    axis: int = -1
    cut: Q = Q(0)
    left: object = None
    right: object = None
    size: int = 1
    total: Q = Q(0)


def rat(x):
    return f'({x.numerator}/{x.denominator} : ℚ)'


def box_literal(box):
    return '![' + ','.join(f'({rat(a)},{rat(b)})' for a, b in box) + ']'


def cap_value(upper, total, height):
    if height == 0:
        return 0.0
    seam = min(upper, height)
    return math.log(total / (total - seam)) + height / total * math.log(
        upper * (total - seam) / (seam * (total - upper)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--splits', type=int, default=100000)
    parser.add_argument('--chunk-leaves', type=int, default=128)
    parser.add_argument('--output', type=Path, default=Path('.lake/riesz-positive-five-cover'))
    args = parser.parse_args()
    if args.splits < 1 or args.chunk_leaves < 1:
        parser.error('split and chunk sizes must be positive')
    lo, hi, owner = Q(693, 1000), Q(1733, 2500), Q(119, 200)
    low, high = float(lo), float(hi)
    root = Node((((3*lo-1)/2, owner),
                 ((lo-owner)/2, (1-(3*lo-1)/2)/3),
                 ((lo-owner)/2, (1-lo)/2)), ())

    def parameters(box):
        (pl, ph), (bl, bh), (al, ah) = box
        upper = min(bh, 1-pl-bl-2*al)
        offset = max(0, low-ph-bh, 2*low-2*ph-bh-ah)
        height = max(0, min(high-pl, 1+2*ph-3*low))
        total = 1-ph-bh-ah
        return upper, offset, height, total, low*pl*bl*al

    def estimate(box):
        upper, offset, height, total, den = parameters(box)
        if box[1][0] >= box[2][1] or height <= 0 or upper <= offset:
            return 0.0
        volume = math.prod(b-a for a, b in box)
        if total <= upper:
            return 1e6*volume
        return max(0, cap_value(upper, total, offset+height)
                   - cap_value(upper, total, offset))/den*volume

    def best_split(box):
        options = []
        for axis in range(3):
            a, b = box[axis]
            mid = (a+b)/2
            left = box[:axis]+((a, mid),)+box[axis+1:]
            right = box[:axis]+((mid, b),)+box[axis+1:]
            value = estimate(left)+estimate(right)
            options.append((value, -(b-a), axis))
        return min(options)[2]

    queue, serial = [], 0

    def push(node):
        nonlocal serial
        fbox = tuple(tuple(map(float, pair)) for pair in node.box)
        cost = estimate(fbox)
        if cost > 0:
            heapq.heappush(queue, (-cost, serial, node, best_split(fbox)))
            serial += 1

    push(root)
    for step in range(args.splits):
        if not queue:
            break
        _, _, node, axis = heapq.heappop(queue)
        a, b = node.box[axis]
        cut = (a+b)/2
        node.axis, node.cut = axis, cut
        node.left = Node(node.box[:axis]+((a, cut),)+node.box[axis+1:],
                         node.path+((axis, cut, False),))
        node.right = Node(node.box[:axis]+((cut, b),)+node.box[axis+1:],
                          node.path+((axis, cut, True),))
        push(node.left)
        push(node.right)
        if (step+1) % 10000 == 0:
            print(json.dumps({'splits': step+1, 'positive_leaves': len(queue),
                              'floating_upper': -sum(row[0] for row in queue)}), flush=True)

    def account(node):
        if node.axis >= 0:
            ls, lt = account(node.left)
            rs, rt = account(node.right)
            node.size, node.total = ls+rs, lt+rt
            return node.size, node.total
        # Recompute EVERY leaf, including zero-priority children, using
        # exact rational geometric endpoints before proposing cap bounds.
        (pl, ph), (bl, bh), (al, ah) = node.box
        upper = min(bh, 1-pl-bl-2*al)
        offset = max(Q(0), lo-ph-bh, 2*lo-2*ph-bh-ah)
        height = max(Q(0), min(hi-pl, 1+2*ph-3*lo))
        total = 1-ph-bh-ah
        if bl < ah and height > 0 and upper > offset:
            if upper >= total:
                raise RuntimeError('unresolved nonintegrable envelope; increase --splits')
            small = cap_value(float(upper), float(total), float(offset))
            big = cap_value(float(upper), float(total), float(offset+height))
            node.lower = Q(math.floor((small-1e-5)*10**9), 10**9) if offset else Q(0)
            proposed = (big-float(node.lower)+1e-5)/float(lo*pl*bl*al)
            node.bound = Q(math.ceil(proposed*10**7), 10**7)
        node.total = node.bound*math.prod(b-a for a, b in node.box)
        return node.size, node.total

    account(root)
    chunks = []

    def partition(node):
        if node.size <= args.chunk_leaves:
            chunks.append(node)
        else:
            partition(node.left)
            partition(node.right)

    partition(root)
    module = 'RieszPositiveFiveInterior'
    args.output.mkdir(parents=True, exist_ok=True)
    module_dir = args.output/module
    module_dir.mkdir(parents=True, exist_ok=True)
    header = '''/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPositiveFiveCover
open RiemannGaussian ZetaRieszPositiveFiveCover
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
'''

    def tree(node):
        if node.axis < 0:
            return f'.leaf ({rat(node.lower)},{rat(node.bound)})'
        return f'.split {node.axis} {rat(node.cut)} ({tree(node.left)}) ({tree(node.right)})'

    outputs = []
    chunk_index = {id(node): i for i, node in enumerate(chunks)}
    constants = (f'def low : ℚ := {rat(lo)}\ndef high : ℚ := {rat(hi)}\n'
                 f'def owner : ℚ := {rat(owner)}\n')
    for i, node in enumerate(chunks):
        path = module_dir/f'Chunk{i:04d}.lean'
        body = header+f'namespace {module}.Chunk{i:04d}\n'+constants
        body += f'def root : Cover.Box := {box_literal(node.box)}\n'
        body += f'def tree : Cover.Tree := {tree(node)}\n'
        body += 'theorem checked : Cover.check (check low high owner) tree root = true := by decide +kernel\n'
        body += f'theorem total_eq : (Cover.totals tree root).2 = {rat(node.total)} := by decide +kernel\n'
        body += f'end {module}.Chunk{i:04d}\n'
        path.write_text(body)
        outputs.append({'file': path.relative_to(args.output).as_posix(), 'leaves': node.size,
                        'total': str(node.total),
                        'path': [[axis, str(cut), right] for axis, cut, right in node.path],
                        'sha256': hashlib.sha256(body.encode()).hexdigest()})
    assembly = ''.join(f'import {module}.Chunk{i:04d}\n' for i in range(len(chunks)))
    assembly += 'open RiemannGaussian ZetaRieszPositiveFiveCover\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nset_option Elab.async false\n'
    assembly += f'namespace {module}.Assembly\n'+constants
    counter = 0

    def assemble(node):
        nonlocal assembly, counter
        name = f'part{counter:04d}'
        counter += 1
        if id(node) in chunk_index:
            chunk = f'{module}.Chunk{chunk_index[id(node)]:04d}'
            assembly += f'abbrev {name}_box := {chunk}.root\nabbrev {name}_tree := {chunk}.tree\n'
            assembly += f'theorem {name}_checked : Cover.check (check low high owner) {name}_tree {name}_box = true := {chunk}.checked\n'
            assembly += f'theorem {name}_total : (Cover.totals {name}_tree {name}_box).2 = {rat(node.total)} := {chunk}.total_eq\n'
            return name, [f'{name}_box', f'{chunk}.root']
        left, ldefs = assemble(node.left)
        right, rdefs = assemble(node.right)
        assembly += f'def {name}_box : Cover.Box := {box_literal(node.box)}\n'
        assembly += f'def {name}_tree : Cover.Tree := .split {node.axis} {rat(node.cut)} {left}_tree {right}_tree\n'
        for side, child, defs in [('left', left, ldefs), ('right', right, rdefs)]:
            assembly += f'theorem {name}_{side} : CertifiedBoxCover.{side}Box {name}_box {node.axis} {rat(node.cut)} = {child}_box := by\n'
            # Kernel reduction also handles the last coordinate of Fin 3;
            # norm_num alone can leave its Function.update unreduced.
            assembly += '  funext i\n  fin_cases i <;> decide +kernel\n'
        assembly += f'theorem {name}_checked : Cover.check (check low high owner) {name}_tree {name}_box = true := by\n'
        assembly += f'  rw [{name}_tree,Cover.check,{name}_left,{name}_right,{left}_checked,{right}_checked]\n  decide +kernel\n'
        assembly += f'theorem {name}_total : (Cover.totals {name}_tree {name}_box).2 = {rat(node.total)} := by\n'
        assembly += f'  simp only [{name}_tree,Cover.totals,{name}_left,{name}_right,{left}_total,{right}_total]\n  norm_num\n'
        return name, [name+'_box']

    root_name, _ = assemble(root)
    upper = Q(1, 250) if root.total <= Q(1, 250) else Q(math.ceil(root.total*10**6), 10**6)
    assembly += '/-- Complete positive-five angular debit, uniformly over the actual saddle cutoff bin. The literal prime-sum transfer is a separate obligation. -/\n'
    assembly += f'theorem whole_debit_upper {{lam : ℝ}} (hlam : (low : ℝ) ≤ lam ∧ lam ≤ high) :\n'
    assembly += f'    (∫ x in Cover.region {root_name}_box, density lam x) ≤ ({rat(upper)} : ℝ) := by\n'
    assembly += f'  apply integral_le_of_checked_cover {root_name}_tree\n'
    assembly += f'    (by intro i; fin_cases i <;> decide +kernel) {root_name}_checked ?_ hlam\n'
    assembly += f'  rw [{root_name}_total]\n  decide +kernel\nend {module}.Assembly\n'
    assembly_path = module_dir/'Assembly.lean'
    assembly_path.write_text(assembly)
    sources = [Path(__file__), Path('RiemannGaussian/ZetaRieszPositiveFiveCover.lean'),
               Path('RiemannGaussian/ZetaRieszPositiveFiveInterior.lean'),
               Path('RiemannGaussian/ZetaRieszCapacityCheck.lean')]
    report = {'status': 'UNTRUSTED_GENERATED_CERTIFICATE_NOT_YET_CHECKED',
              'low': str(lo), 'high': str(hi), 'owner': str(owner),
              'active_cells': len(queue), 'splits': step+1,
              'total_leaves_including_zero_children': root.size,
              'total_upper': str(root.total), 'approximate_upper': float(root.total),
              'claimed_upper': str(upper), 'chunks': outputs,
              'assembly': {'file': assembly_path.relative_to(args.output).as_posix(),
                           'sha256': hashlib.sha256(assembly.encode()).hexdigest()},
              'source_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}}
    (args.output/'manifest.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: report[k] for k in ('status', 'active_cells',
                     'total_leaves_including_zero_children', 'approximate_upper',
                     'claimed_upper')} | {'chunks': len(chunks)}), flush=True)


if __name__ == '__main__':
    main()
