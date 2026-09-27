#!/usr/bin/env python3
"""Emit a COMPLETE untrusted five-prime supply cover for Lean to check.

Floating point chooses refinements and proposed bounds only. Every node,
including zero-priority children, is retained with exact rational cuts.
Generated assertions use `decide +kernel`; generation alone certifies nothing.
The default destination is an optional local scratch directory, not CI.
"""

import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
import hashlib
import heapq
import json
import math
from pathlib import Path

import probe_riesz_ordered_capacity as probe


@dataclass
class Node:
    box: tuple
    path: tuple
    bound: Q = Q(0)
    axis: int = -1
    cut: Q = Q(0)
    left: object = None
    right: object = None
    size: int = 1
    total: Q = Q(0)


def rat(x):
    return f'({x.numerator}/{x.denominator} : ℚ)'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bin', type=int, default=0)
    parser.add_argument('--cells', type=int, default=10000)
    parser.add_argument('--chunk-leaves', type=int, default=16)
    parser.add_argument('--output', type=Path, default=Path('.lake/riesz-five-capacity-cover'))
    args = parser.parse_args()
    assert 0 <= args.bin < 8 and args.cells > 0 and args.chunk_leaves > 0
    probe.LOG_LOWER_TERMS, probe.LOG_UPPER_TERMS = 4, 6
    low, high = Q(693, 1015), Q(139, 195)
    lo = low+(high-low)*args.bin/8-Q(1, 100000)
    hi = low+(high-low)*(args.bin+1)/8+Q(1, 100000)
    root = Node((max(1-lo,hi/2),lo,Q(1,100),1-hi),())
    serial = 0

    def evaluate(node):
        lower, upper = probe.five_bounds(tuple(map(float,node.box)),float(lo),float(hi),8)
        pl,ph,ql,qh = node.box
        area = (ph-pl)*(qh-ql)
        assert area > 0
        # Room for checked outward rounding. This does not establish the
        # bound: Lean must verify the corresponding complete-cell checker.
        proposed = max(0,(lower/float(area))*(1-1e-5)-1e-8)
        node.bound = Q(math.floor(proposed*10**8),10**8)
        node.total = node.bound*area
        return upper-lower,upper

    priority, _ = evaluate(root)
    queue = [(-priority,serial,root)]
    splits = 0
    while queue and len(queue) < args.cells:
        _,_,node = heapq.heappop(queue)
        b = node.box
        axis = 0 if b[1]-b[0] > b[3]-b[2] else 2
        cut = (b[axis]+b[axis+1])/2
        left,right = list(b),list(b)
        left[axis+1],right[axis] = cut,cut
        node.axis,node.cut = axis//2,cut
        node.left = Node(tuple(left),node.path+((node.axis,cut,False),))
        node.right = Node(tuple(right),node.path+((node.axis,cut,True),))
        for child in (node.left,node.right):
            priority,upper = evaluate(child)
            if upper > 0:
                serial += 1
                heapq.heappush(queue,(-priority,serial,child))
        splits += 1

    def account(node):
        if node.axis < 0:
            return node.size,node.total
        ls,lt = account(node.left)
        rs,rt = account(node.right)
        node.size,node.total = ls+rs,lt+rt
        return node.size,node.total

    account(root)
    chunks = []

    def partition(node):
        if node.size <= args.chunk_leaves:
            chunks.append(node)
        else:
            partition(node.left)
            partition(node.right)

    partition(root)
    args.output.mkdir(parents=True,exist_ok=True)
    module = f'RieszFiveCapacityBin{args.bin}'
    module_dir = args.output/module
    module_dir.mkdir(parents=True,exist_ok=True)
    header = '''/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFiveCapacityCover
open RiemannGaussian
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
'''

    def tree(node):
        if node.axis < 0:
            return f'.leaf ({rat(node.bound)},10000000000)'
        return f'.split {node.axis} {rat(node.cut)} ({tree(node.left)}) ({tree(node.right)})'

    outputs = []
    chunk_index = {id(node): i for i,node in enumerate(chunks)}
    for i,node in enumerate(chunks):
        path = module_dir/f'Chunk{i:04d}.lean'
        body = header+f'namespace RieszFiveCapacityBin{args.bin}.Chunk{i:04d}\n'
        body += f'def low : ℚ := {rat(lo)}\ndef high : ℚ := {rat(hi)}\n'
        body += 'def root : ZetaRieszCapacityCover.Box := !['
        body += f'({rat(node.box[0])},{rat(node.box[1])}),({rat(node.box[2])},{rat(node.box[3])})]\n'
        body += f'def tree : ZetaRieszCapacityCover.Tree := {tree(node)}\n'
        body += 'theorem checked : ZetaRieszCapacityCover.check\n'
        body += '    (ZetaRieszFiveCapacityCover.check low high) tree root = true := by decide +kernel\n'
        # Exact, independently checked cache for later assembly.
        body += 'theorem total_eq : (ZetaRieszCapacityCover.totals tree root).1 = '
        body += rat(node.total)+' := by decide +kernel\n'
        body += f'end RieszFiveCapacityBin{args.bin}.Chunk{i:04d}\n'
        path.write_text(body)
        outputs.append({'file':path.relative_to(args.output).as_posix(),'leaves':node.size,'total':str(node.total),
                        'path':[[axis,str(cut),right] for axis,cut,right in node.path],
                        'sha256':hashlib.sha256(body.encode()).hexdigest()})
    # Assemble cached subtree checks and totals. Explicit equality proofs
    # connect every child box to its parent; no manifest is trusted here.
    assembly = ''.join(f'import {module}.Chunk{i:04d}\n' for i in range(len(chunks)))
    assembly += 'open RiemannGaussian\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nset_option Elab.async false\n'
    assembly += f'namespace {module}.Assembly\n'
    assembly += f'def low : ℚ := {rat(lo)}\ndef high : ℚ := {rat(hi)}\n'
    counter = 0

    def assemble(node):
        nonlocal assembly,counter
        name = f'part{counter:04d}'
        counter += 1
        if id(node) in chunk_index:
            chunk = f'{module}.Chunk{chunk_index[id(node)]:04d}'
            assembly += f'abbrev {name}_box := {chunk}.root\nabbrev {name}_tree := {chunk}.tree\n'
            assembly += f'theorem {name}_checked : ZetaRieszCapacityCover.check (ZetaRieszFiveCapacityCover.check low high) {name}_tree {name}_box = true := {chunk}.checked\n'
            assembly += f'theorem {name}_total : (ZetaRieszCapacityCover.totals {name}_tree {name}_box).1 = {rat(node.total)} := {chunk}.total_eq\n'
            return name,[f'{name}_box',f'{chunk}.root']
        left,ldefs = assemble(node.left)
        right,rdefs = assemble(node.right)
        assembly += f'def {name}_box : ZetaRieszCapacityCover.Box := ![({rat(node.box[0])},{rat(node.box[1])}),({rat(node.box[2])},{rat(node.box[3])})]\n'
        assembly += f'def {name}_tree : ZetaRieszCapacityCover.Tree := .split {node.axis} {rat(node.cut)} {left}_tree {right}_tree\n'
        for side,child,defs in [('left',left,ldefs),('right',right,rdefs)]:
            assembly += f'theorem {name}_{side} : CertifiedBoxCover.{side}Box {name}_box {node.axis} {rat(node.cut)} = {child}_box := by\n'
            assembly += '  funext i\n  fin_cases i <;> norm_num ['+', '.join([name+'_box']+defs+[f'CertifiedBoxCover.{side}Box'])+']\n'
        assembly += f'theorem {name}_checked : ZetaRieszCapacityCover.check (ZetaRieszFiveCapacityCover.check low high) {name}_tree {name}_box = true := by\n'
        assembly += f'  rw [{name}_tree,ZetaRieszCapacityCover.check,{name}_left,{name}_right,{left}_checked,{right}_checked]\n'
        assembly += f'  norm_num [{name}_box]\n'
        assembly += f'theorem {name}_total : (ZetaRieszCapacityCover.totals {name}_tree {name}_box).1 = {rat(node.total)} := by\n'
        assembly += f'  simp only [{name}_tree,ZetaRieszCapacityCover.totals,{name}_left,{name}_right,{left}_total,{right}_total]\n  norm_num\n'
        return name,[name+'_box']

    root_name,_ = assemble(root)
    lower = Q(math.floor(root.total*10**6),10**6)
    assembly += '/-- A kernel-checked lower bound on the complete selected five-prime angular region. This is not an arithmetic prime-sum floor. -/\n'
    assembly += f'theorem whole_supply_lower :\n'
    assembly += f'    ({rat(lower)} : ℝ) ≤ (∫ x in ZetaRieszCapacityCover.region {root_name}_box, ZetaRieszFiveCapacityCover.density low high (1/100) x) := by\n'
    assembly += f'  apply ZetaRieszFiveCapacityCover.integral_ge_of_checked_cover {root_name}_tree\n'
    assembly += f'    (by intro i; fin_cases i <;> norm_num [{root_name}_box]) {root_name}_checked ?_\n'
    assembly += f'  rw [{root_name}_total]\n  decide +kernel\nend {module}.Assembly\n'
    assembly_path=module_dir/'Assembly.lean'
    assembly_path.write_text(assembly)
    sources = [Path(__file__),Path(probe.__file__),
               Path('RiemannGaussian/ZetaRieszFiveCapacityCover.lean'),
               Path('RiemannGaussian/ZetaRieszCapacityCover.lean'),
               Path('RiemannGaussian/ZetaRieszCapacityCheck.lean')]
    report = {'status':'UNTRUSTED_GENERATED_CERTIFICATE_NOT_YET_CHECKED','bin':args.bin,
              'low':str(lo),'high':str(hi),'active_cells':len(queue),'splits':splits,
              'total_leaves_including_zero_children':root.size,'total_lower':str(root.total),
              'approximate_lower':float(root.total),'chunks':outputs,
              'assembly':{'file':assembly_path.relative_to(args.output).as_posix(),
                          'sha256':hashlib.sha256(assembly.encode()).hexdigest()},
              'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}}
    (args.output/'manifest.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('status','active_cells','total_leaves_including_zero_children',
                                          'approximate_lower')}|{'chunks':len(chunks)}))


if __name__ == '__main__':
    main()
