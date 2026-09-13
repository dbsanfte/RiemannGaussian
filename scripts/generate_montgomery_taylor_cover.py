#!/usr/bin/env python3
"""Serialize an untrusted exact cover proposal into kernel-checked Lean pieces.

Copyright (c) 2026 David Sanftenberg. Released under Apache 2.0.
Each leaf, matrix and parent-box connection is checked by Lean. Python only
chooses how to split the workload and writes proposed proof terms.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path

from generate_montgomery_taylor_anchor_data import integer

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "RiemannGaussian.CertificateData.MontgomeryTaylorCover"
NS = "RiemannGaussian.MontgomeryTaylorIntegerBoxCertificate.CertificateData.Cover"
HEADER = """ /-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
""".lstrip()
IMPORTS = """import RiemannGaussian.MontgomeryTaylorIntegerCover
import RiemannGaussian.CertificateData.MontgomeryTaylorIntegerRanges
import RiemannGaussian.CertificateData.MontgomeryTaylorIntegerAnchors
"""
OPTIONS = "set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nset_option Elab.async false\n\n"
CHECK = "check CertificateData.table 9960000 568320000 CertificateData.lookup"


def vector(xs):
    return "![" + ", ".join(map(integer, xs)) + "]"


def box_literal(box):
    return "![" + ", ".join(f"({integer(a)}, {integer(b)})" for a, b in box) + "]"


class Cover:
    def __init__(self, path, limit, atomic_limit=31):
        self.path, self.limit, self.atomic_limit = path, limit, atomic_limit
        self.data = json.loads(gzip.decompress(path.read_bytes()))
        d = self.data
        if (d["schema"], d["coordinateDenominator"], d["boundScale"], d["gramScale"],
            d["target"]) != (1, 30000000, 2**40, 4096, [395002, 100000000]):
            raise ValueError("Unexpected exact certificate parameters")
        self.nodes, self.matrices = d["nodes"], d["matrices"]
        self.sizes, self.anchors = [], []
        for i, n in enumerate(self.nodes):
            if n == [0]:
                self.sizes.append(1); self.anchors.append(0)
            elif n[0] == 1 and len(n) == 3 and 0 <= n[1] < 944 and 0 <= n[2] < len(self.matrices):
                self.sizes.append(1); self.anchors.append(1)
            elif n[0] == 2 and len(n) == 5 and 0 <= n[1] < 6 and all(0 <= c < i for c in n[3:]):
                self.sizes.append(1 + self.sizes[n[3]] + self.sizes[n[4]])
                self.anchors.append(self.anchors[n[3]] + self.anchors[n[4]])
            else:
                raise ValueError(f"Malformed node {i}")
        for ds, tri in self.matrices:
            if len(ds) != 19 or len(tri) != 21:
                raise ValueError("Malformed curvature witness")
        self.chunks, self.parents = [], []
        self.root_box = tuple([(10000000, 600000000)] * 6)
        self.root = self.partition(d["root"], self.root_box)
        self.groups, current, size = [], [], 0
        for k, (i, _) in enumerate(self.chunks):
            if current and size + self.sizes[i] > 2 * self.limit + 1:
                self.groups.append(current); current, size = [], 0
            current.append(k); size += self.sizes[i]
        if current:
            self.groups.append(current)

    def partition(self, i, box):
        if self.sizes[i] <= self.limit:
            k = len(self.chunks)
            self.chunks.append((i, box))
            return "chunk", k
        n = self.nodes[i]
        if n[0] != 2:
            raise ValueError("Oversized terminal node")
        j, q = n[1:3]
        left, right = list(box), list(box)
        left[j] = (box[j][0], q); right[j] = (q, box[j][1])
        lc = self.partition(n[3], tuple(left)); rc = self.partition(n[4], tuple(right))
        k = len(self.parents)
        self.parents.append((box, j, q, lc, rc))
        return "parent", k

    def tree_literal(self, i, matrices):
        n = self.nodes[i]
        if n == [0]:
            return ".interval"
        if n[0] == 1:
            matrices.add(n[2])
            return f"(.anchor {n[1]} matrix{n[2]:05d})"
        return f"(.split {n[1]} ({integer(n[2])})\n {self.tree_literal(n[3], matrices)}\n {self.tree_literal(n[4], matrices)})"

    def matrix_literal(self, k):
        ds, tri = self.matrices[k]
        rows, cursor = [], 0
        for i in range(6):
            rows.append(vector(tri[cursor:cursor+i+1] + [0] * (5-i)))
            cursor += i+1
        return f"private def matrix{k:05d} : CurvatureWitness := {{\n  curvature := {vector(ds)},\n  factor := ![" + ",\n    ".join(rows) + "] }\n\n"

    def chunk_source(self, k, profile=False):
        i, box = self.chunks[k]
        matrices = set()
        self.tree_literal(i, matrices)
        pieces, parents = [], []

        def subdivide(i, box):
            if self.sizes[i] <= self.atomic_limit:
                name = f"part{len(pieces):04d}"
                pieces.append((name, i, box))
                return name
            n = self.nodes[i]
            j, q = n[1:3]
            left, right = list(box), list(box)
            left[j] = (box[j][0], q); right[j] = (q, box[j][1])
            lc = subdivide(n[3], tuple(left)); rc = subdivide(n[4], tuple(right))
            name = f"join{len(parents):04d}"
            parents.append((name, box, j, q, lc, rc))
            return name

        root = subdivide(i, box)
        text = HEADER + IMPORTS + """
/-!
# One independently checked piece of the proposed complete cover

Generated by scripts/generate_montgomery_taylor_cover.py.
The public checked theorem includes every continuous leaf of this box.
-/

""" + f"namespace {NS}.Chunk{k:04d}\n\n" + OPTIONS
        text += "".join(self.matrix_literal(m) for m in sorted(matrices))
        for name, ni, cell in pieces:
            text += f"private def {name}_box : Box := {box_literal(cell)}\n"
            text += f"private def {name}_tree : Tree :=\n{self.tree_literal(ni, set())}\n\n"
            if profile:
                text += "set_option trace.profiler true in\n"
            text += f"private theorem {name}_checked : {CHECK} {name}_tree {name}_box = true := by decide +kernel\n\n"
        for name, cell, j, q, lc, rc in parents:
            text += f"private def {name}_box : Box := {box_literal(cell)}\n"
            text += f"private def {name}_tree : Tree := .split {j} ({integer(q)}) {lc}_tree {rc}_tree\n\n"
            text += f"private theorem {name}_checked : {CHECK} {name}_tree {name}_box = true := by\n"
            text += "  apply check_split\n"
            for side, child in (("leftBox", lc), ("rightBox", rc)):
                text += f"  · have hb : {side} {name}_box {j} ({integer(q)}) = {child}_box := by\n"
                text += "      funext i\n      fin_cases i <;> rfl\n"
                text += f"    rw [hb]\n    exact {child}_checked\n"
            text += "\n"
        text += "/-- The exact closed root box of this cover piece. -/\n"
        text += f"def box : Box := {root}_box\n\n"
        text += "/-- The full subdivision of this piece, retaining shared boundaries. -/\n"
        text += f"def tree : Tree := {root}_tree\n\n"
        text += "/-- Every leaf and every exact parent connection has passed the kernel. -/\n"
        text += f"theorem checked : {CHECK} tree box = true := {root}_checked\n\n"
        text += f"end {NS}.Chunk{k:04d}\n"
        return text

    @staticmethod
    def refs(ref):
        kind, k = ref
        if kind == "chunk":
            return tuple(f"Chunk{k:04d}.{n}" for n in ("tree", "box", "checked"))
        return tuple(f"parent{k:04d}_{n}" for n in ("tree", "box", "checked"))

    def aggregate_source(self):
        text = HEADER + "\n".join(f"import {PREFIX}.Group{k:04d}" for k in range(len(self.groups)))
        text += """

/-!
# The full closed cover of the seven-window compact gap domain

Generated by scripts/generate_montgomery_taylor_cover.py.
All leaves are proved in the imported pieces. Every remaining connection
checks both child boxes exactly, up to and including the original root.
-/

""" + f"namespace {NS}\n\n" + OPTIONS
        for k, (box, j, q, lc, rc) in enumerate(self.parents):
            lt, lb, lp = self.refs(lc); rt, rb, rp = self.refs(rc)
            text += f"private def parent{k:04d}_box : Box := {box_literal(box)}\n"
            text += f"private def parent{k:04d}_tree : Tree := .split {j} ({integer(q)}) {lt} {rt}\n\n"
            text += f"private theorem parent{k:04d}_checked : {CHECK} parent{k:04d}_tree parent{k:04d}_box = true := by\n"
            text += "  apply check_split\n"
            for side, childbox, proof in (("leftBox", lb, lp), ("rightBox", rb, rp)):
                text += f"  · have hb : {side} parent{k:04d}_box {j} ({integer(q)}) = {childbox} := by\n"
                text += "      funext i\n      fin_cases i <;> rfl\n"
                text += f"    rw [hb]\n    exact {proof}\n"
            text += "\n"
        tree, box, proof = self.refs(self.root)
        text += "/-- The complete proposed subdivision of the original compact domain. -/\n"
        text += f"def tree : Tree := {tree}\n\n"
        text += "/-- All leaves and all exact parent connections have passed Lean. -/\n"
        text += f"theorem checked : {CHECK} tree rootBox = true := by\n"
        text += f"  have hb : rootBox = {box} := by\n    funext i\n    fin_cases i <;> rfl\n"
        text += f"  rw [hb]\n  exact {proof}\n\nend {NS}\n"
        return text

    def manifest(self):
        return {
            "schemaVersion": 1,
            "proposalSha256": hashlib.sha256(self.path.read_bytes()).hexdigest(),
            "maximumNodesPerPiece": self.limit,
            "maximumNodesPerKernelReduction": self.atomic_limit,
            "rootNodes": self.sizes[self.data["root"]],
            "rootAnchorLeaves": self.anchors[self.data["root"]],
            "pieces": [
                {"namespace": f"{NS}.Chunk{k:04d}", "nodes": self.sizes[i],
                 "anchorLeaves": self.anchors[i], "box": box}
                for k, (i, box) in enumerate(self.chunks)],
            "groups": [{"module": f"{PREFIX}.Group{g:04d}", "pieces": ks,
                        "nodes": sum(self.sizes[self.chunks[k][0]] for k in ks),
                        "anchorLeaves": sum(self.anchors[self.chunks[k][0]] for k in ks)}
                       for g, ks in enumerate(self.groups)],
            "parentConnections": len(self.parents),
        }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("proposal", type=Path)
    p.add_argument("--limit", type=int, default=2047)
    p.add_argument("--atomic-limit", type=int, default=31)
    p.add_argument("--out", type=Path, default=ROOT / "RiemannGaussian/CertificateData/MontgomeryTaylorCover")
    p.add_argument("--sample", type=int, help="Write one representative piece only; no whole-cover assertion")
    p.add_argument("--profile", action="store_true")
    args = p.parse_args()
    if args.limit < 1 or args.atomic_limit < 1:
        p.error("Both size limits must be positive")
    cover = Cover(args.proposal, args.limit, args.atomic_limit)
    args.out.mkdir(parents=True, exist_ok=True)
    if args.sample is None:
        for g, keys in enumerate(cover.groups):
            text = HEADER + IMPORTS
            text += "".join(cover.chunk_source(k, args.profile).removeprefix(HEADER + IMPORTS)
                            for k in keys)
            (args.out / f"Group{g:04d}.lean").write_text(text)
    else:
        (args.out / f"Chunk{args.sample:04d}.lean").write_text(cover.chunk_source(args.sample, args.profile))
    manifest = cover.manifest()
    (args.out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    if args.sample is None:
        args.out.with_suffix(".lean").write_text(cover.aggregate_source())
    print(json.dumps({"pieces": len(cover.chunks), "groups": len(cover.groups), "parents": len(cover.parents),
                      "expandedNodes": manifest["rootNodes"], "anchorLeaves": manifest["rootAnchorLeaves"],
                      "largestPiece": max((p["nodes"], p["anchorLeaves"], p["namespace"]) for p in manifest["pieces"]),
                      "mostAnchors": max((p["anchorLeaves"], p["nodes"], p["namespace"]) for p in manifest["pieces"])}))


if __name__ == "__main__":
    main()
