/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaBlockCertificate
open RiemannGaussian LeanCert.Core LeanCert.Engine CertifiedComplexInterval
open ZetaBlockCertificate
/-!
Optional native timing probe for the sound accelerated evaluator.
Run `lake env lean --run scripts/ProbeZetaBlocks.lean` manually.
This proposes numerical data; it does not produce a kernel certificate
and is not part of the ordinary build or any exhaustive zero verification.
-/
private def cfg : DyadicConfig := {precision := -60, taylorDepth := 32}
def main : IO Unit := do
 let start ← IO.monoMsNow
 let ks := widths 22020 3000 300
 IO.println s!"blocks {ks.length}; final {299+ks.sum}; admissible {admissible cfg 299 ks (rational cfg.precision (1/2) 22000)}"
 match evaluate cfg 299 ks (rational cfg.precision (1/2) 22000) with
 | .error err => IO.println s!"FAILED {repr err}"
 | .ok B =>
   IO.println s!"Re {B.re.lo.toRat} {B.re.hi.toRat}"
   IO.println s!"Im {B.im.lo.toRat} {B.im.hi.toRat}"
   IO.println s!"separated {separated B}"
 let stop ← IO.monoMsNow
 IO.println s!"native milliseconds {stop-start}; sound algorithm, exploratory native execution, not a kernel certificate"
