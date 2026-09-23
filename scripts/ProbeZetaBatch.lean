/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaBlockBatchCertificate

/-!
Optional native performance probe; not a kernel certificate and not part of
ordinary CI. Run `lake env lean --run scripts/ProbeZetaBatch.lean [count]`.
The default is 257 half-step samples from 21836 through 21964, reusing one
center at 21900. The optional count is capped at 257.
-/

open RiemannGaussian LeanCert.Core LeanCert.Engine CertifiedComplexInterval
open ZetaBlockBatchCertificate

private def cfg : DyadicConfig := {precision := -60, taylorDepth := 32}

def main (args : List String) : IO Unit := do
  let count := min 257 ((args.head?.bind String.toNat?).getD 257)
  let center : ℚ := 21900
  let H := 299
  let Ks := ZetaBlockCertificate.widths 22020 3000 (H + 1)
  let S := rational cfg.precision (1 / 2) center
  let D0 := rational cfg.precision 0 (-64)
  let Q := rational cfg.precision 0 (1 / 2)
  let start ← IO.monoMsNow
  match prepare cfg H Ks S D0 Q with
  | .error _ => throw <| IO.userError "Batch preparation failed"
  | .ok B =>
    let ready ← IO.monoMsNow
    IO.println s!"Prepared {Ks.length} blocks and {H} early terms in {ready-start} ms"
    (← IO.getStdout).flush
    let mut worst : ℚ := 0
    for j in [:count] do
      let delta : ℚ := -64 + (j : ℚ) / 2
      let A := rational cfg.precision (1 / 2) (center + delta)
      let D := rational cfg.precision 0 delta
      if !admissible cfg H Ks S A D then
        throw <| IO.userError s!"Sample {j} failed the analytic-domain check"
      match evaluate cfg (H + Ks.sum) B A D j with
      | .error _ => throw <| IO.userError s!"Sample {j} failed evaluation"
      | .ok Z =>
        worst := max worst (max (Z.re.hi.toRat - Z.re.lo.toRat) (Z.im.hi.toRat - Z.im.lo.toRat))
        if j = 0 || j + 1 = count then
          IO.println s!"T={center+delta}: Re=[{Z.re.lo.toRat},{Z.re.hi.toRat}], Im=[{Z.im.lo.toRat},{Z.im.hi.toRat}]"
          (← IO.getStdout).flush
        if (j + 1) % 64 = 0 then
          IO.println s!"Evaluated {j+1}/{count} samples"
          (← IO.getStdout).flush
    let stop ← IO.monoMsNow
    IO.println s!"{count} samples in {stop-ready} ms after {ready-start} ms preparation"
    IO.println s!"Maximum raw coordinate width: {worst}; analytic allowance: 1/1000000000"
    IO.println "Native performance probe only. This output is not a kernel certificate or a complete zero count."
