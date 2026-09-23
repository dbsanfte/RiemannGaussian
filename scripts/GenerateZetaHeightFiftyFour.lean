/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaHorizontalCertificate

/-!
# Candidate prefix checkpoints for the height-fifty-four contour

Run `lake env lean --run scripts/GenerateZetaHeightFiftyFour.lean` manually.
The output regenerates the numerical blocks in
`RiemannGaussian/ZetaHeightFiftyFour/Cell0.lean` through `Cell4.lean`,
between each file's data helpers and `positive`. Native evaluation only proposes data. Every emitted
equality and final sign check must subsequently pass `decide +kernel`.
This generator is not imported by the library or run in ordinary CI.
-/

open RiemannGaussian LeanCert.Core LeanCert.Engine CertifiedComplexInterval
open ZetaHorizontalCertificate

private def cfg : DyadicConfig := {precision := -40, taylorDepth := 20}

def main : IO Unit := do
  let cells : List (ℚ × ℚ) := [(1/2,5/8),(5/8,3/4),(3/4,1),(1,3/2),(1/2,1/2)]
  for ci in [:cells.length] do
    let (a,b) := cells[ci]!
    if h : a ≤ b then
      let A := input cfg a b 54 h
      IO.println s!"private def cell{ci} : Box := input cfg ({a}) ({b}) 54 (by norm_num)\n"
      let mut P := rational cfg.precision 0 0
      for k in [1:81] do
        match natPower cfg k (neg A) with
        | .error err => throw <| IO.userError s!"power evaluation failed: {repr err}"
        | .ok Q =>
          P := add cfg.precision P Q
          unless P.re.lo.exponent == -40 && P.re.hi.exponent == -40 &&
              P.im.lo.exponent == -40 && P.im.hi.exponent == -40 do
            throw <| IO.userError "checkpoint requires a different dyadic exponent"
          IO.println s!"private def prefix{ci}_{k} : Box :="
          IO.println s!"  dataBox ({P.re.lo.mantissa}) ({P.re.hi.mantissa}) ({P.im.lo.mantissa}) ({P.im.hi.mantissa}) (by decide) (by decide)\n"
          IO.println s!"private theorem checked_prefix{ci}_{k} : prefixBox cfg cell{ci} {k} = .ok prefix{ci}_{k} := by"
          if 1 < k then IO.println s!"  rw [prefixBox, checked_prefix{ci}_{k-1}]"
          IO.println "  decide +kernel\n"
      let name := if ci < 4 then s!"checked_{ci}" else "checked_imaginary"
      let imaginary := if ci < 4 then "false" else "true"
      IO.println s!"private theorem {name} : positiveCheck cfg 80"
      IO.println s!"    (input cfg ({a}) ({b}) 54 (by norm_num)) {imaginary} = true := by"
      IO.println s!"  change positiveCheck cfg 80 cell{ci} {imaginary} = true"
      IO.println "  unfold positiveCheck ZetaEulerMaclaurinEnclosure.evaluate"
      IO.println s!"  rw [checked_prefix{ci}_80]"
      IO.println "  decide +kernel\n"
    else throw <| IO.userError "reversed contour cell"
