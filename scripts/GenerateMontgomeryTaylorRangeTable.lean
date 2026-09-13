/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorRangeTable

/- This executable proposes data only. The generated integers must still
   pass the separately proved kernel checker. -/
open RiemannGaussian LeanCert.Core CertifiedIntervalProgram

def main : IO Unit := do
  for i in [166:9472] do
    let n := 16 * i + 8
    let cs := MontgomeryTaylorPhaseGrid.CertificateData.lookup n
    let X := MontgomeryTaylorAdaptiveCell.gridInterval 500 i
    match MontgomeryTaylorAdaptiveCell.evaluate n cs.1 cs.2 X with
    | .error e => throw (IO.userError s!"cell {i}: {repr e}")
    | .ok zs =>
      let v := ((max 0 (intervalEnv zs 2).lo.toRat) * MontgomeryTaylorRangeTable.boundScale).floor
      let d := ((intervalEnv zs 0).lo.toRat * MontgomeryTaylorRangeTable.boundScale).floor
      IO.println s!"{i}\t{v}\t{d}"
