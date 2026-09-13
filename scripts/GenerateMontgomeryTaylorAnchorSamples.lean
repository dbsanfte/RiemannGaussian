/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorAnchorBounds

/- This executable proposes exact fixed-point anchor data. All output
   still requires checking by the separate Lean kernel certificate. -/
open RiemannGaussian LeanCert.Core CertifiedIntervalProgram

def main (args : List String) : IO Unit := do
  let path := args.headD "anchor-points.tsv"
  let contents ← IO.FS.readFile path
  let rows := (contents.trimAscii.toString.splitOn "\n").toArray
  let start := (args[1]?.getD "0").toNat!
  let stop := (args[2]?.getD (toString rows.size)).toNat!
  for idx in [start:min stop rows.size] do
    let fields := (rows[idx]!.splitOn "\t").toArray
    let m : Fin 6 → ℚ := fun j => (fields[j.val]!.toNat! : ℚ) / 10000000
    for t in List.finRange 19 do
      let q := MontgomeryTaylorSevenWindowForms.linearFormRat t m
      let n := ((8000*q+1/2).floor).toNat
      let cs := MontgomeryTaylorPhaseGrid.CertificateData.lookup n
      let X := MontgomeryTaylorPhaseEnclosure.ratPoint q
      match MontgomeryTaylorAdaptiveCell.evaluate n cs.1 cs.2 X with
      | .error e => throw (IO.userError s!"anchor {idx} term {t}: {repr e}")
      | .ok zs =>
        let sc : ℚ := MontgomeryTaylorRangeTable.boundScale
        let v := ((max 0 (intervalEnv zs 2).lo.toRat)*sc).floor
        let dl := ((intervalEnv zs 1).lo.toRat*sc).floor
        let du := ((intervalEnv zs 1).hi.toRat*sc).ceil
        IO.println s!"{idx}\t{t}\t{n}\t{v}\t{dl}\t{du}"
