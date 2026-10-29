/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineFactor
import RiemannGaussian.SemiprimeD1StackRecoveryAffineInnerClear
/-! # Actual product FIRST, suffix SECOND convolution step and all six real drains -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffinePair
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView SemiprimeD1StackProcedureTrace
open SemiprimeD1StackRecoveryAffineOperationInput (emptyRational)
namespace S
export SemiprimeD1StackRecoveryAffineSite (result runBound site_call written_nonempty nonempty_preserved)
end S
/-- Actual stopped scalar-bank view after both real sites and their six physical cache drains. -/
def result (w:Words) (width:List Bool):Words:=
  SemiprimeD1StackRecoveryAffineInnerClear.result (S.result .sum (S.result .product w width) width)
/-- This own bound sums the SAME two actual scalar-site bounds and the actual fixed six-role sweep. -/
def runBound (w:Words) (width:List Bool):Nat:=
  S.runBound .product w width+S.runBound .sum (S.result .product w width) width+
    6*(SemiprimeD1StackRecoveryAffineCleanup.mass (bank (S.result .sum (S.result .product w width) width))+1)
/-- Both scalar operations execute even for zero extensions and W0, with every real continuation retained. -/
theorem source_run (part:Part) (w:Words) (width:List Bool)
    (hr:w.rational=emptyRational width) (hc:w.auxiliary .copyScratch=[])
    (hx:w.registers (.numBase,false)≠[]) (hy:w.registers (.denBase,false)≠[])
    (ha:w.registers (.denPower,false)≠[]):
    ∃q≤runBound w width,Runs program q (.local (.multiply part)) (bank w)
      (.local (.innerNext part)) (bank (result w width)):=by
  obtain ⟨t0,ht0,h0⟩:=S.site_call .product (.local (.multiply part)) (.local (.add part)) w width rfl hr hc hx hy
  have hp:(S.result .product w width).registers (.numPower,false)≠[]:=S.written_nonempty .product w width
  have ha':(S.result .product w width).registers (.denPower,false)≠[]:=
    S.nonempty_preserved .product w width .denPower ha
  obtain ⟨t1,ht1,h1⟩:=S.site_call .sum (.local (.add part)) (.local (.clearInner part 0))
    (S.result .product w width) width rfl hr hc hp ha'
  obtain ⟨t2,ht2,h2⟩:=SemiprimeD1StackRecoveryAffineInnerClear.source_run part
    (S.result .sum (S.result .product w width) width)
  refine ⟨t0+t1+t2,?_,SemiprimeD1StackRecoveryAffinePrimitives.join
    (SemiprimeD1StackRecoveryAffinePrimitives.join h0 h1) h2⟩
  unfold runBound
  omega
/-- The complete clean R36 bank is retained after this actual scalar pair. -/
theorem rational_retained (w:Words) (width:List Bool):(result w width).rational=w.rational:=rfl
/-- Every actual original source/geometry/slope/width word is retained by the arithmetic pair. -/
theorem auxiliary_retained (w:Words) (width:List Bool):(result w width).auxiliary=w.auxiliary:=rfl
/-- The actual q/array/reader/count words are retained across the complete arithmetic pair. -/
theorem added_retained (w:Words) (width:List Bool):(result w width).added=w.added:=rfl
end RiemannGaussian.SemiprimeD1StackRecoveryAffinePair
