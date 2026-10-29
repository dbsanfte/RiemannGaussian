/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridSite
import RiemannGaussian.SemiprimeD1StackRecoveryGridPowerSource
/-! # Actual original-grid row differences and both oriented powers -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridRowBases
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackRecoveryGridOperationInput SemiprimeD1StackRecoveryGridRegisters
open SemiprimeD1StackProcedureTrace
namespace Call
export SemiprimeD1StackRecoveryGridSite (result runBound site_call nonempty_preserved written_nonempty signed_getReg)
end Call
namespace Power
export SemiprimeD1StackRecoveryGridPowerSource (power_source_run runBound)
end Power
/-- Actual signed grid-index negation. -/
def negative (w:Words) (width:List Bool) :Words:=Call.result .negativeIndex w width
/-- Actual fitted center-minus-index word. -/
def numerator (w:Words) (width:List Bool) :Words:=Call.result .numeratorBase (negative w width) width
/-- Actual fitted node-minus-index word, acquired before both power loops. -/
def result (w:Words) (width:List Bool) :Words:=Call.result .denominatorBase (numerator w width) width
/-- Own actual three-operation row-base clock. -/
def runBound (w:Words) (width:List Bool) :Nat:=Call.runBound .negativeIndex w width+
  Call.runBound .numeratorBase (negative w width) width+Call.runBound .denominatorBase (numerator w width) width
attribute [local irreducible] runBound Call.runBound
/-- Three real normalized/twice-fitted operations acquire both exact oriented row difference bases. -/
theorem bases_run (w:Words) (width:List Bool)
    (hr:w.rational=emptyRational width) (hs:w.auxiliary .copyScratch=[])
    (hi:w.registers (.index,false)≠[]) (hc:w.registers (.center,false)≠[]) (hn:w.registers (.node,false)≠[]) :
    ∃q≤runBound w width,Runs program q (.local .negative) (bank w) (.local (.powerCount .numerator)) (bank (result w width)):=by
  obtain ⟨t0,ht0,h0⟩:=Call.site_call .negativeIndex (.local .negative) (.local .numeratorBase) w width rfl hr hs hi hi
  have hc1:=Call.nonempty_preserved .negativeIndex w width .center hc
  have hneg1:=Call.written_nonempty .negativeIndex w width
  obtain ⟨t1,ht1,h1⟩:=Call.site_call .numeratorBase (.local .numeratorBase) (.local .denominatorBase)
    (negative w width) width rfl hr hs hc1 hneg1
  have hn1:=Call.nonempty_preserved .negativeIndex w width .node hn
  have hn2:=Call.nonempty_preserved .numeratorBase (negative w width) width .node hn1
  have hneg2:=Call.nonempty_preserved .numeratorBase (negative w width) width .negative hneg1
  obtain ⟨t2,ht2,h2⟩:=Call.site_call .denominatorBase (.local .denominatorBase) (.local (.powerCount .numerator))
    (numerator w width) width rfl hr hs hn2 hneg2
  change Runs program t0 _ _ _ (bank (negative w width)) at h0
  change Runs program t1 _ _ _ (bank (numerator w width)) at h1
  change Runs program t2 _ _ _ (bank (result w width)) at h2
  refine ⟨t0+t1+t2,?_,PTrace.join (PTrace.join h0 h1) h2⟩
  unfold runBound
  omega
/-- The actual numerator base has its sign byte after both subsequent acquisitions. -/
theorem numerator_nonempty (w:Words) (width:List Bool) :(result w width).registers (.numBase,false)≠[]:=
  Call.nonempty_preserved .denominatorBase (numerator w width) width .numBase
    (Call.written_nonempty .numeratorBase (negative w width) width)
/-- The actual denominator base has its sign byte even for W0. -/
theorem denominator_nonempty (w:Words) (width:List Bool) :(result w width).registers (.denBase,false)≠[]:=
  Call.written_nonempty .denominatorBase (numerator w width) width
/-- Exact actual numerator-power cache, including the literal oneWord at zero multiplicity. -/
def numeratorPower (w:Words) (width:List Bool) (m:Nat) :Words:=
  putReg w .numPower (SemiprimeD1RecoveryPowerBits.power width (getReg w .numBase) m).word
/-- Exact actual denominator-power cache, preserving the numerator-power result and both bases. -/
def powersResult (w:Words) (width:List Bool) (m:Nat) :Words:=
  let ready:=numeratorPower w width m
  putReg ready .denPower (SemiprimeD1RecoveryPowerBits.power width (getReg ready .denBase) m).word
/-- Own actual clocks of both paid multiplicity copies and complete oriented power-source calls. -/
def powersBound (w:Words) (width:List Bool) (m:Nat) :Nat:=
  Power.runBound .numerator w width (getReg w .numBase) m+
    Power.runBound .denominator (numeratorPower w width m) width (getReg (numeratorPower w width m) .denBase) m
attribute [local irreducible] powersBound Power.runBound
/-- Both row powers consume physical copies of the same actual acquired multiplicity, with accumulator FIRST and base SECOND. -/
theorem powers_run (w:Words) (width:List Bool) (m:Nat)
    (hr:w.rational=emptyRational width) (hs:w.auxiliary .copyScratch=[])
    (hz:w.auxiliary .powerTodo=[]) (hm:w.product .product=List.replicate m true)
    (hn:w.registers (.numBase,false)≠[]) (hd:w.registers (.denBase,false)≠[]) :
    ∃q≤powersBound w width m,Runs program q (.local (.powerCount .numerator)) (bank w) (.local .reciprocal)
      (bank (powersResult w width m)):=by
  obtain ⟨p,hp,h0⟩:=Power.power_source_run .numerator w width (getReg w .numBase) m hr hs hz hm
    (Call.signed_getReg w .numBase hn) rfl
  change Runs program p _ _ _ (bank (numeratorPower w width m)) at h0
  have hd1:(numeratorPower w width m).registers (.denBase,false)≠[]:=by
    rw [show (numeratorPower w width m).registers (.denBase,false)=w.registers (.denBase,false) from
      putReg_other w .numPower .denBase _ false (by decide)]
    exact hd
  obtain ⟨q,hq,h1⟩:=Power.power_source_run .denominator (numeratorPower w width m) width
    (getReg (numeratorPower w width m) .denBase) m hr hs hz hm
    (Call.signed_getReg _ .denBase hd1) rfl
  change Runs program q _ _ _ (bank (powersResult w width m)) at h1
  refine ⟨p+q,?_,PTrace.join h0 h1⟩
  unfold powersBound
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryGridRowBases
