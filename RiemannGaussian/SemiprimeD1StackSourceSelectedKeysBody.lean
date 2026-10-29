/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeysLog
/-! # Complete actual two-ID lookup, exact joint-key framing and per-occurrence cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectedKeysBody
open SemiprimeD1StackSourceSelectedKeys SemiprimeD1StackSourceSelectedKeysEncoding
open SemiprimeD1StackSourceSelectedKeysPrimitives SemiprimeD1StackSourceSelectedKeysView
open SemiprimeD1StackSourceSelectedKeysLookup SemiprimeD1StackSourceSelectedKeysLog
open SemiprimeD1StackProcedureTrace
/-- Own actual per-occurrence producer clock; lookup and byte framing, reverse-log and four complete drains all remain paid. -/
def bodyTime (i:Inputs) (own fac:List Bool) :Nat :=lookupClock i own+lookupClock i fac+frameTime i own fac+
  ((readID i.ids own).length+1)+((joint i.ids (own,fac)).length+1)+(own.length+1)+(fac.length+1)
/-- Both selected IDs are acquired by real calls and a complete exact oldjoint key is physically emitted once. -/
theorem body_run (i:Inputs) (reader own fac hist:List Bool)
    (ho:SemiprimeBitArithmetic.bitValue own < i.ids.length) (hf:SemiprimeBitArithmetic.bitValue fac < i.ids.length) :
    ∃q≤bodyTime i own fac,Runs program q (.copyQuery .owner) (view i [] [] [] reader own fac [] [] [] [] hist [])
      .header (view i [] [] [] reader [] [] [] [] [] [] ((chunk i.ids (own,fac)).reverse++hist) []) :=by
  obtain ⟨q,hq,h0⟩:=owner_run i reader own fac hist ho
  obtain ⟨t,ht,h1⟩:=factor_run i reader own fac hist hf
  have h2:=frame_run i reader own fac hist
  have h3:=clear_run i reader own fac (readID i.ids own) (joint i.ids (own,fac)) ((chunk i.ids (own,fac)).reverse++hist)
  refine ⟨_,?_,join (join (join h0 h1) h2) h3⟩
  unfold bodyTime
  omega
end RiemannGaussian.SemiprimeD1StackSourceSelectedKeysBody
