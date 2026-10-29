/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerRecordsResources
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerRecordsPrefixResources
open SemiprimeD1StackOwnerRecords SemiprimeD1StackOwnerRecordsBounds SemiprimeD1StackOwnerRecordsOriginal
open SemiprimeBitArithmetic (bitValue)
open SemiprimePublicAcquiredExecution (wireCount)
open SemiprimeD1OwnerPrefixBits (records)
/-- Actual arbitrary-prefix source has a bound in ITS physically present prefix bytes. -/
theorem source_run_prefix_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    ∃time≤runCap bits.length (records (prefixRows (bitValue bits) fixed) tail).length,
      C.run program time (initialPrefix bits (records (prefixRows (bitValue bits) fixed) tail))=
        some (SemiprimeD1StackOwnerRecordsExecution.done bits hN fixed tail):=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackOwnerRecordsExecution.source_run_prefix bits hc hN fixed tail
  refine ⟨t,ht.trans ((Nat.le_succ _).trans (budget_le bits hc hN fixed tail)),hr⟩
/-- The caller-prefix entry starts with only original N and its actual prefix/tail bytes. -/
theorem initial_length (bits pre:List Bool) (k:Stack) :
    ((initialPrefix bits pre).data k).length≤bits.length+pre.length:=by
  rcases k with k|k
  · exact (SemiprimeD1StackOwnerFibreCatalogueResources.initial_length bits k).trans (Nat.le_add_right _ _)
  · rcases k with k|k
    · exact Nat.zero_le _
    · cases k <;> simp only [initialPrefix,data,rowAux,Sum.elim_inr,List.length_nil] <;> omega
/-- No successful actual prefix extends beyond THIS original-prefix source's real final halt. -/
theorem prefix_fuel (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:C.run program fuel (initialPrefix bits (records (prefixRows (bitValue bits) fixed) tail))=some out) :
    fuel≤runCap bits.length (records (prefixRows (bitValue bits) fixed) tail).length:=by
  obtain ⟨t,ht,he⟩:=source_run_prefix_bound bits hc hN fixed tail
  have hf:fuel≤t:=by
    by_contra hn
    have hh:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [hh,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run program 1 (SemiprimeD1StackOwnerRecordsExecution.done bits hN fixed tail)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- ALL344 roles, arbitrary retained prefix/suffix bytes and actual real-return cells are counted. -/
theorem prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:C.run program fuel (initialPrefix bits (records (prefixRows (bitValue bits) fixed) tail))=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤
      345*(bits.length+(records (prefixRows (bitValue bits) fixed) tail).length+
        runCap bits.length (records (prefixRows (bitValue bits) fixed) tail).length):=by
  let P:=records (prefixRows (bitValue bits) fixed) tail
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (bits.length+P.length) _ _ (initial_length bits P) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ _ hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤344*(bits.length+P.length+fuel):=by
    calc
      _≤∑_k:Stack,(bits.length+P.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel bits hc hN fixed tail fuel out hr
  dsimp only [P] at hs
  omega
/-- SAME actual prefix machine trace with actual caller initialization explicit. -/
noncomputable def ownerRecordsPrefixInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initialPrefix bits (records (prefixRows (bitValue bits) fixed) tail)))
      (some (SemiprimeD1StackCalls.configuration (SemiprimeD1StackOwnerRecordsExecution.done bits hN fixed tail)))
      (runCap bits.length (records (prefixRows (bitValue bits) fixed) tail).length):=by
  apply SemiprimeD1StackCalls.evalsCorrect originalInput output (.local .empty) program
  let cert:=source_run_prefix_bound bits hc hN fixed tail
  exact ⟨⟨Classical.choose cert,(Classical.choose_spec cert).2⟩,(Classical.choose_spec cert).1⟩
/-- Every compiled prefix counts the SAME full344-role payload and actual return cells. -/
theorem machine_prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initialPrefix bits (records (prefixRows (bitValue bits) fixed) tail))))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      345*(bits.length+(records (prefixRows (bitValue bits) fixed) tail).length+
        runCap bits.length (records (prefixRows (bitValue bits) fixed) tail).length):=by
  have he:=SemiprimeD1StackCalls.run_correct originalInput output (.local .empty) program fuel
    (initialPrefix bits (records (prefixRows (bitValue bits) fixed) tail))
  change (C.run program fuel (initialPrefix bits (records (prefixRows (bitValue bits) fixed) tail))).map
    SemiprimeD1StackCalls.configuration=
      (fun q=>q.bind machine.step)^[fuel]
        (some (SemiprimeD1StackCalls.configuration (initialPrefix bits (records (prefixRows (bitValue bits) fixed) tail)))) at he
  have hh:=he.trans hr
  cases hout:C.run program fuel (initialPrefix bits (records (prefixRows (bitValue bits) fixed) tail)) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells bits hc hN fixed tail fuel out hout
end RiemannGaussian.SemiprimeD1StackOwnerRecordsPrefixResources
