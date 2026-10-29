/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortScopeExecution
/-! # Actual original-input transition and all-prefix bounds for scoped port records -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortScopeBounds
open SemiprimeD1StackPortScopeRecords SemiprimeD1StackPortScopeSource
open SemiprimeD1StackPortScopeExecution
open SemiprimeD1PortScopeEncoding (portTape)
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Both actual copied source streams are bounded at their proved executed source halt. -/
theorem stream_bytes (bits:List Bool) (hb:bits≠[]) :
    (portTape (ports bits) []).length+(vectorBits (ids bits)).length≤2*10^107*(bits.length+1)^30 := by
  obtain ⟨time,_,hr⟩:=SemiprimeD1StackPortOrdinalBankBounds.source_run_polynomial bits hb
  have hs:=SemiprimeD1StackPortOrdinalBankBounds.prefix_cells bits hb time _ hr
  change (∑k:S.Stack,(base bits k).length)+0≤10^107*(bits.length+1)^30 at hs
  have hp:=Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset S.Stack))=>Nat.zero_le ((base bits k).length))
    (Finset.mem_univ (S.portStack (SemiprimeD1StackPortCatalogue.aux .output)))
  have hi:=Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset S.Stack))=>Nat.zero_le ((base bits k).length))
    (Finset.mem_univ S.ids)
  have hpe:=congrArg List.length (source_ports bits)
  have hie:=congrArg List.length (source_ids bits)
  change (base bits (S.portStack (SemiprimeD1StackPortCatalogue.aux .output))).length=(portTape (ports bits) []).length at hpe
  change (base bits S.ids).length=(vectorBits (ids bits)).length at hie
  omega
/-- Pure fixed-polynomial substitution, before actual executable source values are instantiated. -/
theorem numeric_budget (n P B:ℕ) (h:P+B≤2*10^107*(n+1)^30) :
    10^104*(n+1)^30+107*(P+B)+16≤10^111*(n+1)^30 := by
  have hp:1≤(n+1)^30:=Nat.succ_le_of_lt (Nat.pow_pos (Nat.succ_pos n))
  omega
/-- The WHOLE actual original-N source/copy/stream/reverse pipeline has a fixed polynomial clock. -/
theorem budget_le (bits:List Bool) (hb:bits≠[]) : budget bits≤10^111*(bits.length+1)^30 :=
  numeric_budget bits.length (portTape (ports bits) []).length (vectorBits (ids bits)).length (stream_bytes bits hb)
/-- No graph, ID, index inverse, M, code or output record is supplied to the public source. -/
theorem source_run_polynomial (bits:List Bool) (hb:bits≠[]) :
    ∃ time ≤ 10^111*(bits.length+1)^30,C.run program time (initial bits)=some (done bits) := by
  obtain ⟨m,hm,hr⟩:=source_run bits hb
  exact ⟨m,hm.trans (budget_le bits hb),hr⟩
/-- Successful executed prefixes cannot pass the actual proved final halt. -/
theorem prefix_fuel_le (bits:List Bool) (hb:bits≠[]) (fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial bits)=some out) : fuel≤10^111*(bits.length+1)^30 := by
  obtain ⟨time,ht,he⟩:=source_run_polynomial bits hb
  have hf:fuel≤time:=by
    by_contra hn
    have h:fuel=time+(1+(fuel-(time+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run program 1 (done bits)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- ALL one hundred and five Boolean stacks and real return frames at EVERY actual source prefix. -/
theorem prefix_cells (bits:List Bool) (hb:bits≠[]) (fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial bits)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤10^114*(bits.length+1)^30 := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ out (by
    intro k
    cases k with
    | inl key =>
      change (S.input bits key).length≤bits.length
      rw [source_input]
      split <;> simp
    | inr key => exact Nat.zero_le _) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤105*(bits.length+fuel):=by
    calc
      _≤∑_k:Stack,(bits.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits hb fuel out hr
  have hn:bits.length≤(bits.length+1)^30:=by
    have h:bits.length+1≤(bits.length+1)^30:=by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 1≤bits.length+1 by omega) (show 1≤30 by omega)
    omega
  omega
/-- ALL actual compiled-machine prefixes start from initList of binary N alone. -/
theorem machine_prefix_cells (bits:List Bool) (hb:bits≠[]) (fuel:ℕ) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤10^114*(bits.length+1)^30 := by
  have he:=SemiprimeD1StackCalls.run_correct (originalInput) (aux .output) (.local .main)
    program fuel (initial bits)
  change (C.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial bits))) at he
  have hh:(C.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=some cfg:=
    he.trans ((congrArg (fun start:machine.Cfg=>
      (fun q:Option machine.Cfg=>q.bind machine.step)^[fuel] (some start)) (initial_eq bits).symm).trans hr)
  cases hc:C.run program fuel (initial bits) with
  | none => rw [hc] at hh;cases hh
  | some out =>
    rw [hc] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells bits hb fuel out hc
/-- Actual finite-machine full-acquisition certificate, rather than a reported-cost assumption. -/
noncomputable def portScopeRecordsInTime (bits:List Bool) (hb:bits≠[]) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (10^111*(bits.length+1)^30) := by
  rw [initial_eq bits]
  apply SemiprimeD1StackCalls.evalsCorrect (originalInput) (aux .output) (.local .main) program
  let cert:=source_run_polynomial bits hb
  let m:=Classical.choose cert
  have hs:=Classical.choose_spec cert
  exact ⟨⟨m,hs.2⟩,hs.1⟩
end RiemannGaussian.SemiprimeD1StackPortScopeBounds
