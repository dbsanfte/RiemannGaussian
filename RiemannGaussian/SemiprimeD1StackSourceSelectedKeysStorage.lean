/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeysBounds
/-! # All39actual Boolean roles and real return cells at every genuine compiled prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectedKeysStorage
open SemiprimeD1StackSourceSelectedKeys SemiprimeD1StackSourceSelectedKeysEncoding
open SemiprimeD1StackSourceSelectedKeysExecution SemiprimeD1StackSourceSelectedKeysBounds
/-- Every initialized actual role is charged to the retained cache/tape input byte inventory. -/
theorem initial_role_bound (i:Inputs) (k:Stack) :((source i).data k).length ≤ inputSize i :=by
  rcases k with k|k
  · have h:=SemiprimeD1StackSourceEnvironmentBounds.cache_initial_bound i.ids i.chosen i.query i.pfx k
    change (environment i k).length ≤ _
    exact h.trans (by unfold inputSize;omega)
  · cases k <;> simp [source,initial,data,inputSize]
/-- Successful source prefixes cannot extend beyond this SAME actual source's genuine final halt. -/
theorem prefix_fuel (i:Inputs) (hc:Complete i) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (source i)=some out) :fuel ≤ runBound i :=by
  obtain ⟨q,hq,hfinal⟩:=source_run i hc
  have ht:fuel ≤ q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hfinal,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hh:SemiprimeD1StackCalls.run program 1 (done i)=none:=rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  exact ht.trans hq
/-- All39 words include original source/cache, both returned IDs, every growing output/history byte and real continuation cell. -/
theorem prefix_cells (i:Inputs) (hc:Complete i) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (source i)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 40*(inputSize i+runBound i+1) :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputSize i) _ _ (initial_role_bound i) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤ 39*(inputSize i+fuel):=by
    calc
      _ ≤ ∑_k:Stack,(inputSize i+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel i hc fuel out hr
  omega
/-- Complete real storage is fixed cubic in actual acquired bytes, including the final chronological key vector. -/
theorem polynomial_space (i:Inputs) :40*(inputSize i+runBound i+1) ≤ 1000000000*(inputSize i)^3 :=by
  have ht:=runBound_le i
  have hS:=inputSize_pos i
  have h12:inputSize i ≤ (inputSize i)^2:=Nat.le_pow (by decide:0<(2:Nat))
  have h23:(inputSize i)^2 ≤ (inputSize i)^3:=by
    have h:=Nat.mul_le_mul_left ((inputSize i)^2) (show 1 ≤ inputSize i from hS)
    simpa only [Nat.mul_one,pow_succ] using h
  have h13:=h12.trans h23
  unfold polynomial at ht
  nlinarith only [ht,hS,h13]
/-- Every actually reached compiled prefix counts all39roles and actual finite-label return stack. -/
theorem machine_prefix_cells (i:Inputs) (hc:Complete i) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun c=>c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (source i)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 1000000000*(inputSize i)^3 :=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .source) (aux .output) .start program fuel (source i)
  have hh:=he.trans hr
  cases hout:SemiprimeD1StackCalls.run program fuel (source i) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact (prefix_cells i hc fuel out hout).trans (polynomial_space i)
end RiemannGaussian.SemiprimeD1StackSourceSelectedKeysStorage
