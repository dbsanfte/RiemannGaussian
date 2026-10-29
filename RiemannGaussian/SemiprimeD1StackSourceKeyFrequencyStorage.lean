/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyBounds
/-! # All21actual Boolean roles and real return cells at every genuine compiled prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyStorage
open SemiprimeD1StackSourceKeyFrequency SemiprimeD1StackSourceKeyFrequencyEncoding
open SemiprimeD1StackSourceKeyFrequencyExecution SemiprimeD1StackSourceKeyFrequencyBounds
/-- Every initialized actual role is charged to the retained cache/tape input byte inventory. -/
theorem initial_role_bound (keys:List (List Bool)) (k:Stack) :((source keys).data k).length ≤ inputSize keys :=by
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> simp [source,initial,input,aux,inputSize,Function.update]
  · cases k <;> simp [source,initial,input,aux,inputSize,Function.update]
/-- Successful source prefixes cannot extend beyond this SAME actual source's genuine final halt. -/
theorem prefix_fuel (keys:List (List Bool)) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (source keys)=some out) :fuel ≤ runBound keys :=by
  obtain ⟨q,hq,hfinal⟩:=source_run keys
  have ht:fuel ≤ q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hfinal,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hh:SemiprimeD1StackCalls.run program 1 (done keys)=none:=rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  exact ht.trans hq
/-- All21 words include original source/cache, both returned IDs, every growing output/history byte and real continuation cell. -/
theorem prefix_cells (keys:List (List Bool)) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (source keys)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 22*(inputSize keys+runBound keys+1) :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputSize keys) _ _ (initial_role_bound keys) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤ 21*(inputSize keys+fuel):=by
    calc
      _ ≤ ∑_k:Stack,(inputSize keys+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel keys fuel out hr
  omega
/-- Complete real storage is fixed fifth degree in actual acquired bytes, including the final chronological key vector. -/
theorem polynomial_space (keys:List (List Bool)) :22*(inputSize keys+runBound keys+1) ≤ 1000000000000*(inputSize keys)^5 :=by
  have ht:=runBound_le keys
  have hS:1≤ inputSize keys:=(SemiprimeD1StackSourceKeyFrequencyBytes.input_bounds keys).1
  have h15:inputSize keys ≤ (inputSize keys)^5:=Nat.le_pow (by decide:0<(5:Nat))
  unfold polynomial at ht
  nlinarith only [ht,hS,h15]
/-- Every actually reached compiled prefix counts all21roles and actual finite-label return stack. -/
theorem machine_prefix_cells (keys:List (List Bool)) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun c=>c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (source keys)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 1000000000000*(inputSize keys)^5 :=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .source) (aux .maximum) .start program fuel (source keys)
  have hh:=he.trans hr
  cases hout:SemiprimeD1StackCalls.run program fuel (source keys) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact (prefix_cells keys fuel out hout).trans (polynomial_space keys)
end RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyStorage
