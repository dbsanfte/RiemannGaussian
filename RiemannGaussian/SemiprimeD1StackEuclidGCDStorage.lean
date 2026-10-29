/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEuclidGCDBounds
/-! # All18 actual Boolean roles and real return cells at every genuine compiled prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackEuclidGCDStorage
open SemiprimeD1StackEuclidGCD SemiprimeD1StackEuclidGCDEncoding
open SemiprimeD1StackEuclidGCDExecution SemiprimeD1StackEuclidGCDBounds
/-- Every retained original byte, including high-zero padding, belongs to the input byte inventory. -/
theorem initial_role_bound (left right:List Bool) (k:Stack) :((initial left right).data k).length ≤ inputSize left right :=by
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> simp [initial,input,inputSize]
  · cases k <;> simp [initial,input,inputSize] <;> omega
/-- Successful source prefixes cannot extend beyond this SAME actual source's genuine final halt. -/
theorem prefix_fuel (left right:List Bool) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial left right)=some out) :fuel ≤ runBound left right :=by
  let q:=runBound left right
  have hfinal:=source_run left right
  have ht:fuel ≤ q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hfinal,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hh:SemiprimeD1StackCalls.run program 1 (done left right)=none:=rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  exact ht
/-- All eighteen words include both retained inputs, actual acquired fuel, every Divider11 operand/scratch, and real continuation cells. -/
theorem prefix_cells (left right:List Bool) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial left right)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 19*(inputSize left right+runBound left right+1) :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputSize left right) _ _ (initial_role_bound left right) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤ 18*(inputSize left right+fuel):=by
    calc
      _ ≤ ∑_k:Stack,(inputSize left right+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel left right fuel out hr
  omega
/-- Complete real storage is fixed fourth degree in actual acquired bytes, including both retained original binary words and physically acquired fuel. -/
theorem polynomial_space (left right:List Bool) :19*(inputSize left right+runBound left right+1) ≤ 10000000000*(inputSize left right)^4 :=by
  have ht:=runBound_le left right
  have hS:1≤ inputSize left right:=by unfold inputSize;omega
  have h14:inputSize left right ≤ (inputSize left right)^4:=Nat.le_pow (by decide:0<(4:Nat))
  unfold polynomial at ht
  nlinarith only [ht,hS,h14]
/-- Every actually reached compiled prefix counts all18roles and actual finite-label return stack. -/
theorem machine_prefix_cells (left right:List Bool) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun c=>c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial left right)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 10000000000*(inputSize left right)^4 :=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .left) (aux .output) .start program fuel (initial left right)
  have hh:=he.trans hr
  cases hout:SemiprimeD1StackCalls.run program fuel (initial left right) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact (prefix_cells left right fuel out hout).trans (polynomial_space left right)
end RiemannGaussian.SemiprimeD1StackEuclidGCDStorage
