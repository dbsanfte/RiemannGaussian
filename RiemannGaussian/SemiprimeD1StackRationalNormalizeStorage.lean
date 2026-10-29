/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalNormalizeBounds
/-! # All22 actual Boolean roles and real return cells at every genuine compiled prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRationalNormalizeStorage
open SemiprimeD1StackRationalNormalize SemiprimeD1StackRationalNormalizeEncoding
open SemiprimeD1StackRationalNormalizeExecution SemiprimeD1StackRationalNormalizeBounds
/-- Every retained original byte, including high-zero padding, belongs to the input byte inventory. -/
theorem initial_role_bound (negative:Bool) (num den:List Bool) (k:Stack) :((initial (negative::num) den).data k).length ≤ inputSize num den :=by
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> simp [initial,input,SemiprimeD1StackEuclidGCD.input,inputSize]
    · cases k <;> simp [initial,input,SemiprimeD1StackEuclidGCD.input,inputSize]
      omega
  · cases k <;> simp [initial,input,inputSize]
    omega
/-- Successful source prefixes cannot extend beyond this SAME actual source's genuine final halt. -/
theorem prefix_fuel (negative:Bool) (num den:List Bool) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial (negative::num) den)=some out) :fuel ≤ runBound num den :=by
  let q:=runBound num den
  have hfinal:=source_run negative num den
  have ht:fuel ≤ q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hfinal,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hh:SemiprimeD1StackCalls.run program 1 (done negative num den)=none:=rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  exact ht
/-- All twenty-two words include both retained original words, actual GCD fuel, every Divider11 operand/scratch, and real continuation cells. -/
theorem prefix_cells (negative:Bool) (num den:List Bool) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial (negative::num) den)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 23*(inputSize num den+runBound num den+1) :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputSize num den) _ _ (initial_role_bound negative num den) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤ 22*(inputSize num den+fuel):=by
    calc
      _ ≤ ∑_k:Stack,(inputSize num den+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel negative num den fuel out hr
  omega
/-- Complete real storage is fixed fourth degree in actual acquired bytes, including both retained original binary words and physically acquired fuel. -/
theorem polynomial_space (num den:List Bool) :23*(inputSize num den+runBound num den+1) ≤ 1000000000000*(inputSize num den)^4 :=by
  have ht:=runBound_le num den
  have hS:1≤ inputSize num den:=by unfold inputSize;omega
  have h14:inputSize num den ≤ (inputSize num den)^4:=Nat.le_pow (by decide:0<(4:Nat))
  unfold polynomial at ht
  nlinarith only [ht,hS,h14]
/-- Every actually reached compiled prefix counts all22roles and actual finite-label return stack. -/
theorem machine_prefix_cells (negative:Bool) (num den:List Bool) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun c=>c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial (negative::num) den)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 1000000000000*(inputSize num den)^4 :=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .originalSigned) (aux .numeratorOutput) .start program fuel (initial (negative::num) den)
  have hh:=he.trans hr
  cases hout:SemiprimeD1StackCalls.run program fuel (initial (negative::num) den) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact (prefix_cells negative num den fuel out hout).trans (polynomial_space num den)
end RiemannGaussian.SemiprimeD1StackRationalNormalizeStorage
