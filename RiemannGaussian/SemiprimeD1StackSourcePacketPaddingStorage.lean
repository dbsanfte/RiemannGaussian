/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourcePacketPaddingBounds
/-! # All25actual Boolean roles and real return cells at every genuine compiled prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourcePacketPaddingStorage
open SemiprimeD1StackSourcePacketPadding SemiprimeD1StackSourcePacketPaddingEncoding
open SemiprimeD1StackSourcePacketPaddingExecution SemiprimeD1StackSourcePacketPaddingBounds
/-- Every initialized actual role is charged to the retained cache/tape input byte inventory. -/
theorem initial_role_bound (keys:List (List Bool)) (a:Nat) (k:Stack) :((source keys a).data k).length ≤ inputSize keys a :=by
  rcases k with k|k
  · have h:=SemiprimeD1StackSourceKeyFrequencyStorage.initial_role_bound keys k
    change ((SemiprimeD1StackSourceKeyFrequencyEncoding.source keys).data k).length≤ inputSize keys a
    exact h.trans (by unfold inputSize;omega)
  · cases k <;> simp [source,initial,input,inputSize]
/-- Successful source prefixes cannot extend beyond this SAME actual source's genuine final halt. -/
theorem prefix_fuel (keys:List (List Bool)) (a:Nat) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (source keys a)=some out) :fuel ≤ runBound keys a :=by
  obtain ⟨q,hq,hfinal⟩:=source_run keys a
  have ht:fuel ≤ q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hfinal,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hh:SemiprimeD1StackCalls.run program 1 (done keys a)=none:=rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  exact ht.trans hq
/-- All25 words include source, dictionary, maximum, actual binary counter/padding/scratch bits and real continuation cells. -/
theorem prefix_cells (keys:List (List Bool)) (a:Nat) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (source keys a)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 26*(inputSize keys a+runBound keys a+1) :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputSize keys a) _ _ (initial_role_bound keys a) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤ 25*(inputSize keys a+fuel):=by
    calc
      _ ≤ ∑_k:Stack,(inputSize keys a+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel keys a fuel out hr
  omega
/-- Complete real storage is fixed fifth degree in actual acquired bytes, including every retained historical dictionary record and original unary exponent. -/
theorem polynomial_space (keys:List (List Bool)) (a:Nat) :26*(inputSize keys a+runBound keys a+1) ≤ 100000000000000*(inputSize keys a)^5 :=by
  have ht:=runBound_le keys a
  have hS:1≤ inputSize keys a:=by
    have h:1≤ FE.inputSize keys:=(SemiprimeD1StackSourceKeyFrequencyBytes.input_bounds keys).1
    unfold inputSize;omega
  have h15:inputSize keys a ≤ (inputSize keys a)^5:=Nat.le_pow (by decide:0<(5:Nat))
  unfold polynomial at ht
  nlinarith only [ht,hS,h15]
/-- Every actually reached compiled prefix counts all25roles and actual finite-label return stack. -/
theorem machine_prefix_cells (keys:List (List Bool)) (a:Nat) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun c=>c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (source keys a)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 100000000000000*(inputSize keys a)^5 :=by
  have he:=SemiprimeD1StackCalls.run_correct (frequencyStack (F.aux .source)) (aux .padding) .start program fuel (source keys a)
  have hh:=he.trans hr
  cases hout:SemiprimeD1StackCalls.run program fuel (source keys a) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact (prefix_cells keys a fuel out hout).trans (polynomial_space keys a)
end RiemannGaussian.SemiprimeD1StackSourcePacketPaddingStorage
