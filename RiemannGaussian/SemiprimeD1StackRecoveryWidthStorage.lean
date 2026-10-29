/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWidthBounds
/-! # All72 actual Boolean roles and real return cells at every genuine compiled prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWidthStorage
open SemiprimeD1StackRecoveryWidth SemiprimeD1StackRecoveryWidthEncoding
open SemiprimeD1StackRecoveryWidthExecution SemiprimeD1StackRecoveryWidthBounds
/-- Every retained original unary marker and the generated grid VALUE are charged to the original-dimension resource. -/
theorem initial_role_bound (a M:Nat) (k:Stack) :((initial (SemiprimeD1StackUnaryDivmod.unary a) (SemiprimeD1StackUnaryDivmod.unary M)).data k).length ≤ inputEnvelope a M :=by
  rcases k with k|k
  · change [].length≤ inputEnvelope a M
    exact Nat.zero_le _
  · cases k <;> simp [initial,input,inputEnvelope,V.envelope,SemiprimeD1StackUnaryDivmod.unary]
    all_goals omega
/-- Successful source prefixes cannot extend beyond this SAME actual source's genuine final halt. -/
theorem prefix_fuel (a M:Nat) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial (SemiprimeD1StackUnaryDivmod.unary a) (SemiprimeD1StackUnaryDivmod.unary M))=some out) :fuel ≤ runBound a M :=by
  obtain ⟨q,hq,hfinal⟩:=source_run a M
  have ht:fuel ≤ q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hfinal,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hh:SemiprimeD1StackCalls.run program 1 (done a M)=none:=rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  exact ht.trans hq
/-- All72 words include retained a/M, actual N by VALUE, all64 arithmetic registers/output/scratch, and real continuation cells. -/
theorem prefix_cells (a M:Nat) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial (SemiprimeD1StackUnaryDivmod.unary a) (SemiprimeD1StackUnaryDivmod.unary M))=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 73*(inputEnvelope a M+runBound a M+1) :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputEnvelope a M) _ _ (initial_role_bound a M) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤ 72*(inputEnvelope a M+fuel):=by
    calc
      _ ≤ ∑_k:Stack,(inputEnvelope a M+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel a M fuel out hr
  omega
/-- Complete real storage is fixed twelfth degree in actual acquired bytes, including both acquired metadata inputs, actual generated N and all64 gate words/template cells. -/
theorem polynomial_space (a M:Nat) :73*(inputEnvelope a M+runBound a M+1) ≤ 100000000000000000000000*(inputEnvelope a M)^12 :=by
  have ht:=runBound_le a M
  have hS:1≤ inputEnvelope a M:=by unfold inputEnvelope V.envelope;omega
  have h112:inputEnvelope a M ≤ (inputEnvelope a M)^12:=Nat.le_pow (by decide:0<(12:Nat))
  unfold polynomial at ht
  nlinarith only [ht,hS,h112]
/-- Every actually reached compiled prefix counts all72roles and actual finite-label return stack. -/
theorem machine_prefix_cells (a M:Nat) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun c=>c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial (SemiprimeD1StackUnaryDivmod.unary a) (SemiprimeD1StackUnaryDivmod.unary M))))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 100000000000000000000000*(inputEnvelope a M)^12 :=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .a) (aux .output) .start program fuel (initial (SemiprimeD1StackUnaryDivmod.unary a) (SemiprimeD1StackUnaryDivmod.unary M))
  have hh:=he.trans hr
  cases hout:SemiprimeD1StackCalls.run program fuel (initial (SemiprimeD1StackUnaryDivmod.unary a) (SemiprimeD1StackUnaryDivmod.unary M)) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact (prefix_cells a M fuel out hout).trans (polynomial_space a M)
end RiemannGaussian.SemiprimeD1StackRecoveryWidthStorage
