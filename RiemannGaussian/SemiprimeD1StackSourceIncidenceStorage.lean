/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceBounds
/-! # Every47 actual Boolean word and real caller-return cell at every compiled query prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceStorage
open SemiprimeD1StackSourceIncidence SemiprimeD1StackSourceIncidenceEncoding
open SemiprimeD1StackSourceIncidenceExecution SemiprimeD1StackSourceIncidenceBounds
/-- Every actual initialized role is charged to the acquired source/cache/power byte budget. -/
theorem initial_role_bound (i:Inputs) (k:Stack) :((source i).data k).length ≤ inputSize i :=by
  rcases k with k|k
  · have h:=SemiprimeD1StackSourceEnvironmentBounds.cache_initial_bound i.ids i.chosen i.query i.pfx k
    change (environment i k).length ≤ _
    exact h.trans (by unfold inputSize;omega)
  · cases k <;> simp only [source,initial,data,Sum.elim_inr,List.length_nil] <;>
      unfold inputSize <;> omega
/-- No successful prefix can continue beyond the same literal program's genuine whole halt. -/
theorem prefix_fuel (i:Inputs) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (source i)=some out) :fuel ≤ runBound i :=by
  obtain ⟨q,hq,hfinal⟩:=source_run i
  have ht:fuel ≤ q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hfinal,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hh:SemiprimeD1StackCalls.run program 1 (done i)=none:=rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  exact ht.trans hq
/-- All47 physical roles, all growing totals and actual finite-label return cells are included. -/
theorem prefix_cells (i:Inputs) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (source i)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 48*(inputSize i+runBound i+1) :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputSize i) _ _ (initial_role_bound i) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤ 47*(inputSize i+fuel):=by
    calc
      _ ≤ ∑_k:Stack,(inputSize i+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel i fuel out hr
  omega
/-- Fixed whole all47/real-return storage cap follows the SAME source's own bit-clock. -/
theorem polynomial_space (i:Inputs) :48*(inputSize i+runBound i+1) ≤ 1000000000000*(inputSize i)^6 :=by
  have ht:=runBound_le i
  have hs:=inputSize_pos i
  have hp:=pow_mono (inputSize i) hs 1 6 (by decide)
  simp only [pow_one] at hp
  unfold polynomial at ht
  nlinarith only [ht,hp,hs]
/-- Every genuinely compiled reachable prefix counts all47words and real returns, rather than a projected view. -/
theorem machine_prefix_cells (i:Inputs) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun c=>c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (source i)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 1000000000000*(inputSize i)^6 :=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .source) (aux .total) .start program fuel (source i)
  have hh:=he.trans hr
  cases hout:SemiprimeD1StackCalls.run program fuel (source i) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact (prefix_cells i fuel out hout).trans (polynomial_space i)
end RiemannGaussian.SemiprimeD1StackSourceIncidenceStorage
