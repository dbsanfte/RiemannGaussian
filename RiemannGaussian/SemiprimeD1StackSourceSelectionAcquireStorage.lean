/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireBounds
/-! # All154 actual data words and real return cells at every compiled source prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireStorage
open SemiprimeD1StackSourceSelectionAcquire SemiprimeD1StackSourceSelectionAcquireEncoding
open SemiprimeD1StackSourceSelectionAcquireExecution SemiprimeD1StackSourceSelectionAcquireBounds
/-- Every initialized physical field is paid by actual row/n/a bytes, with the alphabet cardinality explicitly retained in the envelope. -/
theorem initial_role_bound (net:N.Network) (a:Nat) (k:Stack) :
    ((source net a).data k).length≤ inputSize net a :=by
  rcases k with k|k
  · have h:=SemiprimeD1StackSourceOccurrencesExecution.initial_length net.leftCount (originalRows net) k
    have hb:=(input_bounds net a).2.1
    unfold SemiprimeD1StackSourceOccurrencesBounds.inputSize at hb
    exact h.trans (by omega)
  · rcases k with k|k
    · have h:=SemiprimeD1StackSourceAlphabet64Storage.initial_role_bound a k
      exact h.trans (by have hb:=(input_bounds net a).2.2.1;omega)
    · rcases k with k|k
      · exact Nat.zero_le _
      · rcases k with k|k <;> exact Nat.zero_le _
/-- No successful actual prefix can run beyond this SAME complete source's literal halt. -/
theorem prefix_fuel (net:N.Network) (a fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (source net a)=some out) :fuel≤ timeBound net a :=by
  obtain ⟨q,hq,hfinal⟩:=source_run net a
  have ht:fuel≤ q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hfinal,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hh:SemiprimeD1StackCalls.run program 1 (done net a)=none:=rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  exact ht.trans hq
/-- All154 source/cache/catalogue/selected/output/work/shadow words and actual finite-label returns are included. -/
theorem prefix_cells (net:N.Network) (a fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (source net a)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤155*(inputSize net a+timeBound net a+1) :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputSize net a) _ _ (initial_role_bound net a) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤154*(inputSize net a+fuel):=by
    calc
      _≤∑_k:Stack,(inputSize net a+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel net a fuel out hr
  omega
set_option exponentiation.threshold 512 in
/-- Whole-source storage has fixed constants before every network and exponent, with actual64^a paid in the input envelope. -/
theorem polynomial_space (net:N.Network) (a:Nat) :
    155*(inputSize net a+timeBound net a+1)≤10^503*(inputSize net a)^100 :=by
  have ht:=timeBound_le net a
  have hS:1≤ inputSize net a:=(input_bounds net a).1
  have hpow:inputSize net a≤(inputSize net a)^100:=Nat.le_pow (by decide:0<(100:Nat))
  unfold polynomial at ht
  norm_num only [Nat.reducePow] at ht ⊢
  omega
/-- Every genuine compiled-machine prefix counts ALL154 data roles and the entire real return stack under the SAME whole-source clock. -/
theorem machine_prefix_cells (net:N.Network) (a fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun c=>c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (source net a)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤10^503*(inputSize net a)^100 :=by
  have he:=SemiprimeD1StackCalls.run_correct (occurrenceStack .rows) (keyStack (Keys.aux .output)) (Label.local .start) program fuel (source net a)
  have hh:=he.trans hr
  cases hout:SemiprimeD1StackCalls.run program fuel (source net a) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact (prefix_cells net a fuel out hout).trans (polynomial_space net a)
end RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireStorage
