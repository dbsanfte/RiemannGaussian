/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectClock
/-! # Every actual selector data role and real return cell at every prefix
All63 physical roles are counted, including all25 environment and22 query roles.
The storage bound follows the SAME literal source trace and its own bit clock;
no inactive helper word or real nested return frame is omitted.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectStorage
open SemiprimeD1StackSourceIncidenceSelect SemiprimeD1StackSourceIncidenceSelectExecution
open SemiprimeD1StackSourceIncidenceSelectClock
/-- All seven actual initial source words have lengths bounded by the same physical input inventory. -/
theorem initial_role_bound (i:Inputs) (k:Stack) :((source i).data k).length ≤ inputSize i :=by
  have ht:(occurrenceTape i).length ≤ inputSize i:=by unfold inputSize;omega
  have hc:(catalogue i).length ≤ inputSize i:=by unfold inputSize;omega
  have hs:i.square.length ≤ inputSize i:=by unfold inputSize;omega
  have hu:i.cube.length ≤ inputSize i:=by unfold inputSize;omega
  have hf:i.fourth.length ≤ inputSize i:=by unfold inputSize;omega
  have hn:i.n ≤ inputSize i:=by unfold inputSize;omega
  have hF:i.F ≤ inputSize i:=by unfold inputSize;omega
  rcases k with k|k
  · rcases k with k|k
    · exact Nat.zero_le _
    · cases k <;> first | exact ht | exact hs | exact hu | exact hf | exact Nat.zero_le _
  · cases k
    all_goals first
      | exact hc
      | exact Nat.zero_le _
      | simpa only [source,initial,input,Sum.elim_inr,List.length_replicate] using hn
      | simpa only [source,initial,input,Sum.elim_inr,List.length_replicate] using hF
/-- No successful actual source prefix can run past its true final halt. -/
theorem prefix_fuel (i:Inputs) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (source i)=some out) :fuel ≤ polynomial i :=by
  obtain ⟨t,ht,hstop⟩:=source_run_bounded i
  have hf:fuel ≤ t:=by
    by_contra hn
    have he:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hh:SemiprimeD1StackCalls.run program 1 (done i)=none:=rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- Same literal source prefix counts all63 Boolean fields and every actual nested return symbol. -/
theorem prefix_cells (i:Inputs) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (source i)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤
      1000000000000000000000000000000000*(inputSize i+1)^16 :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputSize i) _ out (initial_role_bound i) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel (source i) out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:=SemiprimeD1StackSourceEnvironmentBounds.word_sum_le out.data (inputSize i+fuel) hd
  rw [stack_card] at hs
  have ht:=prefix_fuel i fuel out hr
  have hS:inputSize i+1 ≤ (inputSize i+1)^16:=by simpa only [pow_one] using
    SemiprimeD1StackSourceIncidenceBounds.pow_mono (inputSize i+1) (by omega) 1 16 (by decide)
  unfold polynomial at ht
  omega
/-- Every reached genuine compiled-machine prefix has the same all63-role and real-return bound. -/
theorem machine_prefix_cells (i:Inputs) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun c=>c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (source i)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      1000000000000000000000000000000000*(inputSize i+1)^16 :=by
  have he:=SemiprimeD1StackCalls.run_correct (queryStack (Q.aux .source)) selected (.local .start) program fuel (source i)
  have hh:=he.trans hr
  cases hout:SemiprimeD1StackCalls.run program fuel (source i) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells i fuel out hout
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectStorage
