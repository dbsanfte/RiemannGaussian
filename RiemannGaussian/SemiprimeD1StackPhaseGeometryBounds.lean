/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseGeometryExecution
/-! # Every actual fourteen-role prefix and real return-cell inventory -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackPhaseGeometryBounds
open SemiprimeD1StackPhaseGeometry SemiprimeD1StackPhaseGeometryComponents
open SemiprimeD1StackPhaseGeometryExecution
/-- A successful prefix cannot extend past the actual source halt. -/
theorem prefix_fuel_le (a t : List Bool) (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial a t)=some out) : fuel≤ runBound a t :=by
  obtain ⟨q,hq,hfinal⟩:=source_run a t
  have hf:fuel≤ q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hfinal,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz:SemiprimeD1StackCalls.run program 1 (done a t)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans hq
/-- All original, transient, acquired, comparison and actual-return cells are paid. -/
theorem prefix_cells (a t : List Bool) (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial a t)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤20000*(a.length+t.length+1) :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (a.length+t.length) _ out (by
    intro k
    rcases k with k|k
    · cases k <;> simp [initial,input,store,S.store]
    · cases k <;> simp [initial,input,store,words]) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤14*(a.length+t.length+fuel):=by
    calc
      _≤∑_k:Stack,(a.length+t.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le a t fuel out hr
  unfold runBound at ht
  omega
/-- The SAME bound applies to every reached prefix of the genuine finite machine. -/
theorem machine_prefix_cells (a t : List Bool) (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial a t)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤20000*(a.length+t.length+1) :=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .exponent) (subStack .output) .start program fuel (initial a t)
  change (SemiprimeD1StackCalls.run program fuel (initial a t)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial a t))) at he
  have hh:=he.trans hr
  cases hc:SemiprimeD1StackCalls.run program fuel (initial a t) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells a t fuel out hc
end RiemannGaussian.SemiprimeD1StackPhaseGeometryBounds
