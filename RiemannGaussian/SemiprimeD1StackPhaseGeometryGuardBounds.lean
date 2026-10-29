/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseGeometryGuardExecution
/-! # All21 physical roles and every actual geometry/guard return cell -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackPhaseGeometryGuardBounds
open SemiprimeD1StackPhaseGeometryGuard SemiprimeD1StackPhaseGeometryGuardComponents
open SemiprimeD1StackPhaseGeometryGuardExecution
/-- Successful prefixes cannot extend past the actual whole source halt. -/
theorem prefix_fuel_le (a u : Nat) (t : List Bool) (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial a u t)=some out) : fuel≤ runBound a u t :=by
  obtain ⟨q,hq,hfinal⟩:=source_run a u t
  have hf:fuel≤ q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hfinal,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz:SemiprimeD1StackCalls.run program 1 (done a u t)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans hq
/-- Every old geometry field, original u, comparator scratch and real return is counted. -/
theorem prefix_cells (a u : Nat) (t : List Bool) (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial a u t)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤300000*(a+u+t.length+1) :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (a+u+t.length) _ out (by
    intro k
    rcases k with k|k
    · rcases k with k|k
      · cases k <;> simp [initial,input,store,G.input,SemiprimeD1StackPhaseGeometry.store,
          SemiprimeD1StackPhaseGeometry.S.store]
      · cases k <;> simp [initial,input,store,G.input,SemiprimeD1StackPhaseGeometry.store,
          SemiprimeD1StackPhaseGeometry.words]
        omega
    · cases k <;> simp [initial,input,store,words]
      omega) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤21*(a+u+t.length+fuel):=by
    calc
      _≤∑_k:Stack,(a+u+t.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le a u t fuel out hr
  unfold runBound at ht
  omega
/-- SAME all-role/real-return bound for every actual compiled finite-machine prefix. -/
theorem machine_prefix_cells (a u : Nat) (t : List Bool) (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial a u t)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤300000*(a+u+t.length+1) :=by
  have he:=SemiprimeD1StackCalls.run_correct (geometryStack (G.aux .exponent)) (aux .output) .start program fuel (initial a u t)
  change (SemiprimeD1StackCalls.run program fuel (initial a u t)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial a u t))) at he
  have hh:=he.trans hr
  cases hc:SemiprimeD1StackCalls.run program fuel (initial a u t) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells a u t fuel out hc
end RiemannGaussian.SemiprimeD1StackPhaseGeometryGuardBounds
