/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution
/-! # Every original/cached/new metadata role and every actual return cell -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataBounds
open SemiprimeD1StackPhaseWorkingPrecisionMetadata SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution
/-- Actual initial words contain only original physically charged inputs. -/
theorem initial_bound (a u M : Nat) (t p : List Bool) (k : Stack) :
    ((initial a u M t p).data k).length≤ M+a+u+t.length+p.length :=by
  have h0:([]:List Bool).length≤ M+a+u+t.length+p.length:=Nat.zero_le _
  have ha:(D.unary a).length≤ M+a+u+t.length+p.length:=by rw [D.unary,List.length_replicate];omega
  have hu:(D.unary u).length≤ M+a+u+t.length+p.length:=by rw [D.unary,List.length_replicate];omega
  have hM:(D.unary M).length≤ M+a+u+t.length+p.length:=by rw [D.unary,List.length_replicate];omega
  have ht:t.length≤ M+a+u+t.length+p.length:=by omega
  have hp:p.length≤ M+a+u+t.length+p.length:=by omega
  dsimp only [initial,input,store,SemiprimeD1StackPhaseGeometryGuard.input,
    SemiprimeD1StackPhaseGeometryGuard.store,SemiprimeD1StackPhaseGeometryGuard.words,
    SemiprimeD1StackPhaseGeometry.input,SemiprimeD1StackPhaseGeometry.store,
    SemiprimeD1StackPhaseGeometry.words,SemiprimeD1StackAdder.store,words]
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> assumption
    · cases k <;> assumption
  · rcases k with k|k <;> cases k <;> assumption
/-- Successful source prefixes cannot extend past the actual metadata halt. -/
theorem prefix_fuel_le (a u M : Nat) (t p : List Bool) (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial a u M t p)=some out) : fuel≤ runBound a u M t p :=by
  obtain ⟨q,hq,hfinal⟩:=source_run a u M t p
  have hf:fuel≤ q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hfinal,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz:SemiprimeD1StackCalls.run program 1 (done a u M t p)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans hq
/-- All37 physical fields and ALL real nested guard/divider/product/copy frames are charged. -/
theorem prefix_cells (a u M : Nat) (t p : List Bool) (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial a u M t p)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤100000000*(M+a+u+t.length+p.length+1)^2 :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (M+a+u+t.length+p.length) _ out
    (initial_bound a u M t p) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤37*(M+a+u+t.length+p.length+fuel):=by
    calc
      _≤∑_k:Stack,(M+a+u+t.length+p.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le a u M t p fuel out hr
  unfold runBound at ht
  have hp: M+a+u+t.length+p.length+1≤(M+a+u+t.length+p.length+1)^2:=Nat.le_pow (by decide : 0<(2:Nat))
  omega
/-- Same complete inventory for every prefix of the genuine fixed finite machine. -/
theorem machine_prefix_cells (a u M : Nat) (t p : List Bool) (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial a u M t p)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤100000000*(M+a+u+t.length+p.length+1)^2 :=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .edges) (aux .q) .start program fuel (initial a u M t p)
  change (SemiprimeD1StackCalls.run program fuel (initial a u M t p)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial a u M t p))) at he
  have hh:=he.trans hr
  cases hc:SemiprimeD1StackCalls.run program fuel (initial a u M t p) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells a u M t p fuel out hc
end RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataBounds
