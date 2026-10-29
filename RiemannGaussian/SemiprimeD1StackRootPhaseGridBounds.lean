/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseGridExecution
/-! # Own polynomial phase-grid clock and all126 physical/return-cell prefixes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseGridBounds
open SemiprimeD1StackRootPhaseGrid SemiprimeD1StackRootPhaseGridEncoding
open SemiprimeD1StackRootPhaseGridExecution
open SemiprimeBitArithmetic (bitValue)
/-- Exact acquired logarithm in original canonical input width; proof-side only. -/
theorem lambda_eq (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    SemiprimeD1StackRootRecursiveControlEncoding.lambdaValue bits=Nat.clog 2 (2^20*bits.length+2) :=by
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  simp only [SemiprimeD1StackRootRecursiveControlEncoding.lambdaValue,
    SemiprimeD1StackRootScheduleOriginal.originalLambda,SemiprimeD1PublicPackingReady.scale,←hw]
/-- The actually acquired original parent exponent has the fixed logarithmic envelope. -/
theorem exponent_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    exponentValue bits≤4*Nat.clog 2 (2^20*bits.length+2) :=by
  have h:=SemiprimeD1Schedule.exponent_le_lam
    (SemiprimeD1StackRootRecursiveControlEncoding.lambdaValue bits) 0
  simpa only [exponentValue,lambda_eq bits hc] using h
/-- The usual ceiling-log bound is proved arithmetically, with no clock or operand oracle. -/
theorem pow_clog_le (x:Nat) (hx:1<x) : 2^(Nat.clog 2 x)≤2*x :=by
  have hp:=Nat.pow_pred_clog_lt_self (by decide : 1<2) hx
  have hl:=Nat.clog_pos (by decide : 1<2) hx
  rw [Nat.pred_eq_sub_one] at hp
  have he:Nat.clog 2 x=(Nat.clog 2 x-1)+1:=by omega
  calc
    _=2^((Nat.clog 2 x-1)+1):=congrArg (fun n:Nat=>2^n) he
    _=2^(Nat.clog 2 x-1)*2:=pow_succ _ _
    _≤_:=by omega
/-- Fixed numerical envelopes for actual binary width and phase count. The
exponential is only in logarithmic metadata; original N is never unary. -/
theorem numeric_bounds (ell a:Nat) (ha:a≤4*Nat.clog 2 (2^20*ell+2)) :
    a+2≤10^8*(ell+1) ∧ 2^(a+1)≤10^30*(ell+1)^4 :=by
  let x:Nat:=2^20*ell+2
  have hx:1<x:=by dsimp [x];omega
  have hs:x≤10^7*(ell+1):=by dsimp [x];omega
  have hl:Nat.clog 2 x≤x:=Nat.clog_le_of_le_pow x.lt_two_pow_self.le
  have hp:=pow_clog_le x hx
  change a≤4*Nat.clog 2 x at ha
  refine ⟨by omega,?_⟩
  calc
    2^(a+1)≤2^(4*Nat.clog 2 x+1):=Nat.pow_le_pow_right (by decide) (by omega)
    _=2*(2^(Nat.clog 2 x))^4:=by
      rw [show 4*Nat.clog 2 x+1=Nat.clog 2 x*4+1 by omega,pow_add,pow_mul,pow_one]
      omega
    _≤2*(2*x)^4:=Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hp 4)
    _=32*x^4:=by ring
    _≤32*(10^7*(ell+1))^4:=Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left hs 4)
    _=32*(10^7)^4*(ell+1)^4:=by ring
    _≤10^30*(ell+1)^4:=Nat.mul_le_mul_right _ (by norm_num)
/-- The entire real copy/fill/enum work is bounded by one fixed degree-five polynomial. -/
theorem preparedBound_le (ell a:Nat) (ha:a≤4*Nat.clog 2 (2^20*ell+2)) :
    preparedBound a≤10^42*(ell+1)^5 :=by
  obtain ⟨hw,hp⟩:=numeric_bounds ell a ha
  have hm:=Nat.mul_le_mul (Nat.mul_le_mul_left 100 hw) hp
  have he:100*(10^8*(ell+1))*(10^30*(ell+1)^4)=10^40*(ell+1)^5:=by ring
  rw [he] at hm
  have h1:1≤(ell+1)^5:=one_le_pow₀ (by omega)
  have h5:ell+1≤(ell+1)^5:=by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1≤ell+1) (by decide : 1≤5)
  unfold preparedBound
  nlinarith
/-- One actual original-input bit-clock pays the entire root call and conditional catalogue. -/
theorem runBound_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    runBound bits≤10^60*(bits.length+1)^10 :=by
  have hr:=SemiprimeD1StackRootRecursiveControlBounds.runBound_le bits hc hN
  have he:=preparedBound_le bits.length (exponentValue bits) (exponent_le bits hc)
  have h5:(bits.length+1)^5≤(bits.length+1)^10:=Nat.pow_le_pow_right (by omega) (by decide)
  have hp:=he.trans (Nat.mul_le_mul_left (10^42) h5)
  have h1:1≤(bits.length+1)^10:=one_le_pow₀ (by omega)
  unfold runBound
  omega
/-- Complete same-program trace under that fixed degree-ten original-input clock. -/
theorem source_run_polynomial (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t≤10^60*(bits.length+1)^10,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) :=by
  obtain ⟨t,ht,hr⟩:=source_run bits hc hN
  exact ⟨t,ht.trans (runBound_le bits hc hN),hr⟩
/-- Actual retained source initialization has exactly one supplied N word. -/
theorem root_input (bits:List Bool) (k:R.Stack) : R.input bits k=(if k=R.originalInput then bits else []) :=by
  have hi:=SemiprimeD1StackCalls.initial_correct R.originalInput R.output (.inl .start) R.program bits
  have he:=hi.trans (SemiprimeD1StackRootRecursiveControlBounds.initial_eq bits)
  exact (congrArg (fun cfg:SemiprimeD1StackRootRecursiveControl.machine.Cfg=>cfg.stk (some k)) he).symm
/-- The genuine target machine starts from original N alone, with no second operand. -/
theorem initial_eq (bits:List Bool) : Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) :=by
  have hs:SemiprimeD1StackCalls.initial originalInput (.inl .start) bits=initial bits:=by
    apply congrArg (fun d=>(⟨some (.inl .start),none,none,d,[]⟩:C.State Stack Label))
    funext k
    cases k with
    | inl k=>
      change (if (Sum.inl k:Stack)=originalInput then bits else [])=R.input bits k
      rw [root_input]
      simp only [originalInput,rootStack,Sum.inl.injEq]
    | inr k=>cases k with
      | inl k=>cases k <;> rfl
      | inr i=>fin_cases i <;> rfl
  exact (SemiprimeD1StackCalls.initial_correct originalInput output (.inl .start) program bits).symm.trans
    (congrArg SemiprimeD1StackCalls.configuration hs)
/-- Genuine N-only finite-machine certificate with the same complete own bit clock. -/
noncomputable def gridInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (10^60*(bits.length+1)^10) :=by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect originalInput output (.inl .start) program
  let h:=source_run_polynomial bits hc hN
  let t:=Classical.choose h
  have ht:=Classical.choose_spec h
  exact ⟨⟨t,ht.2⟩,ht.1⟩
/-- Every initial allocated role is paid by the sole original N word. -/
theorem initial_role_bound (bits:List Bool) (k:Stack) : ((initial bits).data k).length≤bits.length :=by
  cases k with
  | inl k=>change (R.input bits k).length≤bits.length;rw [root_input];split <;> simp
  | inr k=>cases k with
    | inl k=>cases k <;> exact Nat.zero_le _
    | inr i=>fin_cases i <;> exact Nat.zero_le _
/-- The actual same-source halt bounds every successful prefix on either branch. -/
theorem prefix_fuel_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial bits)=some out) : fuel≤ runBound bits :=by
  obtain ⟨t,ht,he⟩:=source_run bits hc hN
  have hf:fuel≤t:=by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:SemiprimeD1StackCalls.run program 1 (done bits)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- All126 Boolean roles, all119 retained source cells and every real return
cell are counted at every reached original-input prefix, on both branches. -/
theorem prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial bits)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤127*(bits.length+runBound bits+1) :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length (initial bits) out (initial_role_bound bits) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel (initial bits) out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤126*(bits.length+fuel):=by
    calc
      _≤∑_k:Stack,(bits.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits hc hN fuel out hr
  omega
/-- Same complete storage inventory on the genuine compiled finite-control machine. -/
theorem machine_prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤127*(bits.length+runBound bits+1) :=by
  rw [initial_eq] at hr
  have he:=SemiprimeD1StackCalls.run_correct originalInput output (.inl .start) program fuel (initial bits)
  have hh:(SemiprimeD1StackCalls.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=some cfg:=he.trans hr
  cases hrun:SemiprimeD1StackCalls.run program fuel (initial bits) with
  | none=>rw [hrun] at hh;cases hh
  | some out=>
    rw [hrun] at hh
    have heq:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells bits hc hN fuel out hrun
/-- A fixed polynomial bounds all actual data and real-return cells. -/
theorem polynomial_space (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    127*(bits.length+runBound bits+1)≤10^63*(bits.length+1)^10 :=by
  have ht:=runBound_le bits hc hN
  have hn:bits.length+1≤(bits.length+1)^10:=by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1≤bits.length+1) (by decide : 1≤10)
  omega
/-- Every actual compiled instruction has at most four fundamental commands. -/
theorem compile_depth (pc:Label) : SemiprimeD1StackBytecode.statementDepth (machine.m pc)≤4 :=
  SemiprimeD1StackCalls.compile_depth (.inl .start:Label) (program pc)
end RiemannGaussian.SemiprimeD1StackRootPhaseGridBounds
