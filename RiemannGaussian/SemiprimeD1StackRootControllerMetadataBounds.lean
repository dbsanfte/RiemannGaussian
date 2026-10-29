/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootControllerMetadataExecution

/-! # Own fixed polynomial and all98-role storage from original binary N -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootControllerMetadataBounds
open SemiprimeD1StackRootControllerMetadata SemiprimeD1StackRootControllerMetadataExecution
open SemiprimeBitArithmetic (bitValue)
/-- The source starts with only its original binary N role populated. -/
theorem source_input (bits:List Bool) (k:S.Stack) :
    S.input bits k=(if k=S.originalInput then bits else []) := by
  have hi:=SemiprimeD1StackCalls.initial_correct S.originalInput S.ids (.inl .start) S.program bits
  have he:=hi.trans (SemiprimeD1StackRootScopeBankMachine.initial_eq bits)
  have hd:=congrArg (fun cfg:SemiprimeD1StackRootScopeBank.machine.Cfg=>cfg.stk (some k)) he
  exact hd.symm
/-- Genuine one-input initialization; even the schedule input role is physically shared. -/
theorem initial_eq (bits:List Bool) :
    Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) := by
  have hs:SemiprimeD1StackCalls.initial originalInput (.inl .start) bits=initial bits := by
    apply congrArg (fun d=>(⟨some (.inl .start),none,none,d,[]⟩:C.State Stack Label))
    funext k
    cases k with
    | inl k=>
      change (if (Sum.inl k:Stack)=originalInput then bits else [])=S.input bits k
      rw [source_input]
      simp only [originalInput,sourceStack,Sum.inl.injEq]
    | inr k=>rfl
  exact (SemiprimeD1StackCalls.initial_correct originalInput edges (.inl .start) program bits).symm.trans
    (congrArg SemiprimeD1StackCalls.configuration hs)
/-- One exact closed time polynomial, with all constants fixed before every N. -/
def polynomial (n:Nat) : Nat := SemiprimeD1StackRootScopeBankBounds.polynomial n+100000000*(n+1)^3+3
/-- The actual same-program bound is this original-input polynomial. -/
theorem runBound_eq (bits:List Bool) : runBound bits=polynomial bits.length := rfl
/-- A single explicit degree-ten majorant retains both acquisitions and caller work. -/
theorem polynomial_le (n:Nat) : polynomial n ≤ 10^50*(n+1)^10 := by
  have h1:1 ≤ (n+1)^5 := one_le_pow₀ (by omega)
  have h5:(n+1)^5 ≤ (n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h3:(n+1)^3 ≤ (n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have hb:2*((10:Nat)^20*(n+1)^5)+1 ≤ 3*10^20*(n+1)^5 := by omega
  have hs:=Nat.pow_le_pow_left hb 2
  have he:(3*(10:Nat)^20*(n+1)^5)^2=9*10^40*(n+1)^10 := by ring
  rw [he] at hs
  norm_num only at hs
  unfold polynomial SemiprimeD1StackRootScopeBankBounds.polynomial SemiprimeD1StackRootScopeBankBounds.tapeCap
  omega
/-- Explicit constants precede the whole original input family. -/
theorem polynomial_monomial : ∃C k:Nat,∀n,polynomial n ≤ C*(n+1)^k :=
  ⟨10^50,10,polynomial_le⟩
/-- Complete actual source execution under one fixed original-byte polynomial. -/
theorem source_run_polynomial (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t≤10^50*(bits.length+1)^10,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) := by
  obtain ⟨t,ht,hr⟩:=source_run bits hc hN
  exact ⟨t,ht.trans ((runBound_eq bits).le.trans (polynomial_le bits.length)),hr⟩
/-- The very same finite machine starts with N alone and pays every included operation. -/
noncomputable def acquireInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (10^50*(bits.length+1)^10) := by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect originalInput edges (.inl .start) program
  let h:=source_run_polynomial bits hc hN
  let t:=Classical.choose h
  have ht:=Classical.choose_spec h
  exact ⟨⟨t,ht.2⟩,ht.1⟩
/-- Every initial physical role is bounded by the one original input word. -/
theorem initial_role_bound (bits:List Bool) (k:Stack) : ((initial bits).data k).length ≤ bits.length := by
  cases k with
  | inl k=>
    change (S.input bits k).length ≤ bits.length
    rw [source_input]
    split <;> simp
  | inr k=>exact Nat.zero_le _
/-- A successful prefix cannot continue after this same program's actual halt. -/
theorem prefix_fuel_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial bits)=some out) : fuel ≤ runBound bits := by
  obtain ⟨t,ht,he⟩:=source_run bits hc hN
  have hf:fuel ≤ t := by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))) := by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz:SemiprimeD1StackCalls.run program 1 (done bits)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- All98 roles, every retained cache/shadow and all real return cells are included. -/
theorem prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial bits)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 99*(bits.length+runBound bits+1) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length (initial bits) out
    (initial_role_bound bits) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel (initial bits) out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤ 98*(bits.length+fuel) := by
    calc
      _ ≤ ∑_k:Stack,(bits.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits hc hN fuel out hr
  omega
/-- Same complete physical inventory at every actual original-input machine prefix. -/
theorem machine_prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 99*(bits.length+runBound bits+1) := by
  rw [initial_eq] at hr
  have he:=SemiprimeD1StackCalls.run_correct originalInput edges (.inl .start) program fuel (initial bits)
  change (SemiprimeD1StackCalls.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits))) at he
  have hh:=he.trans hr
  cases hrun:SemiprimeD1StackCalls.run program fuel (initial bits) with
  | none=>rw [hrun] at hh;cases hh
  | some out=>
    rw [hrun] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells bits hc hN fuel out hrun
/-- A fixed degree-ten bound includes the complete actual bit-cell footprint. -/
theorem polynomial_space (bits:List Bool) :
    99*(bits.length+runBound bits+1) ≤ 10^53*(bits.length+1)^10 := by
  have hn:bits.length+1 ≤ (bits.length+1)^10 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega:1 ≤ bits.length+1) (by decide:1 ≤ 10)
  have ht:runBound bits ≤ 10^50*(bits.length+1)^10 := (runBound_eq bits).le.trans (polynomial_le _)
  omega
/-- Every transition has at most four fundamental compiled commands. -/
theorem compile_depth (pc:Label) : SemiprimeD1StackBytecode.statementDepth (machine.m pc) ≤ 4 :=
  SemiprimeD1StackCalls.compile_depth (.inl .start:Label) (program pc)
end RiemannGaussian.SemiprimeD1StackRootControllerMetadataBounds
