/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductTableExecution
/-! # Whole N-only product-table machine: full own bit time and all83 roles
The complete literal source has a fixed polynomial per ACTUALLY written scalar.
No table/assignment/metadata/native report is used as a time oracle. The only
runtime input is the original binary N; its physical arity is acquired inside.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackProductTableBounds
open SemiprimeD1StackProductTable SemiprimeD1StackProductTableState SemiprimeD1StackProductTableSpec
open SemiprimeD1StackProductTableExecution
open SemiprimeD1TensorTapeCodec (tape)
/-- Every emitted branch/scalar/vector/word/end byte is included in this bound. -/
theorem tree_length (bits front : List Bool) (n : ℕ) : (tape (tree bits front n)).length+1≤7*2^n := by
  induction n generalizing front with
  | zero=>
    have he:tape (tree bits front 0)=SemiprimeD1BooleanTreeStream.leafBytes (answer bits front):=
      (SemiprimeD1BooleanTreeStream.leafBytes_original _).symm
    rw [he]
    cases answer bits front <;> decide
  | succ n ih=>
    have hl:=ih (front++[false])
    have hr:=ih (front++[true])
    change (true::(tape (tree bits (front++[false]) n)++tape (tree bits (front++[true]) n))).length+1≤_
    simp only [List.length_cons,List.length_append,pow_succ]
    omega
/-- Actual three-word physical arity is linear in original binary-input width. -/
theorem arity_le (bits : List Bool) : arity bits≤198*(bits.length+1) := by
  have h:=SemiprimeD1StackPublicProductBounds.cached_length_le bits
  unfold arity
  omega
/-- Every actual DFS leaf and ALL76-role cleanup have the same fixed original
input cubic bound, even though the source executes separately at every leaf. -/
theorem weight_le (bits : List Bool) :
    SemiprimeD1StackProductTableDFS.weight bits (arity bits)≤100000000000000000000000000*(bits.length+1)^3 := by
  have ha:=arity_le bits
  have hi:bits.length+arity bits+2≤200*(bits.length+1) := by omega
  have hp:=Nat.pow_le_pow_left hi 3
  rw [mul_pow] at hp
  norm_num at hp
  have hpos:0<(bits.length+1)^3:=Nat.pow_pos (by omega)
  unfold SemiprimeD1StackProductTableDFS.weight
  omega
/-- Fixed whole-source bit-time allowance, before every original input. The
exponential is the original physical table arity, never N's numerical value. -/
def runBound (bits : List Bool) : ℕ :=1000000000000000000000000000000*(bits.length+1)^3*2^(arity bits)
/-- Bootstrap, every real arithmetic checker call/cleanup, all recursive
frames and the complete physical output reversal satisfy this SAME-source bound. -/
theorem timeBound_le (bits : List Bool) : timeBound bits≤runBound bits := by
  have hw:=weight_le bits
  have ho: (outputTape bits).length+1≤7*2^(arity bits):=tree_length bits [] (arity bits)
  have hp:1≤(2:ℕ)^(arity bits) := by
    have h:0<(2:ℕ)^(arity bits):=by positivity
    omega
  have hI:1≤(bits.length+1)^3 := by
    have h:0<(bits.length+1)^3:=Nat.pow_pos (by omega)
    omega
  have h23:(bits.length+1)^2≤(bits.length+1)^3:=Nat.pow_le_pow_right (by omega) (by decide : 2≤3)
  have hb:SemiprimeD1StackProductTableBootstrap.bootstrapBound bits≤100000000000000*(bits.length+1)^3:=
    Nat.mul_le_mul_left _ h23
  have hba:SemiprimeD1StackProductTableBootstrap.bootstrapBound bits+5≤(100000000000000+5)*(bits.length+1)^3 := by omega
  have hbas:SemiprimeD1StackProductTableBootstrap.bootstrapBound bits+5≤
      ((100000000000000+5)*(bits.length+1)^3)*2^(arity bits) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul hba hp
  have hws:=Nat.mul_le_mul_right (2^(arity bits)) hw
  unfold timeBound runBound
  calc
    _ ≤ ((100000000000000+5)*(bits.length+1)^3)*2^(arity bits)+
        (100000000000000000000000000*(bits.length+1)^3)*2^(arity bits)+14*2^(arity bits) := by omega
    _ = ((100000000000000+5+100000000000000000000000000)*(bits.length+1)^3+14)*2^(arity bits) := by ring
    _ ≤ _ := Nat.mul_le_mul_right (2^(arity bits)) (by omega)
/-- Complete literal source from original binary N with the closed own clock. -/
theorem source_run_bounded (bits : List Bool) (hb : bits≠[]) :
    ∃t≤runBound bits,C.run program t (initial bits)=some (done bits) := by
  obtain ⟨t,ht,hr⟩:=source_run bits hb
  exact ⟨t,ht.trans (timeBound_le bits),hr⟩
/-- Proof-only source-path selection never enters program control or data. -/
noncomputable def sourceTable (bits : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime (C.step program) (initial bits) (some (done bits)) (runBound bits) := by
  let h:=source_run_bounded bits hb
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- The original binary N is the ENTIRE canonical machine input. -/
theorem initial_configuration (bits : List Bool) :
    Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) := by
  have he:initial bits=SemiprimeD1StackCalls.initial (.inr .source : Stack) Label.start bits := rfl
  rw [he]
  exact (SemiprimeD1StackCalls.initial_correct (.inr .source : Stack) (.inr .output : Stack) Label.start program bits).symm
/-- Genuine complete N-only finite machine, without an arity/table/raw/cache/
predicate/result/clock supplier. Every work role/real return is actually executed. -/
noncomputable def machineTable (bits : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (runBound bits) := by
  rw [initial_configuration]
  exact SemiprimeD1StackCalls.evalsCorrect (.inr .source : Stack) (.inr .output : Stack) Label.start program _ _ _
    (sourceTable bits hb)
/-- A successful physical prefix cannot continue beyond this machine's halt. -/
theorem prefix_fuel_le (bits : List Bool) (hb : bits≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits)=some out) : fuel≤runBound bits := by
  obtain ⟨t,ht,he⟩:=source_run_bounded bits hb
  have hf:fuel≤t := by
    by_contra hn
    have hs:fuel=t+(1+(fuel-(t+1))) := by omega
    rw [hs,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run program 1 (done bits)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- Every actual source prefix counts ALL83 Boolean roles, original N, actual
depth/prefix/output/work/caches, every shadow and all real return-label cells. -/
theorem prefix_cells (bits : List Bool) (hb : bits≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length≤84*(bits.length+runBound bits) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ out
    (SemiprimeD1StackProductTableBootstrap.initial_length bits) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k : Stack,(out.data k).length)≤83*(bits.length+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(bits.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,SemiprimeD1StackProductTableBootstrap.stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits hb fuel out hr
  omega
/-- The SAME all-role/actual-return bound for every compiled-machine prefix,
starting from the canonical one-word original binary input ONLY. -/
theorem machine_prefix_cells (bits : List Bool) (hb : bits≠[]) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤84*(bits.length+runBound bits) := by
  rw [initial_configuration] at hr
  have he:=SemiprimeD1StackCalls.run_correct (.inr .source : Stack) (.inr .output : Stack) Label.start program fuel (initial bits)
  change (C.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial bits))) at he
  have hh:=he.trans hr
  cases hc:C.run program fuel (initial bits) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells bits hb fuel out hc
end RiemannGaussian.SemiprimeD1StackProductTableBounds
