/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetScalarMul

set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace RiemannGaussian.SemiprimeD1StackJetScalarMulExecution
open SemiprimeD1StackJetScalarMul SemiprimeD1StackProcedureTrace

/-- Exact binary product produced by the actual included multiplier. -/
def product (a b : List Bool) : List Bool := (SemiprimeBitArithmetic.mulBits a b).bits

/-- Canonical old modular scalar-product bytes. -/
def result (a b width : List Bool) : List Bool := (SemiprimeD1JetScalarBits.mul width.length a b).bits

/-- Exact transition count of the included actual fixed multiplier. -/
def multiplyTime (a b : List Bool) : ℕ :=
  2*a.length+1+SemiprimeD1StackMultiplierExecution.loopClock b a.reverse []

/-- Exact reducer count, including actual high-bit clearing and canonical trimming. -/
def reduceTime (a b width : List Bool) : ℕ :=
  SemiprimeD1StackReduceExecution.trimTime ((product a b).take width.length).reverse+
    SemiprimeD1StackReduceExecution.prefixTime (product a b) width

/-- Actual whole caller count: nested multiply, cache copy, reduce and final halt. -/
def totalTime (a b width : List Bool) : ℕ :=
  (multiplyTime a b+1)+(5*width.length+4)+(reduceTime a b width+1)+1

/-- Actual closed canonical multiplication, preserving cached physical precision. -/
theorem source_run (a b width : List Bool) :
    C.run program (totalTime a b width) (state (some .start) none none a b [] [] [] [] [] [] [] width [])=
    some (state none none none [] [] [] [] [] [] (result a b width) [] [] width []) := by
  let d0:=store a b [] [] [] [] [] [] [] width []
  let d1:=store [] [] [] [] (product a b) [] [] [] [] width []
  let d2:=store [] [] [] width (product a b) [] [] [] [] width []
  let d3:=store [] [] [] [] [] [] (result a b width) [] [] width []
  have h0 : Runs program (multiplyTime a b+1) .start d0 .copyPrecision d1 := by
    intro outer start hs
    let entered : C.State Stack Label:=⟨some (.multiply (.control .start)),none,none,d0,.copyPrecision::outer⟩
    have hstart : C.run program 1 start=some entered := by
      rcases hs with ⟨hp,hd,hf⟩
      simp [C.run,C.step,C.execute,hp,hd,hf,program,entered]
    have hrel : SemiprimeD1StackValidationLink.Rel Sum.inl Label.multiply d0 .copyPrecision outer
        (SemiprimeD1StackMultiplier.state (some (.control .start)) none none a b [] [] [] [] [] [] []) entered := by
      constructor
      · constructor
        · intro k; rfl
        · intro k hk
          rcases k with k|k
          · exact False.elim (hk k rfl)
          · rfl
      · exact ⟨rfl,rfl⟩
    obtain ⟨finish,hfinish,hr⟩:=SemiprimeD1StackValidationLink.run_rel Sum.inl Label.multiply Sum.inl_injective
      program M.code (fun _=>rfl) d0 .copyPrecision outer _ _ _ entered hrel
      (SemiprimeD1StackMultiplierExecution.source_run a b) rfl
    have desired : SemiprimeD1StackMultiplierLink.DataRel Sum.inl d0
        (SemiprimeD1StackMultiplier.state none none none [] [] [] [] (product a b) [] [] [] []).data d1 := by
      constructor
      · intro k; rfl
      · intro k hk
        rcases k with k|k
        · exact False.elim (hk k rfl)
        · cases k <;> rfl
    have hd:=SemiprimeD1StackMultiplierLink.data_unique Sum.inl d0 _ _ _ hr.1 desired
    have hp : finish.pc=some .copyPrecision ∧ finish.frames=outer := hr.2
    refine ⟨finish,?_,hp.1,hd,hp.2⟩
    have hh : C.run program (1+multiplyTime a b) start=some finish := by
      rw [SemiprimeD1StackReturnLink.run_add,hstart,Option.bind_some]
      exact hfinish
    simpa only [Nat.add_comm] using hh
  have h1 : Runs program (5*width.length+4) .copyPrecision d1 .callReduce d2 := by
    apply included_call program copyStack Label.copy copyStack_injective SemiprimeD1StackCopy.code (0:Fin 9)
      (fun _=>rfl) .copyPrecision .callReduce rfl (5*width.length+3)
      (SemiprimeD1StackCopy.state 0 none width [] []) (SemiprimeD1StackCopy.done width (width++[])) d1 d2
    · rfl
    · rfl
    · exact SemiprimeD1StackCopy.copy_words width [] none
    · constructor
      · intro k; fin_cases k <;> rfl
      · intro k hk; rfl
    · constructor
      · intro k; fin_cases k <;> simp [copyStack,reduceStack,SemiprimeD1StackCopy.done,SemiprimeD1StackCopy.payload,d2,store,SemiprimeD1StackMultiplier.payload]
      · intro k hk
        rcases k with k|k
        · rcases k with k|k
          · cases k <;> first | rfl | exact False.elim (hk 1 rfl)
          · rcases k with k|k <;> rfl
        · cases k <;> rfl
  have h2 : Runs program (reduceTime a b width+1) .callReduce d2 .done d3 := by
    apply included_call program reduceStack Label.reduce reduceStack_injective SemiprimeD1StackReduce.code .take
      (fun _=>rfl) .callReduce .done rfl (reduceTime a b width)
      (SemiprimeD1StackReduce.state (some .take) none (product a b) width [] [])
      (SemiprimeD1StackReduce.state none none [] [] [] (result a b width)) d2 d3
    · rfl
    · rfl
    · exact SemiprimeD1StackReduceExecution.source_run (product a b) width
    · constructor
      · intro k; cases k <;> rfl
      · intro k hk; rfl
    · constructor
      · intro k; cases k <;> rfl
      · intro k hk
        rcases k with k|k
        · rcases k with k|k
          · cases k with
            | left => exact False.elim (hk .right rfl)
            | right => exact False.elim (hk .left rfl)
            | scratch => exact False.elim (hk .scratch rfl)
            | output => exact False.elim (hk .output rfl)
          · rcases k with k|k <;> rfl
        · cases k <;> rfl
  have h01:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
  have h012:=runs_trans program _ _ _ _ _ _ _ _ h01 h2
  obtain ⟨finish,hfinish,hout⟩:=h012 [] (state (some .start) none none a b [] [] [] [] [] [] [] width []) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl d3 [] finish hout
  rw [totalTime,SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
  rfl

/-- Closed actual bit-length budget, retaining the actual nested multiplier bound. -/
def timeBound (n m p : ℕ) : ℕ := SemiprimeD1StackMultiplierExecution.timeBound n m+30*(n+m+p+2)

/-- No product, reduction cost or intermediate width is supplied to the caller. -/
theorem totalTime_le (a b width : List Bool) : totalTime a b width ≤ timeBound a.length b.length width.length := by
  have hm:=SemiprimeD1StackMultiplierExecution.source_time a b
  change multiplyTime a b ≤ SemiprimeD1StackMultiplierExecution.timeBound a.length b.length at hm
  have hr:=(SemiprimeD1StackReduceExecution.sourceReduce (product a b) width).steps_le_m
  change reduceTime a b width ≤ 5*((product a b).length+width.length)+10 at hr
  have hl:=SemiprimeBitArithmetic.mulBits_length a b
  change (product a b).length ≤ 2*a.length+b.length at hl
  unfold totalTime timeBound
  omega

/-- Actual source transition certificate for the concrete modular product. -/
def sourceMul (a b width : List Bool) :
    StateTransition.EvalsToInTime (C.step program) (state (some .start) none none a b [] [] [] [] [] [] [] width [])
      (some (state none none none [] [] [] [] [] [] (result a b width) [] [] width []))
      (timeBound a.length b.length width.length) :=
  ⟨⟨_,source_run a b width⟩,totalTime_le a b width⟩

/-- Actual fixed FinTM2 multiplication modulo the acquired physical precision length. -/
def machineMul (a b width : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (state (some .start) none none a b [] [] [] [] [] [] [] width []))
      (some (SemiprimeD1StackCalls.configuration (state none none none [] [] [] [] [] [] (result a b width) [] [] width [])))
      (timeBound a.length b.length width.length) :=
  SemiprimeD1StackCalls.evalsCorrect (K:=Stack) (L:=Label) (Sum.inl M.input) (reduceStack .output)
    Label.start program _ _ _ (sourceMul a b width)

/-- A single fixed cubic monomial bounds the actual complete scalar multiplication. -/
theorem timeBound_le_cube (n m p : ℕ) : timeBound n m p ≤ 2000*(n+m+p+3)^3 := by
  have hm:=SemiprimeD1StackMultiplierExecution.timeBound_le_cube n m
  unfold timeBound
  nlinarith [Nat.zero_le (n*n*n),Nat.zero_le (m*m*m),Nat.zero_le (p*p*p),
    Nat.zero_le (n*m*p),Nat.zero_le (n*n*p),Nat.zero_le (m*m*p),Nat.zero_le (n*p*p),Nat.zero_le (m*p*p)]

/-- Literal output bytes are those of the original canonical modular multiplier. -/
theorem result_eq (a b width : List Bool) : result a b width=(SemiprimeD1JetScalarBits.mul width.length a b).bits := rfl

/-- Every source prefix counts all eleven Boolean data stacks and actual return frames. -/
theorem prefix_cells (a b width : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (state (some .start) none none a b [] [] [] [] [] [] [] width [])=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 12*(a.length+b.length+width.length+fuel) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (a.length+b.length+width.length)
    _ out (by
      intro k
      rcases k with k|k
      · rcases k with k|k
        · cases k <;> simp [state,store,SemiprimeD1StackMultiplier.payload]
        · rcases k with k|k
          · fin_cases k <;> simp [state,store,SemiprimeD1StackMultiplier.payload]; omega
          · cases k <;> simp [state,store,SemiprimeD1StackMultiplier.payload]; omega
      · cases k <;> simp [state,store]) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k:Stack,(out.data k).length) ≤ 11*(a.length+b.length+width.length+fuel) := by
    calc
      _ ≤ ∑_k:Stack,(a.length+b.length+width.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = 11*(a.length+b.length+width.length+fuel) := by
        have hc : Fintype.card SemiprimeD1StackAdder.Stack=4 := by decide
        simp [Stack,SemiprimeD1StackMultiplier.Stack,hc]
  omega

/-- No successful prefix continues beyond the actual proved scalar-product halt. -/
theorem prefix_fuel_le (a b width : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (state (some .start) none none a b [] [] [] [] [] [] [] width [])=some out) :
    fuel ≤ totalTime a b width := by
  by_contra hn
  have he : fuel=totalTime a b width+(1+(fuel-(totalTime a b width+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hh : C.run program 1 (state none none none [] [] [] [] [] [] (result a b width) [] [] width [])=none := rfl
  rw [hh,Option.bind_none] at hr
  cases hr

/-- Original operand/precision size gives a derived polynomial bound at every successful source prefix. -/
theorem prefix_polynomial_cells (a b width : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (state (some .start) none none a b [] [] [] [] [] [] [] width [])=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤
      12*(a.length+b.length+width.length+timeBound a.length b.length width.length) := by
  have hf:=(prefix_fuel_le a b width fuel out hr).trans (totalTime_le a b width)
  exact (prefix_cells a b width fuel out hr).trans (by omega)

/-- Every actual compiled-machine prefix satisfies the same polynomial physical-cell bound. -/
theorem machine_prefix_polynomial_cells (a b width : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (state (some .start) none none a b [] [] [] [] [] [] [] width [])))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      12*(a.length+b.length+width.length+timeBound a.length b.length width.length) := by
  let start:=state (some .start) none none a b [] [] [] [] [] [] [] width []
  have he:=SemiprimeD1StackCalls.run_correct (Sum.inl M.input) (reduceStack .output) Label.start program fuel start
  change (C.run program fuel start).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start)) at he
  cases hc:C.run program fuel start with
  | none => rw [hc,hr] at he; cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj he
    rw [←hcfg]
    exact prefix_polynomial_cells a b width fuel out hc

end RiemannGaussian.SemiprimeD1StackJetScalarMulExecution
