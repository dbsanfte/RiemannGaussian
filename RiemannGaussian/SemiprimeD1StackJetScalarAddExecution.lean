/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetScalarAdd

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackJetScalarAddExecution
open SemiprimeD1StackJetScalarAdd SemiprimeD1StackProcedureTrace

/-- Two actual fixed-program transitions, used for each physical movement cell. -/
theorem two_steps (a b c : C.State Stack Label)
    (h₁ : C.step program a=some b) (h₂ : C.step program b=some c) : C.run program 2 a=some c := by
  change (C.step program a).bind (C.step program)=some c
  rw [h₁,Option.bind_some,h₂]

/-- Actual source run composition. -/
theorem run_append (m n : ℕ) (a b c : C.State Stack Label)
    (hm : C.run program m a=some b) (hn : C.run program n b=some c) : C.run program (m+n) a=some c := by
  rw [SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some,hn]

/-- Exact literal left payload write. -/
theorem store_left (left right scratch output precision work bits : List Bool) :
    Function.update (store left right scratch output precision work) (.inl .left) bits=store bits right scratch output precision work := by
  funext k
  rcases k with k|k
  · cases k <;> simp [store,Function.update]
  · cases k <;> simp [store,Function.update]

@[simp] theorem store_get_left (left right scratch output precision work : List Bool) : store left right scratch output precision work (.inl .left)=left := rfl

/-- Exact literal right payload write. -/
theorem store_right (left right scratch output precision work bits : List Bool) :
    Function.update (store left right scratch output precision work) (.inl .right) bits=store left bits scratch output precision work := by
  funext k
  rcases k with k|k
  · cases k <;> simp [store,Function.update]
  · cases k <;> simp [store,Function.update]

@[simp] theorem store_get_right (left right scratch output precision work : List Bool) : store left right scratch output precision work (.inl .right)=right := rfl

/-- Exact literal scratch payload write. -/
theorem store_scratch (left right scratch output precision work bits : List Bool) :
    Function.update (store left right scratch output precision work) (.inl .scratch) bits=store left right bits output precision work := by
  funext k
  rcases k with k|k
  · cases k <;> simp [store,Function.update]
  · cases k <;> simp [store,Function.update]

@[simp] theorem store_get_scratch (left right scratch output precision work : List Bool) : store left right scratch output precision work (.inl .scratch)=scratch := rfl

/-- Exact literal output payload write. -/
theorem store_output (left right scratch output precision work bits : List Bool) :
    Function.update (store left right scratch output precision work) (.inl .output) bits=store left right scratch bits precision work := by
  funext k
  rcases k with k|k
  · cases k <;> simp [store,Function.update]
  · cases k <;> simp [store,Function.update]

@[simp] theorem store_get_output (left right scratch output precision work : List Bool) : store left right scratch output precision work (.inl .output)=output := rfl

/-- Exact literal precision payload write. -/
theorem store_precision (left right scratch output precision work bits : List Bool) :
    Function.update (store left right scratch output precision work) (.inr false) bits=store left right scratch output bits work := by
  funext k
  rcases k with k|k
  · cases k <;> simp [store,Function.update]
  · cases k <;> simp [store,Function.update]

@[simp] theorem store_get_precision (left right scratch output precision work : List Bool) : store left right scratch output precision work (.inr false)=precision := rfl

/-- Exact literal work payload write. -/
theorem store_work (left right scratch output precision work bits : List Bool) :
    Function.update (store left right scratch output precision work) (.inr true) bits=store left right scratch output precision bits := by
  funext k
  rcases k with k|k
  · cases k <;> simp [store,Function.update]
  · cases k <;> simp [store,Function.update]

@[simp] theorem store_get_work (left right scratch output precision work : List Bool) : store left right scratch output precision work (.inr true)=work := rfl

/-- Every moved bit executes an actual pop and push; outer frames are retained. -/
theorem move_run (left right scratch output precision work : List Bool) (flag : Option Bool) (rt : Option Label) (frames : List Label) :
    C.run program (2*output.length+1) (⟨some .move,flag,rt,store left right scratch output precision work,frames⟩:C.State Stack Label)=
    some (⟨some .restore,none,rt,store left right (output.reverse++scratch) ([]) precision work,frames⟩:C.State Stack Label) := by
  induction output generalizing scratch flag with
  | nil => simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,program,store_output]
  | cons b output ih =>
    have hs : C.run program 2 (⟨some .move,flag,rt,store left right scratch (b::output) precision work,frames⟩:C.State Stack Label)=
        some (⟨some .move,some b,rt,store left right (b::scratch) (output) precision work,frames⟩:C.State Stack Label) := by
      apply two_steps (b:=⟨some (.movePush b),some b,rt,store left right scratch (output) precision work,frames⟩)
      · cases b <;> simp [C.step,C.execute,SemiprimeD1StackBytecode.choose,program,store_output]
      · simp [C.step,C.execute,program,store_scratch]
    have hh:=run_append 2 (2*output.length+1) _ _ _ hs (ih (b::scratch) (some b))
    simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,List.reverse_cons,List.append_assoc,
      List.singleton_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Every moved bit executes an actual pop and push; outer frames are retained. -/
theorem restore_run (left right scratch output precision work : List Bool) (flag : Option Bool) (rt : Option Label) (frames : List Label) :
    C.run program (2*scratch.length+1) (⟨some .restore,flag,rt,store left right scratch output precision work,frames⟩:C.State Stack Label)=
    some (⟨some .copyPrecision,none,rt,store (scratch.reverse++left) right ([]) output precision work,frames⟩:C.State Stack Label) := by
  induction scratch generalizing left flag with
  | nil => simp [C.run,C.step,C.execute,SemiprimeD1StackBytecode.choose,program,store_scratch]
  | cons b scratch ih =>
    have hs : C.run program 2 (⟨some .restore,flag,rt,store left right (b::scratch) output precision work,frames⟩:C.State Stack Label)=
        some (⟨some .restore,some b,rt,store (b::left) right (scratch) output precision work,frames⟩:C.State Stack Label) := by
      apply two_steps (b:=⟨some (.restorePush b),some b,rt,store left right (scratch) output precision work,frames⟩)
      · cases b <;> simp [C.step,C.execute,SemiprimeD1StackBytecode.choose,program,store_scratch]
      · simp [C.step,C.execute,program,store_left]
    have hh:=run_append 2 (2*scratch.length+1) _ _ _ hs (ih (b::left) (some b))
    simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,List.reverse_cons,List.append_assoc,
      List.singleton_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Literal binary sum produced by the actual adder call. -/
def sum (a b : List Bool) : List Bool := (SemiprimeBitArithmetic.addBits a b false).bits

/-- Canonical target bytes of the original modular scalar-adder. -/
def result (a b width : List Bool) : List Bool := (SemiprimeD1JetScalarBits.add width.length a b).bits

/-- Exact component adder transition count. -/
def adderTime (a b : List Bool) : ℕ := 3*(max a.length b.length+1)+2*(sum a b).length+2

/-- Exact component reducer transition count, including all discarded input/counter cells. -/
def reduceTime (a b width : List Bool) : ℕ :=
  SemiprimeD1StackReduceExecution.trimTime ((sum a b).take width.length).reverse+
    SemiprimeD1StackReduceExecution.prefixTime (sum a b) width

/-- Actual whole procedure count, including every call, movement and final halt. -/
def totalTime (a b width : List Bool) : ℕ :=
  (adderTime a b+1)+(2*(sum a b).length+1)+(2*(sum a b).length+1)+
    (5*width.length+4)+(reduceTime a b width+1)+1

/-- Closed literal execution; precision is preserved, result bytes are canonical, other work clears. -/
theorem source_run (a b width : List Bool) :
    C.run program (totalTime a b width) (state (some .start) none none a b [] [] width [])=
    some (state none none none [] [] [] (result a b width) width []) := by
  let d0:=store a b [] [] width []
  let d1:=store [] [] [] (sum a b) width []
  let d2:=store [] [] (sum a b).reverse [] width []
  let d3:=store (sum a b) [] [] [] width []
  let d4:=store (sum a b) width [] [] width []
  let d5:=store [] [] [] (result a b width) width []
  have h0 : Runs program (adderTime a b+1) .start d0 .move d1 := by
    apply included_call program Sum.inl Label.adder Sum.inl_injective SemiprimeD1StackAdder.code (.start false)
      (fun _=>rfl) .start .move rfl (adderTime a b)
      (SemiprimeD1StackAdder.state (some (.start false)) none a b [] [])
      (SemiprimeD1StackAdder.state none none [] [] [] (sum a b)) d0 d1
    · rfl
    · rfl
    · exact SemiprimeD1StackAdderExecution.source_run a b false
    · constructor
      · intro k; cases k <;> rfl
      · intro k hk; rfl
    · constructor
      · intro k; cases k <;> rfl
      · intro k hk
        rcases k with k|k
        · exact False.elim (hk k rfl)
        · cases k <;> rfl
  have h1 : Runs program (2*(sum a b).length+1) .move d1 .restore d2 := by
    intro frames start hs
    rcases start with ⟨pc,flag,rt,data,fs⟩
    rcases hs with ⟨rfl,rfl,rfl⟩
    refine ⟨⟨some .restore,none,rt,d2,fs⟩,?_,rfl,rfl,rfl⟩
    simpa only [List.append_nil] using move_run [] [] [] (sum a b) width [] flag rt fs
  have h2 : Runs program (2*(sum a b).length+1) .restore d2 .copyPrecision d3 := by
    intro frames start hs
    rcases start with ⟨pc,flag,rt,data,fs⟩
    rcases hs with ⟨rfl,rfl,rfl⟩
    refine ⟨⟨some .copyPrecision,none,rt,d3,fs⟩,?_,rfl,rfl,rfl⟩
    simpa only [List.reverse_reverse,List.length_reverse,List.append_nil] using
      restore_run [] [] (sum a b).reverse [] width [] flag rt fs
  have h3 : Runs program (5*width.length+4) .copyPrecision d3 .callReduce d4 := by
    apply included_call program copyStack Label.copy copyStack_injective SemiprimeD1StackCopy.code (0:Fin 9)
      (fun _=>rfl) .copyPrecision .callReduce rfl (5*width.length+3)
      (SemiprimeD1StackCopy.state 0 none width [] []) (SemiprimeD1StackCopy.done width (width++[])) d3 d4
    · rfl
    · rfl
    · exact SemiprimeD1StackCopy.copy_words width [] none
    · constructor
      · intro k; fin_cases k <;> rfl
      · intro k hk; rfl
    · constructor
      · intro k; fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.done,SemiprimeD1StackCopy.payload,d4]
      · intro k hk
        rcases k with k|k
        · cases k <;> first | rfl | exact False.elim (hk 1 rfl)
        · cases k <;> rfl
  have h4 : Runs program (reduceTime a b width+1) .callReduce d4 .done d5 := by
    apply included_call program Sum.inl Label.reduce Sum.inl_injective SemiprimeD1StackReduce.code .take
      (fun _=>rfl) .callReduce .done rfl (reduceTime a b width)
      (SemiprimeD1StackReduce.state (some .take) none (sum a b) width [] [])
      (SemiprimeD1StackReduce.state none none [] [] [] (result a b width)) d4 d5
    · rfl
    · rfl
    · exact SemiprimeD1StackReduceExecution.source_run (sum a b) width
    · constructor
      · intro k; cases k <;> rfl
      · intro k hk; rfl
    · constructor
      · intro k; cases k <;> rfl
      · intro k hk
        rcases k with k|k
        · exact False.elim (hk k rfl)
        · cases k <;> rfl
  have h01:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
  have h012:=runs_trans program _ _ _ _ _ _ _ _ h01 h2
  have h0123:=runs_trans program _ _ _ _ _ _ _ _ h012 h3
  have h01234:=runs_trans program _ _ _ _ _ _ _ _ h0123 h4
  obtain ⟨finish,hfinish,hout⟩:=h01234 [] (state (some .start) none none a b [] [] width []) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl d5 [] finish hout
  rw [totalTime,SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
  rfl

/-- Concrete actual linear bound in binary operand sizes and physical precision size. -/
def timeBound (n m p : ℕ) : ℕ := 30*(n+m+p+2)

/-- The derived bound pays all actual earlier primitive executions. -/
theorem totalTime_le (a b width : List Bool) : totalTime a b width  ≤  timeBound a.length b.length width.length := by
  have ha:=(SemiprimeD1StackAdderExecution.sourceAdd a b false).steps_le_m
  change adderTime a b  ≤  5*(a.length+b.length)+7 at ha
  have hr:=(SemiprimeD1StackReduceExecution.sourceReduce (sum a b) width).steps_le_m
  change reduceTime a b width  ≤  5*((sum a b).length+width.length)+10 at hr
  have hl:=(SemiprimeBitArithmetic.addBits_counts a b false).2.2.2.2
  change (sum a b).length ≤ max a.length b.length+1 at hl
  unfold totalTime timeBound
  omega

/-- Genuine source execution certificate with a derived original-data budget. -/
def sourceAdd (a b width : List Bool) :
    StateTransition.EvalsToInTime (C.step program) (state (some .start) none none a b [] [] width [])
      (some (state none none none [] [] [] (result a b width) width []))
      (timeBound a.length b.length width.length) :=
  ⟨⟨_,source_run a b width⟩,totalTime_le a b width⟩

/-- Actual fixed finite-stack modular addition, preserving the physical precision cache. -/
def machineAdd (a b width : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (state (some .start) none none a b [] [] width []))
      (some (SemiprimeD1StackCalls.configuration (state none none none [] [] [] (result a b width) width [])))
      (timeBound a.length b.length width.length) :=
  SemiprimeD1StackCalls.evalsCorrect (K:=Stack) (L:=Label) (Sum.inl .left) (Sum.inl .output) Label.start program _ _ _
    (sourceAdd a b width)

/-- Literal output bytes are exactly the original canonical modular coefficient bytes. -/
theorem result_eq (a b width : List Bool) : result a b width=(SemiprimeD1JetScalarBits.add width.length a b).bits := rfl

/-- Every successful source prefix counts all six Boolean stacks and real return frames. -/
theorem prefix_cells (a b width : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (state (some .start) none none a b [] [] width [])=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 7*(a.length+b.length+width.length+fuel) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (a.length+b.length+width.length)
    _ out (by
      intro k
      rcases k with k|k
      · cases k <;> simp [state,store] <;> omega
      · cases k <;> simp [state,store]) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k:Stack,(out.data k).length) ≤ 6*(a.length+b.length+width.length+fuel) := by
    calc
      _ ≤ ∑_k:Stack,(a.length+b.length+width.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = 6*(a.length+b.length+width.length+fuel) := by
        have hc : Fintype.card SemiprimeD1StackAdder.Stack=4 := by decide
        simp [Stack,hc]
  omega

/-- No successful prefix extends past the actual modular-adder halt. -/
theorem prefix_fuel_le (a b width : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (state (some .start) none none a b [] [] width [])=some out) :
    fuel ≤ totalTime a b width := by
  by_contra hn
  have he : fuel=totalTime a b width+(1+(fuel-(totalTime a b width+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hh : C.run program 1 (state none none none [] [] [] (result a b width) width [])=none := rfl
  rw [hh,Option.bind_none] at hr
  cases hr

/-- Every source prefix has a fixed linear input-size space bound. -/
theorem prefix_linear_cells (a b width : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (state (some .start) none none a b [] [] width [])=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤
      7*(a.length+b.length+width.length+timeBound a.length b.length width.length) := by
  have hf:=(prefix_fuel_le a b width fuel out hr).trans (totalTime_le a b width)
  exact (prefix_cells a b width fuel out hr).trans (by omega)

/-- The same all-prefix bound holds for the actually compiled finite-stack machine. -/
theorem machine_prefix_linear_cells (a b width : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (state (some .start) none none a b [] [] width [])))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      7*(a.length+b.length+width.length+timeBound a.length b.length width.length) := by
  let start:=state (some .start) none none a b [] [] width []
  have he:=SemiprimeD1StackCalls.run_correct (Sum.inl SemiprimeD1StackAdder.Stack.left)
    (Sum.inl SemiprimeD1StackAdder.Stack.output) Label.start program fuel start
  change (C.run program fuel start).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start)) at he
  cases hc:C.run program fuel start with
  | none => rw [hc,hr] at he; cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj he
    rw [←hcfg]
    exact prefix_linear_cells a b width fuel out hc

end RiemannGaussian.SemiprimeD1StackJetScalarAddExecution
