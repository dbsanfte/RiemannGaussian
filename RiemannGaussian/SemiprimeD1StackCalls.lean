/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBytecode

/-! # Finite procedure calls with an actual return stack
Data stacks contain Boolean payloads. The separate return stack contains fixed
finite program labels; it does not contain native counters or environments.
Every stack alphabet and all internal flags are finite. Captured data and heap
frames remain explicit payload work, not unbounded internal control.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackCalls

/-- Procedure instructions extend literal bytecode, with no function-valued operands. -/
inductive Instruction (K L : Type) where
  /-- One literal Boolean-stack instruction. -/
  | base (instruction : SemiprimeD1StackBytecode.Instruction K L)
  /-- Push the actual finite return label, then jump to the literal callee. -/
  | call (callee continuation : L)
  /-- Pop and jump to the actual saved return label; empty return stack halts. -/
  | ret
  deriving Repr

/-- Source procedure state; all unbounded frames are actual stack payload. -/
structure State (K L : Type) where
  /-- Finite current label. -/
  pc : Option L
  /-- Finite last Boolean read. -/
  flag : Option Bool
  /-- Finite last continuation read. -/
  returned : Option L
  /-- Actual Boolean argument/data stacks. -/
  data : K→List Bool
  /-- Actual unbounded return stack over the FIXED finite program-label alphabet. -/
  frames : List L

/-- Literal procedure execution, including actual return-frame push/pop. -/
def execute {K L : Type} [DecidableEq K] : Instruction K L→State K L→State K L
  | .base (.push k b next),state =>
    ⟨some next,state.flag,state.returned,Function.update state.data k (b::state.data k),state.frames⟩
  | .base (.pop k empty low high),state =>
    let bit:=(state.data k).head?
    ⟨some (SemiprimeD1StackBytecode.choose empty low high bit),bit,state.returned,
      Function.update state.data k (state.data k).tail,state.frames⟩
  | .base (.peek k empty low high),state =>
    let bit:=(state.data k).head?
    ⟨some (SemiprimeD1StackBytecode.choose empty low high bit),bit,state.returned,state.data,state.frames⟩
  | .base (.jump next),state => ⟨some next,state.flag,state.returned,state.data,state.frames⟩
  | .base .halt,state => ⟨none,none,none,state.data,state.frames⟩
  | .call callee continuation,state =>
    ⟨some callee,none,none,state.data,continuation::state.frames⟩
  | .ret,state =>
    match state.frames with
    | [] => ⟨none,none,none,state.data,[]⟩
    | label::frames => ⟨some label,state.flag,some label,state.data,frames⟩

/-- Executable first-order procedure step, independent of any solved-value supplier. -/
def step {K L : Type} [DecidableEq K] (code : L→Instruction K L) (state : State K L) : Option (State K L) :=
  state.pc.map (fun label=>execute (code label) state)

/-- Literal finite source transition traversal. -/
def run {K L : Type} [DecidableEq K] (code : L→Instruction K L) (fuel : ℕ)
    (state : State K L) : Option (State K L) :=
  (fun state=>state.bind (step code))^[fuel] (some state)

/-- Actual typed finite alphabet family, indexed by return/data stack tags. -/
def symbols {K : Type} (L : Type) : Option K→Type
  | none => L
  | some _ => Bool

/-- Encode the actual source stacks without interpreting or synthesizing any answer. -/
def payload {K L : Type} (state : State K L) : (k : Option K)→List (symbols L k)
  | none => state.frames
  | some k => state.data k

/-- Actual target configuration with only finite flags in the internal state. -/
def configuration {K L : Type} (state : State K L) :
    Turing.TM2.Cfg (symbols (K:=K) L) L (Option Bool×Option L) :=
  ⟨state.pc,(state.flag,state.returned),payload state⟩

/-- Fixed literal Boolean dispatch in the enlarged finite flag state. -/
def dispatch {K L : Type} (empty low high : L) :
    Turing.TM2.Stmt (symbols (K:=K) L) L (Option Bool×Option L) :=
  .branch (fun flag=>flag.1.isNone) (.goto (fun _=>empty))
    (.branch (fun flag=>flag.1.getD false) (.goto (fun _=>high)) (.goto (fun _=>low)))

/-- Compile actual procedure calls and returns to genuine stack operations. -/
def compileInstruction {K L : Type} (main : L) :
    Instruction K L→Turing.TM2.Stmt (symbols (K:=K) L) L (Option Bool×Option L)
  | .base (.push k b next) => .push (some k) (fun _=>b) (.goto (fun _=>next))
  | .base (.pop k empty low high) =>
    .pop (some k) (fun flag bit=>(bit,flag.2)) (dispatch empty low high)
  | .base (.peek k empty low high) =>
    .peek (some k) (fun flag bit=>(bit,flag.2)) (dispatch empty low high)
  | .base (.jump next) => .goto (fun _=>next)
  | .base .halt => .load (fun _=>(none,none)) .halt
  | .call callee continuation => .push none (fun _=>continuation)
      (.load (fun _=>(none,none)) (.goto (fun _=>callee)))
  | .ret =>
    .pop none (fun flag returned=>(flag.1,returned))
      (.branch (fun flag=>flag.2.isNone) (.load (fun _=>(none,none)) .halt)
        (.goto (fun flag=>flag.2.getD main)))

/-- Fixed finite procedure machine; every alphabet, including returns, is finite. -/
def machine {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (input output : K) (main : L) (code : L→Instruction K L) : Turing.FinTM2 where
  K:=Option K
  k₀:=some input
  k₁:=some output
  Γ:=symbols L
  Γk₀Fin:=inferInstanceAs (Fintype Bool)
  Λ:=L
  main:=main
  σ:=Option Bool×Option L
  initialState:=(none,none)
  m label:=compileInstruction main (code label)

/-- Every stack alphabet is finite, not only the input alphabet. -/
theorem all_alphabets_finite {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (input output : K) (main : L) (code : L→Instruction K L) :
    ∀k,Finite ((machine input output main code).Γ k) := by
  intro k
  cases k with
  | none => exact inferInstanceAs (Finite L)
  | some k => exact inferInstanceAs (Finite Bool)

/-- Internal control carries only finite Boolean and finite return-label flags. -/
theorem control_finite {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (input output : K) (main : L) (code : L→Instruction K L) :
    Finite (machine input output main code).σ :=
  inferInstanceAs (Finite (Option Bool×Option L))

/-- At most one actual return frame is allocated by one source instruction. -/
theorem execute_frame_bound {K L : Type} [DecidableEq K]
    (instruction : Instruction K L) (state : State K L) :
    (execute instruction state).frames.length  ≤  state.frames.length+1 := by
  cases instruction with
  | base instruction => cases instruction <;> exact Nat.le_succ _
  | call callee continuation => exact le_refl _
  | ret => cases hf:state.frames <;> simp only [execute,hf,List.length_nil,List.length_cons] <;> omega
/-- Updating an actual data stack commutes with the return/data stack encoding. -/
theorem payload_data {K L : Type} [DecidableEq K] (state : State K L)
    (k : K) (bits : List Bool) :
    payload {state with data:=Function.update state.data k bits}=
      Function.update (payload state) (some k) bits := by
  funext stack
  cases stack with
  | none => simp [payload,Function.update] ; rfl
  | some j =>
    by_cases h:j=k
    · subst j
      simp [payload,Function.update] ; rfl
    · simp [payload,Function.update,h] ; rfl

/-- Updating the actual finite-symbol return stack commutes with its encoding. -/
theorem payload_frames {K L : Type} [DecidableEq K] (state : State K L) (frames : List L) :
    payload {state with frames:=frames}=Function.update (payload state) none frames := by
  funext stack
  cases stack with
  | none => simp [payload,Function.update] ; rfl
  | some j => simp [payload,Function.update] ; rfl

/-- Finite Boolean dispatch preserves the actual remembered return flag. -/
theorem dispatch_correct {K L : Type} [DecidableEq K] (empty low high : L)
    (flag : Option Bool) (returned : Option L) (store : (k:Option K)→List (symbols L k)) :
    Turing.TM2.stepAux (dispatch empty low high) (flag,returned) store=
      ⟨some (SemiprimeD1StackBytecode.choose empty low high flag),(flag,returned),store⟩ := by
  cases flag with
  | none => rfl
  | some b => cases b <;> rfl

/-- One source call/return/base instruction equals one actual finite-machine transition. -/
theorem instruction_correct {K L : Type} [DecidableEq K] (main : L)
    (instruction : Instruction K L) (state : State K L) :
    Turing.TM2.stepAux (compileInstruction main instruction) (state.flag,state.returned) (payload state)=
      configuration (execute instruction state) := by
  cases instruction with
  | base instruction =>
    cases instruction with
    | push k b next =>
      change Turing.TM2.Cfg.mk (some next) (state.flag,state.returned)
        (Function.update (payload state) (some k) (b::state.data k))=
        Turing.TM2.Cfg.mk (some next) (state.flag,state.returned)
          (payload {state with data:=Function.update state.data k (b::state.data k)})
      exact congrArg (fun store=>Turing.TM2.Cfg.mk (some next) (state.flag,state.returned) store)
        (payload_data state k (b::state.data k)).symm
    | pop k empty low high =>
      change Turing.TM2.stepAux (dispatch empty low high) ((state.data k).head?,state.returned)
        (Function.update (payload state) (some k) (state.data k).tail)=_
      rw [dispatch_correct]
      change Turing.TM2.Cfg.mk _ _ _=Turing.TM2.Cfg.mk
        (some (SemiprimeD1StackBytecode.choose empty low high (state.data k).head?))
        ((state.data k).head?,state.returned)
        (payload {state with data:=Function.update state.data k (state.data k).tail})
      rw [payload_data]
    | peek k empty low high => exact dispatch_correct empty low high _ _ _
    | jump next => rfl
    | halt => rfl
  | call callee continuation =>
    change Turing.TM2.Cfg.mk (some callee) (none,none)
      (Function.update (payload state) none (continuation::state.frames))=
      Turing.TM2.Cfg.mk (some callee) (none,none)
        (payload {state with frames:=continuation::state.frames})
    exact congrArg (fun store=>(Turing.TM2.Cfg.mk (some callee) (none,none) store:
      Turing.TM2.Cfg (symbols (K:=K) L) L (Option Bool×Option L)))
      (payload_frames state (continuation::state.frames)).symm
  | ret =>
    cases hf:state.frames with
    | nil =>
      change Turing.TM2.stepAux
        (.branch (fun flag:Option Bool×Option L=>flag.2.isNone)
          (.load (fun _=>(none,none)) .halt) (.goto (fun flag=>flag.2.getD main)))
        (state.flag,state.frames.head?) (Function.update (payload state) none state.frames.tail)=_
      simp only [hf,List.head?_nil,List.tail_nil,Turing.TM2.stepAux,Option.isNone_none,Bool.cond_true,
        execute,configuration]
      change Turing.TM2.Cfg.mk none (none,none) (Function.update (payload state) none [])=
        Turing.TM2.Cfg.mk none (none,none) (payload {state with frames:=[]})
      exact congrArg (fun store=>(Turing.TM2.Cfg.mk none (none,none) store:
        Turing.TM2.Cfg (symbols (K:=K) L) L (Option Bool×Option L)))
        (payload_frames state []).symm
    | cons label frames =>
      change Turing.TM2.stepAux
        (.branch (fun flag:Option Bool×Option L=>flag.2.isNone)
          (.load (fun _=>(none,none)) .halt) (.goto (fun flag=>flag.2.getD main)))
        (state.flag,state.frames.head?) (Function.update (payload state) none state.frames.tail)=_
      simp only [hf,List.head?_cons,List.tail_cons,Turing.TM2.stepAux,Option.isNone_some,Bool.cond_false,Option.getD_some,
        execute,configuration]
      change Turing.TM2.Cfg.mk (some label) (state.flag,some label) (Function.update (payload state) none frames)=
        Turing.TM2.Cfg.mk (some label) (state.flag,some label) (payload {state with frames:=frames})
      exact congrArg (fun store=>Turing.TM2.Cfg.mk (some label) (state.flag,some label) store)
        (payload_frames state frames).symm
/-- Whole actual procedure-step refinement to the finite target machine. -/
theorem step_correct {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (input output : K) (main : L) (code : L→Instruction K L) (state : State K L) :
    (machine input output main code).step (configuration state)=
      (step code state).map configuration := by
  cases state with
  | mk pc flag returned data frames =>
    cases pc with
    | none => rfl
    | some label =>
      exact congrArg some
        (instruction_correct main (code label) (⟨some label,flag,returned,data,frames⟩:State K L))

/-- Actual finite source execution equals the target execution at the same step count. -/
theorem run_correct {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (input output : K) (main : L) (code : L→Instruction K L) (fuel : ℕ) (state : State K L) :
    (run code fuel state).map configuration=
      (fun cfg=>cfg.bind (machine input output main code).step)^[fuel] (some (configuration state)) := by
  have h (n:ℕ) (state:Option (State K L)) :
      ((fun state=>state.bind (step code))^[n] state).map configuration=
        (fun cfg=>cfg.bind (machine input output main code).step)^[n] (state.map configuration) := by
    induction n generalizing state with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply',←ih]
      cases hs:((fun state=>state.bind (step code))^[n] state) with
      | none => rfl
      | some state => exact (step_correct input output main code state).symm
  exact h fuel (some state)

/-- Concrete source execution certificates become actual finite-machine time certificates. -/
def evalsCorrect {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (input output : K) (main : L) (code : L→Instruction K L) (start finish:State K L)
    (time:ℕ) (h:StateTransition.EvalsToInTime (step code) start (some finish) time) :
    StateTransition.EvalsToInTime (machine input output main code).step
      (configuration start) (some (configuration finish)) time := by
  refine ⟨⟨h.steps,?_⟩,h.steps_le_m⟩
  have hr:=run_correct input output main code h.steps start
  have he:=h.evals_in_steps
  change run code h.steps start=some finish at he
  rw [he] at hr
  exact hr.symm

/-- One actual successful source step allocates at most one return frame. -/
theorem step_frame_bound {K L : Type} [DecidableEq K] (code:L→Instruction K L)
    (state out:State K L) (h:step code state=some out) :
    out.frames.length ≤ state.frames.length+1 := by
  cases hp:state.pc with
  | none => simp only [step,hp,Option.map_none] at h;cases h
  | some label =>
    change (state.pc.map (fun label=>execute (code label) state))=some out at h
    rw [hp,Option.map_some] at h
    cases h
    exact execute_frame_bound _ _

/-- Source successor execution is a genuine final step, not a result lookup. -/
theorem run_succ {K L : Type} [DecidableEq K] (code:L→Instruction K L)
    (fuel:ℕ) (state:State K L) :
    run code (fuel+1) state=(run code fuel state).bind (step code) := by
  unfold run
  rw [Function.iterate_succ_apply']

/-- Every reached return stack has a proved bound from actual executed source steps. -/
theorem run_frame_bound {K L : Type} [DecidableEq K] (code:L→Instruction K L)
    (fuel:ℕ) (state out:State K L) (h:run code fuel state=some out) :
    out.frames.length ≤ state.frames.length+fuel := by
  induction fuel generalizing out with
  | zero => change some state=some out at h;cases h;exact le_refl _
  | succ fuel ih =>
    rw [run_succ] at h
    cases hm:run code fuel state with
    | none => simp only [hm,Option.bind_none] at h;cases h
    | some mid =>
      have hs:step code mid=some out:=by simpa only [hm,Option.bind_some] using h
      have hb:=step_frame_bound code mid out hs
      have ht:=ih mid hm
      omega

/-- Actual initial source data with an EMPTY real return stack. -/
def initial {K L : Type} [DecidableEq K] (input:K) (main:L) (bits:List Bool) : State K L :=
  ⟨some main,none,none,fun k=>if k=input then bits else [],[]⟩

/-- Actual final source data with every auxiliary/return stack empty. -/
def final {K L : Type} [DecidableEq K] (output:K) (bits:List Bool) : State K L :=
  ⟨none,none,none,fun k=>if k=output then bits else [],[]⟩

/-- Finite source input encoding equals the actual machine input. -/
theorem initial_correct {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (input output:K) (main:L) (code:L→Instruction K L) (bits:List Bool) :
    configuration (initial input main bits)=Turing.initList (machine input output main code) bits := by
  dsimp only [configuration,initial,Turing.initList,machine]
  congr 1
  funext stack
  cases stack with
  | none => rfl
  | some k =>
    by_cases h:k=input
    · subst k; simp [payload,symbols]; rfl
    · simp [payload,symbols,h]

/-- Finite source output encoding equals the actual clean halting configuration. -/
theorem final_correct {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (input output:K) (main:L) (code:L→Instruction K L) (bits:List Bool) :
    configuration (final output bits:State K L)=Turing.haltList (machine input output main code) bits := by
  dsimp only [configuration,final,Turing.haltList,machine]
  congr 1
  funext stack
  cases stack with
  | none => rfl
  | some k =>
    by_cases h:k=output
    · subst k; simp [payload,symbols]; rfl
    · simp [payload,symbols,h]

/-- Actual source trace to the corresponding genuine finite-machine input/output bound. -/
def outputsOfSource {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (input output:K) (main:L) (code:L→Instruction K L) (bits result:List Bool) (time:ℕ)
    (h:StateTransition.EvalsToInTime (step code) (initial input main bits) (some (final output result)) time) :
    Turing.TM2OutputsInTime (machine input output main code) bits (some result) time := by
  have ht:=evalsCorrect input output main code _ _ time h
  rw [initial_correct input output main code bits,final_correct input output main code result] at ht
  exact ht

/-- Each compiled call/return/base transition has at most four fundamental commands. -/
theorem compile_depth {K L : Type} (main:L) (instruction:Instruction K L) :
    SemiprimeD1StackBytecode.statementDepth (compileInstruction main instruction) ≤ 4 := by
  cases instruction with
  | base instruction =>
    cases instruction <;> simp only [compileInstruction,dispatch,SemiprimeD1StackBytecode.statementDepth] <;> decide
  | call callee continuation => exact (by decide:3 ≤ 4)
  | ret => exact (by decide:4 ≤ 4)
/-- One fixed five-label procedure program, independent of every input word. -/
def prependCode (label:Fin 5) : Instruction Unit (Fin 5) :=
  if label=0 then .call 2 1 else if label=1 then .base .halt
  else if label=2 then .base (.push () true 3) else .ret

/-- Concrete procedure machine; finite types and code are fixed before input. -/
def prependMachine : Turing.FinTM2 := machine () () 0 prependCode

/-- Actual callee push, return, and caller halt preserve the arbitrary input tail. -/
theorem prepend_run (bits:List Bool) :
    run prependCode 4 (initial () 0 bits)=some (final () (true::bits):State Unit (Fin 5)) := by
  change some (⟨none,none,none,Function.update (fun k:Unit=>if k=() then bits else []) ()
    (true::bits),[]⟩:State Unit (Fin 5))=_
  congr 1

/-- Actual finite procedure-machine input/output bound, not a supplied result trace. -/
def prependOutputs (bits:List Bool) :
    Turing.TM2OutputsInTime prependMachine bits (some (true::bits)) 4 := by
  apply outputsOfSource () () 0 prependCode bits (true::bits) 4
  exact ⟨⟨4,prepend_run bits⟩,le_refl _⟩
end RiemannGaussian.SemiprimeD1StackCalls
