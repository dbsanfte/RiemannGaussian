/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackUnaryCounter
import RiemannGaussian.SemiprimeD1StackBytecodeBounds

/-! # Linear actual acquisition time for unary control values
The machine reads an original binary control word and outputs actual markers.
The bound depends on the control VALUE, not merely its bit length. It therefore
does not authorize converting the original integer N to unary at binary cost.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackUnaryCounterExecution
open SemiprimeD1StackBytecode SemiprimeD1StackUnaryCounter SemiprimeBitArithmetic
open SemiprimeD1StackAdder (Stack store store_left store_right store_scratch store_output)
open SemiprimeD1StackCopy (run_add)

/-- A physical unary marker sequence; its parameter is proof-side only. -/
def markers (n : ℕ) : List Bool := List.replicate n true

/-- One old marker becomes two real scratch cells in three transitions. -/
theorem double_one (b : Bool) (digits scratch counter : List Bool) (flag : Option Bool) :
    run code 3 (state (some (.double b)) flag [] digits scratch (true::counter))=
      some (state (some (.double b)) (some true) [] digits (true::true::scratch) counter) := by
  simp only [run,Function.iterate_succ_apply,Function.iterate_zero,id_eq,Option.bind_some,
    step,state,Option.map_some,code,execute,store,store_output,store_scratch,
    List.head?_cons,List.tail_cons,choose]

/-- All current counter markers are genuinely consumed and doubled. -/
theorem double_run (n : ℕ) (b : Bool) (digits scratch : List Bool) (flag : Option Bool) :
    run code (3*n+1) (state (some (.double b)) flag [] digits scratch (markers n))=
      some (state (some (.move b)) none [] digits (markers (2*n)++scratch) []) := by
  induction n generalizing scratch flag with
  | zero =>
    simp only [markers,List.replicate_zero,Nat.mul_zero,Nat.zero_add,List.nil_append,
      run,Function.iterate_one,Option.bind_some,step,state,Option.map_some,code,
      execute,store,store_output,List.head?_nil,List.tail_nil,choose]
  | succ n ih =>
    rw [show 3*(n+1)+1=3+(3*n+1) by omega,run_add]
    simp only [markers,List.replicate_succ]
    rw [double_one,Option.bind_some]
    have hh := ih (true::true::scratch) (some true)
    simp only [markers] at hh
    rw [hh]
    rw [show 2*(n+1)=2*n+2 by omega,List.replicate_add (2*n) 2 true]
    simp only [List.replicate_succ,List.replicate_zero,
      List.append_assoc,List.cons_append,List.nil_append]

/-- Moving one scratch marker costs an actual pop and push. -/
theorem move_one (b : Bool) (digits scratch counter : List Bool) (flag : Option Bool) :
    run code 2 (state (some (.move b)) flag [] digits (true::scratch) counter)=
      some (state (some (.move b)) (some true) [] digits scratch (true::counter)) := by
  simp only [run,Function.iterate_succ_apply,Function.iterate_zero,id_eq,Option.bind_some,
    step,state,Option.map_some,code,execute,store,store_scratch,store_output,
    List.head?_cons,List.tail_cons,choose]

/-- Every doubled marker is physically moved back to the counter stack. -/
theorem move_run (n : ℕ) (b : Bool) (digits counter : List Bool) (flag : Option Bool) :
    run code (2*n+1) (state (some (.move b)) flag [] digits (markers n) counter)=
      some (state (some (.finish b)) none [] digits [] (markers n++counter)) := by
  induction n generalizing counter flag with
  | zero =>
    simp only [markers,List.replicate_zero,Nat.mul_zero,Nat.zero_add,List.nil_append,
      run,Function.iterate_one,Option.bind_some,step,state,Option.map_some,code,
      execute,store,store_scratch,List.head?_nil,List.tail_nil,choose]
  | succ n ih =>
    rw [show 2*(n+1)+1=2+(2*n+1) by omega,run_add]
    simp only [markers,List.replicate_succ]
    rw [move_one,Option.bind_some]
    have hh := ih (true::counter) (some true)
    simp only [markers] at hh
    rw [hh]
    have he : markers n++true::counter=true::(markers n++counter) := by
      have hrep : markers n++[true]=true::markers n := by
        simpa only [markers,List.replicate_succ,List.replicate_zero,List.append_nil] using
          (List.replicate_add n 1 true).symm
      calc
        _ = (markers n++[true])++counter := by
          simp only [List.append_assoc,List.singleton_append]
        _ = _ := by rw [hrep,List.cons_append]
    simpa only [markers,List.cons_append] using
      congrArg some (congrArg (state (some (.finish b)) none [] digits []) he)

/-- A complete digit step includes reading, doubling, moving and inserting. -/
theorem digit_run (b : Bool) (digits : List Bool) (n : ℕ) (flag : Option Bool) :
    run code (7*n+4) (state (some .read) flag [] (b::digits) [] (markers n))=
      some (state (some .read) none [] digits []
        (markers (2*n+bitNat b))) := by
  have hr : run code 1 (state (some .read) flag [] (b::digits) [] (markers n))=
      some (state (some (.double b)) (some b) [] digits [] (markers n)) := by
    cases b <;> simp only [run,Function.iterate_one,Option.bind_some,step,state,
      Option.map_some,code,execute,store,store_right,List.head?_cons,List.tail_cons,choose]
  rw [show 7*n+4=1+((3*n+1)+((2*(2*n)+1)+1)) by omega,
    run_add,hr,Option.bind_some,run_add,double_run,List.append_nil,Option.bind_some,
    run_add,move_run,List.append_nil,Option.bind_some]
  cases b <;> simp only [run,Function.iterate_one,Option.bind_some,step,state,
    Option.map_some,code,execute,store,store_output,bitNat,Bool.false_eq_true,
    ite_false,ite_true,Nat.add_zero,markers,List.replicate_succ]

/-- Proof-side MSB-first value specification, never an instruction operand. -/
def highValue (digits : List Bool) (n : ℕ) : ℕ :=
  digits.foldl (fun m b=>2*m+bitNat b) n

/-- Literal transition count for every executed digit phase. -/
def loopTime : List Bool→ℕ→ℕ
  | [],_ => 2
  | b::digits,n => 7*n+4+loopTime digits (2*n+bitNat b)

/-- The complete loop follows the actual physically acquired digit stream. -/
theorem loop_run (digits : List Bool) (n : ℕ) (flag : Option Bool) :
    run code (loopTime digits n) (state (some .read) flag [] digits [] (markers n))=
      some (state none none [] [] [] (markers (highValue digits n))) := by
  induction digits generalizing n flag with
  | nil =>
    simp only [loopTime,highValue,List.foldl_nil,run,Function.iterate_succ_apply,
      Function.iterate_zero,id_eq,Option.bind_some,step,state,Option.map_some,code,
      execute,store,store_right,List.head?_nil,List.tail_nil,choose]
  | cons b digits ih =>
    rw [loopTime,run_add,digit_run,Option.bind_some,ih]
    rfl

/-- MSB-first physical reversal computes the same value as the original word. -/
theorem highValue_reverse (xs : List Bool) : highValue xs.reverse 0=bitValue xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [highValue,List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil] at *
    rw [ih]
    simp only [bitValue]
    omega

/-- Geometric doubling pays for its whole history with the FINAL control value. -/
theorem loopTime_le (digits : List Bool) (n : ℕ) :
    loopTime digits n+7*n ≤ 7*highValue digits n+4*digits.length+2 := by
  induction digits generalizing n with
  | nil => simp only [loopTime,highValue,List.foldl_nil,List.length_nil,Nat.mul_zero];omega
  | cons b digits ih =>
    have hh := ih (2*n+bitNat b)
    simp only [loopTime,highValue,List.foldl_cons,List.length_cons] at *
    omega

/-- Full exact execution starts with only the supplied original binary word. -/
theorem source_run (xs : List Bool) :
    run code (2*xs.length+1+loopTime xs.reverse 0)
      (state (some .reverse) none xs [] [] [])=
      some (state none none [] [] [] (markers (bitValue xs))) := by
  rw [run_add,reverse_run,List.append_nil,Option.bind_some]
  have hh := loop_run xs.reverse 0 none
  simpa only [markers,List.replicate_zero,highValue_reverse] using hh

/-- Actual time is linear in input width AND output marker count. -/
theorem source_time (xs : List Bool) :
    2*xs.length+1+loopTime xs.reverse 0 ≤ 7*bitValue xs+6*xs.length+3 := by
  have hh := loopTime_le xs.reverse 0
  simp only [Nat.mul_zero,Nat.add_zero,List.length_reverse,highValue_reverse] at hh
  omega

/-- Actual source certificate, with no assumed report-to-time conversion. -/
def sourceUnary (xs : List Bool) :
    StateTransition.EvalsToInTime (step code) (state (some .reverse) none xs [] [] [])
      (some (state none none [] [] [] (markers (bitValue xs))))
      (7*bitValue xs+6*xs.length+3) :=
  ⟨⟨_,source_run xs⟩,source_time xs⟩

/-- The actual start is exactly the original single-stack binary input. -/
theorem start_configuration (xs : List Bool) :
    configuration (state (some .reverse) none xs [] [] [])=Turing.initList machine xs := by
  have hs : state (some .reverse) none xs [] [] []=(initial Stack.left Label.reverse xs) := by
    change (⟨some .reverse,none,store xs [] [] []⟩:State Stack Label)=
      ⟨some .reverse,none,fun k=>if k=Stack.left then xs else []⟩
    congr 1
    funext k
    cases k <;> rfl
  rw [hs]
  exact initial_correct Stack.left Stack.output Label.reverse code xs

/-- The actual target has only the physically created unary output. -/
theorem finish_configuration (bits : List Bool) :
    configuration (state none none [] [] [] bits)=Turing.haltList machine bits := by
  have hs : state none none [] [] [] bits=(final Stack.output bits:State Stack Label) := by
    change (⟨none,none,store [] [] [] bits⟩:State Stack Label)=
      ⟨none,none,fun k=>if k=Stack.output then bits else []⟩
    congr 1
    funext k
    cases k <;> rfl
  rw [hs]
  exact final_correct Stack.left Stack.output Label.reverse code bits

/-- Single-input finite machine acquisition, with actual marker output and time. -/
def machineUnary (xs : List Bool) :
    Turing.TM2OutputsInTime machine xs (some (markers (bitValue xs)))
      (7*bitValue xs+6*xs.length+3) := by
  have hh := evalsCorrect Stack.left Stack.output Label.reverse code _ _ _ (sourceUnary xs)
  change StateTransition.EvalsToInTime machine.step
    (configuration (state (some .reverse) none xs [] [] []))
    (some (configuration (state none none [] [] [] (markers (bitValue xs)))))
    (7*bitValue xs+6*xs.length+3) at hh
  have hh0 := Eq.mp (congrArg (fun start : machine.Cfg=>
    StateTransition.EvalsToInTime machine.step start
      (some (configuration (state none none [] [] [] (markers (bitValue xs)))))
      (7*bitValue xs+6*xs.length+3)) (start_configuration xs)) hh
  exact Eq.mp (congrArg (fun finish : machine.Cfg=>
    StateTransition.EvalsToInTime machine.step (Turing.initList machine xs)
      (some finish) (7*bitValue xs+6*xs.length+3))
    (finish_configuration (markers (bitValue xs)))) hh0

/-- All successful source prefixes end before the actual proved halt. -/
theorem prefix_fuel_le (xs : List Bool) (fuel : ℕ) (out : State Stack Label)
    (h : run code fuel (state (some .reverse) none xs [] [] [])=some out) :
    fuel ≤ 7*bitValue xs+6*xs.length+3 := by
  exact (SemiprimeD1StackBytecodeBounds.fuel_le_halt code _ _ out _ fuel
    (source_run xs) rfl h).trans (source_time xs)

/-- Every actual source prefix has linear total physical storage. -/
theorem prefix_cells (xs : List Bool) (fuel : ℕ) (out : State Stack Label)
    (h : run code fuel (state (some .reverse) none xs [] [] [])=some out) :
    SemiprimeD1StackBytecodeBounds.cells out ≤ 28*bitValue xs+25*xs.length+12 := by
  have hs := SemiprimeD1StackBytecodeBounds.run_cells code fuel _ out h
  have hi : SemiprimeD1StackBytecodeBounds.cells (state (some .reverse) none xs [] [] [])=xs.length := by
    change xs.length+(0+(0+(0+0)))=xs.length
    omega
  have hk : Fintype.card Stack=4 := by decide
  rw [hi,hk] at hs
  have hf := prefix_fuel_le xs fuel out h
  omega

/-- Every actual target prefix has the same linear total-cell bound. -/
theorem machine_prefix_cells (xs : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (h : (fun c=>c.bind machine.step)^[fuel] (some (Turing.initList machine xs))=some cfg) :
    (∑k : Stack,(cfg.stk k).length) ≤ 28*bitValue xs+25*xs.length+12 := by
  have hh := run_correct Stack.left Stack.output Label.reverse code fuel
    (state (some .reverse) none xs [] [] [])
  change (run code fuel (state (some .reverse) none xs [] [] [])).map configuration=
    (fun c=>c.bind machine.step)^[fuel]
      (some (configuration (state (some .reverse) none xs [] [] []))) at hh
  have hs : (configuration (state (some .reverse) none xs [] [] []) : machine.Cfg)=
      Turing.initList machine xs := start_configuration xs
  have he : (run code fuel (state (some .reverse) none xs [] [] [])).map configuration=some cfg := by
    calc
      _ = _ := hh
      _ = _ := by exact Eq.trans (congrArg
        (fun start : machine.Cfg=>(fun c : Option machine.Cfg=>c.bind machine.step)^[fuel] (some start)) hs) h
  cases hr : run code fuel (state (some .reverse) none xs [] [] []) with
  | none => rw [hr] at he;cases he
  | some out =>
    rw [hr] at he
    have hc : configuration out=cfg := Option.some.inj he
    subst cfg
    exact prefix_cells xs fuel out hr

/-- Acquired output is a literal marker word of exactly the control value. -/
theorem marker_count (xs : List Bool) : (markers (bitValue xs)).length=bitValue xs := by
  exact List.length_replicate

end RiemannGaussian.SemiprimeD1StackUnaryCounterExecution
