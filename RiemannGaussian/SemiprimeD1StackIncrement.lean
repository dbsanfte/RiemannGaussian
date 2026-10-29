/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTapeFieldMachine
import RiemannGaussian.SemiprimeBitArithmetic

/-! # Fixed-width physical increment with overflow
A fixed finite-control machine consumes an arbitrary little-endian Boolean word
and returns its overflow bit followed by an equally wide wrapped word. All
length/value arithmetic below is specification/proof data, never machine state.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackIncrement
open Turing Turing.TM2 Turing.TM2.Stmt
open SemiprimeBitArithmetic (bitValue bitNat)
open SemiprimeD1TensorTapeFieldMachine (Stack Alphabet Registers contents)

/-- The four fixed carry/copy/output phases. -/
inductive PC | carry | copy | reverse | finish deriving DecidableEq,Inhabited,Repr
instance : Fintype PC where
  elems := {.carry,.copy,.reverse,.finish}
  complete := by intro k; cases k <;> simp

/-- Actual little-endian wrapped word, used only in specifications. -/
def wrapped : List Bool → List Bool
  | [] => []
  | false::xs => true::xs
  | true::xs => false::wrapped xs

/-- Carry leaving the most significant bit, including overflow at width zero. -/
def overflow : List Bool → Bool
  | [] => true
  | false::_ => false
  | true::xs => overflow xs

/-- Actual fixed stack program: no arithmetic or native length operation. -/
def program : PC → Stmt Alphabet PC Registers
  | .carry => .pop .input (fun _ b => (b,false))
      (.branch (fun v => v.1.isSome)
        (.branch (fun v => v.1==some true)
          (.push .scratch (fun _ => false) (.goto (fun _ => .carry)))
          (.push .scratch (fun _ => true) (.goto (fun _ => .copy))))
        (.load (fun _ => (none,true)) (.goto (fun _ => .reverse))))
  | .copy => .pop .input (fun _ b => (b,false))
      (.branch (fun v => v.1.isSome)
        (.push .scratch (fun v => v.1.getD false) (.goto (fun _ => .copy)))
        (.goto (fun _ => .reverse)))
  | .reverse => .pop .scratch (fun v b => (b,v.2))
      (.branch (fun v => v.1.isSome)
        (.push .output (fun v => v.1.getD false) (.goto (fun _ => .reverse)))
        (.goto (fun _ => .finish)))
  | .finish => .push .output (fun v => v.2) .halt

/-- Genuine finite-alphabet machine, with only six finite register settings. -/
def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := PC
  main := .carry
  σ := Registers
  initialState := (none,false)
  m := program

/-- Literal configurations of its three Boolean stacks. -/
def cfg (pc : Option PC) (v : Registers) (input scratch output : List Bool) :
    Cfg Alphabet PC Registers := ⟨pc,v,contents input scratch output⟩

/-- Actual primitive transition function. -/
def step := TM2.step program

/-- Exact transition paths; the count exists only in the proof. -/
inductive Executes : ℕ → Cfg Alphabet PC Registers → Cfg Alphabet PC Registers → Prop
  | refl (c) : Executes 0 c c
  | next {n c d e} : step c=some d → Executes n d e → Executes (n+1) c e

/-- Concatenate actual executions. -/
theorem Executes.trans {n m : ℕ} {a b c : Cfg Alphabet PC Registers}
    (h : Executes n a b) (g : Executes m b c) : Executes (n+m) a c := by
  induction h with
  | refl => simpa using g
  | @next n a d b hs ht ih =>
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Executes.next hs (ih g)

/-- Actual Mathlib iterate equation for every proved path. -/
theorem Executes.iterates {n : ℕ} {a b : Cfg Alphabet PC Registers} (h : Executes n a b) :
    ((fun x : Option (Cfg Alphabet PC Registers) => x.bind step)^[n]) (some a)=some b := by
  induction h with
  | refl => rfl
  | @next n a d b hs ht ih =>
    rw [Function.iterate_succ_apply]
    simpa only [Option.bind_some,hs] using ih

/-- Copy the high suffix after carry has terminated. -/
theorem copy_exec (v : Registers) (xs rev out : List Bool) :
    Executes (xs.length+1) (cfg (some .copy) v xs rev out)
      (cfg (some .reverse) (none,false) [] (xs.reverse++rev) out) := by
  induction xs generalizing v rev with
  | nil =>
    apply Executes.next ?_ (Executes.refl _)
    simp [SemiprimeD1StackIncrement.step,program,cfg,contents,TM2.step,TM2.stepAux]
  | cons b bs ih =>
    have hs : step (cfg (some .copy) v (b::bs) rev out)=
        some (cfg (some .copy) (some b,false) bs (b::rev) out) := by
      simp [SemiprimeD1StackIncrement.step,program,cfg,contents,TM2.step,TM2.stepAux]
    simpa [List.reverse_cons,List.append_assoc] using Executes.next hs (ih (some b,false) (b::rev))

/-- Actual carry scan produces the wrapped bytes and the actual overflow flag. -/
theorem carry_exec (v : Registers) (xs rev out : List Bool) :
    Executes (xs.length+1) (cfg (some .carry) v xs rev out)
      (cfg (some .reverse) (none,overflow xs) [] ((wrapped xs).reverse++rev) out) := by
  induction xs generalizing v rev with
  | nil =>
    apply Executes.next ?_ (Executes.refl _)
    simp [SemiprimeD1StackIncrement.step,program,cfg,contents,wrapped,overflow,TM2.step,TM2.stepAux]
  | cons b bs ih =>
    cases b with
    | false =>
      have hs : step (cfg (some .carry) v (false::bs) rev out)=
          some (cfg (some .copy) (some false,false) bs (true::rev) out) := by
        simp [SemiprimeD1StackIncrement.step,program,cfg,contents,TM2.step,TM2.stepAux]
      simpa [wrapped,overflow,List.reverse_cons,List.append_assoc] using
        Executes.next hs (copy_exec (some false,false) bs (true::rev) out)
    | true =>
      have hs : step (cfg (some .carry) v (true::bs) rev out)=
          some (cfg (some .carry) (some true,false) bs (false::rev) out) := by
        simp [SemiprimeD1StackIncrement.step,program,cfg,contents,TM2.step,TM2.stepAux]
      simpa [wrapped,overflow,List.reverse_cons,List.append_assoc] using
        Executes.next hs (ih (some true,false) (false::rev))

/-- Physical reversal preserves the finite overflow flag. -/
theorem reverse_exec (v : Registers) (rev out : List Bool) :
    Executes (rev.length+1) (cfg (some .reverse) v [] rev out)
      (cfg (some .finish) (none,v.2) [] [] (rev.reverse++out)) := by
  induction rev generalizing v out with
  | nil =>
    apply Executes.next ?_ (Executes.refl _)
    simp [SemiprimeD1StackIncrement.step,program,cfg,contents,TM2.step,TM2.stepAux]
  | cons b bs ih =>
    have hs : step (cfg (some .reverse) v [] (b::bs) out)=
        some (cfg (some .reverse) (some b,v.2) [] bs (b::out)) := by
      simp [SemiprimeD1StackIncrement.step,program,cfg,contents,TM2.step,TM2.stepAux]
    simpa [List.reverse_cons,List.append_assoc] using Executes.next hs (ih (some b,v.2) (b::out))

/-- Wrapped width is EXACTLY the original width, including zero. -/
theorem wrapped_length (xs : List Bool) : (wrapped xs).length=xs.length := by
  induction xs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [wrapped,ih]

/-- Overflow is precisely the all-one condition, vacuously true at width zero. -/
theorem overflow_iff (xs : List Bool) : overflow xs=true ↔ ∀b∈xs,b=true := by
  induction xs with
  | nil => simp [overflow]
  | cons b bs ih => cases b <;> simp [overflow,ih]

/-- The emitted overflow agrees with the literal all-true Boolean test. -/
theorem overflow_eq_all (xs : List Bool) : overflow xs=xs.all id := by
  induction xs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [overflow,ih]

/-- Exact integer balance proves both wraparound and the emitted carry. -/
theorem value_balance (xs : List Bool) :
    bitValue (wrapped xs)+2^xs.length*bitNat (overflow xs)=bitValue xs+1 := by
  induction xs with
  | nil => simp [wrapped,overflow,bitValue,bitNat]
  | cons b bs ih =>
    cases b <;> cases ho : overflow bs <;>
      simp [wrapped,overflow,bitValue,bitNat,ho,pow_succ] at * <;> omega

/-- Mathematical modular meaning of the actual fixed-width bytes. -/
theorem wrapped_value (xs : List Bool) : bitValue (wrapped xs)=(bitValue xs+1)%2^xs.length := by
  have hb := value_balance xs
  have hw := SemiprimeBitArithmetic.bitValue_lt_width (wrapped xs)
  rw [wrapped_length] at hw
  rw [←hb,Nat.add_mod]
  simp [Nat.mod_eq_of_lt hw]

/-- Entire literal output, exact length and transition count; old output tail retained. -/
theorem increment_exec (xs out : List Bool) :
    Executes (2*xs.length+3) (cfg (some .carry) (none,false) xs [] out)
      (cfg none (none,overflow xs) [] [] (overflow xs::(wrapped xs++out))) := by
  have hc := carry_exec (none,false) xs [] out
  have hr := reverse_exec (none,overflow xs) ((wrapped xs).reverse++[]) out
  have hf : step (cfg (some .finish) (none,overflow xs) [] [] (wrapped xs++out))=
      some (cfg none (none,overflow xs) [] [] (overflow xs::(wrapped xs++out))) := by
    simp [SemiprimeD1StackIncrement.step,program,cfg,contents,TM2.step,TM2.stepAux]
  have h := hc.trans (hr.trans (by simpa using Executes.next hf (Executes.refl _)))
  simp only [List.append_nil,List.length_reverse,wrapped_length] at h
  convert h using 1
  omega

/-- Genuine actual transition-time certificate, not an annotated scalar clock. -/
def incrementInTime (xs out : List Bool) :
    StateTransition.EvalsToInTime machine.step (cfg (some .carry) (none,false) xs [] out)
      (some (cfg none (none,overflow xs) [] [] (overflow xs::(wrapped xs++out)))) (2*xs.length+3) :=
  ⟨⟨_,(increment_exec xs out).iterates⟩,le_rfl⟩

/-- The official input initialization acquires only the actual input word. -/
theorem init_eq (xs : List Bool) : Turing.initList machine xs=
    cfg (some .carry) (none,false) xs [] [] := by
  unfold Turing.initList cfg
  dsimp only [machine]
  congr 1
  funext k
  cases k <;> rfl

/-- Actual official bundled-machine certificate from its one Boolean-word input. -/
def bundledInTime (xs : List Bool) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine xs)
      (some (cfg none (none,overflow xs) [] [] (overflow xs::wrapped xs))) (2*xs.length+3) := by
  rw [init_eq]
  simpa using incrementInTime xs []

/-- Every stack alphabet has exactly two physical symbols. -/
theorem alphabet_card (k : Stack) : Fintype.card (Alphabet k)=2 := by
  change Fintype.card Bool=2
  decide

/-- Finite registers have only six settings, independent of every width. -/
theorem registers_card : Fintype.card Registers=6 := by decide

/-- Static elementary stack/control syntax depth. -/
def instructionDepth : Stmt Alphabet PC Registers → ℕ
  | .push _ _ q => 1+instructionDepth q
  | .peek _ _ q => 1+instructionDepth q
  | .pop _ _ q => 1+instructionDepth q
  | .load _ q => 1+instructionDepth q
  | .branch _ q r => 1+max (instructionDepth q) (instructionDepth r)
  | .goto _ => 1
  | .halt => 1

/-- A transition contains at most five elementary stack/control syntax nodes. -/
theorem program_depth (pc : PC) : instructionDepth (program pc)≤5 := by
  cases pc <;> decide

/-- Every jump stays within the same fixed four-label catalogue. -/
theorem program_supports : TM2.Supports program Finset.univ := by
  constructor
  · simp
  · intro pc hpc
    cases pc <;> simp [program,TM2.SupportsStmt]

/-- Total unbounded data in all actual Boolean stacks. -/
def cells (c : Cfg Alphabet PC Registers) : ℕ :=
  (c.stk Stack.input).length+(c.stk Stack.scratch).length+(c.stk Stack.output).length

/-- Every actual instruction creates at most one Boolean cell. -/
theorem step_cells (c d : Cfg Alphabet PC Registers) (h : step c=some d) :
    cells d≤cells c+1 := by
  rcases c with ⟨pc,⟨flag,carry⟩,store⟩
  cases pc with
  | none => simp [SemiprimeD1StackIncrement.step,TM2.step] at h
  | some pc =>
    cases pc <;>
      simp [SemiprimeD1StackIncrement.step,TM2.step,program,TM2.stepAux,
        Bool.cond_eq_ite,Function.update] at h <;>
      (try split_ifs at h) <;> cases h <;> simp [cells,Function.update] <;> omega

/-- All actual intermediate paths have derived storage, not only final output. -/
theorem path_cells {n : ℕ} {c d : Cfg Alphabet PC Registers} (h : Executes n c d) :
    cells d≤cells c+n := by
  induction h with
  | refl => omega
  | @next n c e d hs ht ih =>
    have hh := step_cells c e hs
    omega

/-- Linear all-prefix Boolean storage, including physical copy/reversal scratch. -/
theorem increment_cells (xs out : List Bool) (n : ℕ) (c : Cfg Alphabet PC Registers)
    (h : Executes n (cfg (some .carry) (none,false) xs [] out) c)
    (hn : n≤2*xs.length+3) : cells c≤3*xs.length+out.length+3 := by
  have hh := path_cells h
  simp only [cells,cfg,contents,List.length_nil,Nat.add_zero] at hh
  unfold cells
  omega

end RiemannGaussian.SemiprimeD1StackIncrement
