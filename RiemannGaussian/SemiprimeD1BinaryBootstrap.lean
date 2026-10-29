/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCopy
import RiemannGaussian.SemiprimeD1StackBytecodeBounds
import RiemannGaussian.SemiprimeSourceCompactBits
import RiemannGaussian.SemiprimeBitDivision

/-! # Actual original-binary-input bootstrap
One fixed finite machine retains the binary input, physically counts its bit
length in unary, and writes its zero/nonzero flag. Only the WIDTH is counted
in unary; the input value and every arithmetic payload remain binary.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1BinaryBootstrap
open SemiprimeD1StackBytecode
open SemiprimeD1StackCopy (run_add)
open SemiprimeBitArithmetic (bitValue bitNat)

/-- Four fixed Boolean stacks, before every input integer. -/
inductive Stack | input | reverse | width | nonzero deriving DecidableEq,Repr
/-- Fixed physical stack catalogue. -/
instance : Fintype Stack where
  elems:={.input,.reverse,.width,.nonzero}
  complete:=by intro k;cases k <;> simp

/-- Fixed instruction phases; the second label bit holds seen-one, never a counter. -/
inductive Phase | scan | saveFalse | saveTrue | count | reverse | restoreFalse | restoreTrue | finish | halt
  deriving DecidableEq,Repr
/-- Fixed phase catalogue. -/
instance : Fintype Phase where
  elems:={.scan,.saveFalse,.saveTrue,.count,.reverse,.restoreFalse,.restoreTrue,.finish,.halt}
  complete:=by intro k;cases k <;> simp

/-- Eighteen fixed finite labels, independent of every input length/value. -/
abbrev Label := Phase×Bool

/-- Complete literal bootstrap instruction table. -/
def code : Label→Instruction Stack Label
  | (.scan,seen) => .pop .input (.reverse,seen) (.saveFalse,seen) (.saveTrue,true)
  | (.saveFalse,seen) => .push .reverse false (.count,seen)
  | (.saveTrue,seen) => .push .reverse true (.count,seen)
  | (.count,seen) => .push .width true (.scan,seen)
  | (.reverse,seen) => .pop .reverse (.finish,seen) (.restoreFalse,seen) (.restoreTrue,seen)
  | (.restoreFalse,seen) => .push .input false (.reverse,seen)
  | (.restoreTrue,seen) => .push .input true (.reverse,seen)
  | (.finish,seen) => .push .nonzero seen (.halt,seen)
  | (.halt,_) => .halt

/-- Exact actual payload; lists occur only as stack contents. -/
def payload (input reverse width nonzero:List Bool) : Stack→List Bool
  | .input => input
  | .reverse => reverse
  | .width => width
  | .nonzero => nonzero

/-- Actual control/payload boundary with a finite seen-one bit. -/
def state (phase:Phase) (seen:Bool) (flag:Option Bool) (input reverse width nonzero:List Bool) :
    State Stack Label := ⟨some (phase,seen),flag,payload input reverse width nonzero⟩

/-- Boolean predicate used only to specify the physically acquired flag. -/
def seenOne (bits:List Bool) : Bool := bits.any id

/-- Actual final input/width/flag data with empty scratch. -/
def done (bits:List Bool) : State Stack Label :=
  ⟨none,none,payload bits [] (List.replicate bits.length true) [seenOne bits]⟩

/-- Three literal instructions read one bit, save it, and increment WIDTH by one marker. -/
theorem scan_bit (bit seen:Bool) (xs rev width nz:List Bool) (flag:Option Bool) :
    run code 3 (state .scan seen flag (bit::xs) rev width nz)=
      some (state .scan (seen||bit) (some bit) xs (bit::rev) (true::width) nz) := by
  cases seen <;> cases bit <;> simp [run,Function.iterate_succ_apply,step,execute,code,state,payload,choose,
    Function.update] <;> funext k <;> cases k <;> rfl

/-- Actual first pass acquires the width counter while preserving all input bits in scratch. -/
theorem scan_run (xs rev width nz:List Bool) (seen:Bool) (flag:Option Bool) :
    run code (3*xs.length+1) (state .scan seen flag xs rev width nz)=
      some (state .reverse (seen||seenOne xs) none [] (xs.reverse++rev)
        (List.replicate xs.length true++width) nz) := by
  induction xs generalizing seen flag rev width with
  | nil => simp [run,step,execute,code,state,payload,seenOne,choose]
  | cons bit xs ih =>
    rw [show 3*(bit::xs).length+1=3+(3*xs.length+1) by simp; omega,run_add,scan_bit]
    simp only [Option.bind_some]
    rw [ih]
    simp only [seenOne,List.any_cons,List.length_cons,List.reverse_cons,List.append_assoc,
      List.singleton_append,List.replicate_succ',Bool.or_assoc,id_eq]

/-- Two literal instructions restore one saved bit without changing the width counter. -/
theorem restore_bit (bit seen:Bool) (xs rev width nz:List Bool) (flag:Option Bool) :
    run code 2 (state .reverse seen flag xs (bit::rev) width nz)=
      some (state .reverse seen (some bit) (bit::xs) rev width nz) := by
  cases bit <;> simp [run,Function.iterate_succ_apply,step,execute,code,state,payload,choose,
    Function.update] <;> funext k <;> cases k <;> rfl

/-- Actual restoration, final flag push, and halt: no decoded input value is used. -/
theorem restore_run (rev xs width nz:List Bool) (seen:Bool) (flag:Option Bool) :
    run code (2*rev.length+3) (state .reverse seen flag xs rev width nz)=
      some (⟨none,none,payload (rev.reverse++xs) [] width (seen::nz)⟩:State Stack Label) := by
  induction rev generalizing xs flag with
  | nil =>
    simp [run,Function.iterate_succ_apply,step,execute,code,state,payload,choose,Function.update]
    funext k
    cases k <;> rfl
  | cons bit rev ih =>
    rw [show 2*(bit::rev).length+3=2+(2*rev.length+3) by simp; omega,run_add,restore_bit]
    simp only [Option.bind_some]
    rw [ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

/-- Complete executed original-word bootstrap, with input physically restored. -/
theorem bootstrap_run (bits:List Bool) :
    run code (5*bits.length+4) (state .scan false none bits [] [] [])=some (done bits) := by
  rw [show 5*bits.length+4=(3*bits.length+1)+(2*bits.reverse.length+3) by simp; omega,run_add,scan_run]
  simp only [List.append_nil,Bool.false_or,Option.bind_some]
  rw [restore_run,List.reverse_reverse,List.append_nil]
  rfl

/-- One fixed finite machine from the ORIGINAL binary input stack. -/
def machine : Turing.FinTM2 := SemiprimeD1StackBytecode.machine Stack.input Stack.width (.scan,false) code

/-- Its actual one-input initialization needs no prepared counter, predicate, graph or source metadata. -/
theorem initial_eq (bits:List Bool) :
    Turing.initList machine bits=configuration (state .scan false none bits [] [] []) := by
  dsimp only [Turing.initList,machine,SemiprimeD1StackBytecode.machine,configuration,state]
  congr 1
  funext k
  cases k <;> simp [payload]

/-- Genuine original-input machine execution, with explicit physically acquired width and zero flag. -/
def bootstrapInTime (bits:List Bool) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (configuration (done bits))) (5*bits.length+4) := by
  rw [initial_eq]
  apply evalsCorrect Stack.input Stack.width (.scan,false) code
  exact ⟨⟨5*bits.length+4,bootstrap_run bits⟩,le_refl _⟩

/-- The acquired Boolean is true exactly for positive represented input. -/
theorem seenOne_true (bits:List Bool) : seenOne bits=true ↔ 0<bitValue bits := by
  induction bits with
  | nil => simp [seenOne,bitValue]
  | cons bit bits ih =>
    cases bit <;> simp [seenOne,List.any_cons,bitValue,bitNat] at ih ⊢
    omega

/-- No high zeros gives the exact original Nat.bit_length, not merely the raw input length. -/
theorem canonical_width (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    bits.length=(bitValue bits).size := by
  apply Nat.le_antisymm
  · exact SemiprimeSourceCompactBits.compact_length_of_lt bits hc _ (Nat.lt_size_self _)
  · exact Nat.size_le.mpr (SemiprimeBitArithmetic.bitValue_lt_width bits)
/-- The physically acquired flag equals the existing original binary frontdoor zero test. -/
theorem seenOne_eq_nonzeroBits (bits:List Bool) :
    seenOne bits=(SemiprimeBitDivision.nonzeroBits bits).nonzero := by
  cases h:seenOne bits with
  | false =>
    cases hz:(SemiprimeBitDivision.nonzeroBits bits).nonzero with
    | false => rfl
    | true =>
      have hp:0<bitValue bits:=(SemiprimeBitDivision.nonzeroBits_correct bits).mp hz
      have he:seenOne bits=true:=(seenOne_true bits).mpr hp
      rw [h] at he
      cases he
  | true =>
    cases hz:(SemiprimeBitDivision.nonzeroBits bits).nonzero with
    | true => rfl
    | false =>
      have hp:0<bitValue bits:=(seenOne_true bits).mp h
      have he:(SemiprimeBitDivision.nonzeroBits bits).nonzero=true:=
        (SemiprimeBitDivision.nonzeroBits_correct bits).mpr hp
      rw [hz] at he
      cases he

/-- There are exactly four fixed stack names. -/
theorem stack_card : Fintype.card Stack=4 := by decide

/-- The finite seen-one register is encoded by exactly eighteen fixed labels. -/
theorem label_card : Fintype.card Label=18 := by decide

/-- Every actually reached original-input machine prefix has a linear total storage bound. -/
theorem machine_space (bits:List Bool) (fuel:ℕ) (cfg:machine.Cfg)
    (hr:(fun cfg=>cfg.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (cfg.stk Stack.input).length+(cfg.stk Stack.reverse).length+
      (cfg.stk Stack.width).length+(cfg.stk Stack.nonzero).length ≤21*(bits.length+1) := by
  rw [initial_eq] at hr
  let start:=state .scan false none bits [] [] []
  change (fun cfg=>cfg.bind machine.step)^[fuel] (some (configuration start))=some cfg at hr
  have he:=run_correct Stack.input Stack.width (.scan,false) code fuel start
  change (run code fuel start).map configuration=
    (fun cfg=>cfg.bind machine.step)^[fuel] (some (configuration start)) at he
  cases hc:run code fuel start with
  | none => rw [hc,hr] at he;cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg:configuration out=cfg:=Option.some.inj he
    rw [←hcfg]
    have hf:=SemiprimeD1StackBytecodeBounds.fuel_le_halt code start (done bits) out
      (5*bits.length+4) fuel (bootstrap_run bits) rfl hc
    have h0:=SemiprimeD1StackBytecodeBounds.run_length code fuel start out hc Stack.input
    have h1:=SemiprimeD1StackBytecodeBounds.run_length code fuel start out hc Stack.reverse
    have h2:=SemiprimeD1StackBytecodeBounds.run_length code fuel start out hc Stack.width
    have h3:=SemiprimeD1StackBytecodeBounds.run_length code fuel start out hc Stack.nonzero
    simp only [start,state,payload,List.length_nil,Nat.zero_add] at h0 h1 h2 h3
    change (out.store Stack.input).length+(out.store Stack.reverse).length+
      (out.store Stack.width).length+(out.store Stack.nonzero).length ≤ _
    omega
end RiemannGaussian.SemiprimeD1BinaryBootstrap
