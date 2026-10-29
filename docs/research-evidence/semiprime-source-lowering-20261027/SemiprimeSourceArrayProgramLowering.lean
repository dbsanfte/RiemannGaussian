/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceArrayProgramIR
import RiemannGaussian.SemiprimeSourceProgramBits
import RiemannGaussian.SemiprimeEncodedRowSelection

/-! # Lowering stable source registers to actual Boolean operand addresses
New results are prepended by the physical interpreter. Compiler-stable IDs are
therefore translated at each instruction's actual allocation frontier. The
encoder executes the existing division/remainder digit loop; its generation
ledger is scalar/digit work, not yet a primitive-bit implementation of all
compiler metadata. The emitted program executes the existing Boolean machine.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace RiemannGaussian.SemiprimeSourceArrayProgramLowering
open SemiprimeRationalBits SemiprimeBitArithmetic SemiprimeEncodedRowSelection

/-- Initial registers retain their order; allocated registers are newest first. -/
def address (initial next id : ℕ) : ℕ :=
  if id < initial then next-initial+id else next-1-id

/-- Every initialized stable register has a physical address inside the store. -/
theorem address_lt (initial next id : ℕ) (hi : initial ≤ next) (hid : id < next) :
    address initial next id  <  next := by
  unfold address
  split <;> omega

/-- A newly allocated register is at the front of the next physical store. -/
theorem address_new (initial next : ℕ) (hi : initial ≤ next) :
    address initial (next+1) next = 0 := by
  unfold address
  rw [ite_eq_right (by omega : ¬next < initial)]
  omega

/-- Every previously allocated register shifts by one on an actual prepend. -/
theorem address_step (initial next id : ℕ) (hi : initial ≤ next) (hid : id < next) :
    address initial (next+1) id = address initial next id+1 := by
  unfold address
  split <;> omega

/-- Concrete list-register correspondence; the functional environment is proof-side. -/
def Represents (initial next : ℕ) (memory : List ℚ) (env : ℕ → ℚ) : Prop :=
  memory.length=next ∧ ∀ id < next,(memory[address initial next id]?).getD 0=env id

/-- Original input registers initialize the stable-to-physical correspondence. -/
theorem represents_initial (memory : List ℚ) :
    Represents memory.length memory.length memory (fun id => (memory[id]?).getD 0) := by
  refine ⟨rfl,?_⟩
  intro id hid
  simp only [address,ite_eq_left hid,Nat.sub_self,Nat.zero_add]

/-- A real prepend implements precisely the stable fresh-register update. -/
theorem represents_step (initial next : ℕ) (memory : List ℚ) (env : ℕ → ℚ)
    (out : ℚ) (hi : initial ≤ next) (hm : Represents initial next memory env) :
    Represents initial (next+1) (out::memory) (Function.update env next out) := by
  refine ⟨by simp only [List.length_cons,hm.1],?_⟩
  intro id hid
  by_cases he : id=next
  · subst id
    simp only [address_new initial next hi,List.getElem?_cons_zero,Option.getD_some,
      Function.update_same]
  · have hid' : id < next := by omega
    rw [address_step initial next id hi hid',List.getElem?_cons_succ,hm.2 id hid',
      Function.update_of_ne he]

/-- A generated physical instruction plus its executed digit/construction ledger. -/
structure InstructionRun where
  /-- Literal opcode and two physically generated Boolean addresses. -/
  instruction : SemiprimeSourceProgramBits.Instruction
  /-- Digit extraction and bounded scalar metadata operations. -/
  work : ℕ

/-- Generate both operand addresses at this exact prepend frontier. -/
def lowerInstruction (initial next B : ℕ) (i : SemiprimeSourceArrayProgramIR.Instruction) : InstructionRun :=
  let left := digits B (address initial next i.left)
  let right := digits B (address initial next i.right)
  ⟨⟨i.operation,left.bits,right.bits⟩,left.work+right.work+12⟩

/-- Both generated addresses retain exactly the requested physical width. -/
theorem lowerInstruction_width (initial next B : ℕ) (i : SemiprimeSourceArrayProgramIR.Instruction) :
    (lowerInstruction initial next B i).instruction.left.length=B ∧
      (lowerInstruction initial next B i).instruction.right.length=B := by
  exact ⟨digits_length _ _,digits_length _ _⟩

/-- Original initialized operands are preserved by the physical address encoding. -/
theorem lowerInstruction_value (initial next B : ℕ) (i : SemiprimeSourceArrayProgramIR.Instruction)
    (memory : List ℚ) (env : ℕ → ℚ) (hi : initial ≤ next)
    (hl : i.left < next) (hr : i.right < next) (hB : next ≤ 2^B)
    (hm : Represents initial next memory env) :
    (lowerInstruction initial next B i).instruction.value memory = i.value env := by
  have hleft := digits_value B (address initial next i.left)
    ((address_lt initial next i.left hi hl).trans_le hB)
  have hright := digits_value B (address initial next i.right)
    ((address_lt initial next i.right hi hr).trans_le hB)
  simp only [lowerInstruction,SemiprimeSourceProgramBits.Instruction.value,hleft,hright,hm.2 i.left hl,hm.2 i.right hr]
  rfl

/-- Complete emitted instruction bank with actual generation work. -/
structure ProgramRun where
  /-- Original generated program, traversed in allocation order. -/
  code : List SemiprimeSourceProgramBits.Instruction
  /-- All address digits, metadata and list cells. -/
  work : ℕ

/-- Lower every original scalar instruction once, incrementing its allocation frontier. -/
def lower (initial B : ℕ) : ℕ → List SemiprimeSourceArrayProgramIR.Instruction → ProgramRun
  | _,[] => ⟨[],1⟩
  | next,i::code =>
    let first := lowerInstruction initial next B i
    let rest := lower initial B (next+1) code
    ⟨first.instruction::rest.code,first.work+rest.work+3⟩

/-- Lowering neither duplicates nor drops a source scalar operation. -/
theorem lower_length (initial B next : ℕ) (code : List SemiprimeSourceArrayProgramIR.Instruction) :
    (lower initial B next code).code.length=code.length := by
  induction code generalizing next with
  | nil => rfl
  | cons i code ih => simp only [lower,List.length_cons,ih]

/-- Every emitted operand has a concrete uniformly bounded address payload. -/
theorem lower_width (initial B next : ℕ) (code : List SemiprimeSourceArrayProgramIR.Instruction) :
    ∀ i∈(lower initial B next code).code,i.left.length ≤ B ∧ i.right.length ≤ B := by
  induction code generalizing next with
  | nil => simp [lower]
  | cons i code ih =>
    intro j hj
    simp only [lower,List.mem_cons] at hj
    rcases hj with rfl | hj
    · exact ⟨(lowerInstruction_width initial next B i).1.le,
        (lowerInstruction_width initial next B i).2.le⟩
    · exact ih (next+1) j hj

/-- Exact code-generation ledger, explicitly distinct from whole-machine cost. -/
theorem lower_work (initial B next : ℕ) (code : List SemiprimeSourceArrayProgramIR.Instruction) :
    (lower initial B next code).work=code.length*(8*B+17)+1 := by
  induction code generalizing next with
  | nil => simp [lower]
  | cons i code ih =>
    simp only [lower,lowerInstruction,digits_work,ih,List.length_cons]
    ring

/-- The full physical instruction sequence preserves the exact source environment. -/
theorem lower_evaluate (initial B next : ℕ) (code : List SemiprimeSourceArrayProgramIR.Instruction)
    (memory : List ℚ) (env : ℕ → ℚ) (hi : initial ≤ next)
    (hc : SemiprimeSourceArrayProgramIR.WellFormed next code) (hB : next+code.length ≤ 2^B)
    (hm : Represents initial next memory env) :
    Represents initial (next+code.length)
      (SemiprimeSourceProgramBits.evaluate (lower initial B next code).code memory) (SemiprimeSourceArrayProgramIR.evaluate code next env) := by
  induction code generalizing next memory env with
  | nil => simpa only [lower,SemiprimeSourceProgramBits.evaluate,SemiprimeSourceArrayProgramIR.evaluate,List.length_nil,Nat.add_zero] using hm
  | cons i code ih =>
    have hv := lowerInstruction_value initial next B i memory env hi hc.1 hc.2.1
      (by simp only [List.length_cons] at hB;omega) hm
    have hs := represents_step initial next memory env (i.value env) hi hm
    have hh := ih (next+1) (i.value env::memory) (Function.update env next (i.value env))
      (by omega) hc.2.2 (by simp only [List.length_cons] at hB;omega) hs
    simpa only [lower,SemiprimeSourceProgramBits.evaluate,SemiprimeSourceArrayProgramIR.evaluate,hv,List.length_cons,Nat.add_assoc,
      Nat.add_comm 1] using hh

/-- Source scalar output fits, to be derived from original AST intermediate bounds. -/
def Safe (W : ℕ) : List SemiprimeSourceArrayProgramIR.Instruction → ℕ → (ℕ → ℚ) → Prop
  | [],_,_ => True
  | i::code,next,env => Fits (i.value env) W ∧
      Safe W code (next+1) (Function.update env next (i.value env))

/-- Source-derived fits compose over exactly the executed intermediate environment. -/
theorem safe_append (W : ℕ) (a b : List SemiprimeSourceArrayProgramIR.Instruction)
    (next : ℕ) (env : ℕ → ℚ) :
    Safe W (a++b) next env ↔ Safe W a next env ∧
      Safe W b (next+a.length) (SemiprimeSourceArrayProgramIR.evaluate a next env) := by
  induction a generalizing next env with
  | nil => simp [Safe,SemiprimeSourceArrayProgramIR.evaluate]
  | cons i a ih =>
    simp only [List.cons_append,Safe,ih,List.length_cons,SemiprimeSourceArrayProgramIR.evaluate]
    have h : next+1+a.length=next+(a.length+1) := by omega
    rw [h]
    tauto

/-- Every source-derived fit transfers to the actual lowered physical program. -/
theorem lower_safe (initial B next W : ℕ) (code : List SemiprimeSourceArrayProgramIR.Instruction)
    (memory : List ℚ) (env : ℕ → ℚ) (hi : initial ≤ next)
    (hc : SemiprimeSourceArrayProgramIR.WellFormed next code) (hB : next+code.length ≤ 2^B)
    (hm : Represents initial next memory env) (hs : Safe W code next env) :
    SemiprimeSourceProgramBits.Safe W (lower initial B next code).code memory := by
  induction code generalizing next memory env with
  | nil => trivial
  | cons i code ih =>
    have hv := lowerInstruction_value initial next B i memory env hi hc.1 hc.2.1
      (by simp only [List.length_cons] at hB;omega) hm
    simp only [lower,SemiprimeSourceProgramBits.Safe,hv]
    exact ⟨hs.1,ih (next+1) _ _ (by omega) hc.2.2
      (by simp only [List.length_cons] at hB;omega)
      (represents_step initial next memory env (i.value env) hi hm) hs.2⟩

/-- Linear address width suffices for every emitted ID under the actual total frontier. -/
theorem frontier_fits (next : ℕ) (code : List SemiprimeSourceArrayProgramIR.Instruction) :
    next+code.length ≤ 2^(next+code.length+1) := by
  have h := Nat.lt_two_pow_self (n:=next+code.length+1)
  omega

/-- The actual Boolean interpreter refines the generated scalar source program.
Input words and source-derived Safe remain explicit compiler/acquisition joins. -/
theorem run_refines (initial B next : ℕ) (code : List SemiprimeSourceArrayProgramIR.Instruction)
    (template : List Bool) (memory : List RationalWord) (env : ℕ → ℚ)
    (hi : initial ≤ next) (hc : SemiprimeSourceArrayProgramIR.WellFormed next code)
    (hB : next+code.length ≤ 2^B)
    (hm : Represents initial next (memory.map RationalWord.value) env)
    (hv : ∀ w∈memory,w.Valid) (hs : Safe template.length code next env) :
    Represents initial (next+code.length)
      ((SemiprimeSourceProgramBits.run template (lower initial B next code).code memory).memory.map
        RationalWord.value) (SemiprimeSourceArrayProgramIR.evaluate code next env) ∧
      ∀ w∈(SemiprimeSourceProgramBits.run template (lower initial B next code).code memory).memory,w.Valid := by
  have safe := lower_safe initial B next template.length code (memory.map RationalWord.value)
    env hi hc hB hm hs
  have hr := SemiprimeSourceProgramBits.run_correct template (lower initial B next code).code memory hv safe
  refine ⟨?_,hr.2⟩
  rw [hr.1]
  exact lower_evaluate initial B next code (memory.map RationalWord.value) env hi hc hB hm

/-- Original register/code/word dimensions bound every generated-address scan,
arithmetic circuit and persistent copy in the actual emitted instruction run. -/
theorem run_clock (initial B next : ℕ) (code : List SemiprimeSourceArrayProgramIR.Instruction)
    (template : List Bool) (memory : List RationalWord)
    (hW : 1 ≤ template.length) (hB : 1 ≤ B)
    (hm : ∀ w∈memory,Width w template.length) :
    (SemiprimeSourceProgramBits.run template (lower initial B next code).code memory).clock ≤
      code.length*(SemiprimeSourceProgramBits.stepBudget (memory.length+code.length) template.length B+3)+1 := by
  simpa only [lower_length] using SemiprimeSourceProgramBits.run_clock template
    (lower initial B next code).code memory B hW hB (lower_width initial B next code) hm

end RiemannGaussian.SemiprimeSourceArrayProgramLowering
