/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BinaryBootstrap
import RiemannGaussian.SemiprimeD1StackAdderExecution
import RiemannGaussian.SemiprimeD1StackProcedureTrace

/-! # Original-binary acquisition of the packed root precision and base
Only the physical input N is present initially. Actual width acquisition,
one real add-two per width marker and literal shifts construct binary 2ell,
binary B=2^ell and a 2ell-cell width template. N remains binary throughout.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPackedRootMetadata
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace B
export SemiprimeD1BinaryBootstrap (Stack Label code payload done seenOne)
end B
namespace A
export SemiprimeD1StackAdder (Stack Label code store)
end A
/-- Five actual output, reader and copy-restoration words. -/
inductive Aux where | reader | copyScratch | precision | base | template
  deriving DecidableEq,Repr
/-- Literal auxiliary enumeration, independent of all operands. -/
instance auxFintype : Fintype Aux := Fintype.ofList [.reader,.copyScratch,.precision,.base,.template] (by intro k;cases k <;> simp)
/-- All13 allocated Boolean words; the displaced adder-left shadow is counted. -/
abbrev Stack := B.Stack⊕(A.Stack⊕Aux)
/-- All four actual bootstrap words are retained. -/
def boot (k : B.Stack) : Stack := .inl k
/-- Full allocated adder bank, including its unused left shadow. -/
def adderAllocation (k : A.Stack) : Stack := .inr (.inl k)
/-- Actual helper/output tape roles, fixed before N. -/
def aux (k : Aux) : Stack := .inr (.inr k)
/-- The running binary precision is consumed directly by the real adder. -/
def adder : A.Stack→Stack | .left => aux .precision | k => adderAllocation k
/-- Exactly two real preserving copy sites. -/
inductive Copy where | width | sum deriving DecidableEq
/-- Literal two-site enumeration. -/
instance copyFintype : Fintype Copy := Fintype.ofList [.width,.sum] (by intro k;cases k <;> simp)
/-- Actual source, destination and restoring scratch for both real copies. -/
def copyStack (site : Copy) (k : Fin 3) : Stack :=
  if k=0 then match site with | .width => boot .width | .sum => adder .output
  else if k=1 then match site with | .width => aux .reader | .sum => aux .precision
  else aux .copyScratch
/-- Literal finite control; no length, counter value, result or clock operands. -/
inductive Control where
  | start | seedBase | copyWidth | read | growBase | growFirst | growSecond
  | seedHigh | seedLow | add | copySum | clearSum | done
  deriving DecidableEq
/-- Literal thirteen-stage control enumeration. -/
instance controlFintype : Fintype Control := Fintype.ofList [.start,.seedBase,.copyWidth,.read,.growBase,.growFirst,.growSecond,.seedHigh,.seedLow,.add,.copySum,.clearSum,.done] (by intro k;cases k <;> simp)
/-- All return and included-bytecode labels are fixed before every input. -/
inductive Label where
  | local (pc : Control) | boot (pc : B.Label) | add (pc : A.Label)
  | copy (site : Copy) (pc : Fin 9)
  deriving DecidableEq
/-- Computable finite label decomposition, containing only fixed component labels. -/
def labelEquiv : (Control⊕(B.Label⊕(A.Label⊕(Copy×Fin 9)))) ≃ Label where
  toFun
    | .inl pc => .local pc
    | .inr (.inl pc) => .boot pc
    | .inr (.inr (.inl pc)) => .add pc
    | .inr (.inr (.inr (site,pc))) => .copy site pc
  invFun
    | .local pc => .inl pc
    | .boot pc => .inr (.inl pc)
    | .add pc => .inr (.inr (.inl pc))
    | .copy site pc => .inr (.inr (.inr (site,pc)))
  left_inv x := by rcases x with x|x|x|x <;> rfl
  right_inv x := by cases x <;> rfl
/-- The full fixed label inventory is computably finite. -/
instance labelFintype : Fintype Label := Fintype.ofEquiv _ labelEquiv
local notation "ctl" => Label.local
/-- One fixed literal source, including both actual arithmetic and copy returns. -/
def program : Label→C.Instruction Stack Label
  | .local .start => .call (.boot (.scan,false)) (ctl .seedBase)
  | .local .seedBase => .base (.push (aux .base) true (ctl .copyWidth))
  | .local .copyWidth => .call (.copy .width 0) (ctl .read)
  | .local .read => .base (.pop (aux .reader) (ctl .done) (ctl .growBase) (ctl .growBase))
  | .local .growBase => .base (.push (aux .base) false (ctl .growFirst))
  | .local .growFirst => .base (.push (aux .template) false (ctl .growSecond))
  | .local .growSecond => .base (.push (aux .template) false (ctl .seedHigh))
  | .local .seedHigh => .base (.push (adder .right) true (ctl .seedLow))
  | .local .seedLow => .base (.push (adder .right) false (ctl .add))
  | .local .add => .call (.add (.start false)) (ctl .copySum)
  | .local .copySum => .call (.copy .sum 0) (ctl .clearSum)
  | .local .clearSum => .base (.pop (adder .output) (ctl .read) (ctl .clearSum) (ctl .clearSum))
  | .local .done => .base .halt
  | .boot pc => SemiprimeD1StackMultiplierLink.instruction boot Label.boot (B.code pc)
  | .add pc => SemiprimeD1StackMultiplierLink.instruction adder Label.add (A.code pc)
  | .copy site pc => SemiprimeD1StackMultiplierLink.instruction (copyStack site) (Label.copy site) (SemiprimeD1StackCopy.code pc)
/-- Exact entire allocated payload, including every retained and shadow word. -/
def bank (b : B.Stack→List Bool) (a : A.Stack→List Bool) (u : Aux→List Bool) : Stack→List Bool :=
  Sum.elim b (Sum.elim a u)
/-- Original binary N is the sole initial nonempty word. -/
def input (bits : List Bool) : Stack→List Bool := bank (B.payload bits [] [] []) (fun _ => []) (fun _ => [])
/-- Actual front door before the physical width acquisition. -/
def initial (bits : List Bool) : C.State Stack Label := ⟨some (ctl .start),none,none,input bits,[]⟩
/-- Genuine original-input finite machine, with binary precision as output. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (boot .input) (aux .precision) (ctl .start) program
/-- Actual code includes all13 allocations, including the unused adder shadow. -/
theorem stack_card : Fintype.card Stack=13 := by decide
/-- Bootstrap roles never alias. -/
theorem boot_injective : Function.Injective boot := Sum.inl_injective
/-- Actual adder operands are distinct despite the explicit unused shadow. -/
theorem adder_injective : Function.Injective adder := by intro a b h;cases a <;> cases b <;> simp_all [adder,aux,adderAllocation]
/-- Both copy sites have physically distinct source, destination and scratch. -/
theorem copy_injective (site : Copy) : Function.Injective (copyStack site) := by cases site <;> decide
/-- All data and actual return-cell alphabets are finite. -/
theorem alphabets_finite : ∀k,Finite (machine.Γ k) := SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
/-- Internal state contains only finite read flags and literal labels. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackPackedRootMetadata
