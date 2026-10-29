/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWidthCircuit
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Literal original-dimension recovery template source
Only acquired unary a/M exist initially. Actual a-driven doubling creates unary
N=2^(a+1). The fixed64-gate wiring then uses real preserving copies and actual
unary products; it contains no polynomial evaluator callback or supplied value.
Final real pops/pushes emit one false template cell per acquired width marker.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWidth
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace W
export SemiprimeD1StackRecoveryWidthCircuit (Gate Literal Source Op node left right Earlier literalValue literalGate)
end W
namespace P
export SemiprimeD1StackUnaryProduct (Stack Label code entry contents)
end P
/-- Original metadata, physically acquired grid count, and all actual loops/output scratch. -/
inductive Aux where | a | m | grid | todo | multiplier | productScratch | copyScratch | output deriving DecidableEq,Repr
/-- Literal complete eight-word source/work inventory. -/
instance :Fintype Aux:=Fintype.ofList [.a,.m,.grid,.todo,.multiplier,.productScratch,.copyScratch,.output]
  (by intro k;cases k <;> simp)
/-- Every one of64 fixed arithmetic registers and eight actual metadata/work words is allocated. -/
abbrev Stack:=W.Gate⊕Aux
/-- Literal static gate-result address. -/
def reg :W.Gate→Stack:=Sum.inl
/-- Literal original/cache/work/output address. -/
def aux :Aux→Stack:=Sum.inr
/-- All wires are fixed physical addresses, independent of every acquired counter value. -/
def sourceStack :W.Source→Stack
  | .a=>aux .a | .m=>aux .m | .n=>aux .grid | .reg g=>reg g
/-- Product mode is a compile-time gate property, never an input predicate. -/
def isProduct (g:W.Gate) :Bool:=match W.node g with | .mul _ _=>true | _=>false
/-- Two setup routes and two actual copy sites per fixed gate. -/
inductive Copy where | acquireA | double | left (gate:W.Gate) | right (gate:W.Gate) deriving DecidableEq,Fintype,Repr
/-- Every source is an acquired original/cache/earlier register, never a supplied intermediate. -/
def copySource :Copy→Stack
  | .acquireA=>aux .a | .double=>aux .grid | .left g=>sourceStack (W.left g) | .right g=>sourceStack (W.right g)
/-- Product multiplier is consumed; additions append actual source bytes into the fresh actual gate. -/
def copyTarget :Copy→Stack
  | .acquireA=>aux .todo | .double=>aux .multiplier
  | .left g=>if isProduct g then aux .multiplier else reg g | .right g=>reg g
/-- Actual preserving-copy inclusion always has three distinct physical operands. -/
def copyStack (what:Copy) (k:Fin 3) :Stack:=if k=0 then copySource what else if k=1 then copyTarget what else aux .copyScratch
/-- Real UnaryProduct4 directly aliases its retained multiplicand to the actual earlier right wire. -/
def productStack (g:W.Gate) :P.Stack→Stack
  | .multiplier=>aux .multiplier | .multiplicand=>sourceStack (W.right g)
  | .scratch=>aux .productScratch | .product=>reg g
/-- Runtime has only fixed finite syntax positions, Boolean heads and real return labels. -/
inductive Label where
  | start | seedOne | seedTwo | power | doubleCopy | doubleMove | doublePush
  | gate (g:W.Gate) | constant (literal:W.Literal) (position:Fin 20) | addRight (g:W.Gate) | multiply (g:W.Gate)
  | fill | write | clean (g:W.Gate) | done
  | copier (what:Copy) (pc:Fin 9) | product (g:W.Gate) (pc:P.Label)
  deriving Fintype
/-- Static next instruction location, fixed before all input words. -/
def nextGate (g:W.Gate) :Label:=if h:g.val+1<64 then .gate ⟨g.val+1,h⟩ else .fill
/-- Every one of64 actual registers is physically EOF-drained before the source returns. -/
def nextClean (g:W.Gate) :Label:=if h:g.val+1<64 then .clean ⟨g.val+1,h⟩ else .done
/-- One parameterless actual source for all acquired unary dimensions, including a=0 and M=0. -/
def program :Label→C.Instruction Stack Label
  | .start=>.call (.copier .acquireA 0) .seedOne
  | .seedOne=>.base (.push (aux .grid) true .seedTwo)
  | .seedTwo=>.base (.push (aux .grid) true .power)
  | .power=>.base (.pop (aux .todo) (.gate 0) .doubleCopy .doubleCopy)
  | .doubleCopy=>.call (.copier .double 0) .doubleMove
  | .doubleMove=>.base (.pop (aux .multiplier) .power .doublePush .doublePush)
  | .doublePush=>.base (.push (aux .grid) true .doubleMove)
  | .gate g=>match W.node g with
    | .literal k=>.base (.jump (.constant k 0))
    | .add _ _=>.call (.copier (.left g) 0) (.addRight g)
    | .mul _ _=>.call (.copier (.left g) 0) (.multiply g)
  | .constant k i=>.base (.push (reg (W.literalGate k)) true
      (if h:i.val+1<W.literalValue k then .constant k ⟨i.val+1,by have hmax:=(SemiprimeD1StackRecoveryWidthCircuit.literal_bounds k).2;omega⟩
       else nextGate (W.literalGate k)))
  | .addRight g=>.call (.copier (.right g) 0) (nextGate g)
  | .multiply g=>.call (.product g P.entry) (nextGate g)
  | .fill=>.base (.pop (reg 63) (.clean 0) .write .write)
  | .write=>.base (.push (aux .output) false .fill)
  | .clean g=>.base (.pop (reg g) (nextClean g) (.clean g) (.clean g))
  | .done=>.base .halt
  | .copier what pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack what) (Label.copier what) (SemiprimeD1StackCopy.code pc)
  | .product g pc=>SemiprimeD1StackMultiplierLink.instruction (productStack g) (Label.product g) (P.code pc)
/-- Exactly the two already acquired original unary metadata words are initially populated. -/
def input (a m:List Bool) :Stack→List Bool:=Sum.elim (fun _=>[]) (fun k=>if k=.a then a else if k=.m then m else [])
/-- Honest two-word source front door; no grid size, width, intermediate or template is supplied. -/
def initial (a m:List Bool) :C.State Stack Label:=⟨some .start,none,none,input a m,[]⟩
/-- Genuine fixed finite72-role machine returning the physically emitted false template. -/
def machine :Turing.FinTM2:=SemiprimeD1StackCalls.machine (aux .a) (aux .output) .start program
/-- Actual original/cache sources are distinct from the three actual disposable work roles. -/
theorem source_work (s:W.Source) :sourceStack s≠aux .multiplier ∧ sourceStack s≠aux .productScratch ∧ sourceStack s≠aux .copyScratch:=by
  cases s <;> simp [sourceStack,aux,reg]
/-- Topological wiring makes every actual source register distinct from the actual fresh destination. -/
theorem source_reg (g:W.Gate) (s:W.Source) (hs:W.Earlier g s) :sourceStack s≠reg g:=by
  cases s with
  | a=>simp [sourceStack,reg,aux]
  | m=>simp [sourceStack,reg,aux]
  | n=>simp [sourceStack,reg,aux]
  | reg j=>
    intro h
    have he:j=g:=Sum.inl.inj h
    subst j
    exact (Nat.lt_irrefl _ hs)
/-- Every copy source is physically disjoint from its actual target. -/
theorem copy_separate (what:Copy) :copySource what≠copyTarget what:=by
  cases what with
  | acquireA=>decide
  | double=>decide
  | left g=>
    by_cases hp:isProduct g=true
    · simpa only [copySource,copyTarget,hp,ite_true] using (source_work (W.left g)).1
    · simpa only [copySource,copyTarget,ite_eq_right hp] using
        source_reg g (W.left g) (SemiprimeD1StackRecoveryWidthCircuit.left_earlier g)
  | right g=>exact source_reg g (W.right g) (SemiprimeD1StackRecoveryWidthCircuit.right_earlier g)
/-- Every preserving copy has genuinely distinct source/target/restoration roles. -/
theorem copy_injective (what:Copy) :Function.Injective (copyStack what):=by
  have hs:copySource what≠aux .copyScratch:=by
    cases what with
    | acquireA=>decide
    | double=>decide
    | left g=>exact (source_work (W.left g)).2.2
    | right g=>exact (source_work (W.right g)).2.2
  have ht:copyTarget what≠aux .copyScratch:=by
    cases what with
    | acquireA=>decide
    | double=>decide
    | left g=>by_cases hp:isProduct g=true <;> simp [copyTarget,hp,aux,reg]
    | right g=>simp [copyTarget,reg,aux]
  have hd:=copy_separate what
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [copyStack]
/-- Direct retained right-wire aliasing never collides with multiplier, scratch or fresh output. -/
theorem product_injective (g:W.Gate) :Function.Injective (productStack g):=by
  have hwork:=source_work (W.right g)
  have hreg:=source_reg g (W.right g) (SemiprimeD1StackRecoveryWidthCircuit.right_earlier g)
  intro i j h
  cases i <;> cases j <;> simp_all [productStack,aux,reg]
/-- All64 arithmetic registers and eight physical original/cache/work/output words are included. -/
theorem stack_card :Fintype.card Stack=72:=by decide
/-- Runtime sigma is fixed finite before all a/M input values. -/
theorem control_finite :Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- All actual Boolean roles and finite-label real-return alphabets are fixed finite. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k):=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRecoveryWidth
