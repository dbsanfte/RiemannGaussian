/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1VertexCatalogueEncoding
import RiemannGaussian.SemiprimeD1StackDigitCountBounds
import RiemannGaussian.SemiprimeD1StackValidationLink

/-! # Fixed original-input complete vertex-catalogue controller
Source limits, digit count and every constructor tag are physically acquired.
The one instruction table includes the full public parameter/digit supplier,
actual cache counter and concrete four-axis Cartesian procedures. No graph,
vertex/port list, desired count or runtime body evaluator is an input.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 4096
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVertexCatalogue
namespace Root
export SemiprimeD1BinaryPublicAcquisition (Stack Label program mainLabel digitStack axesStack input initial)
end Root
namespace Count
export SemiprimeD1StackDigitCount (Stack Label program)
end Count
namespace Kernel
export SemiprimeD1StackCartesian4 (Stack Label program limitStack indexStack aux)
end Kernel
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace LinkB
export SemiprimeD1StackMultiplierLink (instruction DataRel data_unique Rel run_rel)
end LinkB
namespace LinkC
export SemiprimeD1StackValidationLink (instruction Rel run_rel)
end LinkC
open SemiprimeD1VertexCatalogueModes (Mode Role roles previous)

/-- Fixed28 public roles plus five derived caches,12 engine roles, seven count roles and scratch. -/
abbrev Stack := Root.Stack⊕(Fin 5⊕(Kernel.Stack⊕(Count.Stack⊕Unit)))
/-- Cached computational equality for the fixed composite stack alphabet. -/
instance : DecidableEq Stack := inferInstanceAs (DecidableEq
  (Root.Stack⊕(Fin 5⊕(Kernel.Stack⊕(Count.Stack⊕Unit)))))
/-- Cached fixed data-role enumeration, independent of N. -/
instance : Fintype Stack := inferInstanceAs (Fintype
  (Root.Stack⊕(Fin 5⊕(Kernel.Stack⊕(Count.Stack⊕Unit)))))
/-- Original acquired public payload inclusion. -/
def rootStack (k:Root.Stack) : Stack := .inl k
/-- Derived physical one/two/three/digitsPred/radiusSucc caches. -/
def cacheStack (k:Fin 5) : Stack := .inr (.inl k)
/-- Actual Cartesian engine data inclusion. -/
def kernelStack (k:Kernel.Stack) : Stack := .inr (.inr (.inl k))
/-- The original immutable acquired digit cache. -/
def originalBank : Root.Stack := SemiprimeD1StackDigitCountBounds.bankRole
/-- Cache counting aliases the ALREADY acquired bank, not a copied/advised value. -/
def countStack : Count.Stack→Stack
  | .bank => rootStack originalBank
  | k => .inr (.inr (.inr (.inl k)))
/-- Physical outer-copy scratch, separate from every source/destination. -/
def scratchStack : Stack := .inr (.inr (.inr (.inr ())))
/-- Actual retained original binary input. -/
def originalInput : Stack := rootStack (Root.digitStack (SemiprimeD1BinaryDigitAcquisition.metaStack .input))
/-- Actual acquired original transform radius. -/
def originalRadius : Stack := rootStack (Root.digitStack (SemiprimeD1BinaryDigitAcquisition.metaStack .radius))
/-- Fixed role selection reads actual cached parameter words, never decoded native dimensions. -/
def roleStack : Role→Stack
  | .one => cacheStack 0 | .two => cacheStack 1 | .three => cacheStack 2
  | .radius => originalRadius
  | .firstAxis => rootStack (Root.axesStack (.inr 0))
  | .secondAxis => rootStack (Root.axesStack (.inr 1))
  | .digits => countStack .count
  | .digitsPred => cacheStack 3
  | .radiusSucc => cacheStack 4

/-- All outer copies are statically selected finite procedures. -/
inductive CopyKind where
  | radiusSucc | digitsPred | limit (mode:Mode) (axis:Fin 4)
  deriving DecidableEq,Repr
instance : Fintype CopyKind where
  elems:={.radiusSucc,.digitsPred}∪Finset.univ.image (fun x:Mode×Fin 4=>CopyKind.limit x.1 x.2)
  complete:=by intro kind;cases kind <;> simp
/-- Actual preserved source word of each copy. -/
def copyInput : CopyKind→Stack
  | .radiusSucc => originalRadius
  | .digitsPred => countStack .count
  | .limit mode axis => roleStack (roles mode axis)
/-- Actual destination cache or physical engine limit. -/
def copyOutput : CopyKind→Stack
  | .radiusSucc => cacheStack 4
  | .digitsPred => cacheStack 3
  | .limit _ axis => kernelStack (Kernel.limitStack axis)
/-- Literal included Copy operands. -/
def copyStack (kind:CopyKind) (i:Fin 3) : Stack :=
  if i=0 then copyInput kind else if i=1 then copyOutput kind else scratchStack

/-- Fixed frontend states; all dynamic dimensions live only in Boolean stacks. -/
inductive Control where
  | main | acquireRoot | acquireCount | copyRadiusSucc | incRadiusSucc | copyDigitsPred | popDigitsPred | halt
  | constants (pc:Fin 6) | initTag (pc:Fin 18)
  | clearLimit (mode:Mode) (axis:Fin 4) | copyLimit (mode:Mode) (axis:Fin 4)
  | runMode (mode:Mode) | afterMode (mode:Mode)
  deriving DecidableEq,Repr
instance : Fintype Control where
  elems:={.main,.acquireRoot,.acquireCount,.copyRadiusSucc,.incRadiusSucc,.copyDigitsPred,.popDigitsPred,.halt}∪
    Finset.univ.image Control.constants∪Finset.univ.image Control.initTag∪
    Finset.univ.image (fun x:Mode×Fin 4=>Control.clearLimit x.1 x.2)∪
    Finset.univ.image (fun x:Mode×Fin 4=>Control.copyLimit x.1 x.2)∪
    Finset.univ.image Control.runMode∪Finset.univ.image Control.afterMode
  complete:=by intro pc;cases pc <;> simp
/-- One finite label type fixed before every original N. -/
abbrev Label := Control⊕(Root.Label⊕(Count.Label⊕(Kernel.Label⊕(CopyKind×Fin 9))))
/-- Cached finite control catalogue, generated before every input. -/
instance : Fintype Label := inferInstanceAs (Fintype
  (Control⊕(Root.Label⊕(Count.Label⊕(Kernel.Label⊕(CopyKind×Fin 9))))))
/-- Actual public-source label map. -/
def rootLabel (pc:Root.Label) : Label := .inr (.inl pc)
/-- Actual digit-counter label map. -/
def countLabel (pc:Count.Label) : Label := .inr (.inr (.inl pc))
/-- Actual closed Cartesian-engine label map. -/
def kernelLabel (pc:Kernel.Label) : Label := .inr (.inr (.inr (.inl pc)))
/-- Actual outer-copy label map. -/
def copyLabel (kind:CopyKind) (pc:Fin 9) : Label := .inr (.inr (.inr (.inr (kind,pc))))
/-- Static continuation between the four copied limits. -/
def afterLimit (mode:Mode) (axis:Fin 4) : Label :=
  if h:axis.val<3 then .inl (.clearLimit mode ⟨axis.val+1,by omega⟩) else .inl (.runMode mode)

/-- ONE fixed literal source table; empty input takes the explicit early branch. -/
def program : Label→C.Instruction Stack Label
  | .inr (.inl pc) => LinkC.instruction rootStack rootLabel (Root.program pc)
  | .inr (.inr (.inl pc)) => LinkC.instruction countStack countLabel (Count.program pc)
  | .inr (.inr (.inr (.inl pc))) => LinkC.instruction kernelStack kernelLabel (Kernel.program pc)
  | .inr (.inr (.inr (.inr (kind,pc)))) => LinkB.instruction (copyStack kind) (copyLabel kind) (SemiprimeD1StackCopy.code pc)
  | .inl .main => .base (.peek originalInput (.inl .halt) (.inl .acquireRoot) (.inl .acquireRoot))
  | .inl .acquireRoot => .call (rootLabel (Root.mainLabel .start)) (.inl .acquireCount)
  | .inl .acquireCount => .call (countLabel (.inl .main)) (.inl .copyRadiusSucc)
  | .inl .copyRadiusSucc => .call (copyLabel .radiusSucc 0) (.inl .incRadiusSucc)
  | .inl .incRadiusSucc => .base (.push (cacheStack 4) true (.inl .copyDigitsPred))
  | .inl .copyDigitsPred => .call (copyLabel .digitsPred 0) (.inl .popDigitsPred)
  | .inl .popDigitsPred => .base (.pop (cacheStack 3) (.inl (.constants 0)) (.inl (.constants 0)) (.inl (.constants 0)))
  | .inl (.constants pc) =>
      if pc=0 then .base (.push (cacheStack 0) true (.inl (.constants 1)))
      else if pc=1 then .base (.push (cacheStack 1) true (.inl (.constants 2)))
      else if pc=2 then .base (.push (cacheStack 1) true (.inl (.constants 3)))
      else if pc=3 then .base (.push (cacheStack 2) true (.inl (.constants 4)))
      else if pc=4 then .base (.push (cacheStack 2) true (.inl (.constants 5)))
      else .base (.push (cacheStack 2) true (.inl (.initTag 0)))
  | .inl (.initTag pc) =>
      if h:pc.val<17 then .base (.push (kernelStack (Kernel.aux 3)) true (.inl (.initTag ⟨pc.val+1,by omega⟩)))
      else .base (.jump (.inl (.clearLimit .flagOr 0)))
  | .inl (.clearLimit mode axis) => .base (.pop (kernelStack (Kernel.limitStack axis))
      (.inl (.copyLimit mode axis)) (.inl (.clearLimit mode axis)) (.inl (.clearLimit mode axis)))
  | .inl (.copyLimit mode axis) => .call (copyLabel (.limit mode axis) 0) (afterLimit mode axis)
  | .inl (.runMode mode) => .call (kernelLabel (.inl .main)) (.inl (.afterMode mode))
  | .inl (.afterMode mode) =>
      if mode=.input then .base (.jump (.inl .halt)) else
        .base (.pop (kernelStack (Kernel.aux 3)) (.inl (.clearLimit (previous mode) 0))
          (.inl (.clearLimit (previous mode) 0)) (.inl (.clearLimit (previous mode) 0)))
  | .inl .halt => .base .halt

/-- Original-input-only initial physical store. -/
def input (bits:List Bool) : Stack→List Bool := Sum.elim (Root.input bits) (fun _=>[])
/-- Actual no-continuation original-input state. -/
def initial (bits:List Bool) : C.State Stack Label := ⟨some (.inl .main),none,none,input bits,[]⟩
/-- ONE fixed finite full catalogue machine, before every binary input. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine originalInput (kernelStack (Kernel.aux 2)) (.inl .main) program
/-- Every actual alphabet is finite, including the fixed global return-tag alphabet. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite originalInput (kernelStack (Kernel.aux 2)) (.inl .main) program
/-- The global finite data bank has53 Boolean stacks independent of N. -/
theorem stack_card : Fintype.card Stack=53 := by decide
end RiemannGaussian.SemiprimeD1StackVertexCatalogue
