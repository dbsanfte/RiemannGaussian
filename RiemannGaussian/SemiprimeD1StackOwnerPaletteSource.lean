/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OwnerTablePalette
import RiemannGaussian.SemiprimeD1StackBytecodeBounds
/-! # Literal finite-control acquisition of every original owner table
All twelve possibilities are fixed code. In the enclosing scanner, degree and
the two flags come from actual port/prefix reads; they are not advice inputs.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackOwnerPaletteSource
open SemiprimeD1OwnerTablePalette (bytes bytes_le)
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
/-- Twelve fixed alternatives, including isolated degree-zero owners. -/
abbrev Mode := Fin 3×Bool×Bool
/-- One real Boolean output role. -/
abbrev Stack := Unit
/-- At most23 literal pushes followed by halt for each fixed alternative. -/
abbrev Label := Mode×Fin 24
/-- Static finite code indexing ONLY fixed literal instruction bits. -/
def code (label : Label) : B.Instruction Stack Label :=
  if h : label.2.val<(bytes label.1.1 label.1.2.1 label.1.2.2).length then
    .push () (((bytes label.1.1 label.1.2.1 label.1.2.2).reverse[label.2.val]?).getD false)
      (label.1,⟨label.2.val+1,by have hb:=bytes_le label.1.1 label.1.2.1 label.1.2.2;omega⟩)
  else .halt
/-- Empty palette data, reached only after degree/flags have been computed. -/
def initial (mode : Mode) : B.State Stack Label := ⟨some (mode,0),none,fun _=>[]⟩
/-- Complete literal tree tape on the actual output role. -/
def done (mode : Mode) : B.State Stack Label :=
  ⟨none,none,fun _=>bytes mode.1 mode.2.1 mode.2.2⟩
/-- Every emitted bit is an actual push, with the actual halt also retained. -/
theorem source_run (mode : Mode) :
    B.run code ((bytes mode.1 mode.2.1 mode.2.2).length+1) (initial mode)=some (done mode) := by
  rcases mode with ⟨degree,low,high⟩
  fin_cases degree <;> cases low <;> cases high <;> apply congrArg some <;> congr 1
end RiemannGaussian.SemiprimeD1StackOwnerPaletteSource
