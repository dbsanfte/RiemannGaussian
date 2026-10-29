/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMacroFiniteEnumerations

/-! # Static original vertex-catalogue modes
Only the mode-to-source-role table enters the finite control of the physical
catalogue builder. Natural dimensions and original typed labels below are
mathematical specifications, never runtime graph/list answer inputs.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1VertexCatalogueModes

/-- The eighteen actual constructor blocks, in original enumeration order. -/
inductive Mode where
  | input | first | scale | second | product | carryInitial | carry | carryTerminal | orGate | inputCheck
  | wordInput | wordFirst | wordTwiddle | wordSecond | wordProduct | wordCarry | flagDigit | flagOr
  deriving DecidableEq,Repr
/-- Literal original mode ordering, fixed before all inputs. -/
def order : List Mode := [.input,.first,.scale,.second,.product,.carryInitial,.carry,.carryTerminal,.orGate,.inputCheck,
  .wordInput,.wordFirst,.wordTwiddle,.wordSecond,.wordProduct,.wordCarry,.flagDigit,.flagOr]
instance : Fintype Mode := Fintype.ofList order (by intro m;cases m <;> simp [order])
/-- Physical source-role catalogue; none stores an unbounded native scalar. -/
inductive Role where
  | one | two | three | radius | firstAxis | secondAxis | digits | digitsPred | radiusSucc
  deriving DecidableEq,Repr
instance : Fintype Role := Fintype.ofList [.one,.two,.three,.radius,.firstAxis,.secondAxis,.digits,.digitsPred,.radiusSucc]
  (by intro k;cases k <;> simp)
/-- Fixed numeric constructor code, specified by the original static order. -/
def code : Mode→ℕ
  | .input => 0 | .first => 1 | .scale => 2 | .second => 3 | .product => 4
  | .carryInitial => 5 | .carry => 6 | .carryTerminal => 7 | .orGate => 8 | .inputCheck => 9
  | .wordInput => 10 | .wordFirst => 11 | .wordTwiddle => 12 | .wordSecond => 13
  | .wordProduct => 14 | .wordCarry => 15 | .flagDigit => 16 | .flagOr => 17
/-- Static predecessor control for reverse physical emission. -/
def previous : Mode→Mode
  | .input => .input | .first => .input | .scale => .first | .second => .scale | .product => .second
  | .carryInitial => .product | .carry => .carryInitial | .carryTerminal => .carry | .orGate => .carryTerminal
  | .inputCheck => .orGate | .wordInput => .inputCheck | .wordFirst => .wordInput | .wordTwiddle => .wordFirst
  | .wordSecond => .wordTwiddle | .wordProduct => .wordSecond | .wordCarry => .wordProduct
  | .flagDigit => .wordCarry | .flagOr => .flagDigit
/-- Four fixed source roles for each actual Cartesian constructor block. -/
def roles : Mode→Fin 4→Role
  | .input => ![.two,.radius,.one,.one]
  | .first => ![.three,.firstAxis,.one,.one]
  | .scale => ![.three,.firstAxis,.secondAxis,.one]
  | .second => ![.three,.secondAxis,.one,.one]
  | .product => ![.radius,.one,.one,.one]
  | .carryInitial => ![.one,.one,.one,.one]
  | .carry => ![.radius,.one,.one,.one]
  | .carryTerminal => ![.one,.one,.one,.one]
  | .orGate => ![.two,.digitsPred,.one,.one]
  | .inputCheck => ![.two,.one,.one,.one]
  | .wordInput => ![.two,.radius,.radiusSucc,.one]
  | .wordFirst => ![.three,.firstAxis,.secondAxis,.radiusSucc]
  | .wordTwiddle => ![.three,.firstAxis,.secondAxis,.radiusSucc]
  | .wordSecond => ![.three,.secondAxis,.firstAxis,.radiusSucc]
  | .wordProduct => ![.radius,.radiusSucc,.one,.one]
  | .wordCarry => ![.radiusSucc,.radiusSucc,.one,.one]
  | .flagDigit => ![.two,.digits,.one,.one]
  | .flagOr => ![.two,.digitsPred,.one,.one]
/-- Original mathematical dimensions for the actual cached source roles. -/
def dimension (r t digits:ℕ) : Role→ℕ
  | .one => 1 | .two => 2 | .three => 3 | .radius => r*t
  | .firstAxis => r | .secondAxis => t | .digits => digits | .digitsPred => digits-1 | .radiusSucc => r*t+1
/-- Original dimension tuple selected by the finite role table. -/
def dims (r t digits:ℕ) (mode:Mode) (axis:Fin 4) : ℕ := dimension r t digits (roles mode axis)

/-- Every physical constructor tag needs at most seventeen unary cells. -/
theorem code_le (mode:Mode) : code mode≤17 := by cases mode <;> decide
/-- The reverse-mode loop removes exactly one actual tag marker between blocks. -/
theorem previous_code (mode:Mode) (hm:mode≠.input) : code (previous mode)+1=code mode := by
  cases mode <;> simp_all [code,previous]
/-- All constructor modes are distinct and complete in the exact original order. -/
theorem order_nodup : order.Nodup := by decide
/-- Exactly eighteen static blocks, including equality-vertex families. -/
theorem order_length : order.length=18 := rfl
/-- Every mode occurs in the finite original family list. -/
theorem mem_order (mode:Mode) : mode∈order := by cases mode <;> simp [order]
/-- All source-role values are bounded by original dimensions, not supplied per-family scope answers. -/
theorem dimension_le (r t digits:ℕ) (B:ℕ) (hr:r≤B) (ht:t≤B) (hR:r*t+1≤B)
    (hd:digits≤B) (h3:3≤B) (role:Role) : dimension r t digits role≤B := by
  cases role <;> simp only [dimension] <;> omega
end RiemannGaussian.SemiprimeD1VertexCatalogueModes
