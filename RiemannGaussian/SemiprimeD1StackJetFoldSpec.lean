/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetFoldOperators
/-! # Actual header/recursive boundaries and own literal fold allowances
The allowances sum actual frozen operator caps and literal parser/frame/copy/
drain/return costs. Native JetRun clocks are never used as a physical clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackJetFoldSpec
open SemiprimeD1StackJetFold SemiprimeD1StackJetFoldState SemiprimeD1StackJetFoldWords
open SemiprimeD1StackJetFoldOperators
open SemiprimeD1JetAxes (Context)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
/-- Actual original inputs and actually acquired metadata at a real fold boundary. -/
structure Header where
  /-- Original physical unary-axis header. -/
  axes:List Bool
  /-- Original binary precision word. -/
  precision:List Bool
  /-- Actual prepared nested child-result vector, retained without recoding its coefficients. -/
  children:List Bool
  /-- Actual physically acquired unary rank counter. -/
  rank:List Bool
  /-- Actual physically acquired unary precision count. -/
  width:List Bool
/-- The acquired physical context agrees with its native proof-side interpretation. -/
structure Matches (ctx:Context) (h:Header):Prop where
  /-- Actual positive-axis encoding. -/
  axes:h.axes=vectorBits (ctx.axes.map unary)
  /-- Actual unary precision width. -/
  width:h.width.length=ctx.precision
  /-- Actual unary rank word. -/
  rank:h.rank=unary ctx.rank
/-- All physical caller/operator boundary words with a fixed actually acquired context. -/
def bank (h:Header) (modes group frames left product result tailSum sum valid:List Bool):Values:=
  values h.axes h.precision h.children h.rank h.width modes group frames left product result tailSum sum valid
/-- Actual product entry; remaining modes and the caller's saved sum words are untouched. -/
def productNode (h:Header) (modes tailSum sum:List Bool) (children:Group) (frames:List Bool):Values:=
  bank h modes (groupTape children) frames [] [] [] tailSum sum []
/-- Actual product return boundary after its complete input vector and temporary operands were consumed. -/
def productOut (h:Header) (modes tailSum sum:List Bool) (answer:Jet) (frames:List Bool):Values:=
  bank h modes [] frames [] (jetTape answer) [] tailSum sum []
/-- Actual complete sum entry, with one real saved activation suffix. -/
def sumNode (h:Header) (modes:Modes) (frames:List Bool):Values:=
  bank h (modeTape modes) [] frames [] [] [] [] [] []
/-- Actual complete sum return boundary, retaining all context and original child inputs. -/
def sumOut (h:Header) (answer:Jet) (frames:List Bool):Values:=
  bank h [] [] frames [] [] [] [] (jetTape answer) []
/-- The real adder computes dense zero from two physically seeded empty-vector markers. -/
theorem add_empty_zero (ctx:Context):
    (SemiprimeD1JetRingBits.add ctx [] []).words=(SemiprimeD1JetAffineCoefficient.zero ctx).words:=by
  have hz:(SemiprimeD1JetScalarBits.add ctx.precision [] []).bits=[]:=by
    cases ctx.precision <;> simp [SemiprimeD1JetScalarBits.add,SemiprimeBitArithmetic.addBits,
      SemiprimeD1JetScalarBits.reduce,SemiprimeD1JetScalarBits.takeBits,SemiprimeSourceCompactBits.trim]
  simp only [SemiprimeD1JetRingBits.add,List.map_map,Function.comp_def,
    SemiprimeD1JetRingBits.addAt,SemiprimeD1JetRingBits.read,SemiprimeD1JetAffineCoefficient.zero]
  rw [hz,List.map_const',List.length_range]
/-- Frozen actual multiplication cap on the two currently restored binary vectors. -/
def multiplyCost (ctx:Context) (h:Header) (a b:Jet):Nat:=
  mulBound ctx (bank h [] [] [] (jetTape a) (jetTape b) [] [] [] [])
/-- Exact frozen actual dense-addition time plus its physical caller transition. -/
def addCost (h:Header) (a b:Jet):Nat:=SemiprimeD1StackJetAddExecution.totalTime h.width h.rank a b+1
/-- Actual per-product-node allowance includes every saved/read/copied/drained payload bit. -/
def productEdge (ctx:Context) (h:Header) (x:Jet) (xs:Group):Nat:=
  multiplyCost ctx h x (productWords ctx xs)+100*((jetTape x).length+
    (jetTape (productWords ctx xs)).length+(jetTape (productWords ctx (x::xs))).length+1)
/-- Own actual primitive-derived right-product allowance. -/
def productBudget (ctx:Context) (h:Header):Group→Nat
  | []=>SemiprimeD1StackJetUnitExecution.totalTime h.width h.rank+2
  | x::xs=>productBudget ctx h xs+productEdge ctx h x xs
/-- Actual per-mode allowance includes the entire real saved head group and saved tail-sum bytes. -/
def sumEdge (ctx:Context) (h:Header) (x:Group) (xs:Modes):Nat:=
  addCost h (productWords ctx x) (sumWords ctx xs)+100*((groupTape x).length+(jetTape (sumWords ctx xs)).length+1)
/-- Own actual primitive-derived right-mode-sum allowance, including every complete head product. -/
def sumBudget (ctx:Context) (h:Header):Modes→Nat
  | []=>SemiprimeD1StackJetAddExecution.totalTime h.width h.rank [] []+4
  | x::xs=>sumBudget ctx h xs+productBudget ctx h x+sumEdge ctx h x xs
end RiemannGaussian.SemiprimeD1StackJetFoldSpec
