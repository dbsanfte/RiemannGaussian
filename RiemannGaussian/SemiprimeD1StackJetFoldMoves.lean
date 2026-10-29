/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetFoldPrimitives
/-! # Physically paid sum/product transfers and old-operand cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackJetFoldMoves
open SemiprimeD1StackJetFold SemiprimeD1StackJetFoldState SemiprimeD1StackJetFoldPrimitives
open SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Exact physical tail-sum transfer: actual preserving copy followed by actual source drain. -/
def movedSum (v:Values):Values:=Function.update (Function.update v .tailSum (v .sum)) .sum []
/-- The recursively acquired tail sum is physically retained while the actual head product is computed. -/
theorem move_sum (v:Values) (hz:v .tailSum=[]):
    Runs program (6*(v .sum).length+5) (ctl .copySum) (data v) (ctl .productCall) (data (movedSum v)):=by
  let b:=Function.update v .tailSum (v .sum)
  have h0:=copy_view .sum .copySum .clearSum v rfl
  change Runs program (5*(v .sum).length+4) _ _ _
    (data (Function.update v .tailSum (v .sum++v .tailSum))) at h0
  rw [hz,List.append_nil] at h0
  have h1:=drain_view .clearSum .productCall .sum b rfl
  change Runs program ((v .sum).length+1) _ _ _ (data (movedSum v)) at h1
  have h:=join h0 h1
  convert h using 1;omega
/-- Exact cleaned current product after both old operands and temporary output are physically drained. -/
def movedProduct (v:Values):Values:=
  Function.update (Function.update (Function.update v .left []) .product (v .result)) .result []
/-- All consumed original/padded operand bits and all produced output bits are counted in the real transfer trace. -/
theorem move_product (v:Values):
    Runs program ((v .left).length+(v .product).length+6*(v .result).length+7)
      (ctl .clearLeft) (data v) (ctl .returning) (data (movedProduct v)):=by
  let a:=Function.update v .left []
  let b:=Function.update a .product []
  let c:=Function.update b .product (v .result)
  have h0:=drain_view .clearLeft .clearRight .left v rfl
  change Runs program ((v .left).length+1) _ _ _ (data a) at h0
  have h1:=drain_view .clearRight .copyProduct .product a rfl
  change Runs program ((v .product).length+1) _ _ _ (data b) at h1
  have h2:=copy_view .product .copyProduct .clearOutput b rfl
  change Runs program (5*(v .result).length+4) _ _ _
    (data (Function.update b .product (v .result++[]))) at h2
  rw [List.append_nil] at h2
  have h3:=drain_view .clearOutput .returning .result c rfl
  change Runs program ((v .result).length+1) _ _ _ (data (Function.update c .result [])) at h3
  have he:Function.update c .result []=movedProduct v:=by funext s;cases s <;> rfl
  rw [he] at h3
  have h:=join h0 (join h1 (join h2 h3))
  convert h using 1;omega
end RiemannGaussian.SemiprimeD1StackJetFoldMoves
