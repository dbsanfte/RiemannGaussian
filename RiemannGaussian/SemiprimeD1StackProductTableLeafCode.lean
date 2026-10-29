/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductTableLeafCalls
/-! # Every actual literal product-table scalar code push
Only the already physically computed singleton checker bit selects the fixed
zero/one branch. These are integral local entries before any network product.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackProductTableLeafCode
open SemiprimeD1StackProductTable SemiprimeD1StackProductTableState
open SemiprimeD1StackProductTableLeafCalls SemiprimeD1StackProcedureTrace
open SemiprimeD1BooleanTreeStream (leafBytes)
/-- Next literal zero-code label, fixed before N. -/
def zeroNext (pos : Fin 4) : Label :=
  if h:pos.val<3 then .zero ⟨pos.val+1,by omega⟩ else .leafCleanup
/-- Next literal one-code label, fixed before N. -/
def oneNext (pos : Fin 6) : Label :=
  if h:pos.val<5 then .one ⟨pos.val+1,by omega⟩ else .leafCleanup
/-- One actual zero-leaf push preserves the full still-live checker store. -/
theorem zero_step (pos : Fin 4) (checker : P.Stack→List Bool) (bits front hist : List Bool) :
    Runs program 1 (.zero pos) (withChecker (data bits 0 front hist) checker) (zeroNext pos)
      (withChecker (data bits 0 front (zeroBits pos::hist)) checker) := by
  apply one_base program (.zero pos) (zeroNext pos) (.push (.inr .reversed) (zeroBits pos) (zeroNext pos)) _ _ rfl
  · rfl
  · funext k;cases k with
    | inl k=>rfl
    | inr k=>cases k <;> rfl
/-- One actual accepted-leaf push preserves every still-live checker byte. -/
theorem one_step (pos : Fin 6) (checker : P.Stack→List Bool) (bits front hist : List Bool) :
    Runs program 1 (.one pos) (withChecker (data bits 0 front hist) checker) (oneNext pos)
      (withChecker (data bits 0 front (oneBits pos::hist)) checker) := by
  apply one_base program (.one pos) (oneNext pos) (.push (.inr .reversed) (oneBits pos) (oneNext pos)) _ _ rfl
  · rfl
  · funext k;cases k with
    | inl k=>rfl
    | inr k=>cases k <;> rfl
/-- Complete scalar/tree/vector/word/end framing, with every bit actually
written. No coefficient getter or already-reduced aggregate is substituted. -/
theorem emit_run (b : Bool) (checker : P.Stack→List Bool) (bits front hist : List Bool) :
    Runs program (leafBytes b).length (emitStart b) (withChecker (data bits 0 front hist) checker) .leafCleanup
      (withChecker (data bits 0 front ((leafBytes b).reverse++hist)) checker) := by
  cases b with
  | false=>
    have h0:=zero_step 0 checker bits front hist
    have h1:=zero_step 1 checker bits front (false::hist)
    have h2:=zero_step 2 checker bits front (true::false::hist)
    have h3:=zero_step 3 checker bits front (false::true::false::hist)
    exact runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3
  | true=>
    have h0:=one_step 0 checker bits front hist
    have h1:=one_step 1 checker bits front (false::hist)
    have h2:=one_step 2 checker bits front (true::false::hist)
    have h3:=one_step 3 checker bits front (true::true::false::hist)
    have h4:=one_step 4 checker bits front (true::true::true::false::hist)
    have h5:=one_step 5 checker bits front (false::true::true::true::false::hist)
    exact runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _
        (runs_trans program _ _ _ _ _ _ _ _
          (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3) h4) h5
end RiemannGaussian.SemiprimeD1StackProductTableLeafCode
