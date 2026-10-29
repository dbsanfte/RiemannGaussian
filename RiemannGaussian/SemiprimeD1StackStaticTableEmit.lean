/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticTableSpec
/-! # Every actual literal static-checker scalar code push
Only the already physically computed singleton checker bit selects the fixed
zero/one branch. These are integral local entries before any network product.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackStaticTableEmit
open SemiprimeD1StackStaticTable SemiprimeD1StackStaticTableSpec SemiprimeD1StackProcedureTrace
open SemiprimeD1BooleanTreeStream (leafBytes)
variable {K L : Type} [DecidableEq K] (s : Static K L)
/-- The actual output bit selects a fixed finite scalar-code branch. -/
def emitStart (b : Bool) : Label L s.roles.length := if b then .one 0 else .zero 0
/-- Next literal zero-code label, fixed before N. -/
def zeroNext (pos : Fin 4) : Label L s.roles.length :=
  if h:pos.val<3 then .zero ⟨pos.val+1,by omega⟩ else .leafCleanup
/-- Next literal one-code label, fixed before N. -/
def oneNext (pos : Fin 6) : Label L s.roles.length :=
  if h:pos.val<5 then .one ⟨pos.val+1,by omega⟩ else .leafCleanup
/-- One actual zero-leaf push preserves the full still-live checker store. -/
theorem zero_step (pos : Fin 4) (live : K→List Bool) (original : K→List Bool) (bank front hist : List Bool) :
    Runs (program s) 1 (.zero pos) (withChecker (data original bank 0 front hist) live) (zeroNext s pos)
      (withChecker (data original bank 0 front (zeroBits pos::hist)) live) := by
  apply one_base (program s) (.zero pos) (zeroNext s pos) (.push (aux .reversed) (zeroBits pos) (zeroNext s pos)) _ _ rfl
  · rfl
  · funext k;cases k with
    | inl k=>rfl
    | inr k=>
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · cases k <;> rfl
/-- One actual accepted-leaf push preserves every still-live checker byte. -/
theorem one_step (pos : Fin 6) (live : K→List Bool) (original : K→List Bool) (bank front hist : List Bool) :
    Runs (program s) 1 (.one pos) (withChecker (data original bank 0 front hist) live) (oneNext s pos)
      (withChecker (data original bank 0 front (oneBits pos::hist)) live) := by
  apply one_base (program s) (.one pos) (oneNext s pos) (.push (aux .reversed) (oneBits pos) (oneNext s pos)) _ _ rfl
  · rfl
  · funext k;cases k with
    | inl k=>rfl
    | inr k=>
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · cases k <;> rfl
/-- Complete scalar/tree/vector/word/end framing, with every bit actually
written. No coefficient getter or already-reduced aggregate is substituted. -/
theorem emit_run (b : Bool) (live : K→List Bool) (original : K→List Bool) (bank front hist : List Bool) :
    Runs (program s) (leafBytes b).length (emitStart s b) (withChecker (data original bank 0 front hist) live) .leafCleanup
      (withChecker (data original bank 0 front ((leafBytes b).reverse++hist)) live) := by
  cases b with
  | false=>
    have h0:=zero_step s 0 live original bank front hist
    have h1:=zero_step s 1 live original bank front (false::hist)
    have h2:=zero_step s 2 live original bank front (true::false::hist)
    have h3:=zero_step s 3 live original bank front (false::true::false::hist)
    exact runs_trans (program s) _ _ _ _ _ _ _ _
      (runs_trans (program s) _ _ _ _ _ _ _ _ (runs_trans (program s) _ _ _ _ _ _ _ _ h0 h1) h2) h3
  | true=>
    have h0:=one_step s 0 live original bank front hist
    have h1:=one_step s 1 live original bank front (false::hist)
    have h2:=one_step s 2 live original bank front (true::false::hist)
    have h3:=one_step s 3 live original bank front (true::true::false::hist)
    have h4:=one_step s 4 live original bank front (true::true::true::false::hist)
    have h5:=one_step s 5 live original bank front (false::true::true::true::false::hist)
    exact runs_trans (program s) _ _ _ _ _ _ _ _
      (runs_trans (program s) _ _ _ _ _ _ _ _
        (runs_trans (program s) _ _ _ _ _ _ _ _
          (runs_trans (program s) _ _ _ _ _ _ _ _ (runs_trans (program s) _ _ _ _ _ _ _ _ h0 h1) h2) h3) h4) h5
end RiemannGaussian.SemiprimeD1StackStaticTableEmit
