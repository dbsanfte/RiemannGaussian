/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishPrimitives
import RiemannGaussian.SemiprimeD1StackRecoveryFinishWords
/-! # Actual simultaneous denominator/numerator low-bit strip trace
The finite source inspects actual denominator bits, pops actual numerator bits,
records every lost one, and writes the actual shifted-one content and odd suffix.
No quotient, valuation or native strip evaluator is an instruction operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishStrip
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishState
open SemiprimeD1StackRecoveryFinishPrimitives SemiprimeD1StackRecoveryFinishWords SemiprimeD1StackProcedureTrace
local notation "ctl"=>Label.local
/-- Exact four changing physical words during the actual low-bit loop. -/
def view (base:Values) (denominator magnitude content lost:List Bool):Values
  | .aux .denominatorWork=>denominator | .aux .numeratorWork=>magnitude
  | .aux .content=>content | .aux .lost=>lost | s=>base s
/-- A denominator pop changes its exact current physical suffix only. -/
theorem denominator_update (base:Values) (d n c l word:List Bool):
    Function.update (view base d n c l) (.aux .denominatorWork) word=view base word n c l:=by
  funext s;cases s with
  | aux a=>cases a <;> rfl
  | _=>rfl
/-- A numerator pop changes its exact current physical suffix only. -/
theorem numerator_update (base:Values) (d n c l word:List Bool):
    Function.update (view base d n c l) (.aux .numeratorWork) word=view base d word c l:=by
  funext s;cases s with
  | aux a=>cases a <;> rfl
  | _=>rfl
/-- The actual content shift writes one literal low zero cell. -/
theorem content_update (base:Values) (d n c l word:List Bool):
    Function.update (view base d n c l) (.aux .content) word=view base d n word l:=by
  funext s;cases s with
  | aux a=>cases a <;> rfl
  | _=>rfl
/-- The source writes the actual accumulated one-bit loss flag. -/
theorem lost_update (base:Values) (d n c l word:List Bool):
    Function.update (view base d n c l) (.aux .lost) word=view base d n c word:=by
  funext s;cases s with
  | aux a=>cases a <;> rfl
  | _=>rfl
/-- Dropping one actual denominator zero leaves the same original odd suffix. -/
theorem odd_false (d:List Bool):odd (false::d)=odd d:=by simp [odd,zeros]
/-- Paired numerator pops implement exact right shifts, with a literal empty tail after EOF. -/
theorem dropped_false (d n:List Bool):dropped (false::d) n=dropped d n.tail:=by
  cases n <;> simp [dropped,zeros]
/-- The actual lost flag combines exactly the discarded low digit and the remaining actual discarded digits. -/
theorem lost_false_step (d n:List Bool):lost (false::d) n=(n.headD false||lost d n.tail):=by
  cases n with
  | nil=>simp [lost,zeros]
  | cons b n=>rfl
/-- Physical low-zero content shifts commute with earlier identical zero cells. -/
theorem zero_prefix (n:Nat) (c:List Bool):
    List.replicate n false++false::c=List.replicate (n+1) false++c:=by
  rw [List.replicate_succ',List.append_assoc]
  rfl
/-- Three actual instructions strip one zero, shift one numerator cell and preserve the exact loss flag. -/
theorem zero_run (base:Values) (d n c:List Bool) (l:Bool):
    Runs program 3 (ctl (.strip l)) (data (view base (false::d) n c []))
      (ctl (.strip (l||n.headD false))) (data (view base d n.tail (false::c) [])):=by
  have h0:=pop_view (ctl (.strip l)) (ctl .abort) (ctl (.zero l)) (ctl (.odd l))
    (.aux .denominatorWork) (view base (false::d) n c []) (false::d) rfl rfl
  rw [denominator_update] at h0
  have h1:=push_view (ctl (.zero l)) (ctl (.shift l)) (.aux .content) false (view base d n c []) rfl
  change Runs program 1 (ctl (.zero l)) _ (ctl (.shift l))
    (data (Function.update (view base d n c []) (.aux .content) (false::c))) at h1
  rw [content_update] at h1
  have h2:=pop_view (ctl (.shift l)) (ctl (.strip l)) (ctl (.strip l)) (ctl (.strip true))
    (.aux .numeratorWork) (view base d n (false::c) []) n rfl rfl
  rw [numerator_update] at h2
  have h2':Runs program 1 (ctl (.shift l)) (data (view base d n (false::c) []))
      (ctl (.strip (l||n.headD false))) (data (view base d n.tail (false::c) [])):=by
    cases n with
    | nil=>simpa only [List.head?_nil,List.headD_nil,SemiprimeD1StackBytecode.choose,Bool.or_false] using h2
    | cons b n=>cases b <;> simpa only [List.head?_cons,List.headD_cons,SemiprimeD1StackBytecode.choose,
        Bool.or_false,Bool.or_true] using h2
  exact join (join h0 h1) h2'
/-- Three actual instructions restore the detected odd one and write the actual loss flag. -/
theorem odd_run (base:Values) (d n c:List Bool) (l:Bool):
    Runs program 3 (ctl (.strip l)) (data (view base (true::d) n c []))
      (ctl .signFloor) (data (view base (true::d) n c [l])):=by
  have h0:=pop_view (ctl (.strip l)) (ctl .abort) (ctl (.zero l)) (ctl (.odd l))
    (.aux .denominatorWork) (view base (true::d) n c []) (true::d) rfl rfl
  rw [denominator_update] at h0
  have h1:=push_view (ctl (.odd l)) (ctl (.saveLost l)) (.aux .denominatorWork) true (view base d n c []) rfl
  change Runs program 1 (ctl (.odd l)) _ (ctl (.saveLost l))
    (data (Function.update (view base d n c []) (.aux .denominatorWork) (true::d))) at h1
  rw [denominator_update] at h1
  have h2:=push_view (ctl (.saveLost l)) (ctl .signFloor) (.aux .lost) l (view base (true::d) n c []) rfl
  change Runs program 1 (ctl (.saveLost l)) _ (ctl .signFloor)
    (data (Function.update (view base (true::d) n c []) (.aux .lost) [l])) at h2
  rw [lost_update] at h2
  exact join (join h0 h1) h2
/-- Full actual strip loop: exact content/suffix/remaining numerator/lost flag, with its SAME own linear clock. -/
theorem strip_run (base:Values) (d:List Bool) (hd:0<SemiprimeBitArithmetic.bitValue d)
    (n c:List Bool) (l:Bool):
    Runs program (3*zeros d+3) (ctl (.strip l)) (data (view base d n c []))
      (ctl .signFloor) (data (view base (odd d) (dropped d n)
        (List.replicate (zeros d) false++c) [l||lost d n])):=by
  induction d generalizing n c l with
  | nil=>simp only [SemiprimeBitArithmetic.bitValue] at hd;omega
  | cons b d ih=>
    cases b with
    | false=>
      have hp:0<SemiprimeBitArithmetic.bitValue d:=by
        simp only [SemiprimeBitArithmetic.bitValue,SemiprimeBitArithmetic.bitNat,Bool.false_eq_true,
          ite_false,Nat.zero_add] at hd
        omega
      have h0:=zero_run base d n c l
      have h1:=ih hp n.tail (false::c) (l||n.headD false)
      have h:=join h0 h1
      have hc:3+(3*zeros d+3)=3*zeros (false::d)+3:=by simp only [zeros];omega
      rw [hc] at h
      simpa only [odd_false,dropped_false,lost_false_step,zeros,zero_prefix,Bool.or_assoc] using h
    | true=>
      simpa only [zeros,odd,dropped,lost,List.drop_zero,List.take_zero,List.any_nil,List.replicate_zero,
        List.nil_append,Bool.or_false,Nat.mul_zero,Nat.zero_add] using odd_run base d n c l
end RiemannGaussian.SemiprimeD1StackRecoveryFinishStrip
