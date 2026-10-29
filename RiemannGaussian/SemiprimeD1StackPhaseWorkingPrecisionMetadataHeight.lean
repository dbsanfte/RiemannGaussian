/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataArithmetic
/-! # Paid numerator construction, actual height division and physical cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataHeight
open SemiprimeD1StackPhaseWorkingPrecisionMetadata SemiprimeD1StackPhaseWorkingPrecisionMetadataPrimitives
open SemiprimeD1StackPhaseWorkingPrecisionMetadataArithmetic SemiprimeD1StackProcedureTrace
/-- Height-only acquired state; ALL transient dividend/divisor/remainder words are empty. -/
def heightCounts (M u : Nat) : Counts :={height:=height M u}
/-- Three real M copies and one real u copy form the complete physical numerator. -/
theorem numerator_run (a u M : Nat) (t p : List Bool) :
    Runs program (15*M+5*u+16) (.numerator 0) (context a u M t p empty)
      .minusOne (context a u M t p {input:=3*M+u}) :=by
  let c1:=copied a u M t 0 empty
  let c2:=copied a u M t 0 c1
  let c3:=copied a u M t 0 c2
  have h0:=copy_context a u M t p 0 empty (.numerator 0) (.numerator 1) rfl
  have h1:=copy_context a u M t p 0 c1 (.numerator 1) (.numerator 2) rfl
  have h2:=copy_context a u M t p 0 c2 (.numerator 2) .addU rfl
  have h3:=copy_context a u M t p 1 c3 .addU .minusOne rfl
  have hh:=join (join (join h0 h1) h2) h3
  change Runs program (((5*M+4)+(5*M+4))+(5*M+4)+(5*u+4)) (.numerator 0) _ .minusOne
    (context a u M t p {input:=u+(M+(M+(M+0)))}) at hh
  rw [show u+(M+(M+(M+0)))=3*M+u by omega] at hh
  convert hh using 1
  omega
/-- The minus-one instruction ACTUALLY pops one numerator marker; u>0 justifies this branch. -/
theorem minus_one (a u M : Nat) (t p : List Bool) (hu : 0<u) :
    Runs program 1 .minusOne (context a u M t p {input:=3*M+u})
      .copyDivisor (context a u M t p {input:=3*M+u-1}) :=by
  have hw:D.unary (3*M+u)=true::D.unary (3*M+u-1):=by
    conv_lhs=>rw [show 3*M+u=(3*M+u-1)+1 by omega]
    rfl
  apply one_base program .minusOne .copyDivisor (.pop (divStack .input) .done .copyDivisor .copyDivisor) _ _ rfl
  · change some (SemiprimeD1StackBytecode.choose Label.done Label.copyDivisor Label.copyDivisor (D.unary (3*M+u)).head?)=some Label.copyDivisor
    rw [hw]
    rfl
  · funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · cases k <;> first | rfl | (change (D.unary (3*M+u)).tail=D.unary (3*M+u-1);rw [hw];rfl)
      · rfl
/-- Actual frozen divider on the physically built numerator and copied original u. -/
theorem divide_run (a u M : Nat) (t p : List Bool) :
    ∃q≤100*(3*M+u-1+u+1)+1,Runs program q .divide
      (context a u M t p {input:=3*M+u-1,divisor:=u}) .clearRemainder
      (context a u M t p {divisor:=u,height:=height M u,remainder:=(3*M+u-1)%u}) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackUnaryDivmodBytecode.divide_run (3*M+u-1) u
  refine ⟨q+1,by omega,?_⟩
  apply included_call program divStack Label.division div_injective D.code D.entry (fun _=>rfl)
    .divide .clearRemainder rfl q
    ⟨some D.entry,none,D.contents (D.unary (3*M+u-1)) (D.unary u) [] [] [] []⟩
    ⟨none,none,D.contents [] (D.unary u) [] [] (D.unary (height M u)) (D.unary ((3*M+u-1)%u))⟩ _ _ rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · rfl
      · rcases k with k|k
        · exact (hk k rfl).elim
        · rfl
/-- BOTH remaining division words are physically erased; only h is retained. -/
theorem division_clear (a u M : Nat) (t p : List Bool) :
    Runs program (((3*M+u-1)%u+1)+(u+1)) .clearRemainder
      (context a u M t p {divisor:=u,height:=height M u,remainder:=(3*M+u-1)%u})
      .qCopyU (context a u M t p (heightCounts M u)) :=by
  let c:Counts:={divisor:=u,height:=height M u,remainder:=(3*M+u-1)%u}
  have h0:=SemiprimeD1StackPhysicalLoops.drain program .clearRemainder .clearDivisor (divStack .remainder)
    rfl (context a u M t p c) (D.unary c.remainder)
  have hi:Function.update (context a u M t p c) (divStack .remainder) (D.unary c.remainder)=context a u M t p c:=
    Function.update_eq_self _ _
  have ho:Function.update (context a u M t p c) (divStack .remainder) []=
      context a u M t p {divisor:=u,height:=height M u}:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k <;> cases k <;> rfl
  rw [hi,ho,D.unary,List.length_replicate] at h0
  have h1:=SemiprimeD1StackPhysicalLoops.drain program .clearDivisor .qCopyU (divStack .divisor)
    rfl (context a u M t p {divisor:=u,height:=height M u}) (D.unary u)
  have hi1:Function.update (context a u M t p {divisor:=u,height:=height M u}) (divStack .divisor) (D.unary u)=
      context a u M t p {divisor:=u,height:=height M u}:=Function.update_eq_self _ _
  have ho1:Function.update (context a u M t p {divisor:=u,height:=height M u}) (divStack .divisor) []=
      context a u M t p (heightCounts M u):=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k <;> cases k <;> rfl
  rw [hi1,ho1,D.unary,List.length_replicate] at h1
  exact join h0 h1
/-- Complete paid h acquisition, using acceptance only to justify the actual positive divisor. -/
theorem source_run (a u M : Nat) (t p : List Bool) (hu : 0<u) :
    ∃q≤1000*(M+u+1),Runs program q (.numerator 0) (context a u M t p empty)
      .qCopyU (context a u M t p (heightCounts M u)) :=by
  have h0:=numerator_run a u M t p
  have h1:=minus_one a u M t p hu
  have h2:=copy_context a u M t p 2 ({input:=3*M+u-1}:Counts) .copyDivisor .divide rfl
  change Runs program (5*u+4) .copyDivisor _ .divide
    (context a u M t p {input:=3*M+u-1,divisor:=u+0}) at h2
  obtain ⟨b,hb,h3⟩:=divide_run a u M t p
  have h4:=division_clear a u M t p
  have hh:=join (join (join (join h0 h1) h2) h3) h4
  refine ⟨_,?_,hh⟩
  have hm:(3*M+u-1)%u≤3*M+u-1:=Nat.mod_le _ _
  omega
end RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataHeight
