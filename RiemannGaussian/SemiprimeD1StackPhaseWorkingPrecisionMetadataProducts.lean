/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataHeight
/-! # Actual paired-marker subtraction, bounded unary products and cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataProducts
open SemiprimeD1StackPhaseWorkingPrecisionMetadata SemiprimeD1StackPhaseWorkingPrecisionMetadataPrimitives
open SemiprimeD1StackProcedureTrace
/-- Proof view selects the actual u-copy or a-copy and actual order-copy fields. -/
def subCounts (second : Bool) (c : Counts) (n s : Nat) : Counts :=
  if second then {c with delta:=n,subtractWork:=s} else {c with multiplicand:=n,subtractWork:=s}
/-- Each physically removed order marker consumes one actual target marker. -/
theorem subtract_pair (second : Bool) (a u M : Nat) (t p : List Bool) (c : Counts) (n s : Nat) :
    Runs program 2 (.subtract second) (context a u M t p (subCounts second c (n+1) (s+1)))
      (.subtract second) (context a u M t p (subCounts second c n s)) :=by
  have h0:Runs program 1 (.subtract second) (context a u M t p (subCounts second c (n+1) (s+1)))
      (.remove second) (context a u M t p (subCounts second c (n+1) s)):=by
    apply one_base program (.subtract second) (.remove second)
      (.pop (aux .subtractWork) (if second then .done else .qCopyH) (.remove second) (.remove second)) _ _ rfl
    · cases second <;> rfl
    · cases second <;> funext k <;> rcases k with k|k
      all_goals first | rfl | (rcases k with k|k <;> cases k <;> rfl)
  have h1:Runs program 1 (.remove second) (context a u M t p (subCounts second c (n+1) s))
      (.subtract second) (context a u M t p (subCounts second c n s)):=by
    apply one_base program (.remove second) (.subtract second)
      (.pop (subtractTarget second) .done (.subtract second) (.subtract second)) _ _ rfl
    · cases second <;> rfl
    · cases second <;> funext k <;> rcases k with k|k
      all_goals first | rfl | (rcases k with k|k <;> cases k <;> rfl)
  exact join h0 h1
/-- The whole copied order is physically consumed; the exact target difference remains. -/
theorem subtract_run (second : Bool) (a u M : Nat) (t p : List Bool) (c : Counts) (s n : Nat) (h : s≤ n) :
    Runs program (2*s+1) (.subtract second) (context a u M t p (subCounts second c n s))
      (if second then .done else .qCopyH) (context a u M t p (subCounts second c (n-s) 0)) :=by
  induction s generalizing n with
  | zero=>
    apply one_base program (.subtract second) _
      (.pop (aux .subtractWork) (if second then .done else .qCopyH) (.remove second) (.remove second)) _ _ rfl
    · cases second <;> rfl
    · cases second <;> funext k <;> rcases k with k|k
      all_goals first | rfl | (rcases k with k|k <;> cases k <;> rfl)
  | succ s ih=>
    cases n with
    | zero=>omega
    | succ n=>
      have hh:=join (subtract_pair second a u M t p c n s) (ih n (by omega))
      rw [show n+1-(s+1)=n-s by omega]
      convert hh using 1
      omega
/-- A real preserving copy of acquired i precedes every actual marker subtraction. -/
theorem copy_subtract (second : Bool) (a u M : Nat) (t p : List Bool) (c : Counts) (n : Nat)
    (hi : order a t≤ n) :
    Runs program (7*order a t+5) (.subtractCopy second) (context a u M t p (subCounts second c n 0))
      (if second then .done else .qCopyH) (context a u M t p (subCounts second c (n-order a t) 0)) :=by
  have h0:=copy_context a u M t p 4 (subCounts second c n 0) (.subtractCopy second) (.subtract second) rfl
  have he:copied a u M t 4 (subCounts second c n 0)=subCounts second c n (order a t):=by cases second <;> rfl
  rw [he] at h0
  change Runs program (5*order a t+4) _ _ _ _ at h0
  have hh:=join h0 (subtract_run second a u M t p c (order a t) n hi)
  convert hh using 1
  omega
/-- Exact physical result of the actual selected bounded product. -/
def productCounts (second : Bool) (c : Counts) : Counts :=
  if second then {c with multiplier:=0,r:=c.multiplier*c.multiplicand}
  else {c with multiplier:=0,q:=c.multiplier*c.multiplicand}
/-- Literal frozen product loops consume multiplier and retain the exact multiplicand. -/
theorem product_run (second : Bool) (a u M : Nat) (t p : List Bool) (c : Counts)
    (hz : (if second then c.r else c.q)=0) :
    ∃q≤5*(c.multiplier*(2*c.multiplicand+3)+1)+1,Runs program q (.product second)
      (context a u M t p c) (.clearMultiplicity second) (context a u M t p (productCounts second c)) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackUnaryProduct.product_run c.multiplier c.multiplicand
  refine ⟨q+1,by omega,?_⟩
  have hout:context a u M t p c (productStack second .product)=[]:=by
    cases second with
    | false=>change c.q=0 at hz;change D.unary c.q=[];rw [hz];rfl
    | true=>change c.r=0 at hz;change D.unary c.r=[];rw [hz];rfl
  apply included_call program (productStack second) (Label.multiply second) (product_injective second)
    P.code P.entry (fun _=>rfl) (.product second) (.clearMultiplicity second) rfl q
    ⟨some P.entry,none,P.contents (D.unary c.multiplier) (D.unary c.multiplicand) [] []⟩
    ⟨none,none,P.contents [] (D.unary c.multiplicand) [] (D.unary (c.multiplier*c.multiplicand))⟩ _ _ rfl rfl hr
  · constructor
    · intro k;cases k
      · rfl
      · rfl
      · rfl
      · exact hout
    · intro k _;rfl
  · constructor
    · intro k;cases second <;> cases k <;> rfl
    · intro k hk;cases second <;> rcases k with k|k
      all_goals first
        | rfl
        | rcases k with k|k
          · rfl
          · cases k <;> first
            | rfl
            | exact (hk .multiplier rfl).elim
            | exact (hk .multiplicand rfl).elim
            | exact (hk .scratch rfl).elim
            | exact (hk .product rfl).elim
/-- Physically erase the retained product operand before reusing its real bank. -/
theorem clear_multiplicity (second : Bool) (a u M : Nat) (t p : List Bool) (c : Counts) :
    Runs program (c.multiplicand+1) (.clearMultiplicity second) (context a u M t p c)
      (if second then .deltaCopyA else .rCopyM) (context a u M t p {c with multiplicand:=0}) :=by
  have h:=SemiprimeD1StackPhysicalLoops.drain program (.clearMultiplicity second)
    (if second then .deltaCopyA else .rCopyM) (aux .multiplicand) rfl (context a u M t p c) (D.unary c.multiplicand)
  have hi:Function.update (context a u M t p c) (aux .multiplicand) (D.unary c.multiplicand)=context a u M t p c:=
    Function.update_eq_self _ _
  have ho:Function.update (context a u M t p c) (aux .multiplicand) []=context a u M t p {c with multiplicand:=0}:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k <;> cases k <;> rfl
  rw [hi,ho,D.unary,List.length_replicate] at h
  exact h
/-- One paid literal successor produces the original (a+1) product operand. -/
theorem plus_one (a u M : Nat) (t p : List Bool) (c : Counts) :
    Runs program 1 .plusOne (context a u M t p c) (.product true)
      (context a u M t p {c with multiplicand:=c.multiplicand+1}) :=by
  apply one_base program .plusOne (.product true) (.push (aux .multiplicand) true (.product true)) _ _ rfl
  · rfl
  · funext k;rcases k with k|k
    · rfl
    · rcases k with k|k <;> cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataProducts
