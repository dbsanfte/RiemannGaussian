/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScheduleLoops
/-! # Seventeen real halving calls and physical root-level delivery -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackRootScheduleHalves
open SemiprimeD1StackRootSchedule SemiprimeD1StackRootSchedulePrimitives
open SemiprimeD1StackRootScheduleLoops SemiprimeD1StackProcedureTrace
/-- The bounded remaining count appears only in proof-side static label indexing. -/
def index (remaining : Nat) (h : remaining≤17) : Fin 18 :=⟨17-remaining,by omega⟩
/-- Real transfer of the final quotient into the retained root-level word. -/
theorem finish_levels (base : Stack→List Bool) (n : Nat) :
    Runs program (2*n+1) (.halve 17) (clean base n) .copyFirst
      (Function.update (clean base 0) (aux .levels) (D.unary n++base (aux .levels))) := by
  have h:=SemiprimeD1StackPhysicalLoops.move_unary program (.halve 17) .pushLevel .copyFirst
    (divStack .input) (aux .levels) (by decide) rfl rfl (clean base 0) n (base (aux .levels))
  have he0:Function.update (Function.update (clean base 0) (aux .levels) (base (aux .levels)))
      (divStack .input) (D.unary n)=clean base n:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · cases k <;> simp [clean,withDiv,D.contents,D.unary,aux,divStack,Function.update]
      · cases k <;> simp [clean,withDiv,aux,divStack,Function.update]
  have he1:Function.update (Function.update (clean base 0) (aux .levels)
      (D.unary n++base (aux .levels))) (divStack .input) []=
      Function.update (clean base 0) (aux .levels) (D.unary n++base (aux .levels)):=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · cases k <;> simp [clean,withDiv,D.contents,D.unary,aux,divStack,Function.update]
      · cases k <;> simp [clean,withDiv,aux,divStack,Function.update]
  dsimp only [D.unary] at he0 he1
  rw [he0,he1] at h
  exact h
/-- Every one of the fixed seventeen divisions is an actual included call;
all discarded remainders and copied quotient cells are physically paid. -/
theorem halves (base : Stack→List Bool) (remaining : Nat) (hr : remaining≤17) (n : Nat) :
    ∃t≤10000*(n+1)*(remaining+1),Runs program t (.halve (index remaining hr))
      (clean base n) .copyFirst
      (Function.update (clean base 0) (aux .levels) (D.unary (n/2^remaining)++base (aux .levels))) := by
  induction remaining generalizing n with
  | zero=>
    refine ⟨2*n+1,by omega,?_⟩
    have he:index 0 hr=(17:Fin 18):=by apply Fin.ext;rfl
    rw [he,pow_zero,Nat.div_one]
    exact finish_levels base n
  | succ r ih=>
    have hlt:17-(r+1)<17:=by omega
    let p:Fin 17:=⟨17-(r+1),hlt⟩
    have hc:program (.halve (index (r+1) hr))=.call (.division Div.entry) (.clearRemainder (.half p)):=by
      simp [program,index,p,show 16-r<17 by omega]
    obtain ⟨td,hd,hdiv⟩:=division_call (.halve (index (r+1) hr)) (.clearRemainder (.half p)) hc base n
    have hm:=cleanup_move (.half p) base (n/2) (n%2)
    have hp:afterMove (.half p)=.halve (index r (by omega)):=by
      apply congrArg Label.halve
      apply Fin.ext
      dsimp [afterMove,p,index]
      omega
    rw [hp] at hm
    obtain ⟨tr,ht,hrec⟩:=ih (by omega) (n/2)
    have h:=join (join hdiv hm) hrec
    have hq:(n/2)/2^r=n/2^(r+1):=by rw [Nat.div_div_eq_div_mul,pow_succ']
    rw [hq] at h
    refine ⟨td+((n%2+1)+(2*(n/2)+1))+tr,?_,h⟩
    have hm2:n%2<2:=Nat.mod_lt n (by decide)
    have hqn:n/2≤n:=Nat.div_le_self n 2
    have ht':tr≤10000*(n+1)*(r+1):=ht.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
    nlinarith
end RiemannGaussian.SemiprimeD1StackRootScheduleHalves
