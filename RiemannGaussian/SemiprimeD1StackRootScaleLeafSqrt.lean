/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScaleLeafSubtract
import RiemannGaussian.SemiprimeD1StackRootScaleLeafArithmetic
/-! # Exact integer square root by executed physical odd subtraction -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
namespace RiemannGaussian.SemiprimeD1StackRootScaleLeafSqrt
open SemiprimeD1StackRootScaleLeaf SemiprimeD1StackRootScaleLeafPrimitives
open SemiprimeD1StackRootScaleLeafArithmetic SemiprimeD1StackProcedureTrace
/-- Fixed-bank view of the actual remaining word, retained odd counter and copied block. -/
def context (old : R.Stack→List Bool) (s : List Bool) (n d c : Nat) (rootWord : List Bool) : Stack→List Bool :=
  store old (D.contents (D.unary n) (D.unary d) (D.unary c) [] [] []) (metadata s rootWord [] [])
/-- The mathematical invariant indexes ONLY physical unary words, never control. -/
def data (old : R.Stack→List Bool) (s : List Bool) (n k c : Nat) : Stack→List Bool :=
  context old s n (odd k) c (D.unary k)
/-- Exact stop state after both odd-work words have really been erased. -/
def result (old : R.Stack→List Bool) (s : List Bool) (k : Nat) : Stack→List Bool :=
  context old s 0 0 0 (D.unary k)
/-- Three literal pushes increment the actual root by one and actual odd block by two. -/
theorem advance (old : R.Stack→List Bool) (s : List Bool) (n k : Nat) :
    Runs program 3 (.advance 0) (data old s n k 0) .squareCopy (data old s n (k+1) 0) :=by
  let first:=context old s n (odd k) 0 (D.unary (k+1))
  let second:=context old s n (odd k+1) 0 (D.unary (k+1))
  let third:=context old s n (odd k+2) 0 (D.unary (k+1))
  have h0:=push (.advance 0) (.advance 1) (aux .root) (data old s n k 0) rfl
  have he0:Function.update (data old s n k 0) (aux .root) (true::data old s n k 0 (aux .root))=first:=by
    funext j;rcases j with j|j
    · rfl
    · rcases j with j|j
      · cases j <;> rfl
      · cases j <;> rfl
  rw [he0] at h0
  have h1:=push (.advance 1) (.advance 2) (divStack .divisor) first rfl
  have he1:Function.update first (divStack .divisor) (true::first (divStack .divisor))=second:=by
    funext j;rcases j with j|j
    · rfl
    · rcases j with j|j
      · cases j <;> rfl
      · cases j <;> rfl
  rw [he1] at h1
  have h2:=push (.advance 2) .squareCopy (divStack .divisor) second rfl
  have he2:Function.update second (divStack .divisor) (true::second (divStack .divisor))=third:=by
    funext j;rcases j with j|j
    · rfl
    · rcases j with j|j
      · cases j <;> rfl
      · cases j <;> rfl
  rw [he2] at h2
  have hv:odd k+2=odd (k+1):=by unfold odd;omega
  have he3:third=data old s n (k+1) 0:=by
    change context old s n (odd k+2) 0 (D.unary (k+1))=_
    rw [hv]
    rfl
  rw [he3] at h2
  exact join (join h0 h1) h2
/-- Copying the retained actual odd counter pays restoration and preserves
ALL15 original root-cache fields and all accumulated scale/root/output words. -/
theorem copy_odd (old : R.Stack→List Bool) (s : List Bool) (n k : Nat) :
    Runs program (5*odd k+4) .squareCopy (data old s n k 0) .popOdd (data old s n k (odd k)) :=by
  have h:=copy_call 2 .squareCopy .popOdd rfl (data old s n k 0) rfl
  have hl:(data old s n k 0 (copySource 2)).length=odd k:=by
    change (List.replicate (odd k) true).length=odd k
    simp only [List.length_replicate]
  rw [hl] at h
  have he:Function.update (data old s n k 0) (copyTarget 2)
      (data old s n k 0 (copySource 2)++data old s n k 0 (copyTarget 2))=data old s n k (odd k):=by
    funext j;rcases j with j|j
    · rfl
    · rcases j with j|j
      · cases j <;> first | rfl | (change D.unary (odd k)++[]=D.unary (odd k);exact List.append_nil _)
      · cases j <;> rfl
  rw [he] at h
  exact h
/-- Both success and final failure are REAL physical branches. The only square
root is in the proved postcondition, never in the finite instruction table. -/
theorem square_root (old : R.Stack→List Bool) (s : List Bool) (n k : Nat) :
    ∃t≤100000*(2*n+k+1)^2,Runs program t .squareCopy (data old s n k 0)
      .copyRoot (result old s (Nat.sqrt (n+k^2))) :=by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih=>
    have hc:=copy_odd old s n k
    let base:=store old (fun _=>[]) (metadata s (D.unary k) [] [])
    have hview (m c:Nat):SemiprimeD1StackRootScaleLeafSubtract.data base m (odd k) c=data old s m k c:=by
      funext j;rcases j with j|j
      · rfl
      · rcases j with j|j <;> rfl
    by_cases hfit:odd k≤ n
    · have hs:=SemiprimeD1StackRootScaleLeafSubtract.fits base (odd k) n (odd k) hfit
      rw [hview n (odd k),hview (n-odd k) 0] at hs
      have ha:=advance old s (n-odd k) k
      have hsmall:n-odd k<n:=subtract_lt n k hfit
      obtain ⟨tr,ht,hr⟩:=ih (n-odd k) hsmall (k+1)
      have h:=join (join (join hc hs) ha) hr
      have hv:(n-odd k)+(k+1)^2=n+k^2:=subtract_invariant n k hfit
      rw [hv] at h
      refine ⟨((5*odd k+4)+(2*odd k+1))+3+tr,?_,h⟩
      have hp:2*(n-odd k)+(k+1)+1+1≤2*n+k+1:=by have h:=potential_decreases n k hfit;omega
      have hsq: (2*(n-odd k)+(k+1)+1+1)^2≤(2*n+k+1)^2:=Nat.pow_le_pow_left hp 2
      unfold odd at *
      nlinarith
    · have hshort:n<odd k:=by omega
      have hs:=SemiprimeD1StackRootScaleLeafSubtract.short base n (odd k) (odd k) hshort
      rw [hview n (odd k)] at hs
      have hd:=SemiprimeD1StackRootScaleLeafSubtract.clear base (odd k) (odd k-n-1)
      have h:=join (join hc hs) hd
      have he:SemiprimeD1StackRootScaleLeafSubtract.data base 0 0 0=result old s k:=by
        funext j;rcases j with j|j
        · rfl
        · rcases j with j|j <;> rfl
      rw [he] at h
      have hv:Nat.sqrt (n+k^2)=k:=stop_exact n k hshort
      rw [hv]
      refine ⟨(5*odd k+4)+(2*n+2)+((odd k-n-1+1)+(odd k+1)),?_,h⟩
      have hp:1≤2*n+k+1:=by omega
      have hsq:2*n+k+1≤(2*n+k+1)^2:=by simpa only [pow_one] using Nat.pow_le_pow_right hp (by decide : 1≤2)
      have hle:odd k-n-1≤ odd k:=by omega
      unfold odd at *
      nlinarith
end RiemannGaussian.SemiprimeD1StackRootScaleLeafSqrt
