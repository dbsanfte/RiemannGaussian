/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScaleLeafSqrt
/-! # Actual acquired-root divisor, exact leaf quotient and literal final +1 -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
namespace RiemannGaussian.SemiprimeD1StackRootScaleLeafDivision
open SemiprimeD1StackRootScaleLeaf SemiprimeD1StackRootScaleLeafPrimitives
open SemiprimeD1StackProcedureTrace
/-- All old fields, scale/root/leaf outputs, and the exact fresh divider fields. -/
def context (old : R.Stack→List Bool) (s k leaf n d q r : Nat) : Stack→List Bool :=
  store old (D.contents (D.unary n) (D.unary d) [] [] (D.unary q) (D.unary r))
    (metadata (D.unary s) (D.unary k) (D.unary leaf) [])
/-- Real quotient cleanup and transfer includes every actual remainder/quotient cell. -/
theorem cleanup (old : R.Stack→List Bool) (s k d q r : Nat) :
    Runs program ((r+1)+(2*q+1)) .clearRemainder (context old s k 0 0 d q r)
      .plusOne (context old s k q 0 d 0 0) :=by
  have h0:=SemiprimeD1StackPhysicalLoops.drain program .clearRemainder .moveLeaf (divStack .remainder)
    rfl (context old s k 0 0 d q r) (D.unary r)
  have hi:Function.update (context old s k 0 0 d q r) (divStack .remainder) (D.unary r)=context old s k 0 0 d q r:=Function.update_eq_self _ _
  have ho:Function.update (context old s k 0 0 d q r) (divStack .remainder) []=context old s k 0 0 d q 0:=by
    funext j;rcases j with j|j
    · rfl
    · rcases j with j|j
      · cases j <;> rfl
      · rfl
  rw [hi,ho] at h0
  have h1:=SemiprimeD1StackPhysicalLoops.move_unary program .moveLeaf .pushLeaf .plusOne
    (divStack .quotient) (aux .leaf) (by decide) rfl rfl (context old s k 0 0 d 0 0) q []
  have he0:Function.update (Function.update (context old s k 0 0 d 0 0) (aux .leaf) [])
      (divStack .quotient) (D.unary q)=context old s k 0 0 d q 0:=by
    funext j;rcases j with j|j
    · rfl
    · rcases j with j|j
      · cases j <;> rfl
      · cases j <;> rfl
  have he1:Function.update (Function.update (context old s k 0 0 d 0 0) (aux .leaf) (D.unary q++[]))
      (divStack .quotient) []=context old s k q 0 d 0 0:=by
    funext j;rcases j with j|j
    · rfl
    · rcases j with j|j
      · cases j <;> rfl
      · cases j <;> first | rfl | (change D.unary q++[]=D.unary q;exact List.append_nil _)
  dsimp only [D.unary] at he0 he1
  rw [he0,he1] at h1
  simpa only [D.unary,List.length_replicate] using join h0 h1
/-- The complete final arithmetic stage copies the ACTUAL root, pushes the
actual denominator +1, executes the frozen real divider, and writes leaf +1. -/
theorem leaf_stage (old : R.Stack→List Bool) (s k : Nat) :
    ∃t≤120*(s+k+2),Runs program t .copyRoot
      (SemiprimeD1StackRootScaleLeafSqrt.result old (D.unary s) k) .done
      (context old s k (s/(k+1)+1) 0 (k+1) 0 0) :=by
  let base:=context old s k 0 0 0 0 0
  let copiedRoot:=context old s k 0 0 k 0 0
  let seeded:=context old s k 0 0 (k+1) 0 0
  have h0:=copy_call 3 .copyRoot .seedDenominator rfl base rfl
  have hl0:(base (copySource 3)).length=k:=by
    change (List.replicate k true).length=k
    simp only [List.length_replicate]
  rw [hl0] at h0
  have he0:Function.update base (copyTarget 3) (base (copySource 3)++base (copyTarget 3))=copiedRoot:=by
    funext j;rcases j with j|j
    · rfl
    · rcases j with j|j
      · cases j <;> first | rfl | (change D.unary k++[]=D.unary k;exact List.append_nil _)
      · cases j <;> rfl
  rw [he0] at h0
  have h1:=push .seedDenominator .copyScale (divStack .divisor) copiedRoot rfl
  have he1:Function.update copiedRoot (divStack .divisor) (true::copiedRoot (divStack .divisor))=seeded:=by
    funext j;rcases j with j|j
    · rfl
    · rcases j with j|j
      · cases j <;> rfl
      · cases j <;> rfl
  rw [he1] at h1
  have h2:=copy_call 4 .copyScale .divide rfl seeded rfl
  have hl2:(seeded (copySource 4)).length=s:=by
    change (List.replicate s true).length=s
    simp only [List.length_replicate]
  rw [hl2] at h2
  have he2:Function.update seeded (copyTarget 4) (seeded (copySource 4)++seeded (copyTarget 4))=clean base s (k+1):=by
    funext j;rcases j with j|j
    · rfl
    · rcases j with j|j
      · cases j <;> first | rfl | (change D.unary s++[]=D.unary s;exact List.append_nil _)
      · cases j <;> rfl
  rw [he2] at h2
  obtain ⟨td,ht,hd⟩:=division_call .divide .clearRemainder rfl base s (k+1)
  have he3:withDiv base (D.contents [] (D.unary (k+1)) [] [] (D.unary (s/(k+1))) (D.unary (s%(k+1))))=
      context old s k 0 0 (k+1) (s/(k+1)) (s%(k+1)):=by
    funext j;rcases j with j|j
    · rfl
    · rcases j with j|j <;> rfl
  rw [he3] at hd
  have hc:=cleanup old s k (k+1) (s/(k+1)) (s%(k+1))
  have h3:=push .plusOne .done (aux .leaf) (context old s k (s/(k+1)) 0 (k+1) 0 0) rfl
  have he4:Function.update (context old s k (s/(k+1)) 0 (k+1) 0 0) (aux .leaf)
      (true::context old s k (s/(k+1)) 0 (k+1) 0 0 (aux .leaf))=
      context old s k (s/(k+1)+1) 0 (k+1) 0 0:=by
    funext j;rcases j with j|j
    · rfl
    · rcases j with j|j
      · cases j <;> rfl
      · cases j <;> rfl
  rw [he4] at h3
  have h:=join (join (join (join (join h0 h1) h2) hd) hc) h3
  refine ⟨(((((5*k+4)+1)+(5*s+4))+td)+((s%(k+1)+1)+(2*(s/(k+1))+1)))+1,?_,h⟩
  have hm:s%(k+1)<k+1:=Nat.mod_lt s (by omega)
  have hq:s/(k+1)≤ s:=Nat.div_le_self s (k+1)
  omega
end RiemannGaussian.SemiprimeD1StackRootScaleLeafDivision
