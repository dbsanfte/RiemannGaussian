/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWidthEncoding
import RiemannGaussian.SemiprimeD1StackRecoveryWidthPrimitives
/-! # Exact actual literal, sum and product gates of the fixed width source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWidthGates
open SemiprimeD1StackRecoveryWidth SemiprimeD1StackRecoveryWidthEncoding
open SemiprimeD1StackRecoveryWidthPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeD1StackUnaryDivmod (unary unary_add unary_succ unary_bump)
/-- Every literal token is an actual push at a fixed finite constant-code location. -/
theorem literal_remaining (n:Nat) (k:W.Literal) (i:Fin 20) (before:Stack→List Bool)
    (hn:i.val+n=W.literalValue k) (hpos:0<n) :
    Runs program n (.constant k i) before (nextGate (W.literalGate k))
      (Function.update before (reg (W.literalGate k)) (unary n++before (reg (W.literalGate k)))) :=by
  induction n generalizing i before with
  | zero=>omega
  | succ n ih=>
    cases n with
    | zero=>
      have hc:¬i.val+1<W.literalValue k:=by omega
      have h:=push_run (.constant k i) (nextGate (W.literalGate k)) (reg (W.literalGate k)) true before
        (by simp only [program,dite_eq_right hc])
      exact h
    | succ n=>
      have hc:i.val+1<W.literalValue k:=by omega
      let j:Fin 20:=⟨i.val+1,by have hb:=(SemiprimeD1StackRecoveryWidthCircuit.literal_bounds k).2;omega⟩
      have h0:=push_run (.constant k i) (.constant k j) (reg (W.literalGate k)) true before
        (by simp only [program,dite_eq_left hc];rfl)
      have h1:=ih j (Function.update before (reg (W.literalGate k)) (true::before (reg (W.literalGate k))))
        (by dsimp [j];omega) (by omega)
      simp only [Function.update_self,Function.update_idem] at h1
      have h:=join h0 h1
      have he:unary (n+1)++true::before (reg (W.literalGate k))=
          unary (n+1+1)++before (reg (W.literalGate k)):=by
        simpa only [unary_succ,List.cons_append] using unary_bump (n+1) (before (reg (W.literalGate k)))
      rw [he] at h
      convert h using 1
      omega
/-- Actual source-gate budget uses only physical literal loads, copy lengths and the real unary-product bound. -/
def gateBound (g:W.Gate) (a M N:Nat) :Nat:=match W.node g with
  | .literal k=>W.literalValue k+1
  | .add l r=>5*(V.sourceValue a M N l+V.sourceValue a M N r)+8
  | .mul l r=>(5*V.sourceValue a M N l+4)+5*(V.sourceValue a M N l*(2*V.sourceValue a M N r+3)+1)+1
/-- A real literal gate starts from its actually empty fresh destination and leaves exactly one acquired register. -/
theorem literal_gate (g:W.Gate) (k:W.Literal) (hg:W.node g=.literal k) (a M N:Nat) :
    Runs program (gateBound g a M N) (.gate g) (bank (atGate g.val a M N)) (nextGate g)
      (bank (atGate (g.val+1) a M N)) :=by
  have hdest:=SemiprimeD1StackRecoveryWidthCircuit.node_literal g k hg
  have h0:=jump_run (.gate g) (.constant k 0) (bank (atGate g.val a M N)) (by simp only [program,hg])
  have h1:=literal_remaining (W.literalValue k) k 0 (bank (atGate g.val a M N)) (by change 0+W.literalValue k=_;omega)
    (SemiprimeD1StackRecoveryWidthCircuit.literal_bounds k).1
  rw [←hdest] at h1
  rw [fresh,List.append_nil] at h1
  have hv:V.value g a M N=W.literalValue k:=by
    rw [SemiprimeD1StackRecoveryWidthPolynomial.gate_formula,hg]
  rw [←hv,gate_write] at h1
  have h:=join h0 h1
  unfold gateBound
  rw [hg]
  dsimp only
  convert h using 1
  omega
/-- Every actual sum gate preserves both acquired operands and appends their marker bytes through TWO real copies. -/
theorem add_gate (g:W.Gate) (l r:W.Source) (hg:W.node g=.add l r) (a M N:Nat) :
    Runs program (gateBound g a M N) (.gate g) (bank (atGate g.val a M N)) (nextGate g)
      (bank (atGate (g.val+1) a M N)) :=by
  let before:=bank (atGate g.val a M N)
  have hp:isProduct g=false:=by simp only [isProduct,hg]
  have hl:=source_ready g (W.left g) (SemiprimeD1StackRecoveryWidthCircuit.left_earlier g) a M N
  have hr:=source_ready g (W.right g) (SemiprimeD1StackRecoveryWidthCircuit.right_earlier g) a M N
  simp only [SemiprimeD1StackRecoveryWidthCircuit.left,hg] at hl
  simp only [SemiprimeD1StackRecoveryWidthCircuit.right,hg] at hr
  have htarget:copyStack (.left g) 1=reg g:=by simp [copyStack,copyTarget,hp]
  have h0:=copy_call (.left g) (.gate g) (.addRight g) (by simp only [program,hg]) before
    (unary (V.sourceValue a M N l)) [] (by
      change bank (atGate g.val a M N) (sourceStack (W.left g))=_
      rw [show W.left g=l by simp only [SemiprimeD1StackRecoveryWidthCircuit.left,hg]]
      exact hl) (by rw [htarget];exact fresh g a M N) rfl
  rw [htarget,List.append_nil] at h0
  have hright:before (sourceStack r)=unary (V.sourceValue a M N r):=hr
  have hne:sourceStack r≠reg g:=source_reg g r (by simpa only [SemiprimeD1StackRecoveryWidthCircuit.right,hg] using
    SemiprimeD1StackRecoveryWidthCircuit.right_earlier g)
  have h1:=copy_call (.right g) (.addRight g) (nextGate g) rfl
    (Function.update before (reg g) (unary (V.sourceValue a M N l)))
    (unary (V.sourceValue a M N r)) (unary (V.sourceValue a M N l))
    (by change Function.update before (reg g) _ (sourceStack (W.right g))=_
        rw [show W.right g=r by simp only [SemiprimeD1StackRecoveryWidthCircuit.right,hg],Function.update_of_ne hne]
        exact hright) (Function.update_self _ _ _) (by
      change Function.update before (reg g) _ (aux .copyScratch)=[]
      rfl)
  change Runs _ _ _ _ _ (Function.update (Function.update before (reg g) _) (reg g) _) at h1
  rw [Function.update_idem] at h1
  have hv:V.value g a M N=V.sourceValue a M N l+V.sourceValue a M N r:=by
    rw [SemiprimeD1StackRecoveryWidthPolynomial.gate_formula,hg]
  have he:unary (V.sourceValue a M N r)++unary (V.sourceValue a M N l)=unary (V.value g a M N):=by
    rw [←unary_add,hv,Nat.add_comm]
  rw [he] at h1
  change Runs _ _ _ _ _ (Function.update (bank (atGate g.val a M N)) (reg g) (unary (V.value g a M N))) at h1
  rw [gate_write] at h1
  have h:=join h0 h1
  simp only [unary,List.length_replicate] at h
  unfold gateBound
  rw [hg]
  dsimp only
  convert h using 1
  omega
/-- Every actual product gate pays its acquired multiplier copy, real preserving product procedure and real return. -/
theorem mul_gate (g:W.Gate) (l r:W.Source) (hg:W.node g=.mul l r) (a M N:Nat) :
    ∃q≤ gateBound g a M N,Runs program q (.gate g) (bank (atGate g.val a M N)) (nextGate g)
      (bank (atGate (g.val+1) a M N)) :=by
  have hp:isProduct g=true:=by simp only [isProduct,hg]
  have hl:=source_ready g (W.left g) (SemiprimeD1StackRecoveryWidthCircuit.left_earlier g) a M N
  have hr:=source_ready g (W.right g) (SemiprimeD1StackRecoveryWidthCircuit.right_earlier g) a M N
  simp only [SemiprimeD1StackRecoveryWidthCircuit.left,hg] at hl
  simp only [SemiprimeD1StackRecoveryWidthCircuit.right,hg] at hr
  have htarget:copyStack (.left g) 1=aux .multiplier:=by simp [copyStack,copyTarget,hp]
  have h0:=copy_call (.left g) (.gate g) (.multiply g) (by simp only [program,hg])
    (bank (atGate g.val a M N)) (unary (V.sourceValue a M N l)) [] (by
      change bank (atGate g.val a M N) (sourceStack (W.left g))=_
      rw [show W.left g=l by simp only [SemiprimeD1StackRecoveryWidthCircuit.left,hg]]
      exact hl) (by rw [htarget];rfl) rfl
  rw [htarget,List.append_nil,update_multiplier] at h0
  let middle:Words:={atGate g.val a M N with multiplier:=unary (V.sourceValue a M N l)}
  obtain ⟨q,hq,h1⟩:=product_call g (bank middle) (unary (V.sourceValue a M N l)) (unary (V.sourceValue a M N r))
    rfl (by
      change bank middle (sourceStack (W.right g))=_
      rw [show W.right g=r by simp only [SemiprimeD1StackRecoveryWidthCircuit.right,hg]]
      have hne:sourceStack r≠aux .multiplier:=(source_work r).1
      have he:bank middle=Function.update (bank (atGate g.val a M N)) (aux .multiplier) (unary (V.sourceValue a M N l)):=
        (update_multiplier _ _).symm
      rw [he,Function.update_of_ne hne]
      exact hr) rfl (by exact fresh g a M N)
  rw [update_multiplier] at h1
  change Runs _ _ _ _ _ (Function.update (bank (atGate g.val a M N)) (reg g)
    (unary ((unary (V.sourceValue a M N l)).length*(unary (V.sourceValue a M N r)).length))) at h1
  simp only [unary,List.length_replicate] at h0 h1 hq
  have hv:V.value g a M N=V.sourceValue a M N l*V.sourceValue a M N r:=by
    rw [SemiprimeD1StackRecoveryWidthPolynomial.gate_formula,hg]
  change Runs _ _ _ _ _ (Function.update (bank (atGate g.val a M N)) (reg g) (unary (V.sourceValue a M N l*V.sourceValue a M N r))) at h1
  rw [←hv,gate_write] at h1
  refine ⟨_,?_,join h0 h1⟩
  unfold gateBound
  rw [hg]
  dsimp only
  omega
/-- Every fixed gate executes actual byte instructions and leaves its exact next physical prefix. -/
theorem gate_run (g:W.Gate) (a M N:Nat) :
    ∃q≤ gateBound g a M N,Runs program q (.gate g) (bank (atGate g.val a M N)) (nextGate g)
      (bank (atGate (g.val+1) a M N)) :=by
  cases hg:W.node g with
  | literal k=>exact ⟨_,le_rfl,literal_gate g k hg a M N⟩
  | add l r=>exact ⟨_,le_rfl,add_gate g l r hg a M N⟩
  | mul l r=>exact mul_gate g l r hg a M N
end RiemannGaussian.SemiprimeD1StackRecoveryWidthGates
