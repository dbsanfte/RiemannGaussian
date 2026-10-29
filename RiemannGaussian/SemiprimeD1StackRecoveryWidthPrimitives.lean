/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWidth
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Actual preserving copies and paid byte scans/drains -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWidthPrimitives
open SemiprimeD1StackRecoveryWidth SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Exact chronological source-fragment composition preserves every real outer return. -/
theorem join {m n:Nat} {pc mid next:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between next after) :
    Runs program (m+n) pc before next after :=runs_trans program m n pc mid next before between after h g
/-- Actual complete preserving copy, including both restoration loops and its real caller return. -/
theorem copy_call (what:Copy) (pc next:Label)
    (hc:program pc=.call (.copier what 0) next) (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (copyStack what 0)=xs) (hy:before (copyStack what 1)=ys) (hs:before (copyStack what 2)=[]) :
    Runs program (5*xs.length+4) pc before next
      (Function.update before (copyStack what 1) (xs++ys)) :=by
  let start:=SemiprimeD1StackCopy.state 0 none xs ys []
  let stop:=SemiprimeD1StackCopy.done xs (xs++ys)
  have hi:Link.DataRel (copyStack what) before start.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update (copyStack what) (copy_injective what) before start.store before hi (1:Fin 3) (xs++ys)
  have he:Function.update start.store 1 (xs++ys)=stop.store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program (copyStack what) (Label.copier what) (copy_injective what) SemiprimeD1StackCopy.code 0
    (fun _=>rfl) pc next hc (5*xs.length+3) start stop before _ rfl rfl
    (SemiprimeD1StackCopy.copy_words xs ys none) hi ho
/-- One literal local push preserves the entire other physical bank and all real outer returns. -/
theorem push_run (pc:Label) (next:Label) (k:Stack) (b:Bool) (before:Stack→List Bool)
    (hc:program pc=.base (.push k b next)) :
    Runs program 1 pc before next (Function.update before k (b::before k)) :=
  one_base program _ _ _ _ _ hc rfl rfl
/-- One literal local pop consumes only the actual physical Boolean head. -/
theorem pop_run (pc:Label) (empty low high:Label) (k:Stack) (before:Stack→List Bool) (xs:List Bool)
    (hc:program pc=.base (.pop k empty low high)) (hx:before k=xs) :
    Runs program 1 pc before (SemiprimeD1StackBytecode.choose empty low high xs.head?) (Function.update before k xs.tail) :=by
  apply one_base program pc _ (.pop k empty low high) before _ hc
  · simp only [SemiprimeD1StackBytecode.execute,hx]
  · simp only [SemiprimeD1StackBytecode.execute,hx]
/-- Every actual source peek preserves the entire acquired word. -/
theorem peek_run (pc:Label) (empty low high:Label) (k:Stack) (before:Stack→List Bool) (xs:List Bool)
    (hc:program pc=.base (.peek k empty low high)) (hx:before k=xs) :
    Runs program 1 pc before (SemiprimeD1StackBytecode.choose empty low high xs.head?) before :=by
  apply one_base program pc _ (.peek k empty low high) before before hc
  · simp only [SemiprimeD1StackBytecode.execute,hx]
  · rfl
/-- Every quotient/remainder/GCD/magnitude cleanup actually visits every byte and its final empty branch. -/
theorem drain_loop (pc:Label) (next:Label) (k:Stack)
    (hc:program pc=.base (.pop k next pc pc)) (before:Stack→List Bool) (xs:List Bool) (hx:before k=xs) :
    Runs program (xs.length+1) pc before next (Function.update before k []) :=by
  induction xs generalizing before with
  | nil=>exact pop_run pc next pc pc k before [] hc hx
  | cons b xs ih=>
    have h0:=pop_run pc next pc pc k before (b::xs) hc hx
    have h1:=ih (Function.update before k xs) (Function.update_self _ _ _)
    have hh:=join (by cases b <;> exact h0) h1
    simpa only [List.length_cons,Function.update_idem,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
/-- One literal static jump advances fixed source syntax without touching any actual word. -/
theorem jump_run (pc next:Label) (before:Stack→List Bool) (hc:program pc=.base (.jump next)) :
    Runs program 1 pc before next before:=one_base program _ _ _ _ _ hc rfl rfl
/-- Real unary multiplication consumes every actual left marker, preserves the exact directly aliased right word,
and emits the actual product markers into its fresh physical destination. -/
theorem product_call (g:W.Gate) (before:Stack→List Bool) (m d:List Bool)
    (hm:before (productStack g .multiplier)=m) (hd:before (productStack g .multiplicand)=d)
    (hs:before (productStack g .scratch)=[]) (ho:before (productStack g .product)=[]) :
    ∃q≤5*(m.length*(2*d.length+3)+1)+1,Runs program q (.multiply g) before (nextGate g)
      (Function.update (Function.update before (aux .multiplier) []) (reg g)
        (SemiprimeD1StackUnaryDivmod.unary (m.length*d.length))) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackUnaryProductRaw.product_run m d
  let start:SemiprimeD1StackBytecode.State P.Stack P.Label:=⟨some P.entry,none,P.contents m d [] []⟩
  let stop:SemiprimeD1StackBytecode.State P.Stack P.Label:=⟨none,none,P.contents [] d [] (SemiprimeD1StackUnaryDivmod.unary (m.length*d.length))⟩
  have hin:Link.DataRel (productStack g) before start.store before:=by
    constructor
    · intro k;cases k
      · exact hm
      · exact hd
      · exact hs
      · exact ho
    · intro k _;rfl
  have h0:=Link.data_update (productStack g) (product_injective g) before start.store before hin .multiplier []
  have h1:=Link.data_update (productStack g) (product_injective g) before _ _ h0 .product
    (SemiprimeD1StackUnaryDivmod.unary (m.length*d.length))
  have he:Function.update (Function.update start.store .multiplier []) .product
      (SemiprimeD1StackUnaryDivmod.unary (m.length*d.length))=stop.store:=by
    funext k;cases k <;> rfl
  rw [he] at h1
  refine ⟨q+1,by omega,?_⟩
  exact included_call program (productStack g) (Label.product g) (product_injective g) P.code P.entry
    (fun _=>rfl) (.multiply g) (nextGate g) rfl q start stop before _ rfl rfl hr hin h1
end RiemannGaussian.SemiprimeD1StackRecoveryWidthPrimitives
