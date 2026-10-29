/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDescriptorRecordPrimitives
import RiemannGaussian.SemiprimeD1StackDescriptorRecordLoadView
import RiemannGaussian.SemiprimeD1StackProcedureReturns
/-! # Actual complete physical descriptor-to-template load and real return -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackDescriptorRecordLoad
open SemiprimeD1StackDescriptorRecord SemiprimeD1StackDescriptorRecordPrimitives
open SemiprimeD1StackDescriptorRecordLoadView SemiprimeD1StackProcedureTrace SemiprimeD1StackProcedureReturns
variable {K L : Type} [DecidableEq K] [Fintype K] (s : T.Static K L) (sourceMap : K→Option (Fin 6))
/-- Every target payload, real EOF, selected copy and call/return is paid. -/
def loadUnit (d : Stack K→List Bool) : Nat :=6*inventory d+5
/-- Each field is physically drained before a selected preserving copy, while
unselected fields remain physically empty without a replacement data write. -/
theorem field_run (d : Stack K→List Bool) (hs : d scratch=[]) (p : Fin s.roles.length) :
    ∃t≤loadUnit d,Runs (program s sourceMap) t (.inl (.load ⟨p.val,by omega⟩))
      (loadPrefix s sourceMap d p.val) (loadNext s p) (loadPrefix s sourceMap d (p.val+1)) := by
  let before:=loadPrefix s sourceMap d p.val
  let target:=templateStack (T.role s p)
  let cleared:=Function.update before target []
  have h0:=drain s sourceMap (.inl (.load ⟨p.val,by omega⟩)) (.inl (.copy p)) target
    (by simp only [program,dite_eq_left p.isLt];rfl) before
  obtain ⟨u,hu,h1⟩ : ∃u≤5*inventory d+4,Runs (program s sourceMap) u (.inl (.copy p))
      cleared (loadNext s p) (loadPrefix s sourceMap d (p.val+1)) := by
    cases hm:sourceMap (T.role s p) with
    | none=>
      have hstep:cleared=loadPrefix s sourceMap d (p.val+1):=by
        simpa only [selected,hm,Option.elim_none] using loadPrefix_step s sourceMap d p
      refine ⟨1,by omega,?_⟩
      rw [←hstep]
      apply one_base (program s sourceMap) (.inl (.copy p)) (loadNext s p)
        (.jump (loadNext s p)) cleared cleared (by simp only [program,hm]) <;> rfl
    | some i=>
      have hcall:program s sourceMap (.inl (.copy p))=.call (copyLabel p 0) (loadNext s p):=by
        simp only [program,hm]
      have h1:=copy_call s sourceMap p (.inl (.copy p)) (loadNext s p) hcall cleared
        (by change (Function.update before target []) target=[];exact Function.update_self _ _ _)
        (by
          change (Function.update before target []) scratch=[]
          rw [Function.update_of_ne (by simp [target,scratch,templateStack,recordStack,R.tableStack,T.template])]
          exact hs)
      have hword:cleared (copyStack s sourceMap p 0)=d (source i):=by
        change (Function.update before target []) (source ((sourceMap (T.role s p)).getD 0))=_
        rw [Function.update_of_ne (by simp [target,source,templateStack,recordStack,R.tableStack,T.template])]
        simp only [hm,Option.getD_some]
        rfl
      rw [hword] at h1
      have hstep:Function.update cleared (copyStack s sourceMap p 1) (d (source i))=
          loadPrefix s sourceMap d (p.val+1):=by
        change Function.update (Function.update before target []) target (d (source i))=_
        rw [Function.update_idem]
        simpa only [selected,hm,Option.elim_some] using loadPrefix_step s sourceMap d p
      rw [hstep] at h1
      exact ⟨5*(d (source i)).length+4,by have h:=cell_le d (source i);omega,h1⟩
  have hr:=runs_trans (program s sourceMap) _ _ _ _ _ _ _ _ h0 h1
  refine ⟨_,?_,hr⟩
  have ht:=prefix_cell_le s sourceMap d p.val (T.role s p)
  change (before target).length+1+u≤_
  change (before target).length≤ inventory d at ht
  unfold loadUnit
  omega
/-- Every literal checker-template position is physically visited, retaining
all source words, checker banks, scope bytes and caller accumulators. -/
theorem load_runs (d : Stack K→List Bool) (hs : d scratch=[]) (n left : Nat)
    (h : n+left=s.roles.length) :
    ∃t≤left*loadUnit d,Runs (program s sourceMap) t (.inl (.load ⟨n,by omega⟩))
      (loadPrefix s sourceMap d n) (.inl (.load ⟨s.roles.length,by omega⟩)) (loaded sourceMap d) := by
  induction left generalizing n with
  | zero=>
    have hn:n=s.roles.length:=by omega
    subst n
    rw [loadPrefix_full]
    exact ⟨0,by omega,runs_refl (program s sourceMap) _ _⟩
  | succ left ih=>
    let p : Fin s.roles.length:=⟨n,by omega⟩
    obtain ⟨a,ha,h0⟩:=field_run s sourceMap d hs p
    obtain ⟨t,ht,h1⟩:=ih (n+1) (by omega)
    have hr:=runs_trans (program s sourceMap) _ _ _ _ _ _ _ _ h0 h1
    refine ⟨a+t,?_,hr⟩
    rw [Nat.succ_mul]
    omega
/-- One real return follows the complete physical load; outer frames survive. -/
theorem load_returns (d : Stack K→List Bool) (hs : d scratch=[]) :
    ∃t≤ s.roles.length*loadUnit d+1,
      Returns (program s sourceMap) t (.inl (.load 0)) d (loaded sourceMap d) := by
  obtain ⟨t,ht,hr⟩:=load_runs s sourceMap d hs 0 s.roles.length (by omega)
  rw [loadPrefix_zero] at hr
  refine ⟨t+1,by omega,?_⟩
  exact of_runs (program s sourceMap) t (.inl (.load 0)) (.inl (.load ⟨s.roles.length,by omega⟩)) _ _ hr
    (by simp only [program,dite_eq_right (Nat.lt_irrefl _)])
end RiemannGaussian.SemiprimeD1StackDescriptorRecordLoad
