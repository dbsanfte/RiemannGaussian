/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPrimitives
/-! # Literal complete 115-role physical cleanup
The actual fixed cleanup order visits every allocated word, including callee
shadows. Retained input/output words are skipped by static jumps; every other
word is physically popped through EOF. Ranks below are proof notation only.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryCleanup
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
noncomputable section

/-- Proof-side inverse of the literal complete cleanup order. -/
def rank (k:Stack):Fin 115:=Classical.choose (role_complete k)
theorem role_rank (k:Stack):role (rank k)=k:=Classical.choose_spec (role_complete k)
theorem rank_role (i:Fin 115):rank (role i)=i:=role_injective (role_rank (role i))
/-- Exact word bank after the first n static cleanup labels have executed. -/
def swept (aborted:Bool) (before:Stack→List Bool) (n:Nat) (k:Stack):List Bool:=
  if retained aborted k then before k else if (rank k).val < n then [] else before k
/-- Exact completely cleaned physical bank. -/
def result (aborted:Bool) (before:Stack→List Bool) (k:Stack):List Bool:=
  if retained aborted k then before k else []
/-- Exact bounded static program location, including its real final status label. -/
def pc (aborted:Bool) (n:Nat):Label:=
  if h:n<115 then .clear aborted ⟨n,h⟩ else if aborted then reject else accept
/-- All allocated physical words contribute to this actual byte sum. -/
def mass (before:Stack→List Bool):Nat:=∑i:Fin 115,(before (role i)).length
private theorem sum_cell {n:Nat} (f:Fin n→Nat) (i:Fin n):f i ≤ ∑j,f j:=by
  exact Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
/-- A currently visited word is paid by the whole actual allocated byte sum. -/
theorem word_le_mass (before:Stack→List Bool) (i:Fin 115):
    (before (role i)).length≤ mass before:=by
  exact sum_cell (fun j:Fin 115=>(before (role j)).length) i
theorem swept_zero (aborted:Bool) (before:Stack→List Bool):swept aborted before 0=before:=by
  funext k;simp only [swept,Nat.not_lt_zero,ite_false];split <;> rfl
theorem swept_all (aborted:Bool) (before:Stack→List Bool):swept aborted before 115=result aborted before:=by
  funext k;simp only [swept,result,(rank k).isLt,ite_true]
theorem swept_current (aborted:Bool) (before:Stack→List Bool) (i:Fin 115):
    swept aborted before i.val (role i)=before (role i):=by
  simp only [swept,rank_role,lt_self_iff_false,ite_false];split <;> rfl
theorem swept_step_skip (aborted:Bool) (before:Stack→List Bool) (i:Fin 115)
    (hi:retained aborted (role i)=true):swept aborted before (i.val+1)=swept aborted before i.val:=by
  funext k
  by_cases hk:k=role i
  · subst k;simp only [swept,hi,ite_true]
  · have hn:(rank k).val≠i.val:=by
      intro he
      have hri:rank k=i:=Fin.ext he
      exact hk ((role_rank k).symm.trans (congrArg role hri))
    have hlt:((rank k).val < i.val+1)↔((rank k).val < i.val):=by omega
    simp only [swept,hlt]
theorem swept_step_clear (aborted:Bool) (before:Stack→List Bool) (i:Fin 115)
    (hi:retained aborted (role i)=false):
    Function.update (swept aborted before i.val) (role i) []=swept aborted before (i.val+1):=by
  funext k
  by_cases hk:k=role i
  · subst k;simp only [Function.update_self,swept,hi,rank_role,Nat.lt_succ_self,Bool.false_eq_true,ite_false,ite_true]
  · have hn:(rank k).val≠i.val:=by
      intro he
      have hri:rank k=i:=Fin.ext he
      exact hk ((role_rank k).symm.trans (congrArg role hri))
    have hlt:((rank k).val < i.val+1)↔((rank k).val < i.val):=by omega
    simp only [Function.update_of_ne hk,swept,hlt]
theorem next_pc (aborted:Bool) (i:Fin 115):nextClear aborted i=pc aborted (i.val+1):=rfl
/-- One actual static cleanup label: retained jump or complete physical word drain. -/
theorem step_trace (aborted:Bool) (before:Stack→List Bool) (i:Fin 115):
    ∃t≤ mass before+1,Runs program t (pc aborted i.val) (swept aborted before i.val)
      (pc aborted (i.val+1)) (swept aborted before (i.val+1)):=by
  have hpc:pc aborted i.val=.clear aborted i:=by simp [pc,i.isLt]
  cases he:retained aborted (role i) with
  | false=>
    have hc:program (.clear aborted i)=.base (.pop (role i) (nextClear aborted i) (.clear aborted i) (.clear aborted i)):=by
      simp only [program,he,Bool.false_eq_true,ite_false]
    have h:=drain_loop (.clear aborted i) (nextClear aborted i) (role i) hc
      (swept aborted before i.val) (before (role i)) (swept_current _ _ _)
    rw [swept_step_clear _ _ _ he,next_pc] at h
    exact ⟨(before (role i)).length+1,Nat.add_le_add_right (word_le_mass before i) 1,by simpa only [hpc] using h⟩
  | true=>
    have hc:program (.clear aborted i)=.base (.jump (nextClear aborted i)):=by simp only [program,he,ite_true]
    have h:=jump_run (.clear aborted i) (nextClear aborted i) (swept aborted before i.val) hc
    rw [next_pc] at h
    refine ⟨1,by omega,?_⟩
    rw [hpc,swept_step_skip _ _ _ he]
    exact h
/-- Complete real remaining sweep, uniformly bounded using the SAME actual bank bytes. -/
theorem sweep_trace (aborted:Bool) (before:Stack→List Bool) (n:Nat) (hn:n≤115):
    ∃t≤(115-n)*(mass before+1),Runs program t (pc aborted n) (swept aborted before n)
      (pc aborted 115) (result aborted before):=by
  by_cases hlast:n=115
  · subst n
    refine ⟨0,by omega,?_⟩
    rw [swept_all]
    exact runs_refl program _ _
  · have hn':n<115:=by omega
    obtain ⟨x,hx,h0⟩:=step_trace aborted before ⟨n,hn'⟩
    obtain ⟨y,hy,h1⟩:=sweep_trace aborted before (n+1) (by omega)
    refine ⟨x+y,?_,join h0 h1⟩
    have he:115-n=1+(115-(n+1)):=by omega
    rw [he,Nat.add_mul,one_mul]
    exact Nat.add_le_add hx hy
termination_by 115-n
/-- Actual entire cleanup, from its first physical role to its real status push. -/
theorem source_trace (aborted:Bool) (before:Stack→List Bool):
    ∃t≤115*(mass before+1),Runs program t (.clear aborted 0) before
      (if aborted then reject else accept) (result aborted before):=by
  obtain ⟨t,ht,h⟩:=sweep_trace aborted before 0 (by omega)
  refine ⟨t,by simpa using ht,?_⟩
  simpa [pc,swept_zero] using h
/-- No physical word outside the fixed retained roles survives silently. -/
theorem result_word (aborted:Bool) (before:Stack→List Bool) (k:Stack):
    result aborted before k=if retained aborted k then before k else []:=rfl
end
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryCleanup
