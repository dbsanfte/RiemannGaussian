/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticWordTablePrimitives
/-! # Actual complete static checker-bank draining -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackStaticWordTableCleanup
open SemiprimeD1StackStaticWordTable SemiprimeD1StackStaticWordTablePrimitives
open SemiprimeD1StackProcedureTrace SemiprimeD1StackProcedureReturns
variable {K L : Type} [DecidableEq K] (s : Static K L)
/-- Proof view of exactly the physically cleared prefix of the static inventory. -/
def cleanPrefix (d : Stack K→List Bool) (n : Nat) : Stack K→List Bool
  | .inl k=>if k∈s.roles.take n then [] else d (.inl k)
  | .inr k=>d (.inr k)
/-- Whole clear checker bank with every template/count/private role preserved. -/
def clean (d : Stack K→List Bool) : Stack K→List Bool
  | .inl _=>[] | .inr k=>d (.inr k)
/-- Empty visited prefix has changed no physical cell. -/
theorem cleanPrefix_zero (d : Stack K→List Bool) : cleanPrefix s d 0=d := by
  funext k;cases k <;> simp only [cleanPrefix,List.take_zero,List.not_mem_nil,ite_false]
/-- Complete literal inventory covers every physical checker role. -/
theorem cleanPrefix_full (d : Stack K→List Bool) : cleanPrefix s d s.roles.length=clean d := by
  funext k
  cases k with
  | inl k=>simp only [cleanPrefix,List.take_length,s.complete k,ite_true,clean]
  | inr k=>rfl
/-- Exact one-role physical reset advances the visited inventory prefix. -/
theorem cleanPrefix_step (d : Stack K→List Bool) (p : Fin s.roles.length) :
    Function.update (cleanPrefix s d p.val) (checker (role s p)) []=cleanPrefix s d (p.val+1) := by
  funext k
  cases k with
  | inl k=>
    by_cases he:k=s.roles[p.val]
    · subst k
      change Function.update (cleanPrefix s d p.val) (Sum.inl s.roles[p.val]) [] (Sum.inl s.roles[p.val])=_
      rw [Function.update_self]
      simp only [cleanPrefix,List.take_succ_eq_append_getElem p.isLt,List.mem_append,List.mem_cons,
        List.not_mem_nil,or_false,or_true,ite_true]
    · rw [Function.update_of_ne (by intro h;exact he (Sum.inl.inj h))]
      simp only [cleanPrefix,List.take_succ_eq_append_getElem p.isLt,List.mem_append,List.mem_cons,
        List.not_mem_nil,or_false,he,or_false]
  | inr k=>rw [Function.update_of_ne (by intro h;cases h)];rfl
/-- Every actual clear can only shorten a payload. -/
theorem cleanPrefix_length (d : Stack K→List Bool) (n : Nat) (k : Stack K) :
    (cleanPrefix s d n k).length≤(d k).length := by
  cases k with
  | inl k=>change (if k∈s.roles.take n then [] else d (.inl k)).length≤_;split <;> simp
  | inr k=>exact le_rfl
/-- Actual total checker payload, used only to bound physical drains. -/
def inventory [Fintype K] (d : Stack K→List Bool) : Nat := ∑k:K,(d (checker k)).length
omit [DecidableEq K] in
/-- Actual checker payload at one role belongs to its complete inventory. -/
theorem cell_le_inventory [Fintype K] (d : Stack K→List Bool) (k : K) :
    (d (checker k)).length≤ inventory d := by
  change (d (checker k)).length≤∑j:K,(d (checker j)).length
  exact Finset.single_le_sum (f:=fun j:K=>(d (checker j)).length)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ k)
/-- Every static role is physically drained; each payload bit, EOF and fixed
role advance is paid. Neither a wholesale reset nor a host getter executes. -/
theorem clear_runs [Fintype K] (d : Stack K→List Bool) (n left : Nat) (h : n+left=s.roles.length) :
    ∃t≤ left*(inventory d+1),Runs (program s) t (.clear ⟨n,by omega⟩)
      (cleanPrefix s d n) (.clear ⟨s.roles.length,by omega⟩) (clean d) := by
  induction left generalizing n with
  | zero=>
    have hn:n=s.roles.length:=by omega
    subst n
    rw [cleanPrefix_full]
    exact ⟨0,by omega,runs_refl (program s) _ _⟩
  | succ left ih=>
    have hn:n<s.roles.length:=by omega
    let p : Fin s.roles.length:=⟨n,hn⟩
    have hd:=drain s (.clear ⟨n,by omega⟩) (.clear ⟨n+1,by omega⟩) (checker (role s p))
      (by simp only [program,dite_eq_left hn];rfl) (cleanPrefix s d n)
    have he:Function.update (cleanPrefix s d n) (checker (role s p)) []=cleanPrefix s d (n+1):=
      cleanPrefix_step s d p
    rw [he] at hd
    obtain ⟨t,ht,hr⟩:=ih (n+1) (by omega)
    have hb: (cleanPrefix s d n (checker (role s p))).length≤ inventory d:=
      (cleanPrefix_length s d n _).trans (cell_le_inventory d (role s p))
    have hout:=runs_trans (program s) _ _ _ _ _ _ _ _ hd hr
    refine ⟨_,?_,hout⟩
    rw [Nat.succ_mul];omega
/-- The final actual return pops the real caller frame after ALL roles clear. -/
theorem clear_returns [Fintype K] (d : Stack K→List Bool) :
    ∃t≤ s.roles.length*(inventory d+1)+1,Returns (program s) t (.clear 0) d (clean d) := by
  obtain ⟨t,ht,hr⟩:=clear_runs s d 0 s.roles.length (by omega)
  rw [cleanPrefix_zero] at hr
  refine ⟨t+1,by omega,?_⟩
  exact of_runs (program s) t (.clear 0) (.clear ⟨s.roles.length,by omega⟩) _ _ hr
    (by simp only [program,dite_eq_right (Nat.lt_irrefl _)])
end RiemannGaussian.SemiprimeD1StackStaticWordTableCleanup
