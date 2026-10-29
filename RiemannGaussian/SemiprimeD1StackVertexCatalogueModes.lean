/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexCataloguePrepare

/-! # Actual complete eighteen-mode loop
All mode bodies are the fixed acquired-limit Cartesian program. Readonly
source formats below are an internal invariant of actual cache acquisition;
the N-only endpoint derives them instead of accepting parameter answers.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 4096
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVertexCatalogueModes
open SemiprimeD1StackVertexCatalogue SemiprimeD1StackVertexCatalogueComponents
open SemiprimeD1StackVertexCatalogueView SemiprimeD1StackVertexCataloguePrepare
open SemiprimeD1StackProcedureFragments (Runs one_base)
open SemiprimeD1VertexCatalogueModes (Mode Role code previous order dims dimension roles)
open SemiprimeD1VertexCatalogueEncoding (modeCatalogue catalogue)

/-- Actual acquired source-role formats; not a public supplied graph/count interface. -/
def RoleFormat (r t digits:ℕ) (base:Stack→List Bool) : Prop :=
  ∀role,base (roleStack role)=List.replicate (dimension r t digits role) true
/-- Exact literal original constructor prefix, used only to specify the actual loop output. -/
def prefixCatalogue (r t digits:ℕ) (mode:Mode) (output:List Bool) : List Bool :=
  (order.take (code mode+1)).foldr (fun m out=>modeCatalogue r t digits m out) output
/-- One actual mode preparation/body/tag transition budget. -/
def blockBudget (D:ℕ) : ℕ := 24*D+43*(D+18)^5+22

/-- Original first block is the literal input-vertex Cartesian family. -/
theorem prefix_input (r t digits:ℕ) (output:List Bool) :
    prefixCatalogue r t digits .input output=modeCatalogue r t digits .input output := rfl
/-- Descending physical emission gives the exact ascending original constructor prefix. -/
theorem prefix_previous (r t digits:ℕ) (mode:Mode) (hm:mode≠.input) (output:List Bool) :
    prefixCatalogue r t digits mode output=
      prefixCatalogue r t digits (previous mode) (modeCatalogue r t digits mode output) := by
  cases mode <;> simp_all [prefixCatalogue,order,code,previous]
/-- The final physical starting mode covers the complete original list, without a supplied catalogue. -/
theorem prefix_full (r t digits:ℕ) (output:List Bool) : prefixCatalogue r t digits .flagOr output=catalogue r t digits output := rfl

/-- Standalone numeric stage substitution does not unfold executable configurations. -/
theorem numeric_block (D p k:ℕ) (hp:p≤24*D+20) (hk:k≤43*(D+18)^5+1) : p+k+1≤blockBudget D := by
  unfold blockBudget
  omega

/-- Complete actual mode recursion; every resource/source-format premise is an
internal invariant discharged by the original-input acquisition endpoint. -/
theorem mode_run (r t digits:ℕ) (base:Stack→List Bool) (D:ℕ)
    (hs:base scratchStack=[]) (hf:RoleFormat r t digits base) (hb:RoleBound D base)
    (mode:Mode) (limits:Fin 4→List Bool) (output:List Bool) (hl:LimitBound D limits) :
    ∃m≤(code mode+1)*blockBudget D,Runs program m (.inl (.clearLimit mode 0))
      (view base limits (List.replicate (code mode) true) output) (.inl .halt)
      (view base (preparedLimits base .input) [] (prefixCatalogue r t digits mode output)) := by
  suffices h:∀k,∀mode:Mode,code mode=k→∀limits output,LimitBound D limits→
      ∃m≤(k+1)*blockBudget D,Runs program m (.inl (.clearLimit mode 0))
        (view base limits (List.replicate (code mode) true) output) (.inl .halt)
        (view base (preparedLimits base .input) [] (prefixCatalogue r t digits mode output)) by
    exact h (code mode) mode rfl limits output hl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro mode hk limits output hl
    obtain ⟨p,hp,hprep⟩:=prepare_run base limits (List.replicate (code mode) true) output mode D hs hl hb
    have hshape:∀j,preparedLimits base mode j=List.replicate (dims r t digits mode j) true:=fun j=>hf (roles mode j)
    have hdim:∀j,dims r t digits mode j≤D:=by
      intro j
      have h:=hb (roles mode j)
      rw [hf] at h
      simpa only [List.length_replicate,dims] using h
    obtain ⟨q,hq,hkernel⟩:=kernel_call base (dims r t digits mode) (preparedLimits base mode)
      (List.replicate (code mode) true) output mode D hshape hdim
    change Runs program q (.inl (.runMode mode))
      (view base (preparedLimits base mode) (List.replicate (code mode) true) output)
      (.inl (.afterMode mode))
      (view base (preparedLimits base mode) (List.replicate (code mode) true) (modeCatalogue r t digits mode output)) at hkernel
    have hqc:q≤43*(D+18)^5+1:=by
      rw [List.length_replicate] at hq
      exact hq.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 43
        (Nat.pow_le_pow_left (by have h:=SemiprimeD1VertexCatalogueModes.code_le mode;omega) 5)) 1)
    have hblock:=numeric_block D p q hp hqc
    by_cases hm:mode=.input
    · subst mode
      have hj:Runs program 1 (.inl (.afterMode .input))
          (view base (preparedLimits base .input) [] (modeCatalogue r t digits .input output)) (.inl .halt)
          (view base (preparedLimits base .input) [] (modeCatalogue r t digits .input output)):=
        one_base program _ _ (.jump (.inl .halt)) _ _ rfl rfl rfl
      have h:=hprep.trans (hkernel.trans hj)
      refine ⟨p+(q+1),?_,?_⟩
      · have hz:k=0:=by simpa only [code] using hk.symm
        simpa only [hz,Nat.zero_add,Nat.one_mul,Nat.add_assoc] using hblock
      · simpa only [code,prefix_input] using h
    · have hpcode:=SemiprimeD1VertexCatalogueModes.previous_code mode hm
      have hlt:code (previous mode)<k:=by omega
      have hlim:LimitBound D (preparedLimits base mode):=fun j=>hb (roles mode j)
      obtain ⟨z,hz,hprev⟩:=ih (code (previous mode)) hlt (previous mode) rfl (preparedLimits base mode)
        (modeCatalogue r t digits mode output) hlim
      have hpop:=pop_run (.inl (.afterMode mode)) (.inl (.clearLimit (previous mode) 0))
        (kernelStack (Kernel.aux 3))
        (view base (preparedLimits base mode) (List.replicate (code mode) true) (modeCatalogue r t digits mode output))
        (by simp only [program,ite_eq_right hm])
      change Runs program 1 _ _ _ (Function.update
        (view base (preparedLimits base mode) (List.replicate (code mode) true) (modeCatalogue r t digits mode output))
        (kernelStack (Kernel.aux 3)) (List.replicate (code mode) true).tail) at hpop
      have ht:(List.replicate (code mode) true).tail=List.replicate (code (previous mode)) true:=by
        rw [List.tail_replicate]
        congr 1
        omega
      rw [ht,view_tag] at hpop
      have h:=hprep.trans (hkernel.trans (hpop.trans hprev))
      refine ⟨p+(q+(1+z)),?_,?_⟩
      · rw [hpcode,hk] at hz
        calc
          p+(q+(1+z))≤blockBudget D+k*blockBudget D:=by omega
          _=(k+1)*blockBudget D:=by ring
      · simpa only [prefix_previous r t digits mode hm output] using h
end RiemannGaussian.SemiprimeD1StackVertexCatalogueModes
