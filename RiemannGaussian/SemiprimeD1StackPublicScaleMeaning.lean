/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicScale
/-! # Exact two-term dot identity and original scale guard equivalence
These are semantic specifications for the already executed backend, not a new
evaluator or a supplied canonicality/verdict input. The output guard is derived
from actual integer equality with the canonical evaluated result.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicScaleMeaning
open SemiprimeBitArithmetic SemiprimeMacroEntryBitPrimitives
/-- The exact actual zero word, one false cell per acquired modulus-word cell. -/
def zeroWord (cached : List Bool) : List Bool := List.replicate cached.length false
/-- The actually constructed false-cell word has integer value zero. -/
theorem zeroWord_value (cached : List Bool) : bitValue (zeroWord cached)=0 := by
  simpa only [zeroWord,List.append_nil,bitValue,Nat.mul_zero] using
    SemiprimeD1StackFermatWords.zeros_value cached.length []
/-- Exact acquired zero/input vector, used only in the correctness specification. -/
def inputAt (cached input : List Bool) (j : ℕ) : List Bool :=
  if j=0 then zeroWord cached else if j=1 then input else []
/-- Literal TWO-term executed dot has exactly the original scale expression's
ring value. This preserves j*k, including all zero-index cases. -/
theorem dot_meaning (cached : List Bool) (base : Expr) (j k : ℕ) (input : List Bool) :
    meaning cached (dotExpr base j k (inputAt cached input) 2)=
      meaning cached (.mul (.literal input) (powerExpr base (j*k))) := by
  simp [dotExpr,inputAt,meaning,powerExpr_meaning,zeroWord_value,bitValue]
/-- Physically checked canonicality bit for the actual zero/input vector. -/
def guard (cached input : List Bool) : Bool :=
  SemiprimeD1StackVectorCanonicalExecution.answer cached [zeroWord cached,input]
/-- The actual computed scale result followed by numeric equality; false guard
branches never execute the dot at runtime. This definition is proof-side only. -/
def answer (cached : List Bool) (base : Expr) (j k : ℕ) (input output : List Bool) : Bool :=
  guard cached input && decide (bitValue (execute cached (dotExpr base j k (inputAt cached input) 2)).bits=bitValue output)
/-- Checking the literal zero adds no canonicality premise on the original input. -/
theorem guard_true (cached input : List Bool) (hm : 0<bitValue cached) :
    guard cached input=true ↔ bitValue input<bitValue cached := by
  rw [guard,SemiprimeD1StackVectorCanonicalExecution.answer_true]
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  have hz : bitValue (zeroWord cached)=0 := by
    exact zeroWord_value cached
  rw [hz]
  exact and_iff_right hm
/-- No explicit output-canonical guard is required: actual integer equality to
the canonical evaluated result PROVES it, yielding exactly the old guard. -/
theorem answer_true (cached : List Bool) (hm : 1<bitValue cached) (base : Expr)
    (hb : Valid cached base) (j k : ℕ) (input output : List Bool) :
    answer cached base j k input output=true ↔
      bitValue input<bitValue cached ∧ bitValue output<bitValue cached ∧
      meaning cached (.mul (.literal input) (powerExpr base (j*k)))=
        (bitValue output : ZMod (bitValue cached)) := by
  rw [answer,Bool.and_eq_true,guard_true cached input (by omega),decide_eq_true_eq]
  constructor
  · rintro ⟨hi,he⟩
    have hv : Valid cached (dotExpr base j k (inputAt cached input) 2) :=
      dotExpr_valid cached hm base hb j k 2 _ (by
        intro q hq
        have hz : bitValue (zeroWord cached)=0 := by
          exact zeroWord_value cached
        interval_cases q <;> simp [inputAt,hz,hi];omega)
    have hbound:=(execute_bounds cached (by omega) _ hv).2
    have hc:=execute_correct cached (by omega) _ hv
    rw [he,dot_meaning] at hc
    exact ⟨hi,by omega,hc.symm⟩
  · rintro ⟨hi,ho,he⟩
    refine ⟨hi,?_⟩
    have hv : Valid cached (dotExpr base j k (inputAt cached input) 2) :=
      dotExpr_valid cached hm base hb j k 2 _ (by
        intro q hq
        have hz : bitValue (zeroWord cached)=0 := by
          exact zeroWord_value cached
        interval_cases q <;> simp [inputAt,hz,hi];omega)
    have hbound:=(execute_bounds cached (by omega) _ hv).2
    have hc:=execute_correct cached (by omega) _ hv
    rw [dot_meaning,he] at hc
    have hh:=congrArg ZMod.val hc
    simpa only [ZMod.val_natCast_of_lt hbound,ZMod.val_natCast_of_lt ho] using hh
/-- The old guarded scale checker and actual guarded TWO-term dot+integer
comparison accept exactly the same inputs, including malformed output words. -/
theorem old_scale (p : SemiprimeMacroGraphSemantics.Config) (tr : SemiprimeMacroGraph.Transform)
    (j k : ℕ) (input output : List Bool) :
    answer (SemiprimeMacroEntryBitCheck.modulus p) (SemiprimeMacroEntryBitCheck.rootExpr p tr) j k input output=
      (SemiprimeMacroEntryBitCheck.equationRun p (fun _ : Fin 1=>input) output
        (.mul (.literal input) (powerExpr (SemiprimeMacroEntryBitCheck.rootExpr p tr) (j*k)))).accepted := by
  let cached:=SemiprimeMacroEntryBitCheck.modulus p
  let expr:=Expr.mul (.literal input) (powerExpr (SemiprimeMacroEntryBitCheck.rootExpr p tr) (j*k))
  have hm : 1<bitValue cached := by
    change 1<bitValue (SemiprimeMacroEntryBitCheck.modulus p)
    have h:=SemiprimeMacroEntryBitCheck.modulus_gt_four p;omega
  have hb:=SemiprimeMacroEntryBitCheck.rootExpr_valid p tr
  apply Bool.eq_iff_iff.mpr
  rw [answer_true cached hm _ hb]
  simp only [SemiprimeMacroEntryBitCheck.equationRun,SemiprimeMacroEntryBitCheck.guardRun_correct,
    SemiprimeMacroEntryBitCheck.andRun,Bool.and_eq_true,SemiprimeMacroEntryBitCheck.canonicalRun_correct,
    lessBits_correct]
  constructor
  · rintro ⟨hi,ho,he⟩
    refine ⟨⟨fun _=>hi,ho⟩,?_⟩
    have hv : Valid cached expr := ⟨hi,powerExpr_valid cached hm _ hb _⟩
    rw [residueEqualityBits_correct cached (by omega) (.literal output) expr ho hv]
    exact he.symm
  · rintro ⟨⟨hi,ho⟩,he⟩
    have hv : Valid cached expr := ⟨hi 0,powerExpr_valid cached hm _ hb _⟩
    rw [residueEqualityBits_correct cached (by omega) (.literal output) expr ho hv] at he
    exact ⟨hi 0,ho,he.symm⟩
end RiemannGaussian.SemiprimeD1StackPublicScaleMeaning
