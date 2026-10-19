/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Literal tail cyclotomic primes and the primitive-root gate

The first physical annulus of the actual tail M<d<=2M detects primitive
roots of the fixed integer base. Below M+1 no retained tail prime exists.
Integrality transport and all source consequences remain paper-level.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
noncomputable section
namespace OpenAIReview.SignedIntegralSource
attribute [local instance] Classical.propDecidable

/-- Actual cyclotomic divisibility is finite-field root incidence. -/
theorem cyclotomic_dvd_iff_root (b d p : ℕ) [Fact p.Prime] :
    (p:ℤ)∣(Polynomial.cyclotomic d ℤ).eval (b:ℤ) ↔
      (Polynomial.cyclotomic d (ZMod p)).IsRoot (b:ZMod p) := by
  rw [←ZMod.intCast_zmod_eq_zero_iff_dvd]
  change (Int.castRingHom (ZMod p)) ((Polynomial.cyclotomic d ℤ).eval (b:ℤ))=0 ↔ _
  have hc := (Polynomial.cyclotomic.eval_apply (b:ℤ) d (Int.castRingHom (ZMod p))).symm
  rw [hc]
  simp only [Polynomial.IsRoot,Int.coe_castRingHom,Int.cast_natCast]

/-- Retaining a prime away from the index forces its exact primitive order. -/
theorem retained_primitive (b d p : ℕ) [Fact p.Prime]
    (hv : (p:ℤ)∣(Polynomial.cyclotomic d ℤ).eval (b:ℤ)) (hd : ¬p∣d) :
    IsPrimitiveRoot (b:ZMod p) d := by
  have : NeZero (d:ZMod p) := ⟨by
    intro h; exact hd ((ZMod.natCast_eq_zero_iff _ _).mp h)⟩
  exact Polynomial.isRoot_cyclotomic_iff.mp ((cyclotomic_dvd_iff_root b d p).mp hv)

/-- Any divisor exceeding half a positive integer is the integer itself. -/
theorem divisor_above_half (d n : ℕ) (hn : 0<n) (hd : d∣n)
    (hlarge : n<2*d) : d=n := by
  obtain ⟨k,hk⟩ := hd
  have hdp : 0<d := by nlinarith
  have hkp : 0<k := by nlinarith
  have hk1 : k=1 := by nlinarith
  simpa [hk1] using hk.symm

/-- The actual retained cyclotomic tail selects exactly primitive-root primes
in its first physical annulus. No prime-density assertion is involved. -/
theorem tail_annulus_iff_primitive (b M p : ℕ) [hp : Fact p.Prime]
    (hlo : M+1<p) (hhi : p≤2*M+1) :
    (∃d∈Finset.Icc (M+1) (2*M),
      (p:ℤ)∣(Polynomial.cyclotomic d ℤ).eval (b:ℤ) ∧ ¬p∣d) ↔
      IsPrimitiveRoot (b:ZMod p) (p-1) := by
  constructor
  · rintro ⟨d,hd,hv,hnd⟩
    have hdlo := (Finset.mem_Icc.mp hd).1
    have hprim := retained_primitive b d p hv hnd
    have hdiv : d∣p-1 := hprim.dvd_of_pow_eq_one _
      (ZMod.pow_card_sub_one_eq_one (hprim.ne_zero (by omega)))
    have hdn : d=p-1 := divisor_above_half d (p-1) (by omega) hdiv (by omega)
    simpa [hdn] using hprim
  · intro hprim
    have hdpos : 0<p-1 := by have := hp.out.two_le;omega
    refine ⟨p-1,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_,?_⟩
    · exact (cyclotomic_dvd_iff_root b (p-1) p).mpr (hprim.isRoot_cyclotomic hdpos)
    · exact Nat.not_dvd_of_pos_of_lt hdpos (by omega)

/-- Adaptive selection of actual tail rows retains the selection at p-1;
integrality cannot replace this mask by density. -/
theorem tail_mask_annulus (b M p : ℕ) [Fact p.Prime]
    (hlo : M+1<p) (hhi : p≤2*M+1) (mask : ℕ→Prop) :
    (∃d∈Finset.Icc (M+1) (2*M), mask d ∧
      (p:ℤ)∣(Polynomial.cyclotomic d ℤ).eval (b:ℤ) ∧ ¬p∣d) ↔
      mask (p-1) ∧ IsPrimitiveRoot (b:ZMod p) (p-1) := by
  constructor
  · rintro ⟨d,hd,hm,hv,hnd⟩
    have hprim := (tail_annulus_iff_primitive b M p hlo hhi).mp ⟨d,hd,hv,hnd⟩
    have heq := (retained_primitive b d p hv hnd).unique hprim
    exact ⟨heq ▸ hm,hprim⟩
  · rintro ⟨hm,hprim⟩
    have hdpos : 0<p-1 := by omega
    refine ⟨p-1,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,hm,?_,?_⟩
    · exact (cyclotomic_dvd_iff_root b (p-1) p).mpr (hprim.isRoot_cyclotomic hdpos)
    · exact Nat.not_dvd_of_pos_of_lt hdpos (by omega)

/-- All retained tail factors are invisible through physical prime M+1. -/
theorem no_tail_prime_below (b M p : ℕ) [hp : Fact p.Prime]
    (hsmall : p≤M+1) :
    ¬∃d∈Finset.Icc (M+1) (2*M),
      (p:ℤ)∣(Polynomial.cyclotomic d ℤ).eval (b:ℤ) ∧ ¬p∣d := by
  rintro ⟨d,hd,hv,hnd⟩
  have hdlo := (Finset.mem_Icc.mp hd).1
  have hprim := retained_primitive b d p hv hnd
  have hdiv : d∣p-1 := hprim.dvd_of_pow_eq_one _
    (ZMod.pow_card_sub_one_eq_one (hprim.ne_zero (by omega)))
  have hle := Nat.le_of_dvd (show 0<p-1 by have := hp.out.two_le;omega) hdiv
  omega

/-- The exact joined first annulus retains every arbitrary complex prime weight. -/
theorem tail_annulus_weights (b M : ℕ) (S : Finset ℕ)
    (hS : ∀p∈S,p.Prime ∧ M+1<p ∧ p≤2*M+1) (w : ℕ→ℂ) :
    (∑p∈S,if ∃d∈Finset.Icc (M+1) (2*M),
      (p:ℤ)∣(Polynomial.cyclotomic d ℤ).eval (b:ℤ) ∧ ¬p∣d
      then w p else 0)=
    ∑p∈S,if IsPrimitiveRoot (b:ZMod p) (p-1) then w p else 0 := by
  apply Finset.sum_congr rfl
  intro p hpS
  obtain ⟨hp,hlo,hhi⟩ := hS p hpS
  have : Fact p.Prime := ⟨hp⟩
  simp only [tail_annulus_iff_primitive b M p hlo hhi]

end OpenAIReview.SignedIntegralSource
#lint+ in OpenAIReview.SignedIntegralSource

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut details : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    details := details.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  logInfo m!"Signed integral source audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.writeFile ".lake/arithmetic-operator-signed-integral-source-gate/axioms.json"
    (Json.mkObj [("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("namespaceLinters",toJson (15:Nat)),("allLocalModuleProvenance",toJson true),
      ("onlyStandardAxioms",toJson true),("details",Json.arr details)]).pretty
