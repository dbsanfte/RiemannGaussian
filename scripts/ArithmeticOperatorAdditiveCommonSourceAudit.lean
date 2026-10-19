/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorQDetSmallWindowAudit

/-!
# Actual additively shifted cutoff common integers

In the saturated physical window, a fixed positive translate deletes all
but a fixed finite prime head. For translate one the only possible prime
is2, and its actual full shifted valuation is retained. No unsaturated
source theorem or estimate is inferred.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
namespace OpenAIReview.AdditiveCommonSource
open QDetSmallWindow
attribute [local instance] Classical.propDecidable

/-- One actual common integer, with the addition performed before taking gcd. -/
def shiftedCommon (b c N h : ℕ) : ℕ :=
  Nat.gcd (cyclotomicProduct b N) (cyclotomicProduct c N+h)

/-- Every positive-index-above-one cyclotomic factor is1 modulo its base. -/
theorem factor_base_residue (b n q : ℕ) (hb : 2≤b) (hn : 1<n) (hqb : q∣b) :
    (cyclotomicNorm b n : ZMod q)=1 := by
  have hv : 0≤(Polynomial.cyclotomic n ℤ).eval (b:ℤ) :=
    (Polynomial.cyclotomic_pos' n (by exact_mod_cast (show 1<b by omega))).le
  have hcast : (cyclotomicNorm b n : ZMod q)=
      (Int.castRingHom (ZMod q)) ((Polynomial.cyclotomic n ℤ).eval (b:ℤ)) := by
    have hh := congrArg (fun x : ℤ => (x:ZMod q)) (Int.natAbs_of_nonneg hv)
    simpa [cyclotomicNorm] using hh
  have he := (Polynomial.cyclotomic.eval_apply (b:ℤ) n (Int.castRingHom (ZMod q))).symm
  have hbq : (b:ZMod q)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr hqb
  rw [hcast]
  change (Int.castRingHom (ZMod q)) ((Polynomial.cyclotomic n ℤ).eval (b:ℤ))=1
  rw [he]
  simp only [Int.coe_castRingHom,Int.cast_natCast,hbq,
    ←Polynomial.coeff_zero_eq_eval_zero,Polynomial.cyclotomic_coeff_zero (ZMod q) hn]

/-- The whole once-counted actual product is1 modulo every divisor of its base. -/
theorem product_base_residue (b N q : ℕ) (hb : 2≤b) (hqb : q∣b) :
    (cyclotomicProduct b N : ZMod q)=1 := by
  simp only [cyclotomicProduct,Nat.cast_prod]
  apply Finset.prod_eq_one
  intro n hn
  exact factor_base_residue b n q hb (by have := (Finset.mem_Icc.mp hn).1;omega) hqb

/-- Exact fixed-translate prime support in the proved saturated physical window. -/
theorem shifted_prime_support (b c N h p : ℕ) (hb : 2≤b) (hc : 2≤c)
    (hp : p.Prime) (hcut : p≤N) :
    p∣shiftedCommon b c N h ↔ ¬p∣b ∧
      ((¬p∣c ∧ p∣h) ∨ (p∣c ∧ p∣h+1)) := by
  rw [shiftedCommon,Nat.dvd_gcd_iff,
    show p∣cyclotomicProduct b N ↔ ¬p∣b from
      by simpa using small_window_support b N p 1 hb hp (by omega) (by simpa using hcut)]
  by_cases hpc : p∣c
  · have hr := product_base_residue c N p hc hpc
    have hh : p∣cyclotomicProduct c N+h ↔ p∣h+1 := by
      rw [←ZMod.natCast_eq_zero_iff (cyclotomicProduct c N+h) p,
        ←ZMod.natCast_eq_zero_iff (h+1) p]
      simp only [Nat.cast_add,Nat.cast_one,hr,add_comm]
    simp only [hpc,not_true_eq_false,false_and,false_or,true_and,hh]
  · have hd : p∣cyclotomicProduct c N := by
      simpa using (small_window_support c N p 1 hc hp (by omega) (by simpa using hcut)).mpr hpc
    have hr : (cyclotomicProduct c N : ZMod p)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    have hh : p∣cyclotomicProduct c N+h ↔ p∣h := by
      rw [←ZMod.natCast_eq_zero_iff (cyclotomicProduct c N+h) p,
        ←ZMod.natCast_eq_zero_iff h p]
      simp only [Nat.cast_add,hr,zero_add]
    simp only [hpc,not_false_eq_true,true_and,false_and,or_false,hh]

/-- Away from the shifted base, every full surviving physical depth is exactly a lag divisor. -/
theorem shifted_power_away_base (b c N h p r : ℕ) (hb : 2≤b) (hc : 2≤c)
    (hp : p.Prime) (hr : 0<r) (hcut : p^r≤N) (hpc : ¬p∣c) :
    p^r∣shiftedCommon b c N h ↔ ¬p∣b ∧ p^r∣h := by
  have hd := (small_window_support c N p r hc hp hr hcut).mpr hpc
  rw [shiftedCommon,Nat.dvd_gcd_iff,small_window_support b N p r hb hp hr hcut]
  have hh : p^r∣cyclotomicProduct c N+h ↔ p^r∣h := by
    have hz : (cyclotomicProduct c N : ZMod (p^r))=0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [←ZMod.natCast_eq_zero_iff (cyclotomicProduct c N+h) (p^r),
      ←ZMod.natCast_eq_zero_iff h (p^r)]
    simp only [Nat.cast_add,hz,zero_add]
  rw [hh]

/-- For translate one the only surviving small prime is the literal two-adic head. -/
theorem shifted_one_prime_support (b c N p : ℕ) (hb : 2≤b) (hc : 2≤c)
    (hp : p.Prime) (hcut : p≤N) :
    p∣shiftedCommon b c N 1 ↔ p=2 ∧ ¬p∣b ∧ p∣c := by
  rw [shifted_prime_support b c N 1 p hb hc hp hcut]
  simp only [hp.not_dvd_one,and_false,false_or,
    show p∣1+1 ↔ p=2 by simpa using Nat.prime_dvd_prime_iff_eq hp Nat.prime_two]
  tauto

/-- Actual full depth survives only at2; no shifted valuation is replaced by one. -/
theorem shifted_one_power_support (b c N p r : ℕ) (hb : 2≤b) (hc : 2≤c)
    (hp : p.Prime) (hr : 0<r) (hcut : p^r≤N) :
    p^r∣shiftedCommon b c N 1 ↔ p=2 ∧ ¬p∣b ∧ p∣c ∧
      p^r∣cyclotomicProduct c N+1 := by
  constructor
  · intro hd
    have hpdiv : p∣shiftedCommon b c N 1 := (dvd_pow_self p hr.ne').trans hd
    have hpN : p≤N := (Nat.le_of_dvd (pow_pos hp.pos _) (dvd_pow_self p hr.ne')).trans hcut
    obtain ⟨h2,hpb,hpc⟩ := (shifted_one_prime_support b c N p hb hc hp hpN).mp hpdiv
    exact ⟨h2,hpb,hpc,(Nat.dvd_gcd_iff.mp hd).2⟩
  · rintro ⟨_h2,hpb,_hpc,hd⟩
    exact Nat.dvd_gcd ((small_window_support b N p r hb hp hr hcut).mpr hpb) hd

/-- Arbitrary literal complex prime-power weights retain exactly that actual head. -/
theorem shifted_one_depth_weights (b c N : ℕ) (hb : 2≤b) (hc : 2≤c)
    (S : Finset (ℕ×ℕ)) (hS : ∀a∈S,a.1.Prime ∧ 0<a.2 ∧ a.1^a.2≤N)
    (w : ℕ×ℕ→ℂ) :
    (∑a∈S,if a.1^a.2∣shiftedCommon b c N 1 then w a else 0)=
    ∑a∈S,if a.1=2 ∧ ¬a.1∣b ∧ a.1∣c ∧
      a.1^a.2∣cyclotomicProduct c N+1 then w a else 0 := by
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨hp,hr,hcut⟩ := hS a ha
  simp only [shifted_one_power_support b c N a.1 a.2 hb hc hp hr hcut]

end OpenAIReview.AdditiveCommonSource
#lint+ in OpenAIReview.AdditiveCommonSource

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
  logInfo m!"Additive common source audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.writeFile ".lake/arithmetic-operator-additive-common-source-gate/axioms.json"
    (Json.mkObj [("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("namespaceLinters",toJson (15:Nat)),("allLocalModuleProvenance",toJson true),
      ("onlyStandardAxioms",toJson true),("details",Json.arr details)]).pretty
