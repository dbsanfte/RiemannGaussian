/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.EtaMoebiusFinitePrefix
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Literal integer cyclotomic residual and finite source conservation

All indices include one. The residual uses the actual Mathlib cyclotomic
polynomial evaluated at every integer base b≥2. Its divisor profile and
floor aggregate are exactly the elementary logarithmic tail. Möbius
inversion and a finite residualPrefix comparison retain the source-bearing residual.
Zero-free continuation and the infinite ℓ¹ inverse remain paper-level.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option warningAsError true
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
namespace OpenAIReview.CyclotomicConvolution

/-- Actual real evaluation of the integer cyclotomic polynomial. -/
def value (b d : ℕ) : ℝ := (Polynomial.cyclotomic d ℝ).eval (b : ℝ)

/-- Actual logarithmic cyclotomic norm with its totient term removed. -/
def residual (b d : ℕ) : ℝ := Real.log (value b d)-(d.totient : ℝ)*Real.log b

/-- Exponentially decaying elementary logarithmic coefficient. -/
def tail (b n : ℕ) : ℝ := Real.log (1-((b : ℝ)^n)⁻¹)

/-- The finite ordinary Möbius residualPrefix, with its integer endpoint retained. -/
def mertens (N : ℕ) : ℝ := ∑ n∈Finset.Icc 1 N,(μ n : ℝ)

/-- The source-bearing finite residualPrefix of actual cyclotomic residuals. -/
def residualPrefix (b N : ℕ) : ℝ := ∑ n∈Finset.Icc 1 N,residual b n

/-- The real evaluation is literally the cast of the integer polynomial value. -/
theorem value_eq_int_eval (b d : ℕ) :
    value b d=(((Polynomial.cyclotomic d ℤ).eval (b : ℤ) : ℤ) : ℝ) := by
  simpa [value] using Polynomial.cyclotomic.eval_apply (b : ℤ) d (Int.castRingHom ℝ)

/-- Actual cyclotomic values are positive, including index one. -/
theorem value_pos (b d : ℕ) (hb : 2≤b) : 0<value b d := by
  exact Polynomial.cyclotomic_pos' d (by exact_mod_cast (show 1<b by omega))

/-- Every logarithmic tail argument is positive at positive indices. -/
theorem tail_argument_pos (b n : ℕ) (hb : 2≤b) (hn : 0<n) :
    0<1-((b : ℝ)^n)⁻¹ := by
  have hpow : 1<(b : ℝ)^n := one_lt_pow₀ (by exact_mod_cast (show 1<b by omega)) hn.ne'
  exact sub_pos.mpr ((inv_lt_one₀ (by positivity)).2 hpow)

/-- Evaluating the actual divisor product retains every cyclotomic factor. -/
theorem divisor_product (b n : ℕ) (hn : 0<n) :
    (∏ d∈n.divisors,value b d)=(b : ℝ)^n-1 := by
  have h:=congrArg (Polynomial.eval (b : ℝ))
    (Polynomial.prod_cyclotomic_eq_X_pow_sub_one hn ℝ)
  simpa [value,Polynomial.eval_prod] using h

/-- The exact actual logarithmic divisor sum, with no sign ambiguity. -/
theorem divisor_log (b n : ℕ) (hb : 2≤b) (hn : 0<n) :
    (∑ d∈n.divisors,Real.log (value b d))=Real.log ((b : ℝ)^n-1) := by
  rw [← Real.log_prod (fun d _ => (value_pos b d hb).ne'),divisor_product b n hn]

/-- Removing the totient term leaves precisely the elementary divisor tail. -/
theorem residual_profile (b n : ℕ) (hb : 2≤b) (hn : 0<n) :
    (∑ d∈n.divisors,residual b d)=tail b n := by
  have ht : (∑ d∈n.divisors,(d.totient : ℝ))=(n : ℝ) := by
    exact_mod_cast Nat.sum_totient n
  have hpow : (b : ℝ)^n≠0 := pow_ne_zero _ (by positivity)
  simp only [residual,Finset.sum_sub_distrib,← Finset.sum_mul]
  rw [ht,divisor_log b n hb hn]
  rw [← Real.log_pow]
  have hpos : 0<(b : ℝ)^n-1 := sub_pos.mpr
    (one_lt_pow₀ (by exact_mod_cast (show 1<b by omega)) hn.ne')
  rw [← Real.log_div hpos.ne' hpow]
  unfold tail
  congr 1
  field_simp

/-- Index one is the nonzero first coefficient; it is never dropped. -/
theorem residual_one (b : ℕ) (hb : 2≤b) : residual b 1=tail b 1 := by
  simpa using residual_profile b 1 hb (by omega)

/-- Actual residuals are exactly the finite Möbius convolution of the tail. -/
theorem residual_moebius (b n : ℕ) (hb : 2≤b) (hn : 0<n) :
    (∑ p∈n.divisorsAntidiagonal,(μ p.1 : ℝ)*tail b p.2)=residual b n := by
  exact ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp
    (fun k hk => residual_profile b k hb hk) n hn

/-- The full factorial floor aggregate deletes the residual source exactly. -/
theorem floor_residual (b N : ℕ) (hb : 2≤b) :
    (∑ d∈Finset.Icc 1 N,(N/d : ℕ)*residual b d)=
      ∑ n∈Finset.Icc 1 N,tail b n := by
  have hs:=RiemannGaussian.sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix N
    (fun d _ => (residual b d : ℂ))
  have hp (n : ℕ) (hn : 0<n) :
      (∑ p∈n.divisorsAntidiagonal,(residual b p.1 : ℂ))=(tail b n : ℂ) := by
    rw [Nat.sum_divisorsAntidiagonal (fun d _ => (residual b d : ℂ))]
    exact_mod_cast residual_profile b n hb hn
  have hs' : (∑ n∈Finset.Icc 1 N,(tail b n : ℂ))=
      ∑ d∈Finset.Icc 1 N,((N/d : ℕ) : ℂ)*(residual b d : ℂ) := by
    calc
      _=∑ n∈Finset.Icc 1 N,∑ p∈n.divisorsAntidiagonal,(residual b p.1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact (hp n (Finset.mem_Icc.mp hn).1).symm
      _=_ := by simpa only [Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,
        nsmul_eq_mul] using hs
  exact_mod_cast hs'.symm

/-- The faithful residualPrefix is the literal tail-weighted divided Möbius residualPrefix. -/
theorem prefix_mertens (b N : ℕ) (hb : 2≤b) :
    residualPrefix b N=∑ d∈Finset.Icc 1 N,tail b d*mertens (N/d) := by
  have hp (n : ℕ) (hn : 0<n) :
      (∑ p∈n.divisorsAntidiagonal,tail b p.1*(μ p.2 : ℝ))=residual b n := by
    rw [Nat.sum_divisorsAntidiagonal' (fun d k => tail b d*(μ k : ℝ))]
    have hm:=residual_moebius b n hb hn
    rw [Nat.sum_divisorsAntidiagonal (fun d k => (μ d : ℝ)*tail b k)] at hm
    simpa only [mul_comm] using hm
  have hs:=RiemannGaussian.sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix N
    (fun d k => ((tail b d : ℂ)*(μ k : ℂ)))
  have he : (residualPrefix b N : ℂ)=
      ∑ d∈Finset.Icc 1 N,(tail b d : ℂ)*(mertens (N/d) : ℂ) := by
    calc
      _=∑ n∈Finset.Icc 1 N,∑ p∈n.divisorsAntidiagonal,
          (tail b p.1 : ℂ)*(μ p.2 : ℂ) := by
        unfold residualPrefix
        push_cast
        apply Finset.sum_congr rfl
        intro n hn
        exact_mod_cast (hp n (Finset.mem_Icc.mp hn).1).symm
      _=_ := by simpa only [← Finset.mul_sum,mertens,Complex.ofReal_sum,
        Complex.ofReal_intCast] using hs
  exact_mod_cast he

/-- Finite comparison retains the actual signed Möbius prefixes. -/
theorem prefix_abs_le (b N : ℕ) (hb : 2≤b) :
    |residualPrefix b N|≤∑ d∈Finset.Icc 1 N,|tail b d| * |mertens (N/d)| := by
  rw [prefix_mertens b N hb]
  simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
    (fun d => tail b d*mertens (N/d)) (Finset.Icc 1 N)

end OpenAIReview.CyclotomicConvolution

#lint+ in OpenAIReview.CyclotomicConvolution

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty cyclotomic-convolution audit."
  logInfo m!"Cyclotomic-convolution audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-cyclotomic-factorial-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-cyclotomic-factorial-gate/axioms.json"
    (Json.mkObj [("scope",toJson "literal cyclotomic logarithmic residual, full finite floor identity, Mobius residualPrefix comparison; source continuation and ell1 inverse paper-level"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("details",Json.arr reports)]).pretty
