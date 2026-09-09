/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeGram
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Signed logarithmic prime moments

Every higher derivative of the actual zeta logarithmic derivative is a
convergent complex prime moment in the Euler half-plane. Finite polynomial
filters act on consecutive moments without discarding their phases. This
is the arithmetic interface for isolating individual local zero modes.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- Alternating Taylor normalization, which gives positive log powers in
the Euler series of the negative logarithmic derivative. -/
def signedTaylorMoment (n : ℕ) (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  (-1) ^ n / (n.factorial : ℂ) * iteratedDeriv n f s

/-- The actual complex prime moment, with its full oscillatory phase. -/
def zetaPrimeLogMoment (n : ℕ) (s : ℂ) : ℂ :=
  signedTaylorMoment n (fun z ↦ -logDeriv riemannZeta z) s

/-- Von Mangoldt's Euler series converges absolutely beyond real part one. -/
theorem abscissaOfAbsConv_vonMangoldt_le_one :
    LSeries.abscissaOfAbsConv (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
  intro y hy
  exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy)

private theorem vonMangoldt_abscissa_lt {s : ℂ} (hs : 1 < s.re) :
    LSeries.abscissaOfAbsConv (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) < s.re :=
  lt_of_le_of_lt abscissaOfAbsConv_vonMangoldt_le_one (by exact_mod_cast hs)

private theorem iterated_logMul_apply (f : ℕ → ℂ) (k n : ℕ) :
    (LSeries.logMul^[k] f) n = (Real.log n : ℂ) ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', LSeries.logMul, ih, ← Complex.natCast_log]
    ring

/-- Higher derivatives retain the complete logarithmic Euler series. -/
theorem iteratedDeriv_neg_logDeriv_riemannZeta {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    iteratedDeriv n (fun z ↦ -logDeriv riemannZeta z) s =
      (-1) ^ n * LSeries
        (LSeries.logMul^[n] (fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ))) s := by
  have he : (fun z ↦ -logDeriv riemannZeta z) =ᶠ[𝓝 s]
      LSeries (fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ)) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
    exact neg_logDeriv_riemannZeta_eq_vonMangoldt hz
  rw [he.iteratedDeriv_eq n, LSeries_iteratedDeriv n (vonMangoldt_abscissa_lt hs)]

/-- The alternating normalization cancels the derivative signs exactly. -/
theorem zetaPrimeLogMoment_eq_LSeries {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    zetaPrimeLogMoment n s =
      LSeries (LSeries.logMul^[n] (fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ))) s /
        (n.factorial : ℂ) := by
  rw [zetaPrimeLogMoment, signedTaylorMoment, iteratedDeriv_neg_logDeriv_riemannZeta hs]
  have hsign : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  calc
    _ = ((-1 : ℂ) ^ n * (-1) ^ n) *
        LSeries (LSeries.logMul^[n] (fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ))) s /
          (n.factorial : ℂ) := by ring
    _ = _ := by rw [hsign, one_mul]

private theorem logMoment_term (s : ℂ) (k n : ℕ) :
    LSeries.term (LSeries.logMul^[k] (fun m ↦ (ArithmeticFunction.vonMangoldt m : ℂ))) s n =
      (ArithmeticFunction.vonMangoldt n : ℂ) * (Real.log n : ℂ) ^ k *
        zetaPrimeFeature s n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.term_of_ne_zero hn, iterated_logMul_apply, div_eq_mul_inv,
      Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn),
      ← Complex.natCast_log, ← Complex.exp_neg]
    unfold zetaPrimeFeature
    rw [mul_comm (Real.log n : ℂ) s]
    ring

/-- The literal log-weighted prime sum converges to the normalized actual
zeta derivative. This is a `HasSum`, not a totalized divergent sum. -/
theorem hasSum_zetaPrimeLogMoment {s : ℂ} (hs : 1 < s.re) (k : ℕ) :
    HasSum (fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ) *
      ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * zetaPrimeFeature s n)
      (zetaPrimeLogMoment k s) := by
  rw [zetaPrimeLogMoment_eq_LSeries hs]
  have h := LSeriesSummable_of_abscissaOfAbsConv_lt_re
    (f := LSeries.logMul^[k] (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)))
    (s := s) (by simpa using vonMangoldt_abscissa_lt hs)
  apply (h.hasSum.div_const (k.factorial : ℂ)).congr_fun
  intro n
  rw [logMoment_term]
  ring

/-- An exact finite filter of consecutive prime moments. -/
def zetaPrimeLogFilter (p : Polynomial ℂ) (start : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ p.support, p.coeff k * zetaPrimeLogMoment (start + k) s

/-- The same filter is one explicit convergent arithmetic sum. All cross
phase cancellation takes place before a norm or real part is taken. -/
theorem hasSum_zetaPrimeLogFilter {s : ℂ} (hs : 1 < s.re)
    (p : Polynomial ℂ) (start : ℕ) :
    HasSum (fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ) * zetaPrimeFeature s n *
      ∑ k ∈ p.support, p.coeff k *
        ((Real.log n : ℂ) ^ (start + k) / ((start + k).factorial : ℂ)))
      (zetaPrimeLogFilter p start s) := by
  have h := hasSum_sum (s := p.support) (fun k _ ↦
    (hasSum_zetaPrimeLogMoment hs (start + k)).mul_left (p.coeff k))
  apply h.congr_fun
  intro n
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

end

end RiemannGaussian
