/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorGrowingRamanujan
import RiemannGaussian.EtaMoebiusFinitePrefix
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Normalized growing Ramanujan codes: the full sub-source cutoff gate

Keep every actual prime power, physical endpoint and height phase. The
exact centered code with coefficients eta(q)/q has norm at most
J*log(M)*M*(2+log(M)) at X=2^J, for ANY moduli subset below M and
ANY bounded coefficients. No prime-density theorem is assumed. This
closes a much larger normalized growing family than the older fourth-root
prototype. It does not cover unnormalized or growing nonprincipal codes.
-/

namespace RiemannGaussian.ArithmeticOperatorNormalizedRamanujanAudit
noncomputable section
open ArithmeticOperatorRamanujanAudit ArithmeticOperatorRamanujanPayment
open Filter
open scoped BigOperators Topology

/-- Normalize the additive divisor-form code BEFORE evaluating the prime sum. -/
def normalizedCoefficient (eta : ℕ → ℂ) (q : ℕ) : ℂ := eta q/(q : ℂ)

/-- Remove the common coprime channel exactly, retaining all exceptional powers. -/
def contrast (S : Finset ℕ) (eta : ℕ → ℂ) (X : ℕ) (y : ℝ) : ℂ :=
  codeObservation S (normalizedCoefficient eta) X y-
    principalCoefficient S (normalizedCoefficient eta)*
      ∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*
        SuzukiCarryCorrelation.primePhase y n

/-- Exact finite correction identity with the complete native cutoff. -/
theorem contrast_eq_corrections (S : Finset ℕ) (eta : ℕ → ℂ) (X : ℕ) (y : ℝ) :
    contrast S eta X y =
      ∑ q ∈ S, normalizedCoefficient eta q*correction q X y :=
  codeObservation_sub_principal S (normalizedCoefficient eta) X y

/-- The complete finite mask/coefficient join is algebraic for arbitrary
integer arrays; it supplies no additional PSD or rank constraint. -/
theorem arbitrary_weight_join (D S : Finset ℕ) (eta w : ℕ → ℂ) :
    (∑ n ∈ D, w n*code S (normalizedCoefficient eta) n)-
      principalCoefficient S (normalizedCoefficient eta)*(∑ n ∈ D, w n) =
    ∑ q ∈ S, normalizedCoefficient eta q*
      ∑ n ∈ D, w n*((ramanujanDivisor q n : ℂ)-(ArithmeticFunction.moebius q : ℂ)) := by
  rw [weighted_code_split,add_sub_cancel_left]
  unfold code principalCoefficient
  simp_rw [←Finset.sum_sub_distrib,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Arithmetic normalization pays only the divisor COUNT, not q squared. -/
theorem ramanujanBudget_le_count {q : ℕ} (hq : 0<q) :
    ramanujanBudget q ≤ (q : ℝ)*(q.divisors.card : ℝ) := by
  unfold ramanujanBudget
  calc
    _ ≤ ∑ d ∈ q.divisors, (q : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdq := Nat.le_of_dvd hq (Nat.dvd_of_mem_divisors hd)
      have hm : ‖ArithmeticFunction.moebius (q/d)‖ ≤ (1 : ℝ) := by
        rw [Int.norm_eq_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q/d)
      rw [norm_mul,Int.norm_natCast]
      exact (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg d)).trans
        (by simpa using (show (d : ℝ)≤q by exact_mod_cast hdq))
    _ = _ := by simp; ring

/-- Exact hyperbola reindexing of the full divisor population. -/
theorem divisorCount_sum_eq (M : ℕ) :
    (∑ q ∈ Finset.Icc 1 M, (q.divisors.card : ℝ)) =
      ∑ d ∈ Finset.Icc 1 M, ((M/d : ℕ) : ℝ) := by
  have hh := sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix M (fun _ _ => (1 : ℂ))
  simp_rw [Nat.sum_divisorsAntidiagonal (fun _ _ => (1 : ℂ))] at hh
  have he : (∑ q ∈ Finset.Icc 1 M, (q.divisors.card : ℂ)) =
      ∑ d ∈ Finset.Icc 1 M, ((M/d : ℕ) : ℂ) := by simpa using hh
  simpa only [Complex.re_sum,Complex.natCast_re] using congrArg Complex.re he

/-- Mean divisor count with the literal floor endpoints retained. -/
theorem divisorCount_sum_le (M : ℕ) :
    (∑ q ∈ Finset.Icc 1 M, (q.divisors.card : ℝ)) ≤ (M : ℝ)*(1+Real.log M) := by
  rw [divisorCount_sum_eq]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 M, (M : ℝ)/d :=
      Finset.sum_le_sum (fun _ _ => Nat.cast_div_le)
    _ = (M : ℝ)*(harmonic M : ℝ) := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,
        div_eq_mul_inv,Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log M) (Nat.cast_nonneg M)

/-- One normalized modulus, before summing any of the actual prime powers. -/
theorem norm_normalized_correction_le {q : ℕ} (hq : 0<q) {eta : ℕ → ℂ}
    (heta : ‖eta q‖≤1) (J : ℕ) (y : ℝ) :
    ‖normalizedCoefficient eta q*correction q (2^J) y‖ ≤
      ((q.divisors.card : ℝ)+1)*((J : ℝ)*Real.log q) := by
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq
  have hlog : 0≤Real.log q := Real.log_natCast_nonneg q
  have hn : ‖normalizedCoefficient eta q‖ ≤ 1/(q : ℝ) := by
    unfold normalizedCoefficient
    rw [norm_div,Complex.norm_natCast]
    exact div_le_div_of_nonneg_right heta hqR.le
  have hm : ‖ArithmeticFunction.moebius q‖ ≤ (1 : ℝ) := by
    rw [Int.norm_eq_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
  have hb : (ramanujanBudget q+‖ArithmeticFunction.moebius q‖)/(q : ℝ) ≤
      (q.divisors.card : ℝ)+1 := by
    apply (div_le_iff₀ hqR).mpr
    have hq1 : (1 : ℝ)≤q := by exact_mod_cast hq
    nlinarith only [ramanujanBudget_le_count hq,hm,hq1]
  rw [norm_mul]
  calc
    _ ≤ (1/(q : ℝ))*‖correction q (2^J) y‖ :=
      mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ ≤ (1/(q : ℝ))*((ramanujanBudget q+‖ArithmeticFunction.moebius q‖)*
        ((J : ℝ)*Real.log q)) :=
      mul_le_mul_of_nonneg_left (norm_correction_le hq y J) (by positivity)
    _ = (ramanujanBudget q+‖ArithmeticFunction.moebius q‖)/(q : ℝ)*
        ((J : ℝ)*Real.log q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (mul_nonneg (Nat.cast_nonneg J) hlog)

/-- All normalized moduli up to M cost only M times logarithms, with
their FULL actual-prime phase and every proper power included. -/
theorem norm_contrast_le {S : Finset ℕ} {M : ℕ} {eta : ℕ → ℂ}
    (hS : S ⊆ Finset.Icc 1 M) (heta : ∀ q ∈ S, ‖eta q‖≤1) (J : ℕ) (y : ℝ) :
    ‖contrast S eta (2^J) y‖ ≤ (J : ℝ)*Real.log M*(M : ℝ)*(2+Real.log M) := by
  rw [contrast_eq_corrections]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ q ∈ S, ((q.divisors.card : ℝ)+1)*((J : ℝ)*Real.log M) := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hq0,hqM⟩ := Finset.mem_Icc.mp (hS hq)
      apply (norm_normalized_correction_le (by omega : 0<q) (heta q hq) J y).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (by exact_mod_cast hq0 : (0 : ℝ)<q) (by exact_mod_cast hqM))
        (Nat.cast_nonneg J)
    _ ≤ ∑ q ∈ Finset.Icc 1 M,
        ((q.divisors.card : ℝ)+1)*((J : ℝ)*Real.log M) :=
      Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by
        exact mul_nonneg (by positivity)
          (mul_nonneg (Nat.cast_nonneg J) (Real.log_natCast_nonneg M)))
    _ = ((∑ q ∈ Finset.Icc 1 M, (q.divisors.card : ℝ))+(M : ℝ))*
        ((J : ℝ)*Real.log M) := by rw [←Finset.sum_mul,Finset.sum_add_distrib]; simp
    _ ≤ ((M : ℝ)*(1+Real.log M)+(M : ℝ))*((J : ℝ)*Real.log M) :=
      mul_le_mul_of_nonneg_right (by linarith only [divisorCount_sum_le M])
        (mul_nonneg (Nat.cast_nonneg J) (Real.log_natCast_nonneg M))
    _ = _ := by ring

/-- The exact correction cannot see ANY power of a prime above the
modulus cutoff. All exponents, not just ordinary primes, are retained. -/
theorem primePower_atom_zero {S : Finset ℕ} {M p k : ℕ} (eta : ℕ → ℂ)
    (hS : S ⊆ Finset.Icc 1 M) (hp : p.Prime) (hMp : M<p) (hk : 0<k) :
    code S (normalizedCoefficient eta) (p^k)-
      principalCoefficient S (normalizedCoefficient eta) = 0 := by
  rw [code_of_coprime S (normalizedCoefficient eta) ?_,sub_self]
  intro q hq
  obtain ⟨hq0,hqM⟩ := Finset.mem_Icc.mp (hS hq)
  have hpc : Nat.Coprime p q := by
    by_contra hh
    have hdvd : p∣q := hp.dvd_iff_not_coprime.mpr hh
    have hle := Nat.le_of_dvd (by omega : 0<q) hdvd
    omega
  exact (Nat.coprime_pow_right_iff hk q p).mpr hpc.symm

/-- General rational sub-source cutoff: every normalized centered code
is geometrically source-small once B/A<beta. No zero assumption,
simple-source assumption or prime-distribution hypothesis is used. -/
theorem tendsto_subsource_contrast {S : ℕ → Finset ℕ} {eta : ℕ → ℕ → ℂ}
    {A B : ℕ} {beta : ℝ}
    (hS : ∀ J, S J ⊆ Finset.Icc 1 (2^(B*J)))
    (heta : ∀ J q, q ∈ S J → ‖eta J q‖≤1)
    (hgap : (B : ℝ)<(A : ℝ)*beta) (y : ℝ) :
    Tendsto (fun J : ℕ => (Real.exp (-(A : ℝ)*beta*Real.log 2)^J : ℂ)*
      contrast (S J) (eta J) (2^(A*J)) y) atTop (𝓝 0) := by
  let a := Real.exp (-(A : ℝ)*beta*Real.log 2)
  let r := Real.exp (((B : ℝ)-(A : ℝ)*beta)*Real.log 2)
  have ha : 0≤a := (Real.exp_pos _).le
  have hr0 : 0≤r := (Real.exp_pos _).le
  have hr1 : r<1 := Real.exp_lt_one_iff.mpr (by
    have hlog : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    nlinarith only [hlog,hgap])
  have he : a*(2 : ℝ)^B=r := by
    dsimp [a,r]
    rw [show (2 : ℝ)^B=Real.exp ((B : ℝ)*Real.log 2) by
      rw [←Real.log_pow,Real.exp_log (by positivity)]]
    rw [←Real.exp_add]
    congr 1
    ring
  have ht2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 hr0 hr1
  have ht3 := tendsto_pow_const_mul_const_pow_of_lt_one 3 hr0 hr1
  have ht : Tendsto (fun J : ℕ =>
      (A : ℝ)*B*Real.log 2*
        (2*((J : ℝ)^2*r^J)+(B : ℝ)*Real.log 2*((J : ℝ)^3*r^J)))
      atTop (𝓝 0) := by
    simpa using ((ht2.const_mul 2).add (ht3.const_mul ((B : ℝ)*Real.log 2))).const_mul
      ((A : ℝ)*B*Real.log 2)
  apply squeeze_zero_norm (a := fun J : ℕ =>
      (A : ℝ)*B*Real.log 2*
        (2*((J : ℝ)^2*r^J)+(B : ℝ)*Real.log 2*((J : ℝ)^3*r^J))) _ ht
  intro J
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg ha]
  apply (mul_le_mul_of_nonneg_left
    (norm_contrast_le (hS J) (heta J) (A*J) y) (pow_nonneg ha J)).trans_eq
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  rw [pow_mul]
  calc
    _ = ((A : ℝ)*B*Real.log 2)*
        ((J : ℝ)^2*(2+(B : ℝ)*J*Real.log 2))*(a*(2 : ℝ)^B)^J := by
      rw [mul_pow]
      ring
    _ = _ := by rw [he]; ring

/-- A nonzero matched source is IMPOSSIBLE in the entire bounded
normalized sub-source family; this is a rejection gate, not a zero exclusion. -/
theorem no_nonzero_source {S : ℕ → Finset ℕ} {eta : ℕ → ℕ → ℂ}
    {A B : ℕ} {beta : ℝ}
    (hS : ∀ J, S J ⊆ Finset.Icc 1 (2^(B*J)))
    (heta : ∀ J q, q ∈ S J → ‖eta J q‖≤1)
    (hgap : (B : ℝ)<(A : ℝ)*beta) (y : ℝ) {v : ℂ} (hv : v≠0) :
    ¬Tendsto (fun J : ℕ => (Real.exp (-(A : ℝ)*beta*Real.log 2)^J : ℂ)*
      contrast (S J) (eta J) (2^(A*J)) y) atTop (𝓝 v) := by
  intro hh
  exact hv (tendsto_nhds_unique hh (tendsto_subsource_contrast hS heta hgap y))

/-- Explicit near-full cutoff, covering EVERY campaign exponent,
including the lower endpoint beta=19999/20000. -/
theorem tendsto_campaign_near_full_code {S : ℕ → Finset ℕ} {eta : ℕ → ℕ → ℂ}
    (hS : ∀ J, S J ⊆ Finset.Icc 1 (2^(19998*J)))
    (heta : ∀ J q, q ∈ S J → ‖eta J q‖≤1)
    {beta : ℝ} (hbeta : 19999/20000≤beta) (y : ℝ) :
    Tendsto (fun J : ℕ => (Real.exp (-20000*beta*Real.log 2)^J : ℂ)*
      contrast (S J) (eta J) (2^(20000*J)) y) atTop (𝓝 0) := by
  exact tendsto_subsource_contrast hS heta (by push_cast; linarith only [hbeta]) y

/-- If principal centering is imposed on the code itself, the WHOLE
observation loses the source, not just its correction remainder. -/
theorem tendsto_centered_observation {S : ℕ → Finset ℕ} {eta : ℕ → ℕ → ℂ}
    {A B : ℕ} {beta : ℝ}
    (hS : ∀ J, S J ⊆ Finset.Icc 1 (2^(B*J)))
    (heta : ∀ J q, q ∈ S J → ‖eta J q‖≤1)
    (hc : ∀ J, principalCoefficient (S J) (normalizedCoefficient (eta J))=0)
    (hgap : (B : ℝ)<(A : ℝ)*beta) (y : ℝ) :
    Tendsto (fun J : ℕ => (Real.exp (-(A : ℝ)*beta*Real.log 2)^J : ℂ)*
      codeObservation (S J) (normalizedCoefficient (eta J)) (2^(A*J)) y)
      atTop (𝓝 0) := by
  simpa only [contrast,hc,zero_mul,sub_zero] using
    tendsto_subsource_contrast hS heta hgap y

end
end RiemannGaussian.ArithmeticOperatorNormalizedRamanujanAudit
