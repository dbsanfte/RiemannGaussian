/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeCompletionPhase

/-!+# A general completion rate and its analytic tilt optimum

Retain the source radius, moving factorial order, literal physical length,
and genuine summability exponent in one explicit scalar rate. These are
independent completion bounds, not signed cancellation assumptions.
-/

namespace RiemannGaussian.ZetaRieszPrimeCompletionRate
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimeCompletion ZetaRieszAnnulusJoint ZetaExposedPrimeMoments
open ZetaRieszPrimePairConvolution

/-- The upper-prime completion exponent before choosing any tilt. -/
def completionExponent (u theta ell q sigma : ℝ) : ℝ :=
  theta * Real.log (u / q) - (3 / 2 - q - sigma) * ell

/-- Every admissible tilt retains the same exact source/order budget. -/
theorem upper_scalar_of_rate {u theta ell q sigma eps L : ℝ}
    (hu : 0 < u) (hq : 0 < q) (hqu : q ≤ u)
    (hgap : 0 ≤ 3 / 2 - q - sigma)
    (hrate : completionExponent u theta ell q sigma ≤ -eps)
    (N k : ℕ) (hk : (k : ℝ) ≤ theta * N) (hL : ell * N ≤ L) :
    u ^ k * (q⁻¹ ^ k * Real.exp (-(3 / 2 - q - sigma) * L)) ≤
      Real.exp (-eps * N) := by
  have hlog : 0 ≤ Real.log (u / q) := Real.log_nonneg ((one_le_div hq).mpr hqu)
  have horder := mul_le_mul_of_nonneg_right hk hlog
  have hlength := mul_le_mul_of_nonneg_left hL hgap
  have hbudget := mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg (α := ℝ) N)
  have heq : u ^ k * (q⁻¹ ^ k * Real.exp (-(3 / 2 - q - sigma) * L)) =
      Real.exp ((k : ℝ) * Real.log (u / q) - (3 / 2 - q - sigma) * L) := by
    rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (div_pos hu hq),
      div_pow, neg_mul, Real.exp_neg]
    simp only [inv_pow]
    ring
  rw [heq]
  apply Real.exp_le_exp.mpr
  dsimp only [completionExponent] at hbudget
  nlinarith only [horder, hlength, hbudget]

/-- Every strictly positive physical slope below the true cutoff slope
gives the general upper completion estimate, uniformly over all heights
and all orders below the chosen proportional ceiling. -/
theorem eventually_norm_physicalPrimeTail_of_rate {u theta ell q sigma eps : ℝ}
    (hu : 0 < u) (hell : 0 ≤ ell) (hue : u < Real.exp (-(ell / 2)))
    (hq : 0 < q) (hqu : q ≤ u) (hsigma : 1 < sigma)
    (hgap : 0 ≤ 3 / 2 - q - sigma)
    (hrate : completionExponent u theta ell q sigma ≤ -eps) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, (k : ℝ) ≤ theta * N → ∀ y : ℝ,
      ‖(u : ℂ) ^ k * physicalPrimeTail u N k y‖ ≤
        Real.exp (-eps * N) * ∑' n, zetaPrimeExpWeight sigma n := by
  filter_upwards [ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu
    (show 0 ≤ ell / 2 by positivity) hue] with N hLN
  intro k hk y
  have hb := norm_maskedMoment_upper_le (fun p => p.Prime ∧
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p)
    k y (SquarefreeVaughanLogSource.length u N) hq hsigma hgap
    (fun p hp => physicalPrimeTail_log_support u N p hp.2)
  have hs := upper_scalar_of_rate hu hq hqu hgap hrate N k hk
    (show ell * N ≤ SquarefreeVaughanLogSource.length u N by nlinarith [hLN])
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ k * ((q⁻¹ ^ k * Real.exp (-(3 / 2 - q - sigma) *
        SquarefreeVaughanLogSource.length u N)) * ∑' n, zetaPrimeExpWeight sigma n) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hu.le _)
    _ = (u ^ k * (q⁻¹ ^ k * Real.exp (-(3 / 2 - q - sigma) *
        SquarefreeVaughanLogSource.length u N))) * ∑' n, zetaPrimeExpWeight sigma n := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hs (tsum_nonneg (fun _ => (Real.exp_pos _).le))

/-- The loss from any positive tilt has an exact nonnegative logarithmic
form relative to the ideal tilt theta/ell. -/
theorem completionExponent_sub_ideal {u theta ell q sigma : ℝ}
    (hu : 0 < u) (htheta : 0 < theta) (hell : 0 < ell) (hq : 0 < q) :
    completionExponent u theta ell q sigma -
      completionExponent u theta ell (theta / ell) sigma =
      theta * (q * ell / theta - 1 - Real.log (q * ell / theta)) := by
  have hlog : Real.log (u / q) - Real.log (u / (theta / ell)) =
      -Real.log (q * ell / theta) := by
    rw [Real.log_div hu.ne' hq.ne',
      Real.log_div hu.ne' (div_pos htheta hell).ne',
      Real.log_div (mul_pos hq hell).ne' htheta.ne',
      Real.log_mul hq.ne' hell.ne', Real.log_div htheta.ne' hell.ne']
    ring
  dsimp only [completionExponent]
  calc
    _ = theta * (Real.log (u / q) - Real.log (u / (theta / ell))) +
        q * ell - theta := by field_simp; ring
    _ = _ := by rw [hlog]; field_simp; ring

/-- The mathematically defined ideal tilt minimizes the completion
exponent over every positive exponential tilt, without a coefficient search. -/
theorem completionExponent_ideal_le {u theta ell q sigma : ℝ}
    (hu : 0 < u) (htheta : 0 < theta) (hell : 0 < ell) (hq : 0 < q) :
    completionExponent u theta ell (theta / ell) sigma ≤
      completionExponent u theta ell q sigma := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos (mul_pos hq hell) htheta)
  have hnonneg := mul_nonneg htheta.le (sub_nonneg.mpr hlog)
  rw [← completionExponent_sub_ideal hu htheta hell hq] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- Every nonideal positive tilt has strictly larger exponent. -/
theorem completionExponent_ideal_lt {u theta ell q sigma : ℝ}
    (hu : 0 < u) (htheta : 0 < theta) (hell : 0 < ell) (hq : 0 < q)
    (hne : q ≠ theta / ell) :
    completionExponent u theta ell (theta / ell) sigma <
      completionExponent u theta ell q sigma := by
  have hx : q * ell / theta ≠ 1 := by
    intro h
    apply hne
    apply (eq_div_iff hell.ne').mpr
    have hmul := (div_eq_iff htheta.ne').mp h
    simpa only [one_mul] using hmul
  have hlog := Real.log_lt_sub_one_of_pos (div_pos (mul_pos hq hell) htheta) hx
  have hpos := mul_pos htheta (sub_pos.mpr hlog)
  rw [← completionExponent_sub_ideal hu htheta hell hq] at hpos
  exact sub_pos.mp hpos

/-- The same independent completion criterion controls the exact finite
minus complete prime array; both omitted support ranges are retained. -/
theorem eventually_norm_finite_sub_complete_of_rate {u theta ell q sigma eps : ℝ}
    (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hell : 0 ≤ ell) (hue : u < Real.exp (-(ell / 2)))
    (hq : 0 < q) (hqu : q ≤ u) (hsigma : 1 < sigma)
    (hgap : 0 ≤ 3 / 2 - q - sigma)
    (hrate : completionExponent u theta ell q sigma ≤ -eps) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, N ≤ 3 * k → (k : ℝ) ≤ theta * N → ∀ y : ℝ,
      ‖(u : ℂ) ^ k * (finiteMoment (intermediatePrimes u N) k
        (3 / 2 + Complex.I * y) - ordinaryPrimeMoment k (3 / 2 + Complex.I * y))‖ ≤
        Real.exp (-(95 / 3072 : ℝ) * N) * (∑' n, zetaPrimeExpWeight (1025 / 1024) n) +
          Real.exp (-eps * N) * ∑' n, zetaPrimeExpWeight sigma n := by
  have hu1 : u < 1 := huh.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  filter_upwards [eventually_norm_physicalPrimeTail_of_rate hu hell hue hq hqu hsigma hgap hrate,
    eventually_norm_smallPrimeMoment_le hu huh,
    ZetaRieszSemiprimeSupport.eventually_quadratic_head_lt_physical hu hu1] with N hhigh hlow hNX
  intro k hklo hkhi y
  rw [ordinaryPrimeMoment_eq_actual_split u N k y hNX]
  have he (a b c : ℂ) : a - (b + a + c) = -(b + c) := by ring
  rw [he, mul_neg, norm_neg, mul_add]
  exact (norm_add_le _ _).trans (add_le_add (hlow k hklo y) (hhigh k hkhi y))

/-- A rigorous logarithm enclosure for one wider order interval. -/
theorem log_five_halves_le : Real.log (5 / 2 : ℝ) ≤ 11 / 12 := by
  rw [Real.log_div (by norm_num) (by norm_num)]
  linarith [Real.log_five_lt_d9, Real.log_two_gt_d9]

/-- The general exponent criterion proves a larger concrete order range
through 17N/32 at every radius in the existing annular interval. -/
theorem wider_rate {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    completionExponent u (17 / 32) (4 / 3) (2 / 5) (8193 / 8192) ≤ -(11 / 30720) := by
  have hlu : Real.log u ≤ -(2 / 3 : ℝ) := by
    simpa only [Real.log_exp] using (Real.log_lt_log hu huh).le
  have hlog : Real.log (u / (2 / 5 : ℝ)) = Real.log u + Real.log (5 / 2 : ℝ) := by
    rw [show u / (2 / 5 : ℝ) = u * (5 / 2) by ring,
      Real.log_mul hu.ne' (by norm_num)]
  dsimp only [completionExponent]
  rw [hlog]
  linarith [log_five_halves_le]

/-- Independent uniform completion now reaches a wider actual order
band, with every floor endpoint and both convergent omitted sums paid. -/
theorem eventually_norm_wider_completion {u : ℝ} (hu : 1 / 2 ≤ u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, N ≤ 3 * k → 32 * k ≤ 17 * N → ∀ y : ℝ,
      ‖(u : ℂ) ^ k * (finiteMoment (intermediatePrimes u N) k
        (3 / 2 + Complex.I * y) - ordinaryPrimeMoment k (3 / 2 + Complex.I * y))‖ ≤
        Real.exp (-(11 / 30720 : ℝ) * N) *
          ((∑' n, zetaPrimeExpWeight (1025 / 1024) n) +
            ∑' n, zetaPrimeExpWeight (8193 / 8192) n) := by
  have hu0 : 0 < u := by linarith
  have h := eventually_norm_finite_sub_complete_of_rate hu0 huh
    (show (0 : ℝ) ≤ 4 / 3 by norm_num) (by norm_num; exact huh)
    (show (0 : ℝ) < 2 / 5 by norm_num) (show (2 / 5 : ℝ) ≤ u by linarith)
    (show (1 : ℝ) < 8193 / 8192 by norm_num) (by norm_num) (wider_rate hu0 huh)
  filter_upwards [h] with N hN
  intro k hklo hkhi y
  have hk : (k : ℝ) ≤ (17 / 32 : ℝ) * N := by
    have hkc : 32 * (k : ℝ) ≤ 17 * N := by exact_mod_cast hkhi
    linarith
  have he : Real.exp (-(95 / 3072 : ℝ) * N) ≤ Real.exp (-(11 / 30720 : ℝ) * N) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  apply (hN k hklo hk y).trans
  rw [mul_add]
  exact add_le_add
    (mul_le_mul_of_nonneg_right he (tsum_nonneg (fun _ => (Real.exp_pos _).le))) le_rfl

/-- The exact derivative weight also has vanishing independent error
on every moving order and moving height in the enlarged band. -/
theorem tendsto_wider_weighted_error (k : ℕ → ℕ) (y : ℕ → ℝ)
    {u : ℝ} (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hk : ∀ᶠ N : ℕ in atTop, N ≤ 3 * k N ∧ 32 * k N ≤ 17 * N) :
    Tendsto (fun N : ℕ => (k N : ℂ) * ((u : ℂ) ^ k N *
      (finiteMoment (intermediatePrimes u N) (k N) (3 / 2 + Complex.I * y N) -
        ordinaryPrimeMoment (k N) (3 / 2 + Complex.I * y N)))) atTop (nhds 0) := by
  let r : ℝ := Real.exp (-(11 / 30720 : ℝ))
  let Z : ℝ := (∑' n, zetaPrimeExpWeight (1025 / 1024) n) +
    ∑' n, zetaPrimeExpWeight (8193 / 8192) n
  have hZ : 0 ≤ Z := add_nonneg (tsum_nonneg (fun _ => (Real.exp_pos _).le))
    (tsum_nonneg (fun _ => (Real.exp_pos _).le))
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have he (N : ℕ) : Real.exp (-(11 / 30720 : ℝ) * N) = r ^ N := by
    rw [mul_comm, Real.exp_nat_mul]
  apply squeeze_zero_norm' (a := fun N : ℕ => (N + 1 : ℝ) ^ 2 * r ^ N * Z) (by
    filter_upwards [eventually_norm_wider_completion hu huh, hk] with N hN hkN
    have hNk : k N ≤ N := by omega
    have hc : (k N : ℝ) ≤ (N + 1 : ℝ) ^ 2 := by
      have hcast : (k N : ℝ) ≤ N := by exact_mod_cast hNk
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    rw [norm_mul, Complex.norm_natCast]
    calc
      _ ≤ (k N : ℝ) * (Real.exp (-(11 / 30720 : ℝ) * N) * Z) :=
        mul_le_mul_of_nonneg_left (hN (k N) hkN.1 hkN.2 (y N)) (Nat.cast_nonneg _)
      _ = (k N : ℝ) * r ^ N * Z := by rw [he]; ring
      _ ≤ (N + 1 : ℝ) ^ 2 * r ^ N * Z :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (pow_nonneg hr0 _)) hZ)
  simpa only [zero_mul] using
    (ZetaRieszShiftedHeadBudget.tendsto_quadratic_geometric hr0 hr1).mul_const Z

/-- Exposed phases transfer to every moving finite order in the wider
band after the independent derivative-weighted error is paid. -/
theorem tendsto_wider_weighted_finite (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ)))
    (k : ℕ → ℕ)
    (hk : ∀ᶠ N : ℕ in atTop, N ≤ 3 * k N ∧ 32 * k N ≤ 17 * N) :
    Tendsto (fun N : ℕ => (k N : ℂ) *
      (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ k N *
        finiteMoment (intermediatePrimes (3 / 2 - rho.1.re) N) (k N)
          (3 / 2 + Complex.I * (rho.1.im : ℂ))))
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hkt : Tendsto k atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hk, eventually_ge_atTop (3 * b)] with N hkN hNb
    omega
  have hu : (1 / 2 : ℝ) ≤ 3 / 2 - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have h := ((ZetaRieszPrimeCompletionPhase.tendsto_weighted_complete rho hrho hexposed).comp hkt).add
    (tendsto_wider_weighted_error k (fun _ => rho.1.im) hu huh hk)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [] with N
  dsimp only [Function.comp_def]
  ring

end
end RiemannGaussian.ZetaRieszPrimeCompletionRate
