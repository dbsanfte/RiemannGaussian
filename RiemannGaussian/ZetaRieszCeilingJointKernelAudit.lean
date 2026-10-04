/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeKernelLaplace
import RiemannGaussian.ZetaRieszCeilingFejerCluster

/-!
# Audit of joint moving-kernel norm payment

Join every complex coefficient FIRST. Even this complete kernel's positive
Laplace price cannot remain bounded if the selected source is preserved and
the separated positive analytic budget tends to zero. The result allows
arbitrary moving kernels and polynomial degrees, not only fixed filters.
It concerns that norm-payment mechanism, not the actual signed prime sum.
The original all-height 42/25 ceiling and all earlier positive/no-go results
remain unchanged and open. No synthetic density is transported to primes.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Complex MeasureTheory Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCeilingJointKernelAudit

/-- The norm is taken after collecting the ENTIRE complex kernel. -/
def price (f : ℝ → ℂ) (d : ℝ) : ℝ :=
  ∫ t : ℝ in Set.Ioi 0, ‖f t‖*Real.exp (-d*t)

/-- The signed source response, with its coefficients still joined. -/
def response (f : ℝ → ℂ) (d : ℝ) : ℂ :=
  ∫ t : ℝ in Set.Ioi 0, Real.exp (-d*t) • f t

/-- Positive pricing does not invent a negative allowance. -/
theorem price_nonneg (f : ℝ → ℂ) (d : ℝ) : 0 <= price f d :=
  integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)

/-- The exact complex source must be preserved before applying a norm. -/
theorem response_norm_le_price (f : ℝ → ℂ) (d : ℝ) : ‖response f d‖ <= price f d := by
  have h := norm_integral_le_integral_norm
    (fun t : ℝ => Real.exp (-d*t) • f t) (μ := volume.restrict (Set.Ioi 0))
  simpa only [response, price, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le,
    mul_comm] using h

/-- Two exterior positive prices bound the middle damping, at ANY
split point. This retains the joined kernel and makes no coefficientwise
estimate, density comparison or actual-prime approximation. -/
theorem price_split (f : ℝ → ℂ) {a u q : ℝ} (hau : a < u) (huq : u < q)
    (ha : IntegrableOn (fun t : ℝ => ‖f t‖*Real.exp (-a*t)) (Set.Ioi 0))
    (hu : IntegrableOn (fun t : ℝ => ‖f t‖*Real.exp (-u*t)) (Set.Ioi 0))
    (hq : IntegrableOn (fun t : ℝ => ‖f t‖*Real.exp (-q*t)) (Set.Ioi 0))
    (T : ℝ) :
    price f u <= Real.exp ((q-u)*T)*price f q+
      Real.exp (-(u-a)*T)*price f a := by
  have hb (t : ℝ) : ‖f t‖*Real.exp (-u*t) <=
      Real.exp ((q-u)*T)*(‖f t‖*Real.exp (-q*t))+
      Real.exp (-(u-a)*T)*(‖f t‖*Real.exp (-a*t)) := by
    by_cases ht : t <= T
    · have he : Real.exp (-u*t) <= Real.exp ((q-u)*T)*Real.exp (-q*t) := by
        rw [<-Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith only [mul_le_mul_of_nonneg_left ht (show 0 <= q-u by linarith only [huq])]
      have hm := mul_le_mul_of_nonneg_left he (norm_nonneg (f t))
      have hp : 0 <= Real.exp (-(u-a)*T)*(‖f t‖*Real.exp (-a*t)) := by positivity
      nlinarith only [hm, hp]
    · have he : Real.exp (-u*t) <= Real.exp (-(u-a)*T)*Real.exp (-a*t) := by
        rw [<-Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith only [mul_le_mul_of_nonneg_left (le_of_not_ge ht)
          (show 0 <= u-a by linarith only [hau])]
      have hm := mul_le_mul_of_nonneg_left he (norm_nonneg (f t))
      have hp : 0 <= Real.exp ((q-u)*T)*(‖f t‖*Real.exp (-q*t)) := by positivity
      nlinarith only [hm, hp]
  have hupper := (hq.const_mul (Real.exp ((q-u)*T))).add
    (ha.const_mul (Real.exp (-(u-a)*T)))
  have h := integral_mono hu hupper hb
  simpa only [price, Pi.add_apply, integral_add (hq.const_mul _) (ha.const_mul _),
    integral_const_mul] using h

/-- Uniformly small separated price forces an arbitrarily large price
at the arithmetic damping. The source remains signed until this step. -/
theorem eventually_price_lower (f : ℕ → ℝ → ℂ) {a u q : ℝ}
    (hau : a < u) (huq : u < q)
    (ha : ∀ N, IntegrableOn (fun t : ℝ => ‖f N t‖*Real.exp (-a*t)) (Set.Ioi 0))
    (hu : ∀ N, IntegrableOn (fun t : ℝ => ‖f N t‖*Real.exp (-u*t)) (Set.Ioi 0))
    (hq : ∀ N, IntegrableOn (fun t : ℝ => ‖f N t‖*Real.exp (-q*t)) (Set.Ioi 0))
    (hsource : ∀ N, 1 <= ‖response (f N) u‖)
    (hpaid : Tendsto (fun N => price (f N) q) atTop (𝓝 0)) (T : ℝ) :
    ∀ᶠ N : ℕ in atTop, (1/2 : ℝ)*Real.exp ((u-a)*T) <= price (f N) a := by
  have hp := hpaid.eventually (gt_mem_nhds
    (show (0 : ℝ) < 1/(2*Real.exp ((q-u)*T)) by positivity))
  filter_upwards [hp] with N hN
  have hc : Real.exp ((q-u)*T)*price (f N) q < 1/2 := by
    have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2*Real.exp ((q-u)*T))).mp hN
    nlinarith only [h]
  have hm := (hsource N).trans ((response_norm_le_price (f N) u).trans
    (price_split (f N) hau huq (ha N) (hu N) (hq N) T))
  have hl : 1/2 <= Real.exp (-(u-a)*T)*price (f N) a := by linarith only [hm, hc]
  have hcancel : Real.exp ((u-a)*T)*Real.exp (-(u-a)*T) = 1 := by
    rw [<-Real.exp_add]
    rw [show (u-a)*T+ -(u-a)*T = 0 by ring, Real.exp_zero]
  calc
    _ = Real.exp ((u-a)*T)*(1/2) := by ring
    _ <= Real.exp ((u-a)*T)*(Real.exp (-(u-a)*T)*price (f N) a) :=
      mul_le_mul_of_nonneg_left hl (Real.exp_pos _).le
    _ = _ := by rw [<-mul_assoc, hcancel, one_mul]

/-- ALL moving joined kernels fail a bounded norm-price endgame if
their generic separated analytic price is paid to zero. This is a method
audit, not a lower bound for the actual signed carrier. -/
theorem price_tendsto_atTop (f : ℕ → ℝ → ℂ) {a u q : ℝ}
    (hau : a < u) (huq : u < q)
    (ha : ∀ N, IntegrableOn (fun t : ℝ => ‖f N t‖*Real.exp (-a*t)) (Set.Ioi 0))
    (hu : ∀ N, IntegrableOn (fun t : ℝ => ‖f N t‖*Real.exp (-u*t)) (Set.Ioi 0))
    (hq : ∀ N, IntegrableOn (fun t : ℝ => ‖f N t‖*Real.exp (-q*t)) (Set.Ioi 0))
    (hsource : ∀ N, 1 <= ‖response (f N) u‖)
    (hpaid : Tendsto (fun N => price (f N) q) atTop (𝓝 0)) :
    Tendsto (fun N => price (f N) a) atTop atTop := by
  apply tendsto_atTop.2
  intro M
  let T := 2*(|M|+1)/(u-a)
  have hT : (u-a)*T = 2*(|M|+1) := by
    dsimp [T]
    field_simp [show u-a ≠ 0 by linarith only [hau]]
  have he := Real.add_one_le_exp ((u-a)*T)
  have hbig : M <= (1/2 : ℝ)*Real.exp ((u-a)*T) := by
    rw [hT] at he ⊢
    linarith only [he, le_abs_self M]
  filter_upwards [eventually_price_lower f hau huq ha hu hq hsource hpaid T] with N hN
  exact hbig.trans hN

/-- The source-normalized factorial polynomial with arbitrary moving
coefficients/degrees, already present in the repository's exact filter. -/
def jointKernel (u : ℝ) (P : ℕ → Polynomial ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  (u : ℂ)^(N+1)*zetaFactorialPolynomial (P N) N t

/-- No fixed-degree or coefficient-growth assumption is needed for
the genuine integrability of each individual joined polynomial. -/
theorem integrable_price_jointKernel (u : ℝ) (P : ℕ → Polynomial ℂ)
    (N : ℕ) {d : ℝ} (hd : 0 < d) :
    IntegrableOn (fun t : ℝ => ‖jointKernel u P N t‖*Real.exp (-d*t)) (Set.Ioi 0) := by
  have h := ((integrableOn_zetaFactorialPolynomial_exp (P N) N hd).const_mul
    ((u : ℂ)^(N+1))).norm
  apply h.congr
  filter_upwards [] with t
  simp only [jointKernel, norm_mul, Complex.norm_exp, Complex.neg_re, Complex.mul_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, mul_assoc]

/-- Exact source evaluation, not a surrogate continuum-prime bridge. -/
theorem response_jointKernel (P : ℕ → Polynomial ℂ) {u : ℝ} (hu : 0 < u) (N : ℕ) :
    response (jointKernel u P N) u = (P N).eval (u : ℂ)⁻¹ := by
  have he (t : ℝ) : Real.exp (-u*t) • jointKernel u P N t =
      (u : ℂ)^(N+1)*(zetaFactorialPolynomial (P N) N t*
        Complex.exp (-(u : ℂ)*(t : ℂ))) := by
    simp only [jointKernel, Complex.real_smul, <-Complex.ofReal_exp,
      <-Complex.ofReal_mul, <-Complex.ofReal_neg]
    ring
  simp only [response, he, integral_const_mul, integral_zetaFactorialPolynomial_exp _ _ hu]
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  rw [<-mul_assoc, <-mul_pow, mul_inv_cancel₀ huC, one_pow, one_mul]

/-- Moving polynomial families cannot evade the general obstruction
by cancelling coefficients before taking the complete kernel's norm. -/
theorem joint_polynomial_price_tendsto_atTop (P : ℕ → Polynomial ℂ) {a u q : ℝ}
    (ha : 0 < a) (hau : a < u) (huq : u < q)
    (hsource : ∀ N, (P N).eval (u : ℂ)⁻¹ = 1)
    (hpaid : Tendsto (fun N => price (jointKernel u P N) q) atTop (𝓝 0)) :
    Tendsto (fun N => price (jointKernel u P N) a) atTop atTop := by
  apply price_tendsto_atTop (jointKernel u P) hau huq
    (fun N => integrable_price_jointKernel u P N ha)
    (fun N => integrable_price_jointKernel u P N (ha.trans hau))
    (fun N => integrable_price_jointKernel u P N ((ha.trans hau).trans huq)) _ hpaid
  intro N
  rw [response_jointKernel P (ha.trans hau), hsource N, norm_one]

/-- No cofinal bounded positive budget exists for this entire moving
polynomial class. The original signed-carrier ceiling is not disproved. -/
theorem not_eventually_bounded_joint_price (P : ℕ → Polynomial ℂ) {a u q : ℝ}
    (ha : 0 < a) (hau : a < u) (huq : u < q)
    (hsource : ∀ N, (P N).eval (u : ℂ)⁻¹ = 1)
    (hpaid : Tendsto (fun N => price (jointKernel u P N) q) atTop (𝓝 0)) (B : ℝ) :
    ¬ (∀ᶠ N : ℕ in atTop, price (jointKernel u P N) a <= B) := by
  intro hb
  have h := (joint_polynomial_price_tendsto_atTop P ha hau huq hsource hpaid).eventually
    (eventually_ge_atTop (B+1))
  have he := (h.and hb).exists
  obtain ⟨N, hl, huN⟩ := he
  linarith only [hl, huN]

/-- A quantitative tradeoff for ONE arbitrary joined kernel. -/
theorem price_lower_of_separated_small (f : ℝ → ℂ) {a u q T : ℝ}
    (hau : a < u) (huq : u < q)
    (ha : IntegrableOn (fun t : ℝ => ‖f t‖*Real.exp (-a*t)) (Set.Ioi 0))
    (hu : IntegrableOn (fun t : ℝ => ‖f t‖*Real.exp (-u*t)) (Set.Ioi 0))
    (hq : IntegrableOn (fun t : ℝ => ‖f t‖*Real.exp (-q*t)) (Set.Ioi 0))
    (hsource : 1 <= ‖response f u‖)
    (hpaid : price f q <= (1/2 : ℝ)*Real.exp (-(q-u)*T)) :
    (1/2 : ℝ)*Real.exp ((u-a)*T) <= price f a := by
  have hc := mul_le_mul_of_nonneg_left hpaid (Real.exp_pos ((q-u)*T)).le
  have hcanc : Real.exp ((q-u)*T)*Real.exp (-(q-u)*T) = 1 := by
    rw [<-Real.exp_add, show (q-u)*T+ -(q-u)*T = 0 by ring, Real.exp_zero]
  have hsmall : Real.exp ((q-u)*T)*price f q <= 1/2 := by
    nlinarith only [hc, hcanc]
  have hm := hsource.trans ((response_norm_le_price f u).trans
    (price_split f hau huq ha hu hq T))
  have hl : 1/2 <= Real.exp (-(u-a)*T)*price f a := by linarith only [hm, hsmall]
  have hcancel : Real.exp ((u-a)*T)*Real.exp (-(u-a)*T) = 1 := by
    rw [<-Real.exp_add, show (u-a)*T+ -(u-a)*T = 0 by ring, Real.exp_zero]
  calc
    _ = Real.exp ((u-a)*T)*(1/2) := by ring
    _ <= Real.exp ((u-a)*T)*(Real.exp (-(u-a)*T)*price f a) :=
      mul_le_mul_of_nonneg_left hl (Real.exp_pos _).le
    _ = _ := by rw [<-mul_assoc, hcancel, one_mul]

/-- At the ORIGINAL upper radius, a separated exp(-N/32) norm price
forces a positive arithmetic norm price at least exp(N/255936)/2.
This is not an actual signed prime-sum bound or native carrier debit. -/
theorem original_radius_geometric_price_lower (f : ℝ → ℂ) {N : ℕ} (hN : 64 <= N)
    (ha : IntegrableOn (fun t : ℝ => ‖f t‖*Real.exp (-(1/2)*t)) (Set.Ioi 0))
    (hu : IntegrableOn (fun t : ℝ => ‖f t‖*Real.exp (-(10001/20000)*t)) (Set.Ioi 0))
    (hq : IntegrableOn (fun t : ℝ => ‖f t‖*Real.exp (-(7/10)*t)) (Set.Ioi 0))
    (hsource : 1 <= ‖response f (10001/20000)‖)
    (hpaid : price f (7/10) <= Real.exp (-(N : ℝ)/32)) :
    (1/2 : ℝ)*Real.exp ((N : ℝ)/255936) <= price f (1/2) := by
  let T : ℝ := (N : ℝ)/(64*(7/10-10001/20000))
  have hTq : (7/10-10001/20000)*T = (N : ℝ)/64 := by norm_num [T]; ring
  have hTu : (10001/20000-1/2)*T = (N : ℝ)/255936 := by norm_num [T]; ring
  have hNre : (64 : ℝ) <= N := by exact_mod_cast hN
  have he : Real.exp (-(N : ℝ)/64) <= 1/2 := by
    have hfirst : Real.exp (-(N : ℝ)/64) <= Real.exp (-1) :=
      Real.exp_le_exp.mpr (by linarith only [hNre])
    have htwo : (2 : ℝ) <= Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hlast : Real.exp (-1) <= 1/2 := by
      simpa only [Real.exp_neg, inv_eq_one_div] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) htwo
    exact hfirst.trans hlast
  have hpaid' : price f (7/10) <= (1/2 : ℝ)*Real.exp (-(7/10-10001/20000)*T) := by
    have heq : Real.exp (-(N : ℝ)/32) =
        Real.exp (-(N : ℝ)/64)*Real.exp (-(N : ℝ)/64) := by
      rw [<-Real.exp_add]
      congr 1
      ring
    have hneg : -(7/10-10001/20000)*T = -((N : ℝ)/64) := by linarith only [hTq]
    rw [hneg, <-neg_div]
    exact hpaid.trans (heq.le.trans (mul_le_mul_of_nonneg_right he (Real.exp_pos _).le))
  have h := price_lower_of_separated_small f (by norm_num : (1/2 : ℝ) < 10001/20000)
    (by norm_num : (10001/20000 : ℝ) < 7/10) ha hu hq hsource hpaid'
  simpa only [hTu] using h

/-- The norm-payment method explicitly exceeds the requested ceiling
eventually; that conclusion is never transferred to the actual carrier. -/
theorem original_radius_price_exceeds_target (f : ℝ → ℂ) {N : ℕ} (hN : 400000 <= N)
    (ha : IntegrableOn (fun t : ℝ => ‖f t‖*Real.exp (-(1/2)*t)) (Set.Ioi 0))
    (hu : IntegrableOn (fun t : ℝ => ‖f t‖*Real.exp (-(10001/20000)*t)) (Set.Ioi 0))
    (hq : IntegrableOn (fun t : ℝ => ‖f t‖*Real.exp (-(7/10)*t)) (Set.Ioi 0))
    (hsource : 1 <= ‖response f (10001/20000)‖)
    (hpaid : price f (7/10) <= Real.exp (-(N : ℝ)/32)) :
    42/25 < price f (1/2) := by
  have hb := original_radius_geometric_price_lower f (by omega : 64 <= N) ha hu hq hsource hpaid
  have hNre : (400000 : ℝ) <= N := by exact_mod_cast hN
  have he : Real.exp (3/2) <= Real.exp ((N : ℝ)/255936) :=
    Real.exp_le_exp.mpr (by linarith only [hNre])
  have h1 : (5/2 : ℝ) <= Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hh : (3/2 : ℝ) <= Real.exp (1/2) := by linarith [Real.add_one_le_exp (1/2)]
  have hg : (15/4 : ℝ) <= Real.exp (3/2) := by
    have h := mul_le_mul h1 hh (by norm_num : (0 : ℝ) <= 3/2) (Real.exp_pos _).le
    rw [<-Real.exp_add, show (1 : ℝ)+1/2 = 3/2 by norm_num] at h
    norm_num at h
    exact h
  linarith only [hb, he, hg]

end RiemannGaussian.ZetaRieszCeilingJointKernelAudit
