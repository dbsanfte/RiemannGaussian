/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCeilingSignedCluster

/-!
# Join moment orders before pricing opposing actual zero modes

The Fejér polynomial is an exact sum of nonnegative geometric-prefix
squares on the closed unit disk. It therefore joins all competing phases
before the actual complete-arithmetic moment estimates are applied. No
nearby constructive-phase hypothesis or distance isolation is assumed.
The full all-height ceiling remains the target, not a replaced goal.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Complex Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCeilingFejerCluster
open ZetaRieszCeilingMomentIsolation ZetaRieszCeilingSignedCluster

/-- One exact finite geometric prefix, with its order-zero endpoint. -/
def geometricPrefix (v : ℂ) : ℕ → ℂ
  | 0 => 1
  | n+1 => 1+v*geometricPrefix v n

/-- The whole radial Fejér polynomial. Coefficients are kept signed
until the exact square identity is proved. -/
def fejerPolynomial (v : ℂ) (d : ℕ) : ℝ :=
  (d+1 : ℝ)+2*∑ j ∈ Finset.range d, ((d : ℝ)-j)*(v^(j+1)).re

/-- The exact positive square form, including its endpoint. -/
def fejerSquare (v : ℂ) (d : ℕ) : ℝ :=
  Complex.normSq (geometricPrefix v d)+(1-Complex.normSq v)*
    ∑ j ∈ Finset.range d, Complex.normSq (geometricPrefix v j)

/-- The prefix's multiplied form retains every shifted power. -/
theorem mul_geometricPrefix_eq (v : ℂ) (n : ℕ) :
    v*geometricPrefix v n = ∑ j ∈ Finset.range (n+1), v^(j+1) := by
  induction n with
  | zero => simp [geometricPrefix]
  | succ n hn =>
    rw [geometricPrefix, mul_add, mul_one, hn, Finset.mul_sum]
    simp_rw [<-pow_succ']
    rw [Finset.sum_range_succ' (fun j => v^(j+1)) (n+1)]
    simp only [Nat.zero_add]
    ring

/-- The difference of consecutive prefix squares is one signed power
sum. This is algebraic endpoint collection, before a norm allowance. -/
theorem geometricPrefix_square_difference (v : ℂ) (n : ℕ) :
    Complex.normSq (geometricPrefix v (n+1))-
      Complex.normSq v*Complex.normSq (geometricPrefix v n) =
      1+2*∑ j ∈ Finset.range (n+1), (v^(j+1)).re := by
  rw [geometricPrefix, Complex.normSq_add, Complex.normSq_mul]
  simp only [Complex.normSq_one, one_mul, Complex.conj_re]
  rw [mul_geometricPrefix_eq, Complex.re_sum]
  ring

/-- The positive square form's exact recurrence. -/
theorem fejerSquare_succ (v : ℂ) (n : ℕ) :
    fejerSquare v (n+1) = fejerSquare v n+
      (1+2*∑ j ∈ Finset.range (n+1), (v^(j+1)).re) := by
  unfold fejerSquare
  rw [Finset.sum_range_succ]
  linear_combination geometricPrefix_square_difference v n

/-- The signed polynomial has the same exact recurrence. -/
theorem fejerPolynomial_succ (v : ℂ) (n : ℕ) :
    fejerPolynomial v (n+1) = fejerPolynomial v n+
      (1+2*∑ j ∈ Finset.range (n+1), (v^(j+1)).re) := by
  have hs : (∑ j ∈ Finset.range n, (((n+1 : ℕ) : ℝ)-j)*(v^(j+1)).re) =
      (∑ j ∈ Finset.range n, ((n : ℝ)-j)*(v^(j+1)).re)+
        ∑ j ∈ Finset.range n, (v^(j+1)).re := by
    rw [<-Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  unfold fejerPolynomial
  rw [Finset.sum_range_succ, hs, Finset.sum_range_succ]
  push_cast
  ring

/-- Exact radial Fejér factorisation, valid for every complex v. -/
theorem fejerPolynomial_eq_square (v : ℂ) (d : ℕ) :
    fejerPolynomial v d = fejerSquare v d := by
  induction d with
  | zero => simp [fejerPolynomial, fejerSquare, geometricPrefix]
  | succ d hd => rw [fejerPolynomial_succ, fejerSquare_succ, hd]

/-- EVERY opposing phase is harmless in the joined Fejér kernel.
This inequality does not restrict v to a constructive-phase cone. -/
theorem fejerPolynomial_nonneg {v : ℂ} (hv : ‖v‖ <= 1) (d : ℕ) :
    0 <= fejerPolynomial v d := by
  rw [fejerPolynomial_eq_square]
  unfold fejerSquare
  have hs : Complex.normSq v <= 1 := by
    have h := pow_le_pow_left₀ (norm_nonneg v) hv 2
    simpa only [Complex.sq_norm, one_pow] using h
  exact add_nonneg (Complex.normSq_nonneg _)
    (mul_nonneg (by linarith only [hs])
      (Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)))

/-- The exact source-node value. -/
theorem fejerPolynomial_one (d : ℕ) : fejerPolynomial 1 d = (d+1 : ℝ)^2 := by
  induction d with
  | zero => simp [fejerPolynomial]
  | succ d hd =>
    rw [fejerPolynomial_succ, hd]
    simp only [one_pow, Complex.one_re, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one, mul_one]
    ring

/-- Exact signed collection of every mode and every test order. -/
theorem weighted_fejer_eq {α : Type*} (S : Finset α) (c : α → ℝ) (v : α → ℂ)
    (d K : ℕ) :
    (∑ i ∈ S, c i*fejerPolynomial (v i^K) d) =
      (d+1 : ℝ)*(∑ i ∈ S, c i)+
        2*∑ j ∈ Finset.range d, ((d : ℝ)-j)*
          (∑ i ∈ S, (c i : ℂ)*v i^(K*(j+1))).re := by
  simp only [fejerPolynomial, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, <-pow_mul]
  simp_rw [mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Fejér positivity collects all opposing phases before any actual
arithmetic bound is applied. -/
theorem weighted_fejer_nonneg {α : Type*} (S : Finset α) (c : α → ℝ)
    (v : α → ℂ) (hc : ∀ i ∈ S, 0 <= c i) (hv : ∀ i ∈ S, ‖v i‖ <= 1)
    (d K : ℕ) :
    0 <= (d+1 : ℝ)*(∑ i ∈ S, c i)+
      2*∑ j ∈ Finset.range d, ((d : ℝ)-j)*
        (∑ i ∈ S, (c i : ℂ)*v i^(K*(j+1))).re := by
  rw [<-weighted_fejer_eq]
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hc i hi) (fejerPolynomial_nonneg
    (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hv i hi)) d)

/-- The exact multiplicity mass of the selected-erased genuine local
divisor. This is a scalar constraint, not a replacement carrier. -/
def competingMass (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) : ℝ :=
  ∑ z ∈ (adaptiveZetaZeroSupport (zetaRightHalfDiscParameter rho hrho) rho.1.im).erase
    (-((3/2-rho.1.re : ℝ) : ℂ)),
    modeCoefficient (zetaRightHalfDiscParameter rho hrho) rho.1.im z

/-- Exposure supplies the closed unit disk for ACTUAL competing nodes.
No larger numerical gap or constructive ordinate cone is assumed. -/
theorem competing_node_norm_le (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖)
    {z : ℂ} (hz : z ∈
      (adaptiveZetaZeroSupport (zetaRightHalfDiscParameter rho hrho) rho.1.im).erase
        (-((3/2-rho.1.re : ℝ) : ℂ))) :
    ‖((3/2-rho.1.re : ℝ) : ℂ)*(-z⁻¹)‖ <= 1 := by
  have hu : 0 < 3/2-rho.1.re := by linarith [rho.re_lt_one]
  have hg := ZetaExposedMovingModes.canonical_support_gap hexposed
    (zetaRightHalfDiscParameter rho hrho) (Finset.mem_erase.mp hz).2
    (Finset.mem_erase.mp hz).1
  rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu.le,
    <-div_eq_mul_inv]
  exact (div_le_one (hu.trans hg)).mpr hg.le

/-- The actual signed zero family satisfies one joint eight-order
inequality. Nothing is norm-paid mode by mode here. -/
theorem competing_fejer_nonneg (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖) :
    0 <= 9*competingMass rho hrho+
      2*∑ j ∈ Finset.range 8, (8-(j : ℝ))*
        (competingMoment rho hrho (1100*(j+1)-1)).re := by
  have ht := weighted_fejer_nonneg
    ((adaptiveZetaZeroSupport (zetaRightHalfDiscParameter rho hrho) rho.1.im).erase
      (-((3/2-rho.1.re : ℝ) : ℂ)))
    (modeCoefficient (zetaRightHalfDiscParameter rho hrho) rho.1.im)
    (fun z => ((3/2-rho.1.re : ℝ) : ℂ)*(-z⁻¹))
    (fun z hz => coefficient_nonneg _ _ (Finset.mem_erase.mp hz).2)
    (fun _ hz => competing_node_norm_le rho hrho hexposed hz) 8 1100
  have he (j : ℕ) : 1100*(j+1)-1+1 = 1100*(j+1) := by omega
  norm_num only at ht
  simpa only [competingMoment, he, competingMass] using ht

/-- The source growth is certified by two exact rational blocks. -/
theorem source_stride_bound {u : ℝ} (hu : 0 <= u) (hU : u <= 10001/20000) :
    (2*u)^1100 <= 1117/1000 := by
  have hb : (10001/10000 : ℝ)^100 <= 10101/10000 := by norm_num
  have ht : (10101/10000 : ℝ)^11 <= 1117/1000 := by norm_num
  have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) <= (10001/10000 : ℝ)^100) hb 11
  rw [<-pow_mul] at h
  exact (pow_le_pow_left₀ (by positivity : 0 <= 2*u)
    (show 2*u <= (10001/10000 : ℝ) by linarith only [hU]) 1100).trans (h.trans ht)

/-- All paid pole, analytic and reflected errors are small uniformly
over the entire eight-order test, not on an isolated selected phase. -/
theorem paid_remainder_lt {u y : ℝ} (hu : 1/2 <= u) (hU : u <= 10001/20000)
    (hheight : localZetaLogHeight y <= 10^150) {k : ℕ}
    (hlo : 1100 <= k) (hhi : k <= 8800) :
    u^k+160*u*(localZetaLogHeight y+localZetaLogHeight 0)*(k : ℝ)*(10*u/7)^(k-1)+
      (localZetaLogHeight y+11)*(4*u/3)^k < 1/1000 := by
  have hpos : 0 <= u := by linarith only [hu]
  have hp := (pow_le_pow_left₀ hpos hU k).trans
    (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) <= 10001/20000)
      (by norm_num : (10001/20000 : ℝ) <= 1) (show 64 <= k by omega))
  have hps : (10001/20000 : ℝ)^64 < 1/3000 := by norm_num
  have hq100 : (10001/14000 : ℝ)^100 <= 1/400000000000000 := by norm_num
  have hq99 : (10001/14000 : ℝ)^99 <= 1/200000000000000 := by norm_num
  have hq : (10001/14000 : ℝ)^1099 <=
      (1/400000000000000 : ℝ)^10*(1/200000000000000) := by
    rw [show (1099 : ℕ) = 100*10+99 by norm_num, pow_add, pow_mul]
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) hq100 10) hq99
      (by positivity) (by positivity)
  have hqU : (10*u/7)^(k-1) <= (10001/14000 : ℝ)^1099 :=
    (pow_le_pow_left₀ (by positivity : 0 <= 10*u/7)
      (show 10*u/7 <= (10001/14000 : ℝ) by linarith only [hU]) _).trans
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
  have hr100 : (10001/15000 : ℝ)^100 <= 1/400000000000000000 := by norm_num
  have hr : (10001/15000 : ℝ)^1100 <= (1/400000000000000000 : ℝ)^11 := by
    rw [show (1100 : ℕ) = 100*11 by norm_num, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hr100 11
  have hrU : (4*u/3)^k <= (10001/15000 : ℝ)^1100 :=
    (pow_le_pow_left₀ (by positivity : 0 <= 4*u/3)
      (show 4*u/3 <= (10001/15000 : ℝ) by linarith only [hU]) k).trans
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hlo)
  have hh := add_le_add hheight zero_height_log_le
  have hhh : localZetaLogHeight y+11 <= (10^150+11 : ℝ) := by linarith only [hheight]
  have hHpos : 0 <= localZetaLogHeight y+localZetaLogHeight 0 := by
    linarith [two_lt_localZetaLogHeight y, two_lt_localZetaLogHeight 0]
  have hc := mul_le_mul (mul_le_mul_of_nonneg_left hU (by norm_num : (0 : ℝ) <= 160))
    hh hHpos (by norm_num : (0 : ℝ) <= 160*(10001/20000))
  have hc' := mul_le_mul hc (show (k : ℝ) <= 8800 by exact_mod_cast hhi)
    (by positivity) (by norm_num : (0 : ℝ) <= 160*(10001/20000)*(10^150+4))
  have hqa := mul_le_mul hc' (hqU.trans hq) (by positivity)
    (by norm_num : (0 : ℝ) <= 160*(10001/20000)*(10^150+4)*8800)
  have hra := mul_le_mul hhh (hrU.trans hr) (by positivity)
    (by norm_num : (0 : ℝ) <= 10^150+11)
  have hqs : (160 : ℝ)*(10001/20000)*(10^150+4)*8800*
      (1/400000000000000 : ℝ)^10*(1/200000000000000) < 1/3000 := by norm_num
  have hrs : (10^150+11 : ℝ)*(1/400000000000000000)^11 < 1/3000 := by norm_num
  have hqab : 160*u*(localZetaLogHeight y+localZetaLogHeight 0)*(k : ℝ)*
      (10*u/7)^(k-1) < 1/3000 := by
    exact hqa.trans_lt (by simpa only [mul_assoc] using hqs)
  have hrab := hra.trans_lt hrs
  have hpab := hp.trans_lt hps
  linarith only [hpab, hqab, hrab]

/-- Exact rational sum of all eight growing arithmetic terms. -/
theorem rational_fejer_cost :
    2*(∑ j ∈ Finset.range 8, (8-(j : ℝ))*(1117/1000 : ℝ)^(j+1)) < 1069/10 := by
  norm_num [Finset.sum_range_succ]

/-- The whole signed test costs less than107, including every paid error. -/
theorem actual_fejer_cost_lt {u y : ℝ} (hu : 1/2 <= u) (hU : u <= 10001/20000)
    (hheight : localZetaLogHeight y <= 10^150) :
    2*(∑ j ∈ Finset.range 8, (8-(j : ℝ))*
      ((2*u)^(1100*(j+1))+u^(1100*(j+1))+
        160*u*(localZetaLogHeight y+localZetaLogHeight 0)*
          ((1100*(j+1) : ℕ) : ℝ)*(10*u/7)^(1100*(j+1)-1)+
        (localZetaLogHeight y+11)*(4*u/3)^(1100*(j+1)))) < 107 := by
  have hmain := source_stride_bound (show 0 <= u by linarith) hU
  have hterm (j : ℕ) (hj : j ∈ Finset.range 8) :
      (8-(j : ℝ))*
        ((2*u)^(1100*(j+1))+u^(1100*(j+1))+
          160*u*(localZetaLogHeight y+localZetaLogHeight 0)*
            ((1100*(j+1) : ℕ) : ℝ)*(10*u/7)^(1100*(j+1)-1)+
          (localZetaLogHeight y+11)*(4*u/3)^(1100*(j+1))) <=
        (8-(j : ℝ))*((1117/1000 : ℝ)^(j+1)+1/1000) := by
    have hj8 := Finset.mem_range.mp hj
    have hjR : (j : ℝ) <= 8 := by exact_mod_cast hj8.le
    have hs : (2*u)^(1100*(j+1)) <= (1117/1000 : ℝ)^(j+1) := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (by positivity) hmain _
    have he := paid_remainder_lt hu hU hheight
      (show 1100 <= 1100*(j+1) by omega) (show 1100*(j+1) <= 8800 by omega)
    apply mul_le_mul_of_nonneg_left _ (by linarith only [hjR])
    simpa only [add_assoc] using add_le_add hs he.le
  have hs := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by norm_num : (0 : ℝ) <= 2)
  have he : 2*(∑ j ∈ Finset.range 8, (8-(j : ℝ))*
      ((1117/1000 : ℝ)^(j+1)+1/1000)) =
      2*(∑ j ∈ Finset.range 8, (8-(j : ℝ))*(1117/1000 : ℝ)^(j+1))+72/1000 := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    norm_num [Finset.sum_range_succ]
  rw [he] at hs
  linarith only [hs, rational_fejer_cost]

/-- Join the eight COMPLETE arithmetic moments and the signed zero
kernel. This explicit inequality is the new ceiling payment. -/
theorem multiplicity_fejer_lt (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖) :
    72*(analyticZetaZeroMultiplicity rho : ℝ) <
      9*competingMass rho (show 1/2 < rho.1.re by linarith)+107 := by
  have hrho : 1/2 < rho.1.re := by linarith
  let u := 3/2-rho.1.re
  let m : ℝ := analyticZetaZeroMultiplicity rho
  have hu : 1/2 <= u := by dsimp [u]; linarith [rho.re_lt_one]
  have hU : u <= 10001/20000 := by dsimp [u]; linarith only [hnear]
  have htest (j : ℕ) (hj : j ∈ Finset.range 8) :
      (8-(j : ℝ))*(m+(competingMoment rho hrho (1100*(j+1)-1)).re) <=
      (8-(j : ℝ))*
        ((2*u)^(1100*(j+1))+u^(1100*(j+1))+
          160*u*(localZetaLogHeight rho.1.im+localZetaLogHeight 0)*
            ((1100*(j+1) : ℕ) : ℝ)*(10*u/7)^(1100*(j+1)-1)+
          (localZetaLogHeight rho.1.im+11)*(4*u/3)^(1100*(j+1))) := by
    have hjR : (j : ℝ) <= 8 := by exact_mod_cast (Finset.mem_range.mp hj).le
    apply mul_le_mul_of_nonneg_left _ (by linarith only [hjR])
    have he : 1100*(j+1)-1+1 = 1100*(j+1) := by omega
    have heR : (((1100*(j+1)-1 : ℕ) : ℝ)+1) = ((1100*(j+1) : ℕ) : ℝ) := by
      exact_mod_cast he
    simpa only [he, heR, m, u] using
      multiplicity_add_competing_re_le rho hrho (1100*(j+1)-1)
  have ht := mul_le_mul_of_nonneg_left (Finset.sum_le_sum htest) (by norm_num : (0 : ℝ) <= 2)
  have hc := actual_fejer_cost_lt hu hU hheight
  have he : 2*(∑ j ∈ Finset.range 8,
      (8-(j : ℝ))*(m+(competingMoment rho hrho (1100*(j+1)-1)).re)) =
      72*m+2*(∑ j ∈ Finset.range 8,
        (8-(j : ℝ))*(competingMoment rho hrho (1100*(j+1)-1)).re) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [<-Finset.sum_mul]
    have hw : (∑ j ∈ Finset.range 8, (8-(j : ℝ))) = 36 := by norm_num [Finset.sum_range_succ]
    rw [hw]
    ring
  rw [he] at ht
  have hp := competing_fejer_nonneg rho hrho hexposed
  change 72*m < 9*competingMass rho hrho+107
  linarith only [ht, hc, hp]

/-- The mass counts multiplicities, not distinct zero positions. -/
def competingNaturalMass (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) : ℕ :=
  ∑ z ∈ (adaptiveZetaZeroSupport (zetaRightHalfDiscParameter rho hrho) rho.1.im).erase
    (-((3/2-rho.1.re : ℝ) : ℂ)),
    (MeromorphicOn.divisor (localZetaPoleRemoved rho.1.im)
      (Metric.ball 0 (adaptiveZetaCanonicalRadius (zetaRightHalfDiscParameter rho hrho)
        rho.1.im)) z).toNat

/-- The real scalar is exactly the natural total multiplicity. -/
theorem competingMass_eq_nat (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) :
    competingMass rho hrho = (competingNaturalMass rho hrho : ℝ) := by
  unfold competingMass competingNaturalMass
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hc := coefficient_nonneg (zetaRightHalfDiscParameter rho hrho) rho.1.im
    (Finset.mem_erase.mp hz).2
  change (0 : ℝ) <= ((MeromorphicOn.divisor (localZetaPoleRemoved rho.1.im)
      (Metric.ball 0 (adaptiveZetaCanonicalRadius (zetaRightHalfDiscParameter rho hrho)
        rho.1.im)) z : ℤ) : ℝ) at hc
  have hi : (0 : ℤ) <= MeromorphicOn.divisor (localZetaPoleRemoved rho.1.im)
      (Metric.ball 0 (adaptiveZetaCanonicalRadius (zetaRightHalfDiscParameter rho hrho)
        rho.1.im)) z := by exact_mod_cast hc
  have ht := congrArg (fun a : ℤ => (a : ℝ)) (Int.toNat_of_nonneg hi)
  simpa only [Int.cast_natCast, modeCoefficient] using ht.symm

/-- A multiple exposed source requires at least FIVE competing units
of actual multiplicity. Opposing phases alone cannot evade this test. -/
theorem multiple_forces_mass_five (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖)
    (hm : 2 <= analyticZetaZeroMultiplicity rho) :
    5 <= competingNaturalMass rho (show 1/2 < rho.1.re by linarith) := by
  have ht := multiplicity_fejer_lt rho hnear hheight hexposed
  rw [competingMass_eq_nat] at ht
  have hmR : (2 : ℝ) <= analyticZetaZeroMultiplicity rho := by exact_mod_cast hm
  have hW : (4 : ℝ) < competingNaturalMass rho (show 1/2 < rho.1.re by linarith) := by
    linarith only [ht, hmR]
  have hn : 4 < competingNaturalMass rho (show 1/2 < rho.1.re by linarith) := by exact_mod_cast hW
  omega

/-- Actual simplicity in every competing-mass<=4 geometry, with no
ordinate-phase or distance-isolation condition. -/
theorem simple_of_competing_mass_le_four (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖)
    (hmass : competingNaturalMass rho (show 1/2 < rho.1.re by linarith) <= 4) :
    analyticZetaZeroMultiplicity rho = 1 := by
  have hp := analyticZetaZeroMultiplicity_positive rho
  by_contra h
  have hm : 2 <= analyticZetaZeroMultiplicity rho := by omega
  have ht := multiple_forces_mass_five rho hnear hheight hexposed hm
  omega

/-- The SAME original native42/25 ceiling is now paid for all sparse
exposed actual clusters, even with opposing individual moment phases. -/
theorem eventually_joinedPhysical_ceiling_of_competing_mass_le_four
    (rho : NontrivialZetaZero) (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖)
    (hmass : competingNaturalMass rho (show 1/2 < rho.1.re by linarith) <= 4) :
    ∀ᶠ j : ℕ in atTop,
      (((3/2-rho.1.re : ℝ) : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical (3/2-rho.1.re) rho.1.im
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).re < 42/25 := by
  have hrho : 1/2 < rho.1.re := by linarith
  have hu : 1/2 <= 3/2-rho.1.re := by linarith [rho.re_lt_one]
  have hU : 3/2-rho.1.re <= ZetaRieszWideOwnerAudit.radiusCeiling := by
    unfold ZetaRieszWideOwnerAudit.radiusCeiling
    linarith
  have hm := simple_of_competing_mass_le_four rho hnear hheight hexposed hmass
  have hs := Complex.continuous_re.tendsto _ |>.comp
    (ZetaRieszJoinedPhysical.tendsto_joinedPhysical_exact_source rho hrho hexposed hU)
  simp only [hm, Nat.cast_one, one_pow, one_mul, Complex.add_re, Complex.neg_re,
    Complex.one_re, Complex.ofReal_re] at hs
  have hc := ZetaRieszEndgameSlack.retainedCost_upper hu hU
  exact hs.eventually (gt_mem_nhds (show -1+ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re) <
    42/25 by linarith only [hc]))

end RiemannGaussian.ZetaRieszCeilingFejerCluster
