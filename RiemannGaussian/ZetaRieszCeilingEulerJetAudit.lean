/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCeilingClusterPowerAudit
import RiemannGaussian.ZetaRieszCeilingMomentIsolation

/-!
# Finite complete-Euler jets do not determine the unpaid source

This is a method audit, not a replacement for the actual prime carrier.
The frozen exposed double-source model can match ANY finite head of the
complete ordinary-prime array exactly. A finite polynomial changes only
its analytic remainder; its modes, eventual source and violation of the
SAME joined evaluator remain unchanged. Every logged order is retained.

The head really is the complete prime series, not a thinned measure.
The patched infinite tail is NOT identified with that series or with
actual zeros. Thus this gives no counterexample to the arithmetic ceiling.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
noncomputable section
open Complex Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCeilingEulerJetAudit
open ZetaRieszCeilingClusterPowerAudit ZetaRieszCeilingMomentIsolation
open ZetaRieszPairPrimePowerPayment ZetaRieszSelbergSourceAudit
open ZetaRieszSignedSelbergPayment ZetaRieszPairPrefixConvolution

/-- Preserve the entire frozen model after an arbitrary finite head. -/
def patchArray (J : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n < J then a n else modelArray modeCount sourceRadius root n

/-- This correction is finite, including orders zero and one. -/
def headCorrection (J : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n < J then a n-modelArray modeCount sourceRadius root n else 0

/-- The exact polynomial added to the local regular generating function. -/
def headPolynomial (J : ℕ) (a : ℕ → ℂ) (t : ℂ) : ℂ :=
  ∑ n ∈ Finset.range J, (a n-modelArray modeCount sourceRadius root n)*t^n

/-- The full finite-head price on the SAME radius 4/3; no asymptotic
smallness of this constant is assumed. -/
def headPrice (J : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ Finset.range J, ‖a n-modelArray modeCount sourceRadius root n‖*(4/3 : ℝ)^(n+1)

theorem patchArray_eq_head {J n : ℕ} (a : ℕ → ℂ) (hn : n < J) :
    patchArray J a n = a n := by simp [patchArray, hn]

theorem patchArray_eq_tail {J n : ℕ} (a : ℕ → ℂ) (hn : J <= n) :
    patchArray J a n = modelArray modeCount sourceRadius root n := by
  simp [patchArray, not_lt.mpr hn]

/-- The head is changed once, with its exact signed difference retained. -/
theorem patchArray_eq (J : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    patchArray J a n = modelArray modeCount sourceRadius root n+headCorrection J a n := by
  by_cases hn : n < J <;> simp [patchArray, headCorrection, hn]

/-- A finite complete-Euler jet cannot change the exposed model source. -/
theorem patchArray_tendsto (J : ℕ) (a : ℕ → ℂ) :
    Tendsto (patchArray J a) atTop (𝓝 (-2)) := by
  apply (modelArray_tendsto (by norm_num [modeCount] : 0 < modeCount)
    (by norm_num [sourceRadius] : 0 < sourceRadius)
    (by norm_num [sourceRadius] : sourceRadius < 1) root_primitive).congr'
  filter_upwards [eventually_ge_atTop J] with n hn
  exact (patchArray_eq_tail a hn).symm

/-- The exact genuine-geometry local model is unchanged: only its
analytic remainder acquires a finite polynomial. -/
theorem patched_local_ledger (J : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    patchArray J a n =
      -2*∑ i ∈ localIndices modeCount sourceRadius root,
        (node sourceRadius root i)^(n+1)+
      (localRegular modeCount sourceRadius root n+headCorrection J a n) := by
  rw [patchArray_eq, model_eq_local]
  ring

/-- The polynomial correction is entire, regardless of the head values. -/
theorem headPolynomial_analytic (J : ℕ) (a : ℕ → ℂ) (t : ℂ) :
    AnalyticAt ℂ (headPolynomial J a) t := by
  apply Finset.analyticAt_fun_sum
  intro n _
  exact analyticAt_const.mul (analyticAt_id.pow n)

/-- The same normalized local analytic disk survives every finite jet.
This is MODEL analyticity, not an actual-zeta decomposition. -/
theorem patched_generating_analytic (J : ℕ) (a : ℕ → ℂ) {t : ℂ}
    (ht : ‖t‖ <= 4/3) :
    AnalyticAt ℂ (fun v => localGenerating modeCount sourceRadius root v+
      headPolynomial J a v) t := by
  exact (localGenerating_analytic (by norm_num [sourceRadius])
    (by norm_num [sourceRadius]) root ht).add (headPolynomial_analytic J a t)

theorem headPrice_nonneg (J : ℕ) (a : ℕ → ℂ) : 0 <= headPrice J a := by
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (by positivity))

/-- An explicit geometric coefficient bound retains the whole head
price; it is never silently discarded as a small error. -/
theorem headCorrection_bound (J : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    ‖headCorrection J a n‖ <= headPrice J a*(3/4 : ℝ)^(n+1) := by
  by_cases hn : n < J
  · have hs := Finset.single_le_sum
      (f := fun k => ‖a k-modelArray modeCount sourceRadius root k‖*(4/3 : ℝ)^(k+1))
      (fun _ _ => mul_nonneg (norm_nonneg _) (by positivity)) (Finset.mem_range.mpr hn)
    change ‖a n-modelArray modeCount sourceRadius root n‖*(4/3 : ℝ)^(n+1) <= headPrice J a at hs
    have hh := mul_le_mul_of_nonneg_right hs (by positivity : (0 : ℝ) <= (3/4)^(n+1))
    have hc : (4/3 : ℝ)^(n+1)*(3/4 : ℝ)^(n+1) = 1 := by
      rw [<-mul_pow]
      norm_num
    simpa only [headCorrection, if_pos hn, mul_assoc, hc, mul_one] using hh
  · simp only [headCorrection, if_neg hn, norm_zero]
    exact mul_nonneg (headPrice_nonneg J a) (by positivity)

/-- Matching a finite Euler jet preserves an explicit geometric local
remainder, with its actual enlarged constant displayed. -/
theorem patched_regular_bound (J : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    ‖localRegular modeCount sourceRadius root n+headCorrection J a n‖ <=
      (4*modeCount+headPrice J a)*(3/4 : ℝ)^(n+1) := by
  apply (norm_add_le _ _).trans
  have hb := localRegular_bound (M := modeCount)
    (by norm_num [sourceRadius] : 0 <= sourceRadius)
    (by norm_num [sourceRadius] : sourceRadius <= 3/5) root n
  exact (add_le_add hb (headCorrection_bound J a n)).trans_eq (by ring)

/-- The finite correction is exactly the displayed polynomial, not
merely some analytic function with the same finite jet. -/
theorem hasSum_headCorrection (J : ℕ) (a : ℕ → ℂ) (t : ℂ) :
    HasSum (fun n => headCorrection J a n*t^n) (headPolynomial J a t) := by
  have hh : HasSum (fun n => headCorrection J a n*t^n)
      (∑ n ∈ Finset.range J, headCorrection J a n*t^n) := hasSum_sum_of_ne_finset_zero
    (s := Finset.range J) (f := fun n => headCorrection J a n*t^n) (by
      intro n hn
      simp only [Finset.mem_range] at hn
      simp [headCorrection, hn])
  have he : (∑ n ∈ Finset.range J, headCorrection J a n*t^n) = headPolynomial J a t := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [headCorrection, if_pos (Finset.mem_range.mp hn)]
  rwa [he] at hh

/-- Exact inverse-series bookkeeping preserves every regular endpoint. -/
theorem hasSum_patched_regular (J : ℕ) (a : ℕ → ℂ) {t : ℂ}
    (ht : ‖t‖ <= 4/3) :
    HasSum (fun n => (localRegular modeCount sourceRadius root n+headCorrection J a n)*t^n)
      (localGenerating modeCount sourceRadius root t+headPolynomial J a t) := by
  simpa only [add_mul] using
    (hasSum_localRegular (by norm_num [sourceRadius])
      (by norm_num [sourceRadius]) root ht).add (hasSum_headCorrection J a t)

/-- No finite array test can detect the tail by forgetting its analytic
remainder. Here the source difference is explicit, never paid to zero. -/
theorem patch_sub_original_tendsto (J : ℕ) (a : ℕ → ℂ) {v : ℂ}
    (ha : Tendsto a atTop (𝓝 v)) :
    Tendsto (fun n => patchArray J a n-a n) atTop (𝓝 (-2-v)) :=
  (patchArray_tendsto J a).sub ha

/-- Agreement on all finite logged indices implies agreement of the
WHOLE finite evaluator, including its two trace endpoints and diagonal. -/
theorem evaluator_eq_of_head_eq (a b : ℕ → ℂ) (u : ℝ) (N : ℕ)
    (hab : ∀ n, n <= N+1 → a n = b n) :
    -traceError a (N-1)-harmonicEvaluation a u N =
      -traceError b (N-1)-harmonicEvaluation b u N := by
  have ht : traceError a (N-1) = traceError b (N-1) := by
    unfold traceError
    rw [hab ((N-1)+1) (by omega)]
    congr 2
    apply Finset.sum_congr rfl
    intro k hk
    have hkN := Finset.mem_range.mp hk
    rw [hab k (by omega), hab (N-1-k) (by omega)]
  have hh : harmonicEvaluation a u N = harmonicEvaluation b u N := by
    have h0 : (∑ k ∈ Finset.range N, a k*a (N-1-k)) =
        ∑ k ∈ Finset.range N, b k*b (N-1-k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkN := Finset.mem_range.mp hk
      rw [hab k (by omega), hab (N-1-k) (by omega)]
    have h1 : (∑ k ∈ centralOrders (N+1) (13*N/32), a (k-1)*a (N-k)/((N+1-k : ℕ) : ℂ)) =
        ∑ k ∈ centralOrders (N+1) (13*N/32), b (k-1)*b (N-k)/((N+1-k : ℕ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkN := Finset.mem_filter.mp hk
      have hkM := Finset.mem_range.mp hkN.1
      rw [hab (k-1) (by omega), hab (N-k) (by omega)]
    have h2 : (∑ k ∈ Finset.Icc 1 (N+1-13*N/32), a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ)) =
        ∑ k ∈ Finset.Icc 1 (N+1-13*N/32), b (k-1)*b (N+1-k)/((N+2-k : ℕ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkN := Finset.mem_Icc.mp hk
      rw [hab (k-1) (by omega), hab (N+1-k) (by omega)]
    unfold harmonicEvaluation
    rw [h0, h1, h2]
  rw [ht, hh]

/-- Apply the UNCHANGED signed evaluator, retaining both prefixes,
the moving length, adjacent orders and the diagonal. -/
theorem patched_joined_gt_ceiling (J : ℕ) (a : ℕ → ℂ) :
    ∀ᶠ N : ℕ in atTop, (42/25 : ℝ) <
      (-traceError (patchArray J a) (N-1)-
        harmonicEvaluation (patchArray J a) sourceRadius N).re := by
  have ht := ZetaRieszCeilingDensityAudit.joined_double_tendsto _ (patchArray_tendsto J a)
    (u := sourceRadius) (by norm_num [sourceRadius]) (by norm_num [sourceRadius])
  have hr := Complex.continuous_re.continuousAt.tendsto.comp ht
  simp only [Complex.ofReal_re] at hr
  have hc := ZetaRieszEndgameSlack.retainedCost_lower
    (u := sourceRadius) (by norm_num [sourceRadius])
    (by norm_num [sourceRadius, ZetaRieszWideOwnerAudit.radiusCeiling])
  exact hr.eventually_const_lt (by linarith only [hc])

/-- The exact complete ordinary-prime head, not a finite-prime sample. -/
def eulerPatch (J : ℕ) (y : ℝ) : ℕ → ℂ := patchArray J (ordinaryArray sourceRadius y)

theorem eulerPatch_matches_complete {J n : ℕ} (y : ℝ) (hn : n < J) :
    eulerPatch J y n = ordinaryArray sourceRadius y n := patchArray_eq_head _ hn

/-- The joined finite regression itself can match COMPLETE actual
arithmetic at every desired finite order. This is not a native-mask
identification for the patched infinite tail. -/
theorem eulerPatch_matches_joined {J N : ℕ} (y : ℝ) (hN : N+1 < J) :
    -traceError (eulerPatch J y) (N-1)-harmonicEvaluation (eulerPatch J y) sourceRadius N =
      -traceError (ordinaryArray sourceRadius y) (N-1)-
        harmonicEvaluation (ordinaryArray sourceRadius y) sourceRadius N :=
  evaluator_eq_of_head_eq _ _ _ _ (fun n hn => eulerPatch_matches_complete y (by omega))

/-- The norm of ordinary-prime moments is bounded by the COMPLETE
real-axis von Mangoldt mass. There is no comparison to the modulus of
the phased von Mangoldt sum, which would be false. -/
theorem ordinary_moment_le_real_axis (y : ℝ) (n : ℕ) :
    ‖zetaOrdinaryPrimeLogMoment n (3/2+I*y)‖ <= (zetaPrimeLogMoment n (3/2 : ℂ)).re := by
  let f : ℕ → ℝ := fun m => ArithmeticFunction.vonMangoldt m*
    (Real.log m)^n/(n.factorial : ℝ)*zetaPrimeExpWeight (3/2) m
  have hr := hasSum_zetaPrimeLogMoment (s := (3/2 : ℂ)) (by norm_num) n
  have hreal (m : ℕ) :
      ((ArithmeticFunction.vonMangoldt m : ℂ)*
        ((Real.log m : ℂ)^n/(n.factorial : ℂ))*zetaPrimeFeature (3/2) m) = (f m : ℂ) := by
    simp only [f, zetaPrimeFeature, zetaPrimeExpWeight, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_natCast,
      Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_ofNat]
    push_cast
    ring
  have hsum := Complex.reCLM.hasSum (hr.congr_fun (fun m => (hreal m).symm))
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at hsum
  have hsumf : HasSum f (zetaPrimeLogMoment n (3/2 : ℂ)).re := hsum
  have hs := summable_zetaOrdinaryPrimeLogMoment n
    (s := 3/2+I*y) (by norm_num)
  have hnorm (m : ℕ) :
      ‖(ArithmeticFunction.vonMangoldt m : ℂ)*zetaPrimeLogKernel n (3/2+I*y) m‖ = f m := by
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, norm_zetaPrimeLogKernel]
    norm_num [f]
    ring
  unfold zetaOrdinaryPrimeLogMoment
  apply (norm_tsum_le_tsum_norm hs.norm).trans
  rw [<-hsumf.tsum_eq]
  apply Summable.tsum_le_tsum _ hs.norm hsumf.summable
  intro m
  by_cases hp : m.Prime
  · simp only [if_pos hp, hnorm]
    exact le_rfl
  · simp only [if_neg hp, norm_zero]
    exact mul_nonneg (div_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (pow_nonneg (Real.log_natCast_nonneg _) _)) (Nat.cast_nonneg _)) (Real.exp_pos _).le

/-- The independently proved, height-uniform Euler moment envelope.
This is a norm allowance only, not an arithmetic ceiling credit. -/
def eulerEnvelope (n : ℕ) : ℝ :=
  (2*sourceRadius)^(n+1)+640*sourceRadius*(n+1)*(10*sourceRadius/7)^n

/-- Complete ordinary-prime coverage, EVERY logged order and EVERY
height satisfy the same explicit envelope used in the audit. -/
theorem complete_ordinary_envelope (y : ℝ) (n : ℕ) :
    ‖ordinaryArray sourceRadius y n‖ <= eulerEnvelope n := by
  let r : Set.Ico (3/4 : ℝ) 1 := ⟨4/5, by norm_num⟩
  have he := scaled_moment_bound r 0
    (by norm_num [sourceRadius] : 0 <= sourceRadius) n
  have hl := zero_height_log_le
  have hp := ordinary_moment_le_real_axis y n
  have hscaled : ‖ordinaryArray sourceRadius y n‖ <=
      ‖(sourceRadius : ℂ)^(n+1)*zetaPrimeLogMoment n (3/2 : ℂ)‖ := by
    unfold ordinaryArray
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hp.trans (Complex.re_le_norm _)) (norm_nonneg _)
  apply (hscaled.trans (by simpa only [Complex.ofReal_zero, mul_zero, add_zero] using he)).trans
  unfold eulerEnvelope
  have hc : 160*sourceRadius*localZetaLogHeight 0 <= 640*sourceRadius := by
    have h := mul_le_mul_of_nonneg_left hl (by norm_num [sourceRadius] : 0 <= 160*sourceRadius)
    nlinarith only [h]
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) <= n+1))
    (pow_nonneg (by norm_num [sourceRadius] : (0 : ℝ) <= 10*sourceRadius/7) n)
  simpa only [add_comm] using add_le_add_left hm ((2*sourceRadius)^(n+1))

/-- A finite exact complete-Euler head DOES NOT repair the all-order
envelope counterexample: the unchanged tail already passes the same
bound. No hidden extra error is inserted at the splice. -/
theorem eulerPatch_all_order_envelope (J : ℕ) (y : ℝ) (n : ℕ) :
    ‖eulerPatch J y n‖ <= eulerEnvelope n := by
  by_cases hn : n < J
  · rw [eulerPatch_matches_complete y hn]
    exact complete_ordinary_envelope y n
  · rw [eulerPatch, patchArray_eq_tail _ (by omega)]
    exact (model_complete_moment_bound n).trans
      (by unfold eulerEnvelope; exact le_add_of_nonneg_right (by norm_num [sourceRadius]; positivity))

/-- A deliberately crude rational head bound, uniform at ALL heights.
It is used only to display the analytic patch constant. -/
theorem eulerEnvelope_head_le {n : ℕ} (hn : n < 512) : eulerEnvelope n <= 200000 := by
  have hp : (2*sourceRadius)^(n+1) <= 2 := by
    have h := pow_le_pow_right₀
      (by norm_num [sourceRadius] : 1 <= 2*sourceRadius) (show n+1 <= 512 by omega)
    have hb : (2*sourceRadius)^512 <= (2 : ℝ) := by
      set_option exponentiation.threshold 512 in norm_num [sourceRadius]
    exact h.trans hb
  have hq : (10*sourceRadius/7)^n <= 1 :=
    pow_le_one₀ (by norm_num [sourceRadius]) (by norm_num [sourceRadius])
  have hnR : (n : ℝ)+1 <= 512 := by exact_mod_cast (show n+1 <= 512 by omega)
  have ht : 640*sourceRadius*(n+1)*(10*sourceRadius/7)^n <= 640*sourceRadius*512 := by
    calc
      _ <= 640*sourceRadius*(n+1)*1 :=
        mul_le_mul_of_nonneg_left hq (by norm_num [sourceRadius]; positivity)
      _ <= _ := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left hnR (by norm_num [sourceRadius])
  unfold eulerEnvelope
  norm_num only [sourceRadius] at ht hp ⊢
  linarith only [hp, ht]

/-- Even 512 EXACT complete ordinary-prime moments fit an explicit
geometric analytic remainder. This does not price the actual carrier. -/
theorem complete_headPrice_le (y : ℝ) :
    headPrice 512 (ordinaryArray sourceRadius y) <= (10 : ℝ)^77 := by
  have hp : (4/3 : ℝ)^512 <= (10 : ℝ)^68 := by
    have hb : (4/3 : ℝ)^128 <= (10 : ℝ)^17 := by norm_num
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) <= (4/3)^128) hb 4
    simpa only [<-pow_mul, Nat.reduceMul] using hh
  have hs : headPrice 512 (ordinaryArray sourceRadius y) <=
      (512 : ℝ)*(200000*(4/3 : ℝ)^512) := by
    unfold headPrice
    calc
      _ <= ∑ _n ∈ Finset.range 512, 200000*(4/3 : ℝ)^512 := by
        apply Finset.sum_le_sum
        intro n hn
        have hnJ := Finset.mem_range.mp hn
        rw [modelArray_eq_zero root_primitive (by norm_num [modeCount]; omega), sub_zero]
        exact mul_le_mul ((complete_ordinary_envelope y n).trans (eulerEnvelope_head_le hnJ))
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) <= 4/3) (show n+1 <= 512 by omega))
          (by positivity) (by norm_num)
      _ = _ := by simp
  have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) <= 512*200000)
  have hc : (512 : ℝ)*200000*(10 : ℝ)^68 <= (10 : ℝ)^77 := by norm_num
  exact hs.trans (by simpa only [mul_assoc] using hm.trans hc)

/-- The complete-prime jet regression has a uniform displayed regular
coefficient constant and the SAME radius, all orders retained. -/
theorem complete_patch_regular_le (y : ℝ) (n : ℕ) :
    ‖localRegular modeCount sourceRadius root n+
      headCorrection 512 (ordinaryArray sourceRadius y) n‖ <=
      (10 : ℝ)^78*(3/4 : ℝ)^(n+1) := by
  have hh := complete_headPrice_le y
  have hc : (4*modeCount : ℝ)+headPrice 512 (ordinaryArray sourceRadius y) <= (10 : ℝ)^78 := by
    norm_num only [modeCount, Nat.cast_ofNat] at *
    linarith only [hh]
  exact (patched_regular_bound 512 _ n).trans
    (mul_le_mul_of_nonneg_right hc (by positivity))

/-- All orders, including zero and one, are kept in this source limit. -/
theorem eulerPatch_tendsto (J : ℕ) (y : ℝ) :
    Tendsto (eulerPatch J y) atTop (𝓝 (-2)) := patchArray_tendsto J _

/-- Actual complete head agreement is not an identification of the
infinite patched tail with actual primes. The same joined reverse
inequality survives every finite complete-arithmetic head test. -/
theorem eulerPatch_joined_gt_ceiling (J : ℕ) (y : ℝ) :
    ∀ᶠ N : ℕ in atTop, (42/25 : ℝ) <
      (-traceError (eulerPatch J y) (N-1)-
        harmonicEvaluation (eulerPatch J y) sourceRadius N).re :=
  patched_joined_gt_ceiling J _

/-- The terminal regression control matches ANY prescribed finite
complete-prime jet, passes EVERY-order Euler envelope, and still
violates the unchanged signed evaluator cofinally. The local negative
integer modes and explicit analytic remainder are those proved above.
There is no claim that this array equals the complete prime tail. -/
theorem exists_complete_jet_control (J : ℕ) (y : ℝ) :
    ∃ b : ℕ → ℂ,
      (∀ n, n < J → b n = ordinaryArray sourceRadius y n) ∧
      (∀ n, ‖b n‖ <= eulerEnvelope n) ∧
      Tendsto b atTop (𝓝 (-2)) ∧
      (∀ᶠ N : ℕ in atTop, (42/25 : ℝ) <
        (-traceError b (N-1)-harmonicEvaluation b sourceRadius N).re) :=
  ⟨eulerPatch J y, fun _ hn => eulerPatch_matches_complete y hn,
    eulerPatch_all_order_envelope J y, eulerPatch_tendsto J y,
    eulerPatch_joined_gt_ceiling J y⟩

/-- A method relying ONLY on finite complete arithmetic moments and
the all-order norm envelope cannot prove the desired ceiling. Actual
infinite prime coverage or an additional cofinal signed correlation is
essential. This does not refute the ceiling for actual zeta zeros. -/
theorem no_ceiling_from_finite_euler_head (J : ℕ) (y : ℝ) :
    ¬ (∀ b : ℕ → ℂ,
      (∀ n, n < J → b n = ordinaryArray sourceRadius y n) →
      (∀ n, ‖b n‖ <= eulerEnvelope n) →
      ∀ᶠ N : ℕ in atTop,
        (-traceError b (N-1)-harmonicEvaluation b sourceRadius N).re <= 42/25) := by
  intro h
  obtain ⟨b, hhead, hbound, _hsource, hlarge⟩ := exists_complete_jet_control J y
  have hsmall := h b hhead hbound
  obtain ⟨N, hl, hs⟩ := (hlarge.and hsmall).exists
  linarith only [hl, hs]

end RiemannGaussian.ZetaRieszCeilingEulerJetAudit
