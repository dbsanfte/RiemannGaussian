/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszClippedOwnerPeriodFloor

/-!
# Signed owner periods over all cofactor prime-log geometries

The signed prime period is evaluated before bounding cofactor mass. Its
inverse-square owner-log saving combines with exact squarefree count
symmetry and the leading-one reciprocal-prime interval bound. This avoids
the comparable-log restriction without making a prime-density replacement
of the signed carrier. Complete fibres and their literal boundaries remain
explicit; no independent whole floor is asserted.
-/

noncomputable section
open Filter Topology Real MeasureTheory
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszBroadOwnerPeriodFloor
open ZetaRieszClippedOwnerPeriodFloor ZetaRieszTinyOwnerPeriodFloor
open ZetaRieszLogShellPeriodFloor ZetaRieszSymmetricPeriodPayment
open ZetaRieszStaggeredFloor ZetaRieszSignedPeriodFloor ZetaRieszFixedCountPeriod
open ZetaRieszAllowancePrimeBoxes ZetaRieszQuantitativePrimePeriod
open ZetaRieszOwnerCurvatureFloor
open ZetaRieszJointOwnerFibreFloor
open ZetaRieszPrimeEndpoint
open ZetaRieszMacroPrimeWindows
open ZetaRieszRadialCompensation ZetaRieszBandCompensation ZetaRieszMultiPeriodSix

set_option maxHeartbeats 800000

private def reciprocalKernel (x : ℝ) : ℝ := 1/(x*log x)

private def reciprocalDeriv (x : ℝ) : ℝ := -(1+(log x)⁻¹)/(x^2*log x)

private theorem reciprocal_hasDerivAt {x : ℝ} (hx : 1<x) :
    HasDerivAt reciprocalKernel (reciprocalDeriv x) x := by
  change HasDerivAt (fun x : ℝ => 1/(x*log x)) _ x
  simpa only [reciprocalDeriv,add_zero,zero_sub,one_mul] using
    profile_deriv (fun _ => 1) (fun _ => 0) 0
      (fun t => hasDerivAt_const t 1) hx

private def errorPrimitive (x : ℝ) : ℝ := -(log x)⁻¹-1/(2*log x^2)

private theorem errorPrimitive_hasDerivAt {x : ℝ} (hx : 1<x) :
    HasDerivAt errorPrimitive (1/(x*log x^2)+1/(x*log x^3)) x := by
  have hx0 : x≠0 := (show 0<x by linarith).ne'
  have hl0 : log x≠0 := (log_pos hx).ne'
  have h₁ := (Real.hasDerivAt_log hx0).inv hl0
  have h₂ := ((Real.hasDerivAt_log hx0).pow 2).const_mul 2
  have h₃ := (hasDerivAt_const x 1).div h₂ (by positivity : 2*log x^2≠0)
  apply (h₁.neg.sub h₃).congr_deriv
  simp only [Pi.pow_apply,one_mul,zero_mul,zero_sub,Nat.cast_ofNat,Nat.reduceSub,pow_one]
  field_simp
  ring

/-- An actual reciprocal-prime interval bound with leading coefficient
ONE. The absolute Chebyshev error here prices only the positive cofactor
mass after signed prime-period cancellation; it does not transport the
retained signed carrier to a continuous prime density. -/
theorem prime_interval_mass_le {a b : ℝ} (ha : 5000≤a) (hab : a≤b) :
    (∑ p ∈ (Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime, (p : ℝ)⁻¹) ≤
      log (b/a)+1/a := by
  have ha0 : 0<a := by linarith
  have hb0 : 0<b := ha0.trans_le hab
  have heab := exp_le_exp.mpr hab
  have hxp x (hx : x ∈ Set.Icc (exp a) (exp b)) : 0<x := (exp_pos a).trans_le hx.1
  have hxl x (hx : x ∈ Set.Icc (exp a) (exp b)) : a≤log x :=
    (le_log_iff_exp_le (hxp x hx)).mpr hx.1
  have hx1 x (hx : x ∈ Set.Icc (exp a) (exp b)) : 1<x :=
    (one_lt_exp_iff.mpr ha0).trans_le hx.1
  have hrd x (hx : x ∈ Set.Icc (exp a) (exp b)) := reciprocal_hasDerivAt (hx1 x hx)
  have hrc : ContinuousOn reciprocalDeriv (Set.Icc (exp a) (exp b)) := by
    exact ((continuousOn_const.add
      ((continuousOn_id.log (fun x hx => (hxp x hx).ne')).inv₀
        (fun x hx => (ha0.trans_le (hxl x hx)).ne'))).neg).div
      ((continuousOn_id.pow 2).mul (continuousOn_id.log (fun x hx => (hxp x hx).ne')))
      (fun x hx => by have := hxp x hx; have := ha0.trans_le (hxl x hx); positivity)
  have hri : IntegrableOn (deriv reciprocalKernel) (Set.Icc (exp a) (exp b)) :=
    hrc.integrableOn_Icc.congr_fun (fun x hx => (hrd x hx).deriv.symm) measurableSet_Icc
  have he := prime_abel reciprocalKernel (exp_pos a).le heab
    (fun x hx => (hrd x hx).differentiableAt) hri
  have hs : (∑ p ∈ (Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime,
      reciprocalKernel p*log p) =
      ∑ p ∈ (Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have hlp : log p≠0 := (log_pos (by exact_mod_cast hpp.one_lt)).ne'
    dsimp only [reciprocalKernel]
    field_simp
  have hmain : (∫ x in Set.Ioc (exp a) (exp b), reciprocalKernel x)=log (b/a) := by
    have hd x (hx : x ∈ Set.uIcc (exp a) (exp b)) :
        HasDerivAt (fun x : ℝ => log (log x)) (reciprocalKernel x) x := by
      rw [Set.uIcc_of_le heab] at hx
      simpa only [reciprocalKernel,Function.comp_def,div_eq_mul_inv,mul_inv_rev,one_mul,mul_comm] using
        ((hasDerivAt_log (ha0.trans_le (hxl x hx)).ne').comp x
          (hasDerivAt_log (hxp x hx).ne'))
    rw [← intervalIntegral.integral_of_le heab,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
    · rw [log_exp,log_exp,log_div hb0.ne' ha0.ne']
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le heab]
      exact (show ContinuousOn reciprocalKernel (Set.Icc (exp a) (exp b)) from
        fun x hx => (hrd x hx).continuousAt.continuousWithinAt).integrableOn_Icc
  have htheta x (hx : x ∈ Set.Icc (exp a) (exp b)) :
      |Chebyshev.theta x-x| ≤ (41/100 : ℝ)*x/log x := by
    have hh := RosserSchoenfeldLargeChebyshev.abs_theta_sub_exp_le (ha.trans (hxl x hx))
    rwa [exp_log (hxp x hx)] at hh
  have hend x (hx : x ∈ Set.Icc (exp a) (exp b)) :
      |reciprocalKernel x*(Chebyshev.theta x-x)| ≤ (41/100 : ℝ)/log x^2 := by
    have hx0 := hxp x hx
    have hl0 := ha0.trans_le (hxl x hx)
    rw [abs_mul,reciprocalKernel,abs_of_pos (by positivity [ha0.trans_le (hxl x hx)])]
    have hh := mul_le_mul_of_nonneg_left (htheta x hx)
      (by positivity [ha0.trans_le (hxl x hx)] : 0≤1/(x*log x))
    exact hh.trans_eq (by field_simp)
  let B : ℝ → ℝ := fun x => (41/100 : ℝ)*(1/(x*log x^2)+1/(x*log x^3))
  have hBc : ContinuousOn B (Set.Icc (exp a) (exp b)) := by
    dsimp only [B]
    apply continuousOn_const.mul
    apply ContinuousOn.add <;>
      exact continuousOn_const.div
        (continuousOn_id.mul ((continuousOn_id.log (fun x hx => (hxp x hx).ne')).pow _))
        (fun x hx => by have := hxp x hx; have := ha0.trans_le (hxl x hx); positivity)
  have hbound x (hx : x ∈ Set.Icc (exp a) (exp b)) :
      |deriv reciprocalKernel x*(x-Chebyshev.theta x)|≤B x := by
    have hx0 := hxp x hx
    have hl0 := ha0.trans_le (hxl x hx)
    rw [(hrd x hx).deriv,abs_mul,abs_sub_comm x]
    have hh := mul_le_mul (le_refl |reciprocalDeriv x|) (htheta x hx)
      (abs_nonneg _) (abs_nonneg _)
    apply hh.trans_eq
    dsimp only [reciprocalDeriv,B]
    rw [abs_div,abs_neg,abs_of_pos (by positivity [ha0.trans_le (hxl x hx)]),
      abs_of_pos (by positivity [ha0.trans_le (hxl x hx)])]
    field_simp
  have hBi : (∫ x in Set.Ioc (exp a) (exp b),B x)=
      (41/100 : ℝ)*(1/a-1/b+1/(2*a^2)-1/(2*b^2)) := by
    rw [← intervalIntegral.integral_of_le heab,intervalIntegral.integral_const_mul]
    have hd x (hx : x ∈ Set.uIcc (exp a) (exp b)) :=
      errorPrimitive_hasDerivAt (hx1 x (by simpa only [Set.uIcc_of_le heab] using hx))
    have hi : IntervalIntegrable (fun x : ℝ => 1/(x*log x^2)+1/(x*log x^3))
        volume (exp a) (exp b) := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le heab]
      exact (hBc.div_const (41/100)).integrableOn_Icc.congr_fun
        (fun x _ => by dsimp [B]; ring) measurableSet_Icc
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
    simp only [errorPrimitive,log_exp]
    ring
  have hierr := integrable_prime_error reciprocalKernel (exp_pos a).le hri
  have hint : |∫ x in Set.Ioc (exp a) (exp b),
      deriv reciprocalKernel x*(x-Chebyshev.theta x)| ≤
        (41/100 : ℝ)*(1/a-1/b+1/(2*a^2)-1/(2*b^2)) := by
    calc
      _ ≤ ∫ x in Set.Ioc (exp a) (exp b), |deriv reciprocalKernel x*(x-Chebyshev.theta x)| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ x in Set.Ioc (exp a) (exp b), B x := setIntegral_mono_on hierr.abs
        (hBc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) measurableSet_Ioc
        (fun x hx => hbound x (Set.Ioc_subset_Icc_self hx))
      _ = _ := hBi
  rw [hs,hmain] at he
  have hh : |(∑ p ∈ (Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime,(p : ℝ)⁻¹)-log (b/a)| ≤
      (41/100 : ℝ)/b^2+(41/100 : ℝ)/a^2+
        (41/100 : ℝ)*(1/a-1/b+1/(2*a^2)-1/(2*b^2)) := by
    rw [he]
    apply ((abs_add_le _ _).trans
      (add_le_add (abs_sub _ _) le_rfl)).trans
    simpa only [log_exp] using add_le_add
      (add_le_add (hend _ ⟨heab,le_rfl⟩) (hend _ ⟨le_rfl,heab⟩)) hint
  have hden : (41/100 : ℝ)/b^2+(41/100 : ℝ)/a^2+
      (41/100 : ℝ)*(1/a-1/b+1/(2*a^2)-1/(2*b^2))≤1/a := by
    have hsq := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ)≤41/100)
      (sq_pos_of_pos ha0) (pow_le_pow_left₀ ha0.le hab 2)
    have hi : 0≤1/b := by positivity
    have hi₂ : 0≤1/(2*b^2) := by positivity
    have he₁ : (41/100 : ℝ)/a^2≤(1/4 : ℝ)/a :=
      (div_le_div_iff₀ (sq_pos_of_pos ha0) ha0).mpr (by nlinarith)
    have he₂ : (41/100 : ℝ)/(2*a^2)≤(1/100 : ℝ)/a :=
      (div_le_div_iff₀ (by positivity : 0<2*a^2) ha0).mpr (by nlinarith)
    have heq : (41/100 : ℝ)/b^2+(41/100 : ℝ)/a^2+
        (41/100 : ℝ)*(1/a-1/b+1/(2*a^2)-1/(2*b^2)) =
        (41/100 : ℝ)/b^2+(41/100 : ℝ)/a^2+
        (41/100 : ℝ)/a-(41/100 : ℝ)*(1/b)+(41/100 : ℝ)/(2*a^2)-
        (41/100 : ℝ)*(1/(2*b^2)) := by ring
    rw [heq]
    have hn₁ : 0≤(41/100 : ℝ)*(1/b) := mul_nonneg (by norm_num) hi
    have hn₂ : 0≤(41/100 : ℝ)*(1/(2*b^2)) := mul_nonneg (by norm_num) hi₂
    calc
      _ ≤ (41/100 : ℝ)/a^2+(41/100 : ℝ)/a^2+(41/100 : ℝ)/a+
          (41/100 : ℝ)/(2*a^2) := by linarith only [hsq,hn₁,hn₂]
      _ ≤ (1/4 : ℝ)/a+(1/4 : ℝ)/a+(41/100 : ℝ)/a+(1/100 : ℝ)/a :=
        add_le_add (add_le_add (add_le_add he₁ he₁) le_rfl) he₂
      _ = (23/25 : ℝ)/a := by ring
      _ ≤ 1/a := div_le_div_of_nonneg_right (by norm_num) ha0.le
  linarith only [(abs_le.mp hh).2,hden]

/-- All selected squarefree counts retain the exact factorial symmetry
for an arbitrary finite prime universe. No comparable-log assumption. -/
theorem interval_cofactor_mass_le (D Q : Finset ℕ) (k : ℕ) {M : ℝ}
    (hQ : (∑ p ∈ Q,(p : ℝ)⁻¹)≤M)
    (hD : ∀ a ∈ D, Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors ⊆ Q) :
    (∑ a ∈ D,(a : ℝ)⁻¹)≤M^k/(k.factorial : ℝ) := by
  have hprod a (ha : a ∈ D) :
      (∏ p ∈ a.primeFactors,(p : ℝ)⁻¹)=(a : ℝ)⁻¹ := by
    rw [Finset.prod_inv_distrib,← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree (hD a ha).1]
  have hh := factorial_product_mass D Q k (fun p => (p : ℝ)⁻¹)
    (fun _ _ => by positivity) hD
  have hpow := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity)) hQ k
  apply (le_div_iff₀ (show (0 : ℝ)<k.factorial by exact_mod_cast Nat.factorial_pos k)).mpr
  rw [mul_comm]
  simpa only [Finset.sum_congr rfl hprod] using hh.trans hpow

private theorem response_constant_bound (k : ℕ) : responseConstant k≤6*(2 : ℝ)^k := by
  have hp (b : ℕ) : (ZetaRieszSignedSperner.parityCapacity (k-2) b : ℝ)≤(2 : ℝ)^k := by
    have hh := (ZetaRieszSignedSperner.parityCapacity_le_middle (k-2) b).trans
      (Nat.choose_le_two_pow (k-2) ((k-2)/2))
    exact_mod_cast hh.trans (Nat.pow_le_pow_right (by norm_num : 1≤(2 : ℕ)) (by omega : k-2≤k))
  have h0 := hp 0
  have h1 := hp 1
  unfold responseConstant
  nlinarith only [h0,h1,one_le_pow₀ (by norm_num : (1 : ℝ)≤2) (n := k)]

/-- Leading-one mass bound for every actual finite prime interval. -/
theorem logPrimes_mass_le {a b : ℝ} (ha : 5000≤a) (hab : a≤b) :
    (∑ p ∈ logPrimes a (b-a),(p : ℝ)⁻¹)≤log (b/a)+1/a := by
  have he : logPrimes a (b-a)=
      (Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime := by
    dsimp [logPrimes,PrimeWindow.primesInWindow]
    rw [← exp_add]
    congr 2
    ring
  rw [he]
  exact prime_interval_mass_le ha hab

/-- The exact count exponential grows quadratically in the owner-log
range, rather than with a coarse exponent exceeding two. This is the
quantitative gain that permits every prime-log geometry to be joined. -/
theorem interval_count_exponential_le {a H : ℝ} (ha : 5000≤a) (hH : a≤H) :
    exp (2*(log (4*H/a)+1/a))≤32*H^2/a^2 := by
  have ha0 : 0<a := by linarith
  have hH0 : 0<H := ha0.trans_le hH
  have he := Real.exp_bound_div_one_sub_of_interval
    (x := 2/a) (by positivity) (by
      apply (div_lt_one ha0).mpr
      linarith)
  have hsmall : 2/a≤1/2 := (div_le_iff₀ ha0).mpr (by linarith)
  have hden : 1/(1-2/a)≤2 := (div_le_iff₀ (by linarith : 0<1-2/a)).mpr (by linarith)
  have he' : exp (2/a)≤2 := he.trans hden
  have hid : exp (2*(log (4*H/a)+1/a))=(4*H/a)^2*exp (2/a) := by
    rw [show 2*(log (4*H/a)+1/a)=2*log (4*H/a)+2/a by ring,exp_add,
      show 2*log (4*H/a)=log ((4*H/a)^2) by rw [log_pow]; norm_num,exp_log (by positivity)]
  rw [hid]
  exact (mul_le_mul_of_nonneg_left he' (sq_nonneg _)).trans_eq (by ring)

/-- Signed original full-factorial prime period with arbitrary cofactor
prime sizes. Only the actual owner logarithm and least-prime upper bound
enter its cost; no lower share restriction is added. -/
theorem broad_unallocated_row_floor {k N : ℕ} (hk : 2 ≤ k) {e : ℝ} (he : |e|=1)
    {v y L H : ℝ} (hH : 5000 ≤ H) (hNv : (N : ℝ)+2 ≤ v)
    (hy : 54 ≤ y) (hL : v/2 ≤ L) {a : ℕ} (ha : Squarefree a)
    (hc : a.primeFactors.card=k) (hmin : log a.minFac ≤ 4*H)
    (hP : H ≤ v-Real.pi/y-log a)
    (howner : ∀ q ∈ a.primeFactors, log q ≤ v-Real.pi/y-log a)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v) ≤ 0) :
    -(amplitude N v/v)*(481*(2 : ℝ)^k/H)*(a : ℝ)⁻¹ ≤
      ∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e ∅ L y N (p*a) := by
  have hH0 : 0 < H := by linarith
  have hπ0 : 0 ≤ Real.pi/y := by positivity
  have hv100 : 100 ≤ v := by linarith [log_natCast_nonneg a]
  have hv0 : 0 < v := by linarith
  have hL0 : 0 < L := by linarith
  have ha0 : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha.ne_zero
  have hP0 : 0 < v-Real.pi/y-log a := hH0.trans_le hP
  let B := responseConstant k*log a.minFac
  let E := (2 : ℝ)^k*Real.pi/(4*y)
  have hB : 0 ≤ B := by dsimp [B]; positivity [responseConstant_pos k,log_natCast_nonneg a.minFac]
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hV0 : 0 < v-Real.pi/y := by linarith [log_natCast_nonneg a]
  have hCb : 0 ≤ jointPeriodCost N v y (log a) := by
    unfold jointPeriodCost
    positivity
  have hBbound : B ≤ responseConstant k*(4*H) :=
    mul_le_mul_of_nonneg_left hmin (responseConstant_pos k).le
  have hEbound : E ≤ (2 : ℝ)^k/64 := by
    have hh := mul_le_mul_of_nonneg_left (quarter_period_width_le hy)
      (by positivity : (0 : ℝ) ≤ 2^k)
    exact (show E=(2 : ℝ)^k*(Real.pi/(4*y)) by dsimp [E]; ring) ▸
      hh.trans_eq (by ring)
  have hinner : B*jointPeriodCost N v y (log a)+E/(v-Real.pi/y-log a) ≤
      (20*responseConstant k+(2 : ℝ)^k/64)/H := by
    have hbc := mul_le_mul hBbound (jointPeriodCost_shell_le hy hNv hH0 hP)
      hCb (by positivity [responseConstant_pos k])
    have hec := (div_le_div_of_nonneg_left hE hH0 hP).trans
      (div_le_div_of_nonneg_right hEbound hH0.le)
    have heq : (responseConstant k*(4*H))*(5/H^2)+((2 : ℝ)^k/64)/H =
        (20*responseConstant k+(2 : ℝ)^k/64)/H := by
      field_simp
      ring
    exact (add_le_add hbc hec).trans_eq heq
  have hbase : 0 ≤ amplitude N v/v := div_nonneg (amplitude_nonneg N hv0.le) hv0.le
  have hpre : 2*amplitude N v/(L*a) ≤ 4*(amplitude N v/v)*(a : ℝ)⁻¹ := by
    have hh := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (by positivity [amplitude_nonneg N hv0.le] :
        0 ≤ 2*amplitude N v) (by positivity : 0 < v/2) hL)
      (inv_nonneg.mpr ha0.le)
    convert hh using 1 <;> first | rfl | (simp only [div_eq_mul_inv,mul_inv_rev]; ring)
  have htotal := mul_le_mul hpre hinner (by positivity :
      0 ≤ B*jointPeriodCost N v y (log a)+E/(v-Real.pi/y-log a))
      (by positivity : 0 ≤ 4*(amplitude N v/v)*(a : ℝ)⁻¹)
  have hcoeff : 4*(20*responseConstant k+(2 : ℝ)^k/64) ≤ 481*(2 : ℝ)^k := by
    nlinarith only [response_constant_bound k,(show 0 ≤ (2 : ℝ)^k by positivity)]
  have hcost := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hcoeff hH0.le)
    (mul_nonneg hbase (inv_nonneg.mpr ha0.le))
  have hfloor := unallocated_fibre_floor hk he hv100 hNv hy hL0 ha hc howner
    (by linarith : 5000 ≤ v-Real.pi/y-log a) hpeak hsign
  change -(2*amplitude N v/(L*a))*(B*jointPeriodCost N v y (log a)+E/(v-Real.pi/y-log a)) ≤ _ at hfloor
  have hpaid : (2*amplitude N v/(L*a))*(B*jointPeriodCost N v y (log a)+E/(v-Real.pi/y-log a)) ≤
      (amplitude N v/v)*(481*(2 : ℝ)^k/H)*(a : ℝ)⁻¹ := by
    exact htotal.trans (by convert hcost using 1 <;> ring)
  rw [neg_mul] at hfloor
  simpa only [neg_mul] using (neg_le_neg hpaid).trans hfloor

/-- The same factorial count sum is uniform over every finite selected
count set. It is charged only after the signed prime periods are joined. -/
theorem sum_count_price_le (I : Finset ℕ) {M : ℝ} (hM : 0≤M) {c : ℝ} (hc : 0≤c) :
    (∑ k ∈ I,c*(2*M)^k/(k.factorial : ℝ))≤c*exp (2*M) := by
  have he := NormedSpace.expSeries_div_hasSum_exp (2*M)
  have hh := he.summable.sum_le_tsum I (fun k _ => by positivity)
  rw [he.tsum_eq,← Real.exp_eq_exp_ℝ] at hh
  simpa only [← Finset.mul_sum,mul_div_assoc] using mul_le_mul_of_nonneg_left hh hc

/-- A complete-period floor for ALL prime-log spreads and ALL counts.
Only the actual owner-log lower endpoint and a finite cofactor prime
universe enter. Unlike a tuple cover, every squarefree label costs once. -/
theorem broad_all_counts_floor (I : Finset ℕ) (N : ℕ) (e : ℝ)
    (S : ℕ → Finset ℕ) (Q : Finset ℕ) {v y L H M : ℝ}
    (hI : ∀ k ∈ I,2≤k) (he : |e|=1) (hH : 5000≤H)
    (hNv : (N : ℝ)+2≤v) (hy : 54≤y) (hL : v/2≤L)
    (hM : 0≤M) (hQmass : (∑ p ∈ Q,(p : ℝ)⁻¹)≤M)
    (hQlog : ∀ p ∈ Q,log p≤4*H)
    (hS : ∀ k ∈ I,∀ a ∈ S k,Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors ⊆ Q)
    (hP : ∀ k ∈ I,∀ a ∈ S k,H≤v-Real.pi/y-log a)
    (howner : ∀ k ∈ I,∀ a ∈ S k,∀ q ∈ a.primeFactors,log q≤v-Real.pi/y-log a)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0) :
    -(481*exp (2*M)/H)*(amplitude N v/v)≤
      ∑ k ∈ I,∑ a ∈ S k,∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e ∅ L y N (p*a) := by
  have hH0 : 0<H := by linarith
  have hv0 : 0<v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hf0 : 0≤amplitude N v/v := div_nonneg (amplitude_nonneg N hv0.le) hv0.le
  have hrow k (hk : k ∈ I) :
      -(481*(2*M)^k/(H*(k.factorial : ℝ)))*(amplitude N v/v)≤
        ∑ a ∈ S k,∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
          signedPart e ∅ L y N (p*a) := by
    have hm := interval_cofactor_mass_le (S k) Q k hQmass (hS k hk)
    have hh := Finset.sum_le_sum (fun a ha => by
      have hs := hS k hk a ha
      have ha1 : a≠1 := by intro ha1; simp [ha1] at hs; have := hI k hk; omega
      have hmin := (Nat.minFac_prime ha1).mem_primeFactors (Nat.minFac_dvd a) hs.1.ne_zero
      exact broad_unallocated_row_floor (hI k hk) he hH hNv hy hL hs.1 hs.2.1
        (hQlog _ (hs.2.2 hmin)) (hP k hk a ha) (howner k hk a ha) hpeak hsign)
    rw [← Finset.mul_sum] at hh
    have hc := mul_le_mul_of_nonneg_left hm
      (by positivity : 0≤(amplitude N v/v)*(481*(2 : ℝ)^k/H))
    have hb := neg_le_neg hc
    have hid : -((amplitude N v/v)*(481*(2 : ℝ)^k/H)*(M^k/(k.factorial : ℝ)))=
        -(481*(2*M)^k/(H*(k.factorial : ℝ)))*(amplitude N v/v) := by
      simp only [mul_pow,div_eq_mul_inv,mul_inv_rev]
      ring
    rw [hid] at hb
    exact hb.trans (by simpa only [neg_mul,mul_assoc] using hh)
  have hh := Finset.sum_le_sum hrow
  have hp := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (sum_count_price_le I hM (by norm_num : (0 : ℝ)≤481)) hH0.le) hf0
  have hid : (∑ k ∈ I,481*(2*M)^k/(H*(k.factorial : ℝ)))=
      (∑ k ∈ I,481*(2*M)^k/(k.factorial : ℝ))/H := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  simp only [neg_mul] at hh
  rw [Finset.sum_neg_distrib,← Finset.sum_mul,hid] at hh
  simpa only [neg_mul] using (neg_le_neg hp).trans hh

/-- Quantitative signed payment without comparable prime-log geometry.
The leading-one prime-mass estimate exactly offsets the count exponential:
one whole owner-log shell costs 15392 H/a^2 in the SAME radial units. -/
theorem broad_interval_period_floor (I : Finset ℕ) (N : ℕ) (e : ℝ)
    (S : ℕ → Finset ℕ) {v y L a H : ℝ} (ha : 5000≤a) (haH : a≤H)
    (hI : ∀ k ∈ I,2≤k) (he : |e|=1) (hNv : (N : ℝ)+2≤v) (hy : 54≤y) (hL : v/2≤L)
    (hS : ∀ k ∈ I,∀ b ∈ S k,Squarefree b ∧ b.primeFactors.card=k ∧
      b.primeFactors ⊆ logPrimes a (4*H-a))
    (hP : ∀ k ∈ I,∀ b ∈ S k,H≤v-Real.pi/y-log b)
    (howner : ∀ k ∈ I,∀ b ∈ S k,∀ q ∈ b.primeFactors,log q≤v-Real.pi/y-log b)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0) :
    -(15392*H/a^2)*(amplitude N v/v)≤
      ∑ k ∈ I,∑ b ∈ S k,∑ p ∈ logPrimes (v-Real.pi/y-log b) (2*Real.pi/y),
        signedPart e ∅ L y N (p*b) := by
  have ha0 : 0<a := by linarith
  have hH0 : 0<H := ha0.trans_le haH
  have hM : 0≤log (4*H/a)+1/a := add_nonneg
    (log_nonneg ((one_le_div ha0).mpr (by linarith))) (by positivity)
  have hh := broad_all_counts_floor I N e S (logPrimes a (4*H-a)) hI he
    (ha.trans haH) hNv hy hL hM (logPrimes_mass_le ha (by linarith : a≤4*H))
    (fun p hp => by have hh := (logPrimes_bounds hp).2.2; linarith) hS hP howner hpeak hsign
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (interval_count_exponential_le ha haH)
      (by norm_num : (0 : ℝ)≤481)) hH0.le
  have hid : (481*(32*H^2/a^2))/H=15392*H/a^2 := by field_simp; ring
  rw [hid] at hc
  have hv0 : 0<v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hpay := neg_le_neg (mul_le_mul_of_nonneg_right hc
    (div_nonneg (amplitude_nonneg N hv0.le) hv0.le))
  simpa only [neg_mul] using hpay.trans (by simpa only [neg_mul] using hh)

/-- The ACTUAL clipped owner-start witness, rather than a comparable-log
assumption, isolates the near-tied pair and bounds the remaining cofactor.
Every original prime outside that pair stays in the original universe Q. -/
theorem broad_clipped_cofactor_cover {k n : ℕ} (hn : Squarefree n)
    (hc : n.primeFactors.card=k+2) (hk : 0<k) {v H : ℝ} (Q : Finset ℕ)
    (hT : v-1/16<log n ∧ log n≤v+1/16)
    (hclip : ∃ q ∈ (n/ZetaRieszPrimeEndpoint.largestPrime n).primeFactors,
      H≤log q ∧ log (ZetaRieszPrimeEndpoint.largestPrime n)-log q≤1/8)
    (hQ : (n/ZetaRieszPrimeEndpoint.largestPrime n).primeFactors ⊆ Q) :
    ∃ b q : ℕ,n=ZetaRieszPrimeEndpoint.largestPrime n*(q*b) ∧ Squarefree b ∧
      b.primeFactors.card=k ∧ b.primeFactors ⊆ Q ∧ log b≤v-2*H+1/16 ∧
      ZetaRieszPrimeEndpoint.largestPrime n ∈ ZetaRieszOwnerTieFloor.pairWindow v b ∧
      q ∈ ZetaRieszOwnerTieFloor.pairWindow v b := by
  have hc3 : 3≤n.primeFactors.card := by omega
  have hd := canonical_owner_data hn hc3
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2≤n.primeFactors.card)
  obtain ⟨q,hq,hqH,hgap⟩ := hclip
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hqN := hqp.mem_primeFactors ((Nat.dvd_of_mem_primeFactors hq).trans
    (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp))) hn.ne_zero
  have hnot : ZetaRieszPrimeEndpoint.largestPrime n≠q := by
    intro he
    have hh := Nat.dvd_of_mem_primeFactors hq
    rw [← he] at hh
    exact hd.2.2.2.2.2 hh
  obtain ⟨b,he,hb,hbc⟩ := ZetaRieszOwnerTieFloor.two_prime_factorization hn hc hp hqN hnot
  have haeq : n/ZetaRieszPrimeEndpoint.largestPrime n=q*b := by
    conv_lhs => lhs; rw [he]
    exact Nat.mul_div_cancel_left _ hd.1.pos
  have hbd : b ∣ n/ZetaRieszPrimeEndpoint.largestPrime n := by rw [haeq]; exact dvd_mul_left b q
  have hbsub := (Nat.primeFactors_mono hbd hd.2.2.1.ne_zero).trans hQ
  have hqle : log q≤log (ZetaRieszPrimeEndpoint.largestPrime n) := log_le_log
    (by exact_mod_cast hqp.pos) (by exact_mod_cast hd.2.2.2.2.1 q hqN)
  have hlog : log n=log (ZetaRieszPrimeEndpoint.largestPrime n)+log q+log b := by
    conv_lhs => rw [he,Nat.cast_mul,log_mul (by exact_mod_cast hd.1.ne_zero)
      (by exact_mod_cast Nat.mul_ne_zero hqp.ne_zero hb.ne_zero),Nat.cast_mul,
      log_mul (by exact_mod_cast hqp.ne_zero) (by exact_mod_cast hb.ne_zero)]
    ring
  refine ⟨b,q,he,hb,hbc,hbsub,by linarith [hT.2],?_,?_⟩
  · exact (mem_logPrimes_iff _ _ _).mpr ⟨hd.1,by linarith [hT.1],by linarith [hT.2]⟩
  · exact (mem_logPrimes_iff _ _ _).mpr ⟨hqp,by linarith [hT.1],by linarith [hT.2]⟩

/-- Count-uniform literal clipped boundary norm. The remaining cofactor
can have ANY prime-log spread inside Q, independently of the tied pair. -/
theorem broad_clipped_count_norm_bound {k N : ℕ} (hk : 0 < k)
    (A D Q : Finset ℕ) (y : ℝ) {v L H M : ℝ} (hH : 10000 ≤ H)
    (hv : 0 < v) (hNv : (N : ℝ)+1 ≤ v) (hL : v/2 ≤ L)
    (hM : 0≤M) (hQmass : (∑ p ∈ Q,(p : ℝ)⁻¹)≤M)
    (hQlog : ∀ p ∈ Q,log p≤4*H)
    (hD : ∀ n ∈ D, Squarefree n ∧ n.primeFactors.card=k+2 ∧
      (v-1/16 < log n ∧ log n ≤ v+1/16) ∧
      (∃ q ∈ (n/largestPrime n).primeFactors,H≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
        (n/largestPrime n).primeFactors ⊆ Q) :
    (∑ n ∈ D, ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
      ((1536*(2*M)^k/(k.factorial : ℝ))/H)*(amplitude N v/v) := by
  have hH0 : 0 < H := by linarith
  let R := (ZetaRieszCofactorMass.products k (4*H)).filter (fun b : ℕ =>
    Squarefree b ∧ b.primeFactors.card=k ∧ b.primeFactors ⊆ Q ∧
      log b ≤ v-2*H+1/16)
  let V := R.sigma (fun b => (ZetaRieszOwnerTieFloor.pairWindow v b).product
    (ZetaRieszOwnerTieFloor.pairWindow v b))
  let label := fun x : Σ _ : ℕ, ℕ×ℕ => x.2.1*(x.2.2*x.1)
  let f := fun n => if n ∈ D then
    ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ else 0
  let B := 2*amplitude N v*responseConstant (k+2)/L
  have hL0 : 0 < L := by linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity [amplitude_nonneg N hv.le,responseConstant_pos (k+2)]
  have hf (n : ℕ) : 0 ≤ f n := by dsimp [f]; split_ifs <;> positivity
  have hcover : D ⊆ V.image label := by
    intro n hn
    obtain ⟨hs,hc,hT,htie,hshell⟩ := hD n hn
    obtain ⟨b,q,he,hb,hbc,hbsub,hcap,hpw,hqw⟩ :=
      broad_clipped_cofactor_cover hs hc hk Q hT htie hshell
    have hbm : b ∈ ZetaRieszCofactorMass.products k (4*H) :=
      ZetaRieszCofactorMass.mem_products_of_squarefree hb hbc
        (fun r hr => hQlog r (hbsub hr))
    exact Finset.mem_image.mpr ⟨⟨b,(largestPrime n,q)⟩,Finset.mem_sigma.mpr
      ⟨Finset.mem_filter.mpr ⟨hbm,hb,hbc,hbsub,hcap⟩,
        Finset.mem_product.mpr ⟨hpw,hqw⟩⟩,he.symm⟩
  have hfirst : (∑ n ∈ D, ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤ ∑ x ∈ V, f (label x) := by
    have hh := (Finset.sum_le_sum_of_subset_of_nonneg hcover (fun n _ _ => hf n)).trans
      (Finset.sum_image_le_of_nonneg (fun n _ => hf n))
    simpa only [f,ite_true,Finset.sum_congr rfl (fun n hn => if_pos hn)] using hh
  have hpoint (b : ℕ) (hb : b ∈ R) (p q : ℕ) :
      f (p*(q*b)) ≤ B*(4*H*(b : ℝ)⁻¹)*(p : ℝ)⁻¹*(q : ℝ)⁻¹ := by
    obtain ⟨_,hbs,hbc,hbsub,_⟩ := Finset.mem_filter.mp hb
    have hb1 : b ≠ 1 := by intro hh; simp [hh] at hbc; omega
    have hm : log b.minFac ≤ 4*H := hQlog _
      (hbsub ((Nat.minFac_prime hb1).mem_primeFactors (Nat.minFac_dvd b) hbs.ne_zero))
    by_cases hn : p*(q*b) ∈ D
    · have hd := hD _ hn
      have hT : |log (p*(q*b) : ℕ)-v| ≤ 1 :=
        abs_le.mpr ⟨by linarith [hd.2.2.1.1],by linarith [hd.2.2.1.2]⟩
      have hh := ZetaRieszOwnerTieFloor.boundary_atom_norm A y hv hNv hL0 hd.1 hd.2.1
        hb1 (dvd_mul_of_dvd_right (dvd_mul_left b q) p) hT
      dsimp only [f]
      rw [if_pos hn]
      have hle := mul_le_mul_of_nonneg_left hm (by positivity :
        0 ≤ B*(b : ℝ)⁻¹*(p : ℝ)⁻¹*(q : ℝ)⁻¹)
      have heq : B*(log b.minFac/(p*(q*b) : ℕ)) =
          (B*(b : ℝ)⁻¹*(p : ℝ)⁻¹*(q : ℝ)⁻¹)*log b.minFac := by
        simp only [Nat.cast_mul,div_eq_mul_inv,mul_inv_rev]
        ring
      change _ ≤ B*(log b.minFac/(p*(q*b) : ℕ)) at hh
      rw [heq] at hh
      exact hh.trans (by convert hle using 1; ring)
    · dsimp only [f]
      rw [if_neg hn]
      positivity
  have hrec := interval_cofactor_mass_le R Q k hQmass (by
    intro b hb
    have hh := (Finset.mem_filter.mp hb).2
    exact ⟨hh.1,hh.2.1,hh.2.2.1⟩)
  have hsum : (∑ x ∈ V, f (label x)) ≤
      B*(4*H)*(4/H^2)*(M^k/(k.factorial : ℝ)) := by
    change (∑ x ∈ R.sigma _, f (label x)) ≤ _
    rw [Finset.sum_sigma]
    have hrow (b : ℕ) (hb : b ∈ R) :
        (∑ pq ∈ (ZetaRieszOwnerTieFloor.pairWindow v b).product
          (ZetaRieszOwnerTieFloor.pairWindow v b), f (pq.1*(pq.2*b))) ≤
        B*(4*H)*(4/H^2)*(b : ℝ)⁻¹ := by
      rw [Finset.product_eq_sprod,Finset.sum_product]
      have hh := Finset.sum_le_sum (s := ZetaRieszOwnerTieFloor.pairWindow v b)
        (fun p _ => Finset.sum_le_sum (s := ZetaRieszOwnerTieFloor.pairWindow v b)
          (fun q _ => hpoint b hb p q))
      have hm := shell_pairWindow_mass hH (Finset.mem_filter.mp hb).2.2.2.2
      have hsq := pow_le_pow_left₀ (by positivity) hm 2
      have heq : (∑ p ∈ ZetaRieszOwnerTieFloor.pairWindow v b,
          ∑ q ∈ ZetaRieszOwnerTieFloor.pairWindow v b,
            B*(4*H*(b : ℝ)⁻¹)*(p : ℝ)⁻¹*(q : ℝ)⁻¹) =
          (B*(4*H*(b : ℝ)⁻¹))*(∑ p ∈ ZetaRieszOwnerTieFloor.pairWindow v b,(p : ℝ)⁻¹)^2 := by
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul,← Finset.mul_sum,pow_two]
        ring
      rw [heq] at hh
      have hpay := mul_le_mul_of_nonneg_left hsq
        (by positivity : 0 ≤ B*(4*H*(b : ℝ)⁻¹))
      exact hh.trans (by convert hpay using 1; field_simp; ring)
    have hh := Finset.sum_le_sum hrow
    rw [← Finset.mul_sum] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hrec (by positivity))
  have hpre : B ≤ 4*(amplitude N v/v)*responseConstant (k+2) := by
    have hh := div_le_div_of_nonneg_left
      (by positivity [amplitude_nonneg N hv.le,responseConstant_pos (k+2)] :
        0 ≤ 2*amplitude N v*responseConstant (k+2))
      (by positivity : 0 < v/2) hL
    convert hh using 1
    all_goals first | rfl | ring
  have hcost := mul_le_mul_of_nonneg_right hpre
    (by positivity [hM] : 0 ≤ (4*H)*(4/H^2)*(M^k/(k.factorial : ℝ)))
  have heq : (4*(amplitude N v/v)*responseConstant (k+2))*
      ((4*H)*(4/H^2)*(M^k/(k.factorial : ℝ))) =
      (64*(amplitude N v/v)*responseConstant (k+2)*(M^k/(k.factorial : ℝ)))*(1/H) := by
    field_simp
    ring
  rw [heq] at hcost
  have hr : responseConstant (k+2) ≤ 24*(2 : ℝ)^k := by
    have hh := response_constant_bound (k+2)
    norm_num [pow_add] at hh
    convert hh using 1
    ring
  have hpay := mul_le_mul_of_nonneg_left hr (by positivity [hM,amplitude_nonneg N hv.le] :
    0 ≤ 64*(amplitude N v/v)*(M^k/(k.factorial : ℝ))*(1/H))
  have hpaid : (64*(amplitude N v/v)*responseConstant (k+2)*
      (M^k/(k.factorial : ℝ)))*(1/H) ≤
        ((1536*(2*M)^k/(k.factorial : ℝ))/H)*(amplitude N v/v) := by
    simp only [mul_pow,div_eq_mul_inv] at hpay ⊢
    nlinarith only [hpay]
  exact hfirst.trans (hsum.trans (by simpa only [mul_assoc] using hcost.trans hpaid))

/-- The entire original clipped ownership population, across EVERY
count, costs one boundary exponential. The two prime reciprocals are
retained before the remaining count mass is summed. -/
theorem broad_clipped_all_counts_norm_bound (A D Q : Finset ℕ) (y : ℝ) (N : ℕ)
    {v L H M : ℝ} (hH : 10000≤H) (hv : 0<v) (hNv : (N : ℝ)+1≤v) (hL : v/2≤L)
    (hM : 0≤M) (hQmass : (∑ p ∈ Q,(p : ℝ)⁻¹)≤M)
    (hQlog : ∀ p ∈ Q,log p≤4*H)
    (hD : ∀ n ∈ D,Squarefree n ∧ 3≤n.primeFactors.card ∧
      (v-1/16<log n ∧ log n≤v+1/16) ∧
      (∃ q ∈ (n/largestPrime n).primeFactors,H≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors ⊆ Q) :
    (∑ n ∈ D,‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖)≤
        (1536*exp (2*M)/H)*(amplitude N v/v) := by
  let I := D.image (fun n => n.primeFactors.card-2)
  let S := fun k => D.filter (fun n => n.primeFactors.card-2=k)
  let f := fun n => ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n‖
  have hI k (hk : k ∈ I) : 0<k := by
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hk
    have := (hD n hn).2.1
    omega
  have hrow k (hk : k ∈ I) :
      (∑ n ∈ S k,f n)≤((1536*(2*M)^k/(k.factorial : ℝ))/H)*(amplitude N v/v) := by
    apply broad_clipped_count_norm_bound (hI k hk) A (S k) Q y hH hv hNv hL hM hQmass hQlog
    intro n hn
    obtain ⟨hn,hcnt⟩ := Finset.mem_filter.mp hn
    have hh := hD n hn
    exact ⟨hh.1,by omega,hh.2.2⟩
  have heq : (∑ k ∈ I,∑ n ∈ S k,f n)=∑ n ∈ D,f n :=
    Finset.sum_fiberwise_of_maps_to (f := f) (fun n hn =>
      Finset.mem_image_of_mem (fun n => n.primeFactors.card-2) hn)
  have hh := Finset.sum_le_sum hrow
  rw [heq,← Finset.sum_mul,← Finset.sum_div] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (sum_count_price_le I hM (by norm_num : (0 : ℝ)≤1536))
      (by linarith : 0≤H)) (div_nonneg (amplitude_nonneg N hv.le) hv.le))

/-- All selected counts, their complete signed periods and the ACTUAL
owner-start mask loss joined into one payment, with no double charge for
the two staggered sign selections. This is the shared mechanism of the
previous single-sector savings, now allowing arbitrary prime-log spreads. -/
theorem broad_signed_period_with_boundary_floor (I : Finset ℕ) (N : ℕ) (e : ℝ)
    (S : ℕ → Finset ℕ) (D P Q₀ U : Finset ℕ) {v y L H M : ℝ}
    (hI : ∀ k ∈ I,2≤k) (he : |e|=1) (hH : 10000≤H)
    (hNv : (N : ℝ)+2≤v) (hy : 54≤y) (hL : v/2≤L)
    (hM : 0≤M) (hUmass : (∑ p ∈ U,(p : ℝ)⁻¹)≤M)
    (hUlog : ∀ p ∈ U,log p≤4*H)
    (hS : ∀ k ∈ I,∀ a ∈ S k,Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors ⊆ U)
    (hP : ∀ k ∈ I,∀ a ∈ S k,H≤v-Real.pi/y-log a)
    (howner : ∀ k ∈ I,∀ a ∈ S k,∀ q ∈ a.primeFactors,log q≤v-Real.pi/y-log a)
    (hD : ∀ n ∈ D,Squarefree n ∧ 3≤n.primeFactors.card ∧
      (v-1/16<log n ∧ log n≤v+1/16) ∧
      (∃ q ∈ (n/largestPrime n).primeFactors,H≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors ⊆ U)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0) :
    -(2017*exp (2*M)/H)*(amplitude N v/v)≤
      (∑ k ∈ I,∑ a ∈ S k,∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e ∅ L y N (p*a))+
      (∑ n ∈ D\P,signedPart 1 ∅ L y N n)+
      (∑ n ∈ D\Q₀,signedPart (-1) ∅ L y N n) := by
  have hv : 0<v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hmain := broad_all_counts_floor I N e S U hI he (by linarith) hNv hy hL
    hM hUmass hUlog hS hP howner hpeak hsign
  have hnorm := broad_clipped_all_counts_norm_bound ∅ D U y N hH hv
    (by linarith) hL hM hUmass hUlog hD
  have hparts := ZetaRieszOwnerTieFloor.missed_parts_floor ∅ D P Q₀ L y N
  have hh := add_le_add hmain ((neg_le_neg hnorm).trans hparts)
  convert! hh using 1 <;> ring

/-- The leading-one reciprocal-prime mass pays the signed main and its
literal clipped boundary in one quadratic price. No counts, divisor
incidences or phase periods have been normed independently. -/
theorem broad_interval_with_boundary_floor (I : Finset ℕ) (N : ℕ) (e : ℝ)
    (S : ℕ → Finset ℕ) (D P Q : Finset ℕ) {v y L a H : ℝ}
    (ha : 5000≤a) (haH : a≤H) (hH : 10000≤H)
    (hI : ∀ k ∈ I,2≤k) (he : |e|=1) (hNv : (N : ℝ)+2≤v) (hy : 54≤y) (hL : v/2≤L)
    (hS : ∀ k ∈ I,∀ b ∈ S k,Squarefree b ∧ b.primeFactors.card=k ∧
      b.primeFactors ⊆ logPrimes a (4*H-a))
    (hP : ∀ k ∈ I,∀ b ∈ S k,H≤v-Real.pi/y-log b)
    (howner : ∀ k ∈ I,∀ b ∈ S k,∀ q ∈ b.primeFactors,log q≤v-Real.pi/y-log b)
    (hD : ∀ n ∈ D,Squarefree n ∧ 3≤n.primeFactors.card ∧
      (v-1/16<log n ∧ log n≤v+1/16) ∧
      (∃ q ∈ (n/largestPrime n).primeFactors,H≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors ⊆ logPrimes a (4*H-a))
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v)≤0) :
    -(64544*H/a^2)*(amplitude N v/v)≤
      (∑ k ∈ I,∑ b ∈ S k,∑ p ∈ logPrimes (v-Real.pi/y-log b) (2*Real.pi/y),
        signedPart e ∅ L y N (p*b))+
      (∑ n ∈ D\P,signedPart 1 ∅ L y N n)+
      (∑ n ∈ D\Q,signedPart (-1) ∅ L y N n) := by
  have ha0 : 0<a := by linarith
  have hH0 : 0<H := ha0.trans_le haH
  have hM : 0≤log (4*H/a)+1/a := add_nonneg
    (log_nonneg ((one_le_div ha0).mpr (by linarith))) (by positivity)
  have hh := broad_signed_period_with_boundary_floor I N e S D P Q (logPrimes a (4*H-a))
    hI he hH hNv hy hL hM (logPrimes_mass_le ha (by linarith : a≤4*H))
    (fun p hp => by have := (logPrimes_bounds hp).2.2; linarith)
    hS hP howner hD hpeak hsign
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (interval_count_exponential_le ha haH)
      (by norm_num : (0 : ℝ)≤2017)) hH0.le
  have hid : (2017*(32*H^2/a^2))/H=64544*H/a^2 := by field_simp; ring
  rw [hid] at hc
  have hv0 : 0<v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hp := neg_le_neg (mul_le_mul_of_nonneg_right hc
    (div_nonneg (amplitude_nonneg N hv0.le) hv0.le))
  simpa only [neg_mul] using hp.trans (by simpa only [neg_mul] using hh)

/-- A literal start-of-period ownership failure supplies the boundary
witness above the SAME owner-log scale. Its location is retained, not
lost by replacing the witness with an anonymous close-owner predicate. -/
theorem actual_clipped_witness {n : ℕ} (hs : Squarefree n)
    (hc : 3≤n.primeFactors.card) {v y H : ℝ} (hy : 54≤y)
    (hT : v-Real.pi/y<log n ∧ log n≤v+Real.pi/y)
    (hH : H≤v-Real.pi/y-log (n/largestPrime n : ℕ))
    (hclip : ∃ q ∈ (n/largestPrime n).primeFactors,
      v-Real.pi/y-log (n/largestPrime n : ℕ)<log q) :
    ∃ q ∈ (n/largestPrime n).primeFactors,H≤log q ∧ log (largestPrime n)-log q≤1/8 := by
  have hd := canonical_owner_data hs hc
  have hlog : log n=log (largestPrime n)+log (n/largestPrime n : ℕ) := by
    conv_lhs => rw [← hd.2.1,Nat.cast_mul,log_mul
      (by exact_mod_cast hd.1.ne_zero) (by exact_mod_cast hd.2.2.1.ne_zero)]
  have hy0 : 0<y := by linarith
  have hπ : Real.pi/y≤1/16 := (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  obtain ⟨q,hq,hqlog⟩ := hclip
  exact ⟨q,hq,hH.trans hqlog.le,by linarith only [hT.2,hlog,hqlog,hπ]⟩

/-- Summing every owner-log scale costs at most twice the maximum
scale, not the number of scales. This complements the inverse-square
signed-period cancellation rather than a positive carrier majorant. -/
theorem sum_dyadic_owner_logs_le (J : Finset ℕ) {H v : ℝ}
    (hH : 0≤H) (hv : 0≤v) (hJ : ∀ j ∈ J,H*(2 : ℝ)^j≤v) :
    (∑ j ∈ J,H*(2 : ℝ)^j)≤2*v := by
  by_cases hne : J.Nonempty
  · let m := J.max' hne
    have hm : m ∈ J := Finset.max'_mem J hne
    have hsub : J ⊆ Finset.range (m+1) := by
      intro j hj
      exact Finset.mem_range.mpr (by have := Finset.le_max' J j hj; dsimp [m]; omega)
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun j _ _ => by positivity : ∀ j ∈ Finset.range (m+1),j ∉ J →0≤H*(2 : ℝ)^j)
    calc
      _ ≤ ∑ j ∈ Finset.range (m+1),H*(2 : ℝ)^j := hs
      _ = H*((2 : ℝ)^(m+1)-1) := by
        rw [← Finset.mul_sum,geom_sum_eq (by norm_num : (2 : ℝ)≠1)]
        norm_num
      _ ≤ 2*(H*(2 : ℝ)^m) := by rw [pow_succ]; nlinarith only [hH]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hJ m hm) (by norm_num)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
    positivity

/-- One joined signed estimate across all counts, arbitrary cofactor
prime spreads, EVERY selected dyadic owner scale and EVERY radial period.
The lower cofactor-prime cutoff and all whole-fibre/mask conditions remain
explicit. It is a relative supply payment, not the independent -79/1000 floor. -/
theorem broad_radial_supply_floor (V : Finset ℕ) (J : ℕ → Finset ℕ)
    (I : ℕ → ℕ → Finset ℕ) (N : ℕ) (e v : ℕ → ℝ)
    (S : ℕ → ℕ → ℕ → Finset ℕ) (D P Q : ℕ → ℕ → Finset ℕ)
    {y L a H : ℝ} (ha : 5000≤a) (haH : a≤H) (hH : 10000≤H) (hy : 54≤y)
    (hJ : ∀ i ∈ V,∀ j ∈ J i,H*(2 : ℝ)^j≤v i)
    (hI : ∀ i ∈ V,∀ j ∈ J i,∀ k ∈ I i j,2≤k)
    (he : ∀ i ∈ V,|e i|=1) (hNv : ∀ i ∈ V,(N : ℝ)+2≤v i)
    (hL : ∀ i ∈ V,v i/2≤L)
    (hS : ∀ i ∈ V,∀ j ∈ J i,∀ k ∈ I i j,∀ b ∈ S i j k,
      Squarefree b ∧ b.primeFactors.card=k ∧
      b.primeFactors ⊆ logPrimes a (4*(H*(2 : ℝ)^j)-a))
    (hP : ∀ i ∈ V,∀ j ∈ J i,∀ k ∈ I i j,∀ b ∈ S i j k,
      H*(2 : ℝ)^j≤v i-Real.pi/y-log b)
    (howner : ∀ i ∈ V,∀ j ∈ J i,∀ k ∈ I i j,∀ b ∈ S i j k,
      ∀ q ∈ b.primeFactors,log q≤v i-Real.pi/y-log b)
    (hD : ∀ i ∈ V,∀ j ∈ J i,∀ n ∈ D i j,Squarefree n ∧ 3≤n.primeFactors.card ∧
      (v i-1/16<log n ∧ log n≤v i+1/16) ∧
      (∃ q ∈ (n/largestPrime n).primeFactors,H*(2 : ℝ)^j≤log q ∧ log (largestPrime n)-log q≤1/8) ∧
      (n/largestPrime n).primeFactors ⊆ logPrimes a (4*(H*(2 : ℝ)^j)-a))
    (hpeak : ∀ i ∈ V,sin (y*v i)=0) (hsign : ∀ i ∈ V,e i*cos (y*v i)≤0) :
    -(129088/a^2)*(∑ i ∈ V,amplitude N (v i))≤
      ∑ i ∈ V,∑ j ∈ J i,
        ((∑ k ∈ I i j,∑ b ∈ S i j k,
          ∑ p ∈ logPrimes (v i-Real.pi/y-log b) (2*Real.pi/y),
            signedPart (e i) ∅ L y N (p*b))+
          (∑ n ∈ D i j\P i j,signedPart 1 ∅ L y N n)+
          (∑ n ∈ D i j\Q i j,signedPart (-1) ∅ L y N n)) := by
  have ha0 : 0<a := by linarith
  have hH0 : 0<H := by linarith
  have hrow i (hi : i ∈ V) := Finset.sum_le_sum (fun j (hj : j ∈ J i) =>
    broad_interval_with_boundary_floor (I i j) N (e i) (S i j) (D i j) (P i j) (Q i j)
      ha (haH.trans (by
        nlinarith only [hH0,one_le_pow₀ (by norm_num : (1 : ℝ)≤2) (n := j)] : H≤H*(2 : ℝ)^j))
      (hH.trans (by
        nlinarith only [hH0,one_le_pow₀ (by norm_num : (1 : ℝ)≤2) (n := j)] : H≤H*(2 : ℝ)^j))
      (hI i hi j hj) (he i hi) (hNv i hi) hy (hL i hi)
      (hS i hi j hj) (hP i hi j hj) (howner i hi j hj) (hD i hi j hj)
      (hpeak i hi) (hsign i hi))
  have hpaid i (hi : i ∈ V) :
      -((129088/a^2)*amplitude N (v i))≤
        ∑ j ∈ J i,
          ((∑ k ∈ I i j,∑ b ∈ S i j k,
            ∑ p ∈ logPrimes (v i-Real.pi/y-log b) (2*Real.pi/y),
              signedPart (e i) ∅ L y N (p*b))+
            (∑ n ∈ D i j\P i j,signedPart 1 ∅ L y N n)+
            (∑ n ∈ D i j\Q i j,signedPart (-1) ∅ L y N n)) := by
    have hv : 0<v i := by linarith only [hNv i hi,Nat.cast_nonneg (α := ℝ) N]
    have hc := mul_le_mul_of_nonneg_left (sum_dyadic_owner_logs_le (J i) hH0.le hv.le (hJ i hi))
      (by positivity : 0≤64544/a^2)
    have hs := mul_le_mul_of_nonneg_right hc
      (div_nonneg (amplitude_nonneg N hv.le) hv.le)
    have hid : ((64544/a^2)*(2*v i))*(amplitude N (v i)/(v i))=
        (129088/a^2)*amplitude N (v i) := by field_simp; ring
    rw [hid] at hs
    have hh := hrow i hi
    simp only [neg_mul] at hh
    rw [Finset.sum_neg_distrib,← Finset.sum_mul] at hh
    have hid' : (∑ j ∈ J i,64544*(H*(2 : ℝ)^j)/a^2)=
        (64544/a^2)*(∑ j ∈ J i,H*(2 : ℝ)^j) := by rw [Finset.mul_sum]; ring
    rw [hid'] at hh
    exact (neg_le_neg hs).trans hh
  have hh := Finset.sum_le_sum hpaid
  simpa only [neg_mul,Finset.sum_neg_distrib,← Finset.mul_sum] using hh

/-- At the logarithmic roughness threshold the one joined all-geometry
price tends to zero against the SAME positive factorial supply. -/
theorem tendsto_broad_radial_price :
    Tendsto (fun N : ℕ =>129088/(log ((N : ℝ)+1))^2) atTop (𝓝 0) := by
  have hl := Real.tendsto_log_atTop.comp
    (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hi := tendsto_inv_atTop_zero.comp hl
  have hh := (tendsto_const_nhds (x := (129088 : ℝ))).mul (hi.pow 2)
  simpa only [Function.comp_def,inv_pow,div_eq_mul_inv,zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero] using hh

/-- Standalone payment in the `amplitude/v` supply units, with original
phase grids and scale condition explicit. `broad_radial_supply_floor`
instead uses `amplitude`; composing these two theorems requires an extra
radial factor. This theorem alone does NOT pay that all-radial main.
Any eventual compatible payment must replace, not duplicate, its credit. -/
theorem eventually_broad_radial_cost_paid {c κ h y v : ℝ}
    (hc : 0 < c) (hy : 54 ≤ y) (hhu : h ≤ 1/20)
    (hκ : κ = c/(512*((⌊2*y⌋₊ : ℝ)+1)*exp 2)) :
    ∀ᶠ N : ℕ in atTop, ∀ (w : ℕ → ℝ) (f : ℕ → ℂ) (V : Finset ℕ)
      (I J : ℕ → Finset ℕ),
      (∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2) →
      (∀ M ∈ radialIndices N,
        c*(M : ℝ)*exp (2*(M : ℝ))/((M : ℝ)+1)*
          ZetaRieszRadialCompensation.radialEnvelope N M ≤
            (∑ n ∈ supply M h (w M), f n).re) →
      V ⊆ radialIndices N →
      (∀ M ∈ V, ∀ i ∈ I M, 2*(M : ℝ) ≤ center v y i ∧
        center v y i < 2*M+2) →
      (∀ M ∈ V, ∀ i ∈ J M,
        2*(M : ℝ) ≤ center (v+Real.pi/y) y i ∧
        center (v+Real.pi/y) y i < 2*M+2) →
      (129088/(log ((N : ℝ)+1))^2)*
        ((∑ i ∈ V.biUnion I, exp (-center v y i/2)*(center v y i)^N/N.factorial)+
          (∑ i ∈ V.biUnion J, exp (-center (v+Real.pi/y) y i/2)*
            (center (v+Real.pi/y) y i)^N/N.factorial)) ≤
        (1/256 : ℝ)*(∑ n ∈ radialSupply N h w, f n).re := by
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hsmall := tendsto_broad_radial_price.eventually
    (gt_mem_nhds (by linarith : (0 : ℝ) < κ/2))
  filter_upwards [hsmall,eventually_ge_atTop (1 : ℕ)]
    with N hprice hN w f V I J hw hscale hV hI hJ
  have hp := ZetaRieszRoughFiveJoinedFloor.period_grids_cost_paid
    hN hc hy hhu hκ w f V I J hw hscale hV hI hJ
  let U : ℝ :=
      (∑ i ∈ V.biUnion I, exp (-center v y i/2)*(center v y i)^N/N.factorial)+
      (∑ i ∈ V.biUnion J, exp (-center (v+Real.pi/y) y i/2)*
        (center (v+Real.pi/y) y i)^N/N.factorial)
  have hnonneg : 0 ≤ U := by
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro i hi
      obtain ⟨M,hM,hii⟩ := Finset.mem_biUnion.mp hi
      have hcenter : 0 ≤ center v y i :=
        (show (0 : ℝ) ≤ 2*(M : ℝ) by positivity).trans (hI M hM i hii).1
      positivity
    · apply Finset.sum_nonneg
      intro i hi
      obtain ⟨M,hM,hii⟩ := Finset.mem_biUnion.mp hi
      have hcenter : 0 ≤ center (v+Real.pi/y) y i :=
        (show (0 : ℝ) ≤ 2*(M : ℝ) by positivity).trans (hJ M hM i hii).1
      positivity
  change κ*U ≤ (1/128 : ℝ)*(∑ n ∈ radialSupply N h w, f n).re at hp
  change (129088/(log ((N : ℝ)+1))^2)*U ≤ _
  calc
    _ ≤ (κ/2)*U := mul_le_mul_of_nonneg_right hprice.le hnonneg
    _ = (1/2 : ℝ)*(κ*U) := by ring
    _ ≤ (1/2 : ℝ)*((1/128 : ℝ)*(∑ n ∈ radialSupply N h w, f n).re) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by ring

end RiemannGaussian.ZetaRieszBroadOwnerPeriodFloor
