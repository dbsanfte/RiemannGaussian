/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCofactorMass
import RiemannGaussian.ZetaRieszSaddleBand

/-! # Signed largest-prime cancellation at every fixed cofactor count

The same finite-prime inequality applies to all fixed counts. The original
factorial kernel, allocation, phase and moving Riesz cutoff remain coupled.
The constants depend on the count; no uniform growing-count assertion is made.
-/
namespace RiemannGaussian.ZetaRieszFixedCountPeriod
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszMacroPrimeWindows
open ZetaSquarefreeRieszWindows ZetaRieszTriplePrime

/-- A count-indexed selection of literal cofactors with unique prime ownership.
There is no least-prime cutoff or coefficient-sign restriction. -/
def cofactors (k : ℕ) (v : ℝ) : Finset ℕ :=
  (ZetaRieszCofactorMass.products k v).filter (fun a =>
    Squarefree a ∧ a.primeFactors.card = k ∧ (203/500 : ℝ)*v < Real.log a ∧
    Real.log a ≤ (197/200 : ℝ)*v ∧
    ∀ p ∈ a.primeFactors, Real.log p ≤ v-1/16-Real.log a)

/-- Each actual integer is counted once through its unique largest prime. -/
def population (k : ℕ) (v y : ℝ) : Finset ℕ := (cofactors k v).biUnion (fun a =>
  (logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)).image (fun p => a*p))

/-- Geometry and exact prime count of every selected cofactor. -/
theorem cofactor_data {k : ℕ} {v : ℝ} {a : ℕ} (ha : a ∈ cofactors k v) :
    Squarefree a ∧ a.primeFactors.card = k ∧ Real.log a.minFac ≤ v ∧
      (203/500 : ℝ)*v < Real.log a ∧ Real.log a ≤ (197/200 : ℝ)*v ∧
      (∀ p ∈ a.primeFactors, Real.log p ≤ v-1/16-Real.log a) := by
  obtain ⟨_,hs,hc,hl,hu,hm⟩ := Finset.mem_filter.mp ha
  have hv : 0 ≤ v := by nlinarith [Real.log_natCast_nonneg a]
  have hmin : Real.log a.minFac ≤ Real.log a := Real.log_le_log
    (by exact_mod_cast Nat.minFac_pos a) (by exact_mod_cast Nat.minFac_le (Nat.pos_of_ne_zero hs.ne_zero))
  exact ⟨hs,hc,by linarith,hl,hu,hm⟩

/-- At every selected count, ownership already bounds the cofactor below 54/55 of the radial center. -/
theorem cofactor_cap_of_owner {a k : ℕ} {v : ℝ} (hv : 0 ≤ v)
    (hs : Squarefree a) (hc : a.primeFactors.card = k) (hk : k ≤ 54)
    (ho : ∀ p ∈ a.primeFactors, Real.log p ≤ v-1/16-Real.log a) :
    Real.log a ≤ (54/55 : ℝ)*v := by
  by_cases hne : a.primeFactors.Nonempty
  · obtain ⟨p,hp⟩ := hne
    have hb : 0 ≤ v-1/16-Real.log a :=
      (Real.log_natCast_nonneg p).trans (ho p hp)
    have hsum := Finset.sum_le_sum ho
    rw [Finset.sum_const,nsmul_eq_mul,hc,
      ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hs] at hsum
    have hkR : (k : ℝ) ≤ 54 := by exact_mod_cast hk
    have h := mul_le_mul_of_nonneg_right hkR hb
    nlinarith only [hsum,h]
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    have hlog := CoprimeEulerPhase.squarefree_log_eq_prime_sum hs
    rw [he,Finset.sum_empty] at hlog
    rw [hlog]
    positivity

/-- Through cofactor count fifty-four, the numerical upper cap is redundant.
All squarefree cofactors satisfying the retained lower share and ownership
conditions are included in the literal signed payment. -/
theorem mem_cofactors_iff_of_count_le {k a : ℕ} (hk : k ≤ 54) {v : ℝ} (hv : 0 ≤ v) :
    a ∈ cofactors k v ↔ Squarefree a ∧ a.primeFactors.card = k ∧
      (203/500 : ℝ)*v < Real.log a ∧
      (∀ p ∈ a.primeFactors, Real.log p ≤ v-1/16-Real.log a) := by
  constructor
  · intro ha
    have hd := cofactor_data ha
    exact ⟨hd.1,hd.2.1,hd.2.2.2.1,hd.2.2.2.2.2⟩
  · rintro ⟨hs,hc,hl,ho⟩
    have hcap := cofactor_cap_of_owner hv hs hc hk ho
    apply Finset.mem_filter.mpr
    refine ⟨ZetaRieszCofactorMass.mem_products_of_squarefree hs hc ?_,hs,hc,hl,by linarith,ho⟩
    intro p hp
    have h := ho p hp
    linarith [Real.log_natCast_nonneg a]

/-- The selected integers of any fixed prime count have unique largest-prime ownership,
all original radial bounds, and prime shares below the separately paid owner band. -/
theorem fibre_geometry {k : ℕ} {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    {a p : ℕ} (ha : a ∈ cofactors k v)
    (hp : p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)) :
    p.Prime ∧ (∀ q ∈ a.primeFactors, q < p) ∧ Squarefree (p*a) ∧
      (p*a).primeFactors.card = k+1 ∧
      v-Real.pi/|y| < Real.log (p*a : ℕ) ∧ Real.log (p*a : ℕ) ≤ v+Real.pi/|y| ∧
      (∀ q ∈ (p*a).primeFactors, Real.log q ≤ (1189/2000 : ℝ)*Real.log (p*a : ℕ)) := by
  obtain ⟨hs,hc,hr,hal,hau,ham⟩ := cofactor_data ha
  have hb := logPrimes_bounds hp
  have hπ : 0 < Real.pi/|y| := div_pos Real.pi_pos (by linarith)
  have hπu : Real.pi/|y| ≤ 1/16 :=
    (div_le_iff₀ (by linarith : 0 < |y|)).mpr (by nlinarith [Real.pi_lt_d4])
  have hl : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hb.1.ne_zero) (by exact_mod_cast hs.ne_zero)]
  have hbu := hb.2.2
  rw [mul_div_assoc] at hbu
  have howner (q : ℕ) (hq : q ∈ a.primeFactors) : q < p := by
    exact_mod_cast (Real.log_lt_log_iff
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos : (0 : ℝ) < q)
      (by exact_mod_cast hb.1.pos : (0 : ℝ) < p)).mp (by linarith [ham q hq,hb.2.1])
  have hpd : ¬p ∣ a := by
    intro hd
    exact (howner p (hb.1.mem_primeFactors hd hs.ne_zero)).false
  have hsf := Nat.squarefree_mul_iff.mpr ⟨hb.1.coprime_iff_not_dvd.mpr hpd,hb.1.squarefree,hs⟩
  have hpf : (p*a).primeFactors = insert p a.primeFactors := by
    rw [Nat.primeFactors_mul hb.1.ne_zero hs.ne_zero,hb.1.primeFactors,Finset.singleton_union]
  have hpm : p ∉ a.primeFactors := fun h => hpd (Nat.dvd_of_mem_primeFactors h)
  have hpmax : Real.log p ≤ (1189/2000 : ℝ)*Real.log (p*a : ℕ) := by
    rw [hl]; linarith
  refine ⟨hb.1,howner,hsf,by rw [hpf,Finset.card_insert_of_notMem hpm,hc],
    by rw [hl]; linarith [hb.2.1],by rw [hl]; linarith,?_⟩
  intro q hq
  rw [hpf] at hq
  rcases Finset.mem_insert.mp hq with rfl | hq
  · exact hpmax
  · exact (Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos)
      (by exact_mod_cast (howner q hq).le)).trans hpmax

/-- The exact reflected response retains the unsaturated second cutoff.
Only its first cutoff changes along a largest-prime phase period. -/
def response (L T : ℝ) (a : ℕ) : ℝ :=
  VaughanLogAverage.riesz (T-L) a-VaughanLogAverage.riesz (Real.log a-L) a

/-- The previously proved saturated formula is recovered exactly when
its cofactor lies below the Riesz cutoff. -/
theorem response_eq_of_saturated {a : ℕ} {L : ℝ} (hL : Real.log a ≤ L) (T : ℝ) :
    response L T a = VaughanLogAverage.riesz (T-L) a := by
  rw [response,ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos (sub_nonpos.mpr hL),sub_zero]

/-- The exact reflected coefficient keeps the count parity explicitly. -/
theorem coefficient_eq_response {k : ℕ} (hk : 2 ≤ k) {v y L : ℝ}
    (hv : 100 ≤ v) (hy : 54 ≤ |y|) (_hLl : (67/100 : ℝ)*v ≤ L)
    {a p : ℕ} (ha : a ∈ cofactors k v)
    (hp : p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)) :
    SquarefreeVaughanLogSource.coefficient L (p*a) =
      (((-1 : ℝ)^(k+1)*(-(Real.log (p*a : ℕ)/L)*
        response L (Real.log (p*a : ℕ)) a) : ℝ) : ℂ) := by
  obtain ⟨hpp,howner,hs,hc,_,_,_⟩ := fibre_geometry hv hy ha hp
  have hd := cofactor_data ha
  have hpd : ¬p ∣ a := by
    intro h
    exact (howner p (hpp.mem_primeFactors h hd.1.ne_zero)).false
  have hn1 : p*a ≠ 1 := by intro h; simp [h] at hc
  have hnp : ¬(p*a).Prime := by intro h; simp [h.primeFactors] at hc; omega
  have hl : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hpp.ne_zero) (by exact_mod_cast hd.1.ne_zero)]
  have href := VaughanLogAverage.riesz_reflection (Real.log (p*a : ℕ)-L) hs hn1 hnp
  rw [sub_sub_cancel,ZetaRieszReflectedLinear.moebius_eq_primeCount hs,hc,
    Int.cast_pow,Int.cast_neg,Int.cast_one,
    riesz_prime_mul (Real.log (p*a : ℕ)-L) hpp hpd] at href
  rw [show Real.log (p*a : ℕ)-L-Real.log p = Real.log a-L by rw [hl]; ring] at href
  rw [SquarefreeVaughanLogSource.coefficient,if_pos ⟨hs,hnp⟩,href]
  congr 1
  dsimp only [response]
  ring

/-- A finite count-dependent constant for the full signed Riesz response. -/
def responseConstant (k : ℕ) : ℝ :=
  2*(1+ZetaRieszSignedSperner.parityCapacity (k-2) 0+
    ZetaRieszSignedSperner.parityCapacity (k-2) 1)

/-- Positivity of the explicit response constant. -/
theorem responseConstant_pos (k : ℕ) : 0 < responseConstant k := by
  unfold responseConstant
  positivity

private theorem cofactor_kernel_bound {k : ℕ} (hk : 2 ≤ k) {v : ℝ} {a : ℕ}
    (ha : a ∈ cofactors k v) (D : ℝ) :
    |VaughanLogAverage.riesz D a| ≤
      (1+ZetaRieszSignedSperner.parityCapacity (k-2) 0+
        ZetaRieszSignedSperner.parityCapacity (k-2) 1)*Real.log a.minFac := by
  have hd := cofactor_data ha
  have hh := ZetaRieszSignedSperner.riesz_bounds_minFac D hd.1 (by omega)
  rw [hd.2.1] at hh
  have h0 : (0 : ℝ) ≤ ZetaRieszSignedSperner.parityCapacity (k-2) 0 := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ ZetaRieszSignedSperner.parityCapacity (k-2) 1 := Nat.cast_nonneg _
  have hr := Real.log_natCast_nonneg a.minFac
  apply abs_le.mpr
  constructor <;> nlinarith only [hh.1,hh.2,hr,mul_nonneg h0 hr,mul_nonneg h1 hr]

/-- Both retained cutoffs cost at most twice the same least-prime bound.
No saturation or coefficient-sign assumption is used. -/
theorem cofactor_response_bound {k : ℕ} (hk : 2 ≤ k) {v : ℝ} {a : ℕ}
    (ha : a ∈ cofactors k v) (L T : ℝ) :
    |response L T a| ≤ responseConstant k*Real.log a.minFac := by
  have ht : |VaughanLogAverage.riesz (T-L) a-VaughanLogAverage.riesz (Real.log a-L) a| ≤
      |VaughanLogAverage.riesz (T-L) a|+|VaughanLogAverage.riesz (Real.log a-L) a| := by
    simpa only [sub_eq_add_neg,abs_neg] using
      abs_add_le (VaughanLogAverage.riesz (T-L) a) (-VaughanLogAverage.riesz (Real.log a-L) a)
  have h := ht.trans (add_le_add (cofactor_kernel_bound hk ha (T-L))
      (cofactor_kernel_bound hk ha (Real.log a-L)))
  convert h using 1 <;> first | rfl | (dsimp only [responseConstant]; ring)

/-- The unsaturated correction is constant on the prime fibre, so it adds
no cutoff-variation cost at all. -/
theorem cofactor_response_variation {k : ℕ} (hk : 2 ≤ k) {v : ℝ} {a : ℕ}
    (ha : a ∈ cofactors k v) (L D E : ℝ) :
    |response L D a-response L E a| ≤ (2 : ℝ)^k*|D-E| := by
  have hd := cofactor_data ha
  have hh := ZetaRieszTentSlope.riesz_cutoff_lipschitz_quarter (D-L) (E-L) hd.1 (by omega)
  rw [ZetaRieszTentSlope.absolute_divisor_mass_eq_card hd.1,
    ZetaRieszSmoothHead.card_divisors_of_squarefree hd.1,hd.2.1,Nat.cast_pow,Nat.cast_ofNat] at hh
  simp only [sub_sub_sub_cancel_right] at hh
  simp only [response,sub_sub_sub_cancel_right]
  nlinarith [mul_nonneg (show 0 ≤ (2 : ℝ)^k by positivity) (abs_nonneg (D-E))]

/-- The whole largest-prime period is summed before any absolute value. -/
theorem sum_population {k : ℕ} {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|) (f : ℕ → ℂ) :
    (∑ n ∈ population k v y, f n) = ∑ a ∈ cofactors k v,
      ∑ p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|), f (p*a) := by
  rw [population,ZetaRieszCoupledWindow.sum_owned_products _ _ f
    (fun a ha => (cofactor_data ha).1.ne_zero) (by
      intro a ha p hp
      have hg := fibre_geometry hv hy ha hp
      exact ⟨hg.1,fun q hq hd => hg.2.1 q
        (hq.mem_primeFactors hd (cofactor_data ha).1.ne_zero)⟩)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro p _
  rw [Nat.mul_comm]

theorem re_response_atom {k : ℕ} (hk : 2 ≤ k) {v y L : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (hLl : (67/100 : ℝ)*v ≤ L)
    {a p : ℕ} (ha : a ∈ cofactors k v)
    (hp : p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)) (N : ℕ) :
    (SquarefreeVaughanLogSource.coefficient L (p*a)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re =
      (-1 : ℝ)^(k+1)*(-(response L (Real.log p+Real.log a) a/L/a)*
        ((Real.exp (-(Real.log p+Real.log a)/2)*(Real.log p+Real.log a)^(N+1)/N.factorial)*
          (p : ℝ)⁻¹*Real.cos (y*(Real.log p+Real.log a)))) := by
  have hpp := (logPrimes_bounds hp).1
  have ha0 := (cofactor_data ha).1.ne_zero
  have hlog : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hpp.ne_zero) (by exact_mod_cast ha0)]
  have hex : Real.exp (-(3/2 : ℝ)*Real.log (p*a : ℕ)) =
      Real.exp (-Real.log (p*a : ℕ)/2)*(p : ℝ)⁻¹*(a : ℝ)⁻¹ := by
    rw [show -(3/2 : ℝ)*Real.log (p*a : ℕ) =
      -Real.log (p*a : ℕ)/2-Real.log (p*a : ℕ) by ring,
      Real.exp_sub,Real.exp_log (by exact_mod_cast Nat.mul_pos hpp.pos (Nat.pos_of_ne_zero ha0)),
      Nat.cast_mul]
    ring
  rw [← ZetaRieszJointAllocation.filter_one_eq,ZetaRieszCosineCarrier.re_coefficient_filter_one,
    coefficient_eq_response hk hv hy hLl ha hp,Complex.ofReal_re,hex,hlog,pow_succ]
  ring



private theorem signed_perturbation (D : Finset ℕ) (R g w : ℕ → ℝ) (R₀ E : ℝ)
    (hE : 0 ≤ E) (_hw : ∀ p ∈ D, 0 ≤ w p)
    (hg : ∀ p ∈ D, |g p| ≤ w p) (hR : ∀ p ∈ D, |R p-R₀| ≤ E) :
    |∑ p ∈ D, R p*g p| ≤ |R₀| * |∑ p ∈ D, g p|+E*(∑ p ∈ D, w p) := by
  have he : (∑ p ∈ D, R p*g p) = R₀*(∑ p ∈ D, g p)+∑ p ∈ D, (R p-R₀)*g p := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  apply add_le_add_right
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun p hp => by
    rw [abs_mul]
    exact mul_le_mul (hR p hp) (hg p hp) (abs_nonneg _) hE)

/-- The changing coefficient is paid only after summing the last-prime
phase. The charges retain its central signed mass, cutoff variation, and exact
allocation variation before bounding the remaining prime sum. -/
theorem fibre_bound {k : ℕ} (hk : 2 ≤ k) (A : Finset ℕ) {m N : ℕ} {v y L V η : ℝ}
    (hv : 100 ≤ v) (hy : 54 ≤ |y|) (hLl : (67/100 : ℝ)*v ≤ L)
    (hV : 0 ≤ V) (hη : 0 ≤ η) {a : ℕ} (ha : a ∈ cofactors k v)
    (hA : ∀ p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|), p ∈ A)
    (hperiod :
      let w := fun p : ℕ => Real.exp (-(Real.log p+Real.log a)/2)*
        (Real.log p+Real.log a)^(N+1)/N.factorial
      let D := logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)
      |∑ p ∈ D, w p*(p : ℝ)⁻¹*Real.cos (y*(Real.log p+Real.log a))| ≤
        (64*η)*m*V*v*(Real.pi/(4*m*|y|))/(v-Real.log a) ∧
      (∑ p ∈ D, w p*(p : ℝ)⁻¹) ≤
        16*m*V*v*(Real.pi/(4*m*|y|))/(v-Real.log a)) :
    |(∑ p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|),
        ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re| ≤
      ((m : ℝ)*V*(Real.pi/(4*m*|y|)))*
        ((10000*responseConstant k*η/v+5000*((k : ℝ)+1)*responseConstant k*Real.sqrt (N+1)/v^2)*(Real.log a.minFac*(a : ℝ)⁻¹)+(2000*(2 : ℝ)^k/v)*(a : ℝ)⁻¹) := by
  let h := Real.pi/(4*m*|y|)
  let D := logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)
  let w := fun p : ℕ => (Real.exp (-(Real.log p+Real.log a)/2)*
    (Real.log p+Real.log a)^(N+1)/N.factorial)*(p : ℝ)⁻¹
  let g := fun p : ℕ => w p*Real.cos (y*(Real.log p+Real.log a))
  have hB0 := (responseConstant_pos k).le
  by_cases hDn : D.Nonempty
  swap
  · have he : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hDn
    change |(∑ p ∈ D, ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re| ≤ _
    rw [he,Finset.sum_empty,Complex.zero_re,abs_zero]
    positivity
  obtain ⟨p₀,hp₀⟩ := hDn
  let R := fun p : ℕ => (1-ZetaRieszJointAllocation.boundedShare A N (p*a))*
    response L (Real.log p+Real.log a) a
  let R₀ := R p₀
  let E := (2 : ℝ)^k+3*((k : ℝ)+1)*responseConstant k*Real.sqrt (N+1)/v*Real.log a.minFac
  have hd := cofactor_data ha
  have hv0 : 0 < v := by linarith
  have hL : 0 < L := by linarith
  have haR : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero hd.1.ne_zero
  have hab : 0 < v-Real.log a := by linarith [hd.2.2.2.2.1]
  have hπ : 0 ≤ Real.pi/|y| := by positivity
  have hπu : Real.pi/|y| ≤ 1/16 :=
    (div_le_iff₀ (by linarith : 0 < |y|)).mpr (by nlinarith [Real.pi_lt_d4])
  have hw (p : ℕ) (hp : p ∈ D) : 0 ≤ w p := by
    have hb := (logPrimes_bounds hp).2
    have ht : 0 ≤ Real.log p+Real.log a := by linarith [hb.1]
    dsimp [w]; positivity
  have hg (p : ℕ) (hp : p ∈ D) : |g p| ≤ w p := by
    dsimp only [g]
    rw [abs_mul,abs_of_nonneg (hw p hp)]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (hw p hp)).trans_eq (mul_one _)
  have hgeo (p : ℕ) (hp : p ∈ D) := fibre_geometry hv hy ha hp
  have hlog (p : ℕ) (hp : p ∈ D) : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast (hgeo p hp).1.ne_zero)
      (by exact_mod_cast hd.1.ne_zero)]
  have hnot (p : ℕ) (hp : p ∈ D) : ¬p ∣ a := by
    intro hh
    exact ((hgeo p hp).2.1 p ((hgeo p hp).1.mem_primeFactors hh hd.1.ne_zero)).false
  have hR (p : ℕ) (hp : p ∈ D) : |R p-R₀| ≤ E := by
    have hpT := (hgeo p hp).2.2.2.2
    have hqT := (hgeo p₀ hp₀).2.2.2.2
    have hdif : |Real.log (p*a : ℕ)-Real.log (p₀*a : ℕ)| ≤ 1/8 := by
      apply abs_le.mpr
      constructor <;> linarith [hpT.1,hpT.2.1,hqT.1,hqT.2.1]
    have hs := ZetaRieszAllocationVariation.boundedShare_fibre_variation_985 A N hd.1 (by omega)
      (hgeo p hp).1 (hnot p hp) (hA p hp) (hgeo p₀ hp₀).1 (hnot p₀ hp₀) (hA p₀ hp₀)
      hv hπ hπu hd.2.2.2.2.1 ⟨hpT.1.le,hpT.2.1⟩ ⟨hqT.1.le,hqT.2.1⟩
    rw [hd.2.1] at hs
    have hshare : |ZetaRieszJointAllocation.boundedShare A N (p*a)-
        ZetaRieszJointAllocation.boundedShare A N (p₀*a)| ≤ 3*((k : ℝ)+1)*Real.sqrt (N+1)/v := by
      apply hs.trans
      have hh := mul_le_mul_of_nonneg_left hdif
        (show 0 ≤ 20*((k : ℝ)+1)*Real.sqrt (N+1)/v by positivity)
      apply hh.trans
      have hz : 0 ≤ 3*((k : ℝ)+1)*Real.sqrt (N+1)/v := by positivity
      ring_nf at hz ⊢
      linarith only [hz]
    have hvary : |response L (Real.log p+Real.log a) a-
        response L (Real.log p₀+Real.log a) a| ≤ (2 : ℝ)^k := by
      have hh := cofactor_response_variation hk ha L (Real.log p+Real.log a) (Real.log p₀+Real.log a)
      rw [hlog p hp,hlog p₀ hp₀] at hdif
      exact hh.trans ((mul_le_mul_of_nonneg_left
        (hdif.trans (by norm_num : (1/8 : ℝ) ≤ 1))
        (show 0 ≤ (2 : ℝ)^k by positivity)).trans_eq (mul_one _))
    have htheta := ZetaRieszJointAllocation.boundedShare_bounds A N (p*a)
    have hthetaAbs : |1-ZetaRieszJointAllocation.boundedShare A N (p*a)| ≤ 1 :=
      abs_le.mpr (by constructor <;> linarith)
    have he : R p-R₀ = (1-ZetaRieszJointAllocation.boundedShare A N (p*a))*
        (response L (Real.log p+Real.log a) a-
          response L (Real.log p₀+Real.log a) a)+
        (ZetaRieszJointAllocation.boundedShare A N (p₀*a)-
          ZetaRieszJointAllocation.boundedShare A N (p*a))*
          response L (Real.log p₀+Real.log a) a := by dsimp [R,R₀]; ring
    rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul,abs_sub_comm (ZetaRieszJointAllocation.boundedShare A N (p₀*a))]
    have h1 := mul_le_mul hthetaAbs hvary (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have h2 := mul_le_mul hshare (cofactor_response_bound hk ha L (Real.log p₀+Real.log a)) (abs_nonneg _)
      (by positivity : 0 ≤ 3*((k : ℝ)+1)*Real.sqrt (N+1)/v)
    dsimp only [E]
    ring_nf at h1 h2 ⊢
    linarith only [h1,h2]
  have hs := signed_perturbation D R g w R₀ E (by dsimp [E]; positivity) hw hg hR
  have he : (∑ p ∈ D, ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re =
      (-1 : ℝ)^(k+1)*(-(1/L/a)*(∑ p ∈ D, R p*g p)) := by
    rw [Complex.re_sum,Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [ZetaRieszJointAllocation.residualCoefficient,mul_assoc,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [re_response_atom hk hv hy hLl ha hp]
    dsimp [R,g,w]
    ring
  change |(∑ p ∈ D, ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
    zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re| ≤ _
  simp only [he,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    abs_of_nonneg (show 0 ≤ 1/L/a by positivity)]
  have hrc : |R₀| ≤ responseConstant k*Real.log a.minFac := by
    dsimp [R₀,R]
    rw [abs_mul]
    have htheta := ZetaRieszJointAllocation.boundedShare_bounds A N (p₀*a)
    have hthetaAbs : |1-ZetaRieszJointAllocation.boundedShare A N (p₀*a)| ≤ 1 :=
      abs_le.mpr (by constructor <;> linarith)
    simpa only [one_mul] using mul_le_mul hthetaAbs (cofactor_response_bound hk ha L _)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hS : |∑ p ∈ D, R p*g p| ≤
      (responseConstant k*Real.log a.minFac)*((64*η)*m*V*v*h/(v-Real.log a))+
        E*(16*m*V*v*h/(v-Real.log a)) := by
    apply hs.trans
    have hh := mul_le_mul hrc hperiod.1 (abs_nonneg _) (mul_nonneg hB0 (Real.log_natCast_nonneg a.minFac))
    exact add_le_add hh (mul_le_mul_of_nonneg_left hperiod.2 (by dsimp [E]; positivity))
  apply (mul_le_mul_of_nonneg_left hS (show 0 ≤ 1/L/a by positivity)).trans
  have hden : v*v ≤ 100*L*(v-Real.log a) := by
    have hh := mul_le_mul hLl (show (3/200 : ℝ)*v ≤ v-Real.log a by linarith [hd.2.2.2.2.1])
      (by positivity) (by positivity : 0 ≤ L)
    nlinarith
  have hfrac : v/(L*(v-Real.log a)) ≤ 100/v :=
    (div_le_div_iff₀ (mul_pos hL hab) hv0).mpr (by nlinarith only [hden])
  have hnonneg : 0 ≤ (m : ℝ)*V*h*(a : ℝ)⁻¹ := by dsimp [h]; positivity
  have hm := mul_le_mul_of_nonneg_right hfrac
    (show 0 ≤ ((m : ℝ)*V*h*(a : ℝ)⁻¹)*(64*responseConstant k*η*Real.log a.minFac+16*E) by dsimp [E]; positivity)
  have hsmall : (64*responseConstant k*η*Real.log a.minFac+16*E)*100 ≤ (10000*responseConstant k*η+5000*((k : ℝ)+1)*responseConstant k*Real.sqrt (N+1)/v)*Real.log a.minFac+2000*(2 : ℝ)^k := by
    have hz1 := mul_nonneg (mul_nonneg hB0 hη) (Real.log_natCast_nonneg a.minFac)
    have hz2 : 0 ≤ ((k : ℝ)+1)*responseConstant k*Real.sqrt (N+1)/v*Real.log a.minFac := by positivity
    have hz3 : 0 ≤ (2 : ℝ)^k := by positivity
    dsimp only [E]
    ring_nf at hz1 hz2 ⊢
    linarith only [hz1,hz2,hz3]
  have ht := mul_le_mul_of_nonneg_left hsmall (div_nonneg hnonneg hv0.le)
  dsimp only [h,E] at hm ht ⊢
  simp only [div_eq_mul_inv,mul_inv_rev] at hm ht ⊢
  ring_nf at hm ht ⊢
  linarith only [hm,ht]


/-- The entire allocated fixed-count residual has arbitrarily small signed
cost uniformly at every center of the growing saddle band. -/
theorem eventually_residual_small {k : ℕ} (hk : 2 ≤ k) {y ε : ℝ} (hy : 54 ≤ |y|) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (v L : ℝ),
      2*(N : ℝ) ≤ v → v ≤ 2*N+Real.sqrt N → Real.cos (y*v) = -1 →
      (67/100 : ℝ)*v ≤ L →
      (∀ a ∈ cofactors k v, ∀ p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|), p ∈ A) →
      |(∑ n ∈ population k v y, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re| ≤
        ε*(Real.pi/(4*|y|))*(Real.exp (-v/2)*v^N/N.factorial) := by
  have hC := ZetaRieszCofactorMass.constants_pos (show 0 < k by omega)
  have hCl := hC.1
  have hCv := hC.2
  have hB := responseConstant_pos k
  let η := min (1/10000 : ℝ) (ε/(40000*responseConstant k*ZetaRieszCofactorMass.logMassConstant k))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηu : η ≤ 1/100 := (min_le_left _ _).trans (by norm_num)
  have hηε : 10000*responseConstant k*η*ZetaRieszCofactorMass.logMassConstant k ≤ ε/4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 40000*responseConstant k*ZetaRieszCofactorMass.logMassConstant k)).mp (min_le_right _ _ : η ≤ _)
    nlinarith only [hh]
  obtain ⟨m,hm,hsmall,hphase⟩ := ZetaRieszBroadSixPeriod.exists_precise_mesh hy hη
  have hr : Tendsto (fun v : ℝ => (5000*((k : ℝ)+1)*responseConstant k*ZetaRieszCofactorMass.logMassConstant k+2000*(2 : ℝ)^k*ZetaRieszCofactorMass.variationConstant k)*v^(-(1/2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).const_mul
      (5000*((k : ℝ)+1)*responseConstant k*ZetaRieszCofactorMass.logMassConstant k+2000*(2 : ℝ)^k*ZetaRieszCofactorMass.variationConstant k)
  obtain ⟨v₀,hv₀⟩ := eventually_atTop.mp (hr.eventually_lt_const (show 0 < ε/2 by positivity))
  filter_upwards [ZetaRieszSaddleBand.eventually_factorial_period hm hy
      (by norm_num : (0 : ℝ) < 1/100) hη hηu hsmall hphase,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop v₀,
    eventually_ge_atTop (1000 : ℕ)] with N hN hNv hlarge A v L hv hvu hpeak hLl hA
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hv100 : 100 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  have hvlarge : v₀ ≤ v := by linarith
  obtain ⟨V,hV,hbase,_,hperiod⟩ := hN v hv hvu hpeak
  let h := Real.pi/(4*m*|y|)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hy0 : 0 < |y| := by linarith
  have hh : 0 < h := by dsimp [h]; positivity
  have hrow (a : ℕ) (ha : a ∈ cofactors k v) := fibre_bound hk A (N := N) hv100 hy hLl hV.le hη.le ha (hA a ha)
    (hperiod (Real.log a) (by have hd := (cofactor_data ha).2.2.2.2.1; linarith))
  have hsum : |(∑ n ∈ population k v y, ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re| ≤
      ((m : ℝ)*V*h)*((10000*responseConstant k*η/v+5000*((k : ℝ)+1)*responseConstant k*Real.sqrt (N+1)/v^2)*(ZetaRieszCofactorMass.logMassConstant k*v)+
        (2000*(2 : ℝ)^k/v)*(ZetaRieszCofactorMass.variationConstant k*v^(1/2 : ℝ))) := by
    rw [sum_population hv100 hy,Complex.re_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply (Finset.sum_le_sum hrow).trans
    rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (mul_le_mul_of_nonneg_left (ZetaRieszCofactorMass.log_mass (by omega : 0 < k) hv0 (cofactors k v) (Finset.filter_subset _ _)) (by positivity))
      (mul_le_mul_of_nonneg_left (ZetaRieszCofactorMass.reciprocal_mass (by omega : 0 < k) hv0 (cofactors k v) (Finset.filter_subset _ _)) (by positivity))
  have hrat : v^(1/2 : ℝ)/v = v^(-(1/2 : ℝ)) := by
    have hh := Real.rpow_sub hv0 (1/2 : ℝ) 1
    norm_num at hh
    exact hh.symm
  have hroot : Real.sqrt (N+1)/v ≤ v^(-(1/2 : ℝ)) := by
    have hs : Real.sqrt (N+1) ≤ Real.sqrt v := Real.sqrt_le_sqrt (by linarith)
    have hh := div_le_div_of_nonneg_right hs hv0.le
    rw [Real.sqrt_eq_rpow v,hrat] at hh
    exact hh
  have hbudget : (10000*responseConstant k*η/v+5000*((k : ℝ)+1)*responseConstant k*Real.sqrt (N+1)/v^2)*(ZetaRieszCofactorMass.logMassConstant k*v)+
      (2000*(2 : ℝ)^k/v)*(ZetaRieszCofactorMass.variationConstant k*v^(1/2 : ℝ)) ≤ ε := by
    have he : (10000*responseConstant k*η/v+5000*((k : ℝ)+1)*responseConstant k*Real.sqrt (N+1)/v^2)*(ZetaRieszCofactorMass.logMassConstant k*v)+
        (2000*(2 : ℝ)^k/v)*(ZetaRieszCofactorMass.variationConstant k*v^(1/2 : ℝ)) =
        10000*responseConstant k*η*ZetaRieszCofactorMass.logMassConstant k+5000*((k : ℝ)+1)*responseConstant k*ZetaRieszCofactorMass.logMassConstant k*(Real.sqrt (N+1)/v)+
          2000*(2 : ℝ)^k*ZetaRieszCofactorMass.variationConstant k*(v^(1/2 : ℝ)/v) := by field_simp
    rw [he,hrat]
    have hh := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 5000*((k : ℝ)+1)*responseConstant k*ZetaRieszCofactorMass.logMassConstant k by positivity)
    have ht := hv₀ v hvlarge
    ring_nf at hh ht hηε ⊢
    linarith only [hh,ht,hηε,hε]
  apply hsum.trans
  have he : (m : ℝ)*h = Real.pi/(4*|y|) := by dsimp [h]; field_simp
  calc
    _ ≤ ((m : ℝ)*V*h)*ε := mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = ε*(Real.pi/(4*|y|))*V := by rw [← he]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbase (by positivity)
/-- Every moving owner stays in the original intermediate-prime mask. -/
theorem eventually_owner_mem (k : ℕ) {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ |y|) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, 2*(N : ℝ) ≤ v → v ≤ 2*N+Real.sqrt N →
      ∀ a ∈ cofactors k v, ∀ p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|),
        p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N := by
  have hroom : u < Real.exp (-(137/200 : ℝ)) :=
    hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans (Real.exp_lt_exp.mpr (by norm_num)))
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ)/(N : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,pow_one,one_mul,add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hl.eventually_lt_const (by norm_num : (0 : ℝ) < 1/100),
    ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
      (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 137/200) hroom,
    ZetaRieszSaddleBand.eventually_sqrt_add_one_le_mul (by norm_num : (0 : ℝ) < 1/1000),
    eventually_ge_atTop (1000 : ℕ)] with N hlog hL hwide hN v hv hvu a ha p hp
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hgeo := fibre_geometry (by linarith : 100 ≤ v) hy ha hp
  have hd := (cofactor_data ha).2.2.2.2.1
  have hpb := logPrimes_bounds hp
  have hpi : Real.pi/|y| ≤ 1/16 :=
    (div_le_iff₀ (by linarith : 0 < |y|)).mpr (by nlinarith [Real.pi_lt_d4])
  apply (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mpr
  refine ⟨hgeo.1,?_,?_⟩
  · have hlg : 2*Real.log (N : ℝ) < (N : ℝ)/50 := by
      have hh := (div_lt_iff₀ hN0).mp hlog
      linarith only [hh]
    have hh : Real.log ((N^2 : ℕ) : ℝ) < Real.log p := by
      rw [Nat.cast_pow,Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith [hpb.2.1,hd]
    exact_mod_cast (Real.log_lt_log_iff (by positivity : (0 : ℝ) < (N^2 : ℕ))
      (by exact_mod_cast hgeo.1.pos)).mp hh
  · have hpp : p ∈ (p*a).primeFactors := hgeo.1.mem_primeFactors (dvd_mul_right p a) hgeo.2.2.1.ne_zero
    have hm := hgeo.2.2.2.2.2.2 p hpp
    have htop : Real.log p < SquarefreeVaughanLogSource.length u N := by
      nlinarith [hgeo.2.2.2.2.2.1]
    have he : Real.log (((ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 : ℕ) : ℝ) =
        SquarefreeVaughanLogSource.length u N := by
      simp only [SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast hgeo.1.pos) (by positivity)).mp (he ▸ htop)


/-- Every selected integer is squarefree, has exactly `k+1` prime factors,
and satisfies the unchanged radial conditions and the new prime-share cap. -/
theorem population_data {k : ℕ} {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|) {n : ℕ}
    (hn : n ∈ population k v y) :
    Squarefree n ∧ n.primeFactors.card = k+1 ∧
      v-Real.pi/|y| < Real.log n ∧ Real.log n ≤ v+Real.pi/|y| ∧
      (∀ a ∈ n.primeFactors, Real.log a ≤ (1189/2000 : ℝ)*Real.log n) := by
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  simpa only [Nat.mul_comm a p] using (fibre_geometry hv hy ha hp).2.2
/-- All original core masks are discharged on the concrete rectangle.
The phase-period selection does not enlarge the arithmetic support. -/
theorem population_subset_core {k : ℕ} (hk : 2 ≤ k) (j : ℕ) (hj : 32 ≤ j)
    (hcount : k+1 < ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) {u v y : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ |y|) (hv : 100 ≤ v)
    (hL : (5/4 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
    (hlo : (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤ v-Real.pi/|y|)
    (hhi : v+Real.pi/|y| ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) :
    population k v y ⊆ ZetaRieszParityPacket.coreBand u
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) := by
  intro n hn
  obtain ⟨hs,hc,htl,htu,hmax⟩ := population_data hv hy hn
  apply ZetaRieszTransitionSixPeriod.mem_core_of_prime_share_le j hj hu hU hL hs
    (by omega) ?_ (hlo.trans_lt htl) (htu.trans hhi) hmax
  rwa [hc]

/-- The wider population is paid in the actual coupled residual carrier,
with its allocation cost absorbed locally. No separate source-scale
allocation error is needed for this population. -/
theorem eventually_population_bound {k : ℕ} (hk : 2 ≤ k) {ε : ℝ} (hε : 0 < ε) {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {m : ℕ} (hm : 0 < m)
    {y : ℝ} (hy : 54 ≤ |y|)
    (_hsmall : Real.pi/(4*m*|y|) ≤ 1/100000)
    (_hphase : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      Real.cos (y*v) = -1 → 2*(N : ℝ) ≤ v → v ≤ 2*N+Real.sqrt N →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      population k v y ⊆ ZetaRieszParityPacket.coreBand u N K ∧
      ∃ V : ℝ, 0 < V ∧ V ≤ Real.exp (-v/2)*v^N/N.factorial ∧
        |u^(N+1)*(∑ n ∈ population k v y,
          ZetaRieszJointAllocation.residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
            (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re| ≤
          u^(N+1)*((m : ℝ)*ε*V*(Real.pi/(4*m*|y|))) := by
  have hroom : u < Real.exp (-(137/200 : ℝ)) :=
    hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans
      (Real.exp_lt_exp.mpr (by norm_num)))
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_residual_small hk hy hε),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
        (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 137/200) hroom),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually (eventually_owner_mem k hu hU hy),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1000 : ℕ)),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (ZetaRieszSaddleBand.eventually_sqrt_add_one_le_mul (by norm_num : (0 : ℝ) < 1/1000)),
    eventually_ge_atTop (32 : ℕ),eventually_ge_atTop (k+1)] with j hraw hL hA hN hwide hj hkj
  intro v
  dsimp only
  intro hv hslo hshi hlo hhi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have hv0 : 0 < v := by change 2*(N : ℝ) ≤ v at hslo; linarith
  have hv100 : 100 ≤ v := by change 2*(N : ℝ) ≤ v at hslo; linarith
  change 2*(137/200 : ℝ)*N ≤ L at hL
  have hLl : (67/100 : ℝ)*v ≤ L := by change v ≤ 2*(N : ℝ)+Real.sqrt N at hshi; linarith
  have hK : k+1 < ZetaRieszPrimeCountFrequency.dyadicPrimeCount j := by
    have hh := (j+3).lt_two_pow_self
    change k+1 < 2^(j+3)
    omega
  have hcore := population_subset_core hk j hj hK hu hU hy hv100 (by linarith) hlo hhi
  let V := Real.exp (-v/2)*v^N/N.factorial
  have hV : 0 < V := by dsimp [V]; positivity
  refine ⟨hcore,V,hV,le_rfl,?_⟩
  have hb := hraw (ZetaRieszAnnulusJoint.intermediatePrimes u N) v L hslo hshi hv hLl (hA v hslo hshi)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hy0 : 0 < |y| := by linarith
  rw [abs_mul,abs_of_nonneg (pow_nonneg (show 0 ≤ u by linarith) _)]
  apply (mul_le_mul_of_nonneg_left hb (pow_nonneg (show 0 ≤ u by linarith) _)).trans_eq
  congr 1
  dsimp only [V]
  field_simp
  dsimp only [N]
  ring

end
end RiemannGaussian.ZetaRieszFixedCountPeriod
