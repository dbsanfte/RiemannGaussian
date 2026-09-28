/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSixCofactorPeriod
import RiemannGaussian.ZetaRieszAllocationVariation

/-!
# Signed six-prime cancellation across the allocation transition

The cofactor lower cut moves to `203v/500`, allowing the largest prime
to cross the old `19/32` transition. The exact allocation is retained
inside each full signed phase period. Its radial variation, rather than
an exponentially small assigned fraction, pays the new region.
-/
namespace RiemannGaussian.ZetaRieszTransitionSixPeriod
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszMacroPrimeWindows
open ZetaSquarefreeRieszWindows ZetaRieszTriplePrime

/-- The added cofactor range below the unique largest prime. -/
def extraCofactors (v : ℝ) : Finset ℕ :=
  (ZetaRieszBroadSixPeriod.cofactors ((133/120 : ℝ)*v)).filter
    (fun a => (3/5 : ℝ)*v < Real.log a ∧
      ∀ q ∈ a.primeFactors, Real.log q ≤ (33/100 : ℝ)*v)

/-- Every earlier cofactor, enlarged through the old allocation transition. -/
def cofactors (v : ℝ) : Finset ℕ :=
  ((ZetaRieszBroadSixPeriod.cofactors v ∪
    ZetaRieszBroadSixPeriod.cofactors ((4/5 : ℝ)*v)).filter
      (fun a => (203/500 : ℝ)*v < Real.log a)) ∪ extraCofactors v

/-- The unchanged full largest-prime phase period on the enlarged set. -/
def population (v y : ℝ) : Finset ℕ := (cofactors v).biUnion (fun a =>
  (logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)).image (fun p => a*p))

private theorem cofactor_data {v : ℝ} {a : ℕ} (ha : a ∈ cofactors v) :
    Squarefree a ∧ a.primeFactors.card = 5 ∧ Real.log a.minFac ≤ v ∧
      (203/500 : ℝ)*v < Real.log a ∧ Real.log a ≤ (133/200 : ℝ)*v ∧
      (∀ p ∈ a.primeFactors, Real.log p ≤ (199/200 : ℝ)*v-Real.log a) := by
  rcases Finset.mem_union.mp ha with ha | ha
  · obtain ⟨ha,hlow⟩ := Finset.mem_filter.mp ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have h := ZetaRieszBroadSixPeriod.cofactor_geometry ha
      have hv : 0 ≤ v := by nlinarith [Real.log_natCast_nonneg a,h.2.2.2.2.1]
      refine ⟨h.1,h.2.1,by nlinarith [h.2.2.1],hlow,by nlinarith [h.2.2.2.2.1],?_⟩
      intro p hp
      linarith [h.2.2.2.2.2 p hp,h.2.2.2.2.1]
    · have h := ZetaRieszBroadSixPeriod.cofactor_geometry ha
      have hv : 0 ≤ v := by nlinarith [Real.log_natCast_nonneg a,h.2.2.2.2.1]
      refine ⟨h.1,h.2.1,by nlinarith [h.2.2.1],hlow,by nlinarith [h.2.2.2.2.1],?_⟩
      intro p hp
      nlinarith [h.2.2.2.2.2 p hp,h.2.2.2.2.1]
  · obtain ⟨ha,hlow,hmax⟩ := Finset.mem_filter.mp ha
    have h := ZetaRieszBroadSixPeriod.cofactor_geometry ha
    have hv : 0 ≤ v := by nlinarith [Real.log_natCast_nonneg a,h.2.2.2.2.1]
    refine ⟨h.1,h.2.1,by nlinarith [h.2.2.1],by nlinarith [hlow],by nlinarith [h.2.2.2.2.1],?_⟩
    intro p hp
    nlinarith [hmax p hp,h.2.2.2.2.1]

/-- The selected six-prime integers have unique largest-prime ownership,
all original radial bounds, and prime shares below the separately paid owner band. -/
theorem fibre_geometry {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    {a p : ℕ} (ha : a ∈ cofactors v)
    (hp : p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)) :
    p.Prime ∧ (∀ q ∈ a.primeFactors, q < p) ∧ Squarefree (p*a) ∧
      (p*a).primeFactors.card = 6 ∧
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

/-- The exact reflected coefficient retains its moving cutoff through
all chambers, with no fixed-sign or plateau hypothesis. -/
theorem coefficient_eq_response {v y L : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (hLl : (67/100 : ℝ)*v ≤ L)
    {a p : ℕ} (ha : a ∈ cofactors v)
    (hp : p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)) :
    SquarefreeVaughanLogSource.coefficient L (p*a) =
      ((-(Real.log (p*a : ℕ)/L)*VaughanLogAverage.riesz (Real.log (p*a : ℕ)-L) a : ℝ) : ℂ) := by
  obtain ⟨hpp,howner,hs,hc,_,_,_⟩ := fibre_geometry hv hy ha hp
  have hadata := cofactor_data ha
  have hpd : ¬p ∣ a := by
    intro h
    exact (howner p (hpp.mem_primeFactors h hadata.1.ne_zero)).false
  have hn1 : p*a ≠ 1 := by intro h; simp [h] at hc
  have hnp : ¬(p*a).Prime := by intro h; simp [h.primeFactors] at hc
  have hlog : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hpp.ne_zero) (by exact_mod_cast hadata.1.ne_zero)]
  have houter : Real.log (p*a : ℕ)-L-Real.log p ≤ 0 := by
    rw [hlog]; linarith [hadata.2.2.2.2.1]
  have href := VaughanLogAverage.riesz_reflection L hs hn1 hnp
  rw [ZetaRieszReflectedLinear.moebius_eq_primeCount hs,hc] at href
  norm_num only [Int.cast_pow,Int.cast_neg,Int.cast_one,one_mul] at href
  rw [riesz_prime_mul (Real.log (p*a : ℕ)-L) hpp hpd,
    ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos houter,sub_zero] at href
  rw [SquarefreeVaughanLogSource.coefficient,if_pos ⟨hs,hnp⟩,← href]
  congr 1
  ring

/-- Every five-prime cofactor has this signed-amplitude bound. -/
theorem cofactor_response_bound {v : ℝ} {a : ℕ} (ha : a ∈ cofactors v) (D : ℝ) :
    |VaughanLogAverage.riesz D a| ≤ 3*Real.log a.minFac := by
  have hd := cofactor_data ha
  have hh := ZetaRieszSignedSperner.riesz_bounds_minFac D hd.1 (by omega : 2 ≤ a.primeFactors.card)
  rw [hd.2.1] at hh
  have hc0 : ZetaRieszSignedSperner.parityCapacity 3 0 = 3 := by decide +kernel
  have hc1 : ZetaRieszSignedSperner.parityCapacity 3 1 = 3 := by decide +kernel
  norm_num only [Nat.reduceSub,hc0,hc1,Nat.cast_ofNat] at hh
  exact abs_le.mpr (by constructor <;> linarith only [hh.1,hh.2])

/-- The full five-prime response changes by at most eight times the
cutoff displacement, including every chamber boundary. -/
theorem cofactor_response_variation {v : ℝ} {a : ℕ} (ha : a ∈ cofactors v) (D E : ℝ) :
    |VaughanLogAverage.riesz D a-VaughanLogAverage.riesz E a| ≤ 8*|D-E| := by
  have hd := cofactor_data ha
  have hh := ZetaRieszTentSlope.riesz_cutoff_lipschitz_quarter D E hd.1
    (by omega : 2 ≤ a.primeFactors.card)
  rw [ZetaRieszTentSlope.absolute_divisor_mass_eq_card hd.1,
    ZetaRieszSmoothHead.card_divisors_of_squarefree hd.1,hd.2.1] at hh
  norm_num only [Nat.reducePow,Nat.cast_ofNat] at hh
  linarith only [hh]

/-- The whole largest-prime period is summed before any absolute value. -/
theorem sum_population {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|) (f : ℕ → ℂ) :
    (∑ n ∈ population v y, f n) = ∑ a ∈ cofactors v,
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

/-- A positive counting constant for all three cofactor bands. -/
def logMassConstant : ℝ := 4*ZetaRieszBroadSixPeriod.logMassConstant
/-- The corresponding cutoff-variation counting constant. -/
def variationConstant : ℝ := 4*ZetaRieszBroadSixPeriod.variationConstant

private theorem mass_constants_pos : 0 < logMassConstant ∧ 0 < variationConstant := by
  have h := ZetaRieszBroadSixPeriod.mass_constants_pos
  exact ⟨mul_pos (by norm_num) h.1,mul_pos (by norm_num) h.2⟩

private theorem cofactor_union_mass (v : ℝ) (f : ℕ → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (∑ a ∈ cofactors v, f a) ≤
      (∑ a ∈ ZetaRieszBroadSixPeriod.cofactors v, f a)+
      (∑ a ∈ ZetaRieszBroadSixPeriod.cofactors ((4/5 : ℝ)*v), f a)+
      ∑ a ∈ ZetaRieszBroadSixPeriod.cofactors ((133/120 : ℝ)*v), f a := by
  have hunion (S T : Finset ℕ) : (∑ a ∈ S ∪ T, f a) ≤ (∑ a ∈ S, f a)+(∑ a ∈ T, f a) := by
    have h := Finset.sum_union_inter (f := f) (s₁ := S) (s₂ := T)
    have hp := Finset.sum_nonneg (s := S ∩ T) (fun a _ => hf a)
    linarith only [h,hp]
  apply (hunion _ _).trans
  apply add_le_add
  · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun a _ _ => hf a)).trans (hunion _ _)
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun a _ _ => hf a)

/-- The transition population keeps the same actual logarithmic mass budget. -/
theorem cofactor_log_mass {v : ℝ} (hv : 0 < v) :
    (∑ a ∈ cofactors v, Real.log a.minFac*(a : ℝ)⁻¹) ≤ logMassConstant*v := by
  have h := cofactor_union_mass v (fun a => Real.log a.minFac*(a : ℝ)⁻¹) (fun a => by positivity)
  have h1 := ZetaRieszBroadSixPeriod.cofactor_log_mass hv
  have h2 := ZetaRieszBroadSixPeriod.cofactor_log_mass (show 0 < (4/5 : ℝ)*v by positivity)
  have h3 := ZetaRieszBroadSixPeriod.cofactor_log_mass (show 0 < (133/120 : ℝ)*v by positivity)
  have hc := ZetaRieszBroadSixPeriod.mass_constants_pos.1
  dsimp only [logMassConstant] at *
  nlinarith only [h,h1,h2,h3,mul_pos hc hv]

/-- Cutoff movement is paid by the actual cofactor reciprocal mass. -/
theorem cofactor_mass {v : ℝ} (hv : 0 < v) :
    (∑ a ∈ cofactors v, (a : ℝ)⁻¹) ≤ variationConstant*v^(1/2 : ℝ) := by
  have h := cofactor_union_mass v (fun a => (a : ℝ)⁻¹) (fun a => by positivity)
  have h1 := ZetaRieszBroadSixPeriod.cofactor_mass hv
  have h2 := ZetaRieszBroadSixPeriod.cofactor_mass (show 0 < (4/5 : ℝ)*v by positivity)
  have h3 := ZetaRieszBroadSixPeriod.cofactor_mass (show 0 < (133/120 : ℝ)*v by positivity)
  have hp2 : ((4/5 : ℝ)*v)^(1/2 : ℝ) ≤ v^(1/2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have hp3 : ((133/120 : ℝ)*v)^(1/2 : ℝ) ≤ 2*v^(1/2 : ℝ) := by
    have hh := Real.rpow_le_rpow (show 0 ≤ (133/120 : ℝ)*v by positivity)
      (show (133/120 : ℝ)*v ≤ 4*v by linarith) (by norm_num : (0 : ℝ) ≤ 1/2)
    have h4 : (4 : ℝ)^(1/2 : ℝ) = 2 := by rw [← Real.sqrt_eq_rpow]; norm_num
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hv.le,h4] at hh
    exact hh
  have hc := ZetaRieszBroadSixPeriod.mass_constants_pos.2
  have hh2 := mul_le_mul_of_nonneg_left hp2 hc.le
  have hh3 := mul_le_mul_of_nonneg_left hp3 hc.le
  dsimp only [variationConstant] at *
  linarith only [h,h1,h2,h3,hh2,hh3]

private theorem re_response_atom {v y L : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (hLl : (67/100 : ℝ)*v ≤ L)
    {a p : ℕ} (ha : a ∈ cofactors v)
    (hp : p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)) (N : ℕ) :
    (SquarefreeVaughanLogSource.coefficient L (p*a)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re =
      -(VaughanLogAverage.riesz (Real.log p+Real.log a-L) a/L/a)*
        ((Real.exp (-(Real.log p+Real.log a)/2)*(Real.log p+Real.log a)^(N+1)/N.factorial)*
          (p : ℝ)⁻¹*Real.cos (y*(Real.log p+Real.log a))) := by
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
    coefficient_eq_response hv hy hLl ha hp,Complex.ofReal_re,hex,hlog,pow_succ]
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
theorem fibre_bound (A : Finset ℕ) {m N : ℕ} {v y L V η : ℝ}
    (hv : 100 ≤ v) (hy : 54 ≤ |y|) (hLl : (67/100 : ℝ)*v ≤ L)
    (hV : 0 ≤ V) (hη : 0 ≤ η) {a : ℕ} (ha : a ∈ cofactors v)
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
        ((1000*η/v+720*Real.sqrt (N+1)/v^2)*(Real.log a.minFac*(a : ℝ)⁻¹)+(100/v)*(a : ℝ)⁻¹) := by
  let h := Real.pi/(4*m*|y|)
  let D := logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)
  let w := fun p : ℕ => (Real.exp (-(Real.log p+Real.log a)/2)*
    (Real.log p+Real.log a)^(N+1)/N.factorial)*(p : ℝ)⁻¹
  let g := fun p : ℕ => w p*Real.cos (y*(Real.log p+Real.log a))
  by_cases hDn : D.Nonempty
  swap
  · have he : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hDn
    change |(∑ p ∈ D, ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re| ≤ _
    rw [he,Finset.sum_empty,Complex.zero_re,abs_zero]
    positivity
  obtain ⟨p₀,hp₀⟩ := hDn
  let R := fun p : ℕ => (1-ZetaRieszJointAllocation.boundedShare A N (p*a))*
    VaughanLogAverage.riesz (Real.log p+Real.log a-L) a
  let R₀ := R p₀
  let E := 1+9*Real.sqrt (N+1)/v*Real.log a.minFac
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
    have hs := ZetaRieszAllocationVariation.boundedShare_fibre_variation A N hd.1 hd.2.1
      (hgeo p hp).1 (hnot p hp) (hA p hp) (hgeo p₀ hp₀).1 (hnot p₀ hp₀) (hA p₀ hp₀)
      hv hπ hπu hd.2.2.2.2.1 ⟨hpT.1.le,hpT.2.1⟩ ⟨hqT.1.le,hqT.2.1⟩
    have hshare : |ZetaRieszJointAllocation.boundedShare A N (p*a)-
        ZetaRieszJointAllocation.boundedShare A N (p₀*a)| ≤ 3*Real.sqrt (N+1)/v := by
      apply hs.trans
      have hh := mul_le_mul_of_nonneg_left hdif
        (show 0 ≤ 24*Real.sqrt (N+1)/v by positivity)
      convert hh using 1; ring
    have hvary : |VaughanLogAverage.riesz (Real.log p+Real.log a-L) a-
        VaughanLogAverage.riesz (Real.log p₀+Real.log a-L) a| ≤ 1 := by
      have hh := cofactor_response_variation ha (Real.log p+Real.log a-L) (Real.log p₀+Real.log a-L)
      rw [hlog p hp,hlog p₀ hp₀] at hdif
      have he : (Real.log p+Real.log a-L)-(Real.log p₀+Real.log a-L) =
        (Real.log p+Real.log a)-(Real.log p₀+Real.log a) := by ring
      rw [he] at hh
      linarith only [hh,hdif]
    have htheta := ZetaRieszJointAllocation.boundedShare_bounds A N (p*a)
    have hthetaAbs : |1-ZetaRieszJointAllocation.boundedShare A N (p*a)| ≤ 1 :=
      abs_le.mpr (by constructor <;> linarith)
    have he : R p-R₀ = (1-ZetaRieszJointAllocation.boundedShare A N (p*a))*
        (VaughanLogAverage.riesz (Real.log p+Real.log a-L) a-
          VaughanLogAverage.riesz (Real.log p₀+Real.log a-L) a)+
        (ZetaRieszJointAllocation.boundedShare A N (p₀*a)-
          ZetaRieszJointAllocation.boundedShare A N (p*a))*
          VaughanLogAverage.riesz (Real.log p₀+Real.log a-L) a := by dsimp [R,R₀]; ring
    rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul,abs_sub_comm (ZetaRieszJointAllocation.boundedShare A N (p₀*a))]
    have h1 := mul_le_mul hthetaAbs hvary (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have h2 := mul_le_mul hshare (cofactor_response_bound ha (Real.log p₀+Real.log a-L)) (abs_nonneg _)
      (by positivity : 0 ≤ 3*Real.sqrt (N+1)/v)
    dsimp only [E]
    ring_nf at h1 h2 ⊢
    linarith only [h1,h2]
  have hs := signed_perturbation D R g w R₀ E (by dsimp [E]; positivity) hw hg hR
  have he : (∑ p ∈ D, ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re =
      -(1/L/a)*(∑ p ∈ D, R p*g p) := by
    rw [Complex.re_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [ZetaRieszJointAllocation.residualCoefficient,mul_assoc,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [re_response_atom hv hy hLl ha hp]
    dsimp [R,g,w]
    ring
  change |(∑ p ∈ D, ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
    zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re| ≤ _
  rw [he,abs_mul,abs_neg,abs_of_nonneg (show 0 ≤ 1/L/a by positivity)]
  have hrc : |R₀| ≤ 3*Real.log a.minFac := by
    dsimp [R₀,R]
    rw [abs_mul]
    have htheta := ZetaRieszJointAllocation.boundedShare_bounds A N (p₀*a)
    have hthetaAbs : |1-ZetaRieszJointAllocation.boundedShare A N (p₀*a)| ≤ 1 :=
      abs_le.mpr (by constructor <;> linarith)
    simpa only [one_mul] using mul_le_mul hthetaAbs (cofactor_response_bound ha _)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hS : |∑ p ∈ D, R p*g p| ≤
      (3*Real.log a.minFac)*((64*η)*m*V*v*h/(v-Real.log a))+
        E*(16*m*V*v*h/(v-Real.log a)) := by
    apply hs.trans
    have hh := mul_le_mul hrc hperiod.1 (abs_nonneg _) (by positivity : 0 ≤ 3*Real.log a.minFac)
    exact add_le_add hh (mul_le_mul_of_nonneg_left hperiod.2 (by dsimp [E]; positivity))
  apply (mul_le_mul_of_nonneg_left hS (show 0 ≤ 1/L/a by positivity)).trans
  have hden : v*v ≤ 5*L*(v-Real.log a) := by
    have hh := mul_le_mul hLl (show (67/200 : ℝ)*v ≤ v-Real.log a by linarith [hd.2.2.2.2.1])
      (by positivity) (by positivity : 0 ≤ L)
    nlinarith
  have hfrac : v/(L*(v-Real.log a)) ≤ 5/v :=
    (div_le_div_iff₀ (mul_pos hL hab) hv0).mpr (by nlinarith only [hden])
  have hnonneg : 0 ≤ (m : ℝ)*V*h*(a : ℝ)⁻¹ := by dsimp [h]; positivity
  have hm := mul_le_mul_of_nonneg_right hfrac
    (show 0 ≤ ((m : ℝ)*V*h*(a : ℝ)⁻¹)*(192*η*Real.log a.minFac+16*E) by dsimp [E]; positivity)
  have hsmall : (192*η*Real.log a.minFac+16*E)*5 ≤ (1000*η+720*Real.sqrt (N+1)/v)*Real.log a.minFac+100 := by
    dsimp only [E]
    ring_nf
    nlinarith [mul_nonneg hη (Real.log_natCast_nonneg a.minFac)]
  have ht := mul_le_mul_of_nonneg_left hsmall (div_nonneg hnonneg hv0.le)
  dsimp only [h,E] at hm ht ⊢
  simp only [div_eq_mul_inv,mul_inv_rev] at hm ht ⊢
  ring_nf at hm ht ⊢
  linarith only [hm,ht]

/-- A genuine signed population bound, arbitrarily small relative to the
local radial weight. All cofactor primes and all cutoff chambers are
included. This is not a source-normalized decay claim. -/
theorem eventually_residual_population_small {y ε : ℝ} (hy : 54 ≤ |y|) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (v L : ℝ),
      2*(N : ℝ) ≤ v → v ≤ 2*N+1 → Real.cos (y*v) = -1 →
      (67/100 : ℝ)*v ≤ L →
      (∀ a ∈ cofactors v, ∀ p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|), p ∈ A) →
      |(∑ n ∈ population v y, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re| ≤
        ε*(Real.pi/(4*|y|))*(Real.exp (-v/2)*v^N/N.factorial) := by
  have hC := mass_constants_pos
  have hCl := hC.1
  have hCv := hC.2
  let η := min (1/10000 : ℝ) (ε/(4000*logMassConstant))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηu : η ≤ 1/100 := (min_le_left _ _).trans (by norm_num)
  have hηε : 1000*η*logMassConstant ≤ ε/4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4000*logMassConstant)).mp (min_le_right _ _ : η ≤ _)
    nlinarith only [hh]
  obtain ⟨m,hm,hsmall,hphase⟩ := ZetaRieszBroadSixPeriod.exists_precise_mesh hy hη
  have hr : Tendsto (fun v : ℝ => (720*logMassConstant+100*variationConstant)*v^(-(1/2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).const_mul
      (720*logMassConstant+100*variationConstant)
  obtain ⟨v₀,hv₀⟩ := eventually_atTop.mp (hr.eventually_lt_const (show 0 < ε/2 by positivity))
  filter_upwards [ZetaRieszSaddlePeriod.eventually_factorial_period hm hy
      (by norm_num : (0 : ℝ) < 1/2) hη hηu hsmall hphase,
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
  have hrow (a : ℕ) (ha : a ∈ cofactors v) := fibre_bound A (N := N) hv100 hy hLl hV.le hη.le ha (hA a ha)
    (hperiod (Real.log a) (by have hd := cofactor_data ha; linarith [hd.2.2.2.2.1]))
  have hsum : |(∑ n ∈ population v y, ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re| ≤
      ((m : ℝ)*V*h)*((1000*η/v+720*Real.sqrt (N+1)/v^2)*(logMassConstant*v)+
        (100/v)*(variationConstant*v^(1/2 : ℝ))) := by
    rw [sum_population hv100 hy,Complex.re_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply (Finset.sum_le_sum hrow).trans
    rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (mul_le_mul_of_nonneg_left (cofactor_log_mass hv0) (by positivity))
      (mul_le_mul_of_nonneg_left (cofactor_mass hv0) (by positivity))
  have hrat : v^(1/2 : ℝ)/v = v^(-(1/2 : ℝ)) := by
    have hh := Real.rpow_sub hv0 (1/2 : ℝ) 1
    norm_num at hh
    exact hh.symm
  have hroot : Real.sqrt (N+1)/v ≤ v^(-(1/2 : ℝ)) := by
    have hs : Real.sqrt (N+1) ≤ Real.sqrt v := Real.sqrt_le_sqrt (by linarith)
    have hh := div_le_div_of_nonneg_right hs hv0.le
    rw [Real.sqrt_eq_rpow v,hrat] at hh
    exact hh
  have hbudget : (1000*η/v+720*Real.sqrt (N+1)/v^2)*(logMassConstant*v)+
      (100/v)*(variationConstant*v^(1/2 : ℝ)) ≤ ε := by
    have he : (1000*η/v+720*Real.sqrt (N+1)/v^2)*(logMassConstant*v)+
        (100/v)*(variationConstant*v^(1/2 : ℝ)) =
        1000*η*logMassConstant+720*logMassConstant*(Real.sqrt (N+1)/v)+
          100*variationConstant*(v^(1/2 : ℝ)/v) := by field_simp
    rw [he,hrat]
    have hh := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 720*logMassConstant by positivity)
    have ht := hv₀ v hvlarge
    ring_nf at hh ht hηε ⊢
    linarith only [hh,ht,hηε,hε]
  apply hsum.trans
  have he : (m : ℝ)*h = Real.pi/(4*|y|) := by dsimp [h]; field_simp
  calc
    _ ≤ ((m : ℝ)*V*h)*ε := mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = ε*(Real.pi/(4*|y|))*V := by rw [← he]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbase (by positivity)
private theorem mem_core_of_prime_share_le (j : ℕ) (hj : 32 ≤ j) {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hL : (5/4 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
    {n : ℕ} (hs : Squarefree n) (hc : 3 ≤ n.primeFactors.card)
    (hK : n.primeFactors.card < ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)
    (hlo : (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j < Real.log n)
    (hhi : Real.log n ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
    (hmax : ∀ p ∈ n.primeFactors, Real.log p ≤ (1189/2000 : ℝ)*Real.log n) :
    n ∈ ZetaRieszParityPacket.coreBand u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
      (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) := by
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  have hN : (0 : ℝ) < N := by
    dsimp [N,ZetaRieszPrimeCountFrequency.dyadicMomentOrder,
      ZetaRieszPrimeCountFrequency.dyadicPrimeCount]
    positivity
  have ht : 0 < Real.log n := by change (39/20 : ℝ)*N < _ at hlo; linarith
  have hW : n ∈ ZetaRieszJointAllocation.literalWindow N := (ZetaRieszJointAllocation.mem_literalWindow N n).mpr
    (by constructor <;> dsimp [N] at * <;> nlinarith)
  have hpX : ∀ p ∈ n.primeFactors,
      p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 := by
    intro p hp
    have hplog : Real.log p < SquarefreeVaughanLogSource.length u N := by
      have hm := hmax p hp
      change Real.log n ≤ (203/100 : ℝ)*N at hhi
      change (5/4 : ℝ)*N ≤ _ at hL
      nlinarith
    have he : Real.log (((ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 : ℕ) : ℝ) =
        SquarefreeVaughanLogSource.length u N := by
      simp only [SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
      (by positivity)).mp (he ▸ hplog)
  have hm := ZetaRieszMaskSupport.window_mem_originalMask j hj hu
    (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le) hL hW hs hc hK hpX
  have hdom (p : ℕ) (hp : p ∈ n.primeFactors) :
      Real.log p < (13/20 : ℝ)*Real.log n := by linarith [hmax p hp]
  have hcancel : n ∉ ZetaRieszJointAllocation.cancellingSector u N K := by
    intro hh
    obtain ⟨_,_,_,_,_,p,hp,_,_,_,hshare⟩ := Finset.mem_filter.mp hh
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hd : Real.log (n/p : ℕ) = Real.log n-Real.log p := by
      rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors hp) (by exact_mod_cast hpp.ne_zero),
        Real.log_div (by exact_mod_cast hs.ne_zero) (by exact_mod_cast hpp.ne_zero)]
    have hh := (div_le_iff₀ ht).mp hshare
    rw [hd] at hh
    nlinarith [hdom p hp]
  have hret : n ∈ ZetaRieszMaskSupport.retainedBand u N K :=
    Finset.mem_sdiff.mpr ⟨hm,hcancel⟩
  have hnd : n ∈ ZetaRieszDominantAllocation.nondominantBand u N K := by
    refine Finset.mem_sdiff.mpr ⟨hret,?_⟩
    intro hd
    obtain ⟨_,_,_,_,p,hp,_,_,hl⟩ := Finset.mem_filter.mp hd
    exact (hdom p hp).not_ge hl
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨hnd,by constructor <;> dsimp [N] at * <;> nlinarith⟩,hlo,hhi⟩

/-- Every selected integer is squarefree, has exactly six prime factors,
and satisfies the unchanged radial conditions and the new prime-share cap. -/
theorem population_data {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|) {n : ℕ}
    (hn : n ∈ population v y) :
    Squarefree n ∧ n.primeFactors.card = 6 ∧
      v-Real.pi/|y| < Real.log n ∧ Real.log n ≤ v+Real.pi/|y| ∧
      (∀ a ∈ n.primeFactors, Real.log a ≤ (1189/2000 : ℝ)*Real.log n) := by
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  simpa only [Nat.mul_comm a p] using (fibre_geometry hv hy ha hp).2.2
/-- All original core masks are discharged on the concrete rectangle.
The phase-period selection does not enlarge the arithmetic support. -/
theorem population_subset_core (j : ℕ) (hj : 32 ≤ j) {u v y : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ |y|) (hv : 100 ≤ v)
    (hL : (5/4 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
    (hlo : (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤ v-Real.pi/|y|)
    (hhi : v+Real.pi/|y| ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) :
    population v y ⊆ ZetaRieszParityPacket.coreBand u
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) := by
  intro n hn
  obtain ⟨hs,hcount,htl,htu,hmax⟩ := population_data hv hy hn
  apply mem_core_of_prime_share_le j hj hu hU hL hs
    (by omega) ?_ (hlo.trans_lt htl) (htu.trans hhi) hmax
  rw [hcount]
  have hk : 8 ≤ ZetaRieszPrimeCountFrequency.dyadicPrimeCount j := by
    change 2^3 ≤ 2^(j+3)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- Every moving owner stays in the original intermediate-prime mask. -/
theorem eventually_owner_mem {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ |y|) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, 2*(N : ℝ) ≤ v → v ≤ 2*N+1 →
      ∀ a ∈ cofactors v, ∀ p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|),
        p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N := by
  have hroom : u < Real.exp (-(137/200 : ℝ)) :=
    hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans (Real.exp_lt_exp.mpr (by norm_num)))
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ)/(N : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,pow_one,one_mul,add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hl.eventually_lt_const (by norm_num : (0 : ℝ) < 1/4),
    ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
      (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 137/200) hroom,
    eventually_ge_atTop (1000 : ℕ)] with N hlog hL hN v hv hvu a ha p hp
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hgeo := fibre_geometry (by linarith : 100 ≤ v) hy ha hp
  have hd := cofactor_data ha
  have hpb := logPrimes_bounds hp
  have hpi : Real.pi/|y| ≤ 1/16 :=
    (div_le_iff₀ (by linarith : 0 < |y|)).mpr (by nlinarith [Real.pi_lt_d4])
  apply (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mpr
  refine ⟨hgeo.1,?_,?_⟩
  · have hlg : 2*Real.log (N : ℝ) < (N : ℝ)/2 := by
      have hh := (div_lt_iff₀ hN0).mp hlog
      linarith only [hh]
    have hh : Real.log ((N^2 : ℕ) : ℝ) < Real.log p := by
      rw [Nat.cast_pow,Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith [hpb.2.1,hd.2.2.2.2.1]
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

/-- The wider population is paid in the actual coupled residual carrier,
with its allocation cost absorbed locally. No separate source-scale
allocation error is needed for this population. -/
theorem eventually_signed_population_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {m : ℕ} (hm : 0 < m)
    {y : ℝ} (hy : 54 ≤ |y|)
    (_hsmall : Real.pi/(4*m*|y|) ≤ 1/100000)
    (_hphase : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      Real.cos (y*v) = -1 → 2*(N : ℝ) ≤ v → v ≤ 2*N+1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      population v y ⊆ ZetaRieszParityPacket.coreBand u N K ∧
      ∃ V : ℝ, 0 < V ∧ V ≤ Real.exp (-v/2)*v^N/N.factorial ∧
        |u^(N+1)*(∑ n ∈ population v y,
          ZetaRieszJointAllocation.residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
            (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re| ≤
          u^(N+1)*((m : ℝ)/100000*V*(Real.pi/(4*m*|y|))) := by
  have hroom : u < Real.exp (-(137/200 : ℝ)) :=
    hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans
      (Real.exp_lt_exp.mpr (by norm_num)))
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_residual_population_small hy (by norm_num : (0 : ℝ) < 1/100000)),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
        (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 137/200) hroom),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually (eventually_owner_mem hu hU hy),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1000 : ℕ)), eventually_ge_atTop (32 : ℕ)] with j hraw hL hA hN hj
  intro v
  dsimp only
  intro hv hslo hshi hlo hhi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have hv0 : 0 < v := by change 2*(N : ℝ) ≤ v at hslo; linarith
  have hv100 : 100 ≤ v := by change 2*(N : ℝ) ≤ v at hslo; linarith
  change 2*(137/200 : ℝ)*N ≤ L at hL
  have hLl : (67/100 : ℝ)*v ≤ L := by change v ≤ 2*(N : ℝ)+1 at hshi; linarith
  have hcore := population_subset_core j hj hu hU hy hv100 (by linarith) hlo hhi
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

/-- The new squarefree six-prime population cannot overlap any supply cell,
without adding an ordering or numerical-cover premise. -/
theorem disjoint_supply {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (t h z : ℝ) (lo H : Fin 4 → ℝ) :
    Disjoint (population v y) (ZetaRieszJointPrimeCells.supplyCell t h z lo H) := by
  apply Finset.disjoint_left.mpr
  intro n hn hs
  have hd := population_data hv hy hn
  have hcard : n.primeFactors.card = n.primeFactorsList.length :=
    List.toFinset_card_of_nodup hd.1.nodup_primeFactorsList
  have hc := ZetaRieszJointTriplePayment.supply_count hs
  rw [ArithmeticFunction.cardFactors_apply,← hcard,hd.2.1] at hc
  omega

/-- Four-prime payments and the new six-prime payment have distinct labels. -/
theorem disjoint_adverse {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S : Finset ℕ) (L t h z a : ℝ) :
    Disjoint (population v y) (ZetaRieszFourBoundaryCover.adversePopulation S L t h z a) := by
  apply Finset.disjoint_left.mpr
  intro n hn hf
  have hc := (population_data hv hy hn).2.1
  have hf := (Finset.mem_filter.mp hf).2.2.1
  omega

/-- Full positive-five interior payments have no six-prime labels. -/
theorem disjoint_interior {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S : Finset ℕ) (L v' z δ : ℝ) (m : ℕ) :
    Disjoint (population v y)
      (ZetaRieszPositiveFiveSignedPayment.periodPopulation S L v' z m δ) := by
  apply Finset.disjoint_left.mpr
  intro n hn hf
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hf
  have hc := (population_data hv hy hn).2.1
  have hf := (Finset.mem_filter.mp hi).2.2.1
  omega

/-- The small-prime five-factor boundary is disjoint from the six-primes. -/
theorem disjoint_head {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S : Finset ℕ) (L v' z : ℝ) (m : ℕ) :
    Disjoint (population v y)
      (ZetaRieszPositiveFiveBoundary.periodPopulation S L v' z m) := by
  apply Finset.disjoint_left.mpr
  intro n hn hf
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hf
  have hc := (population_data hv hy hn).2.1
  have hf := (Finset.mem_filter.mp hi).2.2.1
  omega

/-- Every prime share of the new rectangle is below the paid owner band. -/
theorem disjoint_owner {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S A : Finset ℕ) :
    Disjoint (population v y) (ZetaRieszJointOwnerPayment.population S A) := by
  apply Finset.disjoint_left.mpr
  intro n hn hf
  obtain ⟨_,_,hn1,_,p,hp,_,_,hlo,_⟩ := Finset.mem_filter.mp hf
  have hc := (population_data hv hy hn).2.2.2.2 p hp
  have hnlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  nlinarith


/-- The new six-prime period has no labels in the previously paid
balanced-triple population. -/
theorem disjoint_balanced {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S : Finset ℕ) (t h : ℝ) :
    Disjoint (population v y) (ZetaRieszBroadTripleBudget.population S t h) := by
  apply Finset.disjoint_left.mpr
  intro n hn hb
  have hc := (population_data hv hy hn).2.1
  have hb := (Finset.mem_filter.mp hb).2.2.1
  omega

/-- Nor can it overlap the previously paid unbalanced-triple period. -/
theorem disjoint_triple {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|) :
    Disjoint (population v y) (ZetaRieszTriplePeriod.population v y) := by
  apply Finset.disjoint_left.mpr
  intro n hn ht
  have hc := (population_data hv hy hn).2.1
  have ht := (ZetaRieszTriplePeriod.population_data hv hy ht).2.1
  omega


/-- The previous population is contained in the transition payment. -/
theorem previous_population_subset {v y : ℝ} (hv : 0 ≤ v) :
    ZetaRieszSixCofactorPeriod.population v y ⊆ population v y := by
  intro n hn
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
  refine Finset.mem_biUnion.mpr ⟨a,?_,hn⟩
  rcases Finset.mem_union.mp ha with ha | ha
  · obtain ⟨ha,hl⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha,by linarith⟩)
  · exact Finset.mem_union_right _ ha

/-- A cofactor below the old lower cut gives an actually new label. -/
theorem mem_population_sdiff_of_transition {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    {a p : ℕ} (ha : a ∈ cofactors v) (hal : Real.log a ≤ (41/100 : ℝ)*v)
    (hp : p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)) :
    a*p ∈ population v y\ZetaRieszSixCofactorPeriod.population v y := by
  have hg := fibre_geometry hv hy ha hp
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr
    ⟨a,ha,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩,?_⟩
  intro hn
  obtain ⟨b,hb,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨q,hq,he⟩ := Finset.mem_image.mp hn
  have hgb := ZetaRieszSixCofactorPeriod.fibre_geometry hv hy hb hq
  have hda := cofactor_data ha
  have hbold : (41/100 : ℝ)*v < Real.log b := by
    rcases Finset.mem_union.mp hb with hb | hb
    · exact (ZetaRieszWideSixPeriod.cofactor_geometry hb).2.2.2.1
    · have hh := (Finset.mem_filter.mp hb).2.1
      linarith
  have hb0 : b ≠ 0 := by
    intro hh
    rw [hh,mul_zero] at hgb
    exact hgb.2.2.1.ne_zero rfl
  have hab := (ZetaRieszCoupledWindow.largest_prime_product_unique hg.1 hgb.1
    (fun r hr hd => hg.2.1 r (hr.mem_primeFactors hd hda.1.ne_zero))
    (fun r hr hd => hgb.2.1 r (hr.mem_primeFactors hd hb0)) he.symm).1
  rw [← hab] at hbold
  linarith

/-- The new payment strictly enlarges the actual prime population
at every sufficiently large eligible radial center. -/
theorem eventually_added_population_crosses_transition {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, (N : ℝ) ≤ v →
      ∃ n ∈ population v y\ZetaRieszSixCofactorPeriod.population v y,
        ∃ p ∈ n.primeFactors, (19/32 : ℝ)*Real.log n < Real.log p := by
  have hy0 : 0 < |y| := by linarith
  have hH : 0 < 2*Real.pi/|y| := by positivity
  have hpi : Real.pi/|y| ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hne (S : Finset ℕ) (f : ℕ → ℝ) (hp : 0 < ∑ p ∈ S, f p) : S.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.sum_empty] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  filter_upwards [eventually_macro_reciprocal_bounds
      (by norm_num : (0 : ℝ) < 1/1000000) (by norm_num : (0 : ℝ) < 1/1000000),
    ZetaRieszSharpPrimeWindows.eventually_log_mass_bounds hH
      (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (0 : ℝ) < 1/2),
    eventually_ge_atTop (100000 : ℕ)] with N hmacro hlast hlarge v hv
  have hNR : (100000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hv0 : 0 < v := by linarith
  have hex (i : Fin 4) : ∃ q, q ∈ logPrimes (((203/2000 : ℝ)+(i : ℕ)/100000)*v) (v/100000) := by
    have hi : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
    have hm := (hmacro (((203/2000 : ℝ)+(i : ℕ)/100000)*v) (v/100000)
      (by nlinarith) (by linarith)).1
    exact hne _ _ ((by positivity : 0 < (4999/5000 : ℝ)*(v/100000)/
      (((203/2000 : ℝ)+(i : ℕ)/100000)*v+v/100000)).trans_le hm)
  choose q hq using hex
  have hqp (i : Fin 4) := (logPrimes_bounds (hq i)).1
  have hqb (i : Fin 4) := (logPrimes_bounds (hq i)).2
  have hqu (i : Fin 4) : Real.log (q i) ≤ (51/500 : ℝ)*v := by
    have hiu : ((i : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (show (i : ℕ) ≤ 3 by omega)
    nlinarith [hqb i]
  have hql (i : Fin 4) : (203/2000 : ℝ)*v < Real.log (q i) := by
    have hi : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
    nlinarith [hqb i]
  have hmono : StrictMono q := by
    intro i j hij
    have hijR : ((i : ℕ) : ℝ)+1 ≤ (j : ℕ) := by exact_mod_cast (show (i : ℕ)+1 ≤ j by omega)
    have hlog : Real.log (q i) < Real.log (q j) := by
      nlinarith [hqb i,hqb j,mul_nonneg (show (0 : ℝ) ≤ (j : ℕ)-(i : ℕ)-1 by linarith) hv0.le]
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast (hqp i).pos : (0 : ℝ) < q i)
      (by exact_mod_cast (hqp j).pos : (0 : ℝ) < q j)).mp hlog
  have h2q (i : Fin 4) : 2 ≠ q i := by
    intro h
    have hh := hql i
    rw [← h] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith [Real.log_two_lt_d9]
  have hsprod : Squarefree (∏ i, q i) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i _ j _ hij
      change IsRelPrime (q i) (q j)
      rw [← Nat.coprime_iff_isRelPrime]
      exact (Nat.coprime_primes (hqp i) (hqp j)).mpr (fun h => hij (hmono.injective h))
    · intro i _
      exact (hqp i).squarefree
  have h2d : ¬2 ∣ ∏ i, q i := by
    intro hd
    obtain ⟨i,_,hi⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff _).mp hd
    exact h2q i ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (hqp i)).mp hi)
  let a := ZetaRieszBroadSixPeriod.cofactor (2,q)
  have hloga : Real.log a = Real.log 2+∑ i, Real.log (q i) := by
    dsimp only [a,ZetaRieszBroadSixPeriod.cofactor]
    rw [Nat.cast_mul,Real.log_mul (by norm_num)
      (by exact_mod_cast Finset.prod_ne_zero_iff.mpr (fun i _ => (hqp i).ne_zero)),
      Nat.cast_prod,Real.log_prod (fun i _ => by exact_mod_cast (hqp i).ne_zero)]
    norm_num only [Nat.cast_ofNat]
  rw [Fin.sum_univ_four] at hloga
  have h0 := hqb 0
  have h1 := hqb 1
  have h2 := hqb 2
  have h3 := hqb 3
  norm_num at h0 h1 h2 h3
  have hal : (203/500 : ℝ)*v < Real.log a := by linarith [Real.log_two_gt_d9]
  have hau : Real.log a ≤ (2031/5000 : ℝ)*v := by linarith [Real.log_two_lt_d9]
  have hrq : (2,q) ∈ ZetaRieszBroadSixPeriod.choices ((4/5 : ℝ)*v) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,Fintype.mem_piFinset.mpr (fun i => ?_)⟩,
      Nat.squarefree_mul_iff.mpr ⟨Nat.prime_two.coprime_iff_not_dvd.mpr h2d,
        Nat.prime_two.squarefree,hsprod⟩,?_,?_⟩
    · exact (mem_logPrimes_iff _ _ _).mpr ⟨Nat.prime_two,by norm_num; positivity,
        by norm_num only [Nat.cast_ofNat,zero_add]; linarith [Real.log_two_lt_d9]⟩
    · exact (mem_logPrimes_iff _ _ _).mpr ⟨hqp i,by linarith [hql i],by linarith [hqu i]⟩
    · change (56/125 : ℝ)*((4/5 : ℝ)*v) < Real.log a
      linarith
    · change Real.log a ≤ (3/5 : ℝ)*((4/5 : ℝ)*v)
      linarith
  have ha : a ∈ cofactors v := Finset.mem_union_left _ (Finset.mem_filter.mpr
    ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(2,q),hrq,rfl⟩),hal⟩)
  have hpa : (1/4 : ℝ)*N ≤ v-Real.pi/|y|-Real.log a := by linarith
  have hpmass := (hlast _ hpa).1
  have he : 0 < Real.exp (2*Real.pi/|y|)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hH)
  obtain ⟨p,hp⟩ := hne _ _ ((by positivity : 0 < (1-1/2 : ℝ)*(Real.exp (2*Real.pi/|y|)-1)*
    Real.exp (v-Real.pi/|y|-Real.log a)).trans_le hpmass)
  refine ⟨a*p,mem_population_sdiff_of_transition (by linarith) hy ha (by linarith) hp,p,?_,?_⟩
  · have hg := fibre_geometry (by linarith : 100 ≤ v) hy ha hp
    have hh : p ∈ (p*a).primeFactors := hg.1.mem_primeFactors (dvd_mul_right p a) hg.2.2.1.ne_zero
    simpa only [Nat.mul_comm a p] using hh
  · have hg := fibre_geometry (by linarith : 100 ≤ v) hy ha hp
    have hl : Real.log (a*p : ℕ) = Real.log a+Real.log p := by
      rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast (cofactor_data ha).1.ne_zero)
        (by exact_mod_cast hg.1.ne_zero)]
    have hb := (logPrimes_bounds hp).2.1
    rw [hl]
    linarith

/-- The signed payment strictly enlarges the earlier actual population. -/
theorem eventually_added_population_nonempty {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, (N : ℝ) ≤ v →
      (population v y\ZetaRieszSixCofactorPeriod.population v y).Nonempty := by
  filter_upwards [eventually_added_population_crosses_transition hy] with N hN v hv
  obtain ⟨n,hn,_⟩ := hN v hv
  exact ⟨n,hn⟩

end
end RiemannGaussian.ZetaRieszTransitionSixPeriod
