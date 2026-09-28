/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszBroadSixPeriod
import RiemannGaussian.ZetaRieszWideSixAllocation

/-!
# Wider signed six-prime payment at the local radial scale

The extra cofactor band reaches owner shares near 0.59. Its allocation
cost is paid relative to the actual local prime-period budget. No
source-normalized decay of that slower allocation rate is asserted.
-/
namespace RiemannGaussian.ZetaRieszWideSixPeriod
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszMacroPrimeWindows
open ZetaSquarefreeRieszWindows ZetaRieszTriplePrime

/-- A union of two actually counted cofactor bands, with overlap counted once. -/
def cofactors (v : ℝ) : Finset ℕ :=
  (ZetaRieszBroadSixPeriod.cofactors v ∪
    ZetaRieszBroadSixPeriod.cofactors ((4/5 : ℝ)*v)).filter
      (fun a => (41/100 : ℝ)*v < Real.log a)

/-- The unchanged full largest-prime phase period over the wider cofactor set. -/
def population (v y : ℝ) : Finset ℕ := (cofactors v).biUnion (fun a =>
  (logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)).image (fun p => a*p))

private theorem cofactor_data {v : ℝ} {a : ℕ} (ha : a ∈ cofactors v) :
    Squarefree a ∧ a.primeFactors.card = 5 ∧ Real.log a.minFac ≤ (39/100 : ℝ)*v ∧
      (41/100 : ℝ)*v < Real.log a ∧ Real.log a ≤ (3/5 : ℝ)*v ∧
      (∀ p ∈ a.primeFactors, Real.log p ≤ (39/100 : ℝ)*v) := by
  obtain ⟨ha,hlo⟩ := Finset.mem_filter.mp ha
  rcases Finset.mem_union.mp ha with ha | ha
  · have h := ZetaRieszBroadSixPeriod.cofactor_geometry ha
    exact ⟨h.1,h.2.1,h.2.2.1,hlo,h.2.2.2.2.1,h.2.2.2.2.2⟩
  · have h := ZetaRieszBroadSixPeriod.cofactor_geometry ha
    have hv : 0 ≤ v := by nlinarith [Real.log_natCast_nonneg a,h.2.2.2.2.1]
    refine ⟨h.1,h.2.1,by nlinarith [h.2.2.1],hlo,by nlinarith [h.2.2.2.2.1],?_⟩
    intro p hp
    nlinarith [h.2.2.2.2.2 p hp]

/-- The selected six-prime integers have unique largest-prime ownership,
all original radial bounds, and no prime beyond the allocation-safe share. -/
theorem fibre_geometry {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    {a p : ℕ} (ha : a ∈ cofactors v)
    (hp : p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)) :
    p.Prime ∧ (∀ q ∈ a.primeFactors, q < p) ∧ Squarefree (p*a) ∧
      (p*a).primeFactors.card = 6 ∧
      v-Real.pi/|y| < Real.log (p*a : ℕ) ∧ Real.log (p*a : ℕ) ≤ v+Real.pi/|y| ∧
      (∀ q ∈ (p*a).primeFactors, Real.log q ≤ (591/1000 : ℝ)*Real.log (p*a : ℕ)) := by
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
  have hpmax : Real.log p ≤ (591/1000 : ℝ)*Real.log (p*a : ℕ) := by
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

/-- Twice the already counted logarithmic cofactor constant. -/
def logMassConstant : ℝ := 2*ZetaRieszBroadSixPeriod.logMassConstant
/-- Twice the already counted unweighted cofactor constant. -/
def variationConstant : ℝ := 2*ZetaRieszBroadSixPeriod.variationConstant

private theorem mass_constants_pos : 0 < logMassConstant ∧ 0 < variationConstant := by
  have h := ZetaRieszBroadSixPeriod.mass_constants_pos
  exact ⟨mul_pos (by norm_num) h.1,mul_pos (by norm_num) h.2⟩

private theorem cofactor_union_mass (v : ℝ) (f : ℕ → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (∑ a ∈ cofactors v, f a) ≤
      (∑ a ∈ ZetaRieszBroadSixPeriod.cofactors v, f a)+
      ∑ a ∈ ZetaRieszBroadSixPeriod.cofactors ((4/5 : ℝ)*v), f a := by
  apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun a _ _ => hf a)).trans
  have h : (∑ a ∈ ZetaRieszBroadSixPeriod.cofactors v ∪
      ZetaRieszBroadSixPeriod.cofactors ((4/5 : ℝ)*v), f a)+
      (∑ a ∈ ZetaRieszBroadSixPeriod.cofactors v ∩
        ZetaRieszBroadSixPeriod.cofactors ((4/5 : ℝ)*v), f a) =
      (∑ a ∈ ZetaRieszBroadSixPeriod.cofactors v, f a)+
        ∑ a ∈ ZetaRieszBroadSixPeriod.cofactors ((4/5 : ℝ)*v), f a :=
    Finset.sum_union_inter
  have hpos := Finset.sum_nonneg (s := ZetaRieszBroadSixPeriod.cofactors v ∩
    ZetaRieszBroadSixPeriod.cofactors ((4/5 : ℝ)*v)) (fun a _ => hf a)
  linarith only [h,hpos]

/-- Actual logarithmic cofactor mass; overlapping bands are overcounted
only for this positive counting bound. -/
theorem cofactor_log_mass {v : ℝ} (hv : 0 < v) :
    (∑ a ∈ cofactors v, Real.log a.minFac*(a : ℝ)⁻¹) ≤ logMassConstant*v := by
  have h := cofactor_union_mass v (fun a => Real.log a.minFac*(a : ℝ)⁻¹)
    (fun a => by positivity)
  have h1 := ZetaRieszBroadSixPeriod.cofactor_log_mass hv
  have h2 := ZetaRieszBroadSixPeriod.cofactor_log_mass (show 0 < (4/5 : ℝ)*v by positivity)
  have hc := ZetaRieszBroadSixPeriod.mass_constants_pos.1
  dsimp only [logMassConstant]
  nlinarith only [h,h1,h2,mul_pos hc hv]

/-- The cutoff-variation cofactor mass remains at most square-root size. -/
theorem cofactor_mass {v : ℝ} (hv : 0 < v) :
    (∑ a ∈ cofactors v, (a : ℝ)⁻¹) ≤ variationConstant*v^(1/2 : ℝ) := by
  have h := cofactor_union_mass v (fun a => (a : ℝ)⁻¹) (fun a => by positivity)
  have h1 := ZetaRieszBroadSixPeriod.cofactor_mass hv
  have h2 := ZetaRieszBroadSixPeriod.cofactor_mass (show 0 < (4/5 : ℝ)*v by positivity)
  have hp := Real.rpow_le_rpow (show 0 ≤ (4/5 : ℝ)*v by positivity)
    (show (4/5 : ℝ)*v ≤ v by linarith) (by norm_num : (0 : ℝ) ≤ 1/2)
  have hc := ZetaRieszBroadSixPeriod.mass_constants_pos.2
  have hh := mul_le_mul_of_nonneg_left hp hc.le
  dsimp only [variationConstant]
  linarith only [h,h1,h2,hh]

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
phase. The two charges are its central signed mass and its actual cutoff
variation, not termwise absolute phases. -/
theorem fibre_bound {m N : ℕ} {v y L V η : ℝ}
    (hv : 100 ≤ v) (hy : 54 ≤ |y|) (hLl : (67/100 : ℝ)*v ≤ L)
    (hV : 0 ≤ V) (hη : 0 ≤ η) {a : ℕ} (ha : a ∈ cofactors v)
    (hperiod :
      let w := fun p : ℕ => Real.exp (-(Real.log p+Real.log a)/2)*
        (Real.log p+Real.log a)^(N+1)/N.factorial
      let D := logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)
      |∑ p ∈ D, w p*(p : ℝ)⁻¹*Real.cos (y*(Real.log p+Real.log a))| ≤
        (64*η)*m*V*v*(Real.pi/(4*m*|y|))/(v-Real.log a) ∧
      (∑ p ∈ D, w p*(p : ℝ)⁻¹) ≤
        16*m*V*v*(Real.pi/(4*m*|y|))/(v-Real.log a)) :
    |(∑ p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|),
        SquarefreeVaughanLogSource.coefficient L (p*a)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re| ≤
      ((m : ℝ)*V*(Real.pi/(4*m*|y|)))*
        ((1000*η/v)*(Real.log a.minFac*(a : ℝ)⁻¹)+(100/v)*(a : ℝ)⁻¹) := by
  let h := Real.pi/(4*m*|y|)
  let D := logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)
  let w := fun p : ℕ => (Real.exp (-(Real.log p+Real.log a)/2)*
    (Real.log p+Real.log a)^(N+1)/N.factorial)*(p : ℝ)⁻¹
  let g := fun p : ℕ => w p*Real.cos (y*(Real.log p+Real.log a))
  let R := fun p : ℕ => VaughanLogAverage.riesz (Real.log p+Real.log a-L) a
  let R₀ := VaughanLogAverage.riesz (v-L) a
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
  have hR (p : ℕ) (hp : p ∈ D) : |R p-R₀| ≤ 1 := by
    have hb := (logPrimes_bounds hp).2
    have hbu := hb.2
    rw [mul_div_assoc] at hbu
    have he : |(Real.log p+Real.log a-L)-(v-L)| ≤ Real.pi/|y| := by
      apply abs_le.mpr
      constructor <;> linarith [hb.1]
    have hh := cofactor_response_variation ha (Real.log p+Real.log a-L) (v-L)
    dsimp [R,R₀]
    linarith
  have hs := signed_perturbation D R g w R₀ 1 (by norm_num) hw hg hR
  have he : (∑ p ∈ D, SquarefreeVaughanLogSource.coefficient L (p*a)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re =
      -(1/L/a)*(∑ p ∈ D, R p*g p) := by
    rw [Complex.re_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [re_response_atom hv hy hLl ha hp]
    dsimp [R,g,w]
    ring
  change |(∑ p ∈ D, SquarefreeVaughanLogSource.coefficient L (p*a)*
    zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re| ≤ _
  rw [he,abs_mul,abs_neg,abs_of_nonneg (show 0 ≤ 1/L/a by positivity)]
  have hrc := cofactor_response_bound ha (v-L)
  have hS : |∑ p ∈ D, R p*g p| ≤
      (3*Real.log a.minFac)*((64*η)*m*V*v*h/(v-Real.log a))+
        16*m*V*v*h/(v-Real.log a) := by
    apply hs.trans
    have hh := mul_le_mul hrc hperiod.1 (abs_nonneg _) (by positivity : 0 ≤ 3*Real.log a.minFac)
    exact add_le_add hh (by simpa only [one_mul] using hperiod.2)
  apply (mul_le_mul_of_nonneg_left hS (show 0 ≤ 1/L/a by positivity)).trans
  have hden : v*v ≤ 4*L*(v-Real.log a) := by
    have hh := mul_le_mul hLl (show (2/5 : ℝ)*v ≤ v-Real.log a by linarith [hd.2.2.2.2.1])
      (by positivity) (by positivity : 0 ≤ L)
    nlinarith
  have hfrac : v/(L*(v-Real.log a)) ≤ 4/v :=
    (div_le_div_iff₀ (mul_pos hL hab) hv0).mpr (by nlinarith only [hden])
  have hnonneg : 0 ≤ (m : ℝ)*V*h*(a : ℝ)⁻¹ := by dsimp [h]; positivity
  have hm := mul_le_mul_of_nonneg_right hfrac
    (show 0 ≤ ((m : ℝ)*V*h*(a : ℝ)⁻¹)*(192*η*Real.log a.minFac+16) by positivity)
  have hsmall : (192*η*Real.log a.minFac+16)*4 ≤ 1000*η*Real.log a.minFac+100 := by
    nlinarith [mul_nonneg hη (Real.log_natCast_nonneg a.minFac)]
  have ht := mul_le_mul_of_nonneg_left hsmall (div_nonneg hnonneg hv0.le)
  dsimp only [h] at hm ht ⊢
  simp only [div_eq_mul_inv,mul_inv_rev] at hm ht ⊢
  ring_nf at hm ht ⊢
  linarith only [hm,ht]

/-- A genuine signed population bound, arbitrarily small relative to the
local radial weight. All cofactor primes and all cutoff chambers are
included. This is not a source-normalized decay claim. -/
theorem eventually_raw_population_small {y ε : ℝ} (hy : 54 ≤ |y|) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ v L : ℝ,
      2*(N : ℝ) ≤ v → v ≤ 2*N+1 → Real.cos (y*v) = -1 →
      (67/100 : ℝ)*v ≤ L →
      |(∑ n ∈ population v y, SquarefreeVaughanLogSource.coefficient L n*
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
  have hr : Tendsto (fun v : ℝ => 100*variationConstant*v^(-(1/2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).const_mul
      (100*variationConstant)
  obtain ⟨v₀,hv₀⟩ := eventually_atTop.mp (hr.eventually_lt_const (show 0 < ε/2 by positivity))
  filter_upwards [ZetaRieszSaddlePeriod.eventually_factorial_period hm hy
      (by norm_num : (0 : ℝ) < 1/2) hη hηu hsmall hphase,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop v₀,
    eventually_ge_atTop (1000 : ℕ)] with N hN hNv hlarge v L hv hvu hpeak hLl
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hv100 : 100 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  have hvlarge : v₀ ≤ v := by linarith
  obtain ⟨V,hV,hbase,_,hperiod⟩ := hN v hv hvu hpeak
  let h := Real.pi/(4*m*|y|)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hy0 : 0 < |y| := by linarith
  have hh : 0 < h := by dsimp [h]; positivity
  have hrow (a : ℕ) (ha : a ∈ cofactors v) := fibre_bound (N := N) hv100 hy hLl hV.le hη.le ha
    (hperiod (Real.log a) (by have hd := cofactor_data ha; linarith [hd.2.2.2.2.1]))
  have hsum : |(∑ n ∈ population v y, SquarefreeVaughanLogSource.coefficient L n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re| ≤
      ((m : ℝ)*V*h)*((1000*η/v)*(logMassConstant*v)+
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
  have hbudget : (1000*η/v)*(logMassConstant*v)+(100/v)*(variationConstant*v^(1/2 : ℝ)) ≤ ε := by
    have he : (1000*η/v)*(logMassConstant*v)+(100/v)*(variationConstant*v^(1/2 : ℝ)) =
        1000*η*logMassConstant+100*variationConstant*(v^(1/2 : ℝ)/v) := by field_simp
    rw [he,hrat]
    linarith [hv₀ v hvlarge]
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
    (hmax : ∀ p ∈ n.primeFactors, Real.log p ≤ (591/1000 : ℝ)*Real.log n) :
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
and satisfies the unchanged radial and allocation-safe share conditions. -/
theorem population_data {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|) {n : ℕ}
    (hn : n ∈ population v y) :
    Squarefree n ∧ n.primeFactors.card = 6 ∧
      v-Real.pi/|y| < Real.log n ∧ Real.log n ≤ v+Real.pi/|y| ∧
      (∀ a ∈ n.primeFactors, Real.log a ≤ (591/1000 : ℝ)*Real.log n) := by
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

private theorem sum_population_real {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (f : ℕ → ℝ) :
    (∑ n ∈ population v y, f n) = ∑ a ∈ cofactors v,
      ∑ p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|), f (p*a) := by
  have h := congrArg Complex.re (sum_population hv hy (fun n => (f n : ℂ)))
  simpa only [Complex.re_sum,Complex.ofReal_re] using h

private theorem norm_response_atom {v y L : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (hLl : (67/100 : ℝ)*v ≤ L)
    {a p : ℕ} (ha : a ∈ cofactors v)
    (hp : p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)) (N : ℕ) :
    ‖SquarefreeVaughanLogSource.coefficient L (p*a)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)‖ =
      (|VaughanLogAverage.riesz (Real.log p+Real.log a-L) a|/L/a)*
        ((Real.exp (-(Real.log p+Real.log a)/2)*(Real.log p+Real.log a)^(N+1)/N.factorial)*
          (p : ℝ)⁻¹) := by
  have hpp := (logPrimes_bounds hp).1
  have ha0 := (cofactor_data ha).1.ne_zero
  have hL : 0 < L := by linarith
  have hlog : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hpp.ne_zero) (by exact_mod_cast ha0)]
  have hex : Real.exp (-(3/2 : ℝ)*Real.log (p*a : ℕ)) =
      Real.exp (-Real.log (p*a : ℕ)/2)*(p : ℝ)⁻¹*(a : ℝ)⁻¹ := by
    rw [show -(3/2 : ℝ)*Real.log (p*a : ℕ) =
      -Real.log (p*a : ℕ)/2-Real.log (p*a : ℕ) by ring,
      Real.exp_sub,Real.exp_log (by exact_mod_cast Nat.mul_pos hpp.pos (Nat.pos_of_ne_zero ha0)),
      Nat.cast_mul]
    ring
  rw [norm_mul,coefficient_eq_response hv hy hLl ha hp,
    Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_neg,abs_div,
    abs_of_nonneg (Real.log_natCast_nonneg _),abs_of_pos hL,norm_zetaPrimeLogKernel]
  have hre : (3/2+Complex.I*y : ℂ).re = 3/2 := by norm_num [Complex.mul_re]
  rw [hre]
  change (Real.log (p*a : ℕ)/L*|VaughanLogAverage.riesz (Real.log (p*a : ℕ)-L) a|)*
    ((Real.log (p*a : ℕ))^N/N.factorial*Real.exp (-(3/2 : ℝ)*Real.log (p*a : ℕ))) = _
  rw [hex,hlog,pow_succ]
  ring

/-- Only the assigned fraction is estimated in norm. Its underlying
actual prime population has a bounded relative radial mass. -/
theorem fibre_norm_bound {m N : ℕ} {v y L V : ℝ}
    (hv : 100 ≤ v) (hy : 54 ≤ |y|) (hLl : (67/100 : ℝ)*v ≤ L)
    (hV : 0 ≤ V) {a : ℕ} (ha : a ∈ cofactors v)
    (hperiod :
      (∑ p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|),
        (Real.exp (-(Real.log p+Real.log a)/2)*
          (Real.log p+Real.log a)^(N+1)/N.factorial)*(p : ℝ)⁻¹) ≤
        16*m*V*v*(Real.pi/(4*m*|y|))/(v-Real.log a)) :
    (∑ p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|),
      ‖SquarefreeVaughanLogSource.coefficient L (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)‖) ≤
      (192/v)*((m : ℝ)*V*(Real.pi/(4*m*|y|)))*(Real.log a.minFac*(a : ℝ)⁻¹) := by
  let h := Real.pi/(4*m*|y|)
  have hd := cofactor_data ha
  have hv0 : 0 < v := by linarith
  have hL : 0 < L := by linarith
  have haR : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero hd.1.ne_zero
  have hab : 0 < v-Real.log a := by linarith [hd.2.2.2.2.1]
  have hpoint (p : ℕ) (hp : p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)) :
      ‖SquarefreeVaughanLogSource.coefficient L (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)‖ ≤
      (3*Real.log a.minFac/L/a)*
        ((Real.exp (-(Real.log p+Real.log a)/2)*(Real.log p+Real.log a)^(N+1)/N.factorial)*
          (p : ℝ)⁻¹) := by
    rw [norm_response_atom hv hy hLl ha hp]
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right
        (cofactor_response_bound ha _) hL.le) haR.le) (by positivity)
  apply (Finset.sum_le_sum hpoint).trans
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left hperiod (by positivity : 0 ≤ 3*Real.log a.minFac/L/a)).trans
  have hden : v*v ≤ 4*L*(v-Real.log a) := by
    have hh := mul_le_mul hLl (show (2/5 : ℝ)*v ≤ v-Real.log a by linarith [hd.2.2.2.2.1])
      (by positivity) (by positivity : 0 ≤ L)
    nlinarith
  have hfrac : v/(L*(v-Real.log a)) ≤ 4/v :=
    (div_le_div_iff₀ (mul_pos hL hab) hv0).mpr (by nlinarith only [hden])
  have hm := mul_le_mul_of_nonneg_right hfrac
    (show 0 ≤ 48*((m : ℝ)*V*h)*(Real.log a.minFac*(a : ℝ)⁻¹) by dsimp [h]; positivity)
  dsimp only [h] at hm
  simp only [div_eq_mul_inv,mul_inv_rev] at hm ⊢
  ring_nf at hm ⊢
  exact hm

/-- The literal residual population is arbitrarily small relative to
its local radial budget, with the old allocation paid on this same
population. There is no source-scale envelope loss. -/
theorem eventually_residual_population_small {y ε : ℝ} (hy : 54 ≤ |y|) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (v L : ℝ),
      2*(N : ℝ) ≤ v → v ≤ 2*N+1 → Real.cos (y*v) = -1 →
      (67/100 : ℝ)*v ≤ L →
      |(∑ n ∈ population v y, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re| ≤
        ε*(Real.pi/(4*|y|))*(Real.exp (-v/2)*v^N/N.factorial) := by
  obtain ⟨m,hm,hsmall,hphase⟩ := ZetaRieszBroadSixPeriod.exists_precise_mesh hy
    (by norm_num : (0 : ℝ) < 1/10000)
  have ht := ZetaRieszWideSixAllocation.tendsto_allocation_factor.const_mul (192*logMassConstant)
  simp only [mul_zero] at ht
  filter_upwards [eventually_raw_population_small hy (show 0 < ε/2 by positivity),
    ZetaRieszSaddlePeriod.eventually_factorial_period hm hy
      (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (0 : ℝ) < 1/10000)
      (by norm_num) hsmall hphase,
    ht.eventually_lt_const (show 0 < ε/2 by positivity),
    eventually_ge_atTop (1000 : ℕ)] with N hraw hN htail hlarge A v L hv hvu hpeak hLl
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hv100 : 100 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  obtain ⟨V,hV,hbase,_,hperiod⟩ := hN v hv hvu hpeak
  let h := Real.pi/(4*m*|y|)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hy0 : 0 < |y| := by linarith
  have hh : 0 < h := by dsimp [h]; positivity
  let f := fun n => SquarefreeVaughanLogSource.coefficient L n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hmass : (∑ n ∈ population v y, ‖f n‖) ≤ 192*logMassConstant*((m : ℝ)*V*h) := by
    rw [sum_population_real hv100 hy]
    have hrow (a : ℕ) (ha : a ∈ cofactors v) := fibre_norm_bound (N := N) hv100 hy hLl hV.le ha
      (hperiod (Real.log a) (by have hd := cofactor_data ha; linarith [hd.2.2.2.2.1])).2
    apply (Finset.sum_le_sum hrow).trans
    rw [← Finset.mul_sum]
    apply (mul_le_mul_of_nonneg_left (cofactor_log_mass hv0) (by positivity : 0 ≤ (192/v)*((m : ℝ)*V*h))).trans_eq
    field_simp
  have hassigned : ‖∑ n ∈ population v y, ZetaRieszJointAllocation.assignedCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (ε/2)*(Real.pi/(4*|y|))*(Real.exp (-v/2)*v^N/N.factorial) := by
    apply (norm_sum_le _ _).trans
    have hpoint (n : ℕ) (hn : n ∈ population v y) :
        ‖ZetaRieszJointAllocation.assignedCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        (6*Real.exp (-(N : ℝ)/100000))*‖f n‖ := by
      have hd := population_data hv100 hy hn
      rw [ZetaRieszJointAllocation.assignedCoefficient,mul_assoc,norm_mul,
        Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (ZetaRieszJointAllocation.boundedShare_bounds A N n).1]
      exact mul_le_mul_of_nonneg_right
        (ZetaRieszWideSixAllocation.boundedShare_six_le A N hd.1 hd.2.1 hd.2.2.2.2) (norm_nonneg _)
    apply (Finset.sum_le_sum hpoint).trans
    rw [← Finset.mul_sum]
    apply (mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 6*Real.exp (-(N : ℝ)/100000))).trans
    have he : (m : ℝ)*h = Real.pi/(4*|y|) := by dsimp [h]; field_simp
    calc
      _ = (192*logMassConstant*(6*Real.exp (-(N : ℝ)/100000)))*((m : ℝ)*V*h) := by ring
      _ ≤ (ε/2)*((m : ℝ)*V*h) := mul_le_mul_of_nonneg_right htail.le (by positivity)
      _ = (ε/2)*(Real.pi/(4*|y|))*V := by rw [← he]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbase (by positivity)
  have he : (∑ n ∈ population v y, ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n) =
      (∑ n ∈ population v y, f n)-∑ n ∈ population v y,
        ZetaRieszJointAllocation.assignedCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    simp only [ZetaRieszJointAllocation.residualCoefficient,ZetaRieszJointAllocation.assignedCoefficient,
      Complex.ofReal_sub,Complex.ofReal_one,f]
    ring
  rw [he,Complex.sub_re]
  have hb := (abs_sub _ _).trans (add_le_add (hraw v L hv hvu hpeak hLl)
    ((Complex.abs_re_le_norm _).trans hassigned))
  linarith only [hb]

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
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1000 : ℕ)), eventually_ge_atTop (32 : ℕ)] with j hraw hL hN hj
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
  have hb := hraw (ZetaRieszAnnulusJoint.intermediatePrimes u N) v L hslo hshi hv hLl
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


/-- The previous broad payment is contained in the new payment, so
its labels and its credit must never be counted twice. -/
theorem broad_population_subset {v y : ℝ} (_hv : 0 ≤ v) :
    ZetaRieszBroadSixPeriod.population v y ⊆ population v y := by
  intro n hn
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
  have hd := ZetaRieszBroadSixPeriod.cofactor_geometry ha
  exact Finset.mem_biUnion.mpr ⟨a,Finset.mem_filter.mpr
    ⟨Finset.mem_union_left _ ha,by nlinarith [hd.2.2.2.1]⟩,hn⟩

/-- The wider payment is a nonempty actual prime population eventually. -/
theorem eventually_population_nonempty {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, (N : ℝ) ≤ v → (population v y).Nonempty := by
  filter_upwards [ZetaRieszBroadSixPeriod.eventually_population_nonempty hy] with N hN v hv
  exact (hN v hv).mono (broad_population_subset ((Nat.cast_nonneg N).trans hv))


/-- The checked cofactor geometry, for further signed period payments
that contain this population without counting it twice. -/
theorem cofactor_geometry {v : ℝ} {a : ℕ} (ha : a ∈ cofactors v) :
    Squarefree a ∧ a.primeFactors.card = 5 ∧ Real.log a.minFac ≤ (39/100 : ℝ)*v ∧
      (41/100 : ℝ)*v < Real.log a ∧ Real.log a ≤ (3/5 : ℝ)*v ∧
      (∀ p ∈ a.primeFactors, Real.log p ≤ (39/100 : ℝ)*v) :=
  cofactor_data ha

end
end RiemannGaussian.ZetaRieszWideSixPeriod
