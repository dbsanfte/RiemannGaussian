/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSixPrimePeriod
import RiemannGaussian.ZetaRieszSaddlePeriod
import RiemannGaussian.ZetaRieszPrimeFractionalBudget

/-!
# Broad six-prime cancellation with the moving Riesz coefficient

The largest-prime phase period is retained in full. Cofactor logarithms
lie between `56v/125` and `3v/5`, and each cofactor prime has log at most
`39v/100`. No least-prime lower cutoff or coefficient-sign restriction is
made. Cutoff variation is paid after the signed period is summed.
-/

namespace RiemannGaussian.ZetaRieszBroadSixPeriod
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszMacroPrimeWindows
open ZetaSquarefreeRieszWindows ZetaRieszTriplePrime

/-- All cofactor primes, including fixed small primes. -/
def allPrimes (v : ℝ) : Finset ℕ := logPrimes 0 ((39/100 : ℝ)*v)

/-- A five-prime tuple; squarefreeness removes repeated primes. -/
def cofactor (rq : ℕ × (Fin 4 → ℕ)) : ℕ := rq.1 * ∏ i, rq.2 i

/-- The broad cofactor band, without any sign or least-prime cutoff. -/
def choices (v : ℝ) : Finset (ℕ × (Fin 4 → ℕ)) :=
  ((allPrimes v).product (Fintype.piFinset (fun _ : Fin 4 => allPrimes v))).filter
    (fun rq => Squarefree (cofactor rq) ∧ (56/125 : ℝ)*v < Real.log (cofactor rq) ∧
      Real.log (cofactor rq) ≤ (3/5 : ℝ)*v)

/-- Actual cofactor integers, counting each only once. -/
def cofactors (v : ℝ) : Finset ℕ := (choices v).image cofactor

/-- Actual six-prime integers in the full largest-prime phase period. -/
def population (v y : ℝ) : Finset ℕ := (cofactors v).biUnion (fun a =>
  (logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)).image (fun p => a*p))

private theorem choice_data {v : ℝ} {rq : ℕ × (Fin 4 → ℕ)}
    (hrq : rq ∈ choices v) :
    rq.1.Prime ∧ 0 < Real.log rq.1 ∧ Real.log rq.1 ≤ (39/100 : ℝ)*v ∧
      (∀ i, (rq.2 i).Prime ∧ 0 < Real.log (rq.2 i) ∧
        Real.log (rq.2 i) ≤ (39/100 : ℝ)*v) ∧ Squarefree (cofactor rq) := by
  obtain ⟨hmem,hs,_,_⟩ := Finset.mem_filter.mp hrq
  obtain ⟨hr,hq⟩ := Finset.mem_product.mp hmem
  have hrb := logPrimes_bounds hr
  refine ⟨hrb.1,hrb.2.1,by simpa only [zero_add] using hrb.2.2,?_,hs⟩
  intro i
  simpa only [allPrimes,zero_add] using logPrimes_bounds (Fintype.mem_piFinset.mp hq i)

private theorem cofactor_factor {v : ℝ} {rq : ℕ × (Fin 4 → ℕ)}
    (hrq : rq ∈ choices v) {p : ℕ} (hp : p.Prime) (hd : p ∣ cofactor rq) :
    p = rq.1 ∨ ∃ i, p = rq.2 i := by
  rcases hp.dvd_mul.mp hd with hd | hd
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (choice_data hrq).1).mp hd)
  · obtain ⟨i,_,hi⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
    exact Or.inr ⟨i,(Nat.prime_dvd_prime_iff_eq hp ((choice_data hrq).2.2.2.1 i).1).mp hi⟩

private theorem cofactor_data {v : ℝ}  {a : ℕ} (ha : a ∈ cofactors v) :
    Squarefree a ∧ a.primeFactors.card = 5 ∧ Real.log a.minFac ≤ (39/100 : ℝ)*v ∧
      (56/125 : ℝ)*v < Real.log a ∧ Real.log a ≤ (3/5 : ℝ)*v ∧
      (∀ p ∈ a.primeFactors, Real.log p ≤ (39/100 : ℝ)*v) := by
  obtain ⟨rq,hrq,rfl⟩ := Finset.mem_image.mp ha
  have hd := choice_data hrq
  have hcount : ArithmeticFunction.cardFactors (cofactor rq) = 5 := by
    simp [cofactor,Fin.prod_univ_four,ArithmeticFunction.cardFactors_mul,
      hd.1.ne_zero,(hd.2.2.2.1 0).1.ne_zero,(hd.2.2.2.1 1).1.ne_zero,
      (hd.2.2.2.1 2).1.ne_zero,(hd.2.2.2.1 3).1.ne_zero,
      ArithmeticFunction.cardFactors_apply_prime hd.1,
      ArithmeticFunction.cardFactors_apply_prime (hd.2.2.2.1 0).1,
      ArithmeticFunction.cardFactors_apply_prime (hd.2.2.2.1 1).1,
      ArithmeticFunction.cardFactors_apply_prime (hd.2.2.2.1 2).1,
      ArithmeticFunction.cardFactors_apply_prime (hd.2.2.2.1 3).1]
  have hcard : (cofactor rq).primeFactors.card = 5 := by
    have he : (cofactor rq).primeFactors.card = (cofactor rq).primeFactorsList.length :=
      List.toFinset_card_of_nodup hd.2.2.2.2.nodup_primeFactorsList
    simpa only [ArithmeticFunction.cardFactors_apply,← he] using hcount
  have hmin : Real.log (cofactor rq).minFac ≤ Real.log rq.1 :=
    Real.log_le_log (by exact_mod_cast Nat.minFac_pos _) (by exact_mod_cast (Nat.minFac_le_of_dvd hd.1.two_le (dvd_mul_right rq.1 (∏ i, rq.2 i))))
  have hb := (Finset.mem_filter.mp hrq).2.2
  refine ⟨hd.2.2.2.2,hcard,hmin.trans hd.2.2.1,hb.1,hb.2,?_⟩
  intro p hp
  rcases cofactor_factor hrq (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp) with h | ⟨i,h⟩
  · simpa only [h] using hd.2.2.1
  · simpa only [h] using (hd.2.2.2.1 i).2.2

/-- The selected six-prime integers have unique largest-prime ownership,
all original radial bounds, and no prime beyond the allocation-safe share. -/
theorem fibre_geometry {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    {a p : ℕ} (ha : a ∈ cofactors v)
    (hp : p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)) :
    p.Prime ∧ (∀ q ∈ a.primeFactors, q < p) ∧ Squarefree (p*a) ∧
      (p*a).primeFactors.card = 6 ∧
      v-Real.pi/|y| < Real.log (p*a : ℕ) ∧ Real.log (p*a : ℕ) ≤ v+Real.pi/|y| ∧
      (∀ q ∈ (p*a).primeFactors, Real.log q ≤ (9/16 : ℝ)*Real.log (p*a : ℕ)) := by
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
  have hpmax : Real.log p ≤ (9/16 : ℝ)*Real.log (p*a : ℕ) := by
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


private theorem prime_moment {v e : ℝ} (hv : 0 < v) (he : 0 < e) :
    (∑ p ∈ allPrimes v, (Real.log p)^e*(p : ℝ)⁻¹) ≤
      ZetaRieszPrimeFractionalBudget.momentConstant e*v^e := by
  have hh := ZetaRieszPrimeFractionalBudget.prime_fractional_log_mass_le (allPrimes v) hv he
    (by intro p hp; have hb := logPrimes_bounds hp; exact ⟨hb.1,by linarith [hb.2.2]⟩)
  have heq (p : ℕ) (hp : p ∈ allPrimes v) : Real.exp (-Real.log p) = (p : ℝ)⁻¹ := by
    rw [Real.exp_neg,Real.exp_log (by exact_mod_cast (logPrimes_bounds hp).1.pos)]
  calc
    _ = ∑ p ∈ allPrimes v, (Real.log p)^e*Real.exp (-Real.log p) :=
      Finset.sum_congr rfl (fun p hp => by rw [heq p hp])
    _ ≤ _ := hh

private theorem weighted_tuple_sum (v : ℝ) (f g : ℕ → ℝ) :
    (∑ rq ∈ (allPrimes v).product (Fintype.piFinset (fun _ : Fin 4 => allPrimes v)),
      f rq.1*∏ i, g (rq.2 i)) =
      (∑ p ∈ allPrimes v, f p)*(∑ p ∈ allPrimes v, g p)^4 := by
  rw [Finset.product_eq_sprod,Finset.sum_product]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  congr 1
  exact (Finset.sum_pow' (allPrimes v) g 4).symm

/-- Finite cofactor counting constant, retaining the least-prime log. -/
def logMassConstant : ℝ :=
  ZetaRieszPrimeFractionalBudget.momentConstant (1/2)*
    (ZetaRieszPrimeFractionalBudget.momentConstant (1/8))^4

/-- Finite cofactor counting constant used only for cutoff variation. -/
def variationConstant : ℝ := (2*ZetaRieszPrimeFractionalBudget.momentConstant (1/10))^5

/-- Both actual counting constants are positive. -/
theorem mass_constants_pos : 0 < logMassConstant ∧ 0 < variationConstant := by
  have hhalf := ZetaRieszPrimeFractionalBudget.momentConstant_pos (by norm_num : (0 : ℝ) < 1/2)
  have heighth := ZetaRieszPrimeFractionalBudget.momentConstant_pos (by norm_num : (0 : ℝ) < 1/8)
  have htenth := ZetaRieszPrimeFractionalBudget.momentConstant_pos (by norm_num : (0 : ℝ) < 1/10)
  unfold logMassConstant variationConstant
  constructor <;> positivity

/-- The full cofactor population, with no lower prime cutoff, has the
correct linear logarithmic reciprocal mass. -/
theorem cofactor_log_mass {v : ℝ} (hv : 0 < v) :
    (∑ a ∈ cofactors v, Real.log a.minFac*(a : ℝ)⁻¹) ≤ logMassConstant*v := by
  let f := fun p : ℕ => (Real.log p)^(1/2 : ℝ)*(p : ℝ)⁻¹
  let g := fun p : ℕ => (Real.log p)^(1/8 : ℝ)*(p : ℝ)⁻¹
  have hpoint (rq : ℕ × (Fin 4 → ℕ)) (hrq : rq ∈ choices v) :
      Real.log (cofactor rq).minFac*(cofactor rq : ℝ)⁻¹ ≤ f rq.1*∏ i, g (rq.2 i) := by
    have hd := choice_data hrq
    have hc := (cofactor_data (Finset.mem_image.mpr ⟨rq,hrq,rfl⟩)).2.1
    have hn1 : cofactor rq ≠ 1 := by intro h; simp [h] at hc
    have ht : 0 < Real.log (cofactor rq).minFac := Real.log_pos
      (by exact_mod_cast (Nat.minFac_prime hn1).one_lt)
    have hmin (p : ℕ) (hp : p.Prime) (hpd : p ∣ cofactor rq) :
        Real.log (cofactor rq).minFac ≤ Real.log p :=
      Real.log_le_log (by exact_mod_cast Nat.minFac_pos _) (by exact_mod_cast Nat.minFac_le_of_dvd hp.two_le hpd)
    have hq (i : Fin 4) : rq.2 i ∣ cofactor rq :=
      (Finset.dvd_prod_of_mem (fun j : Fin 4 => rq.2 j) (Finset.mem_univ i)).trans (dvd_mul_left _ _)
    have hb := ZetaRieszPrimeFractionalBudget.minimum_le_weighted_product ht
      (hmin _ hd.1 (dvd_mul_right _ _)) (hmin _ (hd.2.2.2.1 0).1 (hq 0))
      (hmin _ (hd.2.2.2.1 1).1 (hq 1)) (hmin _ (hd.2.2.2.1 2).1 (hq 2))
      (hmin _ (hd.2.2.2.1 3).1 (hq 3))
    have hh := mul_le_mul_of_nonneg_right hb (show 0 ≤ (cofactor rq : ℝ)⁻¹ by positivity)
    dsimp only [f,g]
    simp only [cofactor,Fin.prod_univ_four,Nat.cast_mul,mul_inv_rev] at hh ⊢
    nlinarith only [hh]
  calc
    _ ≤ ∑ rq ∈ choices v, Real.log (cofactor rq).minFac*(cofactor rq : ℝ)⁻¹ :=
      Finset.sum_image_le_of_nonneg (fun a _ => by positivity)
    _ ≤ ∑ rq ∈ choices v, f rq.1*∏ i, g (rq.2 i) := Finset.sum_le_sum hpoint
    _ ≤ ∑ rq ∈ (allPrimes v).product (Fintype.piFinset (fun _ : Fin 4 => allPrimes v)),
        f rq.1*∏ i, g (rq.2 i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intro rq _ _; dsimp [f,g]; positivity)
    _ = (∑ p ∈ allPrimes v, f p)*(∑ p ∈ allPrimes v, g p)^4 := weighted_tuple_sum v f g
    _ ≤ (ZetaRieszPrimeFractionalBudget.momentConstant (1/2)*v^(1/2 : ℝ))*
        (ZetaRieszPrimeFractionalBudget.momentConstant (1/8)*v^(1/8 : ℝ))^4 := by
      exact mul_le_mul (prime_moment hv (by norm_num))
        (pow_le_pow_left₀ (by positivity) (prime_moment hv (by norm_num)) 4)
        (by positivity) (mul_nonneg (ZetaRieszPrimeFractionalBudget.momentConstant_pos (by norm_num : (0 : ℝ) < 1/2)).le (by positivity))
    _ = logMassConstant*v := by
      rw [mul_pow,← Real.rpow_mul_natCast hv.le]
      have he : v^(1/2 : ℝ)*v^((1/8 : ℝ)*4) = v := by
        rw [← Real.rpow_add hv]; norm_num
      calc
        _ = logMassConstant*(v^(1/2 : ℝ)*v^((1/8 : ℝ)*4)) := by unfold logMassConstant; ring
        _ = _ := by rw [he]

/-- The unweighted cofactor mass is at most a fixed square-root power.
It is used only after the signed prime period, to pay cutoff movement. -/
theorem cofactor_mass {v : ℝ} (hv : 0 < v) :
    (∑ a ∈ cofactors v, (a : ℝ)⁻¹) ≤ variationConstant*v^(1/2 : ℝ) := by
  have hprime : (∑ p ∈ allPrimes v, (p : ℝ)⁻¹) ≤
      (2*ZetaRieszPrimeFractionalBudget.momentConstant (1/10))*v^(1/10 : ℝ) := by
    have hpoint (p : ℕ) (hp : p ∈ allPrimes v) :
        (p : ℝ)⁻¹ ≤ 2*((Real.log p)^(1/10 : ℝ)*(p : ℝ)⁻¹) := by
      have hp0 := (logPrimes_bounds hp).1
      have hlo : (1/2 : ℝ) ≤ Real.log p := by
        have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
          (show (2 : ℝ) ≤ p by exact_mod_cast hp0.two_le)
        linarith [Real.log_two_gt_d9]
      have hb := (Real.self_le_rpow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num) (by norm_num : (1/10 : ℝ) ≤ 1)).trans
        (Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1/2) hlo (by norm_num : (0 : ℝ) ≤ 1/10))
      nlinarith [mul_le_mul_of_nonneg_right hb (show 0 ≤ (p : ℝ)⁻¹ by positivity)]
    calc
      _ ≤ ∑ p ∈ allPrimes v, 2*((Real.log p)^(1/10 : ℝ)*(p : ℝ)⁻¹) := Finset.sum_le_sum hpoint
      _ ≤ _ := by rw [← Finset.mul_sum]; nlinarith only [prime_moment hv (by norm_num : (0 : ℝ) < 1/10)]
  have hcover : (∑ a ∈ cofactors v, (a : ℝ)⁻¹) ≤ (∑ p ∈ allPrimes v, (p : ℝ)⁻¹)^5 := by
    calc
      _ ≤ ∑ rq ∈ choices v, (cofactor rq : ℝ)⁻¹ :=
        Finset.sum_image_le_of_nonneg (s := choices v) (g := cofactor)
          (f := fun a : ℕ => (a : ℝ)⁻¹) (fun a _ => by positivity)
      _ ≤ ∑ rq ∈ (allPrimes v).product (Fintype.piFinset (fun _ : Fin 4 => allPrimes v)),
          (cofactor rq : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intro rq _ _; positivity)
      _ = _ := by
        have heq (rq : ℕ × (Fin 4 → ℕ)) : (cofactor rq : ℝ)⁻¹ =
            (rq.1 : ℝ)⁻¹*∏ i, (rq.2 i : ℝ)⁻¹ := by
          simp only [cofactor,Nat.cast_mul,Nat.cast_prod,mul_inv_rev,Finset.prod_inv_distrib]
          ring
        simp_rw [heq]
        rw [weighted_tuple_sum v (fun p : ℕ => (p : ℝ)⁻¹) (fun p : ℕ => (p : ℝ)⁻¹)]
        ring
  apply hcover.trans
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ ∑ p ∈ allPrimes v, (p : ℝ)⁻¹) hprime 5
  rw [mul_pow,← Real.rpow_mul_natCast hv.le] at hh
  norm_num only [Nat.cast_ofNat] at hh
  convert hh using 1; norm_num [variationConstant]
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

/-- A fixed phase mesh can meet any positive precision. It is auxiliary:
the underlying complete prime period does not depend on the mesh. -/
theorem exists_precise_mesh {y η : ℝ} (hy : 54 ≤ |y|) (hη : 0 < η) :
    ∃ m : ℕ, 0 < m ∧ Real.pi/(4*m*|y|) ≤ η/10 ∧
      |y| * (Real.pi/(4*m*|y|)) ≤ η := by
  obtain ⟨m,hm⟩ := exists_nat_gt (10/η)
  have hm0 : (0 : ℝ) < m := (by positivity : (0 : ℝ) < 10/η).trans hm
  have hmη : 10 ≤ (m : ℝ)*η := ((div_lt_iff₀ hη).mp hm).le
  have hy0 : 0 < |y| := by linarith
  refine ⟨m,by exact_mod_cast hm0,?_,?_⟩
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4*m*|y|)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hmη hy0.le,Real.pi_lt_four]
  · have he : |y| * (Real.pi/(4*m*|y|)) = Real.pi/(4*m) := by field_simp
    rw [he]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4*m)).mpr
    nlinarith [Real.pi_lt_four]

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
  obtain ⟨m,hm,hsmall,hphase⟩ := exists_precise_mesh hy hη
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
/-- Every selected integer is squarefree, has exactly six prime factors,
and satisfies the unchanged radial and allocation-safe share conditions. -/
theorem population_data {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|) {n : ℕ}
    (hn : n ∈ population v y) :
    Squarefree n ∧ n.primeFactors.card = 6 ∧
      v-Real.pi/|y| < Real.log n ∧ Real.log n ≤ v+Real.pi/|y| ∧
      (∀ a ∈ n.primeFactors, Real.log a ≤ (9/16 : ℝ)*Real.log n) := by
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
  apply ZetaRieszCoupledWindow.mem_core_of_prime_share_le j hj hu hU hL hs
    (by omega) ?_ (hlo.trans_lt htl) (htu.trans hhi) hmax
  rw [hcount]
  have hk : 8 ≤ ZetaRieszPrimeCountFrequency.dyadicPrimeCount j := by
    change 2^3 ≤ 2^(j+3)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  omega


private theorem eventually_raw_population_bound {m : ℕ} (hm : 0 < m)
    {y : ℝ} (hy : 54 ≤ |y|)
    (_hsmall : Real.pi/(4*m*|y|) ≤ 1/100000)
    (_hphase : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) :
    ∀ᶠ N : ℕ in atTop, ∀ (v L : ℝ),
      Real.cos (y*v) = -1 → 2*(N : ℝ) ≤ v → v ≤ 2*N+1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      (67/100 : ℝ)*v ≤ L → L ≤ (18/25 : ℝ)*v →
      ∃ V : ℝ, 0 < V ∧ V ≤ Real.exp (-v/2)*v^N/N.factorial ∧
        Real.exp (-v/2)*v^N/N.factorial ≤ (501/500 : ℝ)*V ∧
        |(∑ n ∈ population v y, SquarefreeVaughanLogSource.coefficient L n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re| ≤
          (m : ℝ)/100000*V*(Real.pi/(4*m*|y|)) := by
  filter_upwards [eventually_raw_population_small hy (by norm_num : (0 : ℝ) < 1/100000),
    eventually_ge_atTop (1 : ℕ)] with N hN hlarge v L hv hslo hshi _ _ hLl _
  have hv0 : 0 < v := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hlarge
    linarith
  let V := Real.exp (-v/2)*v^N/N.factorial
  have hV : 0 < V := by dsimp [V]; positivity
  refine ⟨V,hV,le_rfl,by change V ≤ (501/500 : ℝ)*V; linarith,?_⟩
  have hh := hN v L hslo hshi hv hLl
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have he : (1/100000 : ℝ)*(Real.pi/(4*|y|))*V =
      (m : ℝ)/100000*V*(Real.pi/(4*m*|y|)) := by field_simp
  rwa [he] at hh

/-- Independent two-sided cancellation inside the WHOLE actual core.
The selected rectangle is arithmetically counted, every original mask
is checked, and the entire complementary response remains signed. -/
theorem eventually_core_joint_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {m : ℕ} (hm : 0 < m)
    {y : ℝ} (hy : 54 ≤ |y|)
    (hsmall : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hphase : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      Real.cos (y*v) = -1 → 2*(N : ℝ) ≤ v → v ≤ 2*N+1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      ∃ V : ℝ, 0 < V ∧ V ≤ Real.exp (-v/2)*v^N/N.factorial ∧
        Real.exp (-v/2)*v^N/N.factorial ≤ (501/500 : ℝ)*V ∧
        |((u : ℂ)^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K-
          ∑ n ∈ ZetaRieszParityPacket.coreBand u N K\population v y,
            ZetaRieszJointAllocation.residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
              (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)).re| ≤
          u^(N+1)*((m : ℝ)/100000*V*(Real.pi/(4*m*|y|)))+ZetaRieszTriplePeriod.allocationBound N := by
  have hroom : u < Real.exp (-(137/200 : ℝ)) :=
    hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans
      (Real.exp_lt_exp.mpr (by norm_num)))
  have hlength := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (show 0 < u by linarith) (by norm_num : (0 : ℝ) ≤ 137/200) hroom
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_raw_population_bound hm hy hsmall hphase),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hlength,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1000 : ℕ)),
    eventually_ge_atTop (32 : ℕ)] with j hraw hLlow hlarge hj
  intro v
  dsimp only
  intro hv hslo hshi hlo hhi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hN : 2 ≤ N := by omega
  have hy0 : 0 < |y| := by linarith
  have hπ : 0 ≤ Real.pi/|y| := by positivity
  have hv100 : 100 ≤ v := by change (39/20 : ℝ)*N ≤ _ at hlo; linarith
  have hLhi : L ≤ (7/5 : ℝ)*N := by
    have he := ZetaRieszHeadOrders.length_le_two_log_two hu.le hN
    change SquarefreeVaughanLogSource.length u N ≤ _ at he
    dsimp only [L]
    nlinarith [Real.log_two_lt_d9,Nat.cast_nonneg (α := ℝ) N]
  change 2*(137/200 : ℝ)*N ≤ L at hLlow
  change (39/20 : ℝ)*N ≤ _ at hlo
  change _ ≤ (203/100 : ℝ)*N at hhi
  obtain ⟨V,hV,hbaseLower,hbase,hB⟩ := hraw v L hv hslo hshi hlo hhi (by linarith) (by linarith)
  refine ⟨V,hV,hbaseLower,hbase,?_⟩
  have hD := population_subset_core j hj hu hU hy hv100 (by change (5/4 : ℝ)*N ≤ L; linarith) hlo hhi
  apply ZetaRieszTriplePeriod.scaled_joint_bound_of_raw _ _ _ (SquarefreeVaughanLogSource.length_pos u N) N hD ?_ ?_ y
    (by linarith : 0 ≤ u) hU hB
  · intro n hn
    have hb := (population_data hv100 hy hn).2.2
    apply (ZetaRieszJointAllocation.mem_literalWindow N n).mpr
    constructor <;> linarith [hb.1,hb.2.1]
  · intro n hn p hp _ _
    have hb := (population_data hv100 hy hn).2.2.2.2 p hp
    nlinarith [Real.log_natCast_nonneg n]

/-- The cancellation reaches the SAME whole J+C used by the source
contradiction. Both a lower and an upper comparison follow, with a proved
vanishing error and the exact signed complement. The local radial debit
is explicit; it is not asserted to vanish at source scale. -/
theorem eventually_whole_joint_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {m : ℕ} (hm : 0 < m)
    {y : ℝ} (hy : 54 ≤ |y|)
    (hsmall : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hphase : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) :
    ∃ err : ℕ → ℝ, (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 → 2*(N : ℝ) ≤ v → v ≤ 2*N+1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      ∃ V : ℝ, 0 < V ∧ V ≤ Real.exp (-v/2)*v^N/N.factorial ∧
        Real.exp (-v/2)*v^N/N.factorial ≤ (501/500 : ℝ)*V ∧
        |((u : ℂ)^(N+1)*(J-
          ∑ n ∈ ZetaRieszParityPacket.coreBand u N K\population v y,
            ZetaRieszJointAllocation.residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
              (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)).re| ≤
          u^(N+1)*((m : ℝ)/100000*V*(Real.pi/(4*m*|y|)))+err j := by
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount
  let J := fun j => ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y (N j) (K j)-
    ZetaRieszLeastOrderOverflow.shortOverflowPacket u y (N j) (K j)+
      ZetaRieszLeastBoundary.rest u y (N j) (K j)
  let E := fun j => (u : ℂ)^(N j+1)*(ZetaRieszParityPacket.coreResponse u y (N j) (K j)-J j)
  have hu0 : 0 ≤ u := by linarith
  have he : Tendsto E atTop (𝓝 0) := by
    have hh := (ZetaRieszJointFloor.tendsto_nondominant_sub_joint hu0 hU y).sub
      (ZetaRieszJointFloor.tendsto_nondominant_sub_core hu0 hU y)
    simp only [sub_zero] at hh
    apply hh.congr'
    filter_upwards [] with j
    dsimp only [E,J,N,K]
    ring
  let err := fun j => ZetaRieszTriplePeriod.allocationBound (N j)+‖E j‖
  refine ⟨err,fun j => add_nonneg (ZetaRieszTriplePeriod.allocationBound_nonneg _) (norm_nonneg _),?_,?_⟩
  · have ht := (ZetaRieszTriplePeriod.tendsto_allocationBound.comp ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder).add he.norm
    simpa only [norm_zero,add_zero,err,N,Function.comp_def] using ht
  filter_upwards [eventually_core_joint_bound hu hU hm hy hsmall hphase] with j hj
  intro v
  dsimp only
  intro hv hslo hshi hlo hhi
  obtain ⟨V,hV,hbaseLower,hbase,hbound⟩ := hj v hv hslo hshi hlo hhi
  refine ⟨V,hV,hbaseLower,hbase,?_⟩
  let rest := ∑ n ∈ ZetaRieszParityPacket.coreBand u (N j) (K j)\population v y,
    ZetaRieszJointAllocation.residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (N j))
      (SquarefreeVaughanLogSource.length u (N j)) (N j) n*zetaPrimeLogKernel (N j) (3/2+Complex.I*y) n
  have hid : (u : ℂ)^(N j+1)*(J j-rest) =
      (u : ℂ)^(N j+1)*(ZetaRieszParityPacket.coreResponse u y (N j) (K j)-rest)-E j := by
    dsimp only [E]
    ring
  change |((u : ℂ)^(N j+1)*(J j-rest)).re| ≤ _
  rw [hid,Complex.sub_re]
  have hs := (abs_sub _ _).trans (add_le_add hbound (Complex.abs_re_le_norm (E j)))
  dsimp only [err]
  simpa only [add_assoc] using hs

/-- The actual coupled residual sum, including its old allocation, has
the proved signed cost. This is the payment used in the combined ledger. -/
theorem eventually_signed_population_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {m : ℕ} (hm : 0 < m)
    {y : ℝ} (hy : 54 ≤ |y|)
    (hsmall : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hphase : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) :
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
          u^(N+1)*((m : ℝ)/100000*V*(Real.pi/(4*m*|y|)))+ZetaRieszTriplePeriod.allocationBound N := by
  filter_upwards [eventually_core_joint_bound hu hU hm hy hsmall hphase,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1000 : ℕ)), eventually_ge_atTop (32 : ℕ),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent (by linarith : 0 < u)
        (by norm_num : (0 : ℝ) ≤ 137/200)
        (hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans
          (Real.exp_lt_exp.mpr (by norm_num)))))] with j hbound hN hj hL
  intro v
  dsimp only
  intro hv hslo hshi hlo hhi
  have hNR : (1000 : ℝ) ≤ ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by exact_mod_cast hN
  have hpi : 0 ≤ Real.pi/|y| := by positivity
  have hQ := population_subset_core j hj hu hU hy (by linarith) (by linarith) hlo hhi
  obtain ⟨V,hV,hbase,_,hc⟩ := hbound v hv hslo hshi hlo hhi
  refine ⟨hQ,V,hV,hbase,?_⟩
  have he := Finset.sum_sdiff hQ (f := fun n =>
    ZetaRieszJointAllocation.residualCoefficient
      (ZetaRieszAnnulusJoint.intermediatePrimes u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) n*
        zetaPrimeLogKernel (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (3/2+Complex.I*y) n)
  unfold ZetaRieszParityPacket.coreResponse at hc
  rw [← he,add_sub_cancel_left] at hc
  simpa only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] using hc
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


/-- Every previously paid six-prime label belongs to the broader
population. The two payments must therefore replace one another. -/
theorem old_population_subset {v y : ℝ} (_hv : 0 ≤ v) :
    ZetaRieszSixPrimePeriod.population v y ⊆ population v y := by
  intro n hn
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨rq,hrq,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hmem,hs⟩ := Finset.mem_filter.mp hrq
  obtain ⟨hr,hq⟩ := Finset.mem_product.mp hmem
  have hrb := logPrimes_bounds hr
  have hqb (i : Fin 4) := logPrimes_bounds (Fintype.mem_piFinset.mp hq i)
  have hc : cofactor rq = ZetaRieszSixPrimePeriod.cofactor rq := rfl
  have hlog : Real.log (cofactor rq) = Real.log rq.1+∑ i, Real.log (rq.2 i) := by
    rw [cofactor,Nat.cast_mul,Real.log_mul (by exact_mod_cast hrb.1.ne_zero)
      (by exact_mod_cast Finset.prod_ne_zero_iff.mpr (fun i _ => (hqb i).1.ne_zero)),
      Nat.cast_prod,Real.log_prod (fun i _ => by exact_mod_cast (hqb i).1.ne_zero)]
  rw [Fin.sum_univ_four] at hlog
  have hchoice : rq ∈ choices v := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,Fintype.mem_piFinset.mpr (fun i => ?_)⟩,hs,?_,?_⟩
    · exact (mem_logPrimes_iff _ _ _).mpr ⟨hrb.1,hrb.2.1,by linarith [hrb.2.2]⟩
    · have hp := hqb i
      exact (mem_logPrimes_iff _ _ _).mpr ⟨hp.1,by linarith [hp.2.1],by linarith [hp.2.2]⟩
    · linarith [hrb.2.1,(hqb 0).2.1,(hqb 1).2.1,(hqb 2).2.1,(hqb 3).2.1]
    · linarith [hrb.2.2,(hqb 0).2.2,(hqb 1).2.2,(hqb 2).2.2,(hqb 3).2.2]
  exact Finset.mem_biUnion.mpr ⟨cofactor rq,Finset.mem_image.mpr ⟨rq,hchoice,rfl⟩,by simpa only [hc] using hn⟩

/-- The expanded payment contains actual six-prime labels eventually,
including the earlier population with least prime two. -/
theorem eventually_population_nonempty {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, (N : ℝ) ≤ v → (population v y).Nonempty := by
  filter_upwards [ZetaRieszSixPrimePeriod.eventually_population_nonempty hy] with N hN v hv
  exact (hN v hv).mono (old_population_subset ((Nat.cast_nonneg N).trans hv))

/-- Reusable geometry of the actual five-prime cofactors. This exposes
the existing checked data for overlapping, rescaled population payments. -/
theorem cofactor_geometry {v : ℝ} {a : ℕ} (ha : a ∈ cofactors v) :
    Squarefree a ∧ a.primeFactors.card = 5 ∧ Real.log a.minFac ≤ (39/100 : ℝ)*v ∧
      (56/125 : ℝ)*v < Real.log a ∧ Real.log a ≤ (3/5 : ℝ)*v ∧
      (∀ p ∈ a.primeFactors, Real.log p ≤ (39/100 : ℝ)*v) :=
  cofactor_data ha

end
end RiemannGaussian.ZetaRieszBroadSixPeriod
