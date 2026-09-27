/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFourPrimeHead

/-!
# Sharp ordinary-prime budgets for signed compensation

Fixed-width logarithmic intervals have arbitrarily small relative errors,
uniformly once their left endpoint exceeds any fixed positive multiple of
the original moment order. These are unsigned population estimates used
inside a signed comparison; they do not replace a signed carrier by a
prime-density integral at source scale.
-/

namespace RiemannGaussian.ZetaRieszSharpPrimeWindows
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic

/-- The actual prime log mass has any prescribed relative accuracy,
uniformly over all macroscopic left endpoints, without an upper endpoint
restriction. The width remains fixed as the moment tends to infinity. -/
theorem eventually_log_mass_bounds {h α ε : ℝ}
    (hh : 0 < h) (hα : 0 < α) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℝ, α*N ≤ a →
      (1-ε)*(Real.exp h-1)*Real.exp a ≤ ∑ p ∈ logPrimes a h, Real.log p ∧
      (∑ p ∈ logPrimes a h, Real.log p) ≤ (1+ε)*(Real.exp h-1)*Real.exp a := by
  have hE : 0 < Real.exp h-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hh)
  have hlo := (PrimeWindow.theta_interval_div_tendsto (Real.exp_pos h)).eventually_const_lt
    (show (1-ε)*(Real.exp h-1) < Real.exp h-1 by nlinarith)
  have hhi := (PrimeWindow.theta_interval_div_tendsto (Real.exp_pos h)).eventually_lt_const
    (show Real.exp h-1 < (1+ε)*(Real.exp h-1) by nlinarith)
  obtain ⟨X,hX⟩ := eventually_atTop.mp (hlo.and hhi)
  have hx : Tendsto (fun N : ℕ => Real.exp (α*N)) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hα)
  filter_upwards [hx.eventually_ge_atTop X] with N hN a ha
  have hb := hX (Real.exp a) (hN.trans (Real.exp_le_exp.mpr ha))
  have hl := (lt_div_iff₀ (Real.exp_pos a)).mp hb.1
  have hu := (div_lt_iff₀ (Real.exp_pos a)).mp hb.2
  rw [← PrimeWindow.sum_log_primesInWindow (Real.exp_pos a).le
    (Real.one_le_exp_iff.mpr hh.le)] at hl hu
  exact ⟨hl.le,hu.le⟩

/-- Sharp actual prime counts, with the two literal logarithmic endpoints
in the denominators. No unknown multiplicative counting constant remains. -/
theorem eventually_card_bounds {h α ε : ℝ}
    (hh : 0 < h) (hα : 0 < α) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℝ, α*N ≤ a →
      (1-ε)*(Real.exp h-1)*Real.exp a/(a+h) ≤ ((logPrimes a h).card : ℝ) ∧
      ((logPrimes a h).card : ℝ) ≤ (1+ε)*(Real.exp h-1)*Real.exp a/a := by
  filter_upwards [eventually_log_mass_bounds hh hα hε,eventually_ge_atTop (1 : ℕ)]
    with N hN hN1 a ha
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have ha0 : 0 < a := by nlinarith
  have hmass := hN a ha
  constructor
  · apply (div_le_iff₀ (by linarith : 0 < a+h)).mpr
    apply hmass.1.trans
    calc
      _ ≤ ∑ _p ∈ logPrimes a h, (a+h) :=
        Finset.sum_le_sum (fun _ hp => (logPrimes_bounds hp).2.2)
      _ = _ := by simp; ring
  · apply (le_div_iff₀ ha0).mpr
    apply le_trans _ hmass.2
    calc
      _ = ∑ _p ∈ logPrimes a h, a := by simp
      _ ≤ _ := Finset.sum_le_sum (fun _ hp => (logPrimes_bounds hp).2.1.le)

/-- Harmonic prime mass with near-sharp endpoint bounds. This is the
population measure appropriate to the unchanged radial factorial kernel. -/
theorem eventually_reciprocal_bounds {h α ε : ℝ}
    (hh : 0 < h) (hα : 0 < α) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℝ, α*N ≤ a →
      (1-ε)*(1-Real.exp (-h))/(a+h) ≤ ∑ p ∈ logPrimes a h, (p : ℝ)⁻¹ ∧
      (∑ p ∈ logPrimes a h, (p : ℝ)⁻¹) ≤ (1+ε)*(Real.exp h-1)/a := by
  filter_upwards [eventually_card_bounds hh hα hε] with N hN a ha
  have hcount := hN a ha
  have hlo : Real.exp (-(a+h))*((logPrimes a h).card : ℝ) ≤
      ∑ p ∈ logPrimes a h, (p : ℝ)⁻¹ := by
    calc
      _ = ∑ _p ∈ logPrimes a h, Real.exp (-(a+h)) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun p hp => by
        have hp0 : (0 : ℝ) < p := by exact_mod_cast (logPrimes_bounds hp).1.pos
        rw [← Real.exp_log hp0,← Real.exp_neg]
        exact Real.exp_le_exp.mpr (by linarith [(logPrimes_bounds hp).2.2]))
  have hhi : (∑ p ∈ logPrimes a h, (p : ℝ)⁻¹) ≤
      Real.exp (-a)*((logPrimes a h).card : ℝ) := by
    calc
      _ ≤ ∑ _p ∈ logPrimes a h, Real.exp (-a) := Finset.sum_le_sum (fun p hp => by
        have hp0 : (0 : ℝ) < p := by exact_mod_cast (logPrimes_bounds hp).1.pos
        rw [← Real.exp_log hp0,← Real.exp_neg]
        exact Real.exp_le_exp.mpr (by linarith [(logPrimes_bounds hp).2.1]))
      _ = _ := by simp; ring
  have he₁ : Real.exp (-(a+h))*Real.exp a = Real.exp (-h) := by
    rw [← Real.exp_add]; congr 1; ring
  have he₂ : Real.exp (-h)*Real.exp h = 1 := by rw [← Real.exp_add]; simp
  have he₃ : Real.exp (-a)*Real.exp a = 1 := by rw [← Real.exp_add]; simp
  constructor
  · have hb := (mul_le_mul_of_nonneg_left hcount.1 (Real.exp_nonneg (-(a+h)))).trans hlo
    have he : Real.exp (-(a+h))*((1-ε)*(Real.exp h-1)*Real.exp a/(a+h)) =
        (1-ε)*(1-Real.exp (-h))/(a+h) := by
      calc
        _ = (1-ε)*((Real.exp (-(a+h))*Real.exp a)*(Real.exp h-1))/(a+h) := by ring
        _ = _ := by rw [he₁,mul_sub,he₂,mul_one]
    rw [he] at hb
    exact hb
  · have hb := hhi.trans (mul_le_mul_of_nonneg_left hcount.2 (Real.exp_nonneg (-a)))
    have he : Real.exp (-a)*((1+ε)*(Real.exp h-1)*Real.exp a/a) =
        (1+ε)*(Real.exp h-1)/a := by
      calc
        _ = (1+ε)*(Real.exp h-1)*(Real.exp (-a)*Real.exp a)/a := by ring
        _ = _ := by rw [he₃,mul_one]
    rw [he] at hb
    exact hb

/-- Product budgets retain every literal prime interval. The relative
precision can be chosen before fixing a finite four- or five-prime grid. -/
theorem eventually_tuple_reciprocal_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h α ε : ℝ} (hh : 0 < h) (hα : 0 < α) (hε : 0 < ε) (hεu : ε ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ a : ι → ℝ, (∀ i, α*N ≤ a i) →
      (∏ i, (1-ε)*(1-Real.exp (-h))/(a i+h)) ≤
        ∑ p ∈ Fintype.piFinset (fun i => logPrimes (a i) h), ∏ i, (p i : ℝ)⁻¹ ∧
      (∑ p ∈ Fintype.piFinset (fun i => logPrimes (a i) h), ∏ i, (p i : ℝ)⁻¹) ≤
        ∏ i, (1+ε)*(Real.exp h-1)/(a i) := by
  filter_upwards [eventually_reciprocal_bounds hh hα hε,eventually_ge_atTop (1 : ℕ)]
    with N hN hN1 a ha
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have ha0 (i : ι) : 0 < a i := by nlinarith [ha i]
  rw [← Finset.prod_univ_sum (fun i => logPrimes (a i) h) (fun (_ : ι) (p : ℕ) => (p : ℝ)⁻¹)]
  constructor
  · apply Finset.prod_le_prod
    · intro i _
      exact div_nonneg (mul_nonneg (sub_nonneg.mpr hεu)
        (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))) (by linarith [ha0 i])
    · intro i _
      exact (hN (a i) (ha i)).1
  · apply Finset.prod_le_prod
    · intro i _
      exact Finset.sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))
    · intro i _
      exact (hN (a i) (ha i)).2

/-- Ordered disjoint prime windows count each integer once. This prevents
the favorable supply from acquiring an artificial factorial multiplicity. -/
theorem ordered_product_injective {k : ℕ} {a : Fin k → ℝ} {h : ℝ}
    (horder : ∀ i j, i < j → a i+h ≤ a j) :
    Set.InjOn (fun p : Fin k → ℕ => ∏ i, p i)
      (Fintype.piFinset (fun i => logPrimes (a i) h) : Set _) := by
  intro p hp q hq he
  dsimp only at he
  funext i
  have hpi := (logPrimes_bounds (Fintype.mem_piFinset.mp hp i)).1
  have hd : p i ∣ ∏ j, q j := by
    rw [← he]
    exact Finset.dvd_prod_of_mem p (Finset.mem_univ i)
  obtain ⟨j,_,hj⟩ := (hpi.prime.dvd_finsetProd_iff q).mp hd
  have heq := (Nat.prime_dvd_prime_iff_eq hpi
    (logPrimes_bounds (Fintype.mem_piFinset.mp hq j)).1).mp hj
  have hij : i = j := by
    rcases lt_trichotomy i j with hij | hij | hij
    · exact False.elim ((logPrimes_order (horder i j hij)
        (Fintype.mem_piFinset.mp hp i) (Fintype.mem_piFinset.mp hq j)).ne heq)
    · exact hij
    · exact False.elim ((logPrimes_order (horder j i hij)
        (Fintype.mem_piFinset.mp hq j) (Fintype.mem_piFinset.mp hp i)).ne heq.symm)
  simpa only [← hij] using heq

private theorem amplitude_radial {n : ℕ} (hn : n ≠ 0) (N : ℕ) :
    amplitude N n =
      (Real.exp (-Real.log n/2)*(Real.log n)^N/N.factorial)*(n : ℝ)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he : Real.exp (-(3/2 : ℝ)*Real.log n) =
      Real.exp (-Real.log n/2)*(n : ℝ)⁻¹ := by
    have hi : (n : ℝ)⁻¹ = Real.exp (-Real.log n) := by rw [Real.exp_neg,Real.exp_log hnR]
    rw [hi,← Real.exp_add]
    congr 1
    ring
  rw [amplitude,he]
  ring

private theorem tuple_log_bounds {k : ℕ} {a : Fin k → ℝ} {h : ℝ}
    {p : Fin k → ℕ} (hp : p ∈ Fintype.piFinset (fun i => logPrimes (a i) h)) :
    (∏ i, p i) ≠ 0 ∧ (∑ i, a i) ≤ Real.log (∏ i, p i : ℕ) ∧
      Real.log (∏ i, p i : ℕ) ≤ (∑ i, a i)+k*h := by
  have hpos (i : Fin k) : (p i).Prime :=
    (logPrimes_bounds (Fintype.mem_piFinset.mp hp i)).1
  have he : Real.log (∏ i, p i : ℕ) = ∑ i, Real.log (p i) := by
    rw [Nat.cast_prod,Real.log_prod (fun i _ => by exact_mod_cast (hpos i).ne_zero)]
  refine ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => (hpos i).ne_zero),?_,?_⟩
  · rw [he]
    exact Finset.sum_le_sum (fun i _ => (logPrimes_bounds (Fintype.mem_piFinset.mp hp i)).2.1.le)
  · rw [he]
    calc
      _ ≤ ∑ i, (a i+h) :=
        Finset.sum_le_sum (fun i _ => (logPrimes_bounds (Fintype.mem_piFinset.mp hp i)).2.2)
      _ = _ := by simp [Finset.sum_add_distrib]

/-- A literal favorable prime box has this explicit signed lower bound.
The original moment, allocation fraction, coefficient and product phase
are tested together. Counting has no undischarged prime-density premise. -/
theorem eventually_signed_box_lower {h α ε : ℝ}
    (hh : 0 < h) (hα : 0 < α) (hε : 0 < ε) (hεu : ε ≤ 1) (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ (a : Fin k → ℝ) (A : Finset ℕ) (L y b : ℝ),
      (∀ i, α*N ≤ a i) → (∀ i j, i < j → a i+h ≤ a j) → 0 ≤ b →
      (∀ p ∈ Fintype.piFinset (fun i => logPrimes (a i) h),
        b ≤ (1-boundedShare A N (∏ i, p i))*
          ((SquarefreeVaughanLogSource.coefficient L (∏ i, p i)).re*
            Real.cos (y*Real.log (∏ i, p i : ℕ)))) →
      b*(Real.exp (-((∑ i, a i)+k*h)/2)*(∑ i, a i)^N/N.factorial)*
        (∏ i, (1-ε)*(1-Real.exp (-h))/(a i+h)) ≤
      (∑ n ∈ (Fintype.piFinset (fun i => logPrimes (a i) h)).image (fun p => ∏ i, p i),
        residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  filter_upwards [eventually_tuple_reciprocal_bounds (ι := Fin k) hh hα hε hεu]
    with N hN a A L y b ha horder hb hscore
  let B := Fintype.piFinset (fun i => logPrimes (a i) h)
  let V := Real.exp (-((∑ i, a i)+k*h)/2)*(∑ i, a i)^N/N.factorial
  have hsum0 : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun i _ => by
    have hn : 0 ≤ α*(N : ℝ) := mul_nonneg hα.le (Nat.cast_nonneg N)
    exact hn.trans (ha i))
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hpoint (p : Fin k → ℕ) (hp : p ∈ B) :
      b*V*(∏ i, (p i : ℝ)⁻¹) ≤
        (residualCoefficient A L N (∏ i, p i)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (∏ i, p i)).re := by
    have hbounds := tuple_log_bounds hp
    have hrad : V ≤ Real.exp (-Real.log (∏ i, p i : ℕ)/2)*
        (Real.log (∏ i, p i : ℕ))^N/N.factorial := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul
        (Real.exp_le_exp.mpr (by linarith [hbounds.2.2]))
        (pow_le_pow_left₀ hsum0 hbounds.2.1 N) (by positivity) (Real.exp_nonneg _)
    have hinv : ∏ i, (p i : ℝ)⁻¹ = ((∏ i, p i : ℕ) : ℝ)⁻¹ := by
      rw [Nat.cast_prod,Finset.prod_inv_distrib]
    rw [re_residual_atom,weight,amplitude_radial hbounds.1 N,hinv]
    have hbr : b*V ≤ b*(Real.exp (-Real.log (∏ i, p i : ℕ)/2)*
        (Real.log (∏ i, p i : ℕ))^N/N.factorial) := mul_le_mul_of_nonneg_left hrad hb
    have hsc := mul_le_mul_of_nonneg_right (hscore p hp)
      (show 0 ≤ amplitude N (∏ i, p i) from ZetaRieszCosineCarrier.factorial_envelope_nonneg _ _)
    rw [amplitude_radial hbounds.1 N] at hsc
    have hbr' := mul_le_mul_of_nonneg_right hbr
      (inv_nonneg.mpr (Nat.cast_nonneg (∏ i, p i)))
    simp only [← mul_assoc] at hsc hbr'
    have ht := hbr'.trans hsc
    exact ht.trans_eq (by ring)
  have hmass := mul_le_mul_of_nonneg_left (hN a ha).1 (mul_nonneg hb hV)
  calc
    _ ≤ b*V*(∑ p ∈ B, ∏ i, (p i : ℝ)⁻¹) := by
      simpa only [V,B] using hmass
    _ = ∑ p ∈ B, b*V*(∏ i, (p i : ℝ)⁻¹) := Finset.mul_sum _ _ _
    _ ≤ ∑ p ∈ B, (residualCoefficient A L N (∏ i, p i)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (∏ i, p i)).re := Finset.sum_le_sum hpoint
    _ = _ := by
      rw [Complex.re_sum,Finset.sum_image (ordered_product_injective horder)]

/-- The adverse population uses the upper prime budget while retaining
only its signed debit, not a termwise absolute coefficient. This is the
counterpart needed to compare four-prime debits with five-prime supply. -/
theorem eventually_signed_box_floor {h α ε : ℝ}
    (hh : 0 < h) (hα : 0 < α) (hε : 0 < ε) (hεu : ε ≤ 1) (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ (a : Fin k → ℝ) (A : Finset ℕ) (L y b : ℝ),
      (∀ i, α*N ≤ a i) → (∀ i j, i < j → a i+h ≤ a j) → 0 ≤ b →
      (∀ p ∈ Fintype.piFinset (fun i => logPrimes (a i) h),
        -b ≤ (1-boundedShare A N (∏ i, p i))*
          ((SquarefreeVaughanLogSource.coefficient L (∏ i, p i)).re*
            Real.cos (y*Real.log (∏ i, p i : ℕ)))) →
      -(b*(Real.exp (-(∑ i, a i)/2)*((∑ i, a i)+k*h)^N/N.factorial)*
        (∏ i, (1+ε)*(Real.exp h-1)/(a i))) ≤
      (∑ n ∈ (Fintype.piFinset (fun i => logPrimes (a i) h)).image (fun p => ∏ i, p i),
        residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  filter_upwards [eventually_tuple_reciprocal_bounds (ι := Fin k) hh hα hε hεu]
    with N hN a A L y b ha horder hb hscore
  let B := Fintype.piFinset (fun i => logPrimes (a i) h)
  let V := Real.exp (-(∑ i, a i)/2)*((∑ i, a i)+k*h)^N/N.factorial
  have hsum0 : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun i _ =>
    (mul_nonneg hα.le (Nat.cast_nonneg N)).trans (ha i))
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hpoint (p : Fin k → ℕ) (hp : p ∈ B) :
      -(b*V*(∏ i, (p i : ℝ)⁻¹)) ≤
        (residualCoefficient A L N (∏ i, p i)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (∏ i, p i)).re := by
    have hbounds := tuple_log_bounds hp
    have hrad : Real.exp (-Real.log (∏ i, p i : ℕ)/2)*
        (Real.log (∏ i, p i : ℕ))^N/N.factorial ≤ V := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul
        (Real.exp_le_exp.mpr (by linarith [hbounds.2.1]))
        (pow_le_pow_left₀ (Real.log_natCast_nonneg _) hbounds.2.2 N)
        (by positivity) (Real.exp_nonneg _)
    have hinv : ∏ i, (p i : ℝ)⁻¹ = ((∏ i, p i : ℕ) : ℝ)⁻¹ := by
      rw [Nat.cast_prod,Finset.prod_inv_distrib]
    rw [re_residual_atom,weight,amplitude_radial hbounds.1 N,hinv]
    have hbr := neg_le_neg (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrad hb)
      (inv_nonneg.mpr (Nat.cast_nonneg (∏ i, p i))))
    have hsc := mul_le_mul_of_nonneg_right (hscore p hp)
      (show 0 ≤ amplitude N (∏ i, p i) from ZetaRieszCosineCarrier.factorial_envelope_nonneg _ _)
    rw [amplitude_radial hbounds.1 N] at hsc
    simp only [← mul_assoc,neg_mul] at hsc
    exact (hbr.trans hsc).trans_eq (by ring)
  have hmass := neg_le_neg (mul_le_mul_of_nonneg_left (hN a ha).2 (mul_nonneg hb hV))
  calc
    _ ≤ -(b*V*(∑ p ∈ B, ∏ i, (p i : ℝ)⁻¹)) := by simpa only [V,B] using hmass
    _ = ∑ p ∈ B, -(b*V*(∏ i, (p i : ℝ)⁻¹)) := by rw [Finset.mul_sum,Finset.sum_neg_distrib]
    _ ≤ ∑ p ∈ B, (residualCoefficient A L N (∏ i, p i)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (∏ i, p i)).re := Finset.sum_le_sum hpoint
    _ = _ := by
      rw [Complex.re_sum,Finset.sum_image (ordered_product_injective horder)]

end
end RiemannGaussian.ZetaRieszSharpPrimeWindows
