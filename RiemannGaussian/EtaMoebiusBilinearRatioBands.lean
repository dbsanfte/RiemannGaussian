import RiemannGaussian.EtaMoebiusBilinearShortShifts

/-!
# Sparse long-range product ratios in the actual Möbius matrix

Reducing a positive product pair by its gcd identifies its ratio
uniquely. Bounding both reduced factors gives a finite row count even
when the products themselves are far apart. The estimate below retains
the actual matrix and the original complex Mellin phases.
-/

open Complex Filter
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The product pair has a reduced ratio whose numerator and denominator both lie below the specified bound. -/
def pairedEtaBilinearSmallRatio (R n m : ℕ) : Prop :=
  n / Nat.gcd n m ≤ R ∧ m / Nat.gcd n m ≤ R

/-- Reducing a product ratio respects the exchange of the original two product indices. -/
theorem pairedEtaBilinearSmallRatio_comm (R n m : ℕ) :
    pairedEtaBilinearSmallRatio R n m ↔ pairedEtaBilinearSmallRatio R m n := by
  simp only [pairedEtaBilinearSmallRatio, Nat.gcd_comm m n, and_comm]

/-- Each positive product has at most `R²` partners with both reduced ratio factors at most `R`, regardless of the physical endpoint or the distance between products. -/
theorem card_pairedEtaBilinearSmallRatio_le (N R : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ((Finset.Icc 1 N).filter (pairedEtaBilinearSmallRatio R n)).card ≤ R ^ 2 := by
  let f : ℕ → ℕ × ℕ := fun m ↦ (n / Nat.gcd n m, m / Nat.gcd n m)
  let T : Finset (ℕ × ℕ) := (Finset.Icc 1 R) ×ˢ (Finset.Icc 1 R)
  have hpos (m : ℕ) (hm : 1 ≤ m) : 1 ≤ n / Nat.gcd n m ∧ 1 ≤ m / Nat.gcd n m := by
    have hg : 0 < Nat.gcd n m := Nat.gcd_pos_of_pos_left m hn
    exact ⟨Nat.div_pos (Nat.gcd_le_left m hn) hg, Nat.div_pos (Nat.gcd_le_right n hm) hg⟩
  have hmap : Set.MapsTo f ((Finset.Icc 1 N).filter (pairedEtaBilinearSmallRatio R n)) T := by
    intro m hm
    obtain ⟨hm, hR⟩ := Finset.mem_filter.mp hm
    obtain ⟨hq, hp⟩ := hpos m (Finset.mem_Icc.mp hm).1
    change (n / Nat.gcd n m, m / Nat.gcd n m) ∈
      ((Finset.Icc 1 R) ×ˢ (Finset.Icc 1 R) : Finset (ℕ × ℕ))
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hq, hR.1⟩, Finset.mem_Icc.mpr ⟨hp, hR.2⟩⟩
  have hinj : Set.InjOn f ((Finset.Icc 1 N).filter (pairedEtaBilinearSmallRatio R n)) := by
    intro a ha b hb hab
    have hq : n / Nat.gcd n a = n / Nat.gcd n b := congrArg Prod.fst hab
    have hp : a / Nat.gcd n a = b / Nat.gcd n b := congrArg Prod.snd hab
    have hqa := (hpos a (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1).1
    have hna := Nat.div_mul_cancel (Nat.gcd_dvd_left n a)
    have hnb := Nat.div_mul_cancel (Nat.gcd_dvd_left n b)
    have hg : Nat.gcd n a = Nat.gcd n b := by
      apply Nat.eq_of_mul_eq_mul_left hqa
      rw [hna, hq, hnb]
    calc
      a = (a / Nat.gcd n a) * Nat.gcd n a := (Nat.div_mul_cancel (Nat.gcd_dvd_right n a)).symm
      _ = (b / Nat.gcd n b) * Nat.gcd n b := by rw [hp, hg]
      _ = b := Nat.div_mul_cancel (Nat.gcd_dvd_right n b)
  simpa only [T, Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel, pow_two] using
    Finset.card_le_card_of_injOn f hmap hinj

private theorem norm_ratio_product_form_le (A L H R : ℕ) (v : ℕ → ℂ) :
    ‖∑ n ∈ Finset.Icc 1 (A + L),
      ∑ m ∈ (Finset.Icc 1 (A + L)).filter
        (fun m ↦ H < Nat.dist n m ∧ pairedEtaBilinearSmallRatio R n m),
          (pairedEtaBilinearPrefixWindowKernel A L n m : ℂ) * v n * starRingEnd ℂ (v m)‖ ≤
      (R : ℝ) ^ 2 * ∑ n ∈ Finset.Icc 1 (A + L), ‖v n‖ ^ 2 := by
  let I := Finset.Icc 1 (A + L)
  let P : ℕ → ℕ → Prop := fun n m ↦ H < Nat.dist n m ∧ pairedEtaBilinearSmallRatio R n m
  have hswap : (∑ n ∈ I, ∑ m ∈ I.filter (P n), ‖v m‖ ^ 2) =
      ∑ n ∈ I, ∑ m ∈ I.filter (P n), ‖v n‖ ^ 2 := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro m _
    simp only [P, Nat.dist_comm m n, pairedEtaBilinearSmallRatio_comm R m n]
  have hcard (n : ℕ) (hn : n ∈ I) : (I.filter (P n)).card ≤ R ^ 2 := by
    apply le_trans (Finset.card_le_card (show I.filter (P n) ⊆
      I.filter (pairedEtaBilinearSmallRatio R n) by
        intro m hm
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm).1, (Finset.mem_filter.mp hm).2.2⟩))
    exact card_pairedEtaBilinearSmallRatio_le (A + L) R (Finset.mem_Icc.mp hn).1
  have hpair (n m : ℕ) :
      ‖(pairedEtaBilinearPrefixWindowKernel A L n m : ℂ) * v n * starRingEnd ℂ (v m)‖ ≤
        (‖v n‖ ^ 2 + ‖v m‖ ^ 2) / 2 := by
    obtain ⟨hK0, hK1⟩ := pairedEtaBilinearPrefixWindowKernel_bounds A L n m
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hK0, norm_conj]
    have hp := mul_le_mul_of_nonneg_right hK1 (mul_nonneg (norm_nonneg (v n)) (norm_nonneg (v m)))
    nlinarith [sq_nonneg (‖v n‖ - ‖v m‖)]
  calc
    _ ≤ ∑ n ∈ I, ∑ m ∈ I.filter (P n), (‖v n‖ ^ 2 + ‖v m‖ ^ 2) / 2 := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m _ ↦ hpair n m))
    _ = ∑ n ∈ I, ((I.filter (P n)).card : ℝ) * ‖v n‖ ^ 2 := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_div]
      rw [hswap]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ∑ n ∈ I, (R : ℝ) ^ 2 * ‖v n‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast hcard n hn
    _ = _ := by rw [Finset.mul_sum]

/-- The signed contribution of long product shifts with both reduced ratio factors bounded; this selection is disjoint from the already controlled short-shift form. -/
def pairedEtaCompletedMoebiusBilinearRatioForm (rho : NontrivialZetaZero) (A L D H R : ℕ) : ℂ :=
  (‖pairedEtaXiCompletionFactor rho.1‖ : ℂ) ^ 2 *
    ∑ n ∈ Finset.Icc 1 (A + L),
      ∑ m ∈ (Finset.Icc 1 (A + L)).filter
        (fun m ↦ H < Nat.dist n m ∧ pairedEtaBilinearSmallRatio R n m),
          (pairedEtaBilinearPrefixWindowKernel A L n m : ℂ) *
            (pairedEtaMoebiusHighProductCoefficient D n : ℂ) *
            (pairedEtaMoebiusHighProductCoefficient D m : ℂ) *
            (n : ℂ) ^ (-rho.1) * starRingEnd ℂ ((m : ℂ) ^ (-rho.1))

/-- The complete signed remainder has both a long product shift and at least one reduced ratio factor beyond the ratio bound. -/
def pairedEtaCompletedMoebiusBilinearRatioRemainder (rho : NontrivialZetaZero) (A L D H R : ℕ) : ℂ :=
  (‖pairedEtaXiCompletionFactor rho.1‖ : ℂ) ^ 2 *
    ∑ n ∈ Finset.Icc 1 (A + L),
      ∑ m ∈ (Finset.Icc 1 (A + L)).filter
        (fun m ↦ H < Nat.dist n m ∧ ¬pairedEtaBilinearSmallRatio R n m),
          (pairedEtaBilinearPrefixWindowKernel A L n m : ℂ) *
            (pairedEtaMoebiusHighProductCoefficient D n : ℂ) *
            (pairedEtaMoebiusHighProductCoefficient D m : ℂ) *
            (n : ℂ) ^ (-rho.1) * starRingEnd ℂ ((m : ℂ) ^ (-rho.1))

/-- The entire original long-shift form splits into its small-ratio contribution and its exact complementary signed remainder. -/
theorem pairedEtaCompletedMoebiusBilinearFarForm_eq_ratio_add_remainder
    (rho : NontrivialZetaZero) (A L D H R : ℕ) :
    pairedEtaCompletedMoebiusBilinearFarForm rho A L D H =
      pairedEtaCompletedMoebiusBilinearRatioForm rho A L D H R +
        pairedEtaCompletedMoebiusBilinearRatioRemainder rho A L D H R := by
  rw [pairedEtaCompletedMoebiusBilinearFarForm, pairedEtaCompletedMoebiusBilinearRatioForm,
    pairedEtaCompletedMoebiusBilinearRatioRemainder, ← mul_add]
  apply congrArg (fun z : ℂ ↦ (‖pairedEtaXiCompletionFactor rho.1‖ : ℂ) ^ 2 * z)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hd : H < Nat.dist n m <;>
    by_cases hR : pairedEtaBilinearSmallRatio R n m <;> simp [hd, hR]

private theorem norm_product_term_sq (rho : NontrivialZetaZero) (D : ℕ)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖(pairedEtaMoebiusHighProductCoefficient D n : ℂ) * (n : ℂ) ^ (-rho.1)‖ ^ 2 =
      (pairedEtaMoebiusHighProductCoefficient D n : ℝ) ^ 2 * (n : ℝ) ^ (-(2 * rho.1.re)) := by
  rw [norm_mul, mul_pow, Complex.norm_intCast, Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]
  simp only [sq_abs]
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  congr 1
  congr 1
  norm_num
  ring

/-- The actual long-shift small-ratio form has a uniform power bound with its proved `R²` row cost. No arithmetic cancellation or favourable phase sign is assumed. -/
theorem norm_pairedEtaCompletedMoebiusBilinearRatioForm_le_power
    (rho : NontrivialZetaZero) {p : ℝ} (hp : 1 < p) (hpr : p ≤ 2 * rho.1.re)
    {D : ℕ} (hD : 1 ≤ D) (A L H R : ℕ) :
    ‖pairedEtaCompletedMoebiusBilinearRatioForm rho A L D H R‖ ≤
      (R : ℝ) ^ 2 * ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 *
        divisorSquareDirichletMass p * (D : ℝ) ^ (p - 2 * rho.1.re) := by
  have he : pairedEtaCompletedMoebiusBilinearRatioForm rho A L D H R =
      (‖pairedEtaXiCompletionFactor rho.1‖ : ℂ) ^ 2 *
        ∑ n ∈ Finset.Icc 1 (A + L),
          ∑ m ∈ (Finset.Icc 1 (A + L)).filter
            (fun m ↦ H < Nat.dist n m ∧ pairedEtaBilinearSmallRatio R n m),
              (pairedEtaBilinearPrefixWindowKernel A L n m : ℂ) *
                ((pairedEtaMoebiusHighProductCoefficient D n : ℂ) * (n : ℂ) ^ (-rho.1)) *
                starRingEnd ℂ ((pairedEtaMoebiusHighProductCoefficient D m : ℂ) * (m : ℂ) ^ (-rho.1)) := by
    simp only [pairedEtaCompletedMoebiusBilinearRatioForm, map_mul, map_intCast]
    apply congrArg (fun z : ℂ ↦ (‖pairedEtaXiCompletionFactor rho.1‖ : ℂ) ^ 2 * z)
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [he, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  have hb := norm_ratio_product_form_le A L H R
    (fun n ↦ (pairedEtaMoebiusHighProductCoefficient D n : ℂ) * (n : ℂ) ^ (-rho.1))
  have hs : (∑ n ∈ Finset.Icc 1 (A + L),
      ‖(pairedEtaMoebiusHighProductCoefficient D n : ℂ) * (n : ℂ) ^ (-rho.1)‖ ^ 2) ≤
        divisorSquareDirichletMass p * (D : ℝ) ^ (p - 2 * rho.1.re) := by
    convert sum_sq_pairedEtaMoebiusHighProductCoefficient_mul_rpow_neg_le hp hpr hD (A + L) using 1
    apply Finset.sum_congr rfl
    intro n hn
    exact norm_product_term_sq rho D (Finset.mem_Icc.mp hn).1
  calc
    _ ≤ ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 *
        ((R : ℝ) ^ 2 * (divisorSquareDirichletMass p * (D : ℝ) ^ (p - 2 * rho.1.re))) :=
      mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left hs (sq_nonneg _))) (sq_nonneg _)
    _ = _ := by ring

/-- The growing reduced-ratio bound for the actual squared divisor schedule. -/
def pairedEtaMoebiusBilinearRatioBound (rho : NontrivialZetaZero) (u : ℕ) : ℕ :=
  ⌊(u : ℝ) ^ ((rho.1.re - 1 / 2) / 2)⌋₊

/-- For a hypothetical right-half zero, both reduced ratio factors in the controlled long-shift selection range over an unbounded set. -/
theorem pairedEtaMoebiusBilinearRatioBound_tendsto_atTop
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (pairedEtaMoebiusBilinearRatioBound rho) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by linarith : 0 < (rho.1.re - 1 / 2) / 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))

/-- A growing family of long-range rational product interactions has a proved negative-power bound on the original squared divisor cutoff, uniformly over physical windows and short-shift exclusions. -/
theorem norm_pairedEtaCompletedMoebiusBilinearRatioForm_twoThirds_le
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re)
    {u : ℕ} (hu : 1 ≤ u) (A L H : ℕ) :
    ‖pairedEtaCompletedMoebiusBilinearRatioForm rho A L (u ^ 2) H
      (pairedEtaMoebiusBilinearRatioBound rho u)‖ ≤
        ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 * divisorSquareDirichletMass (rho.1.re + 1 / 2) *
          (u : ℝ) ^ (1 / 2 - rho.1.re) := by
  have hup : (0 : ℝ) < u := by exact_mod_cast hu
  have hR : (pairedEtaMoebiusBilinearRatioBound rho u : ℝ) ≤
      (u : ℝ) ^ ((rho.1.re - 1 / 2) / 2) := Nat.floor_le (Real.rpow_nonneg hup.le _)
  have hR2 : (pairedEtaMoebiusBilinearRatioBound rho u : ℝ) ^ 2 ≤
      (u : ℝ) ^ (rho.1.re - 1 / 2) := by
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg _) hR 2
    rw [← Real.rpow_mul_natCast hup.le] at hs
    convert hs using 1
    congr 1
    norm_num
  have he : ((u ^ 2 : ℕ) : ℝ) ^ (rho.1.re + 1 / 2 - 2 * rho.1.re) =
      (u : ℝ) ^ (1 - 2 * rho.1.re) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul hup.le]
    congr 1
    norm_num
    ring
  have h := norm_pairedEtaCompletedMoebiusBilinearRatioForm_le_power rho
    (by linarith : 1 < rho.1.re + 1 / 2) (by linarith : rho.1.re + 1 / 2 ≤ 2 * rho.1.re)
    (by nlinarith : 1 ≤ u ^ 2) A L H (pairedEtaMoebiusBilinearRatioBound rho u)
  rw [he] at h
  have hmass := divisorSquareDirichletMass_nonneg (rho.1.re + 1 / 2)
  apply h.trans
  calc
    _ ≤ (u : ℝ) ^ (rho.1.re - 1 / 2) * ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 *
        divisorSquareDirichletMass (rho.1.re + 1 / 2) * (u : ℝ) ^ (1 - 2 * rho.1.re) := by
      gcongr
    _ = ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 * divisorSquareDirichletMass (rho.1.re + 1 / 2) *
        ((u : ℝ) ^ (rho.1.re - 1 / 2) * (u : ℝ) ^ (1 - 2 * rho.1.re)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hup]
      congr 2
      ring

/-- The actual complex long-shift small-ratio form vanishes while its allowed reduced ratio factors grow, uniformly for arbitrary physical windows and distance cutoffs. -/
theorem pairedEtaCompletedMoebiusBilinearRatioForm_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) (A L H : ℕ → ℕ) :
    Tendsto (fun u : ℕ ↦ pairedEtaCompletedMoebiusBilinearRatioForm rho (A u) (L u) (u ^ 2) (H u)
      (pairedEtaMoebiusBilinearRatioBound rho u)) atTop (𝓝 0) := by
  have hd : Tendsto (fun u : ℕ ↦ (u : ℝ) ^ (1 / 2 - rho.1.re)) atTop (𝓝 0) := by
    have hr := tendsto_rpow_neg_atTop (sub_pos.mpr hrho)
    convert hr.comp (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    ext u
    simp only [Function.comp_apply]
    congr 1
    ring
  have hb := hd.const_mul (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 *
    divisorSquareDirichletMass (rho.1.re + 1 / 2))
  rw [mul_zero] at hb
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  exact squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _))
    ((eventually_ge_atTop 1).mono fun u hu ↦
      norm_pairedEtaCompletedMoebiusBilinearRatioForm_twoThirds_le rho hrho hu (A u) (L u) (H u)) hb

/-- After both independently controlled selections vanish, the unchanged source square remains in the signed long-shift form with large reduced ratio height on the original cubic windows. -/
theorem pairedEtaCompletedMoebiusBilinearRatioRemainder_twoThirds_tendsto_source
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun u : ℕ ↦ (pairedEtaCompletedMoebiusBilinearRatioRemainder rho (u ^ 3) (u ^ 3) (u ^ 2)
      (pairedEtaMoebiusBilinearNearRadius rho u) (pairedEtaMoebiusBilinearRatioBound rho u)).re)
      atTop (𝓝 (‖pairedEtaCompletedMoebiusSource rho‖ ^ 2)) := by
  have hf := pairedEtaCompletedMoebiusBilinearFarForm_twoThirds_tendsto_source rho hrho
  have hr := Complex.continuous_re.continuousAt.tendsto.comp
    (pairedEtaCompletedMoebiusBilinearRatioForm_tendsto_zero rho hrho
      (fun u ↦ u ^ 3) (fun u ↦ u ^ 3) (pairedEtaMoebiusBilinearNearRadius rho))
  have he (u : ℕ) : (pairedEtaCompletedMoebiusBilinearRatioRemainder rho (u ^ 3) (u ^ 3) (u ^ 2)
      (pairedEtaMoebiusBilinearNearRadius rho u) (pairedEtaMoebiusBilinearRatioBound rho u)).re =
        (pairedEtaCompletedMoebiusBilinearFarForm rho (u ^ 3) (u ^ 3) (u ^ 2)
          (pairedEtaMoebiusBilinearNearRadius rho u)).re -
        (pairedEtaCompletedMoebiusBilinearRatioForm rho (u ^ 3) (u ^ 3) (u ^ 2)
          (pairedEtaMoebiusBilinearNearRadius rho u) (pairedEtaMoebiusBilinearRatioBound rho u)).re := by
    have h := congrArg Complex.re (pairedEtaCompletedMoebiusBilinearFarForm_eq_ratio_add_remainder rho
      (u ^ 3) (u ^ 3) (u ^ 2) (pairedEtaMoebiusBilinearNearRadius rho u) (pairedEtaMoebiusBilinearRatioBound rho u))
    simp only [Complex.add_re] at h
    linarith
  simpa only [Function.comp_apply, he, Complex.zero_re, sub_zero] using hf.sub hr

/-- Removing both the growing short-shift band and the growing small-ratio long-shift selection changes the original whole-window energy by at most one explicit vanishing power allowance. -/
theorem norm_pairedEtaCompletedMoebiusLargeMeanSquare_sub_ratioRemainder_twoThirds_le
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re)
    {u : ℕ} (hu : 1 ≤ u) (A L : ℕ) :
    ‖(pairedEtaCompletedMoebiusLargeMeanSquare rho A L (u ^ 2) : ℂ) -
      pairedEtaCompletedMoebiusBilinearRatioRemainder rho A L (u ^ 2)
        (pairedEtaMoebiusBilinearNearRadius rho u) (pairedEtaMoebiusBilinearRatioBound rho u)‖ ≤
      4 * ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 * divisorSquareDirichletMass (rho.1.re + 1 / 2) *
        (u : ℝ) ^ (1 / 2 - rho.1.re) := by
  rw [pairedEtaCompletedMoebiusLargeMeanSquare_eq_near_add_far rho A L (u ^ 2)
    (pairedEtaMoebiusBilinearNearRadius rho u),
    pairedEtaCompletedMoebiusBilinearFarForm_eq_ratio_add_remainder rho A L (u ^ 2)
      (pairedEtaMoebiusBilinearNearRadius rho u) (pairedEtaMoebiusBilinearRatioBound rho u)]
  rw [add_sub_assoc, add_sub_cancel_right]
  apply (norm_add_le _ _).trans
  apply le_trans (add_le_add
    (norm_pairedEtaCompletedMoebiusBilinearNearForm_twoThirds_le rho hrho hu A L)
    (norm_pairedEtaCompletedMoebiusBilinearRatioForm_twoThirds_le rho hrho hu A L
      (pairedEtaMoebiusBilinearNearRadius rho u)))
  exact le_of_eq (by ring)

end

end RiemannGaussian
