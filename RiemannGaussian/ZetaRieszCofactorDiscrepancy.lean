/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCofactorPhaseEnergy
import RiemannGaussian.ZetaSquarefreeCounting
import RiemannGaussian.NatDivisorSquareDirichlet

/-!
# A power estimate for the actual signed cofactor cutoff

The squarefree counting input has a genuine power error. It can therefore
be applied to the sharp Möbius cutoff before any phase is discarded. The
density term, the unit and ordinary-prime cofactors, and the variation of
every literal mask must remain explicit. This is not prime-density transport.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszCofactorDiscrepancy
open Real ZetaRieszCofactorPhaseEnergy

/-- The signed density of the SAME sharp squarefree divisor prefix. -/
def densityPrefix (D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, (μ d : ℝ)*SquarefreeCounting.density d.primeFactors

/-- Reordering the literal squarefree count keeps every Möbius sign. -/
theorem count_eq_marks (X D : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, if Squarefree n then sharp D n else 0) =
      ∑ d ∈ Finset.Icc 1 D, (μ d : ℝ)*SquarefreeCounting.count d.primeFactors X := by
  have he n : (if Squarefree n then sharp D n else 0) =
      ∑ d ∈ Finset.Icc 1 D, (μ d : ℝ)*(if Squarefree n ∧ d ∣ n then 1 else 0) := by
    by_cases hn : Squarefree n
    · simp only [hn,if_true,true_and,sharp,mul_ite,mul_one,mul_zero]
    · simp [hn]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.mul_sum]
  by_cases hd : Squarefree d
  · congr 1
    have hi : Finset.Icc 1 X = Finset.Ioc 0 X := by
      ext n
      simp only [Finset.mem_Icc,Finset.mem_Ioc]
      omega
    simp only [SquarefreeCounting.count,Nat.prod_primeFactors_of_squarefree hd,hi]
  · have hm : (μ d : ℝ)=0 := by
      exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd
    simp [hm]

private theorem corrected_mark_le {d : ℕ} (hd : Squarefree d) :
    (∏ p ∈ d.primeFactors, primeSquareCorrectedWeight (3/4) p) ≤
      (d.divisors.card : ℝ)*zetaPrimeExpWeight (3/4) d := by
  have hw p : zetaPrimeExpWeight (3/4) p ≤ 1 := by
    rw [zetaPrimeExpWeight,exp_le_one_iff]
    nlinarith [log_natCast_nonneg p]
  calc
    _ ≤ ∏ p ∈ d.primeFactors, (2 : ℝ)*zetaPrimeExpWeight (3/4) p := by
      apply Finset.prod_le_prod (fun p _ => primeSquareCorrectedWeight_nonneg _ _)
      intro p _
      unfold primeSquareCorrectedWeight
      have hp0 : 0 ≤ zetaPrimeExpWeight (3/4) p := (exp_pos _).le
      nlinarith [mul_le_mul_of_nonneg_left (hw p) hp0]
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,RoughCoprimeFactor.card_divisors_eq hd]
      congr 1
      rw [← zetaPrimeExpWeight_prod d.primeFactors
        (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos),
        Nat.prod_primeFactors_of_squarefree hd]

private theorem mark_sum_bound (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, |(μ d : ℝ)| *
      ∏ p ∈ d.primeFactors, primeSquareCorrectedWeight (3/4) p) ≤
      exp ((3/8 : ℝ)*log D)*divisorSquareDirichletMass (9/8) := by
  have ht d (hd : d ∈ Finset.Icc 1 D) :
      |(μ d : ℝ)| *(∏ p ∈ d.primeFactors, primeSquareCorrectedWeight (3/4) p) ≤
      exp ((3/8 : ℝ)*log D)*((d.divisors.card : ℝ)^2*(d : ℝ)^(-(9/8 : ℝ))) := by
    have hd0 : (0 : ℝ)<d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hl : log d ≤ log D := log_le_log hd0 (by exact_mod_cast (Finset.mem_Icc.mp hd).2)
    by_cases hs : Squarefree d
    · have hm : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have hdc : (d.divisors.card : ℝ) ≤ (d.divisors.card : ℝ)^2 := by
        have hc : 1 ≤ d.divisors.card := Finset.one_le_card.mpr ⟨1,Nat.one_mem_divisors.mpr hs.ne_zero⟩
        have hc' : (1 : ℝ) ≤ d.divisors.card := by exact_mod_cast hc
        nlinarith
      have hw : zetaPrimeExpWeight (3/4) d ≤
          exp ((3/8 : ℝ)*log D)*(d : ℝ)^(-(9/8 : ℝ)) := by
        rw [zetaPrimeExpWeight,rpow_def_of_pos hd0,← exp_add]
        apply exp_le_exp.mpr
        linarith
      calc
        _ ≤ (d.divisors.card : ℝ)*zetaPrimeExpWeight (3/4) d :=
          (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _ => primeSquareCorrectedWeight_nonneg _ _)) hm).trans
            (corrected_mark_le hs)
        _ ≤ (d.divisors.card : ℝ)^2*(exp ((3/8 : ℝ)*log D)*(d : ℝ)^(-(9/8 : ℝ))) :=
          mul_le_mul hdc hw (exp_pos _).le (sq_nonneg _)
        _ = _ := by ring
    · have hm : (μ d : ℝ)=0 := by
        exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs
      rw [hm,abs_zero,zero_mul]
      positivity
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 D,
        exp ((3/8 : ℝ)*log D)*((d.divisors.card : ℝ)^2*(d : ℝ)^(-(9/8 : ℝ))) :=
      Finset.sum_le_sum ht
    _ = exp ((3/8 : ℝ)*log D)*(∑ d ∈ Finset.Icc 1 D,
        (d.divisors.card : ℝ)^2*(d : ℝ)^(-(9/8 : ℝ))) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((summable_card_divisors_sq_mul_rpow_neg (by norm_num : (1 : ℝ)<9/8)).sum_le_tsum _
        (fun _ _ => by positivity)) (exp_pos _).le

/-- One finite constant, independent of both physical and divisor cutoffs. -/
def countingConstant : ℝ :=
  exp (primeSquareWeightMass (3/4))*(divisorSquareDirichletMass (9/8)+1)

/-- The constant is positive; its defining divisor series genuinely converges. -/
theorem countingConstant_pos : 0 < countingConstant := by
  unfold countingConstant
  exact mul_pos (exp_pos _) (by linarith [divisorSquareDirichletMass_nonneg (9/8)])

/-- A power-saving arithmetic error for the literal signed sharp prefix.
No prime-density approximation or zero hypothesis occurs. -/
theorem sharp_count_error (X D : ℕ) :
    |(∑ n ∈ Finset.Icc 1 X, if Squarefree n then sharp D n else 0)-
      densityPrefix D*X| ≤
      countingConstant*(X : ℝ)^(3/4 : ℝ)*exp ((3/8 : ℝ)*log D) := by
  rw [count_eq_marks,densityPrefix,Finset.sum_mul,← Finset.sum_sub_distrib]
  have hm d : |(μ d : ℝ)*SquarefreeCounting.count d.primeFactors X-
      (μ d : ℝ)*SquarefreeCounting.density d.primeFactors*X| ≤
      (exp (primeSquareWeightMass (3/4))*(X : ℝ)^(3/4 : ℝ))*
        (|(μ d : ℝ)| *∏ p ∈ d.primeFactors, primeSquareCorrectedWeight (3/4) p) := by
    have hb := SquarefreeCounting.count_centered_bound d.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp)
      (by norm_num : (1/2 : ℝ)<3/4) (by norm_num : (3/4 : ℝ)≤1) X
    calc
      _ = |(μ d : ℝ)| *|SquarefreeCounting.count d.primeFactors X-
          SquarefreeCounting.density d.primeFactors*X| := by rw [← abs_mul]; congr 1; ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans_eq (by ring)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 D,
        (exp (primeSquareWeightMass (3/4))*(X : ℝ)^(3/4 : ℝ))*
          (|(μ d : ℝ)| *∏ p ∈ d.primeFactors, primeSquareCorrectedWeight (3/4) p) :=
      Finset.sum_le_sum (fun d _ => hm d)
    _ = (exp (primeSquareWeightMass (3/4))*(X : ℝ)^(3/4 : ℝ))*
        (∑ d ∈ Finset.Icc 1 D, |(μ d : ℝ)| *
          ∏ p ∈ d.primeFactors, primeSquareCorrectedWeight (3/4) p) := by rw [Finset.mul_sum]
    _ ≤ (exp (primeSquareWeightMass (3/4))*(X : ℝ)^(3/4 : ℝ))*
        (exp ((3/8 : ℝ)*log D)*divisorSquareDirichletMass (9/8)) :=
      mul_le_mul_of_nonneg_left (mark_sum_bound D) (by positivity)
    _ ≤ _ := by
      unfold countingConstant
      have h : 0 ≤ exp (primeSquareWeightMass (3/4))*(X : ℝ)^(3/4 : ℝ)*
          exp ((3/8 : ℝ)*log D) := by positivity
      nlinarith only [h]

/-- Below the square-root divisor cutoff the counting error has a fixed
one-sixteenth power saving relative to the full physical count. -/
theorem sharp_count_error_short {X D : ℕ} (hX : 0 < X) (hD : 0 < D)
    (hDX : D^2 ≤ X) :
    |(∑ n ∈ Finset.Icc 1 X, if Squarefree n then sharp D n else 0)-
      densityPrefix D*X| ≤ countingConstant*(X : ℝ)^(15/16 : ℝ) := by
  have hxr : (0 : ℝ)<X := by exact_mod_cast hX
  have hdr : (0 : ℝ)<D := by exact_mod_cast hD
  have hl : 2*log D ≤ log X := by
    have h := log_le_log (pow_pos hdr 2) (show (D : ℝ)^2 ≤ X by exact_mod_cast hDX)
    simpa only [log_pow,Nat.cast_ofNat] using h
  apply (sharp_count_error X D).trans
  have hp : (X : ℝ)^(3/4 : ℝ)*exp ((3/8 : ℝ)*log D) ≤ (X : ℝ)^(15/16 : ℝ) := by
    rw [rpow_def_of_pos hxr,rpow_def_of_pos hxr,← exp_add]
    apply exp_le_exp.mpr
    linarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp countingConstant_pos.le

private theorem centered_prefix (D k : ℕ) :
    (∑ n ∈ Finset.Icc 1 k,
      ((if Squarefree n then sharp D n else 0)-densityPrefix D)) =
      (∑ n ∈ Finset.Icc 1 k, if Squarefree n then sharp D n else 0)-densityPrefix D*k := by
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,
    nsmul_eq_mul,mul_comm]

private theorem weighted_error_eq (X D : ℕ) (w : ℕ → ℝ) (hend : w (X+1)=0) :
    (∑ n ∈ Finset.Icc 1 X, w n*(if Squarefree n then sharp D n else 0))-
      densityPrefix D*(∑ n ∈ Finset.Icc 1 X, w n) =
        ∑ k ∈ Finset.Icc 1 X, (w k-w (k+1))*
          ((∑ n ∈ Finset.Icc 1 k, if Squarefree n then sharp D n else 0)-densityPrefix D*k) := by
  rw [← Finset.sum_congr rfl (fun k _ => congrArg (fun z : ℝ => (w k-w (k+1))*z)
    (centered_prefix D k))]
  rw [← ZetaRieszSignedCutoffEnergy.abel_profile X w _ hend]
  simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- The full oscillating weight stays inside the signed main term. Every
mask jump and both exterior endpoints are charged by its exact variation. -/
theorem weighted_error (X D : ℕ) (w : ℕ → ℝ) (hend : w (X+1)=0) :
    |(∑ n ∈ Finset.Icc 1 X, w n*(if Squarefree n then sharp D n else 0))-
      densityPrefix D*(∑ n ∈ Finset.Icc 1 X, w n)| ≤
        countingConstant*exp ((3/8 : ℝ)*log D)*
          (∑ k ∈ Finset.Icc 1 X, (k : ℝ)^(3/4 : ℝ)*|w k-w (k+1)|) := by
  rw [weighted_error_eq X D w hend,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (sharp_count_error k D) (abs_nonneg _)).trans_eq (by ring)

/-- On exponentially large cofactors, short-cutoff counting errors gain
an explicit exponential factor BEFORE estimating the literal variation.
The remaining variation is displayed, not assumed bounded or paid. -/
theorem weighted_error_exponential (X D N : ℕ) (w : ℕ → ℝ) (b : ℝ)
    (hend : w (X+1)=0) (hD : 0 < D)
    (hshort : ∀ k ∈ Finset.Icc 1 X, w k ≠ w (k+1) → D^2 ≤ k)
    (hlower : ∀ k ∈ Finset.Icc 1 X, w k ≠ w (k+1) → exp (b*N) ≤ k) :
    |(∑ n ∈ Finset.Icc 1 X, w n*(if Squarefree n then sharp D n else 0))-
      densityPrefix D*(∑ n ∈ Finset.Icc 1 X, w n)| ≤
        countingConstant*exp (-(b*N)/16)*
          (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|w k-w (k+1)|) := by
  rw [weighted_error_eq X D w hend,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  by_cases hz : w k=w (k+1)
  · simp [hz]
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  have hkr : (0 : ℝ)<k := by exact_mod_cast hk0
  have hl : b*N ≤ log k := by
    simpa only [log_exp] using log_le_log (exp_pos _) (hlower k hk hz)
  have hp : (k : ℝ)^(15/16 : ℝ) ≤ exp (-(b*N)/16)*k := by
    conv_rhs => rw [← exp_log hkr]
    rw [rpow_def_of_pos hkr,← exp_add]
    apply exp_le_exp.mpr
    linarith
  rw [abs_mul]
  calc
    _ ≤ |w k-w (k+1)| *(countingConstant*(k : ℝ)^(15/16 : ℝ)) :=
      mul_le_mul_of_nonneg_left (sharp_count_error_short hk0 hD (hshort k hk hz)) (abs_nonneg _)
    _ ≤ |w k-w (k+1)| *(countingConstant*(exp (-(b*N)/16)*k)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp countingConstant_pos.le) (abs_nonneg _)
    _ = _ := by ring

/-- On an ordinary prime, the sharp prefix is exactly the unpaid unit until
the prime enters. This term must be removed when counting composite cofactors. -/
theorem sharp_prime {p D : ℕ} (hp : p.Prime) (hD : 0 < D) :
    sharp D p = if D < p then 1 else 0 := by
  have hp1 := hp.one_lt
  have he : (Finset.Icc 1 D).filter (fun d => d ∣ p) =
      if p ≤ D then {1,p} else {1} := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.dvd_prime hp]
    split_ifs with hd
    · simp only [Finset.mem_insert,Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro (rfl | rfl) <;> omega
    · simp only [Finset.mem_singleton]
      constructor
      · intro h
        rcases h.2 with h1 | h2
        · exact h1
        · omega
      · rintro rfl
        exact ⟨⟨by omega,by omega⟩,Or.inl rfl⟩
  unfold sharp
  rw [← Finset.sum_filter,he]
  by_cases hd : p ≤ D
  · simp [hd,not_lt.mpr hd,hp.ne_one.symm,ArithmeticFunction.moebius_apply_prime hp]
  · simp [hd,lt_of_not_ge hd]

/-- The unit survives every positive divisor cutoff. -/
theorem sharp_one {D : ℕ} (hD : 0 < D) : sharp D 1 = 1 := by
  simp [sharp,Nat.dvd_one,show 1 ≤ D by omega]

/-- Literal squarefree composite cofactors; both excluded populations are
accounted for in `composite_model` rather than absorbed in an error. -/
def compositePrefix (X : ℕ) : Finset ℕ :=
  (Finset.Ioc 1 X).filter (fun n => Squarefree n ∧ ¬n.Prime)

/-- The signed comparison term contains the exact prime-cofactor subtraction.
The weight includes its phase and every supplied mask, unchanged. -/
def compositeModel (X D : ℕ) (w : ℕ → ℝ) : ℝ :=
  densityPrefix D*(∑ n ∈ Finset.Icc 1 X, w n)-w 1-
    ∑ p ∈ (Finset.Icc 1 X).filter (fun p => p.Prime ∧ D < p), w p

/-- The literal owned rows cannot contain a unit or prime cofactor. This
applies to every original mask, not only an enlarged numerical population. -/
theorem ownerRows_empty_of_count_lt_two (B : Finset ℕ)
    (hB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card)
    {n : ℕ} (hn : n.primeFactors.card < 2) :
    ZetaRieszJointPrimeEnergy.ownerRows B n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨m,hm,_⟩ := Finset.mem_image.mp hp
  obtain ⟨hm,he⟩ := Finset.mem_filter.mp hm
  have hmem : n ∈ ZetaRieszJointPrimeEnergy.cofactors B :=
    Finset.mem_image.mpr ⟨m,hm,he⟩
  have hc := (ZetaRieszJointPrimeEnergy.cofactors_data B hB hmem).2
  omega

/-- The canonical zero extension of the actual masked weight vanishes on
excluded prime cofactors. A nonzero virtual prime subtraction therefore
requires a DIFFERENT extension, whose mask variation still needs control. -/
theorem literal_weight_zero_on_unit_or_prime (A B : Finset ℕ)
    (hB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card)
    (L y scale : ℝ) (N p n : ℕ) (hn : n = 1 ∨ n.Prime) :
    ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N n p = 0 := by
  have hc : n.primeFactors.card < 2 := by
    rcases hn with rfl | hn
    · simp
    · simp [hn.primeFactors]
  simp [ZetaRieszJointPrimeEnergy.maskedWeight,
    ownerRows_empty_of_count_lt_two B hB hc]

/-- For the actual zero-extended rows the entire model is its density term:
there is no signed prime subtraction available to cancel it. This is an
interface audit, not a bound for this main term or its mask variation. -/
theorem literal_compositeModel (A B : Finset ℕ)
    (hB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card)
    (L y scale : ℝ) (N p X D : ℕ) :
    compositeModel X D (fun n => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N n p) =
      densityPrefix D * (∑ n ∈ Finset.Icc 1 X,
        ZetaRieszJointPrimeEnergy.maskedWeight A
          (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N n p) := by
  dsimp only [compositeModel]
  rw [literal_weight_zero_on_unit_or_prime A B hB L y scale N p 1 (Or.inl rfl)]
  have hp : (∑ q ∈ (Finset.Icc 1 X).filter (fun q => q.Prime ∧ D < q),
      ZetaRieszJointPrimeEnergy.maskedWeight A
        (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N q p) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    exact literal_weight_zero_on_unit_or_prime A B hB L y scale N p q
      (Or.inr (Finset.mem_filter.mp hq).2.1)
  rw [hp,sub_zero,sub_zero]

/-- With canonical owner rows, any common cutoff profile factors through
one SIGNED arithmetic scalar. The cofactor weight is independent of `D`. -/
theorem literal_profile_factorization (A B : Finset ℕ)
    (hB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card)
    (L y scale : ℝ) (N p X R : ℕ) (f : ℕ → ℝ) :
    (∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*compositeModel X D
      (fun n => ZetaRieszJointPrimeEnergy.maskedWeight A
        (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N n p)) =
      (∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*densityPrefix D)*
        (∑ n ∈ Finset.Icc 1 X, ZetaRieszJointPrimeEnergy.maskedWeight A
          (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N n p) := by
  simp_rw [literal_compositeModel A B hB L y scale N p X]
  simp only [← mul_assoc,← Finset.sum_mul]

/-- Changing an excluded prime weight does not change the actual composite
sum. Thus the extension used by a main-term argument must be stated. -/
theorem correlation_prime_extension (X D : ℕ) (w : ℕ → ℝ) (a : ℝ)
    {q : ℕ} (hq : q.Prime) :
    correlation (compositePrefix X) (fun n => w n + if n = q then a else 0) D =
      correlation (compositePrefix X) w D := by
  unfold correlation
  apply Finset.sum_congr rfl
  intro n hn
  have hnq : n ≠ q := by
    intro he
    exact (Finset.mem_filter.mp hn).2.2 (he ▸ hq)
  simp [hnq]

/-- The SAME excluded-prime change moves the density/prime main term by
an exact nonzero coefficient in general. Its counting remainder must move
oppositely; an apparent gain in the extended main is not free cancellation. -/
theorem compositeModel_prime_extension (X D : ℕ) (w : ℕ → ℝ) (a : ℝ)
    {q : ℕ} (hq : q.Prime) (hqX : q ≤ X) (hDq : D < q) :
    compositeModel X D (fun n => w n + if n = q then a else 0) =
      compositeModel X D w + (densityPrefix D - 1)*a := by
  have hmem : q ∈ Finset.Icc 1 X := Finset.mem_Icc.mpr ⟨hq.one_lt.le,hqX⟩
  have hprime : q ∈ (Finset.Icc 1 X).filter (fun p => p.Prime ∧ D < p) :=
    Finset.mem_filter.mpr ⟨hmem,hq,hDq⟩
  simp only [compositeModel,Finset.sum_add_distrib,Finset.sum_ite_eq',
    if_pos hmem,if_pos hprime,if_neg hq.ne_one.symm,add_zero]
  ring

/-- Quantitative conservation of the purported main-term improvement:
every excluded-prime change is paid in full by the actual comparison error. -/
theorem comparison_error_prime_extension (X D : ℕ) (w : ℕ → ℝ) (a : ℝ)
    {q : ℕ} (hq : q.Prime) (hqX : q ≤ X) (hDq : D < q) :
    |(correlation (compositePrefix X) (fun n => w n + if n = q then a else 0) D -
        compositeModel X D (fun n => w n + if n = q then a else 0)) -
      (correlation (compositePrefix X) w D - compositeModel X D w)| =
        |densityPrefix D - 1| * |a| := by
  rw [correlation_prime_extension X D w a hq,
    compositeModel_prime_extension X D w a hq hqX hDq]
  have he : (correlation (compositePrefix X) w D -
      (compositeModel X D w + (densityPrefix D - 1)*a)) -
      (correlation (compositePrefix X) w D - compositeModel X D w) =
        -((densityPrefix D - 1)*a) := by ring
  rw [he,abs_neg,abs_mul]

/-- Exact prime and unit deletion, with no completion or prime approximation. -/
theorem composite_model {X D : ℕ} (hX : 0 < X) (hD : 0 < D) (w : ℕ → ℝ) :
    correlation (compositePrefix X) w D-compositeModel X D w =
      (∑ n ∈ Finset.Icc 1 X, w n*(if Squarefree n then sharp D n else 0))-
        densityPrefix D*(∑ n ∈ Finset.Icc 1 X, w n) := by
  have he : correlation (compositePrefix X) w D =
      (∑ n ∈ Finset.Icc 1 X,
        if Squarefree n ∧ ¬n.Prime ∧ n ≠ 1 then w n*sharp D n else 0) := by
    have hs : compositePrefix X = (Finset.Icc 1 X).filter
        (fun n => Squarefree n ∧ ¬n.Prime ∧ n ≠ 1) := by
      ext n
      simp only [compositePrefix,Finset.mem_filter,Finset.mem_Ioc,Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hn,hXn⟩,hs,hp⟩
        exact ⟨⟨by omega,hXn⟩,hs,hp,by omega⟩
      · rintro ⟨⟨hn,hXn⟩,hs,hp,h1⟩
        exact ⟨⟨by omega,hXn⟩,hs,hp⟩
    rw [correlation,hs,Finset.sum_filter]
  have hn n :
      w n*(if Squarefree n then sharp D n else 0) =
        (if Squarefree n ∧ ¬n.Prime ∧ n ≠ 1 then w n*sharp D n else 0)+
        (if n=1 then w 1 else 0)+
        (if n.Prime ∧ D < n then w n else 0) := by
    by_cases h1 : n=1
    · subst n
      simp [sharp_one hD,Nat.not_prime_one]
    by_cases hp : n.Prime
    · simp [hp,hp.squarefree,h1,sharp_prime hp hD]
    by_cases hs : Squarefree n <;> simp [h1,hp,hs]
  simp_rw [hn]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← he]
  have hunit : (∑ n ∈ Finset.Icc 1 X, if n=1 then w 1 else 0)=w 1 := by
    simp [show 1 ≤ X by omega]
  rw [hunit,← Finset.sum_filter]
  unfold compositeModel
  ring

/-- The actual composite-cofactor correlation has a power-counting error;
its density term and signed ordinary-prime subtraction both remain. -/
theorem composite_error {X D : ℕ} (hX : 0 < X) (hD : 0 < D)
    (w : ℕ → ℝ) (hend : w (X+1)=0) :
    |correlation (compositePrefix X) w D-compositeModel X D w| ≤
      countingConstant*exp ((3/8 : ℝ)*log D)*
        (∑ k ∈ Finset.Icc 1 X, (k : ℝ)^(3/4 : ℝ)*|w k-w (k+1)|) := by
  rw [composite_model hX hD w]
  exact weighted_error X D w hend

/-- Explicit exponential saving for a literal weighted composite prefix,
before any bound on its remaining signed main term or mask variation. -/
theorem composite_error_exponential {X D : ℕ} (hX : 0 < X) (hD : 0 < D)
    (N : ℕ) (w : ℕ → ℝ) (b : ℝ) (hend : w (X+1)=0)
    (hshort : ∀ k ∈ Finset.Icc 1 X, w k ≠ w (k+1) → D^2 ≤ k)
    (hlower : ∀ k ∈ Finset.Icc 1 X, w k ≠ w (k+1) → exp (b*N) ≤ k) :
    |correlation (compositePrefix X) w D-compositeModel X D w| ≤
      countingConstant*exp (-(b*N)/16)*
        (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|w k-w (k+1)|) := by
  rw [composite_model hX hD w]
  exact weighted_error_exponential X D N w b hend hD hshort hlower

/-- All cutoffs are recombined with their original signed profile increments.
The finite signed main term is not replaced by its termwise absolute value. -/
theorem profile_error_exponential {X R : ℕ} (hX : 0 < X)
    (N : ℕ) (w f : ℕ → ℝ) (b : ℝ) (hw : w (X+1)=0) (hf : f (R+1)=0)
    (hshort : ∀ k ∈ Finset.Icc 1 X, w k ≠ w (k+1) → R^2 ≤ k)
    (hlower : ∀ k ∈ Finset.Icc 1 X, w k ≠ w (k+1) → exp (b*N) ≤ k) :
    |(∑ n ∈ compositePrefix X, w n*(∑ d ∈ Finset.Icc 1 R,
        f d*(if d ∣ n then (μ d : ℝ) else 0)))-
      (∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*compositeModel X D w)| ≤
        countingConstant*exp (-(b*N)/16)*
          (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|w k-w (k+1)|)*
          (∑ D ∈ Finset.Icc 1 R, |f D-f (D+1)|) := by
  have he : (∑ n ∈ compositePrefix X, w n*(∑ d ∈ Finset.Icc 1 R,
      f d*(if d ∣ n then (μ d : ℝ) else 0))) =
      ∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*correlation (compositePrefix X) w D := by
    simp_rw [ZetaRieszSignedCutoffEnergy.abel_profile R f _ hf,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro D _
    simp only [correlation,sharp,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [he,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ D ∈ Finset.Icc 1 R, |f D-f (D+1)| *
        (countingConstant*exp (-(b*N)/16)*
          (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|w k-w (k+1)|)) := by
      apply Finset.sum_le_sum
      intro D hD
      rw [← mul_sub,abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact composite_error_exponential hX (Finset.mem_Icc.mp hD).1 N w b hw
        (fun k hk hz => (Nat.pow_le_pow_left (Finset.mem_Icc.mp hD).2 2).trans
          (hshort k hk hz)) hlower
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The canonical profile bridge keeps the main as one signed scalar times
the signed weight sum. The cutoff and weighted-variation obligations remain
explicit: the exponential prefactor alone does not pay those masks. -/
theorem literal_profile_error_exponential (A B : Finset ℕ)
    (hB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card)
    (L y scale : ℝ) (N p X R : ℕ) (f : ℕ → ℝ) (hX : 0 < X)
    (hw : ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N (X+1) p = 0)
    (hf : f (R+1)=0)
    (hshort : ∀ k ∈ Finset.Icc 1 X,
      ZetaRieszJointPrimeEnergy.maskedWeight A
        (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N k p ≠
      ZetaRieszJointPrimeEnergy.maskedWeight A
        (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N (k+1) p → R^2 ≤ k)
    (hlower : ∀ k ∈ Finset.Icc 1 X,
      ZetaRieszJointPrimeEnergy.maskedWeight A
        (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N k p ≠
      ZetaRieszJointPrimeEnergy.maskedWeight A
        (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N (k+1) p →
      exp ((N : ℝ)/2) ≤ k) :
    let w := fun n => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N n p
    |(∑ n ∈ compositePrefix X, w n*(∑ d ∈ Finset.Icc 1 R,
      f d*(if d ∣ n then (μ d : ℝ) else 0)))-
      (∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*densityPrefix D)*
        (∑ n ∈ Finset.Icc 1 X, w n)| ≤
      countingConstant*exp (-(N : ℝ)/32)*
        (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|w k-w (k+1)|)*
        (∑ D ∈ Finset.Icc 1 R, |f D-f (D+1)|) := by
  dsimp only
  have h := profile_error_exponential hX N
    (fun n => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N n p) f (1/2) hw hf hshort
    (by simpa only [show ∀ n : ℕ, (1/2 : ℝ)*n=(n : ℝ)/2 from fun n => by ring]
      using hlower)
  rw [literal_profile_factorization A B hB L y scale N p X R f] at h
  convert h using 1
  congr 3
  ring

/-- The error rate on cofactors above exp(N/2) defeats the actual worst
source-envelope growth, with a large explicit margin. -/
theorem source_rate_bound {u : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (N : ℕ) :
    (2*u)^N*exp (-(N : ℝ)/32) ≤ exp (-(3/100 : ℝ)*N) := by
  have hh : 2*u ≤ exp (1/800 : ℝ) := by
    have he := Real.add_one_le_exp (1/800 : ℝ)
    unfold ZetaRieszWideOwnerAudit.radiusCeiling at hu
    linarith
  have hn := pow_le_pow_left₀ (by positivity : 0 ≤ 2*u) hh N
  calc
    _ ≤ exp (1/800 : ℝ)^N*exp (-(N : ℝ)/32) :=
      mul_le_mul_of_nonneg_right hn (exp_pos _).le
    _ = _ := by rw [← exp_nat_mul,← exp_add]; congr 1; ring

/-- The cofactor factor of the literal product phase on one physical shell.
Any additional radial, allocation or support dependence stays in `a`. -/
def shellWeight (M X : ℕ) (a : ℕ → ℝ) (y c : ℝ) (n : ℕ) : ℝ :=
  if M < n ∧ n ≤ X then a n*cos (y*(c+log n))/(n : ℝ) else 0

private theorem log_step_bound {k : ℕ} (hk : 0 < k) :
    |log k-log (k+1 : ℕ)| ≤ 1/(k : ℝ) := by
  have hk0 : (0 : ℝ)<k := by exact_mod_cast hk
  have hk1 : (0 : ℝ)<(k+1 : ℕ) := by positivity
  have hle : log k ≤ log (k+1 : ℕ) := log_le_log hk0 (by exact_mod_cast Nat.le_succ k)
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  have hb := log_le_sub_one_of_pos (div_pos hk1 hk0)
  rw [log_div hk1.ne' hk0.ne'] at hb
  convert hb using 1 <;> push_cast <;> field_simp <;> ring

/-- The phase cost on a dyadic cofactor interval is independent of its
physical size. Exact amplitude variation and both boundary jumps remain. -/
theorem shellWeight_variation {M X : ℕ} (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    (a : ℕ → ℝ) (y c A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ n ∈ Finset.Ioc M X, |a n| ≤ A) :
    (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*
      |shellWeight M X a y c k-shellWeight M X a y c (k+1)|) ≤
        (3+|y|)*A+(∑ k ∈ Finset.Ico (M+1) X, |a k-a (k+1)|) := by
  let w := shellWeight M X a y c
  let V := Finset.Ico (M+1) X
  have hMr : (0 : ℝ)<M := by exact_mod_cast hM
  have hterm k (hk : k ∈ Finset.Icc 1 X) : (k : ℝ)*|w k-w (k+1)| ≤
      (if k=M then A else 0)+(if k=X then A else 0)+
        (if k ∈ V then |a k-a (k+1)|+A*(1+|y|)/(M : ℝ) else 0) := by
    have hk0 : (0 : ℝ)<k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hab n (hn : n ∈ Finset.Ioc M X) :
        |a n*cos (y*(c+log n))| ≤ A := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (abs_cos_le_one _) (abs_nonneg _)).trans
        (by simpa using ha n hn)
    by_cases he : k=M
    · subst k
      have hm1 : M+1 ∈ Finset.Ioc M X := Finset.mem_Ioc.mpr ⟨by omega,by omega⟩
      have hb := hab (M+1) hm1
      have hdiv : |a (M+1)*cos (y*(c+log (M+1 : ℕ)))/(M+1 : ℕ)| ≤ A/(M+1 : ℕ) := by
        rw [abs_div,abs_of_pos (by positivity : (0 : ℝ)<(M+1 : ℕ))]
        exact div_le_div_of_nonneg_right hb (by positivity)
      have hf : (M : ℝ)/(M+1 : ℕ) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        exact_mod_cast Nat.le_succ M
      simp only [w,shellWeight,lt_self_iff_false,false_and,ite_false,
        Finset.mem_Ioc.mp hm1,ite_true,zero_sub,abs_neg,show M≠X by omega,
        show M ∉ V by simp [V],add_zero]
      exact (mul_le_mul_of_nonneg_left hdiv hMr.le).trans
        ((show (M : ℝ)*(A/(M+1 : ℕ))=A*((M : ℝ)/(M+1 : ℕ)) by ring).le.trans
          (by simpa using mul_le_mul_of_nonneg_left hf hA))
    by_cases hx : k=X
    · subst k
      have hxV : X ∉ V := by simp [V]
      have hxI : X ∈ Finset.Ioc M X := Finset.mem_Ioc.mpr ⟨hMX,le_rfl⟩
      have hb := hab X hxI
      simp only [w,shellWeight,hMX,le_refl,and_self,ite_true,
        show ¬(M<X+1 ∧ X+1≤X) by omega,ite_false,sub_zero,
        he,hxV,zero_add,add_zero]
      rw [abs_div,abs_of_pos hk0,mul_div_cancel₀ _ hk0.ne']
      exact hb
    by_cases hv : k ∈ V
    · have hki := Finset.mem_Ico.mp hv
      have h1 : k ∈ Finset.Ioc M X := Finset.mem_Ioc.mpr ⟨by omega,by omega⟩
      have h2 : k+1 ∈ Finset.Ioc M X := Finset.mem_Ioc.mpr ⟨by omega,by omega⟩
      have hk10 : (0 : ℝ)<(k+1 : ℕ) := by positivity
      have hcos : |cos (y*(c+log k))-cos (y*(c+log (k+1 : ℕ)))| ≤ |y|/(k : ℝ) := by
        apply (abs_cos_sub_cos_le _ _).trans
        rw [show y*(c+log k)-y*(c+log (k+1 : ℕ))=y*(log k-log (k+1 : ℕ)) by ring,
          abs_mul]
        exact (mul_le_mul_of_nonneg_left (log_step_bound (Finset.mem_Icc.mp hk).1)
          (abs_nonneg y)).trans_eq (by ring)
      have hid : (k : ℝ)*(w k-w (k+1)) =
          (a k-a (k+1))*cos (y*(c+log k))+
          a (k+1)*(cos (y*(c+log k))-cos (y*(c+log (k+1 : ℕ))))+
          a (k+1)*cos (y*(c+log (k+1 : ℕ)))/(k+1 : ℕ) := by
        simp only [w,shellWeight,Finset.mem_Ioc.mp h1,Finset.mem_Ioc.mp h2,and_self,ite_true]
        push_cast
        field_simp
        ring
      have hb0 : |(a k-a (k+1))*cos (y*(c+log k))| ≤ |a k-a (k+1)| := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
      have hb1 : |a (k+1)*(cos (y*(c+log k))-cos (y*(c+log (k+1 : ℕ))))| ≤ A*|y|/k := by
        rw [abs_mul]
        exact (mul_le_mul (ha _ h2) hcos (abs_nonneg _) hA).trans_eq (by ring)
      have hb2 : |a (k+1)*cos (y*(c+log (k+1 : ℕ)))/(k+1 : ℕ)| ≤ A/(k+1 : ℕ) := by
        rw [abs_div,abs_of_pos hk10]
        exact div_le_div_of_nonneg_right (hab _ h2) hk10.le
      have h1M : A*|y|/(k : ℝ) ≤ A*|y|/(M : ℝ) :=
        div_le_div_of_nonneg_left (mul_nonneg hA (abs_nonneg _)) hMr
          (by exact_mod_cast (show M ≤ k by omega))
      have h2M : A/(k+1 : ℕ) ≤ A/(M : ℝ) :=
        div_le_div_of_nonneg_left hA hMr (by exact_mod_cast (show M ≤ k+1 by omega))
      simp only [he,hx,hv,ite_false,ite_true,zero_add]
      rw [← abs_of_pos hk0,← abs_mul,hid]
      calc
        _ ≤ |(a k-a (k+1))*cos (y*(c+log k))|+
            |a (k+1)*(cos (y*(c+log k))-cos (y*(c+log (k+1 : ℕ))))|+
            |a (k+1)*cos (y*(c+log (k+1 : ℕ)))/(k+1 : ℕ)| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ |a k-a (k+1)|+A*|y|/(k : ℝ)+A/(k+1 : ℕ) :=
          add_le_add (add_le_add hb0 hb1) hb2
        _ ≤ |a k-a (k+1)|+A*|y|/(M : ℝ)+A/(M : ℝ) :=
          add_le_add (add_le_add le_rfl h1M) h2M
        _ = _ := by ring
    · have hkM : k < M := by
        simp only [V,Finset.mem_Ico] at hv
        have := (Finset.mem_Icc.mp hk).2
        omega
      simp [w,shellWeight,show ¬M<k by omega,show ¬M<k+1 by omega,he,hx,hv]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 X, ((if k=M then A else 0)+(if k=X then A else 0)+
        (if k ∈ V then |a k-a (k+1)|+A*(1+|y|)/(M : ℝ) else 0)) := Finset.sum_le_sum hterm
    _ = 2*A+(∑ k ∈ V, |a k-a (k+1)|)+(V.card : ℝ)*(A*(1+|y|)/M) := by
      have hvS : V ⊆ Finset.Icc 1 X := by
        intro k hk
        have := Finset.mem_Ico.mp hk
        exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
      have hfilter : (Finset.Icc 1 X).filter (fun k => k ∈ V)=V :=
        Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr hvS)
      have hleft : (∑ k ∈ Finset.Icc 1 X, if k=M then A else 0)=A := by
        simp [show 1 ≤ M by omega,show M ≤ X by omega]
      have hright : (∑ k ∈ Finset.Icc 1 X, if k=X then A else 0)=A := by
        simp [show 1 ≤ X by omega]
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
      rw [hleft,hright,← Finset.sum_filter,hfilter,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have hc : (V.card : ℝ) ≤ M := by
        dsimp [V]
        rw [Nat.card_Ico]
        exact_mod_cast (show X-(M+1) ≤ M by omega)
      have hb := mul_le_mul_of_nonneg_right hc
        (show 0 ≤ A*(1+|y|)/(M : ℝ) by positivity)
      have hid : (M : ℝ)*(A*(1+|y|)/M)=A*(1+|y|) := by field_simp
      rw [hid] at hb
      dsimp [V] at *
      nlinarith only [hb]

/-- A concrete phase-retaining error bound on a physical shell. No loss
proportional to its integer population remains. The amplitude variation
includes the original allocation and any additional mask discontinuities. -/
theorem shell_composite_error {M X D : ℕ} (hM : 0 < M) (hMX : M < X)
    (hXM : X ≤ 2*M) (hD : 0 < D) (hDM : D^2 ≤ M)
    (N : ℕ) (hlarge : exp ((N : ℝ)/2) ≤ M)
    (a : ℕ → ℝ) (y c A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ n ∈ Finset.Ioc M X, |a n| ≤ A) :
    |correlation (compositePrefix X) (shellWeight M X a y c) D-
      compositeModel X D (shellWeight M X a y c)| ≤
        countingConstant*exp (-(N : ℝ)/32)*
          ((3+|y|)*A+(∑ k ∈ Finset.Ico (M+1) X, |a k-a (k+1)|)) := by
  have hactive k (_ : k ∈ Finset.Icc 1 X)
      (hz : shellWeight M X a y c k ≠ shellWeight M X a y c (k+1)) : M ≤ k := by
    by_contra h
    have hkM : k < M := lt_of_not_ge h
    simp [shellWeight,show ¬M<k by omega,show ¬M<k+1 by omega] at hz
  have hb := composite_error_exponential (show 0 < X by omega) hD N
    (shellWeight M X a y c) (1/2) (by simp [shellWeight])
    (fun k hk hz => hDM.trans (hactive k hk hz))
    (fun k hk hz => by
      have hMk : (M : ℝ) ≤ k := by exact_mod_cast hactive k hk hz
      have he : (1/2 : ℝ)*N=(N : ℝ)/2 := by ring
      rw [he]
      exact hlarge.trans hMk)
  have he : -((1/2 : ℝ)*N)/16=-(N : ℝ)/32 := by ring
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (shellWeight_variation hM hMX hXM a y c A hA ha)
    (mul_nonneg countingConstant_pos.le (exp_pos _).le))

end RiemannGaussian.ZetaRieszCofactorDiscrepancy
