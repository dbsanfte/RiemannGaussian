/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSignedConvolution
import RiemannGaussian.ZetaRoughSquarefreeCounting
import RiemannGaussian.ZetaRieszCofactorDiscrepancy
import RiemannGaussian.ZetaRieszOwnerMaximal
import RiemannGaussian.ZetaRieszPrimeCountMass
import RiemannGaussian.ZetaRieszCosineCarrier

/-!
# Counting errors on the unsigned divisor leg

The Möbius sign remains on the complementary divisor. Only the error in
counting the unsigned squarefree leg is estimated. Its full coprimality
sieve is retained; no prime-density approximation is made. The signed
density main and the small-divisor boundary are not asserted paid.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszUnsignedDivisorError

/-- The unsigned leg with every prime forbidden by the outer product
retained exactly. The actual sieve is not included in the smooth weight. -/
def sieve (S : Finset ℕ) (n : ℕ) : ℝ :=
  if Squarefree n ∧ (¬∃ p ∈ S, p ∣ n) then 1 else 0

/-- The counted unsigned mask is exactly squarefreeness of the ORIGINAL
product, when its outer product is squarefree. No coprimality condition
has been approximated or omitted. -/
theorem sieve_eq_product_squarefree {m : ℕ} (hm : Squarefree m) (d : ℕ) :
    sieve m.primeFactors d = if Squarefree (m*d) then 1 else 0 := by
  have hc : (¬∃ p ∈ m.primeFactors, p ∣ d) ↔ m.Coprime d := by
    constructor
    · intro h
      apply Nat.coprime_of_dvd
      intro p hp hpm hpd
      exact h ⟨p,Nat.mem_primeFactors.mpr ⟨hp,hpm,hm.ne_zero⟩,hpd⟩
    · intro h
      rintro ⟨p,hp,hpd⟩
      exact ((Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd.mp
        (h.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp))) hpd
  unfold sieve
  by_cases hs : Squarefree (m*d)
  · have hh := Nat.squarefree_mul_iff.mp hs
    rw [if_pos ⟨hh.2.2,hc.mpr hh.1⟩,if_pos hs]
  · have hh : ¬(Squarefree d ∧ ¬∃ p ∈ m.primeFactors, p ∣ d) := by
      rintro ⟨hd,hn⟩
      exact hs (Nat.squarefree_mul_iff.mpr ⟨hc.mp hn,hm,hd⟩)
    rw [if_neg hh,if_neg hs]

/-- The complete squarefree coprimality density, including every
intersection. It remains inside the signed arithmetic main. -/
def density (S : Finset ℕ) : ℝ :=
  ∑ W ∈ S.powerset, (-1 : ℝ)^W.card*SquarefreeCounting.density W

/-- A fixed constant for the squarefree lattice error. -/
def countingCost : ℝ := exp (primeSquareWeightMass (3/4))

theorem countingCost_pos : 0 < countingCost := exp_pos _

private theorem sieve_cast (S : Finset ℕ) (n : ℕ) :
    (sieve S n : ℂ) = RoughSquarefreeBare.coefficient S 1 n := by
  simp only [sieve,RoughSquarefreeBare.coefficient,one_dvd,and_true]
  split_ifs <;> simp

private theorem density_cast (S : Finset ℕ) :
    (density S : ℂ) = RoughSquarefreeCounting.markedDensity S 1 := by
  simp [density,RoughSquarefreeCounting.markedDensity,Complex.ofReal_sum]

/-- The same literal squarefree-coprimality error at any admissible
counting exponent. This changes only the error estimate, not its sieve. -/
def countingCostAt (σ : ℝ) : ℝ := exp (primeSquareWeightMass σ)

theorem countingCostAt_pos (σ : ℝ) : 0 < countingCostAt σ := exp_pos _

/-- All intersections of the original coprimality mask, at the chosen
squarefree counting exponent. -/
theorem prefix_error_product_at (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {σ : ℝ} (hσ : 1/2 < σ) (hσ1 : σ ≤ 1) (X : ℕ) :
    |(∑ d ∈ Finset.Icc 1 X, sieve S d)-density S*X| ≤
      countingCostAt σ*(X : ℝ)^σ*
        ∏ p ∈ S, (1+primeSquareCorrectedWeight σ p) := by
  have hc : RoughSquarefreeCounting.markedCount S 1 X =
      ((∑ d ∈ Finset.Icc 1 X, sieve S d : ℝ) : ℂ) := by
    simp only [RoughSquarefreeCounting.markedCount,← sieve_cast,Complex.ofReal_sum]
    congr 2
  have hp : |(∑ d ∈ Finset.Icc 1 X, sieve S d)-density S*X| =
      ‖RoughSquarefreeCounting.markedCount S 1 X-
        RoughSquarefreeCounting.markedDensity S 1*X‖ := by
    rw [hc,← density_cast,← Complex.ofReal_natCast,← Complex.ofReal_mul,← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs]
  rw [hp,RoughSquarefreeCounting.markedCount_centered_eq_subsets S hS
    (show Squarefree (1 : ℕ) by simp)]
  simp only [Nat.primeFactors_one,Finset.empty_union]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ W ∈ S.powerset,
        countingCostAt σ*(X : ℝ)^σ*∏ p ∈ W, primeSquareCorrectedWeight σ p := by
      apply Finset.sum_le_sum
      intro W hW
      have hb := SquarefreeCounting.count_centered_bound W
        (fun p hp => hS p (Finset.mem_powerset.mp hW hp)) hσ hσ1 X
      rw [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
        ← Complex.ofReal_natCast,← Complex.ofReal_mul,← Complex.ofReal_sub,
        Complex.norm_real,Real.norm_eq_abs]
      exact hb
    _ = _ := by rw [Finset.prod_one_add,Finset.mul_sum]

/-- The all-count intersection cost is still at most three per outer
prime even when the exponent is chosen close to one half. -/
theorem prefix_error_at (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {σ : ℝ} (hσ : 1/2 < σ) (hσ1 : σ ≤ 1) (X : ℕ) :
    |(∑ d ∈ Finset.Icc 1 X, sieve S d)-density S*X| ≤
      countingCostAt σ*3^S.card*(X : ℝ)^σ := by
  have hprod : (∏ p ∈ S, (1+primeSquareCorrectedWeight σ p)) ≤ (3 : ℝ)^S.card := by
    calc
      _ ≤ ∏ _p ∈ S, (3 : ℝ) := by
        apply Finset.prod_le_prod
        · intro p _
          positivity [primeSquareCorrectedWeight_nonneg σ p]
        · intro p _
          have ht : 0 ≤ zetaPrimeExpWeight σ p := by
            unfold zetaPrimeExpWeight; positivity
          have hu : zetaPrimeExpWeight σ p ≤ 1 := by
            rw [zetaPrimeExpWeight,exp_le_one_iff]
            nlinarith [log_natCast_nonneg p]
          unfold primeSquareCorrectedWeight
          nlinarith [mul_le_mul_of_nonneg_left hu ht]
      _ = _ := by simp
  exact (prefix_error_product_at S hS hσ hσ1 X).trans
    ((mul_le_mul_of_nonneg_left hprod (by positivity [countingCostAt_pos σ] :
      0 ≤ countingCostAt σ*(X : ℝ)^σ)).trans_eq (by ring))

/-- No maximum-prime cutoff appears in the coprimality counting cost.
The product of its actual factor corrections replaces the old exponential
in the square root of that cutoff. -/
theorem prefix_error_product (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (X : ℕ) :
    |(∑ d ∈ Finset.Icc 1 X, sieve S d)-density S*X| ≤
      countingCost*(X : ℝ)^(3/4 : ℝ)*
        ∏ p ∈ S, (1+primeSquareCorrectedWeight (3/4) p) := by
  have hc : RoughSquarefreeCounting.markedCount S 1 X =
      ((∑ d ∈ Finset.Icc 1 X, sieve S d : ℝ) : ℂ) := by
    simp only [RoughSquarefreeCounting.markedCount,← sieve_cast,Complex.ofReal_sum]
    congr 2
  have hp : |(∑ d ∈ Finset.Icc 1 X, sieve S d)-density S*X| =
      ‖RoughSquarefreeCounting.markedCount S 1 X-
        RoughSquarefreeCounting.markedDensity S 1*X‖ := by
    rw [hc,← density_cast,← Complex.ofReal_natCast,← Complex.ofReal_mul,← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs]
  rw [hp,RoughSquarefreeCounting.markedCount_centered_eq_subsets S hS
    (show Squarefree (1 : ℕ) by simp)]
  simp only [Nat.primeFactors_one,Finset.empty_union]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ W ∈ S.powerset,
        countingCost*(X : ℝ)^(3/4 : ℝ)*
          ∏ p ∈ W, primeSquareCorrectedWeight (3/4) p := by
      apply Finset.sum_le_sum
      intro W hW
      have hb := SquarefreeCounting.count_centered_bound W
        (fun p hp => hS p (Finset.mem_powerset.mp hW hp))
        (by norm_num : (1/2 : ℝ)<3/4) (by norm_num : (3/4 : ℝ)≤1) X
      rw [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
        ← Complex.ofReal_natCast,← Complex.ofReal_mul,← Complex.ofReal_sub,
        Complex.norm_real,Real.norm_eq_abs]
      exact hb
    _ = _ := by rw [Finset.prod_one_add,Finset.mul_sum]

/-- The intersection cost is at most three per outer prime. Summing this
cost later is a convergent count-generating problem, not a height cutoff. -/
theorem prefix_error (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (X : ℕ) :
    |(∑ d ∈ Finset.Icc 1 X, sieve S d)-density S*X| ≤
      countingCost*3^S.card*(X : ℝ)^(3/4 : ℝ) := by
  have hC := countingCost_pos.le
  have hprod : (∏ p ∈ S, (1+primeSquareCorrectedWeight (3/4) p)) ≤
      (3 : ℝ)^S.card := by
    calc
      _ ≤ ∏ _p ∈ S, (3 : ℝ) := by
        apply Finset.prod_le_prod
        · intro p _
          positivity [primeSquareCorrectedWeight_nonneg (3/4) p]
        · intro p _
          have ht : 0 ≤ zetaPrimeExpWeight (3/4) p := by
            unfold zetaPrimeExpWeight; positivity
          have hu : zetaPrimeExpWeight (3/4) p ≤ 1 := by
            rw [zetaPrimeExpWeight,exp_le_one_iff]
            nlinarith [log_natCast_nonneg p]
          unfold primeSquareCorrectedWeight
          nlinarith [mul_le_mul_of_nonneg_left hu ht]
      _ = _ := by simp
  exact (prefix_error_product S hS X).trans
    ((mul_le_mul_of_nonneg_left hprod (by positivity :
      0 ≤ countingCost*(X : ℝ)^(3/4 : ℝ))).trans_eq (by ring))

private theorem weighted_error_eq (S : Finset ℕ) (X : ℕ)
    (w : ℕ → ℝ) (hend : w (X+1)=0) :
    (∑ d ∈ Finset.Icc 1 X, w d*sieve S d)-
      density S*(∑ d ∈ Finset.Icc 1 X, w d) =
        ∑ k ∈ Finset.Icc 1 X, (w k-w (k+1))*
          ((∑ d ∈ Finset.Icc 1 k, sieve S d)-density S*k) := by
  have hc k : (∑ d ∈ Finset.Icc 1 k, (sieve S d-density S)) =
      (∑ d ∈ Finset.Icc 1 k, sieve S d)-density S*k := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Nat.card_Icc,
      Nat.add_sub_cancel,nsmul_eq_mul,mul_comm]
  simp_rw [← hc]
  rw [← ZetaRieszSignedCutoffEnergy.abel_profile X w _ hend]
  simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- The actual unsigned-leg error saves exp(-(1-σ)βN). The signed
density main, both boundary jumps and the full physical phase are kept. -/
theorem weighted_error_exponential_at (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {σ : ℝ} (hσ : 1/2 < σ) (hσ1 : σ ≤ 1)
    (X N : ℕ) (w : ℕ → ℝ) (β : ℝ) (hend : w (X+1)=0)
    (hlower : ∀ k ∈ Finset.Icc 1 X, w k ≠ w (k+1) → exp (β*N) ≤ k) :
    |(∑ d ∈ Finset.Icc 1 X, w d*sieve S d)-
      density S*(∑ d ∈ Finset.Icc 1 X, w d)| ≤
        countingCostAt σ*3^S.card*exp (-((1-σ)*β*N))*
          (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|w k-w (k+1)|) := by
  rw [weighted_error_eq S X w hend,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  by_cases hz : w k=w (k+1)
  · simp [hz]
  have hk0 : (0 : ℝ)<k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  have hl : β*N ≤ log k := by
    simpa only [log_exp] using log_le_log (exp_pos _) (hlower k hk hz)
  have hh : (k : ℝ)^σ ≤ exp (-((1-σ)*β*N))*k := by
    conv_rhs => rw [← exp_log hk0]
    rw [rpow_def_of_pos hk0,← exp_add]
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ 1-σ)]
  rw [abs_mul]
  exact ((mul_le_mul_of_nonneg_left (prefix_error_at S hS hσ hσ1 k) (abs_nonneg _)).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hh (by positivity [countingCostAt_pos σ] :
        0 ≤ countingCostAt σ*3^S.card))
      (abs_nonneg _))).trans_eq (by ring)

/-- On a large unsigned-leg interval, the quarter-power counting error
gains an exponential factor before any weight variation is estimated.
The prime phase and density main are retained exactly. -/
theorem weighted_error_exponential (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (X N : ℕ) (w : ℕ → ℝ) (β : ℝ) (hend : w (X+1)=0)
    (hlower : ∀ k ∈ Finset.Icc 1 X, w k ≠ w (k+1) → exp (β*N) ≤ k) :
    |(∑ d ∈ Finset.Icc 1 X, w d*sieve S d)-
      density S*(∑ d ∈ Finset.Icc 1 X, w d)| ≤
        countingCost*3^S.card*exp (-(β*N)/4)*
          (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|w k-w (k+1)|) := by
  have hC := countingCost_pos.le
  rw [weighted_error_eq S X w hend,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  by_cases hz : w k=w (k+1)
  · simp [hz]
  have hk0 : (0 : ℝ)<k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  have hl : β*N ≤ log k := by
    simpa only [log_exp] using log_le_log (exp_pos _) (hlower k hk hz)
  have hh : (k : ℝ)^(3/4 : ℝ) ≤ exp (-(β*N)/4)*k := by
    conv_rhs => rw [← exp_log hk0]
    rw [rpow_def_of_pos hk0,← exp_add]
    apply exp_le_exp.mpr
    linarith
  rw [abs_mul]
  exact ((mul_le_mul_of_nonneg_left (prefix_error S hS k) (abs_nonneg _)).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ countingCost*3^S.card))
      (abs_nonneg _))).trans_eq (by ring)

/-- Both exterior jumps and the full fixed-height phase are paid on the
unsigned-leg shell. Allocation variation is displayed, not hidden. -/
theorem shell_error (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {M X : ℕ} (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    (N : ℕ) (hlarge : exp ((N : ℝ)/10) ≤ M)
    (a : ℕ → ℝ) (y c A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ d ∈ Finset.Ioc M X, |a d| ≤ A) :
    let w := ZetaRieszCofactorDiscrepancy.shellWeight M X a y c
    |(∑ d ∈ Finset.Icc 1 X, w d*sieve S d)-
      density S*(∑ d ∈ Finset.Icc 1 X, w d)| ≤
        countingCost*3^S.card*exp (-(N : ℝ)/40)*
          ((3+|y|)*A+∑ d ∈ Finset.Ico (M+1) X, |a d-a (d+1)|) := by
  have hC := countingCost_pos.le
  dsimp only
  have hactive k (_ : k ∈ Finset.Icc 1 X)
      (hz : ZetaRieszCofactorDiscrepancy.shellWeight M X a y c k ≠
        ZetaRieszCofactorDiscrepancy.shellWeight M X a y c (k+1)) : M ≤ k := by
    by_contra hn
    have hkM : k < M := lt_of_not_ge hn
    simp [ZetaRieszCofactorDiscrepancy.shellWeight,show ¬M<k by omega,
      show ¬M<k+1 by omega] at hz
  have hb := weighted_error_exponential S hS X N
    (ZetaRieszCofactorDiscrepancy.shellWeight M X a y c) (1/10)
    (by simp [ZetaRieszCofactorDiscrepancy.shellWeight])
    (fun k hk hz => by
      have hMk : (M : ℝ) ≤ k := by exact_mod_cast hactive k hk hz
      simpa only [div_mul_eq_mul_div,one_mul] using hlarge.trans hMk)
  have he : -((1/10 : ℝ)*N)/4=-(N : ℝ)/40 := by ring
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (ZetaRieszCofactorDiscrepancy.shellWeight_variation hM hMX hXM a y c A hA ha)
    (by positivity : 0 ≤ countingCost*3^S.card*exp (-(N : ℝ)/40)))

/-- The full radial factorial amplitude, with the extra logarithm of
the literal Riesz coefficient. No order rectangle is introduced. -/
def radialMoment (N : ℕ) (T : ℝ) : ℝ :=
  exp (-T/2)*T^(N+1)/(N.factorial : ℝ)

/-- This envelope is used only for the unsigned-leg counting ERROR. -/
def radialEnvelope (N : ℕ) : ℝ := ((N : ℝ)+1)*2^(N+1)

theorem radialMoment_nonneg (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ radialMoment N T := by unfold radialMoment; positivity

theorem radialEnvelope_pos (N : ℕ) : 0 < radialEnvelope N := by
  unfold radialEnvelope; positivity

theorem radialMoment_le (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    radialMoment N T ≤ radialEnvelope N := by
  have hb := logMoment_exp_envelope (N+1) hT (by norm_num : (0 : ℝ)<1/2) (1/2)
  norm_num only [sub_self,zero_mul,exp_zero,mul_one,inv_div,one_div] at hb
  have hh := mul_le_mul_of_nonneg_left hb
    (by positivity : 0 ≤ (N : ℝ)+1)
  calc
    _ = ((N : ℝ)+1)*(T^(N+1)/(N+1).factorial*exp (-(1/2 : ℝ)*T)) := by
      unfold radialMoment
      rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      rw [show -T/2=-(1/2 : ℝ)*T by ring]
      field_simp
    _ ≤ _ := hh

private theorem radialMoment_derivative (N : ℕ) (T : ℝ) :
    HasDerivAt (radialMoment N)
      (exp (-T/2)*((N+1 : ℕ)*T^N-T^(N+1)/2)/(N.factorial : ℝ)) T := by
  have hd := ((((hasDerivAt_id T).neg.div_const 2).exp).mul
    ((hasDerivAt_id T).pow (N+1))).div_const (N.factorial : ℝ)
  apply hd.congr_deriv
  simp only [Pi.pow_apply,Pi.neg_apply,id_eq,mul_one,Nat.add_sub_cancel]
  push_cast
  ring

private theorem radialMoment_derivative_bound (N : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    ‖deriv (radialMoment N) T‖ ≤ ((N : ℝ)+2)*radialEnvelope N := by
  have hT0 : 0 < T := by linarith
  have he : deriv (radialMoment N) T =
      (((N : ℝ)+1)/T-1/2)*radialMoment N T := by
    rw [(radialMoment_derivative N T).deriv,radialMoment]
    push_cast
    rw [pow_succ]
    field_simp
  have hq : ((N : ℝ)+1)/T ≤ (N : ℝ)+1 :=
    div_le_self (by positivity) hT
  have hc : |((N : ℝ)+1)/T-1/2| ≤ (N : ℝ)+2 := by
    have hq0 : 0 ≤ ((N : ℝ)+1)/T := by positivity
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  rw [he,Real.norm_eq_abs,abs_mul,abs_of_nonneg (radialMoment_nonneg N hT0.le)]
  exact mul_le_mul hc (radialMoment_le N hT0.le)
    (radialMoment_nonneg N hT0.le) (by positivity)

/-- An explicit derivative estimate for the actual full factorial
amplitude. It costs only a polynomial before the quarter-power saving. -/
theorem radialMoment_lipschitz (N : ℕ) {T U : ℝ} (hT : 1 ≤ T) (hU : 1 ≤ U) :
    |radialMoment N T-radialMoment N U| ≤
      (((N : ℝ)+2)*radialEnvelope N)*|T-U| := by
  have ht : T ∈ Set.Icc 1 (max T U) := ⟨hT,le_max_left _ _⟩
  have hu : U ∈ Set.Icc 1 (max T U) := ⟨hU,le_max_right _ _⟩
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (radialMoment_derivative N t).hasDerivWithinAt)
      (fun t ht => by
        rw [← (radialMoment_derivative N t).deriv]
        exact radialMoment_derivative_bound N ht.1)
      (convex_Icc (1 : ℝ) (max T U)) hu ht

/-- The cofactor share increases when the unsigned leg increases. The
same exact owner weight still has total variation at most two. -/
theorem ownerWeight_variation_increasing {N : ℕ} (hN : 32 ≤ N)
    (m : ℕ) (x : ℕ → ℝ)
    (hx : ∀ i ≤ m, x i ∈ Set.Icc (0 : ℝ) 1)
    (hinc : ∀ i < m, x i ≤ x (i+1)) :
    (∑ i ∈ Finset.range m,
      |ZetaRieszOwnerMaximal.ownerWeight N (x i)-
        ZetaRieszOwnerMaximal.ownerWeight N (x (i+1))|) ≤ 2 := by
  let H := fun i => ZetaRieszOwnerMaximal.lowerMass (N+1) (13*N/32) (x i)
  let L := fun i => ZetaRieszOwnerMaximal.lowerMass (N+1) (N/5+1) (x i)
  have hH i (hi : i < m) : H (i+1) ≤ H i :=
    ZetaRieszOwnerMaximal.lowerMass_antitone _ _ (hx i (by omega))
      (hx (i+1) (by omega)) (hinc i hi)
  have hL i (hi : i < m) : L (i+1) ≤ L i :=
    ZetaRieszOwnerMaximal.lowerMass_antitone _ _ (hx i (by omega))
      (hx (i+1) (by omega)) (hinc i hi)
  have he i : ZetaRieszOwnerMaximal.ownerWeight N (x i) = 1-H i+L i := by
    rw [ZetaRieszOwnerMaximal.ownerWeight,
      ZetaRieszOwnerMaximal.ownerMass_eq_difference hN]
    dsimp [H,L]
    ring
  have hp i (hi : i ∈ Finset.range m) :
      |ZetaRieszOwnerMaximal.ownerWeight N (x i)-
        ZetaRieszOwnerMaximal.ownerWeight N (x (i+1))| ≤
      (H i-H (i+1))+(L i-L (i+1)) := by
    rw [he i,he (i+1)]
    have hh := hH i (Finset.mem_range.mp hi)
    have hl := hL i (Finset.mem_range.mp hi)
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  calc
    _ ≤ ∑ i ∈ Finset.range m, ((H i-H (i+1))+(L i-L (i+1))) := Finset.sum_le_sum hp
    _ = (H 0-H m)+(L 0-L m) := by
      rw [Finset.sum_add_distrib,Finset.sum_range_sub',Finset.sum_range_sub']
    _ ≤ 2 := by
      have hH0 := ZetaRieszOwnerMaximal.lowerMass_bounds (N+1) (13*N/32)
        (hx 0 (by omega)).1 (hx 0 (by omega)).2
      have hHm := ZetaRieszOwnerMaximal.lowerMass_bounds (N+1) (13*N/32)
        (hx m le_rfl).1 (hx m le_rfl).2
      have hL0 := ZetaRieszOwnerMaximal.lowerMass_bounds (N+1) (N/5+1)
        (hx 0 (by omega)).1 (hx 0 (by omega)).2
      have hLm := ZetaRieszOwnerMaximal.lowerMass_bounds (N+1) (N/5+1)
        (hx m le_rfl).1 (hx m le_rfl).2
      dsimp [H,L]
      linarith only [hH0.2,hHm.1,hL0.2,hLm.1]

/-- Joint amplitude variation: the complete factorial kernel and the
literal owner allocation are multiplied BEFORE any count error is paid. -/
theorem owned_radial_variation {N : ℕ} (hN : 32 ≤ N)
    (m : ℕ) (x T : ℕ → ℝ)
    (hx : ∀ i ≤ m, x i ∈ Set.Icc (0 : ℝ) 1)
    (hinc : ∀ i < m, x i ≤ x (i+1))
    (hT : ∀ i ≤ m, 1 ≤ T i) (hmono : ∀ i < m, T i ≤ T (i+1))
    (hspan : T m-T 0 ≤ 1) :
    (∑ i ∈ Finset.range m,
      |ZetaRieszOwnerMaximal.ownerWeight N (x i)*radialMoment N (T i)-
        ZetaRieszOwnerMaximal.ownerWeight N (x (i+1))*radialMoment N (T (i+1))|) ≤
      ((N : ℝ)+4)*radialEnvelope N := by
  let o := fun i => ZetaRieszOwnerMaximal.ownerWeight N (x i)
  let g := fun i => radialMoment N (T i)
  let C := radialEnvelope N
  have hC := (radialEnvelope_pos N).le
  have hg i (hi : i ≤ m) : 0 ≤ g i ∧ g i ≤ C :=
    ⟨radialMoment_nonneg N (by linarith [hT i hi]),
      radialMoment_le N (by linarith [hT i hi])⟩
  have ho i (hi : i ≤ m) : 0 ≤ o i ∧ o i ≤ 1 :=
    ZetaRieszOwnerMaximal.ownerWeight_bounds N (hx i hi).1 (hx i hi).2
  have hb i (hi : i ∈ Finset.range m) : |o i*g i-o (i+1)*g (i+1)| ≤
      C*|o i-o (i+1)|+((N : ℝ)+2)*C*(T (i+1)-T i) := by
    have hi' := Finset.mem_range.mp hi
    rw [show o i*g i-o (i+1)*g (i+1) =
      (o i-o (i+1))*g i+o (i+1)*(g i-g (i+1)) by ring]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul,abs_of_nonneg (hg i (by omega)).1,
      abs_of_nonneg (ho (i+1) (by omega)).1]
    have hv := radialMoment_lipschitz N (hT i (by omega)) (hT (i+1) (by omega))
    rw [abs_sub_comm (T i) (T (i+1)),
      abs_of_nonneg (sub_nonneg.mpr (hmono i hi'))] at hv
    exact add_le_add
      ((mul_le_mul_of_nonneg_left (hg i (by omega)).2 (abs_nonneg _)).trans_eq (by ring))
      ((mul_le_of_le_one_left (abs_nonneg _) (ho (i+1) (by omega)).2).trans hv)
  calc
    _ ≤ ∑ i ∈ Finset.range m,
        (C*|o i-o (i+1)|+((N : ℝ)+2)*C*(T (i+1)-T i)) := Finset.sum_le_sum hb
    _ = C*(∑ i ∈ Finset.range m, |o i-o (i+1)|)+((N : ℝ)+2)*C*(T m-T 0) := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,Finset.sum_range_sub]
    _ ≤ C*2+((N : ℝ)+2)*C*1 := add_le_add
      (mul_le_mul_of_nonneg_left (ownerWeight_variation_increasing hN m x hx hinc) hC)
      (mul_le_mul_of_nonneg_left hspan (by positivity))
    _ = _ := by dsimp [C]; ring

/-- The actual full owner amplitude in the unsigned divisor coordinate.
`P` is the marked prime logarithm and `c` is `log(p*b)`. -/
def ownedAmplitude (N : ℕ) (P c : ℝ) (d : ℕ) : ℝ :=
  ZetaRieszOwnerMaximal.ownerWeight N (1-P/(c+log d))*radialMoment N (c+log d)

theorem ownedAmplitude_bound (N : ℕ) {P c : ℝ} (hP : 0 ≤ P) {d : ℕ}
    (hT : 1 ≤ c+log d) (hPT : P ≤ c+log d) :
    |ownedAmplitude N P c d| ≤ radialEnvelope N := by
  have ht0 : 0 < c+log d := by linarith
  have hx : 1-P/(c+log d) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · have := (div_le_one ht0).mpr hPT; linarith
    · have := div_nonneg hP ht0.le; linarith
  have ho := ZetaRieszOwnerMaximal.ownerWeight_bounds N hx.1 hx.2
  rw [ownedAmplitude,abs_of_nonneg (mul_nonneg ho.1 (radialMoment_nonneg N ht0.le))]
  exact (mul_le_of_le_one_left (radialMoment_nonneg N ht0.le) ho.2).trans
    (radialMoment_le N ht0.le)

/-- No amplitude-variation premise is left on this dyadic shell.
The exact finite owner allocation and every factorial order are retained. -/
theorem ownedAmplitude_variation {N M X : ℕ} (hN : 32 ≤ N)
    (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    {P c : ℝ} (hP : 0 ≤ P)
    (hT : ∀ d ∈ Finset.Icc (M+1) X, 1 ≤ c+log d)
    (hPT : ∀ d ∈ Finset.Icc (M+1) X, P ≤ c+log d) :
    (∑ d ∈ Finset.Ico (M+1) X,
      |ownedAmplitude N P c d-ownedAmplitude N P c (d+1)|) ≤
        ((N : ℝ)+4)*radialEnvelope N := by
  let m := X-(M+1)
  let T := fun i : ℕ => c+log (i+(M+1) : ℕ)
  let x := fun i : ℕ => 1-P/T i
  have hem : m+(M+1)=X := Nat.sub_add_cancel (by omega)
  have hmem i (hi : i ≤ m) : i+(M+1) ∈ Finset.Icc (M+1) X :=
    Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hTi i (hi : i ≤ m) : 1 ≤ T i := hT _ (hmem i hi)
  have hx i (hi : i ≤ m) : x i ∈ Set.Icc (0 : ℝ) 1 := by
    have ht0 : 0 < T i := by linarith [hTi i hi]
    have hp := hPT _ (hmem i hi)
    constructor
    · have := (div_le_one ht0).mpr hp; dsimp [x]; linarith
    · have := div_nonneg hP ht0.le; dsimp [x]; linarith
  have hmono i (_hi : i < m) : T i ≤ T (i+1) := by
    dsimp [T]
    apply add_le_add_right
    exact log_le_log (by exact_mod_cast (show 0 < i+(M+1) by omega))
      (by exact_mod_cast (show i+(M+1) ≤ i+1+(M+1) by omega))
  have hinc i (hi : i < m) : x i ≤ x (i+1) := by
    have hv := div_le_div_of_nonneg_left hP (by linarith [hTi i (by omega)]) (hmono i hi)
    dsimp [x]
    linarith
  have hspan : T m-T 0 ≤ 1 := by
    have hMr : (0 : ℝ)<M := by exact_mod_cast hM
    have hX : (0 : ℝ)<X := by exact_mod_cast (by omega : 0<X)
    have hM1 : (0 : ℝ)<(M+1 : ℕ) := by positivity
    have hdiff : log (X : ℕ)-log (M+1 : ℕ) ≤ log 2 := by
      have hr : (X : ℝ)/(M+1 : ℕ) ≤ 2 := by
        apply (div_le_iff₀ hM1).mpr
        have hh : (X : ℝ) ≤ 2*M := by exact_mod_cast hXM
        push_cast
        linarith
      rw [← log_div hX.ne' hM1.ne']
      exact log_le_log (div_pos hX hM1) hr
    dsimp [T]
    rw [hem]
    simp only [Nat.zero_add,add_sub_add_left_eq_sub]
    linarith [log_two_lt_d9]
  have hb := owned_radial_variation hN m x T hx hinc hTi hmono hspan
  rw [Finset.sum_Ico_eq_sum_range]
  convert hb using 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2 <;> norm_num [ownedAmplitude,x,T,add_assoc,add_comm,add_left_comm]

/-- A concrete signed comparison for the ORIGINAL owner factorial
amplitude. Its density remains one signed phase sum, and its error has
`exp(-N/40)` with no count, share or variation premise. -/
theorem owned_shell_error (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {N M X : ℕ} (hN : 32 ≤ N) (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    (hlarge : exp ((N : ℝ)/10) ≤ M) {P c : ℝ} (hP : 0 ≤ P)
    (hT : ∀ d ∈ Finset.Icc (M+1) X, 1 ≤ c+log d)
    (hPT : ∀ d ∈ Finset.Icc (M+1) X, P ≤ c+log d) (y : ℝ) :
    let w := ZetaRieszCofactorDiscrepancy.shellWeight M X (ownedAmplitude N P c) y c
    |(∑ d ∈ Finset.Icc 1 X, w d*sieve S d)-
      density S*(∑ d ∈ Finset.Icc 1 X, w d)| ≤
        countingCost*3^S.card*exp (-(N : ℝ)/40)*
          (((N : ℝ)+7+|y|)*radialEnvelope N) := by
  have hb := shell_error S hS hM hMX hXM N hlarge (ownedAmplitude N P c) y c
    (radialEnvelope N) (radialEnvelope_pos N).le
    (fun d hd => ownedAmplitude_bound N hP
      (hT d (Finset.mem_Icc.mpr ⟨by have := Finset.mem_Ioc.mp hd; omega,(Finset.mem_Ioc.mp hd).2⟩))
      (hPT d (Finset.mem_Icc.mpr ⟨by have := Finset.mem_Ioc.mp hd; omega,(Finset.mem_Ioc.mp hd).2⟩)))
  apply hb.trans
  have hC := countingCost_pos.le
  have ht := ownedAmplitude_variation hN hM hMX hXM hP hT hPT
  calc
    _ ≤ countingCost*3^S.card*exp (-(N : ℝ)/40)*
        ((3+|y|)*radialEnvelope N+((N : ℝ)+4)*radialEnvelope N) :=
      mul_le_mul_of_nonneg_left (add_le_add_right ht ((3+|y|)*radialEnvelope N))
        (by positivity)
    _ = _ := by ring

open ZetaRieszSignedConvolution
open scoped ArithmeticFunction.Moebius

/-- Exact identification with the original owner incidence. This keeps
the full phase, the full factorial order and the literal allocation. The
unsigned-leg comparison does not introduce a different kernel. -/
theorem owner_phase_eq_amplitude (A : Finset ℕ) (N : ℕ) (L y : ℝ)
    {p b d : ℕ} (hp : p.Prime) (hb : 0 < b) (hd : 0 < d)
    (hs : Squarefree (b*d)) (hc : 2 ≤ (b*d).primeFactors.card)
    (hmax : ∀ q ∈ (b*d).primeFactors, q < p) (hpA : p ∈ A) :
    (phaseWeight (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*(b*d))})
      L N y (b*d) p).re =
      ownedAmplitude N (log p) (log (p*b : ℕ)) d*
        cos (y*(log (p*b : ℕ)+log d))/(L*(p*b : ℕ)*d) := by
  have hp0 : (0 : ℝ)<p := by exact_mod_cast hp.pos
  have hb0 : (0 : ℝ)<b := by exact_mod_cast hb
  have hd0 : (0 : ℝ)<d := by exact_mod_cast hd
  have hn0 : (0 : ℝ)<(p*(b*d) : ℕ) := by
    exact_mod_cast Nat.mul_pos hp.pos (Nat.mul_pos hb hd)
  have hlog : log (p*(b*d) : ℕ) = log (p*b : ℕ)+log d := by
    rw [show p*(b*d)=(p*b)*d by ac_rfl,Nat.cast_mul,
      log_mul (by exact_mod_cast (Nat.mul_pos hp.pos hb).ne') hd0.ne']
  have hco : log (b*d : ℕ)/log (p*(b*d) : ℕ) =
      1-log p/(log (p*b : ℕ)+log d) := by
    have hT : 0 < log (p*(b*d) : ℕ) :=
      log_pos (by exact_mod_cast (show 1 < p*(b*d) by
        have hbd : 1 ≤ b*d := Nat.succ_le_of_lt (Nat.mul_pos hb hd)
        exact lt_of_lt_of_le hp.one_lt (Nat.le_mul_of_pos_right p (by omega))))
    rw [← hlog]
    have hpa : log (p*(b*d) : ℕ)=log p+log (b*d : ℕ) := by
      rw [Nat.cast_mul,log_mul hp0.ne' (by positivity : ((b*d : ℕ) : ℝ) ≠ 0)]
    field_simp
    linarith only [hpa]
  have hw := ZetaRieszOwnerMaximal.ownerWeight_eq_fibre A N hs hc hp hmax hpA
  rw [phaseWeight,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    ← ZetaRieszJointAllocation.filter_one_eq,
    ZetaRieszCosineCarrier.re_filterKernel_one,← hw,hco]
  have he : exp (-(3/2 : ℝ)*log (p*(b*d) : ℕ)) =
      exp (-log (p*(b*d) : ℕ)/2)/(p*(b*d) : ℕ) := by
    calc
      _ = exp (-log (p*(b*d) : ℕ)/2+-log (p*(b*d) : ℕ)) := by congr 1; ring
      _ = exp (-log (p*(b*d) : ℕ)/2)*(exp (log (p*(b*d) : ℕ)))⁻¹ := by
        rw [exp_add,exp_neg]
      _ = _ := by simp only [exp_log hn0,div_eq_mul_inv]
  rw [he,hlog,ownedAmplitude,radialMoment]
  push_cast
  ring

/-- On a saturated owner row, every active complemented-divisor
incidence has unsigned leg strictly below the owner. This pays no phase
and removes no prime: it checks the original largest-prime condition. -/
theorem active_unsigned_lt_owner {L : ℝ} {p b d : ℕ}
    (hp : 0 < p) (hb : 0 < b) (hd : 0 < d)
    (hsat : log (b*d : ℕ) ≤ L) (hactive : pairHinge L p b ≠ 0) : d < p := by
  have ha := ZetaRieszSignedConvolution.pairHinge_active hactive
  have hlog : log (b*d : ℕ)=log b+log d := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hb.ne') (by exact_mod_cast hd.ne')]
  have hdp : log d < log p := by rw [hlog] at hsat; linarith
  exact_mod_cast (log_lt_log_iff (by exact_mod_cast hd) (by exact_mod_cast hp)).mp hdp

/-- Checking all inherited masks requires only the actual squarefree
count cutoff, the original core window and strict nondominant prime
shares. Thus these masks need not be put into the smooth Abel weight. -/
theorem mem_core_of_strict_prime_share (j : ℕ) (hj : 32 ≤ j) {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hL : (11/8 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
    {n : ℕ} (hs : Squarefree n) (hc : 3 ≤ n.primeFactors.card)
    (hK : n.primeFactors.card < ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)
    (hlo : (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j < log n)
    (hhi : log n ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
    (hmax : ∀ p ∈ n.primeFactors, log p < (13/20 : ℝ)*log n) :
    n ∈ ZetaRieszParityPacket.coreBand u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
      (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) := by
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  have hN : (0 : ℝ)<N := by
    dsimp [N,ZetaRieszPrimeCountFrequency.dyadicMomentOrder,
      ZetaRieszPrimeCountFrequency.dyadicPrimeCount]
    positivity
  have ht : 0 < log n := by change (39/20 : ℝ)*N < _ at hlo; linarith
  have hW : n ∈ ZetaRieszJointAllocation.literalWindow N :=
    (ZetaRieszJointAllocation.mem_literalWindow N n).mpr
      (by constructor <;> dsimp [N] at * <;> nlinarith)
  have hpX : ∀ p ∈ n.primeFactors,
      p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 := by
    intro p hp
    have hplog : log p < SquarefreeVaughanLogSource.length u N := by
      have hm := hmax p hp
      change log n ≤ (203/100 : ℝ)*N at hhi
      change (11/8 : ℝ)*N ≤ _ at hL
      nlinarith
    have he : log (((ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 : ℕ) : ℝ) =
        SquarefreeVaughanLogSource.length u N := by
      simp only [SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
    exact_mod_cast (log_lt_log_iff (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
      (by positivity)).mp (he ▸ hplog)
  have hm := ZetaRieszMaskSupport.window_mem_originalMask j hj hu
    (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le)
    (show (5/4 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N by
      change (11/8 : ℝ)*N ≤ _ at hL; linarith) hW hs hc hK hpX
  have hcancel : n ∉ ZetaRieszJointAllocation.cancellingSector u N K := by
    intro hh
    obtain ⟨_,_,_,_,_,p,hp,_,_,_,hshare⟩ := Finset.mem_filter.mp hh
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hd : log (n/p : ℕ)=log n-log p := by
      rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors hp) (by exact_mod_cast hpp.ne_zero),
        log_div (by exact_mod_cast hs.ne_zero) (by exact_mod_cast hpp.ne_zero)]
    have hh := (div_le_iff₀ ht).mp hshare
    rw [hd] at hh
    nlinarith [hmax p hp]
  have hret : n ∈ ZetaRieszMaskSupport.retainedBand u N K :=
    Finset.mem_sdiff.mpr ⟨hm,hcancel⟩
  have hnd : n ∈ ZetaRieszDominantAllocation.nondominantBand u N K := by
    refine Finset.mem_sdiff.mpr ⟨hret,?_⟩
    intro hd
    obtain ⟨_,_,_,_,p,hp,_,_,hl⟩ := Finset.mem_filter.mp hd
    exact (hmax p hp).not_ge hl
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨hnd,by constructor <;> dsimp [N] at * <;> nlinarith⟩,hlo,hhi⟩

/-- The joined hinge has a bounded scalar length; its divisor signs
remain in the main. This bound is used only for counting discrepancies. -/
theorem pairHinge_bounds (L : ℝ) (p b : ℕ) :
    0 ≤ pairHinge L p b ∧ pairHinge L p b ≤ log p := by
  have hp := log_natCast_nonneg p
  unfold pairHinge
  by_cases hb : 0 ≤ log b-L
  · rw [max_eq_right hb,max_eq_right (show 0 ≤ log p+log b-L by linarith)]
    constructor <;> linarith
  · rw [max_eq_left (le_of_not_ge hb)]
    by_cases hpb : 0 ≤ log p+log b-L
    · rw [max_eq_right hpb]; constructor <;> linarith
    · rw [max_eq_left (le_of_not_ge hpb)]; constructor <;> linarith

/-- A partial selection of literal divisor incidences has a coefficient
majorant on its ORIGINAL product label. This is used only to pay the
high-count completion boundary, never the retained signed density main. -/
theorem partial_hinge_majorant {p a : ℕ} (hp : 0 < p) (ha : 0 < a)
    (D : Finset (ℕ×ℕ)) (hD : D ⊆ a.divisorsAntidiagonal) (L : ℝ) :
    |∑ db ∈ D, (μ db.2 : ℝ)*pairHinge L p db.2| ≤
      zetaMoebiusLogMajorant (p*a) := by
  let f : ℕ×ℕ → ℕ×ℕ := fun db => (db.1,p*db.2)
  have hfinj : Function.Injective f := by
    intro x y h
    apply Prod.ext
    · simpa only [f] using congrArg (fun v : ℕ×ℕ => v.1) h
    · have hxy := congrArg (fun v : ℕ×ℕ => v.2) h
      exact Nat.eq_of_mul_eq_mul_left hp hxy
  have hsub : D.image f ⊆ (p*a).divisorsAntidiagonal := by
    intro db hdb
    obtain ⟨dc,hdc,rfl⟩ := Finset.mem_image.mp hdb
    have he := Nat.mem_divisorsAntidiagonal.mp (hD hdc)
    apply Nat.mem_divisorsAntidiagonal.mpr
    constructor
    · dsimp [f]
      calc
        dc.1*(p*dc.2)=p*(dc.1*dc.2) := by ac_rfl
        _ = p*a := by rw [he.1]
    · exact (Nat.mul_pos hp ha).ne'
  calc
    _ ≤ ∑ db ∈ D, |(μ db.2 : ℝ)*pairHinge L p db.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ db ∈ D, log p := by
      apply Finset.sum_le_sum
      intro db _
      have hh := pairHinge_bounds L p db.2
      have hm : |(μ db.2 : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := db.2)
      rw [abs_mul,abs_of_nonneg hh.1]
      exact (mul_le_of_le_one_left hh.1 hm).trans hh.2
    _ ≤ ∑ db ∈ D, log (p*db.2 : ℕ) := by
      apply Finset.sum_le_sum
      intro db hdb
      have hb : 0 < db.2 := Nat.pos_of_mem_divisors
        (Nat.snd_mem_divisors_of_mem_antidiagonal (hD hdb))
      rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne') (by exact_mod_cast hb.ne')]
      linarith [log_natCast_nonneg db.2]
    _ = ∑ db ∈ D.image f, log db.2 := by
      rw [Finset.sum_image (fun _ _ _ _ h => hfinj h)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun db _ _ => log_natCast_nonneg db.2)

/-- A bounded frozen row multiplier is permitted on the count boundary.
This estimate is not applied to the retained signed density main. -/
theorem weighted_partial_hinge_majorant {p a : ℕ} (hp : 0 < p) (ha : 0 < a)
    (D : Finset (ℕ×ℕ)) (hD : D ⊆ a.divisorsAntidiagonal) (L : ℝ)
    (κ : ℕ×ℕ → ℝ) (hκ : ∀ db ∈ D, |κ db| ≤ 4) :
    |∑ db ∈ D, κ db*(μ db.2 : ℝ)*pairHinge L p db.2| ≤
      4*zetaMoebiusLogMajorant (p*a) := by
  let f : ℕ×ℕ → ℕ×ℕ := fun db => (db.1,p*db.2)
  have hfinj : Function.Injective f := by
    intro x y h
    apply Prod.ext
    · simpa only [f] using congrArg (fun v : ℕ×ℕ => v.1) h
    · have hxy := congrArg (fun v : ℕ×ℕ => v.2) h
      exact Nat.eq_of_mul_eq_mul_left hp hxy
  have hsub : D.image f ⊆ (p*a).divisorsAntidiagonal := by
    intro db hdb
    obtain ⟨dc,hdc,rfl⟩ := Finset.mem_image.mp hdb
    have he := Nat.mem_divisorsAntidiagonal.mp (hD hdc)
    apply Nat.mem_divisorsAntidiagonal.mpr
    constructor
    · dsimp [f]
      calc
        dc.1*(p*dc.2)=p*(dc.1*dc.2) := by ac_rfl
        _ = p*a := by rw [he.1]
    · exact (Nat.mul_pos hp ha).ne'
  calc
    _ ≤ ∑ db ∈ D, |κ db*(μ db.2 : ℝ)*pairHinge L p db.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _db ∈ D, 4*log p := by
      apply Finset.sum_le_sum
      intro db hdb
      have hh := pairHinge_bounds L p db.2
      have hm : |(μ db.2 : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := db.2)
      rw [abs_mul,abs_mul,abs_of_nonneg hh.1]
      have ht := (mul_le_of_le_one_left hh.1 hm).trans hh.2
      calc
        _ = |κ db| * (|(μ db.2 : ℝ)| * pairHinge L p db.2) := by ring
        _ ≤ 4*log p := mul_le_mul (hκ db hdb) ht
          (mul_nonneg (abs_nonneg _) hh.1) (by norm_num)
    _ ≤ ∑ db ∈ D, 4*log (p*db.2 : ℕ) := by
      apply Finset.sum_le_sum
      intro db hdb
      have hb : 0 < db.2 := Nat.pos_of_mem_divisors
        (Nat.snd_mem_divisors_of_mem_antidiagonal (hD hdb))
      rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne') (by exact_mod_cast hb.ne')]
      linarith [log_natCast_nonneg db.2]
    _ = 4*∑ db ∈ D.image f, log db.2 := by
      rw [Finset.mul_sum]
      rw [Finset.sum_image (fun _ _ _ _ h => hfinj h)]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun db _ _ => log_natCast_nonneg db.2)) (by norm_num)

/-- Exact weighted original divisor coefficient, for bounded-row
comparison/count errors only. -/
def weightedPartialCoefficient (A : Finset ℕ) (L : ℝ) (N p a : ℕ)
    (D : Finset (ℕ×ℕ)) (κ : ℕ×ℕ → ℝ) : ℂ :=
  ((((1-ZetaRieszJointAllocation.boundedShare A N (p*a))*log (p*a : ℕ)/L)*
    (∑ db ∈ D, κ db*(μ db.2 : ℝ)*pairHinge L p db.2) : ℝ) : ℂ)

/-- The actual high-count error with a frozen multiplier bounded by four
has the same literal majorant with factor eight. -/
theorem weightedPartialCoefficient_bound (A : Finset ℕ) (N : ℕ) {p a : ℕ}
    (hp : 0 < p) (ha : 0 < a) (D : Finset (ℕ×ℕ))
    (hD : D ⊆ a.divisorsAntidiagonal) {L : ℝ} (hL : 0 < L)
    (hT : log (p*a : ℕ) ≤ 2*L) (κ : ℕ×ℕ → ℝ)
    (hκ : ∀ db ∈ D, |κ db| ≤ 4) :
    ‖weightedPartialCoefficient A L N p a D κ‖ ≤
      8*zetaMoebiusLogMajorant (p*a) := by
  have hw := ZetaRieszJointAllocation.boundedShare_bounds A N (p*a)
  have hscale : 0 ≤ (1-ZetaRieszJointAllocation.boundedShare A N (p*a))*log (p*a : ℕ)/L := by
    apply div_nonneg
    · exact mul_nonneg (by linarith only [hw.2]) (log_natCast_nonneg _)
    · exact hL.le
  have hscale2 : (1-ZetaRieszJointAllocation.boundedShare A N (p*a))*log (p*a : ℕ)/L ≤ 2 := by
    apply (div_le_iff₀ hL).mpr
    exact (mul_le_of_le_one_left (log_natCast_nonneg _) (by linarith only [hw.1])).trans hT
  rw [weightedPartialCoefficient,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg hscale]
  exact (mul_le_mul hscale2 (weighted_partial_hinge_majorant hp ha D hD L κ hκ)
    (abs_nonneg _) (by norm_num)).trans_eq (by ring)

/-- A restricted incidence coefficient of the SAME original factorial
atom. The selection may contain every window/count/physical mask. -/
def partialCoefficient (A : Finset ℕ) (L : ℝ) (N p a : ℕ)
    (D : Finset (ℕ×ℕ)) : ℂ :=
  ((((1-ZetaRieszJointAllocation.boundedShare A N (p*a))*log (p*a : ℕ)/L)*
    (∑ db ∈ D, (μ db.2 : ℝ)*pairHinge L p db.2) : ℝ) : ℂ)

/-- The comparison count boundary inherits a fixed factor-two version
of the existing high-count majorant. No phase or selected incidence is
completed in this inequality. -/
theorem partialCoefficient_bound (A : Finset ℕ) (N : ℕ) {p a : ℕ}
    (hp : 0 < p) (ha : 0 < a) (D : Finset (ℕ×ℕ))
    (hD : D ⊆ a.divisorsAntidiagonal) {L : ℝ} (hL : 0 < L)
    (hT : log (p*a : ℕ) ≤ 2*L) :
    ‖partialCoefficient A L N p a D‖ ≤ 2*zetaMoebiusLogMajorant (p*a) := by
  have hw := ZetaRieszJointAllocation.boundedShare_bounds A N (p*a)
  have hscale : 0 ≤ (1-ZetaRieszJointAllocation.boundedShare A N (p*a))*log (p*a : ℕ)/L := by
    apply div_nonneg
    · exact mul_nonneg (by linarith only [hw.2]) (log_natCast_nonneg _)
    · exact hL.le
  have hscale2 : (1-ZetaRieszJointAllocation.boundedShare A N (p*a))*log (p*a : ℕ)/L ≤ 2 := by
    apply (div_le_iff₀ hL).mpr
    exact (mul_le_of_le_one_left (log_natCast_nonneg _) (by linarith only [hw.1])).trans hT
  rw [partialCoefficient,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg hscale]
  exact mul_le_mul hscale2 (partial_hinge_majorant hp ha D hD L)
    (abs_nonneg _) (by norm_num)

/-- Removing the literal high-count cutoff from ANY selected owner
divisor incidences costs source-o(1), uniformly in moving phase heights.
This discharges the count-mask error; it does not bound the lower-count
signed convolution. -/
theorem tendsto_high_count_partial_incidence (S : ℕ → Finset ℕ)
    (A : ℕ → ℕ → Finset ℕ) (D : ℕ → ℕ → Finset (ℕ×ℕ))
    (p a : ℕ → ℕ → ℕ) (L y : ℕ → ℝ) {u : ℝ}
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hL : ∀ j, 0 < L j)
    (hS : ∀ j n, n ∈ S j → Squarefree n ∧
      n ∈ zetaPrimeLogBand (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) ∧
      ZetaRieszPrimeCountFrequency.dyadicPrimeCount j ≤ n.primeFactors.card)
    (hp : ∀ j n, n ∈ S j → 0 < p j n)
    (ha : ∀ j n, n ∈ S j → 0 < a j n)
    (he : ∀ j n, n ∈ S j → p j n*a j n=n)
    (hD : ∀ j n, n ∈ S j → D j n ⊆ (a j n).divisorsAntidiagonal)
    (hT : ∀ j n, n ∈ S j → log n ≤ 2*L j) :
    Tendsto (fun j => (u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      ∑ n ∈ S j, partialCoefficient (A j n) (L j)
        (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (p j n) (a j n) (D j n)*
          zetaPrimeLogKernel (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
            (3/2+Complex.I*y j) n) atTop (𝓝 0) := by
  let c := fun j n => partialCoefficient (A j n) (L j)
    (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (p j n) (a j n) (D j n)/2
  have hc j n (hn : n ∈ S j) : ‖c j n‖ ≤ zetaMoebiusLogMajorant n := by
    have hb := partialCoefficient_bound (A j n)
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (hp j n hn) (ha j n hn) (D j n)
      (hD j n hn) (hL j) (by simpa only [he j n hn] using hT j n hn)
    rw [he j n hn] at hb
    dsimp [c]
    rw [norm_div]
    norm_num
    linarith
  have ht := ZetaRieszWeightedCount.tendsto_normalized_many_sum 1 S c hc
    (fun _ => u) y (fun _ => hu) (fun _ => hU)
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
    (fun j n hn => (hS j n hn).1) (fun j n hn => (hS j n hn).2.1)
    (fun j n hn => (hS j n hn).2.2)
  have h := ht.const_mul (2 : ℂ)
  simp only [mul_zero] at h
  convert h using 1
  ext j
  calc
    _ = (u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        (2*∑ n ∈ S j, c j n*zetaPrimeFilterKernel 1
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (3/2+Complex.I*y j) n) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [ZetaRieszJointAllocation.filter_one_eq]
      dsimp [c]
      ring
    _ = _ := by ring

/-- This is only a comparison ERROR, not a replacement endgame carrier.
The outer Möbius sign and both hinges multiply the whole signed row. -/
def ownedShellDiscrepancy (N : ℕ) (L y : ℝ) (p b M X : ℕ) : ℝ :=
  let w := ZetaRieszCofactorDiscrepancy.shellWeight M X
    (ownedAmplitude N (log p) (log (p*b : ℕ))) y (log (p*b : ℕ))
  ((μ b : ℝ)*pairHinge L p b/(L*(p*b : ℕ)))*
    ((∑ d ∈ Finset.Icc 1 X, w d*sieve (p*b).primeFactors d)-
      density (p*b).primeFactors*(∑ d ∈ Finset.Icc 1 X, w d))

/-- The comparison is exactly the literal owner-divisor incidence minus
ONE signed density row. The finite geometry premise checks ownership;
no arithmetic cancellation or phase estimate is assumed. Core/physical
support conditions can select the two interval endpoints and the outer
pair set before this identity is applied. -/
theorem ownedShellDiscrepancy_eq_literal (A : Finset ℕ) (N : ℕ) (L y : ℝ)
    {p b M X : ℕ} (hp : p.Prime) (hb : 0 < b) (hM : 0 < M) (hpA : p ∈ A)
    (hg : ∀ d ∈ Finset.Ioc M X, sieve (p*b).primeFactors d ≠ 0 →
      Squarefree (b*d) ∧ 2 ≤ (b*d).primeFactors.card ∧
        ∀ q ∈ (b*d).primeFactors, q < p) :
    ownedShellDiscrepancy N L y p b M X =
      (∑ d ∈ Finset.Ioc M X,
        (phaseWeight (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*(b*d))})
          L N y (b*d) p).re*(μ b : ℝ)*pairHinge L p b*sieve (p*b).primeFactors d)-
      ((μ b : ℝ)*pairHinge L p b/(L*(p*b : ℕ)))*density (p*b).primeFactors*
        (∑ d ∈ Finset.Icc 1 X, ZetaRieszCofactorDiscrepancy.shellWeight M X
          (ownedAmplitude N (log p) (log (p*b : ℕ))) y (log (p*b : ℕ)) d) := by
  let w := ZetaRieszCofactorDiscrepancy.shellWeight M X
    (ownedAmplitude N (log p) (log (p*b : ℕ))) y (log (p*b : ℕ))
  have hsub : Finset.Ioc M X ⊆ Finset.Icc 1 X := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨by have := Finset.mem_Ioc.mp hd; omega,
      (Finset.mem_Ioc.mp hd).2⟩
  have hsum : (∑ d ∈ Finset.Icc 1 X, w d*sieve (p*b).primeFactors d) =
      ∑ d ∈ Finset.Ioc M X, w d*sieve (p*b).primeFactors d := by
    symm
    apply Finset.sum_subset hsub
    intro d hd hnot
    have hh : ¬M<d := by
      intro hMd
      exact hnot (Finset.mem_Ioc.mpr ⟨hMd,(Finset.mem_Icc.mp hd).2⟩)
    simp [w,ZetaRieszCofactorDiscrepancy.shellWeight,hh]
  rw [ownedShellDiscrepancy,mul_sub,hsum,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro d hd
    by_cases hz : sieve (p*b).primeFactors d=0
    · simp [hz]
    have hh := hg d hd hz
    have hd0 : 0 < d := by have := Finset.mem_Ioc.mp hd; omega
    rw [owner_phase_eq_amplitude A N L y hp hb hd0 hh.1 hh.2.1 hh.2.2 hpA]
    have hw : w d=ownedAmplitude N (log p) (log (p*b : ℕ)) d*
        cos (y*(log (p*b : ℕ)+log d))/d := by
      simp only [w,ZetaRieszCofactorDiscrepancy.shellWeight,
        if_pos (Finset.mem_Ioc.mp hd)]
    rw [hw]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · ring

/-- The literal two-hinge, phase-retaining unsigned-leg discrepancy.
All actual outer prime intersections and the full owner allocation are
included. Only this discrepancy is norm-paid. -/
theorem ownedShellDiscrepancy_bound {N M X p b : ℕ} (hN : 32 ≤ N)
    (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    (hlarge : exp ((N : ℝ)/10) ≤ M) {L : ℝ} (hL : 0 < L)
    (hp : 0 < p) (hb : 0 < b) (hPL : log p ≤ L)
    (hT : ∀ d ∈ Finset.Icc (M+1) X, 1 ≤ log (p*b : ℕ)+log d)
    (y : ℝ) :
    |ownedShellDiscrepancy N L y p b M X| ≤
      (countingCost*exp (-(N : ℝ)/40)*
        (((N : ℝ)+7+|y|)*radialEnvelope N))*
          (3^(p*b).primeFactors.card/(p*b : ℕ)) := by
  have hpb : (0 : ℝ)<(p*b : ℕ) := by exact_mod_cast Nat.mul_pos hp hb
  have hlog : log (p*b : ℕ) = log p+log b := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne') (by exact_mod_cast hb.ne')]
  have hPT d (_ : d ∈ Finset.Icc (M+1) X) : log p ≤ log (p*b : ℕ)+log d := by
    rw [hlog]
    linarith [log_natCast_nonneg b,log_natCast_nonneg d]
  have he := owned_shell_error (p*b).primeFactors
    (fun _ h => Nat.prime_of_mem_primeFactors h) hN hM hMX hXM hlarge
    (log_natCast_nonneg p) hT hPT y
  have hh := pairHinge_bounds L p b
  have hm : |(μ b : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := b)
  have hc : |(μ b : ℝ)*pairHinge L p b/(L*(p*b : ℕ))| ≤ 1/(p*b : ℕ) := by
    rw [abs_div,abs_mul,abs_of_nonneg hh.1,abs_of_pos (mul_pos hL hpb)]
    apply (div_le_iff₀ (mul_pos hL hpb)).mpr
    have hx := mul_le_mul_of_nonneg_right hm hh.1
    have heq : 1/(p*b : ℕ)*(L*(p*b : ℕ))=L := by field_simp
    rw [heq]
    exact hx.trans (by simpa using hh.2.trans hPL)
  rw [ownedShellDiscrepancy,abs_mul]
  exact (mul_le_mul hc he (abs_nonneg _) (by positivity)).trans_eq (by ring)

/-- The outer intersection costs are jointly summable over every
count and every literal finite outer-pair selection. No separate allowance
is attached to a prime-count class. -/
theorem outer_cost_bound (B : Finset (ℕ×ℕ)) (N : ℕ)
    (hB : ∀ pb ∈ B, pb.1.Prime ∧ Squarefree pb.2 ∧ ¬pb.1 ∣ pb.2)
    (hlog : ∀ pb ∈ B, log (pb.1*pb.2 : ℕ) ≤ (203/100 : ℝ)*N) :
    (∑ pb ∈ B, (3 : ℝ)^(pb.1*pb.2).primeFactors.card/(pb.1*pb.2 : ℕ)) ≤
      3*exp ((203/102400 : ℝ)*N)*
        ZetaRieszPrimeCountMass.countMass (1025/1024)*
          exp (3*ZetaRieszPrimeCountMass.countMass (1025/1024)) := by
  let σ : ℝ := 1025/1024
  let P := B.image Prod.fst
  let Q := B.image Prod.snd
  have hs : 1 < σ := by norm_num [σ]
  have hQ : ∀ b ∈ Q, Squarefree b := by
    intro b hb
    obtain ⟨pb,hpb,rfl⟩ := Finset.mem_image.mp hb
    exact (hB pb hpb).2.1
  have hBP : B ⊆ P.product Q := by
    intro pb hpb
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨pb,hpb,rfl⟩,
      Finset.mem_image.mpr ⟨pb,hpb,rfl⟩⟩
  have hterm pb (hpb : pb ∈ B) :
      (3 : ℝ)^(pb.1*pb.2).primeFactors.card/(pb.1*pb.2 : ℕ) ≤
        3*exp ((203/102400 : ℝ)*N)*
          (exp (-σ*log pb.1)*((3 : ℝ)^pb.2.primeFactors.card*exp (-σ*log pb.2))) := by
    obtain ⟨hp,hb,hpd⟩ := hB pb hpb
    have hpn : pb.1 ∉ pb.2.primeFactors := fun h => hpd (Nat.dvd_of_mem_primeFactors h)
    have hc : (pb.1*pb.2).primeFactors.card = pb.2.primeFactors.card+1 := by
      rw [Nat.primeFactors_mul hp.ne_zero hb.ne_zero,hp.primeFactors,
        Finset.singleton_union,Finset.card_insert_of_notMem hpn]
    have hpn0 : (0 : ℝ)<(pb.1*pb.2 : ℕ) := by
      exact_mod_cast Nat.mul_pos hp.pos (Nat.pos_of_ne_zero hb.ne_zero)
    have hl : log (pb.1*pb.2 : ℕ) = log pb.1+log pb.2 := by
      rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hb.ne_zero)]
    have he : exp ((1/1024 : ℝ)*log (pb.1*pb.2 : ℕ))*
        (exp (-σ*log pb.1)*exp (-σ*log pb.2))=((pb.1*pb.2 : ℕ) : ℝ)⁻¹ := by
      rw [← exp_add,← exp_add,hl]
      have hx : (1/1024 : ℝ)*(log pb.1+log pb.2)+(-σ*log pb.1+-σ*log pb.2) =
          -(log pb.1+log pb.2) := by dsimp [σ]; ring
      rw [hx,← hl,exp_neg,exp_log hpn0]
    have hle : exp ((1/1024 : ℝ)*log (pb.1*pb.2 : ℕ)) ≤
        exp ((203/102400 : ℝ)*N) := by
      apply exp_le_exp.mpr
      linarith [hlog pb hpb]
    rw [hc,pow_succ,div_eq_mul_inv,← he]
    nlinarith [mul_le_mul_of_nonneg_left hle
      (by positivity : 0 ≤ (3 : ℝ)^pb.2.primeFactors.card*
        (exp (-σ*log pb.1)*exp (-σ*log pb.2)))]
  calc
    _ ≤ ∑ pb ∈ B, 3*exp ((203/102400 : ℝ)*N)*
        (exp (-σ*log pb.1)*((3 : ℝ)^pb.2.primeFactors.card*exp (-σ*log pb.2))) :=
      Finset.sum_le_sum hterm
    _ ≤ ∑ pb ∈ P.product Q, 3*exp ((203/102400 : ℝ)*N)*
        (exp (-σ*log pb.1)*((3 : ℝ)^pb.2.primeFactors.card*exp (-σ*log pb.2))) :=
      Finset.sum_le_sum_of_subset_of_nonneg hBP (by intros; positivity)
    _ = 3*exp ((203/102400 : ℝ)*N)*
        ((∑ p ∈ P, exp (-σ*log p))*(∑ b ∈ Q, (3 : ℝ)^b.primeFactors.card*exp (-σ*log b))) := by
      rw [Finset.product_eq_sprod,Finset.sum_product P Q (fun pb => 3*exp ((203/102400 : ℝ)*N)*
        (exp (-σ*log pb.1)*((3 : ℝ)^pb.2.primeFactors.card*exp (-σ*log pb.2))))]
      simp only [Finset.mul_sum,Finset.sum_mul]
      exact Finset.sum_comm
    _ ≤ _ := by
      have hp := (summable_zetaPrimeExpWeight hs).sum_le_tsum P
        (fun _ _ => (exp_pos _).le)
      have hq := ZetaRieszPrimeCountMass.squarefree_count_mass_le_exp Q hQ hs
        (by norm_num : (0 : ℝ)≤3)
      calc
        _ ≤ 3*exp ((203/102400 : ℝ)*N)*
            (ZetaRieszPrimeCountMass.countMass σ*exp (3*ZetaRieszPrimeCountMass.countMass σ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hp hq (Finset.sum_nonneg (by intros; positivity))
              (ZetaRieszPrimeCountMass.countMass_nonneg σ))
            (by positivity : 0 ≤ 3*exp ((203/102400 : ℝ)*N))
        _ = _ := by ring

/-- The genuinely geometric rate AFTER both the full source growth and
the joint outer-pair intersection cost have been included. -/
def errorRate (u : ℝ) : ℝ := 2*u*exp (-(2357/102400 : ℝ))

theorem errorRate_bounds {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    0 ≤ errorRate u ∧ errorRate u ≤ 49/50 := by
  constructor
  · unfold errorRate; positivity
  · rw [errorRate,exp_neg,mul_inv_le_iff₀ (exp_pos _)]
    have he := add_one_le_exp (2357/102400 : ℝ)
    have huU : u ≤ (10001/20000 : ℝ) := hU
    nlinarith

/-- A fixed height-dependent prefactor; every prime-count cost has
already been summed into a convergent Euler mass. -/
def errorConstant : ℝ :=
  6*ZetaRieszWideOwnerAudit.radiusCeiling*countingCost*
    ZetaRieszPrimeCountMass.countMass (1025/1024)*
      exp (3*ZetaRieszPrimeCountMass.countMass (1025/1024))

theorem errorConstant_nonneg : 0 ≤ errorConstant := by
  have hc := countingCost_pos.le
  have hm := ZetaRieszPrimeCountMass.countMass_nonneg (1025/1024)
  unfold errorConstant ZetaRieszWideOwnerAudit.radiusCeiling
  positivity

/-- One global geometric bound for the joint SIGNED comparison error,
over arbitrary outer-prime counts and radial positions. Every cofactor
sign, both hinges, the physical phase and the exact owner allocation remain
in each row. This theorem pays the counting ERROR, not its signed main. -/
theorem source_scaled_shell_error (B : Finset (ℕ×ℕ)) {N : ℕ} (hN : 32 ≤ N)
    (M X : ℕ×ℕ → ℕ) {L u : ℝ} (hL : 0 < L)
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    (hB : ∀ pb ∈ B, pb.1.Prime ∧ Squarefree pb.2 ∧ ¬pb.1 ∣ pb.2)
    (hlog : ∀ pb ∈ B, log (pb.1*pb.2 : ℕ) ≤ (203/100 : ℝ)*N)
    (hM : ∀ pb ∈ B, 0 < M pb)
    (hMX : ∀ pb ∈ B, M pb < X pb)
    (hXM : ∀ pb ∈ B, X pb ≤ 2*M pb)
    (hlarge : ∀ pb ∈ B, exp ((N : ℝ)/10) ≤ M pb)
    (hPL : ∀ pb ∈ B, log pb.1 ≤ L)
    (hT : ∀ pb ∈ B, ∀ d ∈ Finset.Icc (M pb+1) (X pb),
      1 ≤ log (pb.1*pb.2 : ℕ)+log d) :
    |u^(N+1)*∑ pb ∈ B, ownedShellDiscrepancy N L y pb.1 pb.2 (M pb) (X pb)| ≤
      errorConstant*((N : ℝ)+1)*((N : ℝ)+7+|y|)*(49/50 : ℝ)^N := by
  have hc := countingCost_pos.le
  have hm := ZetaRieszPrimeCountMass.countMass_nonneg (1025/1024)
  let H := countingCost*exp (-(N : ℝ)/40)*(((N : ℝ)+7+|y|)*radialEnvelope N)
  have hH : 0 ≤ H := by dsimp [H]; positivity [radialEnvelope_pos N]
  have he : |∑ pb ∈ B, ownedShellDiscrepancy N L y pb.1 pb.2 (M pb) (X pb)| ≤
      H*(3*exp ((203/102400 : ℝ)*N)*ZetaRieszPrimeCountMass.countMass (1025/1024)*
        exp (3*ZetaRieszPrimeCountMass.countMass (1025/1024))) := by
    calc
      _ ≤ ∑ pb ∈ B, |ownedShellDiscrepancy N L y pb.1 pb.2 (M pb) (X pb)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ pb ∈ B, H*(3^(pb.1*pb.2).primeFactors.card/(pb.1*pb.2 : ℕ)) := by
        apply Finset.sum_le_sum
        intro pb hpb
        exact ownedShellDiscrepancy_bound hN (hM pb hpb) (hMX pb hpb) (hXM pb hpb)
          (hlarge pb hpb) hL (hB pb hpb).1.pos
          (Nat.pos_of_ne_zero (hB pb hpb).2.1.ne_zero) (hPL pb hpb) (hT pb hpb) y
      _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (outer_cost_bound B N hB hlog) hH
  have hex : exp (-(N : ℝ)/40)*exp ((203/102400 : ℝ)*N) =
      exp (-(2357/102400 : ℝ))^N := by
    rw [← exp_add,← exp_nat_mul]
    congr 1
    ring
  have hnorm : |u^(N+1)*∑ pb ∈ B, ownedShellDiscrepancy N L y pb.1 pb.2 (M pb) (X pb)| ≤
      (6*u*countingCost*ZetaRieszPrimeCountMass.countMass (1025/1024)*
        exp (3*ZetaRieszPrimeCountMass.countMass (1025/1024)))*
          ((N : ℝ)+1)*((N : ℝ)+7+|y|)*(errorRate u)^N := by
    rw [abs_mul,abs_of_nonneg (pow_nonneg hu _)]
    apply (mul_le_mul_of_nonneg_left he (pow_nonneg hu _)).trans_eq
    dsimp [H,radialEnvelope,errorRate]
    rw [mul_pow,mul_pow,pow_succ,pow_succ]
    have heq := hex
    calc
      _ = (6*u*countingCost*ZetaRieszPrimeCountMass.countMass (1025/1024)*
          exp (3*ZetaRieszPrimeCountMass.countMass (1025/1024)))*
          ((N : ℝ)+1)*((N : ℝ)+7+|y|)*(2^N*u^N)*
            (exp (-(N : ℝ)/40)*exp ((203/102400 : ℝ)*N)) := by ring
      _ = _ := by rw [heq]; ring
  apply hnorm.trans
  have hr := errorRate_bounds hu hU
  have hconst : 6*u*countingCost*ZetaRieszPrimeCountMass.countMass (1025/1024)*
      exp (3*ZetaRieszPrimeCountMass.countMass (1025/1024)) ≤ errorConstant := by
    unfold errorConstant
    gcongr
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hconst (by positivity)) (by positivity))
    (pow_le_pow_left₀ hr.1 hr.2 N) (pow_nonneg hr.1 N)
    (by positivity [errorConstant_nonneg])

/-- All radial shells may be joined before taking the signed comparison
error. A polynomial number of shells leaves the strict geometric saving.
The masks selecting each outer pair and each shell remain arbitrary. -/
theorem source_scaled_shells_error {ι : Type*} (I : Finset ι)
    (B : ι → Finset (ℕ×ℕ)) {N : ℕ} (hN : 32 ≤ N)
    (M X : ι → ℕ×ℕ → ℕ) {L u : ℝ} (hL : 0 < L)
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    (hI : I.card ≤ N+1)
    (hB : ∀ i ∈ I, ∀ pb ∈ B i, pb.1.Prime ∧ Squarefree pb.2 ∧ ¬pb.1 ∣ pb.2)
    (hlog : ∀ i ∈ I, ∀ pb ∈ B i, log (pb.1*pb.2 : ℕ) ≤ (203/100 : ℝ)*N)
    (hM : ∀ i ∈ I, ∀ pb ∈ B i, 0 < M i pb)
    (hMX : ∀ i ∈ I, ∀ pb ∈ B i, M i pb < X i pb)
    (hXM : ∀ i ∈ I, ∀ pb ∈ B i, X i pb ≤ 2*M i pb)
    (hlarge : ∀ i ∈ I, ∀ pb ∈ B i, exp ((N : ℝ)/10) ≤ M i pb)
    (hPL : ∀ i ∈ I, ∀ pb ∈ B i, log pb.1 ≤ L)
    (hT : ∀ i ∈ I, ∀ pb ∈ B i, ∀ d ∈ Finset.Icc (M i pb+1) (X i pb),
      1 ≤ log (pb.1*pb.2 : ℕ)+log d) :
    |u^(N+1)*∑ i ∈ I, ∑ pb ∈ B i,
      ownedShellDiscrepancy N L y pb.1 pb.2 (M i pb) (X i pb)| ≤
      errorConstant*(8+|y|)*((N : ℝ)+1)^3*(49/50 : ℝ)^N := by
  let C := errorConstant*((N : ℝ)+1)*((N : ℝ)+7+|y|)*(49/50 : ℝ)^N
  have hC : 0 ≤ C := by dsimp [C]; positivity [errorConstant_nonneg]
  calc
    _ ≤ ∑ i ∈ I, |u^(N+1)*∑ pb ∈ B i,
        ownedShellDiscrepancy N L y pb.1 pb.2 (M i pb) (X i pb)| := by
      rw [Finset.mul_sum]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ I, C := Finset.sum_le_sum (fun i hi =>
      source_scaled_shell_error (B i) hN (M i) (X i) hL hu hU y
        (hB i hi) (hlog i hi) (hM i hi) (hMX i hi) (hXM i hi)
        (hlarge i hi) (hPL i hi) (hT i hi))
    _ = (I.card : ℝ)*C := by simp
    _ ≤ ((N : ℝ)+1)*C := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hI) hC
    _ ≤ _ := by
      have hp : (N : ℝ)+7+|y| ≤ (8+|y|)*((N : ℝ)+1) := by
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (abs_nonneg y)]
      have hh := mul_le_mul_of_nonneg_left hp
        (by positivity [errorConstant_nonneg] :
          0 ≤ errorConstant*((N : ℝ)+1)^2*(49/50 : ℝ)^N)
      dsimp [C]
      nlinarith only [hh]

/-- The displayed global shell-error allowance tends to zero at source
scale. Its strict rate has already included every outer count cost. -/
theorem tendsto_shell_error_budget (y : ℝ) :
    Tendsto (fun N : ℕ =>
      errorConstant*(8+|y|)*((N : ℝ)+1)^3*(49/50 : ℝ)^N) atTop (𝓝 0) := by
  have ht := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 3
    (by norm_num : (0 : ℝ)<49/50) (by norm_num : (49/50 : ℝ)<1)).const_mul
      (errorConstant*(8+|y|))
  simpa only [mul_zero,mul_assoc] using ht

end RiemannGaussian.ZetaRieszUnsignedDivisorError
