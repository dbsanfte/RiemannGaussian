/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorPowerCovariance

/-!
# Polynomial binomial valuations add no source above the square-root scale

Keep the exact Kummer digit carries and the full base-prime phase. For a
binomial with a+b<=2^(2J), every prime valuation is at most 2J, and primes
above 2^J have valuation zero or one. Thus every fixed positive polynomial
power differs from its linear valuation by at most a square-root times
polylogarithmic budget, uniformly in arbitrary unit-bounded modular/height
phases. This closes the single-binomial/single-prime polynomial prototype,
not products of different prime columns or multiple binary row features.
The remaining linear twisted Kummer sum is NOT paid by this theorem.
-/

namespace RiemannGaussian.ArithmeticOperatorKummerPolynomialAudit
noncomputable section
open ArithmeticOperatorKummerCutoff Filter
open scoped BigOperators Topology

/-- Literal ordinary-prime valuation of the same integer binomial. -/
def valuation (p a b : ℕ) : ℕ := padicValNat p ((a+b).choose b)

/-- All positive prime-power carry orders through the physical cutoff. -/
def carryOrders (p a b J : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (2*J+1)).filter (fun i => p^i≤b%p^i+a%p^i)

/-- Exact Kummer identity at a uniform INTEGER exponent ceiling. -/
theorem valuation_eq_card {p a b J : ℕ} (hp : p.Prime) (hab : a+b≤2^(2*J)) :
    valuation p a b=(carryOrders p a b J).card := by
  let : Fact p.Prime := ⟨hp⟩
  have hlog : Nat.log p (a+b)<2*J+1 := by
    apply Nat.log_lt_of_lt_pow' (by omega)
    exact (hab.trans (Nat.pow_le_pow_left hp.two_le _)).trans_lt
      (Nat.pow_lt_pow_right hp.one_lt (by omega))
  exact valuation_eq_carry_count hlog

theorem valuation_le_orders {p a b J : ℕ} (hp : p.Prime) (hab : a+b≤2^(2*J)) :
    valuation p a b≤2*J := by
  rw [valuation_eq_card hp hab]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp [Nat.card_Ico])

/-- No higher carry is silently dropped: its literal order would
force p squared to lie below a+b, contradicting the physical cutoff. -/
theorem carryOrders_large_prime {p a b J : ℕ} (hp : p.Prime)
    (hab : a+b≤2^(2*J)) (hlarge : 2^J<p) : carryOrders p a b J ⊆ {1} := by
  intro i hi
  obtain ⟨hi0,hi1⟩ := Finset.mem_filter.mp hi
  have hiOne : 1 ≤ i := (Finset.mem_Ico.mp hi0).1
  have hpow : p^i≤a+b := by
    have ha := Nat.mod_le a (p^i)
    have hb := Nat.mod_le b (p^i)
    omega
  by_contra hh
  have hiNe : i≠1 := by simpa only [Finset.mem_singleton] using hh
  have hi2 : 2 ≤ i := by omega
  have hpp : 2^(2*J)<p^2 := by
    rw [show 2*J=J*2 by omega,pow_mul]
    exact Nat.pow_lt_pow_left hlarge (by omega)
  have hpe : p^2≤p^i := Nat.pow_le_pow_right hp.pos hi2
  exact (not_lt_of_ge (hpow.trans hab)) (hpp.trans_le hpe)

/-- Every polynomial power agrees with its linear part on large primes. -/
theorem valuation_large_prime_le_one {p a b J : ℕ} (hp : p.Prime)
    (hab : a+b≤2^(2*J)) (hlarge : 2^J<p) : valuation p a b≤1 := by
  rw [valuation_eq_card hp hab]
  exact (Finset.card_le_card (carryOrders_large_prime hp hab hlarge)).trans (by simp)

/-- The natural defect is nonnegative and is exactly the missing part
of the polynomial power, including valuation zero. -/
def defect (D p a b : ℕ) : ℕ := (valuation p a b)^D-valuation p a b

theorem valuation_power_eq {D : ℕ} (hD : 0<D) (p a b : ℕ) :
    (valuation p a b)^D=valuation p a b+defect D p a b := by
  have hh := Nat.le_self_pow hD.ne' (valuation p a b)
  unfold defect
  omega

theorem defect_large_prime_zero {D p a b J : ℕ} (hD : 0<D) (hp : p.Prime)
    (hab : a+b≤2^(2*J)) (hlarge : 2^J<p) : defect D p a b=0 := by
  have hh := valuation_large_prime_le_one hp hab hlarge
  have hv : valuation p a b=0 ∨ valuation p a b=1 := by omega
  rcases hv with hv | hv <;> simp [defect,hv,hD.ne']

/-- Bounded code phases can depend on the prime, binomial and scale;
they are not replaced by an untwisted approximation. -/
def polynomialPacket (P : Finset ℕ) (a b D : ℕ) (phase : ℕ → ℂ) : ℂ :=
  ∑ p ∈ P, (Real.log p : ℂ)*phase p*((valuation p a b)^D : ℂ)

/-- Only the nonlinear increment; the entire linear packet stays unpaid. -/
def correction (P : Finset ℕ) (a b D : ℕ) (phase : ℕ → ℂ) : ℂ :=
  ∑ p ∈ P, (Real.log p : ℂ)*phase p*(defect D p a b : ℂ)

/-- Exact finite join with every binomial, prime-power order and phase. -/
theorem polynomialPacket_eq_linear_add_correction {D : ℕ} (hD : 0<D)
    (P : Finset ℕ) (a b : ℕ) (phase : ℕ → ℂ) :
    polynomialPacket P a b D phase=
      polynomialPacket P a b 1 phase+correction P a b D phase := by
  unfold polynomialPacket correction
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  have hv : (valuation p a b : ℂ)^D=
      (valuation p a b : ℂ)+(defect D p a b : ℂ) := by
    exact_mod_cast valuation_power_eq hD p a b
  rw [hv,pow_one]
  ring

/-- The support reduction is arithmetic and uniform in the FULL code. -/
theorem correction_eq_small {D J a b : ℕ} (hD : 0<D)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hab : a+b≤2^(2*J)) (phase : ℕ → ℂ) :
    correction P a b D phase=
      correction (P.filter (fun p => p≤2^J)) a b D phase := by
  unfold correction
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hpnot
  have hlarge : 2^J<p := by
    by_contra hh
    exact hpnot (Finset.mem_filter.mpr ⟨hp,by omega⟩)
  rw [defect_large_prime_zero hD (hP p hp) hab hlarge,Nat.cast_zero,mul_zero]

/-- Quantitative source-gate failure of the genuinely nonlinear part,
without PNT, density approximation, zero hypotheses or discarded powers. -/
theorem norm_correction_le {D J a b : ℕ} (hD : 0<D) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hab : a+b≤2^(2*J)) (phase : ℕ → ℂ)
    (hphase : ∀ p ∈ P, ‖phase p‖≤1) :
    ‖correction P a b D phase‖≤
      (2 : ℝ)^J*((2*J : ℕ) : ℝ)^(D+1)*Real.log 2 := by
  classical
  rw [correction_eq_small hD P hP hab]
  let Q := P.filter (fun p => p≤2^J)
  have hcard : (Q.card : ℝ)≤(2 : ℝ)^J := by
    have hs : Q ⊆ Finset.Icc 1 (2^J) := by
      intro p hp
      obtain ⟨hp,hpb⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨(hP p hp).pos,hpb⟩
    exact_mod_cast (by simpa using Finset.card_le_card hs : Q.card≤2^J)
  have hterm (p : ℕ) (hp : p ∈ Q) :
      ‖(Real.log p : ℂ)*phase p*(defect D p a b : ℂ)‖≤
        ((2*J : ℕ) : ℝ)^(D+1)*Real.log 2 := by
    have hpP := (Finset.mem_filter.mp hp).1
    have hpS := (Finset.mem_filter.mp hp).2
    have hlog : ‖(Real.log p : ℂ)‖≤((2*J : ℕ) : ℝ)*Real.log 2 := by
      rw [Complex.norm_real,Real.norm_of_nonneg (Real.log_natCast_nonneg p)]
      have hpX : p≤2^(2*J) := hpS.trans (by
        apply Nat.pow_le_pow_right (by omega : 0<(2 : ℕ)); omega)
      have hh := Real.log_le_log (by exact_mod_cast (hP p hpP).pos : (0 : ℝ)<p)
        (by exact_mod_cast hpX : (p : ℝ)≤(2 : ℝ)^(2*J))
      simpa only [Real.log_pow] using hh
    have hd : ‖(defect D p a b : ℂ)‖≤((2*J : ℕ) : ℝ)^D := by
      rw [Complex.norm_natCast]
      exact_mod_cast (Nat.sub_le ((valuation p a b)^D) (valuation p a b)).trans
        (Nat.pow_le_pow_left (valuation_le_orders (hP p hpP) hab) D)
    rw [norm_mul,norm_mul]
    calc
      _ ≤ (((2*J : ℕ) : ℝ)*Real.log 2)*1*((2*J : ℕ) : ℝ)^D :=
        mul_le_mul (mul_le_mul hlog (hphase p hpP) (norm_nonneg _) (by positivity))
          hd (norm_nonneg _) (by positivity)
      _ = _ := by rw [pow_succ]; ring
  unfold correction
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _p ∈ Q, ((2*J : ℕ) : ℝ)^(D+1)*Real.log 2 :=
      Finset.sum_le_sum hterm
    _ = (Q.card : ℝ)*(((2*J : ℕ) : ℝ)^(D+1)*Real.log 2) := by simp
    _ ≤ _ := by
      calc
        _ ≤ (2 : ℝ)^J*(((2*J : ℕ) : ℝ)^(D+1)*Real.log 2) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by ring

/-- Even moving binomials, prime subsets and code phases cannot give
the nonlinear increment a nonzero campaign power source. -/
theorem tendsto_scaled_correction {D : ℕ} (hD : 0<D)
    (P : ℕ → Finset ℕ) (a b : ℕ → ℕ) (phase : ℕ → ℕ → ℂ)
    (hP : ∀ J p, p ∈ P J → p.Prime) (hab : ∀ J, a J+b J≤2^(2*J))
    (hphase : ∀ J p, p ∈ P J → ‖phase J p‖≤1)
    {beta : ℝ} (hbeta : 1/2<beta) :
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      correction (P J) (a J) (b J) D (phase J)) atTop (𝓝 0) := by
  let r := Real.exp ((1-2*beta)*Real.log 2)
  have hr0 : 0≤r := (Real.exp_pos _).le
  have hr1 : r<1 := Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (by linarith) (Real.log_pos (by norm_num)))
  have he : Real.exp (-2*beta*Real.log 2)*2=r := by
    calc
      _ = Real.exp (-2*beta*Real.log 2)*Real.exp (Real.log 2) := by
        rw [Real.exp_log (by norm_num : (0 : ℝ)<2)]
      _ = _ := by dsimp [r]; rw [←Real.exp_add]; congr 1; ring
  have ht := (tendsto_pow_const_mul_const_pow_of_lt_one (D+1) hr0 hr1).const_mul
    ((2 : ℝ)^(D+1)*Real.log 2)
  simp only [mul_zero] at ht
  apply squeeze_zero_norm (a := fun J : ℕ =>
    ((2 : ℝ)^(D+1)*Real.log 2)*((J : ℝ)^(D+1)*r^J)) _ ht
  intro J
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  apply (mul_le_mul_of_nonneg_left
    (norm_correction_le hD (P J) (hP J) (hab J) (phase J) (hphase J)) (by positivity)).trans_eq
  rw [←he,mul_pow]
  push_cast
  rw [mul_pow]
  ring

/-- Stop at the source gate: the additional polynomial degree cannot
have ANY nonzero matched limit under these literal bounded-code hypotheses. -/
theorem no_nonzero_correction_source {D : ℕ} (hD : 0<D)
    (P : ℕ → Finset ℕ) (a b : ℕ → ℕ) (phase : ℕ → ℕ → ℂ)
    (hP : ∀ J p, p ∈ P J → p.Prime) (hab : ∀ J, a J+b J≤2^(2*J))
    (hphase : ∀ J p, p ∈ P J → ‖phase J p‖≤1)
    {beta : ℝ} (hbeta : 1/2<beta) {v : ℂ} (hv : v≠0) :
    ¬Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      correction (P J) (a J) (b J) D (phase J)) atTop (𝓝 v) := by
  intro hh
  exact hv (tendsto_nhds_unique hh (tendsto_scaled_correction hD P a b phase hP hab hphase hbeta))

/-- Every fixed polynomial with zero constant term has the same exact
linear large-prime channel. The finite coefficients may have any sign
or complex phase; none of the monomial pieces is thrown away. -/
theorem finite_polynomial_eq_linear_add (S : Finset ℕ) (coeff : ℕ → ℂ)
    (hS : ∀ D ∈ S, 0<D) (P : Finset ℕ) (a b : ℕ) (phase : ℕ → ℂ) :
    (∑ D ∈ S, coeff D*polynomialPacket P a b D phase)=
      (∑ D ∈ S, coeff D)*polynomialPacket P a b 1 phase+
        ∑ D ∈ S, coeff D*correction P a b D phase := by
  rw [Finset.sum_mul,←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun D hD => by
    rw [polynomialPacket_eq_linear_add_correction (hS D hD)]
    ring)

/-- Entire fixed-degree/complex-coefficient polynomial class, not just
one positive monomial. Its extra channel vanishes at every source
exponent above one half; the exact signed linear packet is still unpaid. -/
theorem tendsto_scaled_finite_polynomial_sub_linear (S : Finset ℕ) (coeff : ℕ → ℂ)
    (hS : ∀ D ∈ S, 0<D) (P : ℕ → Finset ℕ) (a b : ℕ → ℕ)
    (phase : ℕ → ℕ → ℂ) (hP : ∀ J p, p ∈ P J → p.Prime)
    (hab : ∀ J, a J+b J≤2^(2*J)) (hphase : ∀ J p, p ∈ P J → ‖phase J p‖≤1)
    {beta : ℝ} (hbeta : 1/2<beta) :
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      ((∑ D ∈ S, coeff D*polynomialPacket (P J) (a J) (b J) D (phase J))-
        (∑ D ∈ S, coeff D)*polynomialPacket (P J) (a J) (b J) 1 (phase J)))
      atTop (𝓝 0) := by
  have hh := tendsto_finsetSum S (fun D hD =>
    (tendsto_scaled_correction (hS D hD) P a b phase hP hab hphase hbeta).const_mul (coeff D))
  simp only [mul_zero,Finset.sum_const_zero] at hh
  convert hh using 1
  funext J
  rw [finite_polynomial_eq_linear_add S coeff hS,add_sub_cancel_left,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

end
end RiemannGaussian.ArithmeticOperatorKummerPolynomialAudit
