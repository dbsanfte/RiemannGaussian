/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOwnerDensity
import RiemannGaussian.NatDivisorSquareMean
import RiemannGaussian.ZetaRieszSixPrimeHead

/-!
# The cofactor energy of every prime count together

Ordered prime incidences pay the count square through literal common-multiple
counts. On a cofactor shell this controls the reciprocal owner-log energy,
without a maximum prime count or a replacement of prime sums by a density.
-/

noncomputable section
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszOwnerCountEnergy

/-- Counting ordered pairs of actual prime divisors controls all counts
together, with a diagonal cost and no fixed-count exponential constant. -/
theorem prime_incidence_second_moment (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (((P.filter (fun p => p ∣ n)).card : ℝ)^2)) ≤
      (X : ℝ)*((∑ p ∈ P, 1/(p : ℝ))^2+(∑ p ∈ P, 1/(p : ℝ))) := by
  have he n : (((P.filter (fun p => p ∣ n)).card : ℝ)^2) =
      ∑ p ∈ P, ∑ q ∈ P, if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0 := by
    rw [sq]
    simp only [Finset.card_eq_sum_ones,Nat.cast_sum,Finset.sum_filter,
      Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    split_ifs <;> simp_all
  have hpair p (hp : p ∈ P) q (hq : q ∈ P) :
      (Nat.gcd p q : ℝ)/((p : ℝ)*q) ≤
        (1/(p : ℝ))*(1/(q : ℝ))+(if p=q then 1/(p : ℝ) else 0) := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (hP q hq).pos
    by_cases hpq : p=q
    · subst q
      rw [Nat.gcd_self,if_pos rfl]
      have hid : (p : ℝ)/((p : ℝ)*p) = 1/(p : ℝ) := by field_simp
      rw [hid]
      nlinarith [sq_nonneg (1/(p : ℝ))]
    · have hg : Nat.gcd p q = 1 :=
        ((hP p hp).coprime_iff_not_dvd.mpr
          (fun h => hpq ((Nat.prime_dvd_prime_iff_eq (hP p hp) (hP q hq)).mp h))).gcd_eq_one
      rw [hg,if_neg hpq]
      simp only [Nat.cast_one,add_zero]
      field_simp
      norm_num
  calc
    _ = ∑ p ∈ P, ∑ q ∈ P,
        (((Finset.Icc 1 X).filter (fun n => p ∣ n ∧ q ∣ n)).card : ℝ) := by
      simp_rw [he]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [Finset.card_eq_sum_ones,Nat.cast_sum,Finset.sum_filter,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, (X : ℝ)*
        ((1/(p : ℝ))*(1/(q : ℝ))+(if p=q then 1/(p : ℝ) else 0)) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      exact (card_Icc_common_dvd_le_gcd (hP p hp).pos (hP q hq).pos X).trans
        (by simpa only [mul_div_assoc] using
          mul_le_mul_of_nonneg_left (hpair p hp q hq) (Nat.cast_nonneg (α := ℝ) X))
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      congr 1
      simp_rw [Finset.sum_add_distrib]
      congr 1
      · simp only [sq,Finset.mul_sum,mul_comm]
      · apply Finset.sum_congr rfl
        intro p hp
        simp only [Finset.sum_ite_eq,if_pos hp]

/-- The all-integer count budget follows with the literal prime set. -/
theorem prime_count_second_moment (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (n.primeFactors.card : ℝ)^2) ≤
      (X : ℝ)*((∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, 1/(p : ℝ))^2+
        (∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, 1/(p : ℝ))) := by
  have he n (hn : n ∈ Finset.Icc 1 X) :
      ((Finset.Icc 1 X).filter Nat.Prime).filter (fun p => p ∣ n) = n.primeFactors := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨_,hp⟩,hd⟩
      exact ⟨hp,hd,by have := (Finset.mem_Icc.mp hn).1; omega⟩
    · rintro ⟨hp,hd,_⟩
      exact ⟨⟨⟨hp.pos,(Nat.le_of_dvd (Finset.mem_Icc.mp hn).1 hd).trans
        (Finset.mem_Icc.mp hn).2⟩,hp⟩,hd⟩
  have ht := prime_incidence_second_moment ((Finset.Icc 1 X).filter Nat.Prime)
    (fun p hp => (Finset.mem_filter.mp hp).2) X
  convert ht using 1
  exact Finset.sum_congr rfl (fun n hn => by rw [he n hn])

/-- The literal reciprocal mass of primes through the integer endpoint. -/
def primeHarmonic (X : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, 1/(p : ℝ)

/-- Every term in the finite prime mass is nonnegative. -/
theorem primeHarmonic_nonneg (X : ℕ) : 0 ≤ primeHarmonic X :=
  Finset.sum_nonneg (fun _ _ => by positivity)

/-- Ownership bounds the mean logarithm of every squarefree cofactor
without any restriction on the number of its prime factors. -/
theorem owner_mean_log_le {n : ℕ} (hn : 1 < n) (hs : Squarefree n) {D : ℝ}
    (howner : ∀ p ∈ n.primeFactors, Real.log p ≤ D) :
    0 < Real.log n/(n.primeFactors.card : ℝ) ∧
      Real.log n/(n.primeFactors.card : ℝ) ≤ D := by
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hsum := Finset.sum_le_sum howner
  rw [← CoprimeEulerPhase.squarefree_log_eq_prime_sum hs,Finset.sum_const,nsmul_eq_mul] at hsum
  have hcard : 0 < n.primeFactors.card := by
    by_contra hc
    have he : n.primeFactors.card = 0 := by omega
    rw [he,Nat.cast_zero,zero_mul] at hsum
    linarith
  have hc : (0 : ℝ) < n.primeFactors.card := by exact_mod_cast hcard
  exact ⟨div_pos hlog hc,(div_le_iff₀ hc).mpr (by simpa only [mul_comm] using hsum)⟩

/-- The full reciprocal-log energy on a dyadic cofactor shell has a
literal prime-count budget. The phase may remain in any real weight
bounded by W/n; every prime count is included. -/
theorem shell_energy_le {M : ℕ} (hM : 2 ≤ M) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioc M (2*M)) (w : ℕ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hw : ∀ n ∈ S, |w n| ≤ W/n) :
    (∑ n ∈ S, (w n/(Real.log n/(n.primeFactors.card : ℝ)))^2) ≤
      2*W^2*(primeHarmonic (2*M)^2+primeHarmonic (2*M))/
        ((M : ℝ)*(Real.log M)^2) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hlM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hlocal n (hn : n ∈ S) :
      (w n/(Real.log n/(n.primeFactors.card : ℝ)))^2 ≤
        (W/((M : ℝ)*Real.log M))^2*(n.primeFactors.card : ℝ)^2 := by
    have hnM : M ≤ n := (Finset.mem_Ioc.mp (hS hn)).1.le
    have hn0 : (0 : ℝ) < n := hM0.trans_le (by exact_mod_cast hnM)
    have hln : Real.log M ≤ Real.log n := Real.log_le_log hM0 (by exact_mod_cast hnM)
    have hln0 : 0 < Real.log n := hlM.trans_le hln
    have hden : (M : ℝ)*Real.log M ≤ (n : ℝ)*Real.log n :=
      mul_le_mul (by exact_mod_cast hnM) hln hlM.le hn0.le
    have hsmall : |w n|/Real.log n ≤ W/((M : ℝ)*Real.log M) := calc
      _ ≤ (W/n)/Real.log n := div_le_div_of_nonneg_right (hw n hn) hln0.le
      _ = W/((n : ℝ)*Real.log n) := by ring
      _ ≤ _ := div_le_div_of_nonneg_left hW (mul_pos hM0 hlM) hden
    have he : w n/(Real.log n/(n.primeFactors.card : ℝ)) =
        (w n/Real.log n)*(n.primeFactors.card : ℝ) := by
      rw [div_div_eq_mul_div]
      ring
    rw [he,mul_pow]
    apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have ht := pow_le_pow_left₀ (div_nonneg (abs_nonneg _) hln0.le) hsmall 2
    simpa only [div_pow,sq_abs] using ht
  have hsub : S ⊆ Finset.Icc 1 (2*M) := by
    intro n hn
    have := Finset.mem_Ioc.mp (hS hn)
    exact Finset.mem_Icc.mpr ⟨by omega,this.2⟩
  have hcounts : (∑ n ∈ S, (n.primeFactors.card : ℝ)^2) ≤
      (2*M : ℕ)*(primeHarmonic (2*M)^2+primeHarmonic (2*M)) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)).trans
      (prime_count_second_moment (2*M))
  calc
    _ ≤ ∑ n ∈ S, (W/((M : ℝ)*Real.log M))^2*(n.primeFactors.card : ℝ)^2 :=
      Finset.sum_le_sum hlocal
    _ = (W/((M : ℝ)*Real.log M))^2*(∑ n ∈ S, (n.primeFactors.card : ℝ)^2) := by
      rw [Finset.mul_sum]
    _ ≤ (W/((M : ℝ)*Real.log M))^2*((2*M : ℕ)*
        (primeHarmonic (2*M)^2+primeHarmonic (2*M))) :=
      mul_le_mul_of_nonneg_left hcounts (sq_nonneg _)
    _ = _ := by push_cast; field_simp

/-- Existing literal Chebyshev counts make the finite prime mass
logarithmic in log X. No asymptotic prime-density substitution is used. -/
theorem primeHarmonic_le_loglog (X : ℕ) :
    primeHarmonic X ≤ (2*Real.exp (1/2)*Real.log 4)*
      (1+Real.log (4*Real.log X+8)) := by
  let M := ⌈Real.log X⌉₊
  have hlog : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  have hMl : Real.log X ≤ (M : ℝ) := Nat.le_ceil _
  have hMu : (M : ℝ) < Real.log X+1 := Nat.ceil_lt_add_one hlog
  have hsub : (Finset.Icc 1 X).filter Nat.Prime ⊆
      ZetaRieszAllowancePrimeBoxes.logPrimes 0 (2*(M : ℝ)+2) := by
    intro p hp
    obtain ⟨hpI,hp⟩ := Finset.mem_filter.mp hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hpl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hpu : Real.log p ≤ 2*(M : ℝ)+2 := by
      have hl : Real.log p ≤ Real.log X :=
        Real.log_le_log hp0 (by exact_mod_cast (Finset.mem_Icc.mp hpI).2)
      linarith [Nat.cast_nonneg (α := ℝ) M]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨?_,?_⟩,hp⟩
    · apply (Nat.floor_lt (Real.exp_nonneg _)).mpr
      simpa only [Real.exp_log hp0] using Real.exp_lt_exp.mpr hpl
    · apply Nat.le_floor
      simpa only [Real.exp_zero,mul_one,Real.exp_log hp0] using Real.exp_le_exp.mpr hpu
  have he : primeHarmonic X = ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
      Real.exp (-Real.log p) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [Real.exp_neg,Real.exp_log (by exact_mod_cast (Finset.mem_filter.mp hp).2.pos),one_div]
  have hL : Real.log (4*M+4 : ℕ) ≤ Real.log (4*Real.log X+8) := by
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  calc
    _ ≤ ∑ p ∈ ZetaRieszAllowancePrimeBoxes.logPrimes 0 (2*(M : ℝ)+2),
        Real.exp (-Real.log p) := by
      rw [he]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Real.exp_nonneg _)
    _ ≤ (2*Real.exp (1/2)*Real.log 4)*(1+Real.log (4*M+4 : ℕ)) :=
      ZetaRieszSixPrimeHead.prime_reciprocal_le M
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hL]) (by positivity)

/-- The cofactor energy is now paid in both signed owner-slope bounds.
The base period coefficients remain fixed across the population, and
the literal signed cutoff correction is not removed by this theorem. -/
theorem exists_owner_shell_bounds {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (b N M : ℕ) (S : Finset ℕ) (R : ℕ → ℕ)
      (D a w : ℕ → ℝ) (T : ℕ → ℕ → ℝ) (lo hi : ℕ → ℕ) (W : ℝ),
      32 ≤ N → 2 ≤ M → 0 ≤ W → S ⊆ Finset.Ioc M (2*M) →
      (∀ n ∈ S, Squarefree n) → (∀ n ∈ S, |w n| ≤ W/n) →
      (∀ i < 2^b, 0 < R i) →
      (∀ i < 2^b, (R i : ℝ) < Real.exp (D i) ∧ Real.exp (D i) ≤ R i+1) →
      (∀ (i : ℕ), i < 2^b → ∀ (j : ℕ), j < 2^b →
        h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      (∀ n ∈ S, lo n ≤ hi n ∧ hi n ≤ 2^b) →
      (∀ n ∈ S, ∀ i ∈ Finset.Ico (lo n) (hi n),
        ∀ p ∈ n.primeFactors, Real.log p ≤ T n i-Real.log n) →
      (∀ n ∈ S, ∀ i ∈ Finset.Ico (lo n) (hi n),
        ∀ j ∈ Finset.Ico (lo n) (hi n), i ≤ j → T n i ≤ T n j) →
      let J := ∑ n ∈ S, w n*(∑ i ∈ Finset.Ico (lo n) (hi n),
        (ZetaRieszOwnerMaximal.ownerWeight N (Real.log n/T n i)*a i*
          ZetaRieszGlobalCurvature.cutoffSlope (D i) n)/(T n i-Real.log n));
      let K := Real.sqrt (144*(((b+1 : ℕ) : ℝ)^2)*E*W^2/
        (Real.log M)^2*(primeHarmonic (2*M)^2+primeHarmonic (2*M))*
        (∑ i ∈ Finset.range (2^b), (a i)^2));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := ZetaRieszOwnerDensity.exists_reciprocal_slope_bounds hh
  refine ⟨E,hE,fun b N M S R D a w T lo hi W hN hM hW hS hSF hw hR hD hsep hr howner hmono => ?_⟩
  let δ : ℕ → ℝ := fun n => Real.log n/(n.primeFactors.card : ℝ)
  have hn1 n (hn : n ∈ S) : 1 < n := by
    have := (Finset.mem_Ioc.mp (hS hn)).1
    omega
  have hδ n (hn : n ∈ S) : 0 < δ n := by
    have hpr : ∀ p ∈ n.primeFactors, Real.log p ≤ Real.log n := by
      intro p hp
      apply Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
      have hle : p ≤ n := Nat.le_of_dvd (Nat.zero_lt_of_lt (hn1 n hn))
        (Nat.dvd_of_mem_primeFactors hp)
      exact_mod_cast hle
    exact (owner_mean_log_le (hn1 n hn) (hSF n hn) hpr).1
  have hs : S ⊆ Finset.Ioc 1 (2*M) := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨hn1 n hn,(Finset.mem_Ioc.mp (hS hn)).2⟩
  have hg n (hn : n ∈ S) i (hi' : i ∈ Finset.Ico (lo n) (hi n)) :
      δ n ≤ T n i-Real.log n :=
    (owner_mean_log_le (hn1 n hn) (hSF n hn) (howner n hn i hi')).2
  have hb := hbound b N (2*M) S R D a w T lo hi δ hN hδ hs hSF hR hD hsep hr hg hmono
  have he := shell_energy_le hM S hS w hW hw
  have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hlog : 0 < Real.log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have henergy : (∑ n ∈ S, (w n/δ n)^2)*36*(((b+1 : ℕ) : ℝ)^2)*
      (E*(2*M : ℕ))*(∑ i ∈ Finset.range (2^b), (a i)^2) ≤
      144*(((b+1 : ℕ) : ℝ)^2)*E*W^2/(Real.log M)^2*
        (primeHarmonic (2*M)^2+primeHarmonic (2*M))*
        (∑ i ∈ Finset.range (2^b), (a i)^2) := by
    calc
      _ ≤ (2*W^2*(primeHarmonic (2*M)^2+primeHarmonic (2*M))/
          ((M : ℝ)*(Real.log M)^2))*36*(((b+1 : ℕ) : ℝ)^2)*
          (E*(2*M : ℕ))*(∑ i ∈ Finset.range (2^b), (a i)^2) := by
        gcongr
      _ = _ := by push_cast; field_simp; ring
  have hroot := Real.sqrt_le_sqrt henergy
  dsimp only at hb ⊢
  constructor <;> linarith only [hb.1,hb.2,hroot]

/-- An explicit logarithmic cofactor budget for both signed bounds.
The exponential size of the cofactor population and all prime-count
classes are paid; E_h and the fixed period coefficient energy remain. -/
theorem exists_owner_shell_loglog_bounds {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (b N M : ℕ) (S : Finset ℕ) (R : ℕ → ℕ)
      (D a w : ℕ → ℝ) (T : ℕ → ℕ → ℝ) (lo hi : ℕ → ℕ) (W : ℝ),
      32 ≤ N → 2 ≤ M → 0 ≤ W → S ⊆ Finset.Ioc M (2*M) →
      (∀ n ∈ S, Squarefree n) → (∀ n ∈ S, |w n| ≤ W/n) →
      (∀ i < 2^b, 0 < R i) →
      (∀ i < 2^b, (R i : ℝ) < Real.exp (D i) ∧ Real.exp (D i) ≤ R i+1) →
      (∀ (i : ℕ), i < 2^b → ∀ (j : ℕ), j < 2^b →
        h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      (∀ n ∈ S, lo n ≤ hi n ∧ hi n ≤ 2^b) →
      (∀ n ∈ S, ∀ i ∈ Finset.Ico (lo n) (hi n),
        ∀ p ∈ n.primeFactors, Real.log p ≤ T n i-Real.log n) →
      (∀ n ∈ S, ∀ i ∈ Finset.Ico (lo n) (hi n),
        ∀ j ∈ Finset.Ico (lo n) (hi n), i ≤ j → T n i ≤ T n j) →
      let B := (2*Real.exp (1/2)*Real.log 4)*(1+Real.log (4*Real.log (2*M : ℕ)+8));
      let J := ∑ n ∈ S, w n*(∑ i ∈ Finset.Ico (lo n) (hi n),
        (ZetaRieszOwnerMaximal.ownerWeight N (Real.log n/T n i)*a i*
          ZetaRieszGlobalCurvature.cutoffSlope (D i) n)/(T n i-Real.log n));
      let K := Real.sqrt (144*(((b+1 : ℕ) : ℝ)^2)*E*W^2/
        (Real.log M)^2*(B^2+B)*
        (∑ i ∈ Finset.range (2^b), (a i)^2));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_owner_shell_bounds hh
  refine ⟨E,hE,fun b N M S R D a w T lo hi W hN hM hW hS hSF hw hR hD hsep hr howner hmono => ?_⟩
  have hb := hbound b N M S R D a w T lo hi W hN hM hW hS hSF hw hR hD hsep hr howner hmono
  let B := (2*Real.exp (1/2)*Real.log 4)*(1+Real.log (4*Real.log (2*M : ℕ)+8))
  have hH : primeHarmonic (2*M) ≤ B := primeHarmonic_le_loglog (2*M)
  have hQ : primeHarmonic (2*M)^2+primeHarmonic (2*M) ≤ B^2+B :=
    add_le_add (pow_le_pow_left₀ (primeHarmonic_nonneg _) hH 2) hH
  have hroot : Real.sqrt (144*(((b+1 : ℕ) : ℝ)^2)*E*W^2/
      (Real.log M)^2*(primeHarmonic (2*M)^2+primeHarmonic (2*M))*
      (∑ i ∈ Finset.range (2^b), (a i)^2)) ≤
      Real.sqrt (144*(((b+1 : ℕ) : ℝ)^2)*E*W^2/(Real.log M)^2*
        (B^2+B)*(∑ i ∈ Finset.range (2^b), (a i)^2)) := by
    apply Real.sqrt_le_sqrt
    gcongr
  dsimp only at hb ⊢
  constructor <;> linarith only [hb.1,hb.2,hroot]

/-- The same all-count logarithmic budget retains complete complex
coefficient and cofactor phases before taking the real part. Passing to
the two real coordinates costs only one fixed factor two in E_h. -/
theorem exists_complex_owner_shell_bounds {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (b N M : ℕ) (S : Finset ℕ) (R : ℕ → ℕ)
      (D : ℕ → ℝ) (a w : ℕ → ℂ) (T : ℕ → ℕ → ℝ) (lo hi : ℕ → ℕ) (W : ℝ),
      32 ≤ N → 2 ≤ M → 0 ≤ W → S ⊆ Finset.Ioc M (2*M) →
      (∀ n ∈ S, Squarefree n) → (∀ n ∈ S, ‖w n‖ ≤ W/n) →
      (∀ i < 2^b, 0 < R i) →
      (∀ i < 2^b, (R i : ℝ) < Real.exp (D i) ∧ Real.exp (D i) ≤ R i+1) →
      (∀ (i : ℕ), i < 2^b → ∀ (j : ℕ), j < 2^b →
        h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      (∀ n ∈ S, lo n ≤ hi n ∧ hi n ≤ 2^b) →
      (∀ n ∈ S, ∀ i ∈ Finset.Ico (lo n) (hi n),
        ∀ p ∈ n.primeFactors, Real.log p ≤ T n i-Real.log n) →
      (∀ n ∈ S, ∀ i ∈ Finset.Ico (lo n) (hi n),
        ∀ j ∈ Finset.Ico (lo n) (hi n), i ≤ j → T n i ≤ T n j) →
      let B := (2*Real.exp (1/2)*Real.log 4)*(1+Real.log (4*Real.log (2*M : ℕ)+8));
      let J := (∑ n ∈ S, w n*(∑ i ∈ Finset.Ico (lo n) (hi n),
        (((ZetaRieszOwnerMaximal.ownerWeight N (Real.log n/T n i)*
          ZetaRieszGlobalCurvature.cutoffSlope (D i) n)/(T n i-Real.log n) : ℝ) : ℂ)*a i)).re;
      let K := Real.sqrt (144*(((b+1 : ℕ) : ℝ)^2)*E*W^2/
        (Real.log M)^2*(B^2+B)*
        (∑ i ∈ Finset.range (2^b), ‖a i‖^2));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_owner_shell_loglog_bounds hh
  refine ⟨2*E,by positivity,fun b N M S R D a w T lo hi W hN hM hW hS hSF hw hR hD hsep hr howner hmono => ?_⟩
  let B := (2*Real.exp (1/2)*Real.log 4)*(1+Real.log (4*Real.log (2*M : ℕ)+8))
  let Q := 144*(((b+1 : ℕ) : ℝ)^2)*E*W^2/(Real.log M)^2*(B^2+B)
  have hB0 : 0 ≤ B := (primeHarmonic_nonneg _).trans (primeHarmonic_le_loglog (2*M))
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  let Ar := ∑ i ∈ Finset.range (2^b), (a i).re^2
  let Ai := ∑ i ∈ Finset.range (2^b), (a i).im^2
  let Jr := ∑ n ∈ S, (w n).re*(∑ i ∈ Finset.Ico (lo n) (hi n),
    (ZetaRieszOwnerMaximal.ownerWeight N (Real.log n/T n i)*(a i).re*
      ZetaRieszGlobalCurvature.cutoffSlope (D i) n)/(T n i-Real.log n))
  let Ji := ∑ n ∈ S, (w n).im*(∑ i ∈ Finset.Ico (lo n) (hi n),
    (ZetaRieszOwnerMaximal.ownerWeight N (Real.log n/T n i)*(a i).im*
      ZetaRieszGlobalCurvature.cutoffSlope (D i) n)/(T n i-Real.log n))
  have hreal := hbound b N M S R D (fun i => (a i).re) (fun n => (w n).re)
    T lo hi W hN hM hW hS hSF
    (fun n hn => (Complex.abs_re_le_norm _).trans (hw n hn)) hR hD hsep hr howner hmono
  have hi' := hbound b N M S R D (fun i => (a i).im) (fun n => (w n).im)
    T lo hi W hN hM hW hS hSF
    (fun n hn => (Complex.abs_im_le_norm _).trans (hw n hn)) hR hD hsep hr howner hmono
  change -Real.sqrt (Q*Ar) ≤ Jr ∧ Jr ≤ Real.sqrt (Q*Ar) at hreal
  change -Real.sqrt (Q*Ai) ≤ Ji ∧ Ji ≤ Real.sqrt (Q*Ai) at hi'
  have hr2 : Jr^2 ≤ Q*Ar := by
    have ht := (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mpr (abs_le.mpr hreal)
    rwa [sq_abs,Real.sq_sqrt (mul_nonneg hQ0 (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))] at ht
  have hi2 : Ji^2 ≤ Q*Ai := by
    have ht := (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mpr (abs_le.mpr hi')
    rwa [sq_abs,Real.sq_sqrt (mul_nonneg hQ0 (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))] at ht
  have ha : (∑ i ∈ Finset.range (2^b), ‖a i‖^2) = Ar+Ai := by
    dsimp only [Ar,Ai]
    simp_rw [Complex.sq_norm,Complex.normSq_apply]
    simp only [Finset.sum_add_distrib,pow_two]
  have he : (∑ n ∈ S, w n*(∑ i ∈ Finset.Ico (lo n) (hi n),
      (((ZetaRieszOwnerMaximal.ownerWeight N (Real.log n/T n i)*
        ZetaRieszGlobalCurvature.cutoffSlope (D i) n)/(T n i-Real.log n) : ℝ) : ℂ)*a i)).re = Jr-Ji := by
    dsimp only [Jr,Ji]
    rw [← Finset.sum_sub_distrib,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Complex.mul_re,Complex.re_sum,Complex.im_sum,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    congr 1 <;> congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi' <;> ring
  dsimp only
  rw [he]
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs,Real.sq_sqrt (by positivity),ha]
  have hsame : 144*(((b+1 : ℕ) : ℝ)^2)*(2*E)*W^2/(Real.log M)^2*(B^2+B)*(Ar+Ai) =
      2*Q*(Ar+Ai) := by dsimp [Q]; ring
  change (Jr-Ji)^2 ≤ 144*(((b+1 : ℕ) : ℝ)^2)*(2*E)*W^2/(Real.log M)^2*(B^2+B)*(Ar+Ai)
  rw [hsame]
  nlinarith only [hr2,hi2,sq_nonneg (Jr+Ji)]

end RiemannGaussian.ZetaRieszOwnerCountEnergy
