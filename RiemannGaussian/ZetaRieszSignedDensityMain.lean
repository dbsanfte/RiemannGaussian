/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCofactorDiscrepancy
import RiemannGaussian.EtaMoebiusLogHarmonicBound
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# An explicit bound for the signed cofactor main expression

The squarefree-density Möbius coefficient is a positive Dirichlet convolution
of the classical reciprocal Möbius coefficient. Its exact total mass times the squarefree density is one. Thus its sharp
prefix is bounded by two and its logarithmic Riesz mean by seven, independently
of the cutoff.

Recombining the original two-hinge profile before taking norms gives a
uniform bound of fourteen. This bounds the entire `compositeModel` main
with the literal owned masks, allocation and factorial weight. The final
core bound is explicit but still has the source factor `(2*u)^(N+1)`.
It does not pay the comparison error, prove a cofinal floor/ceiling, or
assert a zero exclusion.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszSignedDensityMain
open Real Filter Topology

/-- The classical reciprocal Möbius Riesz mean at a real logarithmic cutoff. -/
def reciprocalRiesz (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊exp t⌋₊, (μ n : ℝ)/n*(t-log n)

/-- The nonpositive physical range has zero Riesz response, including its boundary. -/
theorem reciprocalRiesz_nonpos {t : ℝ} (ht : t ≤ 0) : reciprocalRiesz t = 0 := by
  by_cases hz : t = 0
  · simp [hz,reciprocalRiesz]
  · have he : exp t < 1 := exp_lt_one_iff.mpr (lt_of_le_of_ne ht hz)
    have hf : ⌊exp t⌋₊ = 0 := Nat.floor_eq_zero.mpr he
    simp [reciprocalRiesz,hf]

/-- An elementary signed bound, uniform over every real cutoff. -/
theorem reciprocalRiesz_bound (t : ℝ) : |reciprocalRiesz t| ≤ 7 := by
  by_cases ht : t ≤ 0
  · rw [reciprocalRiesz_nonpos ht]; norm_num
  have ht0 : 0 < t := lt_of_not_ge ht
  let X := ⌊exp t⌋₊
  have hX : 1 ≤ X := Nat.le_floor (by simpa using one_le_exp_iff.mpr ht0.le)
  have hXr : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hl : log X ≤ t := by
    simpa using log_le_log hXr (Nat.floor_le (exp_pos t).le)
  have hu : t < log (X+1 : ℝ) := by
    simpa using log_lt_log (exp_pos t) (Nat.lt_floor_add_one (exp t))
  have hstep : log (X+1 : ℝ)-log X ≤ 1 := by
    rw [← log_div (by positivity) hXr.ne']
    have hh := log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ)<X+1) hXr)
    have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have hv : (X+1 : ℝ)/X-1 ≤ 1 := by
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hXr).mpr
      linarith
    exact hh.trans hv
  have hdiff : |t-log X| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  have he : reciprocalRiesz t =
      (∑ n ∈ Finset.Icc 1 X, (μ n : ℝ)/n*(log X-log n))+
      (t-log X)*moebiusHarmonicPrefix X := by
    simp only [reciprocalRiesz,moebiusHarmonicPrefix,Finset.mul_sum,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hb : |∑ n ∈ Finset.Icc 1 X, (μ n : ℝ)/n*(log X-log n)| ≤ 5 := by
    by_cases hX1 : X=1
    · simp [hX1]
    · have hX2 : 1<X := by omega
      have hxlog : 0 < log X := log_pos (by exact_mod_cast hX2)
      have hh := mul_le_mul_of_nonneg_right
        (abs_pairedEtaMoebiusLogHarmonic_le_five_div_log hX2) hxlog.le
      rw [div_mul_cancel₀ _ hxlog.ne'] at hh
      rw [← abs_of_nonneg hxlog.le,← abs_mul] at hh
      apply le_trans (le_of_eq ?_) hh
      congr 1
      simp only [pairedEtaMoebiusLogHarmonic,pairedEtaMoebiusTrialLogWeight,
        if_pos hX2,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      field_simp
  rw [he]
  have hc : |(t-log X)*moebiusHarmonicPrefix X| ≤ 2 := by
    rw [abs_mul]
    exact (mul_le_mul hdiff (abs_moebiusHarmonicPrefix_le_two X)
      (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  exact (abs_add_le _ _).trans (by linarith)

private theorem expWeight_one {n : ℕ} (hn : 0 < n) :
    zetaPrimeExpWeight 1 n = (n : ℝ)⁻¹ := by
  simp only [zetaPrimeExpWeight,neg_one_mul,exp_neg]
  rw [exp_log (by exact_mod_cast hn)]

/-- Exact finite square-sieve factorization, retaining each marked prime. -/
theorem finiteDensity_product (W Q : Finset ℕ)
    (hW : ∀ p ∈ W, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) :
    SquarefreeCounting.finiteDensity W Q =
      (∏ p ∈ W, (p : ℝ)⁻¹)*
        ∏ p ∈ Q, (1 - if p ∈ W then (p : ℝ)⁻¹ else (p : ℝ)⁻¹^2) := by
  have hi V (hV : V ∈ Q.powerset) :
      (primeSquareIntersection W V : ℝ)⁻¹ =
        (∏ p ∈ W, (p : ℝ)⁻¹)*
          ∏ p ∈ V, (if p ∈ W then (p : ℝ)⁻¹ else (p : ℝ)⁻¹^2) := by
    have hv p hp := hQ p (Finset.mem_powerset.mp hV hp)
    have hh := zetaPrimeExpWeight_primeSquareIntersection W V hW hv 1
    rw [expWeight_one (primeSquareIntersection_pos W V hW hv)] at hh
    rw [hh]
    congr 1
    · exact Finset.prod_congr rfl (fun p hp => expWeight_one (hW p hp).pos)
    · apply Finset.prod_congr rfl
      intro p hp
      rw [expWeight_one (hv p hp).pos]
  unfold SquarefreeCounting.finiteDensity
  simp_rw [div_eq_mul_inv]
  simp_rw [show (fun p => (1 : ℝ)-(if p ∈ W then (p : ℝ)⁻¹ else (p : ℝ)⁻¹^2)) =
    fun p => 1 + -(if p ∈ W then (p : ℝ)⁻¹ else (p : ℝ)⁻¹^2) from by funext p; ring]
  rw [Finset.prod_one_add,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro V hV
  rw [hi V hV,Finset.prod_neg]
  ring

private theorem prod_selected (W Q : Finset ℕ) (hWQ : W ⊆ Q) (f : ℕ → ℝ) :
    (∏ p ∈ Q, if p ∈ W then f p else 1) = ∏ p ∈ W, f p := by
  rw [Finset.prod_ite]
  simp [Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr hWQ]

/-- Once all marked primes are present, their density cost is exactly `1/(p+1)`. -/
theorem finiteDensity_marks (W Q : Finset ℕ)
    (hW : ∀ p ∈ W, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) (hWQ : W ⊆ Q) :
    SquarefreeCounting.finiteDensity W Q =
      SquarefreeCounting.finiteDensity ∅ Q * ∏ p ∈ W, ((p : ℝ)+1)⁻¹ := by
  rw [finiteDensity_product W Q hW hQ,
    finiteDensity_product ∅ Q (by simp) hQ]
  simp only [Finset.prod_empty,Finset.notMem_empty,if_false,one_mul]
  calc
    _ = ∏ p ∈ Q, (if p ∈ W then (p : ℝ)⁻¹ else 1)*
        (1-if p ∈ W then (p : ℝ)⁻¹ else (p : ℝ)⁻¹^2) := by
      rw [Finset.prod_mul_distrib,prod_selected W Q hWQ]
    _ = ∏ p ∈ Q, (1-(p : ℝ)⁻¹^2)*
        (if p ∈ W then ((p : ℝ)+1)⁻¹ else 1) := by
      apply Finset.prod_congr rfl
      intro p hp
      by_cases hm : p ∈ W
      · simp only [if_pos hm]
        have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hQ p hp).ne_zero
        have hp1 : (p : ℝ)+1 ≠ 0 := by positivity
        field_simp
        ring
      · simp [hm]
    _ = _ := by rw [Finset.prod_mul_distrib,prod_selected W Q hWQ]

/-- The canonical limiting squarefree density has the same exact marked factors. -/
theorem density_marks (W : Finset ℕ) (hW : ∀ p ∈ W, p.Prime) :
    SquarefreeCounting.density W =
      SquarefreeCounting.density ∅ * ∏ p ∈ W, ((p : ℝ)+1)⁻¹ := by
  have he : ∀ᶠ K : ℕ in atTop,
      SquarefreeCounting.finiteDensity W (zetaSquarePrimesThrough K) =
        SquarefreeCounting.finiteDensity ∅ (zetaSquarePrimesThrough K)*
          ∏ p ∈ W, ((p : ℝ)+1)⁻¹ := by
    filter_upwards [eventually_ge_atTop (W.sup id)] with K hK
    apply finiteDensity_marks W _ hW (zetaSquarePrimesThrough_prime K)
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨(hW p hp).pos,(Finset.le_sup (f := id) hp).trans hK⟩,hW p hp⟩
  exact tendsto_nhds_unique (SquarefreeCounting.finiteDensity_tendsto W hW)
    (((SquarefreeCounting.finiteDensity_tendsto ∅ (by simp)).mul_const
      (∏ p ∈ W, ((p : ℝ)+1)⁻¹)).congr' (he.mono (fun _ h => h.symm)))

/-- The unmarked squarefree density lies between zero and one. -/
theorem base_density_bounds :
    0 ≤ SquarefreeCounting.density ∅ ∧ SquarefreeCounting.density ∅ ≤ 1 := by
  have hn K : 0 ≤ SquarefreeCounting.finiteDensity ∅ (zetaSquarePrimesThrough K) :=
    SquarefreeCounting.finiteDensity_nonneg ∅ _ (by simp)
      (zetaSquarePrimesThrough_prime K)
  have hlow := ge_of_tendsto (SquarefreeCounting.finiteDensity_tendsto ∅ (by simp))
    (Eventually.of_forall hn)
  refine ⟨hlow,?_⟩
  have h := ciInf_le (show BddBelow (Set.range (fun K : ℕ =>
      SquarefreeCounting.finiteDensity ∅ (zetaSquarePrimesThrough K))) from
    ⟨0,by rintro _ ⟨K,rfl⟩; exact hn K⟩) 0
  exact h.trans_eq (by simp [zetaSquarePrimesThrough,SquarefreeCounting.finiteDensity,
    primeSquareIntersection])

/-- The multiplicative marked-density factor, extended to all positive integers. -/
def markArith : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => ((p : ℝ)+1)⁻¹)

/-- The nonnegative Dirichlet-convolution correction, including prime powers. -/
def correction : ArithmeticFunction ℝ :=
  markArith.pdiv (ArithmeticFunction.id : ArithmeticFunction ℝ)

/-- The signed reciprocal Möbius arithmetic function. -/
def reciprocalMoebius : ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ).pdiv
    (ArithmeticFunction.id : ArithmeticFunction ℝ)

/-- The marked-density factor is the product over distinct prime factors. -/
theorem markArith_apply {n : ℕ} (hn : n ≠ 0) :
    markArith n = ∏ p ∈ n.primeFactors, ((p : ℝ)+1)⁻¹ := by
  exact ArithmeticFunction.prodPrimeFactors_apply hn

/-- Every correction coefficient is nonnegative. -/
theorem correction_nonneg (n : ℕ) : 0 ≤ correction n := by
  by_cases hn : n=0
  · subst n; simp
  · simp only [correction,ArithmeticFunction.pdiv_apply,ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.id_apply,markArith_apply hn]
    positivity

private theorem mark_prime_power {p : ℕ} (hp : p.Prime) (k : ℕ) :
    markArith (p^(k+1)) = ((p : ℝ)+1)⁻¹ := by
  rw [markArith_apply (pow_ne_zero _ hp.ne_zero),Nat.primeFactors_pow p (by omega),
    hp.primeFactors,Finset.prod_singleton]

/-- Exact signed convolution before any absolute value: no prime-density approximation. -/
theorem density_convolution :
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ).pmul markArith =
      reciprocalMoebius*correction := by
  have hb := ArithmeticFunction.IsMultiplicative.prodPrimeFactors
    (fun p : ℕ => ((p : ℝ)+1)⁻¹)
  have hq := hb.pdiv (ArithmeticFunction.isMultiplicative_id.natCast (R := ℝ))
  have hm := ArithmeticFunction.isMultiplicative_moebius.intCast (R := ℝ)
  have hv := hm.pdiv (ArithmeticFunction.isMultiplicative_id.natCast (R := ℝ))
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ (hm.pmul hb)
    _ (hv.mul hq)).mpr
  intro p k hp
  change ((ArithmeticFunction.moebius : ArithmeticFunction ℝ).pmul markArith) (p^k) =
    (reciprocalMoebius*correction) (p^k)
  cases k with
  | zero => simp [markArith,correction,reciprocalMoebius]
  | succ k =>
    have he : (reciprocalMoebius*correction) (p^(k+1)) =
        correction (p^(k+1))-(p : ℝ)⁻¹*correction (p^k) := by
      rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal
        (fun a b => reciprocalMoebius a*correction b),
        Nat.sum_divisors_prime_pow hp]
      rw [Finset.sum_range_succ',Finset.sum_range_succ']
      have hz : (∑ j ∈ Finset.range k,
          reciprocalMoebius (p^(j+1+1))*correction (p^(k+1)/p^(j+1+1)))=0 := by
        apply Finset.sum_eq_zero
        intro j _
        simp [reciprocalMoebius,ArithmeticFunction.moebius_apply_prime_pow (k := j+1+1) hp (by omega)]
      rw [hz]
      have hdiv : p^(k+1)/p = p^k := by rw [pow_succ,Nat.mul_div_cancel _ hp.pos]
      simp [reciprocalMoebius,ArithmeticFunction.moebius_apply_prime hp,hdiv]
      ring
    rw [he,ArithmeticFunction.pmul_apply,ArithmeticFunction.intCoe_apply,
      mark_prime_power hp k]
    have hpr : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hp1 : (p : ℝ)+1 ≠ 0 := by positivity
    cases k with
    | zero =>
      simp only [Nat.reduceAdd,pow_one,pow_zero,ArithmeticFunction.moebius_apply_prime hp,
        Int.cast_neg,Int.cast_one,correction,ArithmeticFunction.pdiv_apply,
        ArithmeticFunction.natCoe_apply,ArithmeticFunction.id_apply]
      rw [markArith_apply hp.ne_zero,hp.primeFactors,Finset.prod_singleton]
      norm_num [markArith]
      field_simp
      ring
    | succ k =>
      rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega),if_neg (by omega)]
      simp only [Int.cast_zero,zero_mul,correction,ArithmeticFunction.pdiv_apply,
        ArithmeticFunction.natCoe_apply,ArithmeticFunction.id_apply,mark_prime_power hp,
        Nat.cast_pow]
      rw [pow_succ]
      field_simp
      ring

/-- Every squarefree divisor supplies a reciprocal bound for the marked density. -/
theorem markArith_le_inv {a n : ℕ} (ha : Squarefree a) (hd : a ∣ n)
    (hn : n ≠ 0) : markArith n ≤ (a : ℝ)⁻¹ := by
  rw [markArith_apply hn]
  have hs : a.primeFactors ⊆ n.primeFactors := Nat.primeFactors_mono hd hn
  calc
    _ ≤ ∏ p ∈ a.primeFactors, ((p : ℝ)+1)⁻¹ := by
      apply Finset.prod_le_prod_of_subset_of_le_one hs
      · intro p _; positivity
      · intro p hp _
        exact inv_le_one_of_one_le₀ (by have := Nat.cast_nonneg (α := ℝ) p; linarith)
    _ ≤ ∏ p ∈ a.primeFactors, (p : ℝ)⁻¹ := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro p hp
      exact inv_anti₀ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos) (by linarith)
    _ = _ := by
      rw [Finset.prod_inv_distrib,← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree ha]

/-- Square-times-squarefree decomposition gives a summable two-variable majorant. -/
theorem correction_square_bound {a b n : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hsf : Squarefree a) (he : b^2*a=n) :
    correction n ≤ (1/(a : ℝ))^2*(1/(b : ℝ))^2 := by
  have hn : 0 < n := he ▸ Nat.mul_pos (pow_pos hb _) ha
  have hd : a ∣ n := by rw [← he]; exact dvd_mul_left _ _
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  calc
    _ ≤ (a : ℝ)⁻¹/n := div_le_div_of_nonneg_right
      (markArith_le_inv hsf hd hn.ne') (Nat.cast_nonneg n)
    _ = _ := by rw [← he]; push_cast; field_simp

/-- The entire positive correction mass costs at most four, uniformly in the prefix. -/
theorem correction_prefix_bound (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, correction n) ≤ 4 := by
  have hd (n : ℕ) : ∃ a b : ℕ, n ≠ 0 →
      0<a ∧ 0<b ∧ b^2*a=n ∧ Squarefree a := by
    by_cases hn : n=0
    · exact ⟨1,1,fun h => False.elim (h hn)⟩
    · obtain ⟨a,b,ha,hb,he,hs⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hn)
      exact ⟨a,b,fun _ => ⟨ha,hb,he,hs⟩⟩
  choose a b hab using hd
  let S := Finset.Icc 1 X
  have hinj : Set.InjOn (fun n => (a n,b n)) S := by
    intro n hn m hm he
    have hn0 : n≠0 := by have := (Finset.mem_Icc.mp hn).1; omega
    have hm0 : m≠0 := by have := (Finset.mem_Icc.mp hm).1; omega
    rw [← (hab n hn0).2.2.1,← (hab m hm0).2.2.1]
    rw [Prod.mk.inj he |>.1,Prod.mk.inj he |>.2]
  have hsub : S.image (fun n => (a n,b n)) ⊆ S ×ˢ S := by
    intro p hp
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hp
    have hn' := Finset.mem_Icc.mp hn
    obtain ⟨ha,hb,he,_⟩ := hab n (by omega)
    have haN : a n ≤ n := Nat.le_of_dvd (by omega)
      ⟨b n^2,by nlinarith [he]⟩
    have hbN : b n ≤ n := by
      apply Nat.le_of_dvd (by omega)
      exact ⟨b n*a n,by nlinarith [he]⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨ha,haN.trans hn'.2⟩,
      Finset.mem_Icc.mpr ⟨hb,hbN.trans hn'.2⟩⟩
  calc
    _ ≤ ∑ n ∈ S, (1/(a n : ℝ))^2*(1/(b n : ℝ))^2 := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨ha,hb,he,hs⟩ := hab n (by have := (Finset.mem_Icc.mp hn).1; omega)
      exact correction_square_bound ha hb hs he
    _ = ∑ p ∈ S.image (fun n => (a n,b n)), (1/(p.1 : ℝ))^2*(1/(p.2 : ℝ))^2 :=
      (Finset.sum_image (f := fun p : ℕ×ℕ =>
        (1/(p.1 : ℝ))^2*(1/(p.2 : ℝ))^2) hinj).symm
    _ ≤ ∑ p ∈ S ×ˢ S, (1/(p.1 : ℝ))^2*(1/(p.2 : ℝ))^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (∑ n ∈ S, (1/(n : ℝ))^2)^2 := by
      simp only [Finset.sum_product,← Finset.mul_sum]
      rw [← Finset.sum_mul,pow_two]
    _ ≤ 4 := by
      have hlo : 0 ≤ ∑ n ∈ S, (1/(n : ℝ))^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hhi := sum_Icc_inv_sq_le_two X
      nlinarith


/-- The complete positive correction is summable, including every prime power. -/
theorem correction_summable : Summable correction := by
  apply summable_of_sum_le (c := 4) correction_nonneg
  intro S
  calc
    _ = ∑ n ∈ S.filter (fun n => n ≠ 0), correction n := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro n hn hnot
      have hz : n=0 := by simpa [hn] using hnot
      simp [hz]
    _ ≤ ∑ n ∈ Finset.Icc 1 (S.sup id), correction n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        have h := Finset.mem_filter.mp hn
        exact Finset.mem_Icc.mpr ⟨by omega, Finset.le_sup (f := id) h.1⟩
      · exact fun n _ _ => correction_nonneg n
    _ ≤ 4 := correction_prefix_bound _

/-- Its exact local mass is the reciprocal of the prime-square sieve factor. -/
theorem correction_prime_sum {p : ℕ} (hp : p.Prime) :
    (∑' k : ℕ, correction (p^k)) = (1-(p : ℝ)⁻¹^2)⁻¹ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hi : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have he k : correction (p^(k+1)) =
      (((p : ℝ)+1)⁻¹*(p : ℝ)⁻¹)*(p : ℝ)⁻¹^k := by
    change markArith (p^(k+1))/(p^(k+1) : ℕ) = _
    rw [markArith_apply (pow_ne_zero _ hp.ne_zero),
      Nat.primeFactors_pow p (by omega : k+1 ≠ 0),hp.primeFactors,
      Finset.prod_singleton,Nat.cast_pow,div_eq_mul_inv,inv_pow,pow_succ]
    ring
  have hs : Summable (fun k : ℕ => correction (p^k)) := by
    apply (summable_nat_add_iff 1).mp
    simp_rw [he]
    exact (hasSum_geometric_of_lt_one (inv_nonneg.mpr hp0.le) hi).summable.mul_left _
  rw [hs.tsum_eq_zero_add,show correction (p^0)=1 by simp [correction,markArith]]
  simp_rw [he]
  rw [tsum_mul_left,tsum_geometric_of_lt_one (inv_nonneg.mpr hp0.le) hi]
  have hi2 : 1-(p : ℝ)⁻¹^2 ≠ 0 := by
    have := (sq_lt_one_iff₀ (inv_nonneg.mpr hp0.le)).mpr hi
    linarith
  field_simp [hp0.ne', show 1-(p : ℝ)⁻¹ ≠ 0 by linarith, hi2]
  have hm : -1+(p : ℝ) ≠ 0 := by linarith
  have hs2 : -1+(p : ℝ)^2 ≠ 0 := by nlinarith
  ring_nf
  field_simp [hm, hs2]
  ring

/-- The correction and squarefree density normalize to total mass exactly one. -/
theorem density_correction_mass :
    SquarefreeCounting.density ∅ * ∑' n : ℕ, correction n = 1 := by
  have hm : correction.IsMultiplicative :=
    (ArithmeticFunction.IsMultiplicative.prodPrimeFactors
      (fun p : ℕ => ((p : ℝ)+1)⁻¹)).pdiv
      (ArithmeticFunction.isMultiplicative_id.natCast (R := ℝ))
  have he := hm.eulerProduct correction_summable.norm
  have hP K : zetaSquarePrimesThrough K = Nat.primesBelow (K+1) := by
    ext p
    simp only [zetaSquarePrimesThrough,Finset.mem_filter,Finset.mem_Icc,
      Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨_,h⟩,hp⟩; exact ⟨by omega,hp⟩
    · rintro ⟨h,hp⟩; exact ⟨⟨hp.pos,by omega⟩,hp⟩
  have hc := he.comp (tendsto_add_atTop_nat 1)
  have hlim := (SquarefreeCounting.finiteDensity_tendsto ∅ (by simp)).mul hc
  have hid K : SquarefreeCounting.finiteDensity ∅ (zetaSquarePrimesThrough K)*
      (∏ p ∈ Nat.primesBelow (K+1), ∑' k : ℕ, correction (p^k)) = 1 := by
    rw [finiteDensity_product ∅ _ (by simp) (zetaSquarePrimesThrough_prime K),hP]
    simp only [Finset.prod_empty,Finset.notMem_empty,if_false,one_mul]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    have hpP := (Nat.mem_primesBelow.mp hp).2
    rw [correction_prime_sum hpP,mul_inv_cancel₀]
    have hp1 : (1 : ℝ)<p := by exact_mod_cast hpP.one_lt
    have h0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
    have h1 := inv_lt_one_of_one_lt₀ hp1
    nlinarith [sq_nonneg ((p : ℝ)⁻¹-1)]
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr (fun K => (hid K).symm))

/-- Every truncated correction has normalized mass at most one. -/
theorem normalized_correction_prefix_bound (X : ℕ) :
    SquarefreeCounting.density ∅ * (∑ n ∈ Finset.Icc 1 X, correction n) ≤ 1 := by
  rw [← density_correction_mass]
  exact mul_le_mul_of_nonneg_left
    (correction_summable.sum_le_tsum _ (fun _ _ => correction_nonneg _)) base_density_bounds.1


/-- The logarithmic mean of the ORIGINAL signed squarefree-density coefficients. -/
def densityRiesz (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊exp t⌋₊,
    (μ n : ℝ)*SquarefreeCounting.density n.primeFactors*(t-log n)

/-- The exact signed logarithmic mean is a positive convolution of reciprocal Möbius means. -/
theorem densityRiesz_convolution (t : ℝ) :
    densityRiesz t = SquarefreeCounting.density ∅ *
      ∑ b ∈ Finset.Icc 1 ⌊exp t⌋₊, correction b*reciprocalRiesz (t-log b) := by
  have he n (hn : n ∈ Finset.Icc 1 ⌊exp t⌋₊) :
      (μ n : ℝ)*SquarefreeCounting.density n.primeFactors*(t-log n) =
        SquarefreeCounting.density ∅ *
          ∑ ab ∈ n.divisorsAntidiagonal,
            correction ab.1*reciprocalMoebius ab.2*(t-log (ab.1*ab.2 : ℕ)) := by
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    rw [density_marks n.primeFactors (fun _ hp => Nat.prime_of_mem_primeFactors hp),
      ← markArith_apply hn0]
    have hc := congrArg (fun f : ArithmeticFunction ℝ => f n) density_convolution
    rw [mul_comm reciprocalMoebius correction,ArithmeticFunction.mul_apply,
      ArithmeticFunction.pmul_apply,ArithmeticFunction.intCoe_apply] at hc
    rw [show (μ n : ℝ)*(SquarefreeCounting.density ∅*markArith n)*(t-log n) =
      SquarefreeCounting.density ∅*((μ n : ℝ)*markArith n)*(t-log n) by ring,
      hc,mul_assoc,Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl (fun ab hab => by rw [(Nat.mem_divisorsAntidiagonal.mp hab).1])
  unfold densityRiesz
  rw [Finset.sum_congr rfl he,← Finset.mul_sum,
    ZetaRieszGlobalCurvature.weighted_hyperbola (fun a b =>
      correction a*reciprocalMoebius b*(t-log (a*b : ℕ)))]
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  have hb0 : (0 : ℝ)<b := by exact_mod_cast (Finset.mem_Icc.mp hb).1
  rw [reciprocalRiesz,exp_sub,exp_log hb0,Nat.floor_div_natCast,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have ha0 : (0 : ℝ)<a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
  rw [Nat.cast_mul,log_mul hb0.ne' ha0.ne']
  simp only [reciprocalMoebius,ArithmeticFunction.pdiv_apply,
    ArithmeticFunction.intCoe_apply,ArithmeticFunction.natCoe_apply,ArithmeticFunction.id_apply]
  ring

/-- Cutoff-independent bound on the signed density Riesz mean. -/
theorem densityRiesz_bound (t : ℝ) : |densityRiesz t| ≤ 7 := by
  rw [densityRiesz_convolution,abs_mul,abs_of_nonneg base_density_bounds.1]
  have hs : |∑ b ∈ Finset.Icc 1 ⌊exp t⌋₊,
      correction b*reciprocalRiesz (t-log b)| ≤
      (∑ b ∈ Finset.Icc 1 ⌊exp t⌋₊, correction b)*7 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro b _
    rw [abs_mul,abs_of_nonneg (correction_nonneg b)]
    exact mul_le_mul_of_nonneg_left (reciprocalRiesz_bound _) (correction_nonneg b)
  calc
    _ ≤ SquarefreeCounting.density ∅ *
        ((∑ b ∈ Finset.Icc 1 ⌊exp t⌋₊, correction b)*7) :=
      mul_le_mul_of_nonneg_left hs base_density_bounds.1
    _ = (SquarefreeCounting.density ∅ *
        (∑ b ∈ Finset.Icc 1 ⌊exp t⌋₊, correction b))*7 := by ring
    _ ≤ 7 := by have := normalized_correction_prefix_bound ⌊exp t⌋₊; linarith


/-- The real cutoff equals any finite hinge sum containing its whole support. -/
theorem densityRiesz_eq_hinge (t : ℝ) {R : ℕ} (hR : ⌊exp t⌋₊ ≤ R) :
    densityRiesz t = ∑ d ∈ Finset.Icc 1 R,
      (μ d : ℝ)*SquarefreeCounting.density d.primeFactors*max 0 (t-log d) := by
  unfold densityRiesz
  have he : (∑ d ∈ Finset.Icc 1 ⌊exp t⌋₊,
      (μ d : ℝ)*SquarefreeCounting.density d.primeFactors*(t-log d)) =
      ∑ d ∈ Finset.Icc 1 ⌊exp t⌋₊,
        (μ d : ℝ)*SquarefreeCounting.density d.primeFactors*max 0 (t-log d) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hd0 : (0 : ℝ)<d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hde : (d : ℝ) ≤ exp t := (Nat.le_floor_iff (exp_nonneg t)).mp (Finset.mem_Icc.mp hd).2
    rw [max_eq_right (by have := log_le_log hd0 hde; rw [log_exp] at this; linarith)]
  rw [he]
  apply Finset.sum_subset (Finset.Icc_subset_Icc_right hR)
  intro d hd hnot
  have hd0 : (0 : ℝ)<d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hdR : ⌊exp t⌋₊ < d := by
    have := (Finset.mem_Icc.mp hd).1
    simp only [Finset.mem_Icc,not_and] at hnot
    have := hnot this
    omega
  have hdt : exp t < d := (Nat.floor_lt (exp_nonneg t)).mp hdR
  have hlog : t < log d := by simpa using log_lt_log (exp_pos t) hdt
  rw [max_eq_left (by linarith),mul_zero]

/-- The original two-hinge coefficient is exactly the difference of two signed means. -/
theorem hinge_density_eq (L : ℝ) (p : ℕ) {R : ℕ}
    (hR : ⌊exp L⌋₊ ≤ R) :
    (∑ d ∈ Finset.Icc 1 R, (μ d : ℝ)*SquarefreeCounting.density d.primeFactors*
      ZetaRieszJointPrimeEnergy.hinge L p d) = densityRiesz L-densityRiesz (L-log p) := by
  have hlog : 0 ≤ log p := log_natCast_nonneg p
  have hlo : ⌊exp (L-log p)⌋₊ ≤ R :=
    (Nat.floor_mono (exp_le_exp.mpr (by linarith))).trans hR
  rw [densityRiesz_eq_hinge L hR,densityRiesz_eq_hinge (L-log p) hlo,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  unfold ZetaRieszJointPrimeEnergy.hinge
  ring

/-- All divisor-cutoff signs are summed before the constant fourteen is charged. -/
theorem hinge_density_bound (L : ℝ) (p : ℕ) {R : ℕ}
    (hR : ⌊exp L⌋₊ ≤ R) :
    |∑ d ∈ Finset.Icc 1 R, (μ d : ℝ)*SquarefreeCounting.density d.primeFactors*
      ZetaRieszJointPrimeEnergy.hinge L p d| ≤ 14 := by
  rw [hinge_density_eq L p hR]
  exact (abs_sub _ _).trans (by linarith [densityRiesz_bound L,densityRiesz_bound (L-log p)])


open ZetaRieszCofactorDiscrepancy ZetaRieszJointPrimeEnergy


/-- The original sharp density prefix is the same positive convolution of signed prefixes. -/
theorem densityPrefix_convolution (D : ℕ) :
    densityPrefix D = SquarefreeCounting.density ∅ *
      ∑ b ∈ Finset.Icc 1 D, correction b*moebiusHarmonicPrefix (D/b) := by
  have he n (hn : n ∈ Finset.Icc 1 D) :
      (μ n : ℝ)*SquarefreeCounting.density n.primeFactors =
        SquarefreeCounting.density ∅ *
          ∑ ab ∈ n.divisorsAntidiagonal, correction ab.1*reciprocalMoebius ab.2 := by
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    rw [density_marks n.primeFactors (fun _ hp => Nat.prime_of_mem_primeFactors hp),
      ← markArith_apply hn0]
    have hc := congrArg (fun f : ArithmeticFunction ℝ => f n) density_convolution
    rw [mul_comm reciprocalMoebius correction,ArithmeticFunction.mul_apply,
      ArithmeticFunction.pmul_apply,ArithmeticFunction.intCoe_apply] at hc
    rw [← hc]
    ring
  unfold densityPrefix
  rw [Finset.sum_congr rfl he,← Finset.mul_sum,
    ZetaRieszGlobalCurvature.weighted_hyperbola (fun a b => correction a*reciprocalMoebius b)]
  simp only [← Finset.mul_sum,moebiusHarmonicPrefix,reciprocalMoebius,
    ArithmeticFunction.pdiv_apply,ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.natCoe_apply,ArithmeticFunction.id_apply]

/-- The original sharp density coefficient is uniformly bounded, without a zero hypothesis. -/
theorem densityPrefix_bound (D : ℕ) : |densityPrefix D| ≤ 2 := by
  rw [densityPrefix_convolution,abs_mul,abs_of_nonneg base_density_bounds.1]
  have hs : |∑ b ∈ Finset.Icc 1 D, correction b*moebiusHarmonicPrefix (D/b)| ≤
      (∑ b ∈ Finset.Icc 1 D, correction b)*2 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro b _
    rw [abs_mul,abs_of_nonneg (correction_nonneg b)]
    exact mul_le_mul_of_nonneg_left (abs_moebiusHarmonicPrefix_le_two _) (correction_nonneg b)
  calc
    _ ≤ SquarefreeCounting.density ∅ *((∑ b ∈ Finset.Icc 1 D, correction b)*2) :=
      mul_le_mul_of_nonneg_left hs base_density_bounds.1
    _ = (SquarefreeCounting.density ∅ *(∑ b ∈ Finset.Icc 1 D, correction b))*2 := by ring
    _ ≤ 2 := by have := normalized_correction_prefix_bound D; linarith

/-- Uniform sharp-main estimate with the complete signed cofactor sum still intact. -/
theorem literal_main_bound (A B : Finset ℕ)
    (hB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card)
    (L y scale : ℝ) (N p X D : ℕ) :
    |compositeModel X D (fun n => maskedWeight A (ownerRows B) L y scale N n p)| ≤
      2*|∑ n ∈ Finset.Icc 1 X, maskedWeight A (ownerRows B) L y scale N n p| := by
  rw [literal_compositeModel A B hB L y scale N p X D,abs_mul]
  exact mul_le_mul_of_nonneg_right (densityPrefix_bound D) (abs_nonneg _)

/-- The original hinge vanishes beyond its full physical support. -/
theorem hinge_endpoint (L : ℝ) (p R : ℕ) (hR : ⌊exp L⌋₊ ≤ R) :
    hinge L p (R+1) = 0 := by
  have hx : exp L < (R+1 : ℕ) := (Nat.floor_lt (exp_nonneg L)).mp (by omega)
  have hl : L < log (R+1 : ℕ) := by simpa using log_lt_log (exp_pos L) hx
  have hp := log_natCast_nonneg p
  unfold hinge
  rw [max_eq_left (by linarith),max_eq_left (by linarith),sub_self]

/-- Exact main-term identity for the literal zero extension; no virtual primes are inserted. -/
theorem literal_profile_main_eq (A B : Finset ℕ)
    (hB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card)
    (L y scale : ℝ) (N p X R : ℕ) (hR : ⌊exp L⌋₊ ≤ R) :
    (∑ D ∈ Finset.Icc 1 R, (hinge L p D-hinge L p (D+1))*
      compositeModel X D (fun n => maskedWeight A (ownerRows B) L y scale N n p)) =
      (densityRiesz L-densityRiesz (L-log p))*
        ∑ n ∈ Finset.Icc 1 X, maskedWeight A (ownerRows B) L y scale N n p := by
  simp_rw [literal_compositeModel A B hB L y scale N p X]
  simp only [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  change (∑ D ∈ Finset.Icc 1 R, (hinge L p D-hinge L p (D+1))*
    ∑ d ∈ Finset.Icc 1 D, (μ d : ℝ)*SquarefreeCounting.density d.primeFactors) = _
  rw [← ZetaRieszSignedCutoffEnergy.abel_profile R (hinge L p)
    (fun d => (μ d : ℝ)*SquarefreeCounting.density d.primeFactors) (hinge_endpoint L p R hR)]
  simpa only [mul_comm (hinge L p _)] using hinge_density_eq L p hR

/-- The full signed main is bounded after cutoff cancellation, retaining phase inside each column. -/
theorem literal_profile_main_bound (A B : Finset ℕ)
    (hB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card)
    (L y scale : ℝ) (N X R : ℕ) (P : Finset ℕ) (hR : ⌊exp L⌋₊ ≤ R) :
    |∑ p ∈ P, ∑ D ∈ Finset.Icc 1 R, (hinge L p D-hinge L p (D+1))*
      compositeModel X D (fun n => maskedWeight A (ownerRows B) L y scale N n p)| ≤
      14*∑ p ∈ P, |∑ n ∈ Finset.Icc 1 X, maskedWeight A (ownerRows B) L y scale N n p| := by
  simp_rw [literal_profile_main_eq A B hB L y scale N _ X R hR]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  rw [← hinge_density_eq L p hR]
  exact hinge_density_bound L p hR


open ZetaRieszCentralRadialCost

/-- The complete integer factorial mass is bounded after summing radial shells, without a population maximum. -/
theorem radial_integer_mass (k X : ℕ) :
    (∑ m ∈ Finset.Icc 1 X, radial k (log m)/(m : ℝ)) ≤ exp 2 * 2^(k+1) := by
  let J := ⌊log (X+1 : ℕ)⌋₊+1
  let bin (m : ℕ) := ⌊log m⌋₊
  let S (j : ℕ) := (Finset.Icc 1 X).filter (fun m => bin m=j)
  have hmap m (hm : m ∈ Finset.Icc 1 X) : bin m ∈ Finset.range J := by
    have hm0 : (0 : ℝ)< m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hlog := log_le_log hm0 (show (m : ℝ) ≤ (X+1 : ℕ) by exact_mod_cast
      ((Finset.mem_Icc.mp hm).2.trans (Nat.le_succ X)))
    have hh := Nat.floor_mono hlog
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hh)
  have hbin j : (∑ m ∈ S j, radial k (log m)/(m : ℝ)) ≤
      exp (3/2 : ℝ)*radial k (j+1) := by
    have hb m (hm : m ∈ S j) : (j : ℝ) ≤ log m ∧ log m < j+1 := by
      have he := (Finset.mem_filter.mp hm).2
      constructor
      · rw [← he]; exact Nat.floor_le (log_natCast_nonneg m)
      · rw [← he]; exact Nat.lt_floor_add_one _
    have hs : S j ⊆ Finset.Icc 1 ⌊exp (j+1 : ℝ)⌋₊ := by
      intro m hm
      refine Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1,?_⟩
      have hm0 : (0 : ℝ)< m := by exact_mod_cast
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
      apply Nat.le_floor
      simpa only [exp_log hm0] using exp_le_exp.mpr (hb m hm).2.le
    have hcard : (S j).card ≤ ⌊exp (j+1 : ℝ)⌋₊ := by
      simpa using Finset.card_le_card hs
    have hcardR : ((S j).card : ℝ) ≤ exp (j+1 : ℝ) :=
      (show ((S j).card : ℝ) ≤ ⌊exp (j+1 : ℝ)⌋₊ by exact_mod_cast hcard).trans
        (Nat.floor_le (exp_nonneg _))
    have hone m (hm : m ∈ S j) : radial k (log m)/(m : ℝ) ≤
        exp (1/2-(j : ℝ))*radial k (j+1) := by
      have hm0 : (0 : ℝ)< m := by exact_mod_cast
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
      have hi : (m : ℝ)⁻¹=exp (-log m) := by rw [exp_neg,exp_log hm0]
      have he : exp (-log m/2)*exp (-log m) ≤
          exp (1/2-(j : ℝ))*exp (-(j+1 : ℝ)/2) := by
        rw [← exp_add,← exp_add]
        apply exp_le_exp.mpr
        linarith [(hb m hm).1]
      have hp := pow_le_pow_left₀ (log_natCast_nonneg m) (hb m hm).2.le k
      unfold radial
      calc
        _ = (exp (-log m/2)*exp (-log m))*(log m)^k/k.factorial := by
          rw [div_eq_mul_inv _ (m : ℝ),hi]; ring
        _ ≤ (exp (1/2-(j : ℝ))*exp (-(j+1 : ℝ)/2))*(j+1 : ℝ)^k/k.factorial :=
          div_le_div_of_nonneg_right (mul_le_mul he hp (by positivity) (by positivity)) (by positivity)
        _ = _ := by ring
    have hsum := Finset.sum_le_sum hone
    simp only [Finset.sum_const,nsmul_eq_mul] at hsum
    calc
      _ ≤ ((S j).card : ℝ)*(exp (1/2-(j : ℝ))*radial k (j+1)) := hsum
      _ ≤ exp (j+1 : ℝ)*(exp (1/2-(j : ℝ))*radial k (j+1)) :=
        mul_le_mul_of_nonneg_right hcardR (by unfold radial; positivity)
      _ = _ := by rw [← mul_assoc,← exp_add]; congr 2; ring
  have hf := Finset.sum_fiberwise_of_maps_to (f := fun m => radial k (log m)/(m : ℝ)) hmap
  rw [← hf]
  apply (Finset.sum_le_sum (fun j (_ : j ∈ Finset.range J) => hbin j)).trans
  rw [← Finset.mul_sum]
  have hr := sum_radial_le k J (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ)<1)
  simp only [mul_one,div_one] at hr
  have hr' : (∑ j ∈ Finset.range J, radial k (j+1)) ≤ exp (1/2 : ℝ)*2^(k+1) := by
    simpa only [add_comm] using hr
  calc
    _ ≤ exp (3/2 : ℝ)*(exp (1/2 : ℝ)*2^(k+1)) :=
      mul_le_mul_of_nonneg_left hr' (exp_nonneg _)
    _ = _ := by rw [← mul_assoc,← exp_add]; norm_num


open ZetaRieszJointAllocation

/-- The original factorial weight and full product phase in its exact radial normalization. -/
theorem primeWeight_radial (A : Finset ℕ) (L y : ℝ) (N : ℕ) {n p : ℕ}
    (hn : 0 < n) (hp : 0 < p) :
    primeWeight A L y N n p =
      -(1-boundedShare A N (p*n))*((N+1 : ℕ) : ℝ)/L *
        (radial (N+1) (log (p*n : ℕ))/(p*n : ℕ)) * cos (y*log (p*n : ℕ)) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [Nat.cast_mul,log_mul hpR hnR]
  unfold primeWeight radial
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  by_cases hL : L=0
  · simp [hL]
  · field_simp

/-- The residual allocation costs at most one; no factorial-order or count splitting is used. -/
theorem primeWeight_mass_bound (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (y scale : ℝ) (N : ℕ) {n p : ℕ} (hn : 0 < n) (hp : 0 < p) :
    |scale*primeWeight A L y N n p| ≤
      (|scale| *(N+1 : ℕ)/L)*(radial (N+1) (log (n*p : ℕ))/(n*p : ℕ)) := by
  rw [primeWeight_radial A L y N hn hp]
  have ha : |1-boundedShare A N (p*n)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (boundedShare_bounds A N (p*n)).2)]
    linarith [(boundedShare_bounds A N (p*n)).1]
  have hb : |1-boundedShare A N (p*n)| *|cos (y*log (p*n : ℕ))| ≤ 1 :=
    (mul_le_mul ha (abs_cos_le_one _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hr : 0 ≤ radial (N+1) (log (p*n : ℕ))/(p*n : ℕ) := by
    unfold radial; positivity
  simp only [abs_mul,abs_div,abs_neg,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (N+1)),abs_of_pos hL,abs_of_nonneg hr]
  calc
    _ = (|1-boundedShare A N (p*n)| *|cos (y*log (p*n : ℕ))|)*
        ((|scale| *(N+1 : ℕ)/L)*(radial (N+1) (log (p*n : ℕ))/(p*n : ℕ))) := by ring
    _ ≤ (|scale| *(N+1 : ℕ)/L)*(radial (N+1) (log (p*n : ℕ))/(p*n : ℕ)) :=
      mul_le_of_le_one_left (by positivity) hb
    _ = _ := by rw [Nat.mul_comm p n]

/-- Unique largest-prime ownership bounds the entire literal weight once per integer label. -/
theorem literal_weight_mass_bound (A B : Finset ℕ)
    (hB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card)
    {L : ℝ} (hL : 0 < L) (y scale : ℝ) (N : ℕ) :
    (∑ p ∈ ownerPrimes B, |∑ n ∈ Finset.Icc 1 ((cofactors B).sup id),
      maskedWeight A (ownerRows B) L y scale N n p|) ≤
      (|scale| *(N+1 : ℕ)/L)*(exp 2*2^(N+2)) := by
  let f (m : ℕ) := radial (N+1) (log m)/(m : ℝ)
  let V := |scale| *(N+1 : ℕ)/L
  have hf m : 0 ≤ f m := by dsimp [f,radial]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hr (n : ℕ) (hn : 0 < n) :
      (∑ p ∈ ownerPrimes B, |maskedWeight A (ownerRows B) L y scale N n p|) ≤
        V*∑ p ∈ ownerRows B n, f (n*p) := by
    have hs : ownerRows B n ⊆ ownerPrimes B :=
      Finset.image_subset_image (Finset.filter_subset _ _)
    have he : (∑ p ∈ ownerPrimes B, |maskedWeight A (ownerRows B) L y scale N n p|) =
        ∑ p ∈ ownerRows B n, |scale*primeWeight A L y N n p| := by
      rw [← Finset.sum_subset hs]
      · exact Finset.sum_congr rfl (fun p hp => by simp only [maskedWeight,if_pos hp])
      · intro p _ hp
        simp [maskedWeight,hp]
    rw [he,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    exact primeWeight_mass_bound A hL y scale N hn (ownerRows_data B hB hp).1.pos
  have hc : cofactors B ⊆ Finset.Icc 1 ((cofactors B).sup id) := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero (cofactors_data B hB hn).1.ne_zero,
      Finset.le_sup (f := id) hn⟩
  have he : (∑ n ∈ Finset.Icc 1 ((cofactors B).sup id), ∑ p ∈ ownerRows B n, f (n*p)) =
      ∑ n ∈ cofactors B, ∑ p ∈ ownerRows B n, f (n*p) := by
    symm
    apply Finset.sum_subset hc
    intro n _ hn
    have hempty : ownerRows B n=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨m,hm,_⟩ := Finset.mem_image.mp hp
      obtain ⟨hm,he⟩ := Finset.mem_filter.mp hm
      exact hn (Finset.mem_image.mpr ⟨m,hm,he⟩)
    rw [hempty,Finset.sum_empty]
  have howned : (∑ n ∈ cofactors B, ∑ p ∈ ownerRows B n, f (n*p)) = ∑ m ∈ B, f m := by
    have h := ZetaRieszCoupledWindow.sum_owned_products (cofactors B) (ownerRows B)
      (fun m => (f m : ℂ)) (fun _ hn => (cofactors_data B hB hn).1.ne_zero)
      (fun _ _ _ hp => ⟨(ownerRows_data B hB hp).1,(ownerRows_data B hB hp).2.2⟩)
    rw [owner_labels_eq B hB] at h
    exact_mod_cast h.symm
  calc
    _ ≤ ∑ p ∈ ownerPrimes B, ∑ n ∈ Finset.Icc 1 ((cofactors B).sup id),
        |maskedWeight A (ownerRows B) L y scale N n p| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ n ∈ Finset.Icc 1 ((cofactors B).sup id),
        ∑ p ∈ ownerPrimes B, |maskedWeight A (ownerRows B) L y scale N n p| := Finset.sum_comm
    _ ≤ ∑ n ∈ Finset.Icc 1 ((cofactors B).sup id), V*∑ p ∈ ownerRows B n, f (n*p) :=
      Finset.sum_le_sum (fun n hn => hr n (Finset.mem_Icc.mp hn).1)
    _ = V*∑ m ∈ B, f m := by rw [← Finset.mul_sum,he,howned]
    _ ≤ V*∑ m ∈ Finset.Icc 1 (B.sup id), f m := by
      apply mul_le_mul_of_nonneg_left _ hV
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        exact Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero (hB m hm).1.ne_zero,Finset.le_sup (f := id) hm⟩
      · exact fun m _ _ => hf m
    _ ≤ _ := mul_le_mul_of_nonneg_left (radial_integer_mass (N+1) (B.sup id)) hV

/-- An unconditional explicit bound on the WHOLE original signed comparison main, with arbitrary literal masks. -/
theorem whole_signed_main_bound (A B : Finset ℕ)
    (hB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card)
    {L : ℝ} (hL : 0 < L) (y scale : ℝ) (N R : ℕ) (hR : ⌊exp L⌋₊ ≤ R) :
    |∑ p ∈ ownerPrimes B, ∑ D ∈ Finset.Icc 1 R, (hinge L p D-hinge L p (D+1))*
      compositeModel ((cofactors B).sup id) D
        (fun n => maskedWeight A (ownerRows B) L y scale N n p)| ≤
      14*(|scale| *(N+1 : ℕ)/L)*(exp 2*2^(N+2)) := by
  exact (literal_profile_main_bound A B hB L y scale N ((cofactors B).sup id) R
    (ownerPrimes B) hR).trans
      (by have := mul_le_mul_of_nonneg_left (literal_weight_mass_bound A B hB hL y scale N)
            (by norm_num : (0 : ℝ) ≤ 14)
          simpa only [mul_assoc] using this)


open ZetaRieszParityPacket

/-- The actual core comparison main has an explicit source-normalized bound. Its exponential factor still grows for u>1/2. -/
theorem core_signed_main_bound {u : ℝ} (hu : 0 ≤ u) (y : ℝ) (N K : ℕ) :
    let B := (coreBand u N K).filter Squarefree
    let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
    let L := SquarefreeVaughanLogSource.length u N
    |∑ p ∈ ownerPrimes B, ∑ D ∈ Finset.Icc 1 ⌊exp L⌋₊,
      (hinge L p D-hinge L p (D+1))*compositeModel ((cofactors B).sup id) D
        (fun n => maskedWeight A (ownerRows B) L y (u^(N+1)) N n p)| ≤
      28*exp 2*((N+1 : ℕ)/L)*(2*u)^(N+1) := by
  dsimp only
  have hB : ∀ m ∈ (coreBand u N K).filter Squarefree,
      Squarefree m ∧ 3 ≤ m.primeFactors.card := by
    intro m hm
    exact ⟨(Finset.mem_filter.mp hm).2,core_count (Finset.mem_filter.mp hm).1⟩
  have h := whole_signed_main_bound (ZetaRieszAnnulusJoint.intermediatePrimes u N)
    ((coreBand u N K).filter Squarefree) hB (SquarefreeVaughanLogSource.length_pos u N)
    y (u^(N+1)) N ⌊exp (SquarefreeVaughanLogSource.length u N)⌋₊ le_rfl
  apply h.trans_eq
  rw [abs_of_nonneg (pow_nonneg hu _),mul_pow,
    show N+2=(N+1)+1 by omega,pow_succ (2 : ℝ) (N+1)]
  ring

end RiemannGaussian.ZetaRieszSignedDensityMain
