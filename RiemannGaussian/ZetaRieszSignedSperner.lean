/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOneSidedArithmetic
import RiemannGaussian.ZetaRieszParityWindow

/-!
# Sign-sensitive antichain bounds for the literal Riesz coefficients

The Mobius signs occupy different subset ranks. Keeping that parity in the
LYM inequality gives separate upper and lower capacities before the original
product phase and unassigned factorial weight are applied. These are
independent pointwise arithmetic bounds, not a cofinal floor or ceiling for
the full joint carrier.
-/

namespace RiemannGaussian.ZetaRieszSignedSperner
noncomputable section
open scoped BigOperators Classical
open Set MeasureTheory
open ZetaRieszSperner ZetaSquarefreeRieszWindows ZetaRieszOneSidedArithmetic

/-- The largest binomial layer of the specified parity; an absent parity
has capacity zero. This is a scalar allowance, not a new carrier. -/
def parityCapacity (k b : ℕ) : ℕ :=
  ((Finset.range (k+1)).filter (fun j => j % 2 = b)).sup (fun j => k.choose j)

/-- Every layer of the specified parity fits its exact capacity. -/
theorem choose_le_parityCapacity {k j b : ℕ} (hj : j ≤ k) (hb : j % 2 = b) :
    k.choose j ≤ parityCapacity k b := by
  exact Finset.le_sup (f := fun j => k.choose j)
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hb⟩)

/-- Retaining parity never enlarges the existing middle-layer allowance. -/
theorem parityCapacity_le_middle (k b : ℕ) :
    parityCapacity k b ≤ k.choose (k/2) := by
  exact Finset.sup_le (fun j _ => Nat.choose_le_middle j k)

/-- Positive and negative Mobius observations on one antichain have
different capacities. The exact signs are retained throughout the LYM sum. -/
theorem signed_antichain_bounds {ι : Type*} [Fintype ι]
    {A : Finset (Finset ι)} (hA : IsAntichain (· ⊆ ·) (A : Set (Finset ι))) :
    -(parityCapacity (Fintype.card ι) 1 : ℝ) ≤ ∑ S ∈ A, (-1 : ℝ)^S.card ∧
      (∑ S ∈ A, (-1 : ℝ)^S.card) ≤ (parityCapacity (Fintype.card ι) 0 : ℝ) := by
  have hlym : (∑ S ∈ A, ((Fintype.card ι).choose S.card : ℝ)⁻¹) ≤ 1 :=
    Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose hA
  have hterm (S : Finset ι) :
      -(parityCapacity (Fintype.card ι) 1 : ℝ) *
          ((Fintype.card ι).choose S.card : ℝ)⁻¹ ≤ (-1 : ℝ)^S.card ∧
        (-1 : ℝ)^S.card ≤ (parityCapacity (Fintype.card ι) 0 : ℝ) *
          ((Fintype.card ι).choose S.card : ℝ)⁻¹ := by
    have hc : (0 : ℝ) < (Fintype.card ι).choose S.card := by
      exact_mod_cast Nat.choose_pos S.card_le_univ
    rcases Nat.mod_two_eq_zero_or_one S.card with he | ho
    · have hs : (-1 : ℝ)^S.card = 1 := by
        rw [neg_one_pow_eq_pow_mod_two, he]
        norm_num
      have hh : ((Fintype.card ι).choose S.card : ℝ) ≤
          parityCapacity (Fintype.card ι) 0 := by
        exact_mod_cast choose_le_parityCapacity S.card_le_univ he
      rw [hs]
      constructor
      · exact le_trans (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity))
          (by positivity))
          (by norm_num)
      · rw [← div_eq_mul_inv, le_div_iff₀ hc]
        simpa using hh
    · have hs : (-1 : ℝ)^S.card = -1 := by
        rw [neg_one_pow_eq_pow_mod_two, ho]
        norm_num
      have hh : ((Fintype.card ι).choose S.card : ℝ) ≤
          parityCapacity (Fintype.card ι) 1 := by
        exact_mod_cast choose_le_parityCapacity S.card_le_univ ho
      rw [hs]
      constructor
      · rw [← div_eq_mul_inv, div_le_iff₀ hc]
        linarith
      · exact le_trans (by norm_num : (-1 : ℝ) ≤ 0) (by positivity)
  constructor
  · have hs := Finset.sum_le_sum (fun S (_ : S ∈ A) => (hterm S).1)
    rw [← Finset.mul_sum] at hs
    have hh := mul_le_mul_of_nonpos_left hlym
      (show -(parityCapacity (Fintype.card ι) 1 : ℝ) ≤ 0 from
        neg_nonpos.mpr (Nat.cast_nonneg _))
    simpa only [mul_one] using hh.trans hs
  · have hs := Finset.sum_le_sum (fun S (_ : S ∈ A) => (hterm S).2)
    rw [← Finset.mul_sum] at hs
    have hh := mul_le_mul_of_nonneg_left hlym
      (show (0 : ℝ) ≤ parityCapacity (Fintype.card ι) 0 by positivity)
    simpa only [mul_one] using hs.trans hh

/-- The actual squarefree divisor window inherits both signed capacities,
with no averaging of divisors or phases. -/
theorem signedDivisorWindow_bounds {m : ℕ} (hm : Squarefree m) {b : ℝ} (hb : 0 < b)
    (hw : ∀ p ∈ m.primeFactors, b ≤ Real.log p) (v : ℝ) :
    -(parityCapacity m.primeFactors.card 1 : ℝ) ≤ signedDivisorWindow b v m ∧
      signedDivisorWindow b v m ≤ (parityCapacity m.primeFactors.card 0 : ℝ) := by
  let D := m.divisors.filter (fun d : ℕ => v-b < Real.log d ∧ Real.log d < v)
  have hi : Set.InjOn (divisorPrimeSet m) (D : Set ℕ) :=
    (divisorPrimeSet_injective hm).mono (Finset.filter_subset _ _)
  have hsub : D.image (divisorPrimeSet m) ⊆
      subsetWindow (fun p : m.primeFactors => Real.log (p.val : ℝ)) b v := by
    intro A hA
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hA
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    rw [divisorPrimeSet_log_sum hm (Finset.mem_filter.mp hd).1]
    exact (Finset.mem_filter.mp hd).2
  have hA := (subsetWindow_antichain
    (fun p : m.primeFactors => Real.log (p.val : ℝ)) hb
    (fun p => hw p.val p.property) v).subset hsub
  have he : signedDivisorWindow b v m =
      ∑ S ∈ D.image (divisorPrimeSet m), (-1 : ℝ)^S.card := by
    rw [Finset.sum_image (fun d hd e he hh => hi hd he hh), signedDivisorWindow,
      ← Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    have hd' := (Finset.mem_filter.mp hd).1
    have hc : (divisorPrimeSet m d).card = d.primeFactors.card := by
      rw [← divisorPrimeSet_map hm hd', Finset.card_map]
    rw [hc]
    exact_mod_cast ZetaRieszReflectedLinear.moebius_eq_primeCount
      (hm.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd'))
  rw [he]
  simpa only [Fintype.card_coe] using signed_antichain_bounds hA

/-- The exact moving signed divisor window is integrable on each finite
prime interval, including all of its strict boundary conventions. -/
theorem integrableOn_signedDivisorWindow (L a b : ℝ) (m : ℕ) :
    IntegrableOn (fun s => signedDivisorWindow b (L-s) m) (Ioo 0 a) := by
  unfold signedDivisorWindow
  apply integrable_finsetSum
  intro d _
  have he : (fun s : ℝ => if L-s-b < Real.log d ∧ Real.log d < L-s then
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) =
      (Ioo (L-Real.log d-b) (L-Real.log d)).indicator
        (fun _ => ((ArithmeticFunction.moebius d : ℤ) : ℝ)) := by
    funext s
    simp only [indicator_apply, mem_Ioo]
    congr 1
    apply propext
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  rw [he]
  exact (integrableOn_const (μ := volume) (s := Ioo 0 a)
    (C := ((ArithmeticFunction.moebius d : ℤ) : ℝ)) (hs := by simp)).indicator
      measurableSet_Ioo

/-- The two smallest prime differences preserve the separate Mobius
capacities in the original Riesz response, for every real cutoff. -/
theorem riesz_two_primes_bounds (L : ℝ) {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpm : ¬ p ∣ m) (hqm : ¬ q ∣ m)
    (hm : Squarefree m) (hmin : ∀ r ∈ m.primeFactors, q ≤ r) :
    -(Real.log p * (parityCapacity m.primeFactors.card 1 : ℝ)) ≤
        VaughanLogAverage.riesz L (p*(q*m)) ∧
      VaughanLogAverage.riesz L (p*(q*m)) ≤
        Real.log p * (parityCapacity m.primeFactors.card 0 : ℝ) := by
  have hi := integrableOn_signedDivisorWindow L (Real.log p) (Real.log q) m
  have hw (s : ℝ) := signedDivisorWindow_bounds hm (b := Real.log q)
    (Real.log_pos (by exact_mod_cast hq.one_lt))
    (fun r hr => Real.log_le_log (by exact_mod_cast hq.pos)
      (by exact_mod_cast hmin r hr)) (L-s)
  rw [riesz_two_primes_eq_window_integral L hp hq hpq hpm hqm]
  constructor
  · have hl := setIntegral_ge_of_const_le_real measurableSet_Ioo (by simp)
      (fun s (_ : s ∈ Ioo 0 (Real.log p)) => (hw s).1) hi
    simpa only [Real.volume_real_Ioo, sub_zero, max_eq_left (Real.log_natCast_nonneg p),
      neg_mul, mul_neg, mul_comm] using hl
  · have hu := setIntegral_mono_on hi (integrableOn_const (hs := by simp))
      measurableSet_Ioo (fun s (_ : s ∈ Ioo 0 (Real.log p)) => (hw s).2)
    simpa only [setIntegral_const, Real.volume_real_Ioo, sub_zero,
      max_eq_left (Real.log_natCast_nonneg p), smul_eq_mul] using hu

/-- Every squarefree composite has the signed estimate with its actual
least prime. No radial, zero, phase or prime-count cutoff is assumed. -/
theorem riesz_bounds_minFac (L : ℝ) {n : ℕ} (hn : Squarefree n)
    (hcard : 2 ≤ n.primeFactors.card) :
    -(Real.log n.minFac * (parityCapacity (n.primeFactors.card-2) 1 : ℝ)) ≤
        VaughanLogAverage.riesz L n ∧
      VaughanLogAverage.riesz L n ≤
        Real.log n.minFac * (parityCapacity (n.primeFactors.card-2) 0 : ℝ) := by
  obtain ⟨p,q,m,hp,hq,hpq,he,hm,hpm,hqm,hpmin,hqmin,hcount⟩ :=
    exists_two_smallest_factorization hn hcard
  have hn1 : n ≠ 1 := by intro h; simp [h] at hcard
  have hpd : p ∣ n := he ▸ dvd_mul_right p (q*m)
  have hep : p = n.minFac := le_antisymm
    (hpmin n.minFac ((Nat.minFac_prime hn1).mem_primeFactors (Nat.minFac_dvd n) hn.ne_zero))
    (Nat.minFac_le_of_dvd hp.two_le hpd)
  have hh := riesz_two_primes_bounds L hp hq hpq hpm hqm hm hqmin
  rw [← he, hcount, hep] at hh
  exact hh

/-- Replacing only the least prime logarithm by its mean preserves both
one-sided capacities and permits a direct comparison with the old budget. -/
theorem riesz_bounds_mean (L : ℝ) {n : ℕ} (hn : Squarefree n)
    (hcard : 2 ≤ n.primeFactors.card) :
    -(Real.log n / n.primeFactors.card *
        (parityCapacity (n.primeFactors.card-2) 1 : ℝ)) ≤ VaughanLogAverage.riesz L n ∧
      VaughanLogAverage.riesz L n ≤ Real.log n / n.primeFactors.card *
        (parityCapacity (n.primeFactors.card-2) 0 : ℝ) := by
  obtain ⟨p,q,m,hp,hq,hpq,he,hm,hpm,hqm,hpmin,hqmin,hcount⟩ :=
    exists_two_smallest_factorization hn hcard
  have hh := riesz_two_primes_bounds L hp hq hpq hpm hqm hm hqmin
  rw [← he,hcount] at hh
  have hpmean := smallest_prime_log_le_mean hn (by omega) hp hpmin
  exact ⟨(neg_le_neg (mul_le_mul_of_nonneg_right hpmean (by positivity))).trans hh.1,
    hh.2.trans (mul_le_mul_of_nonneg_right hpmean (by positivity))⟩

/-- The original coefficient reverses the two Mobius capacities. The
actual least prime is retained, rather than a continuum prime share. -/
theorem coefficient_bounds_minFac {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card) :
    -(Real.log n / L * Real.log n.minFac *
        (parityCapacity (n.primeFactors.card-2) 0 : ℝ)) ≤
        (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤
        Real.log n / L * Real.log n.minFac *
          (parityCapacity (n.primeFactors.card-2) 1 : ℝ) := by
  have hnp : ¬ n.Prime := by
    intro hp
    simp only [hp.primeFactors, Finset.card_singleton] at hcard
    omega
  have hh := riesz_bounds_minFac L hn hcard
  have ha : 0 ≤ Real.log n / L := div_nonneg (Real.log_natCast_nonneg n) hL.le
  have hlo := mul_le_mul_of_nonneg_left hh.1 ha
  have hhi := mul_le_mul_of_nonneg_left hh.2 ha
  have hs : Squarefree n ∧ ¬ n.Prime := ⟨hn,hnp⟩
  simp only [SquarefreeVaughanLogSource.coefficient, if_pos hs, Complex.ofReal_re]
  have he : -Real.log n * VaughanLogAverage.riesz L n / L =
      -(Real.log n/L)*VaughanLogAverage.riesz L n := by ring
  rw [he]
  constructor <;> nlinarith only [hlo,hhi]

/-- The parity-specific allowance on the exact nonzero coefficient
support, using the mean only for its least-prime logarithm. -/
def signedAllowance (L : ℝ) (n b : ℕ) : ℝ :=
  if Squarefree n ∧ 2 ≤ n.primeFactors.card then
    (Real.log n / L) * (Real.log n / n.primeFactors.card) *
      (parityCapacity (n.primeFactors.card-2) b : ℝ)
  else 0

/-- Both signed capacities are nonnegative at the original positive length. -/
theorem signedAllowance_nonneg {L : ℝ} (hL : 0 < L) (n b : ℕ) :
    0 ≤ signedAllowance L n b := by
  unfold signedAllowance
  split_ifs
  · have := Real.log_natCast_nonneg n
    positivity
  · rfl

/-- Each side is no larger than the old absolute antichain allowance. -/
theorem signedAllowance_le_middle {L : ℝ} (hL : 0 < L) (n b : ℕ) :
    signedAllowance L n b ≤ middleLayerAllowance L n := by
  unfold signedAllowance middleLayerAllowance
  split_ifs
  · apply mul_le_mul_of_nonneg_left
      (by exact_mod_cast parityCapacity_le_middle (n.primeFactors.card-2) b)
    exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le)
      (div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg _))
  · rfl

/-- A signed arithmetic interval for every original coefficient, with
all support conditions discharged and no zero hypothesis. -/
theorem coefficient_bounds {L : ℝ} (hL : 0 < L) (n : ℕ) :
    -signedAllowance L n 0 ≤ (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤ signedAllowance L n 1 := by
  by_cases hc : SquarefreeVaughanLogSource.coefficient L n = 0
  · rw [hc,Complex.zero_re]
    exact ⟨neg_nonpos.mpr (signedAllowance_nonneg hL n 0), signedAllowance_nonneg hL n 1⟩
  · obtain ⟨hn,hcard⟩ := coefficient_ne_zero_support hc
    have hnp : ¬ n.Prime := by
      intro hp
      simp only [hp.primeFactors, Finset.card_singleton] at hcard
      omega
    have hh := riesz_bounds_mean L hn hcard
    have ha : 0 ≤ Real.log n / L := div_nonneg (Real.log_natCast_nonneg n) hL.le
    have hlo := mul_le_mul_of_nonneg_left hh.1 ha
    have hhi := mul_le_mul_of_nonneg_left hh.2 ha
    have hs : Squarefree n ∧ 2 ≤ n.primeFactors.card := ⟨hn,hcard⟩
    have hs' : Squarefree n ∧ ¬ n.Prime := ⟨hn,hnp⟩
    simp only [signedAllowance, if_pos hs, SquarefreeVaughanLogSource.coefficient,
      if_pos hs', Complex.ofReal_re]
    have he : -Real.log n * VaughanLogAverage.riesz L n / L =
        -(Real.log n/L)*VaughanLogAverage.riesz L n := by ring
    rw [he]
    constructor <;> nlinarith only [hlo,hhi]

/-- Four residual prime coordinates have six even subsets in their
largest even layer, but only four in their largest odd layer. -/
theorem parityCapacity_four : parityCapacity 4 0 = 6 ∧ parityCapacity 4 1 = 4 := by
  decide +kernel

/-- Six residual coordinates already have the reverse asymmetry. -/
theorem parityCapacity_six : parityCapacity 6 0 = 15 ∧ parityCapacity 6 1 = 20 := by
  decide +kernel

/-- Every literal squarefree six-prime coefficient has upper cost four
least-prime logarithms; the previous symmetric estimate charged six. -/
theorem coefficient_six_bounds {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hn : Squarefree n) (hcard : n.primeFactors.card = 6) :
    -(6*(Real.log n/L)*Real.log n.minFac) ≤
        (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤
        4*(Real.log n/L)*Real.log n.minFac := by
  have hh := coefficient_bounds_minFac hL hn (by omega)
  rw [hcard] at hh
  norm_num only [Nat.reduceSub,parityCapacity_four.1,parityCapacity_four.2,
    Nat.cast_ofNat] at hh
  constructor <;> nlinarith only [hh.1,hh.2]

/-- The lower charge keeps the original cosine, assigning its two signs
the appropriate distinct arithmetic capacities. -/
def lowerCost (L y : ℝ) (n : ℕ) : ℝ :=
  signedAllowance L n 0 * max (Real.cos (y*Real.log n)) 0 +
    signedAllowance L n 1 * max (-Real.cos (y*Real.log n)) 0

/-- The upper charge reverses the phase assignments, as required for
the independent multiple-zero ceiling rather than the simple-zero floor. -/
def upperCost (L y : ℝ) (n : ℕ) : ℝ :=
  signedAllowance L n 1 * max (Real.cos (y*Real.log n)) 0 +
    signedAllowance L n 0 * max (-Real.cos (y*Real.log n)) 0

/-- Both one-sided charges are nonnegative for all original phases. -/
theorem costs_nonneg {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ) :
    0 ≤ lowerCost L y n ∧ 0 ≤ upperCost L y n := by
  have h₀ := signedAllowance_nonneg hL n 0
  have h₁ := signedAllowance_nonneg hL n 1
  constructor <;> dsimp only [lowerCost,upperCost] <;> positivity

/-- Neither signed phase charge exceeds the previous absolute allowance.
Only this scalar comparison takes an absolute cosine; the carrier does not. -/
theorem costs_le_antichain {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ) :
    lowerCost L y n ≤ middleLayerAllowance L n * |Real.cos (y*Real.log n)| ∧
      upperCost L y n ≤ middleLayerAllowance L n * |Real.cos (y*Real.log n)| := by
  have h₀ := signedAllowance_le_middle hL n 0
  have h₁ := signedAllowance_le_middle hL n 1
  by_cases hcos : 0 ≤ Real.cos (y*Real.log n)
  · simp only [lowerCost,upperCost,max_eq_left hcos,
      max_eq_right (neg_nonpos.mpr hcos),mul_zero,add_zero,abs_of_nonneg hcos]
    exact ⟨mul_le_mul_of_nonneg_right h₀ hcos,mul_le_mul_of_nonneg_right h₁ hcos⟩
  · have hcos' := le_of_not_ge hcos
    simp only [lowerCost,upperCost,max_eq_right hcos',
      max_eq_left (neg_nonneg.mpr hcos'),mul_zero,zero_add,abs_of_nonpos hcos']
    exact ⟨mul_le_mul_of_nonneg_right h₁ (neg_nonneg.mpr hcos'),
      mul_le_mul_of_nonneg_right h₀ (neg_nonneg.mpr hcos')⟩

/-- The sign-sensitive bounds act on the actual coefficient and phase,
independently of every hypothetical zero. -/
theorem coefficient_phase_bounds {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ) :
    -lowerCost L y n ≤
        (SquarefreeVaughanLogSource.coefficient L n).re * Real.cos (y*Real.log n) ∧
      (SquarefreeVaughanLogSource.coefficient L n).re * Real.cos (y*Real.log n) ≤
        upperCost L y n := by
  have hh := coefficient_bounds hL n
  by_cases hcos : 0 ≤ Real.cos (y*Real.log n)
  · simp only [lowerCost,upperCost,max_eq_left hcos,
      max_eq_right (neg_nonpos.mpr hcos),mul_zero,add_zero]
    exact ⟨by simpa only [neg_mul] using mul_le_mul_of_nonneg_right hh.1 hcos,
      mul_le_mul_of_nonneg_right hh.2 hcos⟩
  · have hcos' := le_of_not_ge hcos
    simp only [lowerCost,upperCost,max_eq_right hcos',
      max_eq_left (neg_nonneg.mpr hcos'),mul_zero,zero_add]
    constructor
    · have hi := mul_le_mul_of_nonpos_right hh.2 hcos'
      nlinarith only [hi]
    · have hi := mul_le_mul_of_nonpos_right hh.1 hcos'
      nlinarith only [hi]

/-- The actual unassigned factorial atom inherits both signed bounds.
Its allocation, order, prime phase and all external masks remain unchanged. -/
theorem residual_atom_bounds (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (y : ℝ) (N n : ℕ) :
    -(weight A N n * lowerCost L y n) ≤
        (ZetaRieszJointAllocation.residualCoefficient A L N n *
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ∧
      (ZetaRieszJointAllocation.residualCoefficient A L N n *
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤
        weight A N n * upperCost L y n := by
  rw [re_residual_atom]
  have hh := coefficient_phase_bounds hL y n
  exact ⟨by simpa only [mul_neg] using
    mul_le_mul_of_nonneg_left hh.1 (weight_nonneg A N n),
    mul_le_mul_of_nonneg_left hh.2 (weight_nonneg A N n)⟩

/-- Retain every favorable observation, rather than spending it as part
of a nonnegative envelope. The lower and upper ledgers are alternatives. -/
theorem residual_atom_retained_bounds (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (y : ℝ) (N n : ℕ) :
    let v := (ZetaRieszJointAllocation.residualCoefficient A L N n *
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    max v 0 - weight A N n * lowerCost L y n ≤ v ∧
      v ≤ min v 0 + weight A N n * upperCost L y n := by
  dsimp only
  have hh := residual_atom_bounds A hL y N n
  have hlow := mul_nonneg (weight_nonneg A N n) (costs_nonneg hL y n).1
  have hupp := mul_nonneg (weight_nonneg A N n) (costs_nonneg hL y n).2
  by_cases hv : 0 ≤ (ZetaRieszJointAllocation.residualCoefficient A L N n *
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
  · rw [max_eq_left hv,min_eq_right hv]
    constructor <;> linarith only [hh.2,hlow]
  · have hv' := le_of_not_ge hv
    rw [max_eq_right hv',min_eq_left hv']
    constructor <;> linarith only [hh.1,hupp]

/-- The improved six-prime upper capacity is exactly two thirds of the
old symmetric allowance, including the case of an absent coefficient. -/
theorem six_allowance_ratio (L : ℝ) {n : ℕ} (hcard : n.primeFactors.card = 6) :
    signedAllowance L n 1 = (2/3 : ℝ)*middleLayerAllowance L n := by
  unfold signedAllowance middleLayerAllowance
  split_ifs
  · rw [hcard]
    norm_num [parityCapacity_four.2,Nat.choose]
    ring
  · simp

/-- On a negative original cosine, the six-prime floor charge falls by
one third, independently of every prime mask and zero hypothesis. -/
theorem six_lowerCost_saving {L y : ℝ} {n : ℕ} (hcard : n.primeFactors.card = 6)
    (hcos : Real.cos (y*Real.log n) ≤ 0) :
    lowerCost L y n = (2/3 : ℝ)*
      (middleLayerAllowance L n * |Real.cos (y*Real.log n)|) := by
  rw [lowerCost,max_eq_right hcos,max_eq_left (neg_nonneg.mpr hcos),
    mul_zero,zero_add,six_allowance_ratio L hcard,abs_of_nonpos hcos]
  ring

/-- On a positive original cosine, the same one-third saving belongs
to the multiple-zero ceiling charge, not a second independent supply. -/
theorem six_upperCost_saving {L y : ℝ} {n : ℕ} (hcard : n.primeFactors.card = 6)
    (hcos : 0 ≤ Real.cos (y*Real.log n)) :
    upperCost L y n = (2/3 : ℝ)*
      (middleLayerAllowance L n * |Real.cos (y*Real.log n)|) := by
  rw [upperCost,max_eq_left hcos,max_eq_right (neg_nonpos.mpr hcos),
    mul_zero,add_zero,six_allowance_ratio L hcard,abs_of_nonneg hcos]
  ring

/-- The other orientation first improves at eight primes: the even
capacity is three quarters of the old symmetric allowance. -/
theorem eight_allowance_ratio (L : ℝ) {n : ℕ} (hcard : n.primeFactors.card = 8) :
    signedAllowance L n 0 = (3/4 : ℝ)*middleLayerAllowance L n := by
  unfold signedAllowance middleLayerAllowance
  split_ifs
  · rw [hcard]
    norm_num [parityCapacity_six.1,Nat.choose]
    ring
  · simp

/-- Any chosen subset of the literal core receives both independent
signed comparisons, while all selected favorable observations and the
entire unselected complex sum remain. This does not assert a cofinal
bound for that signed complement or for the joint harmonic carrier. -/
theorem core_subset_bounds (u y : ℝ) (N K : ℕ) (D : Finset ℕ)
    (hD : D ⊆ ZetaRieszParityPacket.coreBand u N K) :
    let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
    let L := SquarefreeVaughanLogSource.length u N
    let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n *
      zetaPrimeLogKernel N (3/2+Complex.I*y) n
    (∑ n ∈ ZetaRieszParityPacket.coreBand u N K \ D, f n).re +
        (∑ n ∈ D, max (f n).re 0) - (∑ n ∈ D, weight A N n * lowerCost L y n) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re ∧
      (ZetaRieszParityPacket.coreResponse u y N K).re ≤
        (∑ n ∈ ZetaRieszParityPacket.coreBand u N K \ D, f n).re +
          (∑ n ∈ D, min (f n).re 0) + (∑ n ∈ D, weight A N n * upperCost L y n) := by
  dsimp only
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n *
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hh (n : ℕ) := residual_atom_retained_bounds A
    (SquarefreeVaughanLogSource.length_pos u N) y N n
  have hlo := Finset.sum_le_sum (fun n (_ : n ∈ D) => (hh n).1)
  have hhi := Finset.sum_le_sum (fun n (_ : n ∈ D) => (hh n).2)
  rw [Finset.sum_sub_distrib] at hlo
  rw [Finset.sum_add_distrib] at hhi
  have he := congrArg Complex.re (Finset.sum_sdiff (f := f) hD)
  simp only [Complex.add_re,Complex.re_sum] at he
  change (∑ n ∈ ZetaRieszParityPacket.coreBand u N K \ D, f n).re +
      (∑ n ∈ D, max (f n).re 0) - (∑ n ∈ D, weight A N n * lowerCost L y n) ≤
      (∑ n ∈ ZetaRieszParityPacket.coreBand u N K, f n).re ∧
    (∑ n ∈ ZetaRieszParityPacket.coreBand u N K, f n).re ≤
      (∑ n ∈ ZetaRieszParityPacket.coreBand u N K \ D, f n).re +
        (∑ n ∈ D, min (f n).re 0) + (∑ n ∈ D, weight A N n * upperCost L y n)
  simp only [Complex.re_sum]
  change (∑ n ∈ D, max (f n).re 0) -
    (∑ n ∈ D, weight A N n * lowerCost L y n) ≤ ∑ n ∈ D, (f n).re at hlo
  change (∑ n ∈ D, (f n).re) ≤ (∑ n ∈ D, min (f n).re 0) +
    (∑ n ∈ D, weight A N n * upperCost L y n) at hhi
  constructor <;> linarith only [he,hlo,hhi]

end
end RiemannGaussian.ZetaRieszSignedSperner
