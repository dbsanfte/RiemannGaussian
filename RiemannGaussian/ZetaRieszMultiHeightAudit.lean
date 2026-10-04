/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCoupledSquareEnergy
import RiemannGaussian.ZetaStechkinZeroFree

/-!
# A native-weight preflight for multi-height positivity

The completed ordinary-prime and von Mangoldt energy minus its FULL credit
is expanded without a norm. A three-height polynomial multiplies the
collected, signed pair coefficient; prime positivity does not give that
coefficient a sign. A positive Stechkin support factor preserves its sign.
Shifting EVERY auxiliary center cannot give a uniform pointwise comparison
against an unshifted target. These are limits of this positivity mechanism,
not a disproof of a complete-prime inequality using additional correlations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszMultiHeightAudit
open ZetaRieszCoupledSignedBound ZetaRieszPairPrimePowerPayment

/-- Positive prime measure and factorial amplitude, prior to its phase. -/
def amplitude (c : ℕ → ℝ) (u σ : ℝ) (k n : ℕ) : ℝ :=
  u^(k+1)*c n*log n^k/(k.factorial : ℝ)*exp (-σ*log n)

/-- The original phase is retained on every arithmetic atom. -/
def atom (c : ℕ → ℝ) (u σ y : ℝ) (k n : ℕ) : ℂ :=
  (amplitude c u σ k n : ℂ)*Complex.exp (-Complex.I*(y*log n : ℝ))

/-- Parameterization of the ordinary/von Mangoldt array, not a new carrier. -/
def array (c : ℕ → ℝ) (u σ y : ℝ) (k : ℕ) : ℂ := ∑' n, atom c u σ y k n

/-- The canonical target with its entire conjugated correlation credit. -/
def signedPrice (a : ℕ → ℂ) (N K : ℕ) (b : ℝ) : ℝ :=
  diagonalEnergy a N K b-correlationCredit a N K b

theorem signedPrice_eq (a : ℕ → ℂ) (N K : ℕ) (b : ℝ) :
    signedPrice a N K b=
      (∑ i∈Finset.range N,(symmetricWeight N K b i : ℂ)*a i*a (N-1-i)).re := by
  exact (joined_real_eq_energy_sub_credit a N K b).symm

/-- All original factorial orders and both prefixes have been collected.
This amplitude is SIGNED even when `c` is the positive prime measure. -/
def pairAmplitude (c : ℕ → ℝ) (u σ : ℝ) (N K : ℕ) (b : ℝ) (pq : ℕ × ℕ) : ℝ :=
  ∑ i∈Finset.range N,symmetricWeight N K b i*
    amplitude c u σ i pq.1*amplitude c u σ (N-1-i) pq.2

theorem amplitude_nonneg {c : ℕ → ℝ} (hc : ∀ n,0≤c n) {u : ℝ}
    (hu : 0≤u) (σ : ℝ) (k n : ℕ) : 0≤amplitude c u σ k n := by
  unfold amplitude
  exact mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hu _) (hc n))
    (pow_nonneg (Real.log_natCast_nonneg _) _)) (Nat.cast_nonneg _)) (exp_pos _).le

theorem atom_eq_kernel (c : ℕ → ℝ) (u σ y : ℝ) (k n : ℕ) :
    atom c u σ y k n=
      (u : ℂ)^(k+1)*(c n : ℂ)*zetaPrimeLogKernel k ((σ : ℂ)+Complex.I*y) n := by
  unfold atom amplitude zetaPrimeLogKernel zetaPrimeFeature
  rw [show -(((σ : ℂ)+Complex.I*y)*(log n : ℂ))=
    (-σ*log n : ℝ)+ -Complex.I*(y*log n : ℝ) by push_cast;ring,
    Complex.exp_add,←Complex.ofReal_exp]
  push_cast
  ring

/-- Ordinary-prime gating is explicit; no proper powers are discarded. -/
def ordinaryCoefficient (n : ℕ) : ℝ :=
  if n.Prime then ArithmeticFunction.vonMangoldt n else 0

theorem ordinary_array_eq (u y : ℝ) (k : ℕ) :
    array ordinaryCoefficient u (3/2) y k=ordinaryArray u y k := by
  unfold array ordinaryArray zetaOrdinaryPrimeLogMoment
  rw [←tsum_mul_left]
  apply tsum_congr
  intro n
  rw [atom_eq_kernel]
  by_cases hn : n.Prime <;> simp [ordinaryCoefficient,hn,mul_assoc]

theorem mangoldt_array_eq (u y : ℝ) (k : ℕ) :
    array ArithmeticFunction.vonMangoldt u (3/2) y k=mangoldtArray u y k := by
  unfold array mangoldtArray
  rw [←(hasSum_zetaPrimeLogMoment (by norm_num : (1 : ℝ)<
    ((3/2 : ℂ)+Complex.I*y).re) k).tsum_eq,←tsum_mul_left]
  apply tsum_congr
  intro n
  rw [atom_eq_kernel]
  simp only [mul_assoc,zetaPrimeLogKernel,Complex.ofReal_div,Complex.ofReal_ofNat]

theorem summable_ordinary_atoms (u σ y : ℝ) (hσ : 1<σ) (k : ℕ) :
    Summable (atom ordinaryCoefficient u σ y k) := by
  have h := (summable_zetaOrdinaryPrimeLogMoment k
    (by simpa using hσ : 1<((σ : ℂ)+Complex.I*y).re)).mul_left ((u : ℂ)^(k+1))
  apply h.congr
  intro n
  rw [atom_eq_kernel]
  by_cases hn : n.Prime <;> simp [ordinaryCoefficient,hn,mul_assoc]

theorem summable_mangoldt_atoms (u σ y : ℝ) (hσ : 1<σ) (k : ℕ) :
    Summable (atom ArithmeticFunction.vonMangoldt u σ y k) := by
  have h := (hasSum_zetaPrimeLogMoment
    (by simpa using hσ : 1<((σ : ℂ)+Complex.I*y).re) k).summable.mul_left
    ((u : ℂ)^(k+1))
  apply h.congr
  intro n
  rw [atom_eq_kernel]
  simp only [mul_assoc,zetaPrimeLogKernel]

private theorem atom_product (c : ℕ → ℝ) (u σ y : ℝ) (i j p q : ℕ) :
    atom c u σ y i p*atom c u σ y j q=
      (amplitude c u σ i p*amplitude c u σ j q : ℝ)*
        Complex.exp (-Complex.I*(y*(log p+log q) : ℝ)) := by
  have he : Complex.exp (-Complex.I*(y*log p : ℝ))*
      Complex.exp (-Complex.I*(y*log q : ℝ))=
      Complex.exp (-Complex.I*(y*(log p+log q) : ℝ)) := by
    rw [←Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = ((amplitude c u σ i p : ℂ)*(amplitude c u σ j q : ℂ))*
        (Complex.exp (-Complex.I*(y*log p : ℝ))*
          Complex.exp (-Complex.I*(y*log q : ℝ))) := by unfold atom;ring
    _ = _ := by rw [he];simp only [Complex.ofReal_mul]

private theorem pair_sum_eq (c : ℕ → ℝ) (u σ y : ℝ) (N K : ℕ) (b : ℝ)
    (pq : ℕ × ℕ) :
    (∑ i∈Finset.range N,(symmetricWeight N K b i : ℂ)*
      atom c u σ y i pq.1*atom c u σ y (N-1-i) pq.2)=
      (pairAmplitude c u σ N K b pq : ℂ)*
        Complex.exp (-Complex.I*(y*(log pq.1+log pq.2) : ℝ)) := by
  unfold pairAmplitude
  simp only [Complex.ofReal_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc,atom_product]
  simp only [Complex.ofReal_mul]
  ring

private theorem phase_re (a t : ℝ) :
    ((a : ℂ)*Complex.exp (-Complex.I*(t : ℂ))).re=a*cos t := by
  rw [Complex.re_ofReal_mul,Complex.exp_re]
  simp

private theorem pair_complex_summable {c : ℕ → ℝ} {u σ y : ℝ} {N K : ℕ} {b : ℝ}
    (hs : ∀ k,Summable (atom c u σ y k)) :
    Summable (fun pq : ℕ × ℕ => ∑ i∈Finset.range N,(symmetricWeight N K b i : ℂ)*
      atom c u σ y i pq.1*atom c u σ y (N-1-i) pq.2) := by
  apply summable_sum
  intro i _
  apply ((summable_mul_of_summable_norm (hs i).norm (hs (N-1-i)).norm).mul_left
    (symmetricWeight N K b i : ℂ)).congr
  intro pq
  simp only [mul_assoc]

theorem pair_phase_summable {c : ℕ → ℝ} {u σ y : ℝ} {N K : ℕ} {b : ℝ}
    (hs : ∀ k,Summable (atom c u σ y k)) :
    Summable (fun pq : ℕ × ℕ => pairAmplitude c u σ N K b pq*
      cos (y*(log pq.1+log pq.2))) := by
  apply (Complex.reCLM.summable (pair_complex_summable (N := N) (K := K) (b := b) hs)).congr
  intro pq
  change (∑ i∈Finset.range N,(symmetricWeight N K b i : ℂ)*
    atom c u σ y i pq.1*atom c u σ y (N-1-i) pq.2).re=_
  rw [pair_sum_eq,phase_re]

/-- A horizontal shift damps the same native amplitude; it does not change
any factorial, prefix, prime or diagonal index. -/
theorem amplitude_shift (c : ℕ → ℝ) (u σ h : ℝ) (k n : ℕ) :
    amplitude c u (σ+h) k n=exp (-h*log n)*amplitude c u σ k n := by
  unfold amplitude
  rw [show -(σ+h)*log n=-h*log n+ -σ*log n by ring,exp_add]
  ring

theorem pairAmplitude_shift (c : ℕ → ℝ) (u σ h : ℝ) (N K : ℕ) (b : ℝ)
    (pq : ℕ × ℕ) :
    pairAmplitude c u (σ+h) N K b pq=
      exp (-h*(log pq.1+log pq.2))*pairAmplitude c u σ N K b pq := by
  unfold pairAmplitude
  simp_rw [amplitude_shift]
  rw [Finset.mul_sum,show -h*(log pq.1+log pq.2)=
    -h*log pq.1+ -h*log pq.2 by ring,exp_add]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The full `D-Q`, not its energy alone, equals the actual signed pair
series. Both ordered incidences, every diagonal and low order remain. -/
theorem signedPrice_eq_pair_phase {c : ℕ → ℝ} {u σ y : ℝ} (N K : ℕ) (b : ℝ)
    (hs : ∀ k,Summable (atom c u σ y k)) :
    signedPrice (array c u σ y) N K b=
      ∑' pq : ℕ × ℕ,pairAmplitude c u σ N K b pq*cos (y*(log pq.1+log pq.2)) := by
  rw [signedPrice_eq]
  have hex : (∑ i∈Finset.range N,(symmetricWeight N K b i : ℂ)*
      array c u σ y i*array c u σ y (N-1-i))=
      ∑' pq : ℕ × ℕ,∑ i∈Finset.range N,(symmetricWeight N K b i : ℂ)*
        atom c u σ y i pq.1*atom c u σ y (N-1-i) pq.2 := by
    simp_rw [mul_assoc (symmetricWeight N K b _ : ℂ)]
    rw [Summable.tsum_finsetSum (s := Finset.range N) (fun i _ =>
      (summable_mul_of_summable_norm (hs i).norm (hs (N-1-i)).norm).mul_left
        (symmetricWeight N K b i : ℂ))]
    apply Finset.sum_congr rfl
    intro i _
    rw [array,array,tsum_mul_tsum_of_summable_norm (hs i).norm (hs (N-1-i)).norm,
      ←tsum_mul_left]
  rw [hex,Complex.re_tsum (pair_complex_summable hs)]
  apply tsum_congr
  intro pq
  rw [pair_sum_eq,phase_re]

/-- Prime positivity has been retained, but the collected coefficient
inside this exact three-height square remains signed. -/
theorem three_height_eq_signed_square {c : ℕ → ℝ} {u σ y : ℝ} (N K : ℕ) (b : ℝ)
    (hs : ∀ t k,Summable (atom c u σ t k)) :
    3*signedPrice (array c u σ 0) N K b-
      4*signedPrice (array c u σ y) N K b+
      signedPrice (array c u σ (2*y)) N K b=
      ∑' pq : ℕ × ℕ,2*pairAmplitude c u σ N K b pq*
        (1-cos (y*(log pq.1+log pq.2)))^2 := by
  rw [signedPrice_eq_pair_phase N K b (hs 0),
    signedPrice_eq_pair_phase N K b (hs y),signedPrice_eq_pair_phase N K b (hs (2*y))]
  have h0 := pair_phase_summable (N := N) (K := K) (b := b) (hs 0)
  have h1 := pair_phase_summable (N := N) (K := K) (b := b) (hs y)
  have h2 := pair_phase_summable (N := N) (K := K) (b := b) (hs (2*y))
  rw [←tsum_mul_left,←tsum_mul_left,←(h0.mul_left 3).tsum_sub (h1.mul_left 4),
    ←((h0.mul_left 3).sub (h1.mul_left 4)).tsum_add h2]
  apply tsum_congr
  intro pq
  rw [show 2*y*(log pq.1+log pq.2)=2*(y*(log pq.1+log pq.2)) by ring,cos_two_mul]
  simp only [zero_mul,cos_zero,mul_one]
  ring

/-- The initially proposed `3+4*cos+cos(2*)` comparison, on the full signed
quadratic rather than on a positive surrogate. -/
theorem three_height_plus_eq_signed_square {c : ℕ → ℝ} {u σ y : ℝ} (N K : ℕ) (b : ℝ)
    (hs : ∀ t k,Summable (atom c u σ t k)) :
    3*signedPrice (array c u σ 0) N K b+
      4*signedPrice (array c u σ y) N K b+
      signedPrice (array c u σ (2*y)) N K b=
      ∑' pq : ℕ × ℕ,2*pairAmplitude c u σ N K b pq*
        (1+cos (y*(log pq.1+log pq.2)))^2 := by
  rw [signedPrice_eq_pair_phase N K b (hs 0),
    signedPrice_eq_pair_phase N K b (hs y),signedPrice_eq_pair_phase N K b (hs (2*y))]
  have h0 := pair_phase_summable (N := N) (K := K) (b := b) (hs 0)
  have h1 := pair_phase_summable (N := N) (K := K) (b := b) (hs y)
  have h2 := pair_phase_summable (N := N) (K := K) (b := b) (hs (2*y))
  rw [←tsum_mul_left,←tsum_mul_left,←(h0.mul_left 3).tsum_add (h1.mul_left 4),
    ←((h0.mul_left 3).add (h1.mul_left 4)).tsum_add h2]
  apply tsum_congr
  intro pq
  rw [show 2*y*(log pq.1+log pq.2)=2*(y*(log pq.1+log pq.2)) by ring,cos_two_mul]
  simp only [zero_mul,cos_zero,mul_one]
  ring

/-- This is the unweakened ordinary-prime trigonometric comparison.
The right side has NOT been asserted nonnegative. -/
theorem ordinary_three_height_eq_signed_square (u y : ℝ) (N K : ℕ) (b : ℝ) :
    3*signedPrice (ordinaryArray u 0) N K b-
      4*signedPrice (ordinaryArray u y) N K b+
      signedPrice (ordinaryArray u (2*y)) N K b=
      ∑' pq : ℕ × ℕ,2*pairAmplitude ordinaryCoefficient u (3/2) N K b pq*
        (1-cos (y*(log pq.1+log pq.2)))^2 := by
  simpa only [show array ordinaryCoefficient u (3/2) 0=ordinaryArray u 0 from
      funext (ordinary_array_eq u 0),show array ordinaryCoefficient u (3/2) y=ordinaryArray u y from
      funext (ordinary_array_eq u y),show array ordinaryCoefficient u (3/2) (2*y)=ordinaryArray u (2*y) from
      funext (ordinary_array_eq u (2*y))] using three_height_eq_signed_square (y := y) N K b
    (fun t k => summable_ordinary_atoms u (3/2) t (by norm_num) k)

/-- Proper prime powers give the SAME signed coefficient obstruction. -/
theorem mangoldt_three_height_eq_signed_square (u y : ℝ) (N K : ℕ) (b : ℝ) :
    3*signedPrice (mangoldtArray u 0) N K b-
      4*signedPrice (mangoldtArray u y) N K b+
      signedPrice (mangoldtArray u (2*y)) N K b=
      ∑' pq : ℕ × ℕ,2*pairAmplitude ArithmeticFunction.vonMangoldt u (3/2) N K b pq*
        (1-cos (y*(log pq.1+log pq.2)))^2 := by
  simpa only [show array ArithmeticFunction.vonMangoldt u (3/2) 0=mangoldtArray u 0 from
      funext (mangoldt_array_eq u 0),show array ArithmeticFunction.vonMangoldt u (3/2) y=mangoldtArray u y from
      funext (mangoldt_array_eq u y),show array ArithmeticFunction.vonMangoldt u (3/2) (2*y)=mangoldtArray u (2*y) from
      funext (mangoldt_array_eq u (2*y))] using three_height_eq_signed_square (y := y) N K b
    (fun t k => summable_mangoldt_atoms u (3/2) t (by norm_num) k)

/-- A nontrivial nonnegative polynomial cannot turn a negative collected
coefficient into a positive arithmetic contribution. -/
theorem negative_weight_polynomial {w : ℝ} (hw : w<0) {P : ℝ → ℝ} {t : ℝ}
    (hP : 0<P t) : w*P t<0 := mul_neg_of_neg_of_pos hw hP

theorem minus_square_pointwise_iff (w : ℝ) :
    (∀ t : ℝ,0≤w*(3-4*cos t+cos (2*t))) ↔ 0≤w := by
  constructor
  · intro h
    have hh := h Real.pi
    rw [Real.cos_pi,show 2*Real.pi=Real.pi+Real.pi by ring,Real.cos_add,
      Real.cos_pi,Real.sin_pi] at hh
    nlinarith
  · intro hw t
    rw [cos_two_mul]
    have h := mul_nonneg hw (sq_nonneg (1-cos t))
    nlinarith

/-- A Stechkin support subtraction with positive support factor does not
repair a negative native quadratic coefficient. -/
theorem stechkin_factor_preserves_negative {w κ h T : ℝ} (hw : w<0)
    (hκ : κ*exp (-h*T)<1) : w*(1-κ*exp (-h*T))<0 :=
  mul_neg_of_neg_of_pos hw (by linarith)

/-- An abstract coherent array supplies equality to the minus comparison,
so a height-blind algebraic identity earns no strict source saving. -/
theorem coherent_three_height_equality (a : ℕ → ℂ) (N K : ℕ) (b : ℝ) :
    3*signedPrice a N K b-4*signedPrice a N K b+signedPrice a N K b=0 := by ring

/-- Source preflight for the height-zero pole: its common native total
order gives `(2*u)^(N+1)`, not an auxiliary radius saving. -/
theorem geometric_array_signedPrice (q : ℝ) (N K : ℕ) (b : ℝ) :
    signedPrice (fun i => (q : ℂ)^(i+1)) N K b=
      q^(N+1)*∑ i∈Finset.range N,symmetricWeight N K b i := by
  rw [signedPrice_eq]
  have he : (∑ i∈Finset.range N,(symmetricWeight N K b i : ℂ)*
      (q : ℂ)^(i+1)*(q : ℂ)^(N-1-i+1))=
      (q : ℂ)^(N+1)*∑ i∈Finset.range N,(symmetricWeight N K b i : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hiN := Finset.mem_range.mp hi
    rw [mul_assoc,←pow_add,show i+1+(N-1-i+1)=N+1 by omega]
    ring
  rw [he,←Complex.ofReal_sum,←Complex.ofReal_pow,←Complex.ofReal_mul,Complex.ofReal_re]

/-- Eliminating the unshifted height-zero coefficient makes a nonnegative
degree-two cosine comparison trivial. It is not a free pole deletion. -/
theorem degree_two_zero_constant_trivial {a₁ a₂ : ℝ}
    (hp : ∀ t : ℝ,0≤a₁*cos t+a₂*cos (2*t)) : a₁=0 ∧ a₂=0 := by
  have h0 := hp 0
  have hπ := hp Real.pi
  have hh := hp (Real.pi/2)
  simp only [mul_zero,cos_zero,mul_one] at h0
  rw [Real.cos_pi,show 2*Real.pi=Real.pi+Real.pi by ring,
    Real.cos_add,Real.cos_pi,Real.sin_pi] at hπ
  rw [Real.cos_pi_div_two,show 2*(Real.pi/2)=Real.pi by ring,Real.cos_pi] at hh
  constructor <;> nlinarith

/-- Necessary phase-zero cost when all auxiliary terms are shifted by at
least `delta`. This holds for ANY degree and coefficients, before a norm. -/
theorem shifted_auxiliary_necessary_cost {ι : Type*} (S : Finset ι)
    (c h : ι → ℝ) {δ T target : ℝ} (hT : 0≤T)
    (hh : ∀ i∈S,δ≤h i)
    (hcompare : target≤∑ i∈S,c i*exp (-h i*T)) :
    target*exp (δ*T)≤∑ i∈S,|c i| := by
  have hbound : (∑ i∈S,c i*exp (-h i*T))≤
      (∑ i∈S,|c i|)*exp (-δ*T) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    exact (mul_le_mul_of_nonneg_right (le_abs_self _) (exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith [hh i hi])) (abs_nonneg _))
  have hc := mul_le_mul_of_nonneg_right (hcompare.trans hbound) (exp_pos (δ*T)).le
  simpa only [mul_assoc,←exp_add,neg_mul,neg_add_cancel,exp_zero,mul_one] using hc

/-- Fixed coefficients at only safer centers cannot dominate a positive
unshifted target for every total logarithm. In particular, increasing the
trigonometric degree does not fix this pointwise obstruction. -/
theorem no_all_safe_pointwise_comparison {ι : Type*} (S : Finset ι)
    (c h : ι → ℝ) {δ target : ℝ} (hδ : 0<δ) (htarget : 0<target)
    (hh : ∀ i∈S,δ≤h i) :
    ¬∀ T : ℝ,0≤T → target≤∑ i∈S,c i*exp (-h i*T) := by
  intro hall
  let M := ∑ i∈S,|c i|
  obtain ⟨T,hT0⟩ := exists_gt (max 0 ((M/target-1)/δ))
  have hTpos : 0<T := (le_max_left _ _).trans_lt hT0
  have hTL : (M/target-1)/δ<T := (le_max_right _ _).trans_lt hT0
  have hlin : M<target*(1+δ*T) := by
    have h := (div_lt_iff₀ hδ).mp hTL
    have hmul := (div_lt_iff₀ htarget).mp (by linarith only [h] : M/target<1+δ*T)
    nlinarith only [hmul]
  have he := Real.add_one_le_exp (δ*T)
  have hb := shifted_auxiliary_necessary_cost S c h hTpos.le hh (hall T hTpos.le)
  have hm := mul_le_mul_of_nonneg_left he htarget.le
  dsimp only [M] at hlin
  linarith

end RiemannGaussian.ZetaRieszMultiHeightAudit
