/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFivePositiveHead
import RiemannGaussian.ZetaRieszBroadTripleBudget
import RiemannGaussian.ZetaRieszJointReflectionBounds

/-!
# A fixed positive-five population in the joint spending ledger

The four cofactor prime shares lie in `1/10..9/80`. Literal reciprocal
prime counts bound their complete positive-coefficient cost by `1/10000`
of the local radial scale. The last prime keeps its exact product endpoint.
This debit can be paid from the existing central period surplus, with
one signed complementary sum and without reusing any earlier credit.
-/

namespace RiemannGaussian.ZetaRieszPositiveFiveBudget
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszMacroPrimeWindows
open ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic ZetaRieszPrimeEndpoint

/-- A fixed, positive-coefficient five-prime sector of the original set.
All pre-existing masks and weights remain in `S` and in the summand. -/
def population (S : Finset ℕ) (L t h : ℝ) : Finset ℕ :=
  S.filter (fun n => Squarefree n ∧ n.primeFactors.card = 5 ∧
    t < Real.log n ∧ Real.log n ≤ t+h ∧
    0 < (SquarefreeVaughanLogSource.coefficient L n).re ∧
    ∀ p ∈ n.primeFactors.erase (largestPrime n),
      (1/10 : ℝ)*Real.log n ≤ Real.log p ∧ Real.log p ≤ (9/80 : ℝ)*Real.log n)

private def outerPrimes (t h : ℝ) : Finset ℕ :=
  logPrimes (t/10) (t/80+(9/80 : ℝ)*h)

private def representations (t h : ℝ) : Finset ((Fin 4 → ℕ) × ℕ) :=
  (Fintype.piFinset (fun _ : Fin 4 => outerPrimes t h)).biUnion
    (fun v => (logPrimes (t-Real.log (∏ i, v i : ℕ)) h).image (fun p => (v,p)))

private theorem population_covered (S : Finset ℕ) (L t h : ℝ) :
    population S L t h ⊆ (representations t h).image (fun v => (∏ i, v.1 i)*v.2) := by
  intro n hn
  obtain ⟨_,hs,hc,ht,hth,_,hshare⟩ := Finset.mem_filter.mp hn
  have hne : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  have hP : largestPrime n ∈ n.primeFactors := by
    rw [largestPrime,dif_pos hne]
    exact Finset.max'_mem _ _
  have hpP := Nat.prime_of_mem_primeFactors hP
  have hcard : (n.primeFactors.erase (largestPrime n)).card = 4 := by
    rw [Finset.card_erase_of_mem hP,hc]
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,he⟩ := Finset.card_eq_four.mp hcard
  let v : Fin 4 → ℕ := ![a,b,c,d]
  have hv (i : Fin 4) : v i ∈ n.primeFactors.erase (largestPrime n) := by
    fin_cases i <;> simp [v,he]
  have hprime (i : Fin 4) := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase (hv i))
  have hmem (i : Fin 4) : v i ∈ outerPrimes t h := by
    have hh := hshare _ (hv i)
    apply (mem_logPrimes_iff _ _ _).mpr
    refine ⟨hprime i,by linarith,by linarith⟩
  have hnprod : (∏ i, v i)*largestPrime n = n := by
    calc
      _ = (∏ p ∈ n.primeFactors.erase (largestPrime n), p)*largestPrime n := by
        rw [he]
        simp [v,Fin.prod_univ_four,hab,hac,had,hbc,hbd,hcd,mul_assoc]
      _ = ∏ p ∈ n.primeFactors, p := Finset.prod_erase_mul _ _ hP
      _ = n := Nat.prod_primeFactors_of_squarefree hs
  have hlog : Real.log n = Real.log (∏ i, v i : ℕ)+Real.log (largestPrime n) := by
    conv_lhs => rw [← hnprod,Nat.cast_mul]
    exact Real.log_mul
      (by exact_mod_cast Finset.prod_ne_zero_iff.mpr (fun i _ => (hprime i).ne_zero))
      (by exact_mod_cast hpP.ne_zero)
  apply Finset.mem_image.mpr
  refine ⟨(v,largestPrime n),?_,hnprod⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨v,Fintype.mem_piFinset.mpr hmem,Finset.mem_image.mpr ⟨largestPrime n,?_,rfl⟩⟩
  exact (mem_logPrimes_iff _ _ _).mpr ⟨hpP,by linarith,by linarith⟩

/-- Literal counting, with a cofactor-dependent final-prime interval.
No continuum density or signed prime approximation is assumed. -/
theorem eventually_reciprocal_mass {h : ℝ} (hh : 0 < h) (hhu : h ≤ 1/100000) :
    ∀ᶠ N : ℕ in atTop, ∀ (S : Finset ℕ) (L t : ℝ), (N : ℝ) ≤ t →
      (∑ n ∈ population S L t h, (n : ℝ)⁻¹) ≤ (1/2000 : ℝ)*h/t := by
  filter_upwards [eventually_macro_reciprocal_bounds
      (by norm_num : (0 : ℝ) < 1/10) (by norm_num : (0 : ℝ) < 1/80),
    ZetaRieszPhaseBudget.eventually_phase_window_mass hh hhu
      (by norm_num : (0 : ℝ) < 1/2),eventually_ge_atTop (1 : ℕ)]
    with N hmacro hlast hN S L t hNt
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : 1 ≤ t := hn.trans hNt
  have ht0 : 0 < t := by linarith
  let P := outerPrimes t h
  let V := Fintype.piFinset (fun _ : Fin 4 => P)
  have hmass : (∑ p ∈ P, (p : ℝ)⁻¹) ≤ 63/500 := by
    have hb := (hmacro (t/10) (t/80+(9/80 : ℝ)*h) (by linarith) (by linarith)).2
    apply hb.trans
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < t/10)).mpr
    linarith only [ht,hhu]
  have hlast' (v : Fin 4 → ℕ) (hv : v ∈ V) :
      (∑ p ∈ logPrimes (t-Real.log (∏ i, v i : ℕ)) h, (p : ℝ)⁻¹) ≤ (183/100 : ℝ)*h/t := by
    have hp (i : Fin 4) := logPrimes_bounds (Fintype.mem_piFinset.mp hv i)
    have he : Real.log (∏ i, v i : ℕ) = ∑ i, Real.log (v i) := by
      rw [Nat.cast_prod,Real.log_prod (fun i _ => by exact_mod_cast (hp i).1.ne_zero)]
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hp i).2.2)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
    have hgap : (549/1000 : ℝ)*t ≤ t-Real.log (∏ i, v i : ℕ) := by
      rw [he]
      linarith only [hsum,ht,hhu]
    have hg : 0 < t-Real.log (∏ i, v i : ℕ) := by nlinarith
    apply (hlast _ (by nlinarith : (1/2 : ℝ)*N ≤ t-Real.log (∏ i, v i : ℕ))).2.trans
    apply (div_le_div_iff₀ hg ht0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hgap hh.le]
  have hcover : (∑ n ∈ population S L t h, (n : ℝ)⁻¹) ≤
      ∑ v ∈ V, (∏ i, (v i : ℝ)⁻¹)*
        (∑ p ∈ logPrimes (t-Real.log (∏ i, v i : ℕ)) h, (p : ℝ)⁻¹) := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (population_covered S L t h)
      (fun n _ _ => inv_nonneg.mpr (Nat.cast_nonneg n))).trans
    apply (Finset.sum_image_le_of_nonneg (fun _ _ => by positivity)).trans
    rw [representations,Finset.sum_biUnion (by
      intro v _ w _ hvw
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨q,_,he⟩ := Finset.mem_image.mp hy
      exact hvw (congrArg Prod.fst he).symm)]
    apply Finset.sum_le_sum
    intro v hv
    apply (Finset.sum_image_le_of_nonneg (fun _ _ => by positivity)).trans
    simp only [Finset.mul_sum,Nat.cast_mul,Nat.cast_prod,mul_inv_rev,Finset.prod_inv_distrib]
    exact le_of_eq (by congr 1; ext p; ring)
  have hs := Finset.sum_le_sum (fun v hv =>
    mul_le_mul_of_nonneg_left (hlast' v hv) (by positivity : (0 : ℝ) ≤ ∏ i, (v i : ℝ)⁻¹))
  have he : (∑ v ∈ V, ∏ i, (v i : ℝ)⁻¹) = (∑ p ∈ P, (p : ℝ)⁻¹)^4 := by
    exact (Finset.sum_pow' P (fun p : ℕ => (p : ℝ)⁻¹) 4).symm
  rw [← Finset.sum_mul,he] at hs
  have hb := pow_le_pow_left₀ (by positivity) hmass 4
  have hc : (∑ p ∈ P, (p : ℝ)⁻¹)^4*((183/100 : ℝ)*h/t) ≤ (1/2000 : ℝ)*h/t := by
    have he := mul_le_mul_of_nonneg_right hb (by positivity : (0 : ℝ) ≤ (183/100 : ℝ)*h/t)
    have hcoef : (63/500 : ℝ)^4*((183/100 : ℝ)*h/t) ≤ (1/2000 : ℝ)*h/t := by
      have hd := mul_le_mul_of_nonneg_right
        (by norm_num : (63/500 : ℝ)^4*(183/100) ≤ 1/2000) (div_nonneg hh.le ht0.le)
      convert hd using 1 <;> first | rfl | ring
    exact he.trans hcoef
  exact hcover.trans (hs.trans hc)

private theorem amplitude_le_window {n : ℕ} (hn : n ≠ 0) {t h : ℝ}
    (ht : t ≤ Real.log n) (hth : Real.log n ≤ t+h) (N : ℕ) :
    amplitude N n ≤ (Real.exp (-t/2)*(t+h)^N/N.factorial)*(n : ℝ)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he : Real.exp (-(3/2 : ℝ)*Real.log n) =
      Real.exp (-Real.log n/2)*(n : ℝ)⁻¹ := by
    rw [show (n : ℝ)⁻¹ = Real.exp (-Real.log n) by rw [Real.exp_neg,Real.exp_log hnR],
      ← Real.exp_add]
    congr 1
    ring
  have hr : Real.exp (-Real.log n/2)*(Real.log n)^N/N.factorial ≤
      Real.exp (-t/2)*(t+h)^N/N.factorial := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul (Real.exp_le_exp.mpr (by linarith))
      (pow_le_pow_left₀ (Real.log_natCast_nonneg n) hth N) (by positivity) (Real.exp_nonneg _)
  have hm := mul_le_mul_of_nonneg_right hr (inv_nonneg.mpr hnR.le)
  unfold amplitude
  rw [he]
  convert hm using 1 <;> first | rfl | ring

/-- The actual positive coefficient costs less than one sixth of the
window centre. Every original allocation factor is still bounded by one. -/
theorem coefficient_le {S : Finset ℕ} {L t h : ℝ} (ht : 1 ≤ t) (hhu : h ≤ 1/100000)
    (hL : (69/100 : ℝ)*t ≤ L) (hLu : L ≤ (7/10 : ℝ)*t)
    {n : ℕ} (hn : n ∈ population S L t h) :
    ‖SquarefreeVaughanLogSource.coefficient L n‖ ≤ t/6 := by
  obtain ⟨_,_,hc,htn,hnt,hpos,hshare⟩ := Finset.mem_filter.mp hn
  have hne : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  have hP : largestPrime n ∈ n.primeFactors := by
    rw [largestPrime,dif_pos hne]
    exact Finset.max'_mem _ _
  have hcard : (n.primeFactors.erase (largestPrime n)).card = 4 := by
    rw [Finset.card_erase_of_mem hP,hc]
  obtain ⟨r,hr⟩ := Finset.card_pos.mp (show 0 < (n.primeFactors.erase (largestPrime n)).card by omega)
  have hL0 : 0 < L := by linarith
  have hb := ZetaRieszFivePositiveHead.positiveAllowance_le_cofactor_log hc hr hL0
  rw [ZetaRieszFivePrimeReserve.positiveAllowance_eq hc hL0 (by linarith) (by linarith),
    max_eq_right hpos.le] at hb
  have hratio : Real.log n/L ≤ 29/20 := (div_le_iff₀ hL0).mpr (by linarith)
  have hc' : (SquarefreeVaughanLogSource.coefficient L n).re ≤ t/6 :=
    (hb.trans (mul_le_mul_of_nonneg_right hratio (Real.log_natCast_nonneg r))).trans
      (by linarith [(hshare r hr).2])
  have he := Complex.re_add_im (SquarefreeVaughanLogSource.coefficient L n)
  rw [ZetaRieszCosineCarrier.coefficient_im_eq_zero,Complex.ofReal_zero,zero_mul,add_zero] at he
  rwa [← he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hpos.le]

/-- A quantitative bound for the literal positive-five cost. This is
uniform in the actual phase height and retains every mask through `S`. -/
theorem eventually_norm_mass {h : ℝ} (hh : 0 < h) (hhu : h ≤ 1/100000) :
    ∀ᶠ N : ℕ in atTop, ∀ (S A : Finset ℕ) (t L y : ℝ),
      (N : ℝ) ≤ t → (69/100 : ℝ)*t ≤ L → L ≤ (7/10 : ℝ)*t →
      (∑ n ∈ population S L t h, ‖residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
          (1/10000 : ℝ)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*h := by
  filter_upwards [eventually_reciprocal_mass hh hhu,eventually_ge_atTop (1 : ℕ)]
    with N hmass hN S A t L y hNt hL hLu
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht := hn.trans hNt
  have ht0 : 0 < t := by linarith
  let V := Real.exp (-t/2)*(t+h)^N/N.factorial
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hpoint (n : ℕ) (hn : n ∈ population S L t h) :
      ‖residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        (t/6*V)*(n : ℝ)⁻¹ := by
    obtain ⟨_,hs,_,htn,hnt,_,_⟩ := Finset.mem_filter.mp hn
    have hker : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ = amplitude N n := by
      rw [norm_zetaPrimeLogKernel]
      norm_num [zetaPrimeExpWeight,amplitude]
      ring
    rw [norm_mul,hker]
    have hb := mul_le_mul
      ((ZetaRieszJointCountFloor.norm_residual_le A L N n).trans (coefficient_le ht hhu hL hLu hn))
      (amplitude_le_window hs.ne_zero htn.le hnt N)
      (by unfold amplitude; positivity) (by positivity : 0 ≤ t/6)
    convert hb using 1 <;> first | rfl | ring
  have hs := Finset.sum_le_sum hpoint
  rw [← Finset.mul_sum] at hs
  have hb := mul_le_mul_of_nonneg_left (hmass S L t hNt) (by positivity : 0 ≤ t/6*V)
  have he : t/6*V*((1/2000 : ℝ)*h/t) = (1/12000 : ℝ)*V*h := by
    field_simp
    ring
  rw [he] at hb
  exact hs.trans (hb.trans (by nlinarith only [mul_nonneg hV hh.le]))

end
end RiemannGaussian.ZetaRieszPositiveFiveBudget
