/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszGlobalCurvature
import RiemannGaussian.ZetaRieszFixedCountPeriod
/-!
# Count-free affine bounds for literal signed prime periods

The cutoff-crossing estimate applies directly to residualCoefficient with the
original allocation, factorial kernel, both reflected cutoffs and signed phase.
It covers arbitrary squarefree cofactor counts and masked prime sets, including
clipped periods. The signed constant and first moments remain on the right.
Unique largest-prime ownership identifies the inequality with an actual integer
population, and a second theorem aggregates any finite set of radial periods.
No source-scale bound for those moments or their total weights is asserted.
-/

noncomputable section
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszGlobalPrimePeriod
open ZetaRieszGlobalCurvature ZetaRieszFixedCountPeriod

/-- The literal prime-fibre weight retains parity, allocation, the factorial
kernel and its full signed phase. It has no fixed count or share restriction. -/
def signedPrimeWeight (A : Finset ℕ) (L : ℝ) (N : ℕ) (y : ℝ) (a p : ℕ) : ℝ :=
  (-1 : ℝ)^(a.primeFactors.card+1)*(-(1/L))*
    (1-ZetaRieszJointAllocation.boundedShare A N (p*a))*
    (Real.exp (-(Real.log p+Real.log a)/2)*(Real.log p+Real.log a)^(N+1)/N.factorial)*
    (p : ℝ)⁻¹*Real.cos (y*(Real.log p+Real.log a))

/-- The two-cutoff formula applies to every squarefree composite cofactor,
including counts and geometries outside the earlier fixed-count selections. -/
theorem coefficient_eq_response {a p : ℕ} (hs : Squarefree a)
    (hc : 2 ≤ a.primeFactors.card) (hp : p.Prime) (hpd : ¬p ∣ a) (L : ℝ) :
    SquarefreeVaughanLogSource.coefficient L (p*a) =
      (((-1 : ℝ)^(a.primeFactors.card+1)*(-(Real.log (p*a : ℕ)/L)*
        response L (Real.log (p*a : ℕ)) a) : ℝ) : ℂ) := by
  have hsq := Nat.squarefree_mul_iff.mpr ⟨hp.coprime_iff_not_dvd.mpr hpd,hp.squarefree,hs⟩
  have hpm : p ∉ a.primeFactors := fun h => hpd (Nat.dvd_of_mem_primeFactors h)
  have hcnt : (p*a).primeFactors.card = a.primeFactors.card+1 := by
    rw [Nat.primeFactors_mul hp.ne_zero hs.ne_zero,hp.primeFactors,
      Finset.singleton_union,Finset.card_insert_of_notMem hpm]
  have hn1 : p*a ≠ 1 := by intro h; simp [h] at hcnt
  have hnp : ¬(p*a).Prime := by
    intro h
    have he : (p*a).primeFactors.card = 1 := by rw [h.primeFactors]; simp
    omega
  have hl : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hs.ne_zero)]
  have href := VaughanLogAverage.riesz_reflection (Real.log (p*a : ℕ)-L) hsq hn1 hnp
  rw [sub_sub_cancel,ZetaRieszReflectedLinear.moebius_eq_primeCount hsq,hcnt,
    Int.cast_pow,Int.cast_neg,Int.cast_one,
    ZetaSquarefreeRieszWindows.riesz_prime_mul (Real.log (p*a : ℕ)-L) hp hpd] at href
  rw [show Real.log (p*a : ℕ)-L-Real.log p = Real.log a-L by rw [hl]; ring] at href
  rw [SquarefreeVaughanLogSource.coefficient,if_pos ⟨hsq,hnp⟩,href]
  congr 1
  dsimp only [response]
  ring

/-- Pointwise bridge to the existing literal residual coefficient.
Both Riesz cutoffs and the original allocation survive exactly. -/
theorem re_residual_atom {a p : ℕ} (hs : Squarefree a)
    (hc : 2 ≤ a.primeFactors.card) (hp : p.Prime) (hpd : ¬p ∣ a)
    (A : Finset ℕ) (L y : ℝ) (N : ℕ) :
    (ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re =
      signedPrimeWeight A L N y a p * response L (Real.log p+Real.log a) a/a := by
  have hlog : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hs.ne_zero)]
  have hex : Real.exp (-(3/2 : ℝ)*Real.log (p*a : ℕ)) =
      Real.exp (-Real.log (p*a : ℕ)/2)*(p : ℝ)⁻¹*(a : ℝ)⁻¹ := by
    rw [show -(3/2 : ℝ)*Real.log (p*a : ℕ) =
      -Real.log (p*a : ℕ)/2-Real.log (p*a : ℕ) by ring,
      Real.exp_sub,Real.exp_log (by exact_mod_cast Nat.mul_pos hp.pos (Nat.pos_of_ne_zero hs.ne_zero)),
      Nat.cast_mul]
    ring
  have he : (SquarefreeVaughanLogSource.coefficient L (p*a)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re =
      (-1 : ℝ)^(a.primeFactors.card+1)*(-(response L (Real.log p+Real.log a) a/L/a)*
        ((Real.exp (-(Real.log p+Real.log a)/2)*(Real.log p+Real.log a)^(N+1)/N.factorial)*
          (p : ℝ)⁻¹*Real.cos (y*(Real.log p+Real.log a)))) := by
    rw [← ZetaRieszJointAllocation.filter_one_eq,ZetaRieszCosineCarrier.re_coefficient_filter_one,
      coefficient_eq_response hs hc hp hpd,Complex.ofReal_re,hex,hlog,pow_succ]
    ring
  rw [ZetaRieszJointAllocation.residualCoefficient,mul_assoc,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [he]
  dsimp [signedPrimeWeight]
  ring


/-- A count-free signed bound for the actual finite prime sum. The only
unpaid terms on the right are its retained constant and first signed moments;
the cutoff-crossing cost is explicit and independent of the number of factors. -/
theorem literal_affine_error_le (A S : Finset ℕ) (X N : ℕ) (P : ℕ → Finset ℕ)
    (L v y : ℝ) {h W : ℝ} (hh : 0 ≤ h) (hW : 0 ≤ W)
    (hS : S ⊆ Finset.Icc 1 X)
    (hSF : ∀ a ∈ S, Squarefree a ∧ 2 ≤ a.primeFactors.card)
    (hP : ∀ a ∈ S, ∀ p ∈ P a, p.Prime ∧ ¬p ∣ a)
    (hx : ∀ a ∈ S, ∀ p ∈ P a, |Real.log p+Real.log a-v| ≤ h)
    (hg : ∀ a ∈ S, (∑ p ∈ P a, |signedPrimeWeight A L N y a p|) ≤ W) :
    let g := signedPrimeWeight A L N y
    let M := ∑ a ∈ S,
      (response L v a*(∑ p ∈ P a, g a p)+cutoffSlope (v-L) a*
        (∑ p ∈ P a, g a p*(Real.log p+Real.log a-v)))/a
    |(∑ a ∈ S, ∑ p ∈ P a, ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re-M| ≤
      W*((1+Real.log X)*h*(Real.exp (2*h)-1+Real.exp (h-(v-L)))) := by
  let g := signedPrimeWeight A L N y
  have hi a (ha : a ∈ S) :
      (∑ p ∈ P a, ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re =
      (∑ p ∈ P a, g a p*response L (Real.log p+Real.log a) a)/a := by
    rw [Complex.re_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    exact re_residual_atom (hSF a ha).1 (hSF a ha).2 (hP a ha p hp).1
      (hP a ha p hp).2 A L y N
  have he : (∑ a ∈ S, ∑ p ∈ P a, ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re-
      (∑ a ∈ S, (response L v a*(∑ p ∈ P a, g a p)+cutoffSlope (v-L) a*
        (∑ p ∈ P a, g a p*(Real.log p+Real.log a-v)))/a) =
      ∑ a ∈ S, ((∑ p ∈ P a, g a p*VaughanLogAverage.riesz
        (v-L+(Real.log p+Real.log a-v)) a)-VaughanLogAverage.riesz (v-L) a*
        (∑ p ∈ P a, g a p)-cutoffSlope (v-L) a*
        (∑ p ∈ P a, g a p*(Real.log p+Real.log a-v)))/a := by
    rw [Complex.re_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [hi a ha,← sub_div]
    congr 1
    simp only [response,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [show v-L+(Real.log p+Real.log a-v) = Real.log p+Real.log a-L by ring]
    ring
  dsimp only
  change |_-_| ≤ _
  rw [he]
  exact joint_affine_error_le S X P (fun a p => Real.log p+Real.log a-v) g hh hW
    (v-L) hS hx hg

/-- The same global cost improves both sides of the literal signed estimate;
no phase-selected positive credit is appended to the completed sum. -/
theorem literal_affine_bounds (A S : Finset ℕ) (X N : ℕ) (P : ℕ → Finset ℕ)
    (L v y : ℝ) {h W : ℝ} (hh : 0 ≤ h) (hW : 0 ≤ W)
    (hS : S ⊆ Finset.Icc 1 X)
    (hSF : ∀ a ∈ S, Squarefree a ∧ 2 ≤ a.primeFactors.card)
    (hP : ∀ a ∈ S, ∀ p ∈ P a, p.Prime ∧ ¬p ∣ a)
    (hx : ∀ a ∈ S, ∀ p ∈ P a, |Real.log p+Real.log a-v| ≤ h)
    (hg : ∀ a ∈ S, (∑ p ∈ P a, |signedPrimeWeight A L N y a p|) ≤ W) :
    let g := signedPrimeWeight A L N y
    let M := ∑ a ∈ S,
      (response L v a*(∑ p ∈ P a, g a p)+cutoffSlope (v-L) a*
        (∑ p ∈ P a, g a p*(Real.log p+Real.log a-v)))/a
    let E := W*((1+Real.log X)*h*(Real.exp (2*h)-1+Real.exp (h-(v-L))))
    M-E ≤ (∑ a ∈ S, ∑ p ∈ P a, ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re ∧
      (∑ a ∈ S, ∑ p ∈ P a, ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re ≤ M+E := by
  have h := abs_le.mp (literal_affine_error_le A S X N P L v y hh hW hS hSF hP hx hg)
  dsimp only
  constructor <;> linarith only [h.1,h.2]


/-- The count-free crossing cost also aggregates over an arbitrary finite
collection of radial periods. Only the sum of their literal weight budgets
appears; no factor counting share cells or prime-count classes is introduced. -/
theorem radial_affine_error_le {ι : Type*} (B : Finset ι) (A : Finset ℕ)
    (S : ι → Finset ℕ) (X N : ℕ) (P : ι → ℕ → Finset ℕ)
    (L y : ℝ) (v W : ι → ℝ) {h D₀ : ℝ} (hh : 0 ≤ h)
    (hW : ∀ j ∈ B, 0 ≤ W j) (hD : ∀ j ∈ B, D₀ ≤ v j-L)
    (hS : ∀ j ∈ B, S j ⊆ Finset.Icc 1 X)
    (hSF : ∀ j ∈ B, ∀ a ∈ S j, Squarefree a ∧ 2 ≤ a.primeFactors.card)
    (hP : ∀ j ∈ B, ∀ a ∈ S j, ∀ p ∈ P j a, p.Prime ∧ ¬p ∣ a)
    (hx : ∀ j ∈ B, ∀ a ∈ S j, ∀ p ∈ P j a, |Real.log p+Real.log a-v j| ≤ h)
    (hg : ∀ j ∈ B, ∀ a ∈ S j,
      (∑ p ∈ P j a, |signedPrimeWeight A L N y a p|) ≤ W j) :
    let g := signedPrimeWeight A L N y
    let M := fun j => ∑ a ∈ S j,
      (response L (v j) a*(∑ p ∈ P j a, g a p)+cutoffSlope (v j-L) a*
        (∑ p ∈ P j a, g a p*(Real.log p+Real.log a-v j)))/a
    |(∑ j ∈ B, ∑ a ∈ S j, ∑ p ∈ P j a,
      ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re-(∑ j ∈ B, M j)| ≤
      (∑ j ∈ B, W j)*((1+Real.log X)*h*(Real.exp (2*h)-1+Real.exp (h-D₀))) := by
  dsimp only
  rw [Complex.re_sum,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j ∈ B, W j*((1+Real.log X)*h*(Real.exp (2*h)-1+Real.exp (h-(v j-L)))) :=
      Finset.sum_le_sum (fun j hj => literal_affine_error_le A (S j) X N (P j)
        L (v j) y hh (hW j hj) (hS j hj) (hSF j hj) (hP j hj) (hx j hj) (hg j hj))
    _ ≤ ∑ j ∈ B, W j*((1+Real.log X)*h*(Real.exp (2*h)-1+Real.exp (h-D₀))) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left ?_ (hW j hj)
      apply mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by linarith [Real.log_natCast_nonneg X]) hh)
      have he : Real.exp (h-(v j-L)) ≤ Real.exp (h-D₀) :=
        Real.exp_le_exp.mpr (sub_le_sub_left (hD j hj) h)
      simpa only [add_comm] using add_le_add_left he (Real.exp (2*h)-1)
    _ = _ := by rw [Finset.sum_mul]


/-- The two-sided estimate applies to the literal union of uniquely owned
integer labels. Each label is counted once, with every selected mask retained. -/
theorem owned_population_affine_bounds (A S : Finset ℕ) (X N : ℕ) (P : ℕ → Finset ℕ)
    (L v y : ℝ) {h W : ℝ} (hh : 0 ≤ h) (hW : 0 ≤ W)
    (hS : S ⊆ Finset.Icc 1 X)
    (hSF : ∀ a ∈ S, Squarefree a ∧ 2 ≤ a.primeFactors.card)
    (hP : ∀ a ∈ S, ∀ p ∈ P a, p.Prime ∧ ∀ q ∈ a.primeFactors, q < p)
    (hx : ∀ a ∈ S, ∀ p ∈ P a, |Real.log p+Real.log a-v| ≤ h)
    (hg : ∀ a ∈ S, (∑ p ∈ P a, |signedPrimeWeight A L N y a p|) ≤ W) :
    let g := signedPrimeWeight A L N y
    let M := ∑ a ∈ S,
      (response L v a*(∑ p ∈ P a, g a p)+cutoffSlope (v-L) a*
        (∑ p ∈ P a, g a p*(Real.log p+Real.log a-v)))/a
    let E := W*((1+Real.log X)*h*(Real.exp (2*h)-1+Real.exp (h-(v-L))))
    let F := (∑ n ∈ S.biUnion (fun a => (P a).image (fun p => a*p)),
      ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    M-E ≤ F ∧ F ≤ M+E := by
  have hp' a (ha : a ∈ S) p (hp : p ∈ P a) : p.Prime ∧ ¬p ∣ a := by
    refine ⟨(hP a ha p hp).1,?_⟩
    intro hd
    exact ((hP a ha p hp).2 p ((hP a ha p hp).1.mem_primeFactors hd (hSF a ha).1.ne_zero)).false
  have he : (∑ n ∈ S.biUnion (fun a => (P a).image (fun p => a*p)),
      ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n) =
      ∑ a ∈ S, ∑ p ∈ P a, ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a) := by
    rw [ZetaRieszCoupledWindow.sum_owned_products S P _ (fun a ha => (hSF a ha).1.ne_zero) (by
      intro a ha p hp
      exact ⟨(hP a ha p hp).1,fun q hq hd =>
        (hP a ha p hp).2 q (hq.mem_primeFactors hd (hSF a ha).1.ne_zero)⟩)]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro p _
    rw [Nat.mul_comm a p]
  dsimp only
  rw [he]
  exact literal_affine_bounds A S X N P L v y hh hW hS hSF hp' hx hg

end RiemannGaussian.ZetaRieszGlobalPrimePeriod
