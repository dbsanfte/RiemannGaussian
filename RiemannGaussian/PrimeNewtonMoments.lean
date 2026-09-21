/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.PrimeNewtonThree
import RiemannGaussian.DirichletFamilyMoments

/-!
# Complete differentiated Newton identities

Increasing prime triples are preserved as literal labels in every
absolutely convergent logarithmic moment.
-/

namespace RiemannGaussian.PrimeNewtonThree
noncomputable section
open Filter Topology
open scoped BigOperators Classical

/-- Coordinates are r,q,p, so the outer sum has largest prime r. -/
def tripleWeight (v : ℕ × ℕ × ℕ) : ℂ :=
  if v.2.2 < v.2.1 ∧ v.2.1 < v.1 ∧ v.2.2.Prime ∧ v.2.1.Prime ∧ v.1.Prime then 1 else 0

/-- The original integer product, with no separation of its phase. -/
def tripleLabel (v : ℕ × ℕ × ℕ) : ℕ := v.2.2 * (v.2.1*v.1)

theorem weighted_triple_eq (s : ℂ) (r q p : ℕ) :
    tripleWeight (r,q,p)*zetaPrimeFeature s (tripleLabel (r,q,p)) =
      if p<q ∧ q<r then primeAtom s r*(primeAtom s q*primeAtom s p) else 0 := by
  by_cases hpq : p<q ∧ q<r
  · by_cases hp : p.Prime <;> by_cases hq : q.Prime <;> by_cases hr : r.Prime
    all_goals simp only [tripleWeight, tripleLabel, primeAtom, hpq, hp, hq, hr,
      and_self, and_true, and_false, if_true, if_false, zero_mul, mul_zero, one_mul]
    rw [CoprimeEulerPhase.feature_mul s hp.pos (Nat.mul_pos hq.pos hr.pos),
      CoprimeEulerPhase.feature_mul s hq.pos hr.pos]
    ring
  · simp [tripleWeight, hpq, show ¬(p<q ∧ q<r ∧ p.Prime ∧ q.Prime ∧ r.Prime) from
      fun h => hpq ⟨h.1,h.2.1⟩]

/-- The ordered three-prime series is absolutely convergent. -/
theorem summable_weighted_triple {s : ℂ} (hs : 1 < s.re) :
    Summable (fun v => tripleWeight v*zetaPrimeFeature s (tripleLabel v)) := by
  have hf := summable_primeAtom hs
  have hp := summable_mul_of_summable_norm hf.norm (hf.norm.mul_norm hf.norm)
  have hi := hp.indicator {v : ℕ × ℕ × ℕ | v.2.2 < v.2.1 ∧ v.2.1 < v.1}
  apply hi.congr
  rintro ⟨r,q,p⟩
  rw [weighted_triple_eq]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]

theorem threeSeries_eq_moment_zero {s : ℂ} (hs : 1 < s.re) :
    threeSeries s = DirichletFamilyMoments.moment tripleWeight tripleLabel 0 s := by
  simp only [DirichletFamilyMoments.moment, zetaPrimeLogKernel, pow_zero,
    Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
  rw [(summable_weighted_triple hs).tsum_prod]
  unfold threeSeries
  apply tsum_congr
  intro r
  rw [((summable_weighted_triple hs).prod_factor r).tsum_prod]
  rw [tsum_eq_sum (s := Finset.range r)]
  · rw [pairPrefix, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    rw [tsum_eq_sum (s := Finset.range q)]
    · rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [weighted_triple_eq, if_pos ⟨Finset.mem_range.mp hp,Finset.mem_range.mp hq⟩]
      ring
    · intro p hp
      rw [weighted_triple_eq, if_neg (fun h => hp (Finset.mem_range.mpr h.1))]
  · intro q hq
    have hz (p : ℕ) : tripleWeight (r,q,p)*zetaPrimeFeature s (tripleLabel (r,q,p)) = 0 := by
      rw [weighted_triple_eq, if_neg (fun h => hq (Finset.mem_range.mpr h.2))]
    simp only [hz, tsum_zero]

/-- The actual E₃ factorial moment; each squarefree increasing triple
appears once, with its full product phase. -/
def threeMoment (N : ℕ) (s : ℂ) : ℂ :=
  DirichletFamilyMoments.moment tripleWeight tripleLabel N s

theorem hasSum_threeMoment (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun v => tripleWeight v*zetaPrimeLogKernel N s (tripleLabel v)) (threeMoment N s) :=
  (DirichletFamilyMoments.summable_moment tripleWeight tripleLabel
    (fun _ hσ => summable_weighted_triple (by simpa using hσ)) N hs).hasSum

/-- Differentiating E₃ inserts the full product logarithm, with no
independence or cancellation assumption on prime phases. -/
theorem signedTaylorMoment_threeSeries (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    signedTaylorMoment N threeSeries s = threeMoment N s := by
  have he : threeSeries =ᶠ[𝓝 s] DirichletFamilyMoments.moment tripleWeight tripleLabel 0 := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
    exact threeSeries_eq_moment_zero hz
  rw [signedTaylorMoment_congr N he]
  exact DirichletFamilyMoments.signedTaylorMoment_eq tripleWeight tripleLabel
    (fun _ hσ => summable_weighted_triple (by simpa using hσ)) N hs

/-- The differentiated Newton identity is an identity of the actual
convergent factorial moments, with all product-rule cross terms retained. -/
theorem six_threeMoment (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    6*threeMoment N s = signedTaylorMoment N
      (fun w => primeSeries w^3-3*primeSeries w*primeSeries (2*w)+2*primeSeries (3*w)) s := by
  have he : (fun w => (6 : ℂ)*threeSeries w) =ᶠ[𝓝 s]
      (fun w => primeSeries w^3-3*primeSeries w*primeSeries (2*w)+2*primeSeries (3*w)) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with w hw
    exact six_threeSeries hw
  rw [← signedTaylorMoment_congr N he, signedTaylorMoment_const_mul,
    signedTaylorMoment_threeSeries N hs]

end
end RiemannGaussian.PrimeNewtonThree
