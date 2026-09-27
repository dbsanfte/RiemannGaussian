/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOrderedCapacity

/-!
# The exact incidence factor in the favorable five-prime supply

Summing one marked pair over the six ordered incidences of the three large
primes counts each of the three caps twice. The factor one half is proved
on the original finite atom, including its allocation and complex phase.
It does not average triple discrepancies or add a new supply population.
-/

namespace RiemannGaussian.ZetaRieszCapacityIncidence
noncomputable section
open scoped BigOperators Classical
open ZetaRieszOrderedCapacity ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic

/-- The six ordered incidences contain two copies of each symmetric pair
score. Distinctness is essential and is not hidden in a factorial factor. -/
theorem sum_offDiag_three {α : Type*} [DecidableEq α] {p q a : α}
    (hpq : p ≠ q) (hpa : p ≠ a) (hqa : q ≠ a) (f : α → α → ℝ)
    (hsymm : ∀ x y, f x y = f y x) :
    (∑ e ∈ ({p,q,a} : Finset α).offDiag, f e.1 e.2) =
      2*(f p q+f p a+f q a) := by
  have he : ({p,q,a} : Finset α).offDiag =
      (({p,q,a} : Finset α) ×ˢ {p,q,a}).filter (fun e => e.1 ≠ e.2) := by
    ext e
    simp [and_assoc]
  rw [he,Finset.sum_filter,Finset.sum_product]
  simp [hpq,hpa,hqa,Ne.symm hpq,Ne.symm hpa,Ne.symm hqa]
  rw [hsymm q p,hsymm a p,hsymm a q]
  ring

/-- The one-pair cap used by the population integral. The complementary
large prime has been removed by the exact total-log identity. -/
def pairCap (lo hi : ℝ) (b r p q : ℕ) : ℝ :=
  min (Real.log r) (max 0 (min (lo-Real.log p-Real.log q)
    (Real.log b+Real.log r-hi+Real.log p+Real.log q)))

/-- Pair exchange leaves this literal cap unchanged. -/
theorem pairCap_comm (lo hi : ℝ) (b r p q : ℕ) :
    pairCap lo hi b r p q = pairCap lo hi b r q p := by
  unfold pairCap
  congr 3 <;> ring

/-- The exact half-incidence lower bound for the actual five-prime atom.
The same product, factorial order, allocation and cosine occur on both
sides; the six incidences do not provide six independent labels. -/
theorem re_five_atom_ge_ordered_pairs (A : Finset ℕ) (N : ℕ) {p q a b r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : a.Prime) (hb : b.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpa : p ≠ a) (hqa : q ≠ a)
    (hrb : r ≤ b) (hs : Squarefree (p*(q*(a*(b*r)))))
    {L lo hi y : ℝ} (hL : 0 < L) (hlo : lo ≤ L) (hhi : L ≤ hi)
    (hpb : Real.log p+Real.log (b*r : ℕ) ≤ lo)
    (hqb : Real.log q+Real.log (b*r : ℕ) ≤ lo)
    (hab : Real.log a+Real.log (b*r : ℕ) ≤ lo)
    (hpqa : hi ≤ Real.log p+Real.log q+Real.log a)
    (hcos : Real.cos (y*Real.log (p*(q*(a*(b*r))) : ℕ)) ≤ 0) :
    (weight A N (p*(q*(a*(b*r))))*(Real.log (p*(q*(a*(b*r))) : ℕ)/L)*
      (-Real.cos (y*Real.log (p*(q*(a*(b*r))) : ℕ)))/2)*
        (∑ e ∈ ({p,q,a} : Finset ℕ).offDiag, pairCap lo hi b r e.1 e.2) ≤
      (residualCoefficient A L N (p*(q*(a*(b*r))))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*(a*(b*r))))).re := by
  have hlog : Real.log (p*(q*(a*(b*r))) : ℕ) =
      Real.log p+Real.log q+Real.log a+Real.log b+Real.log r := by
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne_zero
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne_zero
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne_zero
    simp only [Nat.cast_mul]
    rw [Real.log_mul hp0 (mul_ne_zero hq0 (mul_ne_zero ha0 (mul_ne_zero hb0 hr0))),
      Real.log_mul hq0 (mul_ne_zero ha0 (mul_ne_zero hb0 hr0)),
      Real.log_mul ha0 (mul_ne_zero hb0 hr0),Real.log_mul hb0 hr0]
    ring
  rw [sum_offDiag_three hpq hpa hqa _ (pairCap_comm lo hi b r)]
  have hc := re_five_atom_ge_three_caps A N hp hq ha hb hr hrb hs
    hL hlo hhi hpb hqb hab hpqa hcos
  have he :
      min (Real.log r) (max 0 (min (lo-Real.log p-Real.log q)
        (Real.log (p*(q*(a*(b*r))) : ℕ)-hi-Real.log a)))+
      min (Real.log r) (max 0 (min (lo-Real.log p-Real.log a)
        (Real.log (p*(q*(a*(b*r))) : ℕ)-hi-Real.log q)))+
      min (Real.log r) (max 0 (min (lo-Real.log q-Real.log a)
        (Real.log (p*(q*(a*(b*r))) : ℕ)-hi-Real.log p))) =
        pairCap lo hi b r p q+pairCap lo hi b r p a+pairCap lo hi b r q a := by
    rw [hlog]
    unfold pairCap
    congr 4 <;> ring
  rw [he] at hc
  convert hc using 1
  ring

/-- Global signed supply inequality with the exact pair multiplicity.
Only the selected actual labels are replaced; every other label remains in
the original signed sum. No previous four-prime supply is spent here. -/
theorem re_sum_ge_ordered_pair_credit (S D A : Finset ℕ) (N : ℕ)
    (p q a b r : ℕ → ℕ) {L lo hi y : ℝ}
    (hDS : D ⊆ S) (hL : 0 < L) (hlo : lo ≤ L) (hhi : L ≤ hi)
    (hD : ∀ n ∈ D,
      n = p n*(q n*(a n*(b n*r n))) ∧
      (p n).Prime ∧ (q n).Prime ∧ (a n).Prime ∧ (b n).Prime ∧ (r n).Prime ∧
      p n ≠ q n ∧ p n ≠ a n ∧ q n ≠ a n ∧ r n ≤ b n ∧ Squarefree n ∧
      Real.log (p n)+Real.log (b n*r n : ℕ) ≤ lo ∧
      Real.log (q n)+Real.log (b n*r n : ℕ) ≤ lo ∧
      Real.log (a n)+Real.log (b n*r n : ℕ) ≤ lo ∧
      hi ≤ Real.log (p n)+Real.log (q n)+Real.log (a n) ∧
      Real.cos (y*Real.log n) ≤ 0) :
    (∑ n ∈ S\D, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
      (∑ n ∈ D, (weight A N n*(Real.log n/L)*(-Real.cos (y*Real.log n))/2)*
        ∑ e ∈ ({p n,q n,a n} : Finset ℕ).offDiag, pairCap lo hi (b n) (r n) e.1 e.2) ≤
      (∑ n ∈ S, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have he := congrArg Complex.re (Finset.sum_sdiff
    (f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n) hDS)
  rw [Complex.add_re] at he
  rw [← he]
  apply add_le_add le_rfl
  rw [Complex.re_sum]
  apply Finset.sum_le_sum
  intro n hn
  obtain ⟨hnp,hp,hq,ha,hb,hr,hpq,hpa,hqa,hrb,hs,hpb,hqb,hab,hpqa,hcos⟩ := hD n hn
  have hc := re_five_atom_ge_ordered_pairs A N hp hq ha hb hr hpq hpa hqa hrb
    (hnp ▸ hs) hL hlo hhi hpb hqb hab hpqa (hnp ▸ hcos)
  simpa only [← hnp] using hc

end
end RiemannGaussian.ZetaRieszCapacityIncidence
