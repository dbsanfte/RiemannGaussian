/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointQuintupleFloor
import RiemannGaussian.ZetaRieszExtremePrimeProfile
import RiemannGaussian.ZetaRieszRenewalWeightAudit
import RiemannGaussian.ZetaRieszSymmetricOperators
import RiemannGaussian.ZetaRieszAllowanceGrowth

/-!
# Quantitative limits of small-factor compensation

When every large-prime pair remains saturated, adjoining a nonunit
squarefree small factor to a balanced triple leaves only prime insertions.
Composite insertions cancel exactly. The total weighted prime-insertion
mass has an explicit logarithmic budget relative to the base kernel.
All selections and the original residual allocation are retained. These
are local signed comparisons, not a floor for the whole core.
-/

namespace RiemannGaussian.ZetaRieszSmallDescendants
noncomputable section
open scoped BigOperators Classical
open Filter Topology ZetaSquarefreeRieszWindows ZetaRieszJointAllocation

/-- All seven proper large-prime subsets saturate the small factor.
For a composite small factor their contributions are exactly zero;
for a prime they retain its logarithm with total incidence one. -/
theorem riesz_balanced_extension {p q r a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hs : Squarefree (p*(q*(r*a)))) (ha1 : a ≠ 1) {L : ℝ}
    (hpq : Real.log p+Real.log q+Real.log a ≤ L)
    (hpr : Real.log p+Real.log r+Real.log a ≤ L)
    (hqr : Real.log q+Real.log r+Real.log a ≤ L)
    (ht : L ≤ Real.log p+Real.log q+Real.log r) :
    VaughanLogAverage.riesz L (p*(q*(r*a))) = if a.Prime then Real.log a else 0 := by
  have ha := hs.of_mul_right.of_mul_right.of_mul_right
  have hpnd : ¬p ∣ q*(r*a) :=
    hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)
  have hqnd : ¬q ∣ r*a :=
    hq.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs.of_mul_right)
  have hrnd : ¬r ∣ a :=
    hr.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs.of_mul_right.of_mul_right)
  have sat (X : ℝ) (hX : Real.log a ≤ X) :
      VaughanLogAverage.riesz X a = if a.Prime then Real.log a else 0 := by
    split_ifs with h
    · exact ZetaRieszExtremePrimeProfile.riesz_prime_of_saturated h hX
    · exact ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated ha ha1 h hX
  have hp0 := Real.log_natCast_nonneg p
  have hq0 := Real.log_natCast_nonneg q
  have hr0 := Real.log_natCast_nonneg r
  rw [riesz_prime_mul L hp hpnd,riesz_prime_mul L hq hqnd,
    riesz_prime_mul (L-Real.log p) hq hqnd,riesz_prime_mul L hr hrnd,
    riesz_prime_mul (L-Real.log q) hr hrnd,riesz_prime_mul (L-Real.log p) hr hrnd,
    riesz_prime_mul (L-Real.log p-Real.log q) hr hrnd,
    sat L (by linarith),sat (L-Real.log p) (by linarith),
    sat (L-Real.log q) (by linarith),sat (L-Real.log r) (by linarith),
    sat (L-Real.log p-Real.log q) (by linarith),
    sat (L-Real.log p-Real.log r) (by linarith),
    sat (L-Real.log q-Real.log r) (by linarith),
    ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos
      (show L-Real.log p-Real.log q-Real.log r ≤ 0 by linarith)]
  ring

/-- The coefficient itself, before phase observation or allocation. -/
theorem coefficient_balanced_extension {p q r a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hs : Squarefree (p*(q*(r*a)))) (ha1 : a ≠ 1) {L : ℝ}
    (hpq : Real.log p+Real.log q+Real.log a ≤ L)
    (hpr : Real.log p+Real.log r+Real.log a ≤ L)
    (hqr : Real.log q+Real.log r+Real.log a ≤ L)
    (ht : L ≤ Real.log p+Real.log q+Real.log r) :
    SquarefreeVaughanLogSource.coefficient L (p*(q*(r*a))) =
      if a.Prime then ((-Real.log (p*(q*(r*a)) : ℕ)*Real.log a/L : ℝ) : ℂ) else 0 := by
  have hnp : ¬(p*(q*(r*a))).Prime := Nat.not_prime_mul hp.ne_one
    (fun h => hq.ne_one (mul_eq_one.mp h).1)
  rw [SquarefreeVaughanLogSource.coefficient,if_pos ⟨hs,hnp⟩,
    riesz_balanced_extension hp hq hr hs ha1 hpq hpr hqr ht]
  split_ifs <;> simp

/-- The smaller-count budget and a fixed balanced large-prime box imply
all pair saturations. This covers every small-composite prime count. -/
theorem balanced_pair_geometry {N : ℕ} {p q r a : ℕ} {L : ℝ}
    (hL : (137/100 : ℝ)*N ≤ L) (hLu : L ≤ (7/5 : ℝ)*N)
    (hp : Real.log p ≤ (27/40 : ℝ)*N)
    (hq : Real.log q ≤ (27/40 : ℝ)*N)
    (hr : Real.log r ≤ (27/40 : ℝ)*N)
    (ha : Real.log a ≤ (N : ℝ)/2048)
    (ht : 2*(N : ℝ) ≤ Real.log p+Real.log q+Real.log r) :
    Real.log p+Real.log q+Real.log a ≤ L ∧
      Real.log p+Real.log r+Real.log a ≤ L ∧
      Real.log q+Real.log r+Real.log a ≤ L ∧
      L ≤ Real.log p+Real.log q+Real.log r := by
  constructor
  · linarith [Nat.cast_nonneg (α := ℝ) N]
  constructor
  · linarith [Nat.cast_nonneg (α := ℝ) N]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) N]

/-- Inserting a positive factor above the factorial saddle costs at
most its reciprocal. This retains the actual factorial order and is
uniform in the complex phase height. It is a bound for this local
comparison, not a source-scale bound for a whole prime sum. -/
theorem norm_kernel_extension_le (N : ℕ) (y : ℝ) {m a : ℕ}
    (hm : 1 < m) (ha : 0 < a) (hT : 2*(N : ℝ) ≤ Real.log m) :
    ‖zetaPrimeLogKernel N (3/2+Complex.I*y) (m*a)‖ ≤
      Real.exp (-Real.log a)*‖zetaPrimeLogKernel N (3/2+Complex.I*y) m‖ := by
  have hTm : 0 < Real.log m := Real.log_pos (by exact_mod_cast hm)
  have hd := Real.log_natCast_nonneg a
  have he : Real.log (a*m : ℕ) = Real.log a+Real.log m := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast ha.ne') (by exact_mod_cast (show m ≠ 0 by omega))]
  have hratio : (Real.log (a*m : ℕ)/Real.log m)^N ≤ Real.exp (Real.log a/2) := by
    have hbase : Real.log (a*m : ℕ)/Real.log m ≤ Real.exp (Real.log a/Real.log m) := by
      rw [he,add_div,div_self hTm.ne']
      simpa only [add_comm] using Real.add_one_le_exp (Real.log a/Real.log m)
    have hmul : (N : ℝ)*(Real.log a/Real.log m) ≤ Real.log a/2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      have h := mul_le_mul_of_nonneg_right hT (div_nonneg hd hTm.le)
      have heq : Real.log m*(Real.log a/Real.log m) = Real.log a := by field_simp
      rw [heq] at h
      linarith
    exact (pow_le_pow_left₀ (div_nonneg (Real.log_natCast_nonneg _) hTm.le) hbase N).trans
      (by rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.mpr hmul)
  rw [Nat.mul_comm m a,ZetaRieszTypeII.kernel_mul_transport N _ ha hm]
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.log_natCast_nonneg _) hTm.le),norm_zetaPrimeFeature]
  have hphase : zetaPrimeExpWeight (3/2+Complex.I*(y : ℂ)).re a =
      Real.exp (-(3/2 : ℝ)*Real.log a) := by norm_num [zetaPrimeExpWeight]
  rw [hphase]
  calc
    _ ≤ (Real.exp (Real.log a/2)*Real.exp (-(3/2 : ℝ)*Real.log a))*
        ‖zetaPrimeLogKernel N (3/2+Complex.I*y) m‖ := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

/-- A completely explicit insertion budget. Bounding by all integers
and the harmonic sum is enough; no prime-density approximation is used. -/
theorem small_factor_log_mass_le (N : ℕ) (D : Finset ℕ)
    (hD : ∀ a ∈ D, 0 < a ∧ a ≤ N^2) :
    (∑ a ∈ D, Real.log a*Real.exp (-Real.log a)) ≤
      2*Real.log N*(1+2*Real.log N) := by
  have hpoint (a : ℕ) (haD : a ∈ D) :
      Real.log a*Real.exp (-Real.log a) ≤
        (2*Real.log N)*(a : ℝ)⁻¹ := by
    obtain ⟨ha,hau⟩ := hD a haD
    have hl : Real.log a ≤ 2*Real.log N := by
      have hh := Real.log_le_log (by exact_mod_cast ha : (0 : ℝ) < a)
        (by exact_mod_cast hau : (a : ℝ) ≤ (N : ℝ)^2)
      simpa only [Real.log_pow,Nat.cast_ofNat] using hh
    rw [Real.exp_neg,Real.exp_log (by exact_mod_cast ha : (0 : ℝ) < a)]
    exact mul_le_mul_of_nonneg_right hl (by positivity)
  have hh : (∑ a ∈ Finset.Icc 1 (N^2), (a : ℝ)⁻¹) ≤ 1+2*Real.log N := by
    have h := harmonic_le_one_add_log (N^2)
    have hl : Real.log (N^2 : ℕ) = 2*Real.log N := by
      rw [Nat.cast_pow,Real.log_pow]
      norm_num
    rw [hl] at h
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using h
  have hsub : D ⊆ Finset.Icc 1 (N^2) := fun a ha => Finset.mem_Icc.mpr (hD a ha)
  calc
    _ ≤ ∑ a ∈ D, (2*Real.log N)*(a : ℝ)⁻¹ := Finset.sum_le_sum hpoint
    _ = (2*Real.log N)*∑ a ∈ D, (a : ℝ)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ (2*Real.log N)*∑ a ∈ Finset.Icc 1 (N^2), (a : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun a _ _ => by positivity)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)

/-- Any chosen nonunit extensions in the balanced chamber satisfy this
coefficient budget. Composite factors contribute exactly zero, regardless
of their size; only the prime case needs the original logarithmic window. -/
theorem norm_residual_extension_le (A : Finset ℕ) (N : ℕ) {p q r a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hs : Squarefree (p*(q*(r*a)))) (ha1 : a ≠ 1) {L : ℝ} (hL : 0 < L)
    (hpq : Real.log p+Real.log q+Real.log a ≤ L)
    (hpr : Real.log p+Real.log r+Real.log a ≤ L)
    (hqr : Real.log q+Real.log r+Real.log a ≤ L)
    (ht : L ≤ Real.log p+Real.log q+Real.log r)
    (hwindow : Real.log (p*(q*(r*a)) : ℕ) ≤ 2*L) :
    ‖residualCoefficient A L N (p*(q*(r*a)))‖ ≤
      if a.Prime then 2*Real.log a else 0 := by
  have h := ZetaRieszJointCountFloor.norm_residual_le A L N (p*(q*(r*a)))
  rw [coefficient_balanced_extension hp hq hr hs ha1 hpq hpr hqr ht] at h
  split_ifs at h ⊢ with ha
  · have hquot : Real.log (p*(q*(r*a)) : ℕ)/L ≤ 2 :=
      (div_le_iff₀ hL).mpr (by linarith)
    have he : ‖((-Real.log (p*(q*(r*a)) : ℕ)*Real.log a/L : ℝ) : ℂ)‖ =
        (Real.log (p*(q*(r*a)) : ℕ)/L)*Real.log a := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_div,abs_mul,abs_neg,
        abs_of_nonneg (Real.log_natCast_nonneg _),abs_of_nonneg (Real.log_natCast_nonneg _),
        abs_of_pos hL]
      ring
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_right hquot (Real.log_natCast_nonneg a))
  · simpa only [norm_zero] using h

/-- The complete sum of surviving small-factor descendants has a
quantitative budget. D is arbitrary: all physical, window, count,
coprimality and phase selections may be retained in it. No missing child
is inserted and no phase is frozen. Composite descendants, even above
N squared, vanish before taking the norm. -/
theorem norm_descendants_le (A D : Finset ℕ) (N : ℕ) (y : ℝ) {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) {L : ℝ} (hL : 0 < L)
    (hT : 2*(N : ℝ) ≤ Real.log (p*(q*r) : ℕ))
    (hD : ∀ a ∈ D, a ≠ 1 ∧ Squarefree (p*(q*(r*a))) ∧
      Real.log p+Real.log q+Real.log a ≤ L ∧
      Real.log p+Real.log r+Real.log a ≤ L ∧
      Real.log q+Real.log r+Real.log a ≤ L ∧
      L ≤ Real.log p+Real.log q+Real.log r ∧
      Real.log (p*(q*(r*a)) : ℕ) ≤ 2*L ∧ (a.Prime → a ≤ N^2)) :
    ‖∑ a ∈ D, residualCoefficient A L N (p*(q*(r*a)))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*(r*a)))‖ ≤
      4*Real.log N*(1+2*Real.log N)*
        ‖zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))‖ := by
  let Q := D.filter Nat.Prime
  have hm : 1 < p*(q*r) := hp.one_lt.trans_le
    (Nat.le_mul_of_pos_right p (Nat.mul_pos hq.pos hr.pos))
  have he : (∑ a ∈ D, residualCoefficient A L N (p*(q*(r*a)))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*(r*a)))) =
      ∑ a ∈ Q, residualCoefficient A L N (p*(q*(r*a)))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*(r*a))) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a ha hout
    obtain ⟨ha1,hs,hpq,hpr,hqr,ht,hw,_⟩ := hD a ha
    have hnp : ¬a.Prime := fun h => hout (Finset.mem_filter.mpr ⟨ha,h⟩)
    have hb := norm_residual_extension_le A N hp hq hr hs ha1 hL hpq hpr hqr ht hw
    rw [if_neg hnp] at hb
    rw [norm_le_zero_iff.mp hb,zero_mul]
  rw [he]
  have hmass := small_factor_log_mass_le N Q (by
    intro a ha
    obtain ⟨haD,hap⟩ := Finset.mem_filter.mp ha
    exact ⟨hap.pos,(hD a haD).2.2.2.2.2.2.2 hap⟩)
  calc
    _ ≤ ∑ a ∈ Q, ‖residualCoefficient A L N (p*(q*(r*a)))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*(r*a)))‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ Q, (2*Real.log a*Real.exp (-Real.log a))*
        ‖zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))‖ := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨haD,hap⟩ := Finset.mem_filter.mp ha
      obtain ⟨ha1,hs,hpq,hpr,hqr,ht,hw,_⟩ := hD a haD
      have hc := norm_residual_extension_le A N hp hq hr hs ha1 hL hpq hpr hqr ht hw
      rw [if_pos hap] at hc
      have hk := norm_kernel_extension_le N y hm hap.pos hT
      rw [Nat.mul_assoc,Nat.mul_assoc] at hk
      rw [norm_mul]
      calc
        _ ≤ (2*Real.log a)*(Real.exp (-Real.log a)*
            ‖zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))‖) :=
          mul_le_mul hc hk (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ = 2*(∑ a ∈ Q, Real.log a*Real.exp (-Real.log a))*
        ‖zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))‖ := by
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmass (by norm_num : (0 : ℝ) ≤ 2))
        (norm_nonneg (zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))))
      convert h using 1 <;> first | rfl | ring

/-- The pair and full-window hypotheses of the quantitative bound follow
from this concrete interior chamber and the already paid smooth-factor
budget. No small-factor prime count is fixed. -/
theorem norm_descendants_of_geometry (A D : Finset ℕ) (N : ℕ) (y : ℝ)
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    {L : ℝ} (hL : 0 < L) (hLlo : (137/100 : ℝ)*N ≤ L)
    (hLhi : L ≤ (7/5 : ℝ)*N)
    (hpbox : Real.log p ≤ (27/40 : ℝ)*N)
    (hqbox : Real.log q ≤ (27/40 : ℝ)*N)
    (hrbox : Real.log r ≤ (27/40 : ℝ)*N)
    (hT : 2*(N : ℝ) ≤ Real.log (p*(q*r) : ℕ))
    (hD : ∀ a ∈ D, a ≠ 1 ∧ Squarefree (p*(q*(r*a))) ∧
      Real.log a ≤ (N : ℝ)/2048 ∧ (a.Prime → a ≤ N^2)) :
    ‖∑ a ∈ D, residualCoefficient A L N (p*(q*(r*a)))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*(r*a)))‖ ≤
      4*Real.log N*(1+2*Real.log N)*
        ‖zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))‖ := by
  have hlogm : Real.log (p*(q*r) : ℕ) = Real.log p+Real.log q+Real.log r := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast Nat.mul_ne_zero hq.ne_zero hr.ne_zero),Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hr.ne_zero)]
    ring
  apply norm_descendants_le A D N y hp hq hr hL hT
  intro a haD
  obtain ⟨ha1,hs,hsmall,hprime⟩ := hD a haD
  have ha0 := hs.of_mul_right.of_mul_right.of_mul_right.ne_zero
  have hlogn : Real.log (p*(q*(r*a)) : ℕ) = Real.log p+Real.log q+Real.log r+Real.log a := by
    rw [← Nat.mul_assoc,← Nat.mul_assoc,Nat.cast_mul,
      Real.log_mul (by exact_mod_cast Nat.mul_ne_zero (Nat.mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero)
        (by exact_mod_cast ha0),Nat.mul_assoc,hlogm]
  obtain ⟨h1,h2,h3,h4⟩ := balanced_pair_geometry hLlo hLhi hpbox hqbox hrbox hsmall
    (by rwa [← hlogm])
  exact ⟨ha1,hs,h1,h2,h3,h4,by rw [hlogn]; linarith [Nat.cast_nonneg (α := ℝ) N],hprime⟩

/-- The raw balanced coefficient and the literal surviving allocation
give a linear-order lower bound for the base atom's modulus. -/
theorem base_atom_norm_lower (A : Finset ℕ) (N : ℕ) (y : ℝ) {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) {L : ℝ} (hL : 0 < L)
    (hLu : L ≤ (3/2 : ℝ)*N)
    (hpqL : Real.log p+Real.log q ≤ L)
    (hprL : Real.log p+Real.log r ≤ L)
    (hqrL : Real.log q+Real.log r ≤ L)
    (hT : 2*(N : ℝ) ≤ Real.log (p*(q*r) : ℕ))
    (hshare : (1/2 : ℝ) ≤ 1-boundedShare A N (p*(q*r))) :
    (N : ℝ)/4*‖zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))‖ ≤
      ‖residualCoefficient A L N (p*(q*r))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))‖ := by
  have hlt : L ≤ Real.log (p*(q*r) : ℕ) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hcoef := ZetaRieszSymmetricOperators.coefficient_three_pair_saturated
    hp hq hr hpq hpr hqr hpqL hprL hqrL hlt
  have hquot : 1 ≤ Real.log (p*(q*r) : ℕ)/L := (le_div_iff₀ hL).mpr (by linarith)
  have hgap : (N : ℝ)/2 ≤ Real.log (p*(q*r) : ℕ)-L := by linarith
  have hcost : (N : ℝ)/2 ≤ (Real.log (p*(q*r) : ℕ)/L)*(Real.log (p*(q*r) : ℕ)-L) := by
    nlinarith [mul_le_mul_of_nonneg_right hquot (sub_nonneg.mpr hlt)]
  have hnorm : (N : ℝ)/4 ≤ ‖residualCoefficient A L N (p*(q*r))‖ := by
    rw [residualCoefficient,hcoef,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ 1-boundedShare A N (p*(q*r))),
      abs_of_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) N] :
        0 ≤ (Real.log (p*(q*r) : ℕ)/L)*(Real.log (p*(q*r) : ℕ)-L))]
    nlinarith [mul_le_mul_of_nonneg_right hshare
      (show 0 ≤ (Real.log (p*(q*r) : ℕ)/L)*(Real.log (p*(q*r) : ℕ)-L) by
        nlinarith [Nat.cast_nonneg (α := ℝ) N])]
  simpa only [norm_mul] using mul_le_mul_of_nonneg_right hnorm
    (norm_nonneg (zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))))

/-- The surviving-half premise is supplied uniformly by the existing
literal allocation estimate, not by a new arithmetic hypothesis. -/
theorem eventually_balanced_unassigned_half :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (n : ℕ), Squarefree n → 1 < n →
      n.primeFactors.card = 3 →
      (∀ p ∈ n.primeFactors, Real.log p ≤ Real.log n/2) →
      (1/2 : ℝ) ≤ 1-boundedShare A N n := by
  filter_upwards [ZetaRieszAllowanceGrowth.eventually_triple_unassigned]
    with N hN A n hs hn1 hc hbal
  have hb := ZetaRieszBalancedCompanion.share_small_of_selected_primes_balanced
    A N hs hn1 (fun p hp _ _ => hbal p hp)
  rw [hc] at hb
  norm_num only [Nat.cast_ofNat] at hb
  unfold boundedShare
  split_ifs
  · linarith
  · norm_num

/-- The actual balanced prime boxes used by the existing growth audit
eventually lie in this chamber, uniformly over its bounded phase shift.
The assertion is about actual prime products, not continuum shares. -/
theorem eventually_prime_boxes_in_chamber {C h : ℝ} (hC : 0 ≤ C) (hh : 0 ≤ h) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℝ, (2/3 : ℝ)*N ≤ b → b ≤ (2/3 : ℝ)*N+C →
      ∀ n ∈ ZetaRieszAllowancePrimeBoxes.tripleProducts b h,
        2*(N : ℝ) ≤ Real.log n ∧
          ∀ p ∈ n.primeFactors, Real.log p ≤ (27/40 : ℝ)*N := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
    (240*(C+3*h+1))] with N hN b hb hb' n hn
  have hdata := ZetaRieszAllowancePrimeBoxes.tripleProducts_bounds hh hn
  constructor
  · linarith [hdata.2.2.1]
  · intro p hp
    have hl := hdata.2.2.2.2 p hp
    linarith

/-- Even optimally phased descendants cannot supply a fixed fraction
of the base negative atom. The arbitrary signed complement W is retained
verbatim. This is an upper obstruction estimate, not the desired lower
floor for the full core. -/
theorem signed_block_upper {N : ℕ} (hN : 0 < N) {B D W : ℂ} {K : ℝ}
    (hbase : (N : ℝ)/4*K ≤ ‖B‖)
    (hdesc : ‖D‖ ≤ 4*Real.log N*(1+2*Real.log N)*K)
    (hphase : B.re ≤ -(1/2 : ℝ)*‖B‖) :
    (W+(B+D)).re ≤ W.re+
      (16*Real.log N*(1+2*Real.log N)/(N : ℝ)-1/2)*‖B‖ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : K ≤ 4/(N : ℝ)*‖B‖ := by
    calc
      _ ≤ 4*‖B‖/(N : ℝ) := (le_div_iff₀ hn).mpr (by linarith)
      _ = _ := by ring
  have h := hdesc.trans (mul_le_mul_of_nonneg_left hk (by positivity))
  have hr := Complex.re_le_norm D
  simp only [Complex.add_re]
  calc
    _ ≤ W.re-(1/2 : ℝ)*‖B‖+
        (4*Real.log N*(1+2*Real.log N))*(4/(N : ℝ)*‖B‖) := by linarith
    _ = _ := by ring

/-- The signed obstruction for actual prime labels and their selected
descendants. An arbitrary complementary carrier W remains in the same
observation. The phase premise selects a negative base atom; descendants
retain their own phases and allocation without restriction. -/
theorem re_balanced_descendants_upper (A D : Finset ℕ) {N : ℕ} (hN : 0 < N)
    (y : ℝ) {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {L : ℝ} (hL : 0 < L) (hLlo : (137/100 : ℝ)*N ≤ L)
    (hLhi : L ≤ (7/5 : ℝ)*N)
    (hpbox : Real.log p ≤ (27/40 : ℝ)*N)
    (hqbox : Real.log q ≤ (27/40 : ℝ)*N)
    (hrbox : Real.log r ≤ (27/40 : ℝ)*N)
    (hT : 2*(N : ℝ) ≤ Real.log (p*(q*r) : ℕ))
    (hshare : (1/2 : ℝ) ≤ 1-boundedShare A N (p*(q*r)))
    (hD : ∀ a ∈ D, a ≠ 1 ∧ Squarefree (p*(q*(r*a))) ∧
      Real.log a ≤ (N : ℝ)/2048 ∧ (a.Prime → a ≤ N^2))
    (W : ℂ)
    (hphase : (residualCoefficient A L N (p*(q*r))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))).re ≤
      -(1/2 : ℝ)*‖residualCoefficient A L N (p*(q*r))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))‖) :
    (W+(residualCoefficient A L N (p*(q*r))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))+
      ∑ a ∈ D, residualCoefficient A L N (p*(q*(r*a)))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*(r*a))))).re ≤
      W.re+(16*Real.log N*(1+2*Real.log N)/(N : ℝ)-1/2)*
        ‖residualCoefficient A L N (p*(q*r))*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))‖ := by
  have hb := base_atom_norm_lower A N y hp hq hr hpq hpr hqr hL
    (by linarith [Nat.cast_nonneg (α := ℝ) N])
    (by linarith [Nat.cast_nonneg (α := ℝ) N])
    (by linarith [Nat.cast_nonneg (α := ℝ) N])
    (by linarith [Nat.cast_nonneg (α := ℝ) N]) hT hshare
  exact signed_block_upper hN hb
    (norm_descendants_of_geometry A D N y hp hq hr hL hLlo hLhi hpbox hqbox hrbox hT hD) hphase

/-- The fully explicit relative budget tends to zero, also along the
original dyadic orders by composition. This does not say the unnormalized
or source-normalized descendant sum itself tends to zero. -/
theorem tendsto_relative_budget :
    Tendsto (fun N : ℕ => 16*Real.log N*(1+2*Real.log N)/(N : ℝ)) atTop (𝓝 0) := by
  have h1 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h2 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simp only [Function.comp_def,one_mul,add_zero,pow_one] at h1 h2
  have h := (h1.const_mul 16).add (h2.const_mul 32)
  simp only [mul_zero,add_zero] at h
  convert h using 1
  ext N
  ring

/-- On the unchanged dyadic schedule the relative compensation budget
is already below one thousandth from index 32. This is a fraction of a
base atom's modulus, NOT an absolute source-scale allowance. -/
theorem dyadic_relative_budget_lt (j : ℕ) (hj : 32 ≤ j) :
    16*Real.log (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)*
        (1+2*Real.log (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))/
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j : ℝ) < 1/1000 := by
  have hk : 2000*(2*j+9) < ZetaRieszPrimeCountFrequency.dyadicPrimeCount j := by
    induction j, hj using Nat.le_induction with
    | base => norm_num [ZetaRieszPrimeCountFrequency.dyadicPrimeCount]
    | succ j hj ih =>
      have he : ZetaRieszPrimeCountFrequency.dyadicPrimeCount (j+1) =
          2*ZetaRieszPrimeCountFrequency.dyadicPrimeCount j := by
        simp only [ZetaRieszPrimeCountFrequency.dyadicPrimeCount,
          show j+1+3 = (j+3)+1 by omega,pow_succ]
        ring
      rw [he]
      omega
  have hk0 : (0 : ℝ) < ZetaRieszPrimeCountFrequency.dyadicPrimeCount j := by
    unfold ZetaRieszPrimeCountFrequency.dyadicPrimeCount
    positivity
  have hn0 : (0 : ℝ) < ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by
    unfold ZetaRieszPrimeCountFrequency.dyadicMomentOrder ZetaRieszPrimeCountFrequency.dyadicPrimeCount
    positivity
  have hl := ZetaRieszMaskSupport.log_dyadicMoment_le j hj
  calc
    _ ≤ 16*((j : ℝ)+4)*(1+2*((j : ℝ)+4))/
        (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j : ℝ) := by gcongr
    _ = 2*(2*(j : ℝ)+9)/(ZetaRieszPrimeCountFrequency.dyadicPrimeCount j : ℝ) := by
      simp only [ZetaRieszPrimeCountFrequency.dyadicMomentOrder,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
      field_simp
      ring
    _ < _ := (div_lt_iff₀ hk0).mpr (by
      have hh : (2000 : ℝ)*(2*(j : ℝ)+9) < ZetaRieszPrimeCountFrequency.dyadicPrimeCount j :=
        by exact_mod_cast hk
      linarith)

end
end RiemannGaussian.ZetaRieszSmallDescendants
