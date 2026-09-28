/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimePeriodCancellation
import RiemannGaussian.ZetaRieszQuintupleHinge
import RiemannGaussian.ZetaRieszJointAllocationFloor
import RiemannGaussian.ZetaRieszJointFloor

/-!
# Joint phase cancellation for literal unbalanced triples

The two reflected-large primes leave exactly the least-prime logarithm
in the original coefficient. A full period of the remaining prime leg
therefore uses the proved signed factorial estimate. The old allocation
is retained through its existing geometrically decaying error.
-/

namespace RiemannGaussian.ZetaRieszTriplePeriod
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszCapacityPhaseBudget

/-- Exact coefficient on the two-large-prime triple chamber. -/
theorem coefficient_two_large {p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {L : ℝ} (hprL : Real.log p+Real.log r ≤ L)
    (hqrL : Real.log q+Real.log r ≤ L) (hpqL : L ≤ Real.log p+Real.log q) :
    SquarefreeVaughanLogSource.coefficient L (p*(q*r)) =
      ((Real.log (p*(q*r) : ℕ)/L*Real.log r : ℝ) : ℂ) := by
  have hs : Squarefree (p*(q*r)) := Nat.squarefree_mul_iff.mpr ⟨
    hp.coprime_iff_not_dvd.mpr (by
      intro hd
      rcases hp.dvd_mul.mp hd with hd | hd
      · exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd)
      · exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp hd)),hp.squarefree,
    Nat.squarefree_mul_iff.mpr ⟨hq.coprime_iff_not_dvd.mpr
      (fun hd => hqr ((Nat.prime_dvd_prime_iff_eq hq hr).mp hd)),hq.squarefree,hr.squarefree⟩⟩
  have hnp : ¬(p*(q*r)).Prime := by
    intro h
    have hd : p ∣ p*(q*r) := dvd_mul_right _ _
    have he := (Nat.prime_dvd_prime_iff_eq hp h).mp hd
    have hqr1 : 1 < q*r := by nlinarith [hq.two_le,hr.two_le]
    have hgt : p < p*(q*r) := by simpa using Nat.mul_lt_mul_of_pos_left hqr1 hp.pos
    omega
  have hR : VaughanLogAverage.riesz L (p*(q*r)) = -Real.log r := by
    rw [ZetaRieszParityPacket.riesz_three L hp hq hr hpq hpr hqr]
    unfold ZetaRieszParityPacket.threeHinge
    have hp0 := Real.log_natCast_nonneg p
    have hq0 := Real.log_natCast_nonneg q
    have hr0 := Real.log_natCast_nonneg r
    rw [max_eq_right (by linarith : 0 ≤ L),
      max_eq_right (by linarith : 0 ≤ L-Real.log p),
      max_eq_right (by linarith : 0 ≤ L-Real.log q),
      max_eq_right (by linarith : 0 ≤ L-Real.log r),
      max_eq_left (by linarith : L-Real.log p-Real.log q ≤ 0),
      max_eq_right (by linarith : 0 ≤ L-Real.log p-Real.log r),
      max_eq_right (by linarith : 0 ≤ L-Real.log q-Real.log r),
      max_eq_left (by linarith : L-Real.log p-Real.log q-Real.log r ≤ 0)]
    ring
  rw [SquarefreeVaughanLogSource.coefficient,if_pos ⟨hs,hnp⟩,hR]
  congr 1
  ring

/-- The original atom, with its full phase and exact factorial order,
is precisely the weighted last-prime sum used in the period estimate. -/
theorem re_two_large_atom {p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {L : ℝ} (hprL : Real.log p+Real.log r ≤ L)
    (hqrL : Real.log q+Real.log r ≤ L) (hpqL : L ≤ Real.log p+Real.log q)
    (N : ℕ) (y : ℝ) :
    (SquarefreeVaughanLogSource.coefficient L (p*(q*r))*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))).re =
      (Real.log r/L/(q*r : ℕ))*
        ((Real.exp (-(Real.log p+Real.log (q*r : ℕ))/2)*
          (Real.log p+Real.log (q*r : ℕ))^(N+1)/N.factorial)*
            (p : ℝ)⁻¹*Real.cos (y*(Real.log p+Real.log (q*r : ℕ)))) := by
  have hlog : Real.log (p*(q*r) : ℕ) = Real.log p+Real.log (q*r : ℕ) := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast Nat.mul_ne_zero hq.ne_zero hr.ne_zero)]
  have hex : Real.exp (-(3/2 : ℝ)*Real.log (p*(q*r) : ℕ)) =
      Real.exp (-Real.log (p*(q*r) : ℕ)/2)*(p : ℝ)⁻¹*((q*r : ℕ) : ℝ)⁻¹ := by
    rw [show -(3/2 : ℝ)*Real.log (p*(q*r) : ℕ) =
      -Real.log (p*(q*r) : ℕ)/2-Real.log (p*(q*r) : ℕ) by ring,
      Real.exp_sub,Real.exp_log (by exact_mod_cast Nat.mul_pos hp.pos (Nat.mul_pos hq.pos hr.pos)),
      Nat.cast_mul]
    ring
  rw [← ZetaRieszJointAllocation.filter_one_eq,
    ZetaRieszCosineCarrier.re_coefficient_filter_one,
    coefficient_two_large hp hq hr hpq hpr hqr hprL hqrL hpqL,Complex.ofReal_re,
    hex,hlog,pow_succ]
  ring

/-- A literal unbalanced triple fibre has a two-sided signed period
bound, uniform over all macroscopic cofactor endpoints. The hypothesis
on L is the exact Riesz chamber, not a phase or cancellation premise. -/
theorem eventually_raw_triple_period {m : ℕ} (hm : 0 < m)
    {y α : ℝ} (hy : 54 ≤ |y|) (hα : 0 < α)
    (hsmall : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hphase : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ,
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      ∃ V : ℝ, 0 < V ∧ V ≤ Real.exp (-v/2)*v^N/N.factorial ∧
        Real.exp (-v/2)*v^N/N.factorial ≤ (501/500 : ℝ)*V ∧
      ∀ (q r : ℕ) (L : ℝ), q.Prime → r.Prime → r < q → 0 < L →
        α*N+1 ≤ v-Real.log (q*r : ℕ) →
        Real.log q ≤ v-Real.pi/|y|-Real.log (q*r : ℕ) →
        v+Real.pi/|y|-Real.log q ≤ L → Real.log q+Real.log r ≤ L →
        L ≤ v-Real.pi/|y|-Real.log r →
        |(∑ p ∈ logPrimes (v-Real.pi/|y|-Real.log (q*r : ℕ)) (2*Real.pi/|y|),
          SquarefreeVaughanLogSource.coefficient L (p*(q*r))*
            zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))).re| ≤
          (Real.log r/L/(q*r : ℕ))*
            ((1/500 : ℝ)*(8*m)*(V*(v-Real.pi/|y|))*(Real.pi/(4*m*|y|))/
              (v-Real.log (q*r : ℕ))) := by
  filter_upwards [ZetaRieszPrimePeriodCancellation.eventually_factorial_prime_period
    hm hy hα hsmall hphase] with N hN v hv hlo hhi
  obtain ⟨V,hV,hbaseLower,hbase,hbound⟩ := hN v hv hlo hhi
  refine ⟨V,hV,hbaseLower,hbase,?_⟩
  intro q r L hq hr hrq hL ha howner hpr hqr hpq
  have hy0 : 0 < |y| := by linarith
  have hlog : Real.log (q*r : ℕ) = Real.log q+Real.log r := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hr.ne_zero)]
  have hrql : Real.log r < Real.log q := Real.log_lt_log
    (by exact_mod_cast hr.pos) (by exact_mod_cast hrq)
  have hatom (p : ℕ)
      (hp : p ∈ logPrimes (v-Real.pi/|y|-Real.log (q*r : ℕ)) (2*Real.pi/|y|)) :
      (SquarefreeVaughanLogSource.coefficient L (p*(q*r))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))).re =
        (Real.log r/L/(q*r : ℕ))*
          ((Real.exp (-(Real.log p+Real.log (q*r : ℕ))/2)*
            (Real.log p+Real.log (q*r : ℕ))^(N+1)/N.factorial)*
              (p : ℝ)⁻¹*Real.cos (y*(Real.log p+Real.log (q*r : ℕ)))) := by
    have hb := logPrimes_bounds hp
    have hlq : Real.log q < Real.log p := howner.trans_lt hb.2.1
    have hlr : Real.log r < Real.log p := hrql.trans hlq
    have hub : Real.log p+Real.log (q*r : ℕ) ≤ v+Real.pi/|y| := by
      have hh := hb.2.2
      rw [mul_div_assoc] at hh
      linarith
    exact re_two_large_atom hb.1 hq hr
      (by intro he; simp [he] at hlq) (by intro he; simp [he] at hlr) hrq.ne'
      (by rw [hlog] at hub; linarith) hqr
      (by rw [hlog] at hb; linarith [hb.2.1]) N y
  have he : (∑ p ∈ logPrimes (v-Real.pi/|y|-Real.log (q*r : ℕ)) (2*Real.pi/|y|),
      SquarefreeVaughanLogSource.coefficient L (p*(q*r))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))).re =
      (Real.log r/L/(q*r : ℕ))*
        (∑ p ∈ logPrimes (v-Real.pi/|y|-Real.log (q*r : ℕ)) (2*Real.pi/|y|),
          (Real.exp (-(Real.log p+Real.log (q*r : ℕ))/2)*
            (Real.log p+Real.log (q*r : ℕ))^(N+1)/N.factorial)*
              (p : ℝ)⁻¹*Real.cos (y*(Real.log p+Real.log (q*r : ℕ)))) := by
    rw [Complex.re_sum,Finset.mul_sum]
    exact Finset.sum_congr rfl hatom
  rw [he,abs_mul,abs_of_nonneg (show 0 ≤ Real.log r/L/(q*r : ℕ) by
    exact div_nonneg (div_nonneg (Real.log_natCast_nonneg r) hL.le) (Nat.cast_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [ZetaRieszPrimePeriodCancellation.sum_prime_period _ hm v (Real.log (q*r : ℕ)) y hy0]
  exact hbound _ ha

/-- One literal two-prime cofactor and its complete last-prime period. -/
def fibre (v y : ℝ) (q r : ℕ) : Finset ℕ :=
  (logPrimes (v-Real.pi/|y|-Real.log (q*r : ℕ)) (2*Real.pi/|y|)).image
    (fun p => p*(q*r))

/-- The actual integer image has no duplicated incidence. -/
theorem sum_fibre (v y : ℝ) {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (f : ℕ → ℂ) :
    (∑ n ∈ fibre v y q r, f n) =
      ∑ p ∈ logPrimes (v-Real.pi/|y|-Real.log (q*r : ℕ)) (2*Real.pi/|y|), f (p*(q*r)) := by
  apply Finset.sum_image
  intro p _ p' _ he
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hq hr) he

/-- The selected unbalanced rectangle forces the exact chamber and
strict prime ordering, uniformly through the full radial period. -/
theorem rectangle_geometry {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    {q r p : ℕ} (hq : q ∈ logPrimes ((9/25 : ℝ)*v) ((1/25 : ℝ)*v))
    (hr : r ∈ logPrimes ((2/25 : ℝ)*v) ((1/50 : ℝ)*v))
    (hp : p ∈ logPrimes (v-Real.pi/|y|-Real.log (q*r : ℕ)) (2*Real.pi/|y|)) :
    p.Prime ∧ q.Prime ∧ r.Prime ∧ r < q ∧ q < p ∧
      v-Real.pi/|y| < Real.log (p*(q*r) : ℕ) ∧
      Real.log (p*(q*r) : ℕ) ≤ v+Real.pi/|y| ∧
      (∀ a ∈ (p*(q*r)).primeFactors, Real.log a ≤ (9/16 : ℝ)*Real.log (p*(q*r) : ℕ)) ∧
      Real.log r < (31/100 : ℝ)*Real.log (p*(q*r) : ℕ) := by
  have hqb := logPrimes_bounds hq
  have hrb := logPrimes_bounds hr
  have hpb := logPrimes_bounds hp
  have hy0 : 0 < |y| := by linarith
  have hπ : 0 < Real.pi/|y| := by positivity
  have hπu : Real.pi/|y| ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hm : Real.log (q*r : ℕ) = Real.log q+Real.log r := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hqb.1.ne_zero)
      (by exact_mod_cast hrb.1.ne_zero)]
  have hn : Real.log (p*(q*r) : ℕ) = Real.log p+Real.log (q*r : ℕ) := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hpb.1.ne_zero)
      (by exact_mod_cast Nat.mul_ne_zero hqb.1.ne_zero hrb.1.ne_zero)]
  have hpbu := hpb.2.2
  rw [mul_div_assoc] at hpbu
  have hrlq : Real.log r < Real.log q := by linarith [hqb.2.1,hrb.2.2]
  have hqlp : Real.log q < Real.log p := by rw [hm] at hpb; linarith [hqb.2.2,hrb.2.2,hpb.2.1]
  have hrq : r < q := by exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast hrb.1.pos)
    (by exact_mod_cast hqb.1.pos)).mp hrlq
  have hqp : q < p := by exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast hqb.1.pos)
    (by exact_mod_cast hpb.1.pos)).mp hqlp
  have hnl : v-Real.pi/|y| < Real.log (p*(q*r) : ℕ) := by rw [hn]; linarith [hpb.2.1]
  have hnu : Real.log (p*(q*r) : ℕ) ≤ v+Real.pi/|y| := by rw [hn]; linarith only [hpbu]
  have hpmax : Real.log p ≤ (9/16 : ℝ)*Real.log (p*(q*r) : ℕ) := by
    rw [hn,hm] at hnl hnu ⊢
    linarith [hqb.2.1,hrb.2.1]
  refine ⟨hpb.1,hqb.1,hrb.1,hrq,hqp,hnl,hnu,?_,?_⟩
  · intro a ha
    have had := Nat.dvd_of_mem_primeFactors ha
    have hap := Nat.prime_of_mem_primeFactors ha
    rcases hap.dvd_mul.mp had with had | had
    · have he := (Nat.prime_dvd_prime_iff_eq hap hpb.1).mp had
      simpa only [he] using hpmax
    · rcases hap.dvd_mul.mp had with had | had
      · have he := (Nat.prime_dvd_prime_iff_eq hap hqb.1).mp had
        simpa only [he] using hqlp.le.trans hpmax
      · have he := (Nat.prime_dvd_prime_iff_eq hap hrb.1).mp had
        simpa only [he] using (hrlq.trans hqlp).le.trans hpmax
  · linarith [hrb.2.2]

/-- Ordered cofactor primes for the concrete unbalanced rectangle. -/
def cofactorPairs (v : ℝ) : Finset (ℕ × ℕ) :=
  (logPrimes ((9/25 : ℝ)*v) ((1/25 : ℝ)*v)).product
    (logPrimes ((2/25 : ℝ)*v) ((1/50 : ℝ)*v))

/-- Genuine two-prime cofactors, each with one representation. -/
def cofactors (v : ℝ) : Finset ℕ := (cofactorPairs v).image (fun qr => qr.1*qr.2)

/-- Complete periods of actual triples; no phase sector is thrown away. -/
def population (v y : ℝ) : Finset ℕ := (cofactors v).biUnion (fun a =>
  (logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)).image (fun p => a*p))

theorem cofactor_injective {v : ℝ} (hv : 0 ≤ v) :
    Set.InjOn (fun qr : ℕ × ℕ => qr.1*qr.2) (cofactorPairs v : Set (ℕ × ℕ)) := by
  rintro ⟨q,r⟩ hqr ⟨q',r'⟩ hqr' he
  change q*r = q'*r' at he
  obtain ⟨hq,hr⟩ := Finset.mem_product.mp hqr
  obtain ⟨hq',hr'⟩ := Finset.mem_product.mp hqr'
  have hqp := (logPrimes_bounds hq).1
  have hrp := (logPrimes_bounds hr).1
  have hqp' := (logPrimes_bounds hq').1
  have hrp' := (logPrimes_bounds hr').1
  have hnot : q ≠ r' := by
    intro he
    have hl := (logPrimes_bounds hq).2.1
    have hu := (logPrimes_bounds hr').2.2
    rw [he] at hl
    linarith only [hl,hu,hv]
  have hd : q ∣ q'*r' := by rw [← he]; exact dvd_mul_right _ _
  have hqq : q = q' := by
    rcases hqp.dvd_mul.mp hd with hd | hd
    · exact (Nat.prime_dvd_prime_iff_eq hqp hqp').mp hd
    · exact False.elim (hnot ((Nat.prime_dvd_prime_iff_eq hqp hrp').mp hd))
  subst q'
  have hrr := Nat.eq_of_mul_eq_mul_left hqp.pos he
  exact Prod.ext rfl hrr

/-- Unique largest-prime ownership and the ordered cofactor windows
preserve the exact original integer sum, with no incidence average. -/
theorem sum_population {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|) (f : ℕ → ℂ) :
    (∑ n ∈ population v y, f n) = ∑ qr ∈ cofactorPairs v,
      ∑ p ∈ logPrimes (v-Real.pi/|y|-Real.log (qr.1*qr.2 : ℕ)) (2*Real.pi/|y|),
        f (p*(qr.1*qr.2)) := by
  have hm (a : ℕ) (ha : a ∈ cofactors v) : a ≠ 0 := by
    obtain ⟨⟨q,r⟩,hqr,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hq,hr⟩ := Finset.mem_product.mp hqr
    exact Nat.mul_ne_zero (logPrimes_bounds hq).1.ne_zero (logPrimes_bounds hr).1.ne_zero
  have ho (a : ℕ) (ha : a ∈ cofactors v) (p : ℕ)
      (hp : p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)) :
      p.Prime ∧ ∀ r : ℕ, r.Prime → r ∣ a → r < p := by
    obtain ⟨⟨q,r⟩,hqr,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hq,hr⟩ := Finset.mem_product.mp hqr
    have hg := rectangle_geometry hv hy hq hr hp
    refine ⟨hg.1,?_⟩
    intro s hs hd
    rcases hs.dvd_mul.mp hd with hd | hd
    · have he := (Nat.prime_dvd_prime_iff_eq hs hg.2.1).mp hd
      simpa only [he] using hg.2.2.2.2.1
    · have he := (Nat.prime_dvd_prime_iff_eq hs hg.2.2.1).mp hd
      simpa only [he] using hg.2.2.2.1.trans hg.2.2.2.2.1
  rw [population,ZetaRieszCoupledWindow.sum_owned_products _ _ f hm ho,
    cofactors,Finset.sum_image (cofactor_injective (by linarith : 0 ≤ v))]
  apply Finset.sum_congr rfl
  intro qr _
  apply Finset.sum_congr rfl
  intro p _
  rw [Nat.mul_comm]

/-- The concrete rectangle has an explicit upper harmonic cofactor
mass. This is an actual prime count, not a continuum density. -/
theorem eventually_cofactor_mass :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, (N : ℝ) ≤ v →
      (∑ qr ∈ cofactorPairs v, ((qr.1*qr.2 : ℕ) : ℝ)⁻¹) ≤ 7/250 := by
  filter_upwards [ZetaRieszMacroPrimeWindows.eventually_macro_reciprocal_bounds
      (by norm_num : (0 : ℝ) < 1/100) (by norm_num : (0 : ℝ) < 1/100),
    eventually_ge_atTop (1 : ℕ)] with N hN hlarge v hv
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hv0 : 0 < v := by linarith
  have hq := (hN ((9/25 : ℝ)*v) ((1/25 : ℝ)*v) (by linarith) (by linarith)).2
  have hr := (hN ((2/25 : ℝ)*v) ((1/50 : ℝ)*v) (by linarith) (by linarith)).2
  have hqu : (∑ q ∈ logPrimes ((9/25 : ℝ)*v) ((1/25 : ℝ)*v), (q : ℝ)⁻¹) ≤ 501/4500 := by
    apply hq.trans
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hru : (∑ r ∈ logPrimes ((2/25 : ℝ)*v) ((1/50 : ℝ)*v), (r : ℝ)⁻¹) ≤ 501/2000 := by
    apply hr.trans
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hprod := mul_le_mul hqu hru
    (Finset.sum_nonneg (fun r _ => inv_nonneg.mpr (Nat.cast_nonneg r))) (by norm_num)
  have he : (∑ qr ∈ cofactorPairs v, ((qr.1*qr.2 : ℕ) : ℝ)⁻¹) =
      (∑ q ∈ logPrimes ((9/25 : ℝ)*v) ((1/25 : ℝ)*v), (q : ℝ)⁻¹)*
      (∑ r ∈ logPrimes ((2/25 : ℝ)*v) ((1/50 : ℝ)*v), (r : ℝ)⁻¹) := by
    simp only [cofactorPairs,Finset.product_eq_sprod,Finset.sum_product,Nat.cast_mul,mul_inv_rev]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [he]
  exact hprod.trans (by norm_num)

/-- The whole concrete triple rectangle pays at most m/6250 of the
local radial period budget, after signed prime cancellation and actual
cofactor counting. Both phase signs are included in the same population. -/
theorem eventually_raw_population_bound {m : ℕ} (hm : 0 < m)
    {y : ℝ} (hy : 54 ≤ |y|)
    (hsmall : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hphase : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) :
    ∀ᶠ N : ℕ in atTop, ∀ (v L : ℝ),
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      (2/3 : ℝ)*v ≤ L → L ≤ (3/4 : ℝ)*v →
      ∃ V : ℝ, 0 < V ∧ V ≤ Real.exp (-v/2)*v^N/N.factorial ∧
        Real.exp (-v/2)*v^N/N.factorial ≤ (501/500 : ℝ)*V ∧
        |(∑ n ∈ population v y, SquarefreeVaughanLogSource.coefficient L n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re| ≤
            (m : ℝ)/6250*V*(Real.pi/(4*m*|y|)) := by
  filter_upwards [eventually_raw_triple_period hm hy (by norm_num : (0 : ℝ) < 1/2) hsmall hphase,
    eventually_cofactor_mass,eventually_ge_atTop (1000 : ℕ)] with N hN hmass hlarge v L hv hlo hhi hLl hLu
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hy0 : 0 < |y| := by linarith
  have hπ : 0 < Real.pi/|y| := by positivity
  have hπu : Real.pi/|y| ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hv100 : 100 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  have hL : 0 < L := by linarith
  obtain ⟨V,hV,hbaseLower,hbase,hraw⟩ := hN v hv hlo hhi
  refine ⟨V,hV,hbaseLower,hbase,?_⟩
  let h := Real.pi/(4*m*|y|)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : 0 < h := by dsimp [h]; positivity
  have hrow (qr : ℕ × ℕ) (hqr : qr ∈ cofactorPairs v) :
      |(∑ p ∈ logPrimes (v-Real.pi/|y|-Real.log (qr.1*qr.2 : ℕ)) (2*Real.pi/|y|),
        SquarefreeVaughanLogSource.coefficient L (p*(qr.1*qr.2))*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(qr.1*qr.2))).re| ≤
            ((2*m : ℝ)/375*V*h)*((qr.1*qr.2 : ℕ) : ℝ)⁻¹ := by
    obtain ⟨hq,hr⟩ := Finset.mem_product.mp hqr
    have hqb := logPrimes_bounds hq
    have hrb := logPrimes_bounds hr
    have hrq : qr.2 < qr.1 := by
      exact_mod_cast (Real.log_lt_log_iff
        (by exact_mod_cast hrb.1.pos : (0 : ℝ) < qr.2)
        (by exact_mod_cast hqb.1.pos : (0 : ℝ) < qr.1)).mp (by linarith [hrb.2.2,hqb.2.1])
    have hlog : Real.log (qr.1*qr.2 : ℕ) = Real.log qr.1+Real.log qr.2 := by
      rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hqb.1.ne_zero)
        (by exact_mod_cast hrb.1.ne_zero)]
    have hb := hraw qr.1 qr.2 L hqb.1 hrb.1 hrq hL
      (by rw [hlog]; linarith [hqb.2.2,hrb.2.2])
      (by rw [hlog]; linarith [hqb.2.2,hrb.2.2])
      (by linarith [hqb.2.1]) (by linarith [hqb.2.2,hrb.2.2])
      (by linarith [hrb.2.2])
    have ha : 0 < v-Real.log (qr.1*qr.2 : ℕ) := by rw [hlog]; linarith [hqb.2.2,hrb.2.2]
    have hlr : Real.log qr.2/L ≤ 1/6 := by
      apply (div_le_iff₀ hL).mpr
      linarith [hrb.2.2]
    have ht : (v-Real.pi/|y|)/(v-Real.log (qr.1*qr.2 : ℕ)) ≤ 2 := by
      apply (div_le_iff₀ ha).mpr
      rw [hlog]
      linarith [hqb.2.2,hrb.2.2]
    have ht0 : 0 ≤ (v-Real.pi/|y|)/(v-Real.log (qr.1*qr.2 : ℕ)) := by
      apply div_nonneg _ ha.le
      linarith
    have hprod := mul_le_mul hlr ht ht0 (by norm_num : (0 : ℝ) ≤ 1/6)
    have hc := mul_le_mul_of_nonneg_right hprod
      (show 0 ≤ (1/500 : ℝ)*(8*m)*V*h*((qr.1*qr.2 : ℕ) : ℝ)⁻¹ by positivity)
    apply hb.trans
    convert hc using 1 <;> dsimp only [h] <;> ring
  rw [sum_population hv100 hy,Complex.re_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum hrow).trans
  rw [← Finset.mul_sum]
  have hb := mul_le_mul_of_nonneg_left (hmass v (by linarith))
    (show 0 ≤ (2*m : ℝ)/375*V*h by positivity)
  apply hb.trans
  have hp := mul_le_mul_of_nonneg_right (by norm_num : (2/375 : ℝ)*(7/250) ≤ 1/6250)
    (show 0 ≤ (m : ℝ)*V*h by positivity)
  convert hp using 1 <;> dsimp only [h] <;> ring

/-- Every label of the rectangle is an actual squarefree triple in the
original radial period and below the old allocation transition. -/
theorem population_data {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|) {n : ℕ}
    (hn : n ∈ population v y) :
    Squarefree n ∧ n.primeFactors.card = 3 ∧
      v-Real.pi/|y| < Real.log n ∧ Real.log n ≤ v+Real.pi/|y| ∧
      (∀ a ∈ n.primeFactors, Real.log a ≤ (9/16 : ℝ)*Real.log n) ∧
      ∃ r ∈ n.primeFactors, Real.log r < (31/100 : ℝ)*Real.log n := by
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨⟨q,r⟩,hqr,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hq,hr⟩ := Finset.mem_product.mp hqr
  rw [Nat.mul_comm (q*r) p]
  have hg := rectangle_geometry hv hy hq hr hp
  obtain ⟨hpp,hqp,hrp,hrq,hqp',hlo,hhi,hmax,hrsmall⟩ := hg
  have hpq := hqp'.ne'
  have hpr := (hrq.trans hqp').ne'
  have hqr := hrq.ne'
  have hs : Squarefree (p*(q*r)) := Nat.squarefree_mul_iff.mpr ⟨
    hpp.coprime_iff_not_dvd.mpr (by
      intro hd
      rcases hpp.dvd_mul.mp hd with hd | hd
      · exact hpq ((Nat.prime_dvd_prime_iff_eq hpp hqp).mp hd)
      · exact hpr ((Nat.prime_dvd_prime_iff_eq hpp hrp).mp hd)),hpp.squarefree,
    Nat.squarefree_mul_iff.mpr ⟨hqp.coprime_iff_not_dvd.mpr
      (fun hd => hqr ((Nat.prime_dvd_prime_iff_eq hqp hrp).mp hd)),hqp.squarefree,hrp.squarefree⟩⟩
  have hpf : (p*(q*r)).primeFactors = {p,q,r} := by
    simp [Nat.primeFactors_mul hpp.ne_zero (Nat.mul_ne_zero hqp.ne_zero hrp.ne_zero),
      Nat.primeFactors_mul hqp.ne_zero hrp.ne_zero,hpp.primeFactors,hqp.primeFactors,hrp.primeFactors,
      Finset.insert_comm]
  refine ⟨hs,?_,hlo,hhi,hmax,r,?_,hrsmall⟩
  · simp [hpf,hpq,hpr,hqr]
  · simp [hpf]

/-- All original core masks are discharged on the concrete rectangle.
The phase-period selection does not enlarge the arithmetic support. -/
theorem population_subset_core (j : ℕ) (hj : 32 ≤ j) {u v y : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ |y|) (hv : 100 ≤ v)
    (hL : (5/4 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
    (hlo : (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤ v-Real.pi/|y|)
    (hhi : v+Real.pi/|y| ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) :
    population v y ⊆ ZetaRieszParityPacket.coreBand u
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) := by
  intro n hn
  obtain ⟨hs,hcount,htl,htu,hmax,_⟩ := population_data hv hy hn
  apply ZetaRieszCoupledWindow.mem_core_of_prime_share_le j hj hu hU hL hs
    (by omega) ?_ (hlo.trans_lt htl) (htu.trans hhi) hmax
  rw [hcount]
  exact lt_of_lt_of_le (by decide : 3 < 4) (ZetaRieszPrimeCountFrequency.four_le_dyadicPrimeCount j)

/-- The new rectangle is disjoint from every earlier balanced-triple
selection, even before imposing any phase window. -/
theorem disjoint_balanced (S : Finset ℕ) (t h : ℝ) {v y : ℝ}
    (hv : 100 ≤ v) (hy : 54 ≤ |y|) :
    Disjoint (population v y) (ZetaRieszBroadTripleBudget.population S t h) := by
  apply Finset.disjoint_left.mpr
  intro n hn hb
  obtain ⟨_,_,_,_,_,r,hr,hrsmall⟩ := population_data hv hy hn
  have hall := (Finset.mem_filter.mp hb).2.2.2.2.2
  exact hrsmall.not_ge (hall r hr).1

/-- The existing source-normalized allocation error; it is paid once
for the entire selected population, not once per prime representation. -/
def allocationBound (N : ℕ) : ℝ :=
  (4*ZetaRieszWideOwnerAudit.radiusCeiling)*((N : ℝ)+1)*
    ZetaRieszJointAllocationFloor.Refined.allocationRate^N*
      zetaMoebiusLogMajorantMass (1+1/262144)

theorem allocationBound_nonneg (N : ℕ) : 0 ≤ allocationBound N := by
  unfold allocationBound
  exact mul_nonneg (mul_nonneg (by unfold ZetaRieszWideOwnerAudit.radiusCeiling; positivity)
    (pow_nonneg ZetaRieszJointAllocationFloor.Refined.allocationRate_bounds.1 _))
    (tsum_nonneg fun n => mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_nonneg _))

theorem tendsto_allocationBound : Tendsto allocationBound atTop (𝓝 0) :=
  ZetaRieszJointAllocationFloor.Refined.tendsto_allowance

/-- A proved raw signed estimate transfers to BOTH sides of the whole
retained sum. The complementary signed sum, phase and all weights stay
literal; the previously proved allocation error is the only added cost. -/
theorem scaled_joint_bound_of_raw (A S D : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hDS : D ⊆ S) (hD : D ⊆ ZetaRieszJointAllocation.literalWindow N)
    (hbal : ∀ n ∈ D, ∀ p ∈ n.primeFactors, p ∈ A →
      ZetaRieszJointAllocation.eligibleCofactor p (n/p) →
        Real.log p ≤ (293/500 : ℝ)*Real.log n)
    (y : ℝ) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    {B : ℝ} (hb : |(∑ n ∈ D, SquarefreeVaughanLogSource.coefficient L n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re| ≤ B) :
    |((u : ℂ)^(N+1)*
      ((∑ n ∈ S, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)-
       ∑ n ∈ S\D, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)).re| ≤
      u^(N+1)*B+allocationBound N := by
  have ha := ZetaRieszJointAllocationFloor.Refined.norm_scaled_assigned_sum_le
    A D hL N hD hbal y hu hU
  have he : (∑ n ∈ S, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)-
       (∑ n ∈ S\D, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n) =
      (∑ n ∈ D, SquarefreeVaughanLogSource.coefficient L n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)-
       ∑ n ∈ D, ZetaRieszJointAllocation.assignedCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
    have hs := Finset.sum_sdiff (f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n) hDS
    have hd : (∑ n ∈ D, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n) =
      (∑ n ∈ D, SquarefreeVaughanLogSource.coefficient L n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)-
       ∑ n ∈ D, ZetaRieszJointAllocation.assignedCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n _
      unfold ZetaRieszJointAllocation.residualCoefficient ZetaRieszJointAllocation.assignedCoefficient
      push_cast
      ring
    rw [hd] at hs
    linear_combination -hs
  rw [he,mul_sub,Complex.sub_re]
  apply (abs_sub _ _).trans
  apply add_le_add _ ((Complex.abs_re_le_norm _).trans ha)
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    abs_mul,abs_of_nonneg (pow_nonneg hu _)]
  exact mul_le_mul_of_nonneg_left hb (pow_nonneg hu _)

/-- Independent two-sided cancellation inside the WHOLE actual core.
The selected rectangle is arithmetically counted, every original mask
is checked, and the entire complementary response remains signed. -/
theorem eventually_core_joint_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {m : ℕ} (hm : 0 < m)
    {y : ℝ} (hy : 54 ≤ |y|)
    (hsmall : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hphase : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      ∃ V : ℝ, 0 < V ∧ V ≤ Real.exp (-v/2)*v^N/N.factorial ∧
        Real.exp (-v/2)*v^N/N.factorial ≤ (501/500 : ℝ)*V ∧
        |((u : ℂ)^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K-
          ∑ n ∈ ZetaRieszParityPacket.coreBand u N K\population v y,
            ZetaRieszJointAllocation.residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
              (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)).re| ≤
          u^(N+1)*((m : ℝ)/6250*V*(Real.pi/(4*m*|y|)))+allocationBound N := by
  have hroom : u < Real.exp (-(137/200 : ℝ)) :=
    hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans
      (Real.exp_lt_exp.mpr (by norm_num)))
  have hlength := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (show 0 < u by linarith) (by norm_num : (0 : ℝ) ≤ 137/200) hroom
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_raw_population_bound hm hy hsmall hphase),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hlength,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1000 : ℕ)),
    eventually_ge_atTop (32 : ℕ)] with j hraw hLlow hlarge hj
  intro v
  dsimp only
  intro hv hlo hhi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hN : 2 ≤ N := by omega
  have hy0 : 0 < |y| := by linarith
  have hπ : 0 ≤ Real.pi/|y| := by positivity
  have hv100 : 100 ≤ v := by change (39/20 : ℝ)*N ≤ _ at hlo; linarith
  have hLhi : L ≤ (7/5 : ℝ)*N := by
    have he := ZetaRieszHeadOrders.length_le_two_log_two hu.le hN
    change SquarefreeVaughanLogSource.length u N ≤ _ at he
    dsimp only [L]
    nlinarith [Real.log_two_lt_d9,Nat.cast_nonneg (α := ℝ) N]
  change 2*(137/200 : ℝ)*N ≤ L at hLlow
  change (39/20 : ℝ)*N ≤ _ at hlo
  change _ ≤ (203/100 : ℝ)*N at hhi
  obtain ⟨V,hV,hbaseLower,hbase,hB⟩ := hraw v L hv hlo hhi (by linarith) (by linarith)
  refine ⟨V,hV,hbaseLower,hbase,?_⟩
  have hD := population_subset_core j hj hu hU hy hv100 (by change (5/4 : ℝ)*N ≤ L; linarith) hlo hhi
  apply scaled_joint_bound_of_raw _ _ _ (SquarefreeVaughanLogSource.length_pos u N) N hD ?_ ?_ y
    (by linarith : 0 ≤ u) hU hB
  · intro n hn
    have hb := (population_data hv100 hy hn).2.2
    apply (ZetaRieszJointAllocation.mem_literalWindow N n).mpr
    constructor <;> linarith [hb.1,hb.2.1]
  · intro n hn p hp _ _
    have hb := (population_data hv100 hy hn).2.2.2.2.1 p hp
    nlinarith [Real.log_natCast_nonneg n]

/-- The cancellation reaches the SAME whole J+C used by the source
contradiction. Both a lower and an upper comparison follow, with a proved
vanishing error and the exact signed complement. The local radial debit
is explicit; it is not asserted to vanish at source scale. -/
theorem eventually_whole_joint_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {m : ℕ} (hm : 0 < m)
    {y : ℝ} (hy : 54 ≤ |y|)
    (hsmall : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hphase : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) :
    ∃ err : ℕ → ℝ, (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      ∃ V : ℝ, 0 < V ∧ V ≤ Real.exp (-v/2)*v^N/N.factorial ∧
        Real.exp (-v/2)*v^N/N.factorial ≤ (501/500 : ℝ)*V ∧
        |((u : ℂ)^(N+1)*(J-
          ∑ n ∈ ZetaRieszParityPacket.coreBand u N K\population v y,
            ZetaRieszJointAllocation.residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
              (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)).re| ≤
          u^(N+1)*((m : ℝ)/6250*V*(Real.pi/(4*m*|y|)))+err j := by
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount
  let J := fun j => ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y (N j) (K j)-
    ZetaRieszLeastOrderOverflow.shortOverflowPacket u y (N j) (K j)+
      ZetaRieszLeastBoundary.rest u y (N j) (K j)
  let E := fun j => (u : ℂ)^(N j+1)*(ZetaRieszParityPacket.coreResponse u y (N j) (K j)-J j)
  have hu0 : 0 ≤ u := by linarith
  have he : Tendsto E atTop (𝓝 0) := by
    have hh := (ZetaRieszJointFloor.tendsto_nondominant_sub_joint hu0 hU y).sub
      (ZetaRieszJointFloor.tendsto_nondominant_sub_core hu0 hU y)
    simp only [sub_zero] at hh
    apply hh.congr'
    filter_upwards [] with j
    dsimp only [E,J,N,K]
    ring
  let err := fun j => allocationBound (N j)+‖E j‖
  refine ⟨err,fun j => add_nonneg (allocationBound_nonneg _) (norm_nonneg _),?_,?_⟩
  · have ht := (tendsto_allocationBound.comp ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder).add he.norm
    simpa only [norm_zero,add_zero,err,N,Function.comp_def] using ht
  filter_upwards [eventually_core_joint_bound hu hU hm hy hsmall hphase] with j hj
  intro v
  dsimp only
  intro hv hlo hhi
  obtain ⟨V,hV,hbaseLower,hbase,hbound⟩ := hj v hv hlo hhi
  refine ⟨V,hV,hbaseLower,hbase,?_⟩
  let rest := ∑ n ∈ ZetaRieszParityPacket.coreBand u (N j) (K j)\population v y,
    ZetaRieszJointAllocation.residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (N j))
      (SquarefreeVaughanLogSource.length u (N j)) (N j) n*zetaPrimeLogKernel (N j) (3/2+Complex.I*y) n
  have hid : (u : ℂ)^(N j+1)*(J j-rest) =
      (u : ℂ)^(N j+1)*(ZetaRieszParityPacket.coreResponse u y (N j) (K j)-rest)-E j := by
    dsimp only [E]
    ring
  change |((u : ℂ)^(N j+1)*(J j-rest)).re| ≤ _
  rw [hid,Complex.sub_re]
  have hs := (abs_sub _ _).trans (add_le_add hbound (Complex.abs_re_le_norm (E j)))
  dsimp only [err]
  simpa only [add_assoc] using hs

/-- The period payment controls a genuinely nonempty prime population
at all sufficiently large orders; its eventual bound is not vacuous. -/
theorem eventually_population_nonempty {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, (N : ℝ) ≤ v → (population v y).Nonempty := by
  have hy0 : 0 < |y| := by linarith
  have hH : 0 < 2*Real.pi/|y| := by positivity
  have hπ : Real.pi/|y| ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hne (S : Finset ℕ) (f : ℕ → ℝ) (hp : 0 < ∑ p ∈ S, f p) : S.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.sum_empty] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  filter_upwards [ZetaRieszMacroPrimeWindows.eventually_macro_reciprocal_bounds
      (by norm_num : (0 : ℝ) < 1/100) (by norm_num : (0 : ℝ) < 1/100),
    ZetaRieszSharpPrimeWindows.eventually_log_mass_bounds hH
      (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (0 : ℝ) < 1/2),
    eventually_ge_atTop (1000 : ℕ)] with N hmacro hlast hlarge v hv
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hv0 : 0 < v := by linarith
  have hqmass := (hmacro ((9/25 : ℝ)*v) ((1/25 : ℝ)*v) (by linarith) (by linarith)).1
  have hrmass := (hmacro ((2/25 : ℝ)*v) ((1/50 : ℝ)*v) (by linarith) (by linarith)).1
  obtain ⟨q,hq⟩ := hne _ _ ((by positivity : 0 < (4999/5000 : ℝ)*((1/25)*v)/
    ((9/25)*v+(1/25)*v)).trans_le hqmass)
  obtain ⟨r,hr⟩ := hne _ _ ((by positivity : 0 < (4999/5000 : ℝ)*((1/50)*v)/
    ((2/25)*v+(1/50)*v)).trans_le hrmass)
  have hqb := logPrimes_bounds hq
  have hrb := logPrimes_bounds hr
  have hlog : Real.log (q*r : ℕ) = Real.log q+Real.log r := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hqb.1.ne_zero)
      (by exact_mod_cast hrb.1.ne_zero)]
  have hpa : (1/4 : ℝ)*N ≤ v-Real.pi/|y|-Real.log (q*r : ℕ) := by
    rw [hlog]
    linarith [hqb.2.2,hrb.2.2]
  have hpmass := (hlast _ hpa).1
  have he : 0 < Real.exp (2*Real.pi/|y|)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hH)
  obtain ⟨p,hp⟩ := hne _ _ ((by positivity : 0 < (1-1/2 : ℝ)*(Real.exp (2*Real.pi/|y|)-1)*
    Real.exp (v-Real.pi/|y|-Real.log (q*r : ℕ))).trans_le hpmass)
  refine ⟨(q*r)*p,Finset.mem_biUnion.mpr ⟨q*r,?_,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩⟩
  exact Finset.mem_image.mpr ⟨(q,r),Finset.mem_product.mpr ⟨hq,hr⟩,rfl⟩

/-- A fully specified two-sided WHOLE comparison: the phase mesh and
period are supplied by the theorem, the paid population is nonempty,
and its cost uses the original radial kernel with no free budget variable.
This is a local payment, not a claim that its source-scaled cost vanishes. -/
theorem eventually_whole_saddle_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    ∃ err : ℕ → ℝ, (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      (2 : ℝ)*N ≤ v ∧ v ≤ 2*N+1/2 ∧ Real.cos (y*v) = -1 ∧
      (population v y).Nonempty ∧
      |((u : ℂ)^(N+1)*(J-
          ∑ n ∈ ZetaRieszParityPacket.coreBand u N K\population v y,
            ZetaRieszJointAllocation.residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
              (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)).re| ≤
        (Real.pi/(25000*|y|))*u^(N+1)*(Real.exp (-v/2)*v^N/N.factorial)+err j := by
  obtain ⟨m,hm,_,hsmall,hphase⟩ := exists_period_mesh hy
  obtain ⟨err,herr,ht,hevent⟩ := eventually_whole_joint_bound hu hU hm hy hsmall hphase
  refine ⟨err,herr,ht,?_⟩
  filter_upwards [hevent,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_population_nonempty hy),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1000 : ℕ))] with j hj hne hlarge
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hy0 : 0 < |y| := by linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hπ : Real.pi/|y| ≤ 1/2 :=
    (div_le_iff₀ hy0).mpr (by linarith [Real.pi_lt_four])
  obtain ⟨v,hv,hv',hpeak⟩ := exists_negative_peak hy ((2 : ℝ)*N)
  obtain ⟨V,hV,hbaseLower,_,hbound⟩ := hj v hpeak (by change (39/20 : ℝ)*N ≤ _; linarith)
    (by change _ ≤ (203/100 : ℝ)*N; linarith)
  refine ⟨v,hv,hv',hpeak,hne v (by linarith),?_⟩
  apply hbound.trans
  apply add_le_add _ le_rfl
  have hc : (u^(N+1)*((m : ℝ)/6250*V*(Real.pi/(4*m*|y|)))) =
      (Real.pi/(25000*|y|))*u^(N+1)*V := by
    field_simp [ne_of_gt hmR,ne_of_gt hy0]
    ring
  rw [hc]
  have hu0 : 0 ≤ u := by linarith
  exact mul_le_mul_of_nonneg_left hbaseLower (by positivity)

end
end RiemannGaussian.ZetaRieszTriplePeriod
