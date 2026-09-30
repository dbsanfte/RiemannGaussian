/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSelectedPhysical

/-!
# The selected resonance against the entire literal ordered cofactor

The finite quotient is expanded exactly, with its Euler denominators,
least-prime ordering and factorial orders retained. Its inverse is a finite
signed Riesz response at the Gamma-translated cutoff. Nothing is completed.
-/

namespace RiemannGaussian.ZetaRieszSelectedCofactor
noncomputable section
open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Classical
open ZetaRieszSelectedGamma ZetaRieszSelectedPhysical ZetaRieszMarkedEulerError
open ZetaRieszUnshiftedCharacter ZetaRieszMarkedSeparation

/-- The full Euler-denominator weight of a selected middle-prime subset. -/
def middleWeight (U : Finset ℕ) (s : ℂ) : ℂ := ∏ p ∈ U, eulerOdds p s

/-- The least-prime difference and every larger selected prime difference. -/
def subsetCharacter (r : ℕ) (U : Finset ℕ) (xi : ℝ) : ℂ :=
  (1-zetaPrimeFeature (Complex.I*xi) r)*
    ∏ p ∈ U, (1-zetaPrimeFeature (Complex.I*xi) p)

theorem middleWeight_analytic (U : Finset ℕ) (h16 : ∀ p ∈ U, 16 ≤ p)
    {s : ℂ} (hs : 1/2 ≤ s.re) : AnalyticAt ℂ (middleWeight U) s := by
  unfold middleWeight
  apply Finset.analyticAt_fun_prod
  intro p hp
  exact eulerOdds_analytic (h16 p hp) hs

/-- Exact finite subset expansion of the quotient, including its empty
subset. All denominator channels remain in `middleWeight`. -/
theorem quotient_eq_subsets (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {s : ℂ} (hs : 1/2 ≤ s.re) (xi : ℝ) :
    quotient Q xi s = ∑ U ∈ Q.powerset,
      (∏ p ∈ U, (1-zetaPrimeFeature (Complex.I*xi) p))*middleWeight U s := by
  have he (p : ℕ) (hp : p ∈ Q) :
      (1-zetaPrimeFeature s p*zetaPrimeFeature (Complex.I*xi) p)/(1-zetaPrimeFeature s p) =
      1+(1-zetaPrimeFeature (Complex.I*xi) p)*eulerOdds p s := by
    have hb := ZetaSquarefreeSignedTail.norm_primeFeature_le_quarter hs (h16 p hp)
    have hd : 1-zetaPrimeFeature s p ≠ 0 := by
      intro hh
      have hf : zetaPrimeFeature s p = 1 := by linear_combination -hh
      rw [hf,norm_one] at hb
      norm_num at hb
    unfold eulerOdds
    field_simp
    ring
  rw [quotient,Finset.prod_congr rfl he,Finset.prod_one_add]
  simp only [Finset.prod_mul_distrib,middleWeight]

theorem quotient_moment_subsets (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {s : ℂ} (hs : 1/2 < s.re) (k : ℕ) (xi : ℝ) :
    signedTaylorMoment k (quotient Q xi) s = ∑ U ∈ Q.powerset,
      (∏ p ∈ U, (1-zetaPrimeFeature (Complex.I*xi) p))*
        signedTaylorMoment k (middleWeight U) s := by
  have he : quotient Q xi =ᶠ[nhds s] (fun z => ∑ U ∈ Q.powerset,
      (∏ p ∈ U, (1-zetaPrimeFeature (Complex.I*xi) p))*middleWeight U z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).eventually_mem hs]
      with z hz
    exact quotient_eq_subsets Q h16 hz.le xi
  have ha (U : Finset ℕ) (hU : U ∈ Q.powerset) :
      AnalyticAt ℂ (fun z => (∏ p ∈ U, (1-zetaPrimeFeature (Complex.I*xi) p))*middleWeight U z) s :=
    analyticAt_const.mul (middleWeight_analytic U
      (fun p hp => h16 p (Finset.mem_powerset.mp hU hp)) hs.le)
  rw [signedTaylorMoment_congr k he,signedTaylorMoment_sum Q.powerset k _ ha]
  simp only [signedTaylorMoment_const_mul]

/-- The unchanged correlated factorial coefficient of a least-prime
incidence and its nonempty larger-prime subset. -/
def indexWeight (N j h : ℕ) (a : Index) (s : ℂ) : ℂ :=
  zetaPrimeLogKernel h s a.1*signedTaylorMoment (N+1-j-h) (middleWeight a.2) s

theorem cofactor_eq_indices (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    {s : ℂ} (hs : 1/2 < s.re) {N j h : ℕ}
    (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j) (xi : ℝ) :
    ZetaRieszMarkedPrimeCompletion.cofactor A N j h s xi =
      ∑ a ∈ indices A, indexWeight N j h a s*subsetCharacter a.1 a.2 xi := by
  have hk : N+1-j-h ≠ 0 := by
    have hb := (Finset.mem_filter.mp hh).2
    omega
  unfold ZetaRieszMarkedPrimeCompletion.cofactor
  rw [indices,Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro r _hr
  have ht16 : ∀ p ∈ tailPrimes A r, 16 ≤ p :=
    fun p hp => h16 p (Finset.mem_filter.mp hp).1
  rw [quotient_moment_subsets (tailPrimes A r) ht16 hs,
    Finset.mul_sum]
  calc
    _ = ∑ U ∈ (tailPrimes A r).powerset,
        indexWeight N j h ⟨r,U⟩ s*subsetCharacter r U xi := by
      apply Finset.sum_congr rfl
      intro U _hU
      simp only [indexWeight,subsetCharacter,ZetaRieszMarkedEuler.coeff_leg]
      ring
    _ = _ := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro U _hU hnot
      have hU : U = ∅ := by
        by_contra hne
        exact hnot (Finset.mem_filter.mpr ⟨_hU,Finset.nonempty_iff_ne_empty.mpr hne⟩)
      subst U
      have he : middleWeight ∅ = fun _ => (1 : ℂ) := by ext z; simp [middleWeight]
      simp only [indexWeight,he,moment_one,
        PowerSeries.coeff_one,if_neg hk,mul_zero,zero_mul]

theorem subsetCharacter_eq_primeProduct {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime)
    {a : Index} (ha : a ∈ indices A) (xi : ℝ) :
    subsetCharacter a.1 a.2 xi = ZetaRieszPrimeFourier.primeProduct (label a) xi := by
  have hd := label_data hA ha
  have hr : a.1 ∉ a.2 := by
    intro h
    exact (Finset.mem_filter.mp ((index_data ha).2.1 h)).2.false
  simp only [ZetaRieszPrimeFourier.primeProduct,hd.2.2.2.1,Finset.prod_insert hr,
    subsetCharacter]

/-- The exact physical cofactor response, before any sign or norm bound. -/
def physicalCofactor (A : Finset ℕ) (N j h : ℕ) (s : ℂ) (L : ℝ) : ℂ :=
  ∑ a ∈ indices A, indexWeight N j h a s*(VaughanLogAverage.riesz L (label a) : ℂ)

/-- Gamma times beyond the actual moving length contribute exactly zero. -/
theorem physicalCofactor_eq_zero_of_nonpos (A : Finset ℕ) (N j h : ℕ) (s : ℂ)
    {L : ℝ} (hL : L ≤ 0) : physicalCofactor A N j h s L = 0 := by
  unfold physicalCofactor
  simp only [ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos hL,
    Complex.ofReal_zero,mul_zero,Finset.sum_const_zero]

/-- Each individual cofactor response is confined to a literal translated
divisor window. Both affine tails cancel before any norm is used. -/
theorem physical_atom_eq_zero_outside {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime)
    {a : Index} (ha : a ∈ indices A) {L t : ℝ}
    (ht : t ≤ L-Real.log (label a) ∨ L ≤ t) :
    VaughanLogAverage.riesz (L-t) (label a) = 0 := by
  have hd := label_data hA ha
  rcases ht with ht | ht
  · exact ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated hd.1 hd.2.1.ne' hd.2.2.1
      (by linarith)
  · exact ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos (by linarith) _

private theorem subset_integrable_aux (r : ℕ) {U : Finset ℕ} (hU : U.Nonempty)
    (x : ℝ → ℝ) (hx : Measurable x)
    (hi : ∀ q ∈ U, IntegrableOn
      (fun xi : ℝ => twoPrimeCharacter r q (x xi)/(xi : ℂ)^2) (Ioi 0)) :
    IntegrableOn (fun xi : ℝ => subsetCharacter r U (x xi)/(xi : ℂ)^2) (Ioi 0) := by
  obtain ⟨q,hq⟩ := hU
  let rest (xi : ℝ) : ℂ := ∏ p ∈ U.erase q, (1-zetaPrimeFeature (Complex.I*x xi) p)
  have hr : Measurable rest := by
    unfold rest zetaPrimeFeature
    fun_prop
  have hb (xi : ℝ) : ‖rest xi‖ ≤ (2 : ℝ)^(U.erase q).card := by
    unfold rest
    rw [norm_prod]
    calc
      _ ≤ ∏ _p ∈ U.erase q, (2 : ℝ) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          (fun p _ => ZetaRieszMainFrequency.phase_le_two p (x xi))
      _ = _ := by simp
  apply ((hi q hq).mul_bdd hr.aestronglyMeasurable (Eventually.of_forall hb)).congr
  filter_upwards with xi
  unfold subsetCharacter twoPrimeCharacter rest
  rw [← Finset.mul_prod_erase U _ hq]
  ring

theorem subset_integrable (r : ℕ) {U : Finset ℕ} (hU : U.Nonempty) :
    IntegrableOn (fun xi : ℝ => subsetCharacter r U xi/(xi : ℂ)^2) (Ioi 0) ∧
    IntegrableOn (fun xi : ℝ => subsetCharacter r U (-xi)/(xi : ℂ)^2) (Ioi 0) := by
  exact ⟨subset_integrable_aux r hU id measurable_id
    (fun q _ => integrable_twoPrimeCharacter r q),
    subset_integrable_aux r hU (fun xi => -xi) measurable_neg
      (fun q _ => integrable_twoPrimeCharacter_neg r q)⟩

/-- Every literal rectangle cofactor has TWO Fourier zeros, because the
nonempty middle subset survives and the empty subset has positive order. -/
theorem cofactor_integrable (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    {s : ℂ} (hs : 1/2 < s.re) {N j h : ℕ}
    (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j) :
    IntegrableOn (fun xi : ℝ =>
      ZetaRieszMarkedPrimeCompletion.cofactor A N j h s xi/(xi : ℂ)^2) (Ioi 0) ∧
    IntegrableOn (fun xi : ℝ =>
      ZetaRieszMarkedPrimeCompletion.cofactor A N j h s (-xi)/(xi : ℂ)^2) (Ioi 0) := by
  simp_rw [cofactor_eq_indices A h16 hs hh,Finset.sum_div,mul_div_assoc]
  constructor
  · apply integrable_finsetSum
    intro a ha
    exact ((subset_integrable a.1 (index_data ha).2.2).1.const_mul _)
  · apply integrable_finsetSum
    intro a ha
    exact ((subset_integrable a.1 (index_data ha).2.2).2.const_mul _)

theorem cofactor_measurable (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    {s : ℂ} (hs : 1/2 < s.re) {N j h : ℕ}
    (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j) :
    Measurable (ZetaRieszMarkedPrimeCompletion.cofactor A N j h s) := by
  change Measurable (fun xi => ZetaRieszMarkedPrimeCompletion.cofactor A N j h s xi)
  simp_rw [cofactor_eq_indices A h16 hs hh]
  unfold subsetCharacter zetaPrimeFeature
  fun_prop

theorem cofactor_pair_integral (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (h16 : ∀ p ∈ A, 16 ≤ p) {s : ℂ} (hs : 1/2 < s.re) {N j h : ℕ}
    (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j) (L : ℝ) :
    -1/(2*(Real.pi : ℂ))*(∫ xi : ℝ in Ioi 0,
      pair (ZetaRieszMarkedPrimeCompletion.cofactor A N j h s) L xi/(xi : ℂ)^2) =
    physicalCofactor A N j h s L := by
  have he (xi : ℝ) :
      pair (ZetaRieszMarkedPrimeCompletion.cofactor A N j h s) L xi/(xi : ℂ)^2 =
      ∑ a ∈ indices A, indexWeight N j h a s*
        (ZetaRieszPrimeFourier.primePair (label a) L xi/(xi : ℂ)^2) := by
    simp only [pair,cofactor_eq_indices A h16 hs hh,Finset.mul_sum,
      ← Finset.sum_add_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a ha
    rw [subsetCharacter_eq_primeProduct hA ha,subsetCharacter_eq_primeProduct hA ha]
    unfold phase ZetaRieszPrimeFourier.primePair
    ring
  simp_rw [he]
  have hi (a : Index) (ha : a ∈ indices A) : IntegrableOn (fun xi : ℝ =>
      indexWeight N j h a s*(ZetaRieszPrimeFourier.primePair (label a) L xi/(xi : ℂ)^2)) (Ioi 0) := by
    have hd := label_data hA ha
    exact (ZetaRieszPrimeFourier.integrable_primePair_div_sq hd.1 hd.2.1.ne' L).const_mul _
  rw [integral_finsetSum _ hi,Finset.mul_sum]
  unfold physicalCofactor
  apply Finset.sum_congr rfl
  intro a ha
  have hd := label_data hA ha
  rw [integral_const_mul,ZetaRieszPrimeFourier.riesz_eq_primePair_integral L hd.1
    hd.2.1.ne' hd.2.2.1]
  ring

/-- The entire fixed rectangle atom of the actual finite ordered
quotient is a positive Gamma average of an explicit signed physical Riesz
sum. This retains every prime subset, both phases and the exact orders. -/
theorem selected_atom_fourier_eq_physical {u : ℝ} (hu : 0 < u)
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (h16 : ∀ p ∈ A, 16 ≤ p)
    {s : ℂ} (hs : 1/2 < s.re) {N j h : ℕ} (hj : 0 < j)
    (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j) (L : ℝ) :
    (u : ℂ)^j*(-1/(2*(Real.pi : ℂ)))*
      (∫ xi : ℝ in Ioi 0, selectedPair
        (ZetaRieszMarkedPrimeCompletion.cofactor A N j h s) u j L xi/(xi : ℂ)^2) =
    (1/(j : ℂ))*(∫ t : ℝ in Ioi 0,
      (gammaKernel u j t : ℂ)*physicalCofactor A N j h s (L-t)) := by
  have hi := cofactor_integrable A h16 hs hh
  rw [selected_pair_eq_gamma_average hu hj _ (cofactor_measurable A h16 hs hh) hi.1 hi.2]
  simp_rw [cofactor_pair_integral A hA h16 hs hh]

/-- The selected shifted symbol is the existing literal symbol at `-u`.
The response uses the same prefactor as `shiftedResponse`; its contribution
to `shiftedMain` has coefficient `+m`, because the prime moment has residue
`-m` and `shiftedMain` negates that moment. -/
def selectedResponse (A : Finset ℕ) (N : ℕ) (u y L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioi 0,
      pair (ZetaRieszShiftedExterior.shiftedSymbol (-(u : ℂ)) A N y) L xi/(xi : ℂ)^2

theorem selected_symbol_pair_eq (A : Finset ℕ) (N : ℕ) (u y L xi : ℝ) :
    pair (ZetaRieszShiftedExterior.shiftedSymbol (-(u : ℂ)) A N y) L xi/(xi : ℂ)^2 =
      ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
        selectedPair (ZetaRieszMarkedPrimeCompletion.cofactor A N j h (3/2+Complex.I*y))
          u j L xi/(xi : ℂ)^2 := by
  simp only [pair,ZetaRieszShiftedExterior.shiftedSymbol,Finset.mul_sum,
    ← Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro h _hh
  unfold selectedPair
  ring

/-- Exact inversion of the ENTIRE selected shifted rectangle. All
frequency integrals are integrable. The complementary source power and
the original moving-length prefactor are retained explicitly. -/
theorem selectedResponse_eq_gamma_average {u : ℝ} (hu : 0 < u)
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y L : ℝ) :
    (u : ℂ)^(N+1)*selectedResponse A N u y L =
    -((N+1 : ℕ) : ℂ)/(L : ℂ)*
      ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
        ((u : ℂ)^(N+1-j)/(j : ℂ))*(∫ t : ℝ in Ioi 0,
          (gammaKernel u j t : ℂ)*physicalCofactor A N j h (3/2+Complex.I*y) (L-t)) := by
  have hs : (1/2 : ℝ) < (3/2+Complex.I*(y : ℂ)).re := by norm_num
  have hi (j : ℕ) (h : ℕ) (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j) :
      IntegrableOn (fun xi : ℝ => selectedPair
        (ZetaRieszMarkedPrimeCompletion.cofactor A N j h (3/2+Complex.I*y)) u j L xi/(xi : ℂ)^2)
        (Ioi 0) := by
    have hhpos := ZetaRieszMarkedLogDerivative.marked_order_pos hh
    have hc := cofactor_integrable A h16 hs hh
    exact selected_pair_integrable hu hhpos _ (cofactor_measurable A h16 hs hh) hc.1 hc.2 L
  unfold selectedResponse
  simp_rw [selected_symbol_pair_eq]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun h hh => hi j h hh))]
  simp_rw [integral_finsetSum _ (fun h hh => hi _ h hh),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro h hh
  have hjN : j ≤ N+1 := by have := Finset.mem_range.mp hj; omega
  have hp : (u : ℂ)^(N+1) = (u : ℂ)^(N+1-j)*(u : ℂ)^j := by
    rw [← pow_add,Nat.sub_add_cancel hjN]
  have he := selected_atom_fourier_eq_physical hu A hA h16 hs
    (ZetaRieszMarkedLogDerivative.marked_order_pos hh) hh L
  calc
    _ = (-((N+1 : ℕ) : ℂ)/(L : ℂ))*(u : ℂ)^(N+1-j)*
        ((u : ℂ)^j*(-1/(2*(Real.pi : ℂ)))*
          (∫ xi : ℝ in Ioi 0, selectedPair
            (ZetaRieszMarkedPrimeCompletion.cofactor A N j h (3/2+Complex.I*y)) u j L xi/(xi : ℂ)^2)) := by
      rw [hp]
      ring
    _ = _ := by rw [he]; ring

/-- The real joint ledger retains an arbitrary unchanged complement and
the actual zero multiplicity. A floor requires an UPPER bound on the
correlated physical average relative to that complement; positivity of
the Gamma kernel alone is not a floor. -/
theorem joint_real_eq {u : ℝ} (hu : 0 < u)
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N m : ℕ) (y L : ℝ) (C : ℂ) :
    ((u : ℂ)^(N+1)*((m : ℂ)*selectedResponse A N u y L+C)).re =
      ((u : ℂ)^(N+1)*C).re-
        ((m : ℝ)*(N+1 : ℕ)/(L : ℝ)) *
          (∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
            ((u : ℂ)^(N+1-j)/(j : ℂ))*(∫ t : ℝ in Ioi 0,
              (gammaKernel u j t : ℂ)*physicalCofactor A N j h (3/2+Complex.I*y) (L-t))).re := by
  have he := selectedResponse_eq_gamma_average hu A hA h16 N y L
  rw [mul_add,show (u : ℂ)^(N+1)*((m : ℂ)*selectedResponse A N u y L) =
    (m : ℂ)*((u : ℂ)^(N+1)*selectedResponse A N u y L) by ring,he]
  rw [show -((N+1 : ℕ) : ℂ)/(L : ℂ) = ((-((N+1 : ℕ) : ℝ)/L : ℝ) : ℂ) by
    push_cast; rfl]
  simp only [Complex.add_re,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

end
end RiemannGaussian.ZetaRieszSelectedCofactor
