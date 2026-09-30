/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaExposedPrimeFilter
import RiemannGaussian.ZetaRieszEulerPrimeHeadDensity

/-!
# Geometric decay of moving coefficients outside an exposed source

The finite competing-mode sum is estimated only after the selected mode has
been erased. Coefficients may depend on the moment order, provided their
growth is polynomial. The selected coefficient is retained exactly and is
not charged to an absolute Fourier budget. Transport of a hard-masked
arithmetic carrier to this finite expansion is a separate obligation.
-/

noncomputable section
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaExposedMovingModes
open Filter Topology

/-- A finite spectral complement tolerates polynomially moving coefficients.
The explicit constant is the number of competing modes times `C`. -/
theorem complement_bound (S : Finset ℂ) (z0 : ℂ) {u R C : ℝ}
    (hu : 0 ≤ u) (hR : 0 < R) (hC : 0 ≤ C) (d N : ℕ) (a : ℕ → ℂ → ℂ)
    (hgap : ∀ z ∈ S.erase z0, R ≤ ‖z‖)
    (ha : ∀ z ∈ S.erase z0, ‖a N z‖ ≤ C*((N : ℝ)+1)^d) :
    ‖∑ z ∈ S.erase z0, a N z*((u : ℂ)*(-z⁻¹))^(N+1)‖ ≤
      ((S.erase z0).card*C)*((N : ℝ)+1)^d*(u/R)^(N+1) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _z ∈ S.erase z0, C*((N : ℝ)+1)^d*(u/R)^(N+1) := by
      apply Finset.sum_le_sum
      intro z hz
      have hm : ‖(u : ℂ)*(-z⁻¹)‖ ≤ u/R := by
        rw [norm_mul,norm_neg,norm_inv,Complex.norm_real,Real.norm_of_nonneg hu,
          ← div_eq_mul_inv]
        exact div_le_div_of_nonneg_left hu hR (hgap z hz)
      rw [norm_mul,norm_pow]
      exact mul_le_mul (ha z hz) (pow_le_pow_left₀ (norm_nonneg _) hm _)
        (by positivity) (by positivity)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

/-- The polynomial coefficient allowance is beaten by the strict exposed gap. -/
theorem tendsto_complement (S : Finset ℂ) (z0 : ℂ) {u R C : ℝ}
    (hu : 0 < u) (huR : u < R) (hC : 0 ≤ C) (d : ℕ) (a : ℕ → ℂ → ℂ)
    (hgap : ∀ z ∈ S.erase z0, R ≤ ‖z‖)
    (ha : ∀ N z, z ∈ S.erase z0 → ‖a N z‖ ≤ C*((N : ℝ)+1)^d) :
    Tendsto (fun N => ∑ z ∈ S.erase z0,
      a N z*((u : ℂ)*(-z⁻¹))^(N+1)) atTop (𝓝 0) := by
  have hR := hu.trans huR
  have hr : 0 < u/R := div_pos hu hR
  have hr1 : u/R < 1 := (div_lt_one hR).mpr huR
  have hlim := ((ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric
    d hr hr1).mul_const (u/R)).const_mul (((S.erase z0).card : ℝ)*C)
  simp only [zero_mul,mul_zero] at hlim
  apply squeeze_zero_norm (fun N => complement_bound S z0 hu.le hR hC d N a hgap (ha N))
  convert hlim using 1
  funext N
  rw [pow_succ]
  ring

/-- The selected mode has ratio exactly one. Its moving coefficient remains
signed and unevaluated; all other modes stay in the explicit complement. -/
theorem selected_split (S : Finset ℂ) {u : ℝ} (hu : u ≠ 0)
    (hselected : -(u : ℂ) ∈ S) (a : ℕ → ℂ → ℂ) (N : ℕ) :
    (∑ z ∈ S, a N z*((u : ℂ)*(-z⁻¹))^(N+1)) =
      a N (-(u : ℂ))+
        ∑ z ∈ S.erase (-(u : ℂ)), a N z*((u : ℂ)*(-z⁻¹))^(N+1) := by
  rw [← Finset.sum_erase_add _ _ hselected]
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  simp only [inv_neg,neg_neg,mul_inv_cancel₀ huC,one_pow,mul_one]
  ring

/-- The exposed global gap also separates every competing point of the
actual canonical local divisor. No reflected or synthetic mode is used. -/
theorem canonical_support_gap {rho : NontrivialZetaZero} {R : ℝ}
    (hgap : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      R < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (r : Set.Ico (3/4 : ℝ) 1) {z : ℂ}
    (hz : z ∈ adaptiveZetaZeroSupport r rho.1.im)
    (hne : z ≠ -((3/2-rho.1.re : ℝ) : ℂ)) : R < ‖z‖ := by
  have hdiv := (mem_adaptiveZetaZeroSupport r rho.1.im z).mp hz
  have hmem := (MeromorphicOn.divisor (localZetaPoleRemoved rho.1.im)
    (Metric.ball 0 (adaptiveZetaCanonicalRadius r rho.1.im))).supportWithinDomain hdiv
  have hzR : ‖z‖ < adaptiveZetaCanonicalRadius r rho.1.im := by
    simpa only [Metric.mem_ball,dist_zero_right] using hmem
  have hz1 : ‖z‖ < 1 := hzR.trans (adaptiveZetaCanonicalRadius_spec r rho.1.im).2.1
  let s : ℂ := 3/2+Complex.I*(rho.1.im : ℂ)+z
  have hspos : 0 < s.re := by
    simp only [s,Complex.add_re,Complex.mul_re,Complex.div_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im]
    norm_num
    linarith [(abs_le.mp (Complex.abs_re_le_norm z)).1]
  let tau : NontrivialZetaZero := ⟨s,isNontrivialZetaZero_of_poleRemoved_eq_zero hspos
    (adaptiveZetaPoleRemoved_eq_zero_of_divisor_ne_zero r rho.1.im hdiv)⟩
  have htau : tau ≠ rho := by
    intro hsame
    apply hne
    have hre := congrArg (fun t : NontrivialZetaZero => t.1.re) hsame
    have him := congrArg (fun t : NontrivialZetaZero => t.1.im) hsame
    change s.re=rho.1.re at hre
    change s.im=rho.1.im at him
    norm_num [s] at hre him
    apply Complex.ext <;> simp <;> linarith
  have he : (3/2+Complex.I*(rho.1.im : ℂ))-tau.1 = -z := by
    change (3/2+Complex.I*(rho.1.im : ℂ))-s = -z
    dsimp [s]
    ring
  simpa only [he,norm_neg] using hgap tau htau

/-- One gap works for every polynomially controlled moving coefficient
family on the canonical support; the rate is explicitly `u/R`. -/
theorem exists_canonical_complement_bound (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (r : Set.Ico (3/4 : ℝ) 1) :
    ∃ R : ℝ, 3/2-rho.1.re < R ∧ R < 1 ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (d : ℕ) (a : ℕ → ℂ → ℂ),
        (∀ N z, z ∈ (adaptiveZetaZeroSupport r rho.1.im).erase
          (-((3/2-rho.1.re : ℝ) : ℂ)) → ‖a N z‖ ≤ C*((N : ℝ)+1)^d) →
        (∀ N, ‖∑ z ∈ (adaptiveZetaZeroSupport r rho.1.im).erase
            (-((3/2-rho.1.re : ℝ) : ℂ)),
          a N z*((((3/2-rho.1.re : ℝ) : ℂ))*(-z⁻¹))^(N+1)‖ ≤
          (((adaptiveZetaZeroSupport r rho.1.im).erase
            (-((3/2-rho.1.re : ℝ) : ℂ))).card*C)*
              ((N : ℝ)+1)^d*((3/2-rho.1.re)/R)^(N+1)) ∧
        Tendsto (fun N => ∑ z ∈ (adaptiveZetaZeroSupport r rho.1.im).erase
            (-((3/2-rho.1.re : ℝ) : ℂ)),
          a N z*((((3/2-rho.1.re : ℝ) : ℂ))*(-z⁻¹))^(N+1)) atTop (𝓝 0) := by
  obtain ⟨R,huR,hR1,hgap⟩ := ZetaExposedZero.exists_exposed_source_radius hrho hexposed
  have hu : 0 < 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  refine ⟨R,huR,hR1,fun C hC d a ha => ?_⟩
  have hg z (hz : z ∈ (adaptiveZetaZeroSupport r rho.1.im).erase
      (-((3/2-rho.1.re : ℝ) : ℂ))) : R ≤ ‖z‖ :=
    (canonical_support_gap hgap r (Finset.mem_erase.mp hz).2 (Finset.mem_erase.mp hz).1).le
  exact ⟨fun N => complement_bound _ _ hu.le (hu.trans huR) hC d N a hg (ha N),
    tendsto_complement _ _ hu huR hC d a hg ha⟩

/-- Exact isolation in the existing complete prime filter. The complement
is separated before any norm; the pole, analytic residual and reflected
terms retain their old signs. This identity allows `P` to vary with `N`. -/
theorem primeFilter_selected_split (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re) (P : Polynomial ℂ) (N : ℕ) :
    let r := zetaRightHalfDiscParameter rho hrho
    let u : ℝ := 3/2-rho.1.re
    let S := adaptiveZetaZeroSupport r rho.1.im
    let d := fun z : ℂ => (MeromorphicOn.divisor (localZetaPoleRemoved rho.1.im)
      (Metric.ball 0 (adaptiveZetaCanonicalRadius r rho.1.im)) z : ℂ)
    (u : ℂ)^(N+1)*zetaPrimeLogFilter P N (3/2+Complex.I*(rho.1.im : ℂ)) =
      -(analyticZetaZeroMultiplicity rho : ℂ)*P.eval (u : ℂ)⁻¹-
        (∑ z ∈ S.erase (-(u : ℂ)),
          d z*P.eval (-z⁻¹)*((u : ℂ)*(-z⁻¹))^(N+1))+
        (u : ℂ)^(N+1)*
          (((1/2+Complex.I*(rho.1.im : ℂ))⁻¹)^(N+1)*
            P.eval ((1/2+Complex.I*(rho.1.im : ℂ))⁻¹)-
            adaptiveZetaResidualFilter r rho.1.im P N+
            adaptiveZetaReflectedFilter r rho.1.im P N) := by
  dsimp only
  let r := zetaRightHalfDiscParameter rho hrho
  let u : ℝ := 3/2-rho.1.re
  let S := adaptiveZetaZeroSupport r rho.1.im
  let d := fun z : ℂ => (MeromorphicOn.divisor (localZetaPoleRemoved rho.1.im)
    (Metric.ball 0 (adaptiveZetaCanonicalRadius r rho.1.im)) z : ℂ)
  have hu : u ≠ 0 := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hi : -(u : ℂ) = ((rho.1.re-3/2 : ℝ) : ℂ) := by dsimp [u]; push_cast; ring
  have hd : d (-(u : ℂ)) = (analyticZetaZeroMultiplicity rho : ℂ) := by
    dsimp [d,r]
    rw [hi,divisor_adaptiveZetaPoleRemoved_nontrivialZero]
    simp
  have hs : -(u : ℂ) ∈ S := by
    dsimp [S,r]
    rw [hi,mem_adaptiveZetaZeroSupport,divisor_adaptiveZetaPoleRemoved_nontrivialZero]
    exact_mod_cast (analyticZetaZeroMultiplicity_positive rho).ne'
  have hsplit := selected_split S hu hs (fun _ z => d z*P.eval (-z⁻¹)) N
  simp only [inv_neg,neg_neg,hd] at hsplit
  have he : (u : ℂ)^(N+1)*
      (∑ z ∈ S, d z*((-z⁻¹)^(N+1)*P.eval (-z⁻¹))) =
      (analyticZetaZeroMultiplicity rho : ℂ)*P.eval (u : ℂ)⁻¹+
        ∑ z ∈ S.erase (-(u : ℂ)), d z*P.eval (-z⁻¹)*((u : ℂ)*(-z⁻¹))^(N+1) := by
    rw [← hsplit,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [mul_pow]
    ring
  rw [zetaPrimeLogFilter_eq_adaptive_modes r rho.1.im]
  simp only [mul_sub,Finset.sum_sub_distrib]
  rw [he]
  dsimp only [u,S,d,r] at *
  simp only [adaptiveZetaReflectedFilter,mul_add,mul_sub]
  ring

/-- The literal direct-zero complement in the complete prime-filter
expansion. This is not a definition of a masked arithmetic packet. -/
def primeFilterComplement (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re)
    (P : Polynomial ℂ) (N : ℕ) : ℂ :=
  let r := zetaRightHalfDiscParameter rho hrho
  let u : ℝ := 3/2-rho.1.re;
  -∑ z ∈ (adaptiveZetaZeroSupport r rho.1.im).erase (-(u : ℂ)),
    (MeromorphicOn.divisor (localZetaPoleRemoved rho.1.im)
      (Metric.ball 0 (adaptiveZetaCanonicalRadius r rho.1.im)) z : ℂ)*
      P.eval (-z⁻¹)*((u : ℂ)*(-z⁻¹))^(N+1)

/-- The moving-filter complement has an explicit geometric bound. Only
the competing evaluations need a polynomial budget; the selected value is
unrestricted. The bound is not asserted for unexpanded hard masks. -/
theorem primeFilterComplement_bound (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re) {R C : ℝ} (huR : 3/2-rho.1.re < R)
    (hgap : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      R < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hC : 0 ≤ C) (d N : ℕ) (P : Polynomial ℂ)
    (ha : ∀ z ∈ (adaptiveZetaZeroSupport (zetaRightHalfDiscParameter rho hrho) rho.1.im).erase
        (-((3/2-rho.1.re : ℝ) : ℂ)),
      ‖(MeromorphicOn.divisor (localZetaPoleRemoved rho.1.im)
        (Metric.ball 0 (adaptiveZetaCanonicalRadius (zetaRightHalfDiscParameter rho hrho) rho.1.im)) z : ℂ)*
          P.eval (-z⁻¹)‖ ≤ C*((N : ℝ)+1)^d) :
    ‖primeFilterComplement rho hrho P N‖ ≤
      (((adaptiveZetaZeroSupport (zetaRightHalfDiscParameter rho hrho) rho.1.im).erase
        (-((3/2-rho.1.re : ℝ) : ℂ))).card*C)*
          ((N : ℝ)+1)^d*((3/2-rho.1.re)/R)^(N+1) := by
  have hu : 0 < 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  let r := zetaRightHalfDiscParameter rho hrho
  let S := (adaptiveZetaZeroSupport r rho.1.im).erase
    (-((3/2-rho.1.re : ℝ) : ℂ))
  let a : ℕ → ℂ → ℂ := fun _ z =>
    (MeromorphicOn.divisor (localZetaPoleRemoved rho.1.im)
      (Metric.ball 0 (adaptiveZetaCanonicalRadius r rho.1.im)) z : ℂ)*P.eval (-z⁻¹)
  have hg : ∀ z ∈ S, R ≤ ‖z‖ := by
    intro z hz
    exact (canonical_support_gap hgap r (Finset.mem_erase.mp hz).2
      (Finset.mem_erase.mp hz).1).le
  have ha' : ∀ z ∈ S, ‖a N z‖ ≤ C*((N : ℝ)+1)^d := ha
  unfold primeFilterComplement
  rw [norm_neg]
  exact complement_bound (adaptiveZetaZeroSupport r rho.1.im)
    (-((3/2-rho.1.re : ℝ) : ℂ)) hu.le (hu.trans huR) hC d N a hg ha'

/-- Uniform polynomial evaluation budgets suffice for a genuinely moving
polynomial filter. No bound on its selected-source evaluation is needed. -/
theorem tendsto_primeFilterComplement (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re) {R C : ℝ} (huR : 3/2-rho.1.re < R)
    (hgap : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      R < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hC : 0 ≤ C) (d : ℕ) (P : ℕ → Polynomial ℂ)
    (ha : ∀ N z, z ∈ (adaptiveZetaZeroSupport
        (zetaRightHalfDiscParameter rho hrho) rho.1.im).erase
        (-((3/2-rho.1.re : ℝ) : ℂ)) →
      ‖(MeromorphicOn.divisor (localZetaPoleRemoved rho.1.im)
        (Metric.ball 0 (adaptiveZetaCanonicalRadius
          (zetaRightHalfDiscParameter rho hrho) rho.1.im)) z : ℂ)*
          (P N).eval (-z⁻¹)‖ ≤ C*((N : ℝ)+1)^d) :
    Tendsto (fun N => primeFilterComplement rho hrho (P N) N) atTop (𝓝 0) := by
  have hu : 0 < 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  let r := zetaRightHalfDiscParameter rho hrho
  let a : ℕ → ℂ → ℂ := fun N z =>
    (MeromorphicOn.divisor (localZetaPoleRemoved rho.1.im)
      (Metric.ball 0 (adaptiveZetaCanonicalRadius r rho.1.im)) z : ℂ)*(P N).eval (-z⁻¹)
  have hg : ∀ z ∈ (adaptiveZetaZeroSupport r rho.1.im).erase
      (-((3/2-rho.1.re : ℝ) : ℂ)), R ≤ ‖z‖ := by
    intro z hz
    exact (canonical_support_gap hgap r (Finset.mem_erase.mp hz).2
      (Finset.mem_erase.mp hz).1).le
  have h := (tendsto_complement (adaptiveZetaZeroSupport r rho.1.im)
    (-((3/2-rho.1.re : ℝ) : ℂ)) hu huR hC d a hg ha).neg
  simpa only [primeFilterComplement, a, r, neg_zero] using h

/-- Quantitative source isolation in the actual complete prime filter.
The entire old pole/residual/reflected expression is retained exactly.
Its decay for an arbitrary moving filter is not assumed or asserted here. -/
theorem primeFilter_resonance_bound (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re) {R C : ℝ} (huR : 3/2-rho.1.re < R)
    (hgap : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      R < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hC : 0 ≤ C) (d N : ℕ) (P : Polynomial ℂ)
    (ha : ∀ z ∈ (adaptiveZetaZeroSupport (zetaRightHalfDiscParameter rho hrho) rho.1.im).erase
        (-((3/2-rho.1.re : ℝ) : ℂ)),
      ‖(MeromorphicOn.divisor (localZetaPoleRemoved rho.1.im)
        (Metric.ball 0 (adaptiveZetaCanonicalRadius (zetaRightHalfDiscParameter rho hrho) rho.1.im)) z : ℂ)*
          P.eval (-z⁻¹)‖ ≤ C*((N : ℝ)+1)^d) :
    let r := zetaRightHalfDiscParameter rho hrho
    let u : ℝ := 3/2-rho.1.re
    ‖(u : ℂ)^(N+1)*zetaPrimeLogFilter P N (3/2+Complex.I*(rho.1.im : ℂ)) -
      (-(analyticZetaZeroMultiplicity rho : ℂ)*P.eval (u : ℂ)⁻¹+
        (u : ℂ)^(N+1)*
          (((1/2+Complex.I*(rho.1.im : ℂ))⁻¹)^(N+1)*
            P.eval ((1/2+Complex.I*(rho.1.im : ℂ))⁻¹)-
            adaptiveZetaResidualFilter r rho.1.im P N+
            adaptiveZetaReflectedFilter r rho.1.im P N))‖ ≤
      (((adaptiveZetaZeroSupport r rho.1.im).erase (-(u : ℂ))).card*C)*
        ((N : ℝ)+1)^d*(u/R)^(N+1) := by
  dsimp only
  have he := primeFilter_selected_split rho hrho P N
  dsimp only at he
  rw [he]
  convert primeFilterComplement_bound rho hrho huR hgap hC d N P ha using 1
  congr 1
  unfold primeFilterComplement
  ring

end RiemannGaussian.ZetaExposedMovingModes
