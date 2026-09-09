/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusTailMoments
import RiemannGaussian.ZetaPrimePowerMoments
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# Differential separation of the actual Möbius contributions

Coupling the derivative of the negative logarithmic derivative to `zeta'`
cancels its second-derivative term exactly. Dividing by the selected zero's
vanishing factor gives a double pole for every genuine multiplicity.
The corresponding prime-divisor contribution has strictly smaller pole
order. All expressions retain their complex coefficients; removable values
are supplied explicitly rather than inferred from totalized division.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The derivative coupling cancels the second derivative without taking
norms or discarding the phase of any term. -/
theorem deriv_coupled_neg_logDeriv {f : ℂ → ℂ} {s : ℂ}
    (hf : AnalyticAt ℂ f s) (h0 : f s ≠ 0) :
    deriv f s * deriv (fun z ↦ -logDeriv f z) s -
      deriv (deriv f) s * (-logDeriv f s) = deriv f s ^ 3 / f s ^ 2 := by
  have hd := ((hf.deriv.differentiableAt.hasDerivAt.div
    hf.differentiableAt.hasDerivAt h0).neg).deriv
  change deriv (fun z ↦ -(deriv f z / f z)) s = _ at hd
  simp only [logDeriv_apply]
  rw [hd]
  field_simp
  ring

/-- Differentiating a genuine finite nonzero meromorphic order preserves
the leading phase and multiplies its coefficient by that order. -/
theorem meromorphicTrailingCoeffAt_deriv_of_order {f : ℂ → ℂ} {s : ℂ} {n : ℤ}
    (hf : MeromorphicAt f s) (hn : (n : ℂ) ≠ 0)
    (ho : meromorphicOrderAt f s = n) :
    meromorphicTrailingCoeffAt (deriv f) s = n * meromorphicTrailingCoeffAt f s := by
  obtain ⟨g, hg, hg0, (he : f =ᶠ[𝓝[≠] s] fun z ↦ (z - s) ^ n • g z)⟩ :=
    (meromorphicOrderAt_eq_int_iff hf).mp ho
  have hge : deriv f =ᶠ[𝓝[≠] s] fun z ↦
      (z - s) ^ (n - 1) * ((n : ℂ) * g z + (z - s) * deriv g z) := by
    filter_upwards [hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin, he.nhdsNE_deriv] with z hgz hzs hz
    have hne : z - s ≠ 0 := by simpa [sub_eq_zero] using hzs
    calc
      deriv f z = deriv (fun z ↦ (z - s) ^ n * g z) z := hz
      _ = (z - s) ^ n * deriv g z + (n * (z - s) ^ (n - 1)) * g z := by
        rw [deriv_fun_mul (by fun_prop (disch := grind)) hgz.differentiableAt]
        have hd : deriv (fun z : ℂ ↦ (z - s) ^ n) z = n * (z - s) ^ (n - 1) := by
          change deriv ((· ^ n) ∘ (· - s)) z = _
          rw [deriv_comp _ (by fun_prop (disch := grind)) (by fun_prop)]
          simp [deriv_zpow]
        rw [hd]
        ring
      _ = (z - s) ^ (n - 1) * ((n : ℂ) * g z + (z - s) * deriv g z) := by
        have hp : (z - s) ^ n = (z - s) ^ (n - 1) * (z - s) := by
          simpa using zpow_add_one₀ hne (n - 1)
        rw [hp]
        ring
  have hga : AnalyticAt ℂ (fun z ↦ (n : ℂ) * g z + (z - s) * deriv g z) s := by
    fun_prop
  rw [hga.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
    (by simpa using mul_ne_zero hn hg0) (by simpa only [smul_eq_mul] using hge),
    hg.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE hg0 he]
  simp

/-- The meromorphic order of actual zeta is its full analytic zero
multiplicity, without a simplicity hypothesis. -/
theorem meromorphicOrderAt_riemannZeta_nontrivialZero (rho : NontrivialZetaZero) :
    meromorphicOrderAt riemannZeta rho.1 = (analyticZetaZeroMultiplicity rho : ℤ) := by
  have ha := analyticAt_riemannZeta_nontrivialZero rho
  obtain ⟨g, hg, hg0, he⟩ := ha.analyticOrderAt_ne_top.mp
    (analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho)
  apply (meromorphicOrderAt_eq_int_iff ha.meromorphicAt).mpr
  refine ⟨g, hg, hg0, ?_⟩
  filter_upwards [he.filter_mono nhdsWithin_le_nhds] with z hz
  simpa only [zpow_natCast, analyticZetaZeroMultiplicity] using hz

/-- The genuine derivative has exactly one fewer vanishing order. -/
theorem meromorphicOrderAt_deriv_riemannZeta_nontrivialZero (rho : NontrivialZetaZero) :
    meromorphicOrderAt (deriv riemannZeta) rho.1 =
      ((analyticZetaZeroMultiplicity rho : ℤ) - 1 : ℤ) := by
  apply meromorphicOrderAt_deriv_eq_sub_one _
    (meromorphicOrderAt_riemannZeta_nontrivialZero rho)
  have hm := analyticZetaZeroMultiplicity_positive rho
  exact_mod_cast (show analyticZetaZeroMultiplicity rho ≠ 0 by omega)

/-- The derivative retains the exact leading zeta coefficient and the
full positive integer multiplicity. -/
theorem meromorphicTrailingCoeffAt_deriv_riemannZeta_nontrivialZero (rho : NontrivialZetaZero) :
    meromorphicTrailingCoeffAt (deriv riemannZeta) rho.1 =
      (analyticZetaZeroMultiplicity rho : ℂ) * meromorphicTrailingCoeffAt riemannZeta rho.1 := by
  apply meromorphicTrailingCoeffAt_deriv_of_order
    (analyticAt_riemannZeta_nontrivialZero rho).meromorphicAt _
    (meromorphicOrderAt_riemannZeta_nontrivialZero rho)
  have hm := analyticZetaZeroMultiplicity_positive rho
  exact_mod_cast (show analyticZetaZeroMultiplicity rho ≠ 0 by omega)

/-- The punctured cofactor that removes only the excess multiplicity of
the selected zero. Its removable value will be supplied separately. -/
def zetaMoebiusWronskianCofactor (rho : NontrivialZetaZero) (s : ℂ) : ℂ :=
  deriv riemannZeta s ^ 2 / (s - rho.1) ^ ((analyticZetaZeroMultiplicity rho : ℤ) - 1)

/-- The full differential response, with the genuine selected-zero
multiplicity correction. -/
def zetaMoebiusWronskian (rho : NontrivialZetaZero) (s : ℂ) : ℂ :=
  zetaMoebiusWronskianCofactor rho s * (deriv riemannZeta s / riemannZeta s ^ 2)

/-- Actual zeta is meromorphic also at its pole, with no prescribed
value at the pole needed for the punctured identity. -/
theorem meromorphicAt_riemannZeta (s : ℂ) : MeromorphicAt riemannZeta s := by
  by_cases hs : s = 1
  · subst s
    have he : riemannZeta =ᶠ[𝓝[≠] (1 : ℂ)] fun z ↦ (z - 1)⁻¹ * riemannZeta₁ z := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact riemannZeta_eq_inv_sub_mul (by simpa using hz)
    rw [MeromorphicAt.meromorphicAt_congr he]
    exact ((analyticAt_id.sub analyticAt_const).meromorphicAt.inv).mul
      (differentiable_riemannZeta₁.analyticAt 1).meromorphicAt
  · exact (analyticOn_riemannZeta s (by simpa using hs)).meromorphicAt

/-- The exact pole order at one is retained for later finite pole
cancellation. -/
theorem meromorphicOrderAt_riemannZeta_one : meromorphicOrderAt riemannZeta 1 = -1 := by
  apply (meromorphicOrderAt_eq_int_iff (meromorphicAt_riemannZeta 1)).mpr
  refine ⟨riemannZeta₁, differentiable_riemannZeta₁.analyticAt 1, by simp [riemannZeta₁_one], ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  simpa only [zpow_neg_one, smul_eq_mul] using
    riemannZeta_eq_inv_sub_mul (by simpa using hz)

/-- The raw multiplicity cofactor is meromorphic everywhere. -/
theorem meromorphicAt_zetaMoebiusWronskianCofactor (rho : NontrivialZetaZero) (s : ℂ) :
    MeromorphicAt (zetaMoebiusWronskianCofactor rho) s := by
  unfold zetaMoebiusWronskianCofactor
  exact ((meromorphicAt_riemannZeta s).deriv.pow 2).div
    ((analyticAt_id.sub analyticAt_const).meromorphicAt.zpow _)

/-- The complete differential response is genuinely meromorphic. -/
theorem meromorphicAt_zetaMoebiusWronskian (rho : NontrivialZetaZero) (s : ℂ) :
    MeromorphicAt (zetaMoebiusWronskian rho) s :=
  (meromorphicAt_zetaMoebiusWronskianCofactor rho s).mul
    ((meromorphicAt_riemannZeta s).deriv.div ((meromorphicAt_riemannZeta s).pow 2))

/-- At the selected zero the cofactor has nonnegative order `m - 1`;
the division does not introduce a new pole. -/
theorem meromorphicOrderAt_zetaMoebiusWronskianCofactor (rho : NontrivialZetaZero) :
    meromorphicOrderAt (zetaMoebiusWronskianCofactor rho) rho.1 =
      ((analyticZetaZeroMultiplicity rho : ℤ) - 1 : ℤ) := by
  change meromorphicOrderAt ((deriv riemannZeta) ^ 2 /
    ((fun s ↦ s - rho.1) ^ ((analyticZetaZeroMultiplicity rho : ℤ) - 1))) rho.1 = _
  rw [meromorphicOrderAt_div ((meromorphicAt_riemannZeta rho.1).deriv.pow 2) (by fun_prop),
    meromorphicOrderAt_pow (meromorphicAt_riemannZeta rho.1).deriv,
    meromorphicOrderAt_zpow (by fun_prop), meromorphicOrderAt_id_sub_const,
    meromorphicOrderAt_deriv_riemannZeta_nontrivialZero]
  change ((2 : ℤ) : WithTop ℤ) * (((analyticZetaZeroMultiplicity rho : ℤ) - 1 : ℤ) : WithTop ℤ) -
    (((analyticZetaZeroMultiplicity rho : ℤ) - 1 : ℤ) : WithTop ℤ) * ((1 : ℤ) : WithTop ℤ) = _
  rw [← WithTop.coe_mul, ← WithTop.coe_mul, ← WithTop.LinearOrderedAddCommGroup.coe_sub,
    WithTop.coe_inj]
  ring

/-- The explicit analytic repair of the cofactor at its removable
point. It keeps the raw formula at every other point. -/
def zetaMoebiusWronskianCofactorRegular (rho : NontrivialZetaZero) : ℂ → ℂ :=
  toMeromorphicNFAt (zetaMoebiusWronskianCofactor rho) rho.1

/-- The repaired cofactor is analytic at the selected zero for every
genuine multiplicity. -/
theorem analyticAt_zetaMoebiusWronskianCofactorRegular (rho : NontrivialZetaZero) :
    AnalyticAt ℂ (zetaMoebiusWronskianCofactorRegular rho) rho.1 := by
  apply (MeromorphicAt.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt
    (meromorphicAt_zetaMoebiusWronskianCofactor rho rho.1)).mp
  rw [meromorphicOrderAt_zetaMoebiusWronskianCofactor]
  have hm := analyticZetaZeroMultiplicity_positive rho
  exact_mod_cast (show (0 : ℤ) ≤ (analyticZetaZeroMultiplicity rho : ℤ) - 1 by omega)

/-- Filling the removable point preserves the literal cofactor
everywhere away from that one point. -/
theorem zetaMoebiusWronskianCofactorRegular_eq (rho : NontrivialZetaZero) {s : ℂ}
    (hs : s ≠ rho.1) :
    zetaMoebiusWronskianCofactorRegular rho s = zetaMoebiusWronskianCofactor rho s := by
  exact (MeromorphicAt.eqOn_compl_singleton_toMeromorphicNFAt
    (meromorphicAt_zetaMoebiusWronskianCofactor rho rho.1) (by simpa using hs)).symm

/-- The selected response has a double pole for every multiplicity,
including multiple zeros. -/
theorem meromorphicOrderAt_zetaMoebiusWronskian (rho : NontrivialZetaZero) :
    meromorphicOrderAt (zetaMoebiusWronskian rho) rho.1 = -2 := by
  change meromorphicOrderAt (zetaMoebiusWronskianCofactor rho *
    (deriv riemannZeta / riemannZeta ^ 2)) rho.1 = _
  rw [meromorphicOrderAt_mul (meromorphicAt_zetaMoebiusWronskianCofactor rho rho.1)
      ((meromorphicAt_riemannZeta rho.1).deriv.div ((meromorphicAt_riemannZeta rho.1).pow 2)),
    meromorphicOrderAt_zetaMoebiusWronskianCofactor,
    meromorphicOrderAt_div (meromorphicAt_riemannZeta rho.1).deriv
      ((meromorphicAt_riemannZeta rho.1).pow 2),
    meromorphicOrderAt_pow (meromorphicAt_riemannZeta rho.1),
    meromorphicOrderAt_deriv_riemannZeta_nontrivialZero,
    meromorphicOrderAt_riemannZeta_nontrivialZero]
  change (((analyticZetaZeroMultiplicity rho : ℤ) - 1 : ℤ) : WithTop ℤ) +
    ((((analyticZetaZeroMultiplicity rho : ℤ) - 1 : ℤ) : WithTop ℤ) -
      ((2 : ℤ) : WithTop ℤ) * ((analyticZetaZeroMultiplicity rho : ℤ) : WithTop ℤ)) =
      ((-2 : ℤ) : WithTop ℤ)
  rw [← WithTop.coe_mul, ← WithTop.LinearOrderedAddCommGroup.coe_sub,
    ← WithTop.coe_add, WithTop.coe_inj]
  ring

private theorem trailing_div {f g : ℂ → ℂ} {s : ℂ}
    (hf : MeromorphicAt f s) (hg : MeromorphicAt g s) :
    meromorphicTrailingCoeffAt (f / g) s =
      meromorphicTrailingCoeffAt f s / meromorphicTrailingCoeffAt g s := by
  rw [div_eq_mul_inv, hf.meromorphicTrailingCoeffAt_mul hg.inv,
    meromorphicTrailingCoeffAt_inv, div_eq_mul_inv]

/-- The multiplicity correction preserves the exact squared leading
phase of `zeta'`. -/
theorem meromorphicTrailingCoeffAt_zetaMoebiusWronskianCofactor (rho : NontrivialZetaZero) :
    meromorphicTrailingCoeffAt (zetaMoebiusWronskianCofactor rho) rho.1 =
      ((analyticZetaZeroMultiplicity rho : ℂ) * meromorphicTrailingCoeffAt riemannZeta rho.1) ^ 2 := by
  change meromorphicTrailingCoeffAt ((deriv riemannZeta) ^ 2 /
    ((fun s ↦ s - rho.1) ^ ((analyticZetaZeroMultiplicity rho : ℤ) - 1))) rho.1 = _
  rw [trailing_div ((meromorphicAt_riemannZeta rho.1).deriv.pow 2) (by fun_prop),
    (meromorphicAt_riemannZeta rho.1).deriv.meromorphicTrailingCoeffAt_pow,
    MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop),
    meromorphicTrailingCoeffAt_id_sub_const]
  simp [meromorphicTrailingCoeffAt_deriv_riemannZeta_nontrivialZero]

/-- The exact double-pole coefficient is `m^3` times zeta's leading
coefficient. In particular its phase is retained. -/
theorem meromorphicTrailingCoeffAt_zetaMoebiusWronskian (rho : NontrivialZetaZero) :
    meromorphicTrailingCoeffAt (zetaMoebiusWronskian rho) rho.1 =
      (analyticZetaZeroMultiplicity rho : ℂ) ^ 3 * meromorphicTrailingCoeffAt riemannZeta rho.1 := by
  have hz := meromorphicAt_riemannZeta rho.1
  have hc0 : meromorphicTrailingCoeffAt riemannZeta rho.1 ≠ 0 :=
    hz.meromorphicTrailingCoeffAt_ne_zero (by
      rw [meromorphicOrderAt_riemannZeta_nontrivialZero]
      exact WithTop.coe_ne_top)
  change meromorphicTrailingCoeffAt (zetaMoebiusWronskianCofactor rho *
    (deriv riemannZeta / riemannZeta ^ 2)) rho.1 = _
  rw [(meromorphicAt_zetaMoebiusWronskianCofactor rho rho.1).meromorphicTrailingCoeffAt_mul
      (hz.deriv.div (hz.pow 2)), trailing_div hz.deriv (hz.pow 2),
    hz.meromorphicTrailingCoeffAt_pow,
    meromorphicTrailingCoeffAt_zetaMoebiusWronskianCofactor,
    meromorphicTrailingCoeffAt_deriv_riemannZeta_nontrivialZero]
  field_simp

/-- The selected differential source is nonzero; no simple-zero
assumption or numerical lower bound for `zeta'` is used. -/
theorem meromorphicTrailingCoeffAt_zetaMoebiusWronskian_ne_zero (rho : NontrivialZetaZero) :
    meromorphicTrailingCoeffAt (zetaMoebiusWronskian rho) rho.1 ≠ 0 :=
  (meromorphicAt_zetaMoebiusWronskian rho rho.1).meromorphicTrailingCoeffAt_ne_zero (by
    rw [meromorphicOrderAt_zetaMoebiusWronskian]
    norm_num)

/-- The punctured double-pole limit gives the literal nonzero zeta
source coefficient, with every multiplicity accounted for. -/
theorem tendsto_zetaMoebiusWronskian_mul_sq (rho : NontrivialZetaZero) :
    Tendsto (fun s ↦ (s - rho.1) ^ 2 * zetaMoebiusWronskian rho s) (𝓝[≠] rho.1)
      (𝓝 ((analyticZetaZeroMultiplicity rho : ℂ) ^ 3 *
        meromorphicTrailingCoeffAt riemannZeta rho.1)) := by
  change Tendsto ((fun s : ℂ ↦ s - rho.1) ^ (2 : ℕ) * zetaMoebiusWronskian rho) _ _
  have h := (meromorphicAt_zetaMoebiusWronskian rho rho.1).tendsto_nhds_meromorphicTrailingCoeffAt
  simpa [meromorphicOrderAt_zetaMoebiusWronskian,
    meromorphicTrailingCoeffAt_zetaMoebiusWronskian, smul_eq_mul] using h

/-- Away from the actual pole and zeros, the response is exactly the
coupled logarithmic derivative divided by the excess multiplicity factor. -/
theorem zetaMoebiusWronskian_eq_coupled (rho : NontrivialZetaZero) {s : ℂ}
    (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    zetaMoebiusWronskian rho s =
      (deriv riemannZeta s * deriv (fun z ↦ -logDeriv riemannZeta z) s -
        deriv (deriv riemannZeta) s * (-logDeriv riemannZeta s)) /
          (s - rho.1) ^ ((analyticZetaZeroMultiplicity rho : ℤ) - 1) := by
  rw [deriv_coupled_neg_logDeriv (analyticOn_riemannZeta s (by simpa using hs)) hz]
  simp only [zetaMoebiusWronskian, zetaMoebiusWronskianCofactor, div_eq_mul_inv]
  ring

/-- The filled cofactor is analytic at every point except zeta's
genuine pole at one. The selected zero creates no extra singularity. -/
theorem analyticAt_zetaMoebiusWronskianCofactorRegular_of_ne_one (rho : NontrivialZetaZero)
    {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ (zetaMoebiusWronskianCofactorRegular rho) s := by
  by_cases hr : s = rho.1
  · subst s
    exact analyticAt_zetaMoebiusWronskianCofactorRegular rho
  have he : zetaMoebiusWronskianCofactorRegular rho =ᶠ[𝓝 s] zetaMoebiusWronskianCofactor rho := by
    filter_upwards [eventually_ne_nhds hr] with z hz
    exact zetaMoebiusWronskianCofactorRegular_eq rho hz
  rw [analyticAt_congr he]
  have hz : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s (by simpa using hs)
  have hne : s - rho.1 ≠ 0 := sub_ne_zero.mpr hr
  change AnalyticAt ℂ ((deriv riemannZeta) ^ 2 /
    ((fun z ↦ z - rho.1) ^ ((analyticZetaZeroMultiplicity rho : ℤ) - 1))) s
  exact (hz.deriv.pow 2).div ((analyticAt_id.sub analyticAt_const).zpow hne) (zpow_ne_zero _ hne)

/-- Away from the selected point, the multiplicity correction is a
nonvanishing analytic factor and does not alter the derivative's order. -/
theorem meromorphicOrderAt_zetaMoebiusWronskianCofactor_of_ne (rho : NontrivialZetaZero)
    {s : ℂ} (hs : s ≠ rho.1) :
    meromorphicOrderAt (zetaMoebiusWronskianCofactor rho) s =
      2 * meromorphicOrderAt (deriv riemannZeta) s := by
  have hb : AnalyticAt ℂ (fun z ↦ z - rho.1) s := by fun_prop
  have hbo : meromorphicOrderAt (fun z ↦ z - rho.1) s = 0 := by
    rw [hb.meromorphicOrderAt_eq, hb.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hs)]
    simp
  change meromorphicOrderAt ((deriv riemannZeta) ^ 2 /
    ((fun z ↦ z - rho.1) ^ ((analyticZetaZeroMultiplicity rho : ℤ) - 1))) s = _
  rw [meromorphicOrderAt_div ((meromorphicAt_riemannZeta s).deriv.pow 2) (by fun_prop),
    meromorphicOrderAt_pow (meromorphicAt_riemannZeta s).deriv,
    meromorphicOrderAt_zpow hb.meromorphicAt, hbo]
  simp

private theorem order_wronskian_of_ne (rho : NontrivialZetaZero) {s : ℂ} (hs : s ≠ rho.1)
    {n : ℤ} (hn : (n : ℂ) ≠ 0) (ho : meromorphicOrderAt riemannZeta s = n) :
    meromorphicOrderAt (zetaMoebiusWronskian rho) s = ((n - 3 : ℤ) : WithTop ℤ) := by
  have hd := meromorphicOrderAt_deriv_eq_sub_one hn ho
  have hz := meromorphicAt_riemannZeta s
  change meromorphicOrderAt (zetaMoebiusWronskianCofactor rho *
    (deriv riemannZeta / riemannZeta ^ 2)) s = _
  rw [meromorphicOrderAt_mul (meromorphicAt_zetaMoebiusWronskianCofactor rho s)
      (hz.deriv.div (hz.pow 2)), meromorphicOrderAt_zetaMoebiusWronskianCofactor_of_ne rho hs,
    meromorphicOrderAt_div hz.deriv (hz.pow 2), meromorphicOrderAt_pow hz, ho, hd]
  change ((2 : ℤ) : WithTop ℤ) * ((n - 1 : ℤ) : WithTop ℤ) +
    (((n - 1 : ℤ) : WithTop ℤ) - ((2 : ℤ) : WithTop ℤ) * (n : WithTop ℤ)) = _
  rw [← WithTop.coe_mul, ← WithTop.coe_mul, ← WithTop.LinearOrderedAddCommGroup.coe_sub,
    ← WithTop.coe_add, WithTop.coe_inj]
  ring

/-- Every other nontrivial zero has order `k - 3`, hence at most a
double pole, irrespective of its actual multiplicity or distance. -/
theorem meromorphicOrderAt_zetaMoebiusWronskian_other_zero (rho tau : NontrivialZetaZero)
    (hne : tau.1 ≠ rho.1) :
    meromorphicOrderAt (zetaMoebiusWronskian rho) tau.1 =
      ((analyticZetaZeroMultiplicity tau : ℤ) - 3 : ℤ) := by
  apply order_wronskian_of_ne rho hne _ (meromorphicOrderAt_riemannZeta_nontrivialZero tau)
  have hm := analyticZetaZeroMultiplicity_positive tau
  exact_mod_cast (show (analyticZetaZeroMultiplicity tau : ℤ) ≠ 0 by omega)

/-- The cofactor has only the expected fourth-order pole at one. -/
theorem meromorphicOrderAt_zetaMoebiusWronskianCofactor_one (rho : NontrivialZetaZero) :
    meromorphicOrderAt (zetaMoebiusWronskianCofactor rho) 1 = -4 := by
  rw [meromorphicOrderAt_zetaMoebiusWronskianCofactor_of_ne rho rho.2.2.2.symm]
  have hd : meromorphicOrderAt (deriv riemannZeta) 1 = ((-2 : ℤ) : WithTop ℤ) := by
    simpa using meromorphicOrderAt_deriv_eq_sub_one (by norm_num : ((-1 : ℤ) : ℂ) ≠ 0)
      meromorphicOrderAt_riemannZeta_one
  rw [hd]
  change ((2 : ℤ) : WithTop ℤ) * ((-2 : ℤ) : WithTop ℤ) = ((-4 : ℤ) : WithTop ℤ)
  rw [← WithTop.coe_mul]
  rfl

/-- The complete response has a fourth-order pole at one. This
explicit exceptional pole can be included in the finite cancellation. -/
theorem meromorphicOrderAt_zetaMoebiusWronskian_one (rho : NontrivialZetaZero) :
    meromorphicOrderAt (zetaMoebiusWronskian rho) 1 = -4 := by
  simpa using order_wronskian_of_ne rho rho.2.2.2.symm
    (by norm_num : ((-1 : ℤ) : ℂ) ≠ 0) meromorphicOrderAt_riemannZeta_one

end

end RiemannGaussian
