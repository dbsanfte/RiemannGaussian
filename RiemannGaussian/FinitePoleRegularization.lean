/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierPoleResidues
import RiemannGaussian.RiemannXiSuzukiSpectralUpperContourProjection

/-!
# Removing complete finite Laurent principal parts

An arbitrary-order pole requires the whole numerator Taylor jet, not
only its residue. We construct that principal part, prove local analytic
removability after subtraction, and patch finitely many such poles
simultaneously. The actual mixed Suzuki carrier numerators instantiate
the local theorem with their genuine analytic denominator orders.
-/

open Complex Filter Metric Set Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

/-- The full finite negative Laurent part of `F(z)/(z-c)^m`, written
with its common denominator to retain every Taylor coefficient. -/
def poleTaylorPrincipalPart (m : ℕ) (F : ℂ → ℂ) (c z : ℂ) : ℂ :=
  (∑ k ∈ Finset.range m,
    (z - c) ^ k / (k.factorial : ℂ) * iteratedDeriv k F c) / (z - c) ^ m

/-- The complete Taylor quotient is exactly the finite negative Laurent
sum away from its center, with the same coefficient ordering. -/
theorem poleTaylorPrincipalPart_eq_sum_zpow_of_ne (m : ℕ) (F : ℂ → ℂ)
    {c z : ℂ} (hz : z ≠ c) :
    poleTaylorPrincipalPart m F c z =
      ∑ k ∈ Finset.range m,
        (iteratedDeriv k F c / (k.factorial : ℂ)) * (z - c) ^ ((k : ℤ) - (m : ℤ)) := by
  rw [poleTaylorPrincipalPart, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [zpow_sub₀ (sub_ne_zero.mpr hz)]
  simp only [zpow_natCast]
  ring

/-- The residue coefficient of the complete principal part. Order zero
has no negative Laurent terms and therefore has residue zero. -/
def poleTaylorResidue (m : ℕ) (F : ℂ → ℂ) (c : ℂ) : ℂ :=
  if m = 0 then 0 else iteratedDeriv (m - 1) F c / ((m - 1).factorial : ℂ)

/-- A complete Laurent principal part is analytic away from its center. -/
theorem analyticAt_poleTaylorPrincipalPart_of_ne (m : ℕ) (F : ℂ → ℂ)
    {c z : ℂ} (hz : z ≠ c) : AnalyticAt ℂ (poleTaylorPrincipalPart m F c) z := by
  unfold poleTaylorPrincipalPart
  apply AnalyticAt.div
  · apply Finset.analyticAt_fun_sum
    intro k _hk
    fun_prop
  · fun_prop
  · exact pow_ne_zero _ (sub_ne_zero.mpr hz)

/-- Taylor's theorem at an arbitrary center gives an analytic remainder
after subtracting the complete negative Laurent part of a pole model. -/
theorem exists_analytic_poleTaylor_remainder {F : ℂ → ℂ} {c : ℂ}
    (hF : AnalyticAt ℂ F c) (m : ℕ) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H c ∧
      (fun z => F z / (z - c) ^ m - poleTaylorPrincipalPart m F c z) =ᶠ[𝓝[≠] c] H := by
  have hshift : AnalyticAt ℂ (fun w => F (w + c)) 0 := by
    have hg : AnalyticAt ℂ (fun w : ℂ => w + c) 0 := by fun_prop
    exact (show AnalyticAt ℂ F (0 + c) by simpa only [zero_add] using hF).comp
      (f := fun w : ℂ => w + c) (x := 0) hg
  obtain ⟨H, hH, hTaylor⟩ := hshift.exists_eventuallyEq_sum_add_pow_mul m
  have hback : AnalyticAt ℂ (fun z => H (z - c)) c := by
    have hg : AnalyticAt ℂ (fun z : ℂ => z - c) c := by fun_prop
    exact (show AnalyticAt ℂ H (c - c) by simpa only [sub_self] using hH).comp
      (f := fun z : ℂ => z - c) (x := c) hg
  have ht : Tendsto (fun z : ℂ => z - c) (𝓝 c) (𝓝 0) := by
    have hc : Continuous (fun z : ℂ => z - c) := by fun_prop
    simpa only [sub_self] using hc.continuousAt.tendsto (x := c)
  refine ⟨fun z => H (z - c), hback, ?_⟩
  filter_upwards [(ht.eventually hTaylor).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hzc
  have he : F z = (∑ k ∈ Finset.range m,
      (z - c) ^ k / (k.factorial : ℂ) * iteratedDeriv k F c) +
        (z - c) ^ m * H (z - c) := by
    simpa only [sub_add_cancel, smul_eq_mul, iteratedDeriv_comp_add_const, zero_add] using hz
  rw [he]
  unfold poleTaylorPrincipalPart
  field_simp [pow_ne_zero m (sub_ne_zero.mpr hzc)]
  ring

/-- Any function with the indicated genuine punctured pole model becomes
locally analytic after the full principal part is subtracted. -/
theorem exists_analytic_remainder_of_pole_model {f F : ℂ → ℂ} {c : ℂ}
    (hF : AnalyticAt ℂ F c) (m : ℕ)
    (hmodel : f =ᶠ[𝓝[≠] c] fun z => F z / (z - c) ^ m) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H c ∧
      (fun z => f z - poleTaylorPrincipalPart m F c z) =ᶠ[𝓝[≠] c] H := by
  obtain ⟨H, hH, he⟩ := exists_analytic_poleTaylor_remainder hF m
  refine ⟨H, hH, ?_⟩
  filter_upwards [hmodel, he] with z hz hrem
  simpa only [hz] using hrem

/-- The complete finite principal sum for arbitrary centers, orders,
and analytic pole numerators. No simplicity assumption is made. -/
def finitePolePrincipalSum (S : Finset ℂ) (order : ℂ → ℕ)
    (numerator : ℂ → ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ c ∈ S, poleTaylorPrincipalPart (order c) (numerator c) c z

/-- The finite principal sum is analytic away from all its centers. -/
theorem analyticAt_finitePolePrincipalSum_of_not_mem (S : Finset ℂ)
    (order : ℂ → ℕ) (numerator : ℂ → ℂ → ℂ) {z : ℂ} (hz : z ∉ S) :
    AnalyticAt ℂ (finitePolePrincipalSum S order numerator) z := by
  apply Finset.analyticAt_fun_sum
  intro c hc
  exact analyticAt_poleTaylorPrincipalPart_of_ne _ _ (fun h => hz (h ▸ hc))

/-- A finite collection of complete pole models yields an actual
analytic representative after subtracting all their principal parts.
The original function is retained everywhere outside the finite set. -/
theorem exists_finitePole_analytic_regularization (U : Set ℂ) (S : Finset ℂ)
    (f : ℂ → ℂ) (order : ℂ → ℕ) (numerator : ℂ → ℂ → ℂ)
    (hSU : ∀ c ∈ S, c ∈ U)
    (hoff : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ f z)
    (hnum : ∀ c ∈ S, AnalyticAt ℂ (numerator c) c)
    (hmodel : ∀ c ∈ S, f =ᶠ[𝓝[≠] c] fun z => numerator c z / (z - c) ^ order c) :
    ∃ H : ℂ → ℂ, (∀ z ∈ U, AnalyticAt ℂ H z) ∧
      (∀ z ∉ S, H z = f z - finitePolePrincipalSum S order numerator z) := by
  apply exists_analyticAtOn_of_finite_removable U S
    (fun z => f z - finitePolePrincipalSum S order numerator z) hSU
  · intro z hzU hzS
    exact (hoff z hzU hzS).sub (analyticAt_finitePolePrincipalSum_of_not_mem S order numerator hzS)
  · intro c hc
    obtain ⟨H, hH, hrem⟩ := exists_analytic_remainder_of_pole_model
      (hnum c hc) (order c) (hmodel c hc)
    have hrest : AnalyticAt ℂ (finitePolePrincipalSum (S.erase c) order numerator) c :=
      analyticAt_finitePolePrincipalSum_of_not_mem _ _ _ (Finset.notMem_erase c S)
    refine ⟨fun z => H z - finitePolePrincipalSum (S.erase c) order numerator z,
      hH.sub hrest, ?_⟩
    filter_upwards [hrem] with z hz
    have hsum : finitePolePrincipalSum S order numerator z =
        poleTaylorPrincipalPart (order c) (numerator c) c z +
          finitePolePrincipalSum (S.erase c) order numerator z := by
      exact (Finset.add_sum_erase S (fun a => poleTaylorPrincipalPart (order a) (numerator a) a z) hc).symm
    rw [hsum]
    linear_combination hz

/-- The full Laurent principal part of one actual mixed Suzuki carrier
pole, using the genuine denominator order and original ordered nodes. -/
def suzukiXiMixedCarrierPolePrincipalPart (rho sigma : NontrivialZetaZero)
    (c z : ℂ) : ℂ :=
  poleTaylorPrincipalPart (analyticOrderNatAt suzukiXiEValue c)
    (suzukiXiMixedCarrierPoleNumerator rho sigma c) c z

/-- Subtracting the complete principal part of an actual mixed carrier
pole leaves an analytic local representative, including at multiple poles. -/
theorem exists_suzukiXiMixedCarrierPole_analytic_remainder
    (rho sigma : NontrivialZetaZero) {c : ℂ} (hxi : riemannXiSpectral c ≠ 0) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H c ∧
      (fun z => suzukiXiZeroCarrier z /
          ((z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
            (z - zetaSpectralCoordinate sigma.1)) -
        suzukiXiMixedCarrierPolePrincipalPart rho sigma c z) =ᶠ[𝓝[≠] c] H := by
  apply exists_analytic_remainder_of_pole_model
    (analyticAt_suzukiXiMixedCarrierPoleNumerator rho sigma hxi)
  filter_upwards [suzukiXiZeroCarrier_eventually_eq_power_pole c] with z hz
  rw [hz]
  unfold suzukiXiMixedCarrierPoleNumerator
  ring

end
end RiemannGaussian
