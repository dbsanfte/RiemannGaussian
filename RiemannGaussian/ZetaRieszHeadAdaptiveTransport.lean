import RiemannGaussian.ZetaRieszHeadAdaptive
import RiemannGaussian.ZetaRieszShiftedHeadBudget

/-!
# The actual adaptive head and its complete source transport

Every fixed filter retains all shifts. The independent geometric estimate
controls exactly the high cofactor orders 8k>=7M; the remaining signed
carrier and its whole negative multiplicity source are preserved.
-/

namespace RiemannGaussian.ZetaRieszHeadAdaptiveTransport
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszHeadOrders ZetaRieszHeadAdaptive
open ZetaRieszShiftedHeadBudget ZetaRieszAnnulusJoint ZetaExposedPrimeMoments
open ZetaPrimeCofactorCompletion

/-- The exact geometric rate for the enlarged high-order range. -/
def adaptiveRate : ℝ := Real.exp (-(7 / 9216 : ℝ))

/-- The enlarged range still has a strict positive geometric saving. -/
theorem adaptiveRate_bounds : 0 < adaptiveRate ∧ adaptiveRate < 1 :=
  ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by norm_num)⟩

/-- The complete physical head restricted only in cofactor factorial
order, now to eight k at least seven M for every original filter shift. -/
def adaptiveHead (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ j ∈ P.support, -(P.coeff j * ((N + j + 1 : ℕ) : ℂ) /
      (SquarefreeVaughanLogSource.length u N : ℂ)) *
    adaptiveHighConvolution (intermediatePrimes u N) (N + j + 1) (3 / 2 + Complex.I * y)

/-- The enlarged-range bound retains every fixed filter coefficient
and its exact source-normalization and factorial-shift cost. -/
def adaptiveHeadCost (P : Polynomial ℂ) (u : ℝ) : ℝ :=
  (u * zetaMoebiusLogMajorantMass (1025 / 1024) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n) *
    ∑ j ∈ P.support, ‖P.coeff j‖ * u⁻¹ ^ (j + 1) * (j + 2 : ℝ) ^ 2

/-- The whole larger high head is independently bounded at the
actual cutoff, for every fixed polynomial and uniformly in the ordinate. -/
theorem norm_adaptiveHead_le (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ))) (hN : 3 ≤ N) :
    ‖(u : ℂ) ^ (N + 1) * adaptiveHead P u y N‖ ≤
      ((N + 1 : ℝ) ^ 2 * adaptiveRate ^ N) * adaptiveHeadCost P u := by
  have hmass := zetaMoebiusLogMajorantMass_nonneg (1025 / 1024)
  have hZ : 0 ≤ ∑' n, zetaPrimeExpWeight (1025 / 1024) n := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  unfold adaptiveHead adaptiveHeadCost
  apply norm_fixedFilter_of_shiftedBounds P _ N hu (one_le_length u N)
    (by positivity) adaptiveRate_bounds.1.le adaptiveRate_bounds.2.le
  intro j _
  have hb := norm_actual_adaptiveHighConvolution N (N + j + 1) y hu huh hN (by omega)
  have he : Real.exp (-(7 / 9216 : ℝ) * (N + j + 1 : ℕ)) = adaptiveRate ^ (N + j + 1) := by
    rw [mul_comm, Real.exp_nat_mul]
    rfl
  rw [he] at hb
  simpa only [Nat.cast_add, Nat.cast_one] using hb

/-- The enlarged high-head component tends to zero without any zero
or cancellation premise. This is an estimate for the actual fixed filter. -/
theorem tendsto_adaptiveHead (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * adaptiveHead P u y N) atTop (nhds 0) := by
  apply squeeze_zero_norm' (by
    filter_upwards [eventually_ge_atTop 3] with N hN
    exact norm_adaptiveHead_le P N y hu huh hN)
  simpa only [zero_mul] using (tendsto_quadratic_geometric
    adaptiveRate_bounds.1.le adaptiveRate_bounds.2).mul_const (adaptiveHeadCost P u)

/-- All lower cofactor orders retain their exact complex correlations
after the larger independent deletion, with every filter shift present. -/
def adaptiveRemainingHead (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ j ∈ P.support, -(P.coeff j * ((N + j + 1 : ℕ) : ℂ) /
      (SquarefreeVaughanLogSource.length u N : ℂ)) *
    ∑ k ∈ (Finset.range (N + j + 2)).filter (fun k => 8 * k < 7 * (N + j + 1)),
      cofactorMoment (intermediatePrimes u N) k (3 / 2 + Complex.I * y) *
        ordinaryPrimeMoment (N + j + 1 - k) (3 / 2 + Complex.I * y)

/-- The whole literal head partitions exactly at the new seven-eighths
order boundary, preserving both prime variables and every original phase. -/
theorem completedHead_eq_adaptive_split (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) :
    completedCofactorHead (intermediatePrimes u N) P N (3 / 2 + Complex.I * y)
      (SquarefreeVaughanLogSource.length u N) = adaptiveRemainingHead P u y N + adaptiveHead P u y N := by
  rw [completedHead_eq_convolution _ (fun a ha =>
    ((mem_intermediatePrimes u N a).mp ha).1.pos) P N (by norm_num)]
  simp only [adaptiveRemainingHead, adaptiveHead, adaptiveHighConvolution, adaptiveHighOrders,
    ← Finset.sum_add_distrib, ← mul_add]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : 7 * (N + j + 1) ≤ 8 * k
  · simp [hk, not_lt.mpr hk]
  · simp [hk, lt_of_not_ge hk]

/-- The full signed carrier after the larger independent head-order
deletion, with its original finite arithmetic components unchanged. -/
def adaptiveJoint (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  ZetaRieszCentralPair.centralUnpairedResponse P u y N + adaptiveRemainingHead P u y N +
    ZetaRieszCentralPair.centralPairResponse P u y N

/-- The exact whole-carrier difference is the independently paid
enlarged high head. No sign or phase is dropped from the remaining sum. -/
theorem centralJoint_sub_adaptiveJoint (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) :
    ZetaRieszCentralPair.centralJoint P u y N - adaptiveJoint P u y N = adaptiveHead P u y N := by
  rw [ZetaRieszCentralPair.centralJoint, adaptiveJoint, completedHead_eq_adaptive_split]
  ring

/-- The larger whole-carrier deletion has an explicit independent
geometric allowance from order three onward, uniformly in height. -/
theorem norm_centralJoint_sub_adaptiveJoint_le (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ))) (hN : 3 ≤ N) :
    ‖(u : ℂ) ^ (N + 1) *
      (ZetaRieszCentralPair.centralJoint P u y N - adaptiveJoint P u y N)‖ ≤
      ((N + 1 : ℝ) ^ 2 * adaptiveRate ^ N) * adaptiveHeadCost P u := by
  rw [centralJoint_sub_adaptiveJoint]
  exact norm_adaptiveHead_le P N y hu huh hN

/-- The entire negative-multiplicity source survives the larger
independent deletion on the annular interval. The joint floor stays open. -/
theorem tendsto_adaptiveJoint_exposed (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      adaptiveJoint 1 (3 / 2 - rho.1.re) rho.1.im N)
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : (0 : ℝ) < 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have h := (ZetaRieszCentralPair.tendsto_centralJoint_exposed rho hrho hexposed huh).sub
    (tendsto_adaptiveHead 1 rho.1.im hu huh)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  have he := centralJoint_sub_adaptiveJoint 1 (3 / 2 - rho.1.re) rho.1.im N
  rw [← he]
  ring

end
end RiemannGaussian.ZetaRieszHeadAdaptiveTransport
