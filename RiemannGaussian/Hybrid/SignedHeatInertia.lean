import RiemannGaussian.HermitianRankTrace.HermitianPosPart
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Exact Hermitian inertia from signed spectral heat

This module retains the continuous heat transform of the complete spectrum of
a finite Hermitian matrix.  For a Hermitian matrix `A` with eigenvalues
`lambda_i`, the spectral functional calculus defines

`heatFlow(A,u) = exp(-u*A^2)`

and its sign-bearing companion

`signedHeatFlow(A,u) = A*exp(-u*A^2)`.

Their real traces are the finite sums

`sum_i exp(-u*lambda_i^2)` and
`sum_i lambda_i*exp(-u*lambda_i^2)`.

Lean proves the scalar Mellin--Gaussian integral, its genuine positive-time
integrability, the finite sum--integral exchange, and the exact formula

`(1/sqrt pi) * integral_0^infinity u^(-1/2) J_A(u) du = n_+(A)-n_-(A)`.

The ordinary heat trace tends to the zero index.  Combining both observables
therefore reconstructs the positive inertia exactly.  No low-moment,
rank--trace, eta-arithmetic, or zero-location assumption enters this finite
spectral theorem.
-/

open Matrix Finset MeasureTheory Set Filter Topology
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian.HermitianRankTrace

noncomputable section

/-! ## The scalar signed heat transform -/

/-- The three-valued real spectral sign, written explicitly so the zero
eigenvalue convention used by the heat integral is visible. -/
def realSpectralSign (x : ℝ) : ℝ :=
  if 0 < x then 1 else if x < 0 then -1 else 0

/-- The signed Mellin--Gaussian heat integral recovers the sign of every real
spectral value, including the zero value. -/
theorem signedHeatScalarIntegral_eq_sign (x : ℝ) :
    (1 / Real.sqrt Real.pi) *
        ∫ u : ℝ in Set.Ioi 0,
          u ^ (-(1 / 2 : ℝ)) *
            (x * Real.exp (-u * x ^ 2)) =
      realSpectralSign x := by
  by_cases hx : x = 0
  · simp [hx, realSpectralSign]
  · have hxSq : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (1 / 2 : ℝ)) (r := x ^ 2) (by norm_num) hxSq
    have hbase :
        (∫ u : ℝ in Set.Ioi 0,
          u ^ (-(1 / 2 : ℝ)) * Real.exp (-u * x ^ 2)) =
          Real.sqrt Real.pi / |x| := by
      calc
        (∫ u : ℝ in Set.Ioi 0,
            u ^ (-(1 / 2 : ℝ)) * Real.exp (-u * x ^ 2)) =
            ∫ u : ℝ in Set.Ioi 0,
              u ^ ((1 / 2 : ℝ) - 1) *
                Real.exp (-((x ^ 2) * u)) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro u _hu
          have hpow : (-(1 / 2 : ℝ)) = (1 / 2 : ℝ) - 1 := by
            norm_num
          have hexp : Real.exp (-u * x ^ 2) =
              Real.exp (-(x ^ 2 * u)) := by
            congr 1
            ring
          change u ^ (-(1 / 2 : ℝ)) * Real.exp (-u * x ^ 2) =
            u ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(x ^ 2 * u))
          rw [hpow, hexp]
        _ = (1 / (x ^ 2)) ^ (1 / 2 : ℝ) *
              Real.Gamma (1 / 2 : ℝ) := hgamma
        _ = Real.sqrt Real.pi / |x| := by
          rw [Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow]
          rw [Real.sqrt_div (by positivity), Real.sqrt_one,
            Real.sqrt_sq_eq_abs]
          field_simp
    rw [show (∫ u : ℝ in Set.Ioi 0,
          u ^ (-(1 / 2 : ℝ)) *
            (x * Real.exp (-u * x ^ 2))) =
        x * (∫ u : ℝ in Set.Ioi 0,
          u ^ (-(1 / 2 : ℝ)) * Real.exp (-u * x ^ 2)) by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _hu
      ring]
    rw [hbase]
    unfold realSpectralSign
    rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · rw [if_neg (not_lt.mpr hxneg.le), if_pos hxneg,
        abs_of_neg hxneg]
      have hsqrt : Real.sqrt Real.pi ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
      field_simp
    · rw [if_pos hxpos, abs_of_pos hxpos]
      have hsqrt : Real.sqrt Real.pi ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
      field_simp

/-- The signed scalar heat integrand is genuinely integrable on positive
proper time. -/
theorem signedHeatScalarIntegrableOn (x : ℝ) :
    IntegrableOn
      (fun u : ℝ ↦
        u ^ (-(1 / 2 : ℝ)) *
          (x * Real.exp (-u * x ^ 2))) (Set.Ioi 0) := by
  by_cases hx : x = 0
  · simp [hx]
  · have hxSq : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    have hbase := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (-(1 / 2 : ℝ))) (b := x ^ 2)
      (by norm_num) (by norm_num) hxSq
    have hfun :
        (fun u : ℝ ↦
          u ^ (-(1 / 2 : ℝ)) *
            (x * Real.exp (-u * x ^ 2))) =
        (fun u : ℝ ↦
          (u ^ (-(1 / 2 : ℝ)) *
            Real.exp (-(x ^ 2) * u ^ (1 : ℝ))) * x) := by
      funext u
      rw [Real.rpow_one]
      rw [show -u * x ^ 2 = -(x ^ 2 * u) by ring]
      ring_nf
    rw [hfun]
    exact hbase.mul_const x

/-- Summing the three-valued spectral sign gives the real positive count
minus the real negative count. -/
theorem sum_realSpectralSign_eq_card_pos_sub_card_neg
    {n : Type*} [Fintype n] (eigenvalue : n → ℝ) :
    ∑ i, realSpectralSign (eigenvalue i) =
      ((#{i | 0 < eigenvalue i} : ℕ) : ℝ) -
        ((#{i | eigenvalue i < 0} : ℕ) : ℝ) := by
  classical
  calc
    (∑ i, realSpectralSign (eigenvalue i)) =
        ∑ i, ((if 0 < eigenvalue i then 1 else 0) -
          (if eigenvalue i < 0 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      unfold realSpectralSign
      by_cases hpos : 0 < eigenvalue i
      · have hneg : ¬eigenvalue i < 0 := not_lt.mpr hpos.le
        simp [hpos, hneg]
      · by_cases hneg : eigenvalue i < 0
        · simp [hpos, hneg]
        · simp [hpos, hneg]
    _ = (∑ i, if 0 < eigenvalue i then 1 else 0) -
        (∑ i, if eigenvalue i < 0 then 1 else 0) := by
      rw [Finset.sum_sub_distrib]
    _ = ((#{i | 0 < eigenvalue i} : ℕ) : ℝ) -
        ((#{i | eigenvalue i < 0} : ℕ) : ℝ) := by
      simp only [Finset.sum_boole]

/-! ## Hermitian spectral heat flow -/

variable {K : Type*} [RCLike K]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The zero index of a Hermitian matrix, counted with spectral
multiplicity. -/
def zeroIndex {A : Matrix n n K} (hA : A.IsHermitian) : ℕ :=
  #{i | hA.eigenvalues i = 0}

/-- The ordinary Hermitian heat flow obtained by applying
`x ↦ exp(-u*x^2)` to the complete real spectrum. -/
def hermitianHeatFlow {A : Matrix n n K} (hA : A.IsHermitian) (u : ℝ) :
    Matrix n n K :=
  specMap hA (fun x ↦ Real.exp (-u * x ^ 2))

/-- The signed Hermitian heat flow obtained by applying
`x ↦ x*exp(-u*x^2)` to the complete real spectrum. -/
def hermitianSignedHeatFlow {A : Matrix n n K} (hA : A.IsHermitian)
    (u : ℝ) : Matrix n n K :=
  specMap hA (fun x ↦ x * Real.exp (-u * x ^ 2))

/-- The real trace of the complete Hermitian heat flow. -/
def hermitianHeatTrace {A : Matrix n n K} (hA : A.IsHermitian)
    (u : ℝ) : ℝ :=
  rtrace (hermitianHeatFlow hA u)

/-- The real trace of the sign-bearing Hermitian heat flow. -/
def hermitianSignedHeatCurrent {A : Matrix n n K} (hA : A.IsHermitian)
    (u : ℝ) : ℝ :=
  rtrace (hermitianSignedHeatFlow hA u)

/-- The ordinary Hermitian heat flow is Hermitian at every real heat time. -/
theorem hermitianHeatFlow_isHermitian {A : Matrix n n K}
    (hA : A.IsHermitian) (u : ℝ) :
    (hermitianHeatFlow hA u).IsHermitian :=
  specMap_isHermitian hA _

/-- The ordinary Hermitian heat flow is positive semidefinite at every real
heat time. -/
theorem hermitianHeatFlow_posSemidef {A : Matrix n n K}
    (hA : A.IsHermitian) (u : ℝ) :
    (hermitianHeatFlow hA u).PosSemidef := by
  unfold hermitianHeatFlow
  exact specMap_posSemidef hA (fun _i ↦ (Real.exp_pos _).le)

/-- The signed Hermitian heat flow remains Hermitian at every heat time. -/
theorem hermitianSignedHeatFlow_isHermitian {A : Matrix n n K}
    (hA : A.IsHermitian) (u : ℝ) :
    (hermitianSignedHeatFlow hA u).IsHermitian :=
  specMap_isHermitian hA _

/-- The ordinary heat trace is the complete finite eigenvalue heat sum. -/
theorem hermitianHeatTrace_eq_sum_eigenvalues {A : Matrix n n K}
    (hA : A.IsHermitian) (u : ℝ) :
    hermitianHeatTrace hA u =
      ∑ i, Real.exp (-u * (hA.eigenvalues i) ^ 2) := by
  unfold hermitianHeatTrace hermitianHeatFlow
  exact rtrace_specMap hA _

/-- The signed heat current is the complete finite sign-bearing eigenvalue
heat sum. -/
theorem hermitianSignedHeatCurrent_eq_sum_eigenvalues
    {A : Matrix n n K} (hA : A.IsHermitian) (u : ℝ) :
    hermitianSignedHeatCurrent hA u =
      ∑ i, hA.eigenvalues i *
        Real.exp (-u * (hA.eigenvalues i) ^ 2) := by
  unfold hermitianSignedHeatCurrent hermitianSignedHeatFlow
  exact rtrace_specMap hA _

/-- The complete spectral heat family obeys the exact additive semigroup
law. -/
theorem hermitianHeatFlow_add {A : Matrix n n K} (hA : A.IsHermitian)
    (u v : ℝ) :
    hermitianHeatFlow hA (u + v) =
      hermitianHeatFlow hA u * hermitianHeatFlow hA v := by
  unfold hermitianHeatFlow
  rw [← specMap_mul]
  congr 1
  funext x
  rw [Pi.mul_apply, ← Real.exp_add]
  congr 1
  ring

/-- The signed heat flow is the original matrix multiplied by its ordinary
spectral heat flow. -/
theorem hermitianSignedHeatFlow_eq_mul {A : Matrix n n K}
    (hA : A.IsHermitian) (u : ℝ) :
    hermitianSignedHeatFlow hA u = A * hermitianHeatFlow hA u := by
  unfold hermitianSignedHeatFlow hermitianHeatFlow
  calc
    specMap hA (fun x ↦ x * Real.exp (-u * x ^ 2)) =
        specMap hA (fun x : ℝ ↦ x) *
        specMap hA (fun x ↦ Real.exp (-u * x ^ 2)) := by
      have hmul := specMap_mul hA (fun x : ℝ ↦ x)
        (fun x ↦ Real.exp (-u * x ^ 2))
      change specMap hA (fun x : ℝ ↦
          x * Real.exp (-u * x ^ 2)) =
        specMap hA (fun x : ℝ ↦ x) *
          specMap hA (fun x ↦ Real.exp (-u * x ^ 2)) at hmul
      exact hmul
    _ = A * specMap hA (fun x ↦ Real.exp (-u * x ^ 2)) := by
      have hid := specMap_id hA
      change specMap hA (fun x : ℝ ↦ x) = A at hid
      rw [hid]

/-! ## Exact inertia recovery -/

/-- The singularly weighted signed heat current of a finite Hermitian matrix
is genuinely integrable over positive proper time. -/
theorem hermitianSignedHeatCurrent_integrableOn
    {A : Matrix n n K} (hA : A.IsHermitian) :
    IntegrableOn
      (fun u : ℝ ↦ u ^ (-(1 / 2 : ℝ)) *
        hermitianSignedHeatCurrent hA u) (Set.Ioi 0) := by
  have hsum :
      (fun u : ℝ ↦ u ^ (-(1 / 2 : ℝ)) *
        hermitianSignedHeatCurrent hA u) =
      (fun u : ℝ ↦ ∑ i,
        u ^ (-(1 / 2 : ℝ)) *
          (hA.eigenvalues i *
            Real.exp (-u * (hA.eigenvalues i) ^ 2))) := by
    funext u
    rw [hermitianSignedHeatCurrent_eq_sum_eigenvalues, Finset.mul_sum]
  rw [hsum]
  exact integrable_finsetSum Finset.univ
    (fun i _hi ↦ signedHeatScalarIntegrableOn (hA.eigenvalues i))

/-- Exact signature formula: the normalized signed heat integral is the
positive spectral index minus the negative spectral index. -/
theorem signature_eq_signedHeatIntegral {A : Matrix n n K}
    (hA : A.IsHermitian) :
    (1 / Real.sqrt Real.pi) *
        ∫ u : ℝ in Set.Ioi 0,
          u ^ (-(1 / 2 : ℝ)) * hermitianSignedHeatCurrent hA u =
      (posIndex hA : ℝ) - (negIndex hA : ℝ) := by
  have hsum :
      (fun u : ℝ ↦ u ^ (-(1 / 2 : ℝ)) *
        hermitianSignedHeatCurrent hA u) =
      (fun u : ℝ ↦ ∑ i,
        u ^ (-(1 / 2 : ℝ)) *
          (hA.eigenvalues i *
            Real.exp (-u * (hA.eigenvalues i) ^ 2))) := by
    funext u
    rw [hermitianSignedHeatCurrent_eq_sum_eigenvalues, Finset.mul_sum]
  rw [hsum]
  have hintegral :
      (∫ u : ℝ in Set.Ioi 0, ∑ i,
        u ^ (-(1 / 2 : ℝ)) *
          (hA.eigenvalues i *
            Real.exp (-u * (hA.eigenvalues i) ^ 2))) =
        ∑ i, ∫ u : ℝ in Set.Ioi 0,
          u ^ (-(1 / 2 : ℝ)) *
            (hA.eigenvalues i *
              Real.exp (-u * (hA.eigenvalues i) ^ 2)) := by
    simpa using
      (integral_finsetSum (s := Finset.univ)
        (f := fun i ↦ fun u : ℝ ↦
          u ^ (-(1 / 2 : ℝ)) *
            (hA.eigenvalues i *
              Real.exp (-u * (hA.eigenvalues i) ^ 2)))
        (fun i _hi ↦ signedHeatScalarIntegrableOn (hA.eigenvalues i)))
  rw [hintegral, Finset.mul_sum]
  calc
    (∑ i, (1 / Real.sqrt Real.pi) *
        ∫ u : ℝ in Set.Ioi 0,
          u ^ (-(1 / 2 : ℝ)) *
            (hA.eigenvalues i *
              Real.exp (-u * (hA.eigenvalues i) ^ 2))) =
      ∑ i, realSpectralSign (hA.eigenvalues i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact signedHeatScalarIntegral_eq_sign (hA.eigenvalues i)
    _ = (posIndex hA : ℝ) - (negIndex hA : ℝ) := by
      unfold posIndex negIndex
      exact sum_realSpectralSign_eq_card_pos_sub_card_neg hA.eigenvalues

/-- Positive, negative, and zero spectral indices partition the entire
finite dimension. -/
theorem posIndex_add_negIndex_add_zeroIndex {A : Matrix n n K}
    (hA : A.IsHermitian) :
    (posIndex hA : ℝ) + (negIndex hA : ℝ) +
        (zeroIndex hA : ℝ) = Fintype.card n := by
  classical
  unfold posIndex negIndex zeroIndex
  rw [← Finset.sum_boole (R := ℝ) (fun i ↦ 0 < hA.eigenvalues i)
      Finset.univ,
    ← Finset.sum_boole (R := ℝ) (fun i ↦ hA.eigenvalues i < 0)
      Finset.univ,
    ← Finset.sum_boole (R := ℝ) (fun i ↦ hA.eigenvalues i = 0)
      Finset.univ]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    (Finset.univ.sum fun i : n ↦
        (if 0 < hA.eigenvalues i then (1 : ℝ) else 0) +
          (if hA.eigenvalues i < 0 then 1 else 0) +
          (if hA.eigenvalues i = 0 then 1 else 0)) =
        Finset.univ.sum fun _i : n ↦ (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rcases lt_trichotomy (hA.eigenvalues i) 0 with hneg | hzero | hpos
      · simp [hneg, hneg.ne, hneg.le]
      · simp [hzero]
      · simp [hpos, hpos.ne', hpos.le]
    _ = Fintype.card n := by simp

/-- The positive inertia is reconstructed exactly from the signed heat
integral together with the matrix dimension and zero index. -/
theorem posIndex_eq_signedHeat {A : Matrix n n K}
    (hA : A.IsHermitian) :
    (posIndex hA : ℝ) =
      (1 / 2 : ℝ) *
        ((Fintype.card n : ℝ) - (zeroIndex hA : ℝ) +
          (1 / Real.sqrt Real.pi) *
            ∫ u : ℝ in Set.Ioi 0,
              u ^ (-(1 / 2 : ℝ)) *
                hermitianSignedHeatCurrent hA u) := by
  rw [signature_eq_signedHeatIntegral hA]
  linarith [posIndex_add_negIndex_add_zeroIndex hA]

/-! ## Zero index from the ordinary heat trace -/

/-- A single scalar heat mode tends to one exactly at a zero eigenvalue and
to zero otherwise. -/
theorem tendsto_scalarHeat_atTop (x : ℝ) :
    Tendsto (fun u : ℝ ↦ Real.exp (-u * x ^ 2)) atTop
      (nhds (if x = 0 then 1 else 0)) := by
  by_cases hx : x = 0
  · simp [hx]
  · have hxSq : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    have hlinear : Tendsto (fun u : ℝ ↦ -u * x ^ 2) atTop atBot := by
      have h := tendsto_const_nhds.neg_mul_atTop
        (neg_lt_zero.mpr hxSq) tendsto_id
      exact h.congr' (Eventually.of_forall fun u ↦ by
        simp only [id_eq, mul_comm, neg_mul, mul_neg])
    rw [if_neg hx]
    have hExp := Real.tendsto_exp_atBot.comp hlinear
    change Tendsto (fun u : ℝ ↦ Real.exp (-u * x ^ 2)) atTop
      (nhds 0) at hExp
    exact hExp

/-- The ordinary Hermitian heat trace converges exactly to the zero index as
proper time tends to infinity. -/
theorem tendsto_hermitianHeatTrace_atTop_zeroIndex
    {A : Matrix n n K} (hA : A.IsHermitian) :
    Tendsto (hermitianHeatTrace hA) atTop (nhds (zeroIndex hA : ℝ)) := by
  have hsum : Tendsto
      (fun u : ℝ ↦ ∑ i,
        Real.exp (-u * (hA.eigenvalues i) ^ 2)) atTop
      (nhds (∑ i, if hA.eigenvalues i = 0 then 1 else 0)) := by
    exact tendsto_finsetSum Finset.univ
      (fun i _hi ↦ tendsto_scalarHeat_atTop (hA.eigenvalues i))
  rw [show hermitianHeatTrace hA =
      (fun u : ℝ ↦ ∑ i,
        Real.exp (-u * (hA.eigenvalues i) ^ 2)) by
    funext u
    exact hermitianHeatTrace_eq_sum_eigenvalues hA u]
  simpa only [zeroIndex, Finset.sum_boole] using hsum

end

end RiemannGaussian.HermitianRankTrace
