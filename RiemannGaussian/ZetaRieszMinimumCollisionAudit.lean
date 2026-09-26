/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCausalSurface
import RiemannGaussian.ZetaRieszLeastOrderOverflow
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# A quantitative audit of the remaining least-prime projection

Two ordered Laplace chambers evaluate the factorial moment of a minimum.
Their sum sees the sum of the two mode denominators, not their individual
norms. Opposite imaginary parts can therefore survive this projection.

The last two inequalities certify positive *candidate* collision budgets
at the actual factorial boundary proportions. They are not asymptotics
for a Riesz response: its residue, all-count cancellation and arithmetic
transfer remain to be established. No prime mask or target is changed.
-/

namespace RiemannGaussian.ZetaRieszMinimumCollisionAudit
noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators

/-- The two exponential modes, with a common positive real denominator. -/
def node (d eta : ℝ) : ℂ := (d : ℂ)+Complex.I*eta

theorem node_add_opposite (d eta : ℝ) :
    node d eta+node d (-eta) = ((2*d : ℝ) : ℂ) := by
  simp only [node, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

/-- The two chambers `x=r, y=r+v` and `x=r+v, y=r` retain both
choices of the least coordinate. This is a model integral, not a prime sum. -/
def minimumMoment (h : ℕ) (d eta : ℝ) : ℂ :=
  ∫ r : ℝ in Ioi 0, ((r^h/(h.factorial : ℝ)*Real.exp (-(2*d)*r) : ℝ) : ℂ)*
    ((∫ v : ℝ in Ioi 0, Complex.exp (-node d eta*(v : ℂ)))+
     (∫ v : ℝ in Ioi 0, Complex.exp (-node d (-eta)*(v : ℂ))))

/-- Factoring the two chamber exponentials leaves exactly the sum of
their denominators on the minimum coordinate. -/
theorem chamber_factor (d eta r v : ℝ) :
    Complex.exp (-node d eta*(r : ℂ)-node d (-eta)*(r+v))+
      Complex.exp (-node d eta*(r+v)-node d (-eta)*(r : ℂ)) =
      Complex.exp (-((2*d : ℝ) : ℂ)*r)*
        (Complex.exp (-node d (-eta)*(v : ℂ))+
          Complex.exp (-node d eta*(v : ℂ))) := by
  have h := node_add_opposite d eta
  have h₁ : -node d eta*(r : ℂ)-node d (-eta)*(r+v) =
      -((2*d : ℝ) : ℂ)*r+(-node d (-eta)*(v : ℂ)) := by
    linear_combination -h*r
  have h₂ : -node d eta*(r+v)-node d (-eta)*(r : ℂ) =
      -((2*d : ℝ) : ℂ)*r+(-node d eta*(v : ℂ)) := by
    linear_combination -h*r
  rw [h₁,h₂,Complex.exp_add,Complex.exp_add,mul_add]

private theorem tail_eq {d : ℝ} (hd : 0 < d) (eta : ℝ) :
    (∫ v : ℝ in Ioi 0, Complex.exp (-node d eta*(v : ℂ))) = (node d eta)⁻¹ := by
  rw [integral_exp_mul_complex_Ioi (by simpa [node] using neg_neg_of_pos hd)]
  simp

/-- The exact minimum-moment transform. Both ordered chambers have
already been summed; no individual complete-leg limit is used. -/
theorem minimumMoment_eq (h : ℕ) {d : ℝ} (hd : 0 < d) (eta : ℝ) :
    minimumMoment h d eta =
      1/((node d eta*node d (-eta))*((2*d : ℝ) : ℂ)^h) := by
  have ha : node d eta ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp [node] at hr
    linarith
  have hb : node d (-eta) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp [node] at hr
    linarith
  have hdC : ((2*d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : 2*d ≠ 0)
  have hf : (h.factorial : ℝ) ≠ 0 := by positivity
  have hi : (∫ r : ℝ in Ioi 0,
      r^h/(h.factorial : ℝ)*Real.exp (-(2*d)*r)) = 1/(2*d)^(h+1) := by
    simp_rw [div_mul_eq_mul_div]
    rw [integral_div, ZetaRieszCausalSurface.radial_integral h (by positivity)]
    field_simp
  rw [minimumMoment, tail_eq hd, tail_eq hd, integral_mul_const,
    integral_complex_ofReal, hi]
  have hc : ((1/(2*d)^(h+1) : ℝ) : ℂ) =
      1/((2*d : ℝ) : ℂ)^(h+1) := by push_cast; rfl
  rw [hc]
  have hs : (node d eta)⁻¹+(node d (-eta))⁻¹ =
      ((2*d : ℝ) : ℂ)/(node d eta*node d (-eta)) := by
    rw [← node_add_opposite d eta]
    field_simp
    ring
  rw [hs,pow_succ]
  field_simp [ha,hb,hdC]

/-- Conjugate mode denominators leave a positive scalar prefactor. -/
theorem node_mul_opposite (d eta : ℝ) :
    node d eta*node d (-eta) = ((d^2+eta^2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [node, pow_two]
  ring

/-- On the total-log clock, the normalized minimum moment is governed
by the *real* denominator d, even if both separate mode norms exceed u. -/
theorem normalized_minimumMoment (h : ℕ) {d : ℝ} (hd : 0 < d) (u eta : ℝ) :
    ((2*u : ℝ) : ℂ)^h*minimumMoment h d eta =
      (((u/d)^h/(d^2+eta^2) : ℝ) : ℂ) := by
  rw [minimumMoment_eq h hd eta, node_mul_opposite]
  have hd0 : d ≠ 0 := ne_of_gt hd
  have he : d^2+eta^2 ≠ 0 := by nlinarith [sq_nonneg eta]
  have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd0
  have heC : (d : ℂ)^2+(eta : ℂ)^2 ≠ 0 := by exact_mod_cast he
  push_cast
  simp only [mul_pow, div_pow]
  field_simp [hdC,heC]

/-- These synthetic exposed modes are precisely the close-mode stress
parameters. They are not asserted to be zeros of zeta. -/
theorem stress_geometry :
    0 < (10001/20000 : ℝ)-1/40000 ∧
    (10001/20000 : ℝ)-1/40000 < 10001/20000 ∧
    (10001/20000 : ℝ) < ‖node (10001/20000-1/40000) (3/500)‖ ∧
    (10001/20000 : ℝ) < ‖node (10001/20000-1/40000) (-(3/500))‖ := by
  have hs : (20002 : ℝ) < Real.sqrt 400097601 :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;>
    rw [Complex.norm_def] <;>
    norm_num [node, Complex.normSq] <;> linarith

/-- The exact normalized model grows despite the separate nodes being
outside the source disk. This is not a counterexample to the full carrier. -/
theorem normalized_minimumMoment_tendsto_of_gain {d u : ℝ}
    (hd : 0 < d) (hdu : d < u) (eta : ℝ) :
    Tendsto (fun h : ℕ => (((2*u : ℝ) : ℂ)^h*minimumMoment h d eta).re)
      atTop atTop := by
  simp_rw [normalized_minimumMoment _ hd, Complex.ofReal_re]
  exact (tendsto_pow_atTop_atTop_of_one_lt
    ((lt_div_iff₀ hd).mpr (by linarith : 1*d < u))).atTop_div_const
      (by nlinarith [sq_nonneg eta])

/-- A concrete close-mode instance of the general minimum collision. -/
theorem normalized_minimumMoment_tendsto :
    Tendsto (fun h : ℕ =>
      (((2*(10001/20000 : ℝ) : ℝ) : ℂ)^h*
        minimumMoment h (10001/20000-1/40000) (3/500)).re) atTop atTop := by
  exact normalized_minimumMoment_tendsto_of_gain stress_geometry.1
    stress_geometry.2.1 _

/-- Candidate radial gain at owner share 21/40 and balanced opposite
frequencies on the remaining shares. It still requires a nonzero joint
residue before it can describe a response. -/
def radialGain : ℝ := Real.log (800080/800061)

/-- The multinomial relative-entropy cost at the lower least-order
boundary, with 48 equal cofactor shares 19/1920. -/
def lowerCollisionCost : ℝ :=
  (1/100 : ℝ)*Real.log (96/95)+(93/200)*Real.log (4464/4465)

/-- The corresponding cost at the upper boundary, with 12 equal
cofactor shares 19/480. -/
def upperCollisionCost : ℝ :=
  (1/25 : ℝ)*Real.log (96/95)+(87/200)*Real.log (1044/1045)

/-- Factorial concentration alone does not make this candidate budget
negative. This is an inequality between explicit real numbers only. -/
theorem lower_collision_budget_pos :
    (1/50000 : ℝ) < radialGain-lowerCollisionCost := by
  have hg := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 800080/800061)
  have h₁ := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 96/95)
  have h₂ := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4464/4465)
  norm_num at hg h₁ h₂
  dsimp [radialGain, lowerCollisionCost]
  linarith

/-- The upper-face candidate also has positive budget. No residue or
cross-count cancellation is inferred from this rate test. -/
theorem upper_collision_budget_pos :
    (1/60000 : ℝ) < radialGain-upperCollisionCost := by
  have hg := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 800080/800061)
  have h₁ := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 96/95)
  have h₂ := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1044/1045)
  norm_num at hg h₁ h₂
  dsimp [radialGain, upperCollisionCost]
  linarith

/-- The Riesz kernel on an equal-share cofactor boundary, grouped by
subset cardinality. Equality is a continuum limit, not a squarefree label. -/
def equalKernel (k : ℕ) (r d : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)*(-1 : ℝ)^j*max 0 (d-j*r)

/-- This is exactly the existing signed finite-difference kernel, with
every subset sign present, rather than a separate surrogate. -/
theorem kernel_equal_shares (k : ℕ) (r d : ℝ) :
    ZetaRieszContinuumCascade.kernel (Finset.univ : Finset (Fin k)) (fun _ => r) d =
      equalKernel k r d := by
  classical
  simp only [ZetaRieszContinuumCascade.kernel,Finset.sum_const,nsmul_eq_mul]
  rw [Finset.sum_powerset]
  simp only [Finset.card_univ,Fintype.card_fin,equalKernel]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_powersetCard j (Finset.univ : Finset (Fin k))
    (fun m : ℕ => (-1 : ℝ)^m*max 0 (d-m*r))]
  simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- At this strict-core rational ratio, the upper-face collision is
not eliminated by the Riesz kernel pointwise. No residue is inferred. -/
theorem upper_collision_kernel :
    equalKernel 12 (19/480) (693/1000-21/40) = -(39/25 : ℝ) := by
  norm_num [equalKernel,Finset.sum_range_succ,Nat.choose]

/-- The lower-face candidate likewise has a nonzero kernel. This does
not establish its signed integral or rule out cross-count cancellation. -/
theorem lower_collision_kernel :
    0 < equalKernel 48 (19/1920) (693/1000-21/40) := by
  norm_num [equalKernel,Finset.sum_range_succ,Nat.choose]

/-- An interior collision needs no multinomial large-deviation cost:
the owner has share 14/25 and each of its 44 cofactors has share 1/100.
All three grouped order fractions equal their log-share parameters. -/
theorem interior_collision_entropy_zero :
    (14/25 : ℝ)+44*(1/100) = 1 ∧
    (21/40 : ℝ) < 14/25 ∧ (14/25 : ℝ) < 23/40 ∧
    (14/25 : ℝ)*Real.log ((14/25)/(14/25))+
      (1/100)*Real.log ((1/100)/(1/100))+
      (43/100)*Real.log ((43/100)/(43/100)) = 0 := by
  norm_num

/-- Narrowing the radius does not by itself give a negative candidate
budget: at the interior zero-cost collision, every positive horizontal
gain gives positive radial gain. This is not a response asymptotic. -/
theorem interior_collision_budget_pos {u delta : ℝ}
    (hd : 0 < delta) (hdu : delta < u) :
    0 < Real.log (u/(u-(11/25)*delta)) := by
  have ha : 0 < u-(11/25)*delta := by linarith
  exact Real.log_pos ((lt_div_iff₀ ha).mpr (by linarith))

/-- The exact Riesz kernel is nonzero at the zero-cost interior
collision as well. Equal shares still denote a continuum boundary,
not repeated primes in a squarefree label. -/
theorem interior_collision_kernel :
    equalKernel 44 (1/100) (693/1000-14/25) = (106328047/125 : ℝ) := by
  norm_num [equalKernel,Finset.sum_range_succ,Nat.choose]


/-! ## Summing the balanced collision chambers

The following local cone calculation closes neither the global asymptotic
nor the arithmetic transfer. It shows that summing all least-coordinate
incidences does not itself annihilate these two candidate corners.
-/

/-- The factored orthant Laplace chambers, summed over every possible
least-coordinate incidence. This is a finite cone model, not a prime sum
or an asserted asymptotic coefficient of the retained carrier. -/
def collisionChambers {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → ℂ) : ℂ :=
  ∑ m ∈ S, ∏ i ∈ S.erase m,
    ∫ v : ℝ in Ioi 0, Complex.exp (-a i*(v : ℂ))

/-- Summing the incidences before estimation retains the sum of complex
denominators in the numerator. No chamber is replaced by its norm. -/
theorem collisionChambers_eq {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → ℂ) (ha : ∀ i ∈ S, 0 < (a i).re) :
    collisionChambers S a = (∑ i ∈ S, a i)/(∏ i ∈ S, a i) := by
  have hn (i : ι) (hi : i ∈ S) : a i ≠ 0 := by
    intro h
    have hh := ha i hi
    rw [h, Complex.zero_re] at hh
    exact lt_irrefl 0 hh
  have ht (i : ι) (hi : i ∈ S) :
      (∫ v : ℝ in Ioi 0, Complex.exp (-a i*(v : ℂ))) = (a i)⁻¹ := by
    rw [integral_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos (ha i hi))]
    simp
  calc
    _ = ∑ m ∈ S, ∏ i ∈ S.erase m, (a i)⁻¹ := by
      apply Finset.sum_congr rfl
      intro m _
      exact Finset.prod_congr rfl (fun i hi => ht i (Finset.mem_of_mem_erase hi))
    _ = ∑ m ∈ S, (∏ i ∈ S, (a i)⁻¹)*a m := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [← Finset.prod_erase_mul S (fun i => (a i)⁻¹) hm,
        mul_assoc, inv_mul_cancel₀ (hn m hm), mul_one]
    _ = _ := by
      rw [← Finset.mul_sum, Finset.prod_inv_distrib]
      ring

/-- An equal number of opposite-frequency legs with the same positive
real normal slope. These are synthetic parameters, not asserted zeros. -/
def pairedNode {m : ℕ} (a eta : ℝ) (i : Fin m × Bool) : ℂ :=
  if i.2 then node a eta else node a (-eta)

/-- The imaginary common-shift phases cancel in the balanced family. -/
theorem paired_node_sum (m : ℕ) (a eta : ℝ) :
    (∑ i : Fin m × Bool, pairedNode a eta i) = ((2*m*a : ℝ) : ℂ) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, pairedNode, Bool.false_eq_true,
    ite_true, ite_false]
  simp only [node_add_opposite, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  ring

/-- Every conjugate pair contributes one positive real denominator. -/
theorem paired_node_prod (m : ℕ) (a eta : ℝ) :
    (∏ i : Fin m × Bool, pairedNode a eta i) = ((a^2+eta^2)^m : ℝ) := by
  simp only [Fintype.prod_prod_type, Fintype.prod_bool, pairedNode, Bool.false_eq_true,
    ite_true, ite_false,
    node_mul_opposite, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Complex.ofReal_pow]

/-- Exact summed cone integral for 2m balanced legs. In particular the
opposite phases do not annihilate this incidence sum. -/
theorem paired_collision_eq (m : ℕ) {a : ℝ} (ha : 0 < a) (eta : ℝ) :
    collisionChambers (Finset.univ : Finset (Fin m × Bool)) (pairedNode a eta) =
      (((2*m*a)/(a^2+eta^2)^m : ℝ) : ℂ) := by
  rw [collisionChambers_eq _ _ (by
    intro i _
    unfold pairedNode
    split <;> simpa [node] using ha),
    paired_node_sum, paired_node_prod]
  push_cast
  rfl

/-- The determinant of the fixed-total coordinate map's linear part:
x_i=(s-sum y)/(k+1)+y_i. This proves the scalar Jacobian, not a
change-of-variables theorem for the full masked carrier. -/
theorem chamber_jacobian (k : ℕ) :
    Matrix.det (1 + Matrix.replicateCol Unit (fun _ : Fin k => -(1/(k+1 : ℝ))) *
      Matrix.replicateRow Unit (fun _ : Fin k => (1 : ℝ))) = 1/(k+1 : ℝ) := by
  rw [Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, one_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The balanced cone with its 1/(2m) fixed-total Jacobian included.
Its definition remains a model; no asymptotic transport is assumed. -/
def diagonalCone (m : ℕ) (a eta : ℝ) : ℂ :=
  collisionChambers (Finset.univ : Finset (Fin m × Bool)) (pairedNode a eta)/(2*m)

/-- The entire phase-dependent cone factor, after all least incidences. -/
theorem diagonalCone_eq {m : ℕ} (hm : 0 < m) {a : ℝ} (ha : 0 < a) (eta : ℝ) :
    diagonalCone m a eta = ((a/(a^2+eta^2)^m : ℝ) : ℂ) := by
  rw [diagonalCone, paired_collision_eq m ha eta]
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  push_cast
  field_simp

/-- Balanced opposite frequencies leave a strictly positive cone factor. -/
theorem diagonalCone_re_pos {m : ℕ} (hm : 0 < m) {a : ℝ} (ha : 0 < a) (eta : ℝ) :
    0 < (diagonalCone m a eta).re := by
  rw [diagonalCone_eq hm ha, Complex.ofReal_re]
  exact div_pos ha (pow_pos (by nlinarith [sq_nonneg eta]) _)

/-- Outward normal rate of the grouped factorial entropy at the equal
cofactor boundary. The finite factorial packet is not replaced by this rate. -/
def normalSlope (k : ℕ) (b s : ℝ) : ℝ := (k*b-s)/((k-1)*s)

/-- The two varying logarithms of the limiting grouped factorial
profile, with owner share 1-s and least-order share b. -/
def factorialProfile (k : ℕ) (b s q : ℝ) : ℝ :=
  b*Real.log ((s-q)/k)+(s-b)*Real.log (s-(s-q)/k)

/-- The cone slope is the derivative of the coupled factorial profile;
the owner/cofactor correlation is retained in its second logarithm. -/
theorem factorialProfile_hasDerivAt {k : ℕ} (hk : 2 ≤ k) (b : ℝ) {s : ℝ}
    (hs : 0 < s) : HasDerivAt (factorialProfile k b s) (-normalSlope k b s) 0 := by
  have hkR : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  have hx : s/(k : ℝ) ≠ 0 := div_ne_zero hs.ne' hk0
  have hy : s-s/(k : ℝ) ≠ 0 := by
    have : s/(k : ℝ) < s := (div_lt_self hs hkR)
    linarith
  have h₁ : HasDerivAt (fun q : ℝ => (s-q)/(k : ℝ)) (-1/(k : ℝ)) 0 := by
    simpa using ((hasDerivAt_const (0 : ℝ) s).sub (hasDerivAt_id 0)).div_const (k : ℝ)
  have h₂ := (hasDerivAt_const (0 : ℝ) s).sub h₁
  have h := ((h₁.log (by simpa using hx)).const_mul b).add
    ((h₂.log (by simpa using hy)).const_mul (s-b))
  have he : -normalSlope k b s =
      b*(-1/(k : ℝ)/(s/k))+(s-b)*((1/(k : ℝ))/(s-s/k)) := by
    unfold normalSlope
    have hk1 : -1+(k : ℝ) ≠ 0 := by linarith
    have hk1' : (k : ℝ)-1 ≠ 0 := by linarith
    field_simp [hk0, hk1, hk1', hs.ne']
    ring
  change HasDerivAt (factorialProfile k b s) _ 0 at h
  simp only [Pi.sub_apply, sub_zero, zero_sub, neg_div, neg_neg] at h
  simp only [neg_div] at he
  rwa [← he] at h

/-- The two original least-order fractions give positive rational
normal slopes at owner share 21/40, with 12 and 48 equal cofactors. -/
theorem boundary_normal_slopes :
    normalSlope 12 (1/25) (19/40) = (1/1045 : ℝ) ∧
    normalSlope 48 (1/100) (19/40) = (1/4465 : ℝ) := by
  norm_num [normalSlope]

/-- The two rational regression cones reinforce after the original
lower-minus-upper orientation. Positive amplitudes are arbitrary model
weights, not unproved arithmetic residues. -/
theorem paired_face_cones_neg (eta : ℝ) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (A * equalKernel 12 (19/480) (693/1000-21/40) *
        (diagonalCone 6 (1/1045) eta).re -
      B * equalKernel 48 (19/1920) (693/1000-21/40) *
        (diagonalCone 24 (1/4465) eta).re) < 0 := by
  rw [upper_collision_kernel]
  have hu := diagonalCone_re_pos (m := 6) (by norm_num) (a := 1/1045) (by norm_num) eta
  have hl := diagonalCone_re_pos (m := 24) (by norm_num) (a := 1/4465) (by norm_num) eta
  have ht : A * (-(39/25 : ℝ)) * (diagonalCone 6 (1/1045) eta).re < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hA (by norm_num)) hu
  have hb : 0 < B * equalKernel 48 (19/1920) (693/1000-21/40) *
      (diagonalCone 24 (1/4465) eta).re :=
    mul_pos (mul_pos hB lower_collision_kernel) hl
  linarith

/-- The upper-face Riesz sign persists on this full ratio interval. -/
theorem upper_kernel_negative_on_window {lam : ℝ}
    (hlo : 693/1000 ≤ lam) (hhi : lam ≤ 694/1000) :
    equalKernel 12 (19/480) (lam-21/40) < 0 := by
  have hh (j : ℕ) : max 0 (lam-21/40-j*(19/480 : ℝ)) =
      if j ≤ 4 then lam-21/40-j*(19/480 : ℝ) else 0 := by
    split_ifs with hj
    · have h : (j : ℝ) ≤ 4 := by exact_mod_cast hj
      exact max_eq_right (by linarith)
    · have h : (5 : ℝ) ≤ j := by exact_mod_cast (by omega : 5 ≤ j)
      exact max_eq_left (by linarith)
  unfold equalKernel
  simp_rw [hh]
  norm_num [Finset.sum_range_succ, Nat.choose]
  linarith

/-- The lower-face sign persists even across its seventeenth hinge. -/
theorem lower_kernel_positive_on_window {lam : ℝ}
    (hlo : 693/1000 ≤ lam) (hhi : lam ≤ 694/1000) :
    0 < equalKernel 48 (19/1920) (lam-21/40) := by
  have hh (j : ℕ) : max 0 (lam-21/40-j*(19/1920 : ℝ)) =
      if j ≤ 16 then lam-21/40-j*(19/1920 : ℝ) else
        if j = 17 then max 0 (lam-21/40-17*(19/1920 : ℝ)) else 0 := by
    split_ifs with hj hj'
    · have h : (j : ℝ) ≤ 16 := by exact_mod_cast hj
      exact max_eq_right (by linarith)
    · rw [hj']; norm_num
    · have h : (18 : ℝ) ≤ j := by exact_mod_cast (by omega : 18 ≤ j)
      exact max_eq_left (by linarith)
  have he : equalKernel 48 (19/1920) (lam-21/40) =
      ∑ j ∈ Finset.range 49, (Nat.choose 48 j : ℝ)*(-1 : ℝ)^j*
        (if j ≤ 16 then lam-21/40-j*(19/1920 : ℝ) else
          if j = 17 then max 0 (lam-21/40-17*(19/1920 : ℝ)) else 0) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hh]
  rw [he]
  norm_num [Finset.sum_range_succ, Nat.choose]
  by_cases hc : lam-21/40-17*(19/1920 : ℝ) ≤ 0
  · rw [max_eq_left (by linarith)]
    linarith
  · rw [max_eq_right (by linarith)]
    linarith

/-- The canonical limiting ratio lies inside the checked kernel window
throughout the restricted radius range. No finite radial slice is frozen. -/
theorem source_ratio_window {u : ℝ} (hu : 1/2 ≤ u) (hU : u ≤ 10001/20000) :
    693/1000 ≤ -2*u*Real.log u ∧ -2*u*Real.log u ≤ 694/1000 := by
  have hu0 : 0 < u := by linarith
  have hlow := Real.log_le_log (by norm_num : (0 : ℝ) < 1/2) hu
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub] at hlow
  have hhi := Real.log_le_sub_one_of_pos (by positivity : 0 < 2*u)
  rw [Real.log_mul (by norm_num) hu0.ne'] at hhi
  have hl2 := Real.log_two_gt_d9
  have hu2 := Real.log_two_lt_d9
  have hpos : 0 < -Real.log u := by nlinarith
  constructor <;> nlinarith

/-- The two cone factors cannot cancel on the whole checked ratio
window. Other counts, other corners, radial asymptotics and actual primes
are not estimated by this finite model sign theorem. -/
theorem paired_face_cones_window_neg {lam : ℝ}
    (hlo : 693/1000 ≤ lam) (hhi : lam ≤ 694/1000) (eta : ℝ)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (A * equalKernel 12 (19/480) (lam-21/40) *
        (diagonalCone 6 (1/1045) eta).re -
      B * equalKernel 48 (19/1920) (lam-21/40) *
        (diagonalCone 24 (1/4465) eta).re) < 0 := by
  have hu := diagonalCone_re_pos (m := 6) (by norm_num) (a := 1/1045) (by norm_num) eta
  have hl := diagonalCone_re_pos (m := 24) (by norm_num) (a := 1/4465) (by norm_num) eta
  have ht : A * equalKernel 12 (19/480) (lam-21/40) *
      (diagonalCone 6 (1/1045) eta).re < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hA
      (upper_kernel_negative_on_window hlo hhi)) hu
  have hb : 0 < B * equalKernel 48 (19/1920) (lam-21/40) *
      (diagonalCone 24 (1/4465) eta).re :=
    mul_pos (mul_pos hB (lower_kernel_positive_on_window hlo hhi)) hl
  linarith

/-- The same model sign at the canonical limiting source ratio. This
is not a surviving-residue theorem or a bound on the full carrier. -/
theorem paired_face_cones_source_neg {u : ℝ} (hu : 1/2 ≤ u) (hU : u ≤ 10001/20000)
    (eta : ℝ) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (A * equalKernel 12 (19/480) (-2*u*Real.log u-21/40) *
        (diagonalCone 6 (1/1045) eta).re -
      B * equalKernel 48 (19/1920) (-2*u*Real.log u-21/40) *
        (diagonalCone 24 (1/4465) eta).re) < 0 :=
  paired_face_cones_window_neg (source_ratio_window hu hU).1
    (source_ratio_window hu hU).2 eta hA hB

/-! ## Coherent cofactor modes

After fixing the owner on the positive-frequency mode, let `same` be the
cofactor share on that same mode, and `neutral` the selected-mode share.
All other cofactor share is on the conjugate mode. The following exact
coupled-denominator comparison sums those shares before comparing norms.
It does not assert dominance of the full masked integral or transfer a
complete-prime phase through a mask.
-/

/-- Exact squared-denominator excess over the all-opposite cofactor choice. -/
theorem coherent_normSq_difference (u delta eta p same neutral : ℝ) :
    Complex.normSq (node (u-delta+delta*neutral) (eta*(2*p-1+2*same+neutral))) -
      Complex.normSq (node (u-delta) (eta*(2*p-1))) =
      2*(u-delta)*delta*neutral+(delta*neutral)^2+
        eta^2*(2*(2*p-1)*(2*same+neutral)+(2*same+neutral)^2) := by
  simp only [node, Complex.normSq_apply]
  simp
  ring

/-- A wrong cofactor share bounded below by `r` gives a quantitative
gap in the joint radial denominator. No prime-count truncation is used. -/
theorem coherent_normSq_gap {u delta eta p same neutral r : ℝ}
    (hd : 0 ≤ delta) (hdu : delta ≤ u) (hp : 1/2 ≤ p)
    (hs : 0 ≤ same) (hn : 0 ≤ neutral) (hr : 0 ≤ r) (hm : r ≤ same+neutral) :
    2*eta^2*(2*p-1)*r+eta^2*r^2 ≤
      Complex.normSq (node (u-delta+delta*neutral) (eta*(2*p-1+2*same+neutral))) -
        Complex.normSq (node (u-delta) (eta*(2*p-1))) := by
  rw [coherent_normSq_difference]
  have h₀ : 0 ≤ 2*(u-delta)*delta*neutral := by positivity
  have h₁ : r ≤ 2*same+neutral := by linarith
  have h₂ : 0 ≤ 2*p-1 := by linarith
  have h₃ : 2*(2*p-1)*r+r^2 ≤
      2*(2*p-1)*(2*same+neutral)+(2*same+neutral)^2 := by nlinarith
  have h₄ := mul_le_mul_of_nonneg_left h₃ (sq_nonneg eta)
  nlinarith [sq_nonneg (delta*neutral)]

/-- A genuinely mixed cofactor assignment has strictly larger norm than
the coherent conjugate choice when the owner has more than half the share. -/
theorem coherent_denominator_strict {u delta eta p same neutral : ℝ}
    (hd : 0 ≤ delta) (hdu : delta ≤ u) (hp : 1/2 < p)
    (he : eta ≠ 0) (hs : 0 ≤ same) (hn : 0 ≤ neutral) (hm : 0 < same+neutral) :
    ‖node (u-delta) (eta*(2*p-1))‖ <
      ‖node (u-delta+delta*neutral) (eta*(2*p-1+2*same+neutral))‖ := by
  have hg := coherent_normSq_gap (eta := eta) hd hdu hp.le hs hn hm.le (le_refl (same+neutral))
  have hpos : 0 < eta^2*(same+neutral)^2 := mul_pos (sq_pos_of_ne_zero he) (sq_pos_of_pos hm)
  have hp0 : 0 ≤ 2*p-1 := by linarith
  have hnon : 0 ≤ 2*eta^2*(2*p-1)*(same+neutral) := by positivity
  rw [Complex.norm_def, Complex.norm_def]
  exact Real.sqrt_lt_sqrt (Complex.normSq_nonneg _) (by linarith)


end
end RiemannGaussian.ZetaRieszMinimumCollisionAudit
