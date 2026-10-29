/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WeightedCardinality

/-! # Quantitative acquisition at the actual D.11 working precision

The dyadic tile scale cancels between the per-weight multiplicity and the
working precision. No relation D ≈ sqrt(u) is needed. The explicit numerical
guards remain obligations of the original recursive schedule; this module
does not assert a complete primitive-machine clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1ModeRate
open SemiprimeD1ModeCatalog SemiprimeD1WeightedCardinality

/-- The original tapered-jet height, with natural ceiling division. -/
def jetHeight (M u : ℕ) : ℕ := (3*M+u-1)/u

/-- D.11 precision, including both the recovery loss and entry-lifting reserve. -/
def workingPrecision (M u a i p : ℕ) : ℕ :=
  p+8*jetHeight M u*2^(a-i)+8*M*(a+1)

/-- The strict positive-weight budget actually sent to the finite enumerator. -/
def modeBudget (M u a i p : ℕ) : ℕ := workingPrecision M u a i p-1

/-- Ceiling division adds at most one original u-sized block. -/
theorem jetHeight_mul_le (M u : ℕ) (hu : u≤M) : jetHeight M u*u≤4*M := by
  have h := Nat.div_mul_le_self (3*M+u-1) u
  change (3*M+u-1)/u*u≤4*M
  omega

/-- At D.11 precision, P*u is at most a fixed multiple of M*D. -/
theorem precision_scaled_le (M u a i p : ℕ) (hu : u≤M)
    (hp : p*u≤M*2^(a-i)) (ha : (a+1)*u≤2^(a-i)) :
    workingPrecision M u a i p*u≤41*M*2^(a-i) := by
  have hh := jetHeight_mul_le M u hu
  calc
    _ = p*u+8*2^(a-i)*(jetHeight M u*u)+8*M*((a+1)*u) := by
      unfold workingPrecision
      ring
    _ ≤ M*2^(a-i)+8*2^(a-i)*(4*M)+8*M*2^(a-i) := by
      exact Nat.add_le_add (Nat.add_le_add hp (Nat.mul_le_mul_left _ hh))
        (Nat.mul_le_mul_left _ ha)
    _ = _ := by ring

/-- Actual floor multiplicity and actual strict precision have a scale-free product. -/
theorem multiplicity_budget_scaled_le (M u a i p : ℕ) (hu : u≤M)
    (hp : p*u≤M*2^(a-i)) (ha : (a+1)*u≤2^(a-i)) :
    ((6*M/2^(a-i))*modeBudget M u a i p)*u≤246*M^2 := by
  have hP : modeBudget M u a i p*u≤41*M*2^(a-i) :=
    (Nat.mul_le_mul_right u (Nat.sub_le _ _)).trans
      (precision_scaled_le M u a i p hu hp ha)
  have hD := Nat.div_mul_le_self (6*M) (2^(a-i))
  calc
    _ = (6*M/2^(a-i))*(modeBudget M u a i p*u) := by ring
    _ ≤ (6*M/2^(a-i))*(41*M*2^(a-i)) := Nat.mul_le_mul_left _ hP
    _ = 41*M*((6*M/2^(a-i))*2^(a-i)) := by ring
    _ ≤ 41*M*(6*M) := Nat.mul_le_mul_left _ hD
    _ = _ := by ring

/-- An elementary square comparison gives a fixed explicit exponential constant. -/
theorem sqrt_exponent_le (B P M u : ℕ) (hu : 0<u)
    (h : (B*P)*u≤246*M^2) :
    3*Real.sqrt ((B:ℝ)*P)≤48*(M:ℝ)/Real.sqrt (u:ℝ) := by
  have hR : (B:ℝ)*P*u≤246*(M:ℝ)^2 := by exact_mod_cast h
  have hs := Real.sq_sqrt (show (0:ℝ)≤(B:ℝ)*P by positivity)
  have ht := Real.sq_sqrt (show (0:ℝ)≤u by positivity)
  have hpos : 0<Real.sqrt (u:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hu)
  have hroot : Real.sqrt ((B:ℝ)*P)*Real.sqrt (u:ℝ)≤16*(M:ℝ) := by
    have hprod : (Real.sqrt ((B:ℝ)*P)*Real.sqrt (u:ℝ))^2≤(16*(M:ℝ))^2 := by
      rw [mul_pow,hs,ht]
      nlinarith [sq_nonneg (M:ℝ)]
    nlinarith [Real.sqrt_nonneg ((B:ℝ)*P),Real.sqrt_nonneg (u:ℝ),
      Nat.cast_nonneg (α := ℝ) M]
  apply (le_div_iff₀ hpos).mpr
  nlinarith

/-- The literal acquired menu has exp(48 M/sqrt(u)) entries under original guards. -/
theorem menu_bound (packets M u a i p : ℕ) (hi : i≤a) (hu0 : 0<u) (hu : u≤M)
    (hpackets : packets*2^a≤3*M)
    (hp : p*u≤M*2^(a-i)) (ha : (a+1)*u≤2^(a-i)) :
    ((acquireModes packets (2^(i+1)) (modeBudget M u a i p)).values.length:ℝ)≤
      Real.exp (48*(M:ℝ)/Real.sqrt (u:ℝ)) := by
  exact (packet_menu_bound packets a i M (modeBudget M u a i p) hi hpackets).trans
    (Real.exp_le_exp.mpr (sqrt_exponent_le _ _ M u hu0
      (multiplicity_budget_scaled_le M u a i p hu hp ha)))

/-- The actual catalogue/weight/tuple work has the same explicit node exponent.
The polynomial factor and all catalogue overhead are retained exactly. -/
theorem work_bound (packets M u a i p : ℕ) (hi : i≤a) (hu0 : 0<u) (hu : u≤M)
    (hpackets : packets*2^a≤3*M)
    (hp : p*u≤M*2^(a-i)) (ha : (a+1)*u≤2^(a-i)) :
    ((acquireModes packets (2^(i+1)) (modeBudget M u a i p)).work:ℝ)≤
      (modeFactor (packets*2^(i+1)) (modeBudget M u a i p):ℝ)*
        Real.exp (48*(M:ℝ)/Real.sqrt (u:ℝ))+
          (modeOverhead (packets*2^(i+1)) (modeBudget M u a i p):ℝ) := by
  apply (packet_work_bound packets a i M (modeBudget M u a i p) hi hpackets).trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Real.exp_le_exp.mpr (sqrt_exponent_le _ _ M u hu0
    (multiplicity_budget_scaled_le M u a i p hu hp ha))

end RiemannGaussian.SemiprimeD1ModeRate
