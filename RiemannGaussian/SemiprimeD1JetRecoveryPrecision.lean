/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WeightPrecision

/-! # Actual original D.5 recovery under modular representative errors
The input seam is ONLY retained child-jet error precision. Every weight,
inverse-integrality fact, scalar loss and working precision is derived from
original grid data. This is a rational-coordinate theorem, not a bit clock.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1JetRecoveryPrecision
open scoped BigOperators
open Polynomial SemiprimeD1DyadicBounds SemiprimeD1WeightPrecision
  SemiprimeD1WireKernelOriginal SemiprimeD1TaperedLoss SemiprimeD1JetRecoveryGrid
  SemiprimeD1JetRecoveryWeights SemiprimeD1HermiteNodes SemiprimeD1HermiteOriginal
  SemiprimeJetArray

/-- Actual original scalar linear recovery from supplied retained CHILD coefficient arrays.
All scalar weights are acquired from the original grid inside this finite expression. -/
def recover (a M u : ℕ) (packets : ℕ→Array ℚ) : ℚ :=
  ∑t∈active a (height M u) u,∑j∈Finset.range (nodeMultiplicity a (height M u) u t),
    coefficient (acquire a (height M u) u t).weights j*coefficient (packets t) j

/-- Exact rational retained packets used only as a proof witness, not a runtime jet oracle. -/
noncomputable def exactPacket (a M u : ℕ) (H : ℚ[X]) (t : ℕ) : Array ℚ :=
  Array.ofFn (fun j : Fin (nodeMultiplicity a (height M u) u t) =>
    (H.comp (SemiprimeD1ScaledHermite.affine (alpha a) (node a t))).coeff j.val)

/-- The proof witness has exactly the retained width. -/
theorem exactPacket_size (a M u : ℕ) (H : ℚ[X]) (t : ℕ) :
    (exactPacket a M u H t).size=nodeMultiplicity a (height M u) u t := by
  simp only [exactPacket,Array.size_ofFn]

/-- Every retained proof-witness coefficient is the true scaled Taylor coefficient. -/
theorem exactPacket_coefficient (a M u : ℕ) (H : ℚ[X]) (t j : ℕ)
    (hj : j<nodeMultiplicity a (height M u) u t) :
    coefficient (exactPacket a M u H t) j=
      (H.comp (SemiprimeD1ScaledHermite.affine (alpha a) (node a t))).coeff j := by
  simp [exactPacket,coefficient,hj]

/-- Exact recovery is a DERIVED original Hermite identity on the proof witness. -/
theorem recover_exact (a M u : ℕ) (hu : 0<u) (hM : u≤M) (H : ℚ[X])
    (hH : H.natDegree≤M*(2*(2^a)-1)) : recover a M u (exactPacket a M u H)=H.eval 0 := by
  exact (recover_from_retained_arrays a M u hu hM H hH (exactPacket a M u H)
    (fun t _ => exactPacket_size a M u H t) (fun t _ j hj => exactPacket_coefficient a M u H t j hj)).symm

/-- ORIGINAL tapered D.5 precision theorem: ANY permitted representative jet lifts
produce the same parent answer modulo2^p, coordinatewise and without a weight oracle. -/
theorem recover_error (a M u p : ℕ) (hu : 0<u) (hM : u≤M) (H : ℚ[X])
    (hH : H.natDegree≤M*(2*(2^a)-1)) (packets : ℕ→Array ℚ)
    (herr : ∀t∈active a (height M u) u,∀j<nodeMultiplicity a (height M u) u t,
      AtLeast (precision a M u p t:ℤ)
        (coefficient (packets t) j-
          (H.comp (SemiprimeD1ScaledHermite.affine (alpha a) (node a t))).coeff j)) :
    AtLeast (p:ℤ) (recover a M u packets-H.eval 0) := by
  have he : recover a M u packets-H.eval 0=
      ∑t∈active a (height M u) u,∑j∈Finset.range (nodeMultiplicity a (height M u) u t),
        coefficient (acquire a (height M u) u t).weights j*
          (coefficient (packets t) j-
            (H.comp (SemiprimeD1ScaledHermite.affine (alpha a) (node a t))).coeff j) := by
    rw [← recover_exact a M u hu hM H hH]
    unfold recover
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← mul_sub,exactPacket_coefficient a M u H t j (Finset.mem_range.mp hj)]
  rw [he]
  apply SemiprimeD1DyadicBounds.sum
  intro t ht
  apply SemiprimeD1DyadicBounds.sum
  intro j hj
  have hqr := (Finset.mem_filter.mp ht).1
  have htc := (Finset.mem_filter.mp ht).2.1
  let tt : Fin (size a) := ⟨t,Finset.mem_range.mp hqr⟩
  have htn : point a t≠0 := (not_congr (point_zero_iff a t)).mpr htc
  exact weighted_error a M u p tt hM htn (active_positive a (height M u) u t ht)
    j (Finset.mem_range.mp hj) _ (herr t ht j (Finset.mem_range.mp hj))

/-- The reconstructed rational coordinates are integral whenever the actual parent
value is integral. Known even-denominator cancellation is thereby justified algebraically. -/
theorem recover_integral (a M u p : ℕ) (hu : 0<u) (hM : u≤M) (H : ℚ[X])
    (hH : H.natDegree≤M*(2*(2^a)-1)) (packets : ℕ→Array ℚ)
    (h0 : AtLeast 0 (H.eval 0))
    (herr : ∀t∈active a (height M u) u,∀j<nodeMultiplicity a (height M u) u t,
      AtLeast (precision a M u p t:ℤ)
        (coefficient (packets t) j-
          (H.comp (SemiprimeD1ScaledHermite.affine (alpha a) (node a t))).coeff j)) :
    AtLeast 0 (recover a M u packets) := by
  have he := mono (recover_error a M u p hu hM H hH packets herr) (show (0:ℤ)≤p by positivity)
  simpa only [sub_add_cancel] using add he h0

/-- Finite FREE old-algebra coordinates require no multiplicative valuation or
nilpotent-ring evaluation: the actual parent precision holds independently in every coordinate. -/
theorem recover_coordinates_error (a M u p c : ℕ) (hu : 0<u) (hM : u≤M)
    (H : Fin c→ℚ[X]) (hH : ∀d,(H d).natDegree≤M*(2*(2^a)-1))
    (packets : Fin c→ℕ→Array ℚ)
    (herr : ∀d,∀t∈active a (height M u) u,∀j<nodeMultiplicity a (height M u) u t,
      AtLeast (precision a M u p t:ℤ)
        (coefficient (packets d t) j-
          ((H d).comp (SemiprimeD1ScaledHermite.affine (alpha a) (node a t))).coeff j)) :
    ∀d,AtLeast (p:ℤ) (recover a M u (packets d)-(H d).eval 0) := by
  intro d
  exact recover_error a M u p hu hM (H d) (hH d) (packets d) (herr d)

end RiemannGaussian.SemiprimeD1JetRecoveryPrecision
