/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSelectedCofactor

/-!
# Summing the selected Gamma rectangle before estimating it

The probability mass below is exactly the old integer rectangle. No
limiting share indicator, independent-leg bound or sign estimate is used.
-/

namespace RiemannGaussian.ZetaRieszGammaCollapse
noncomputable section
open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Classical
open ZetaRieszSelectedGamma ZetaRieszSelectedCofactor
open ZetaRieszSkewAllocation ZetaRieszJointAllocation

/-- The source power and Gamma normalization cancel at every selected
marked order, before any integral or estimate. -/
theorem gamma_factorial_collapse (u t : ℝ) {N j : ℕ}
    (hj : 0 < j) (hjN : j ≤ N+1) :
    u^(N+1-j)/(j : ℝ)*gammaKernel u j t =
      u^(N+1)*Real.exp (-u*t)*t^(j-1)/(j.factorial : ℝ) := by
  have hf : (j : ℝ)*((j-1).factorial : ℝ) = (j.factorial : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (Nat.ne_of_gt hj))
  unfold gammaKernel
  calc
    _ = (u^(N+1-j)*u^j)*(t^(j-1)*Real.exp (-u*t))/
        ((j : ℝ)*((j-1).factorial : ℝ)) := by ring
    _ = _ := by rw [← pow_add,Nat.sub_add_cancel hjN,hf]; ring

/-- The same exact cancellation in the complex physical response. -/
theorem gamma_factorial_collapse_complex (u t : ℝ) {N j : ℕ}
    (hj : 0 < j) (hjN : j ≤ N+1) :
    (u : ℂ)^(N+1-j)/(j : ℂ)*(gammaKernel u j t : ℂ) =
      (u : ℂ)^(N+1)*(Real.exp (-u*t) : ℂ)*(t : ℂ)^(j-1)/
        (j.factorial : ℂ) := by
  exact_mod_cast gamma_factorial_collapse u t hj hjN

/-- Exact three-slot rectangle probability. The second and third slots
are conditioned on their sum, exactly as in the original rectangleMass. -/
def continuousRectangleMass (N : ℕ) (t a b : ℝ) : ℝ :=
  rectangleMass N ((a+b)/(t+(a+b))) (a/(a+b))

theorem continuousRectangleMass_bounds (N : ℕ) {t a b : ℝ}
    (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a+b) :
    0 ≤ continuousRectangleMass N t a b ∧
      continuousRectangleMass N t a b ≤ 1 := by
  have hT : 0 < t+(a+b) := by linarith
  have hx : 0 ≤ (a+b)/(t+(a+b)) := div_nonneg hab.le hT.le
  have hx1 : (a+b)/(t+(a+b)) ≤ 1 := (div_le_one hT).mpr (by linarith)
  have hc : 0 ≤ a/(a+b) := div_nonneg ha hab.le
  have hc1 : a/(a+b) ≤ 1 := (div_le_one hab).mpr (by linarith)
  exact ⟨(rectangleMass_bounds N hx hx1 hc hc1).1,
    (rectangleMass_bounds N hx hx1 hc hc1).2.trans
      (rectangleMarginal_bounds N hx hx1).2⟩

theorem factorial_atom_eq_mass (N j h : ℕ) (hj : j ≤ N+1)
    (hh : h ≤ N+1-j) (t a b : ℝ) (hab : a+b ≠ 0) (hT : t+(a+b) ≠ 0) :
    t^j/(j.factorial : ℝ)*(a^h/(h.factorial : ℝ))*
        (b^(N+1-j-h)/((N+1-j-h).factorial : ℝ)) =
      (t+(a+b))^(N+1)/((N+1).factorial : ℝ)*
        mass (N+1) j (1-(a+b)/(t+(a+b)))*
        mass (N+1-j) h (a/(a+b)) := by
  have he : 1-(a+b)/(t+(a+b)) = t/(t+(a+b)) := by field_simp; ring
  rw [he,mass_as_factorials (N+1) j hj t (a+b) hT,
    mass_as_factorials (N+1-j) h hh a b hab]
  have hf : ((N+1).factorial : ℝ) ≠ 0 := by positivity
  have hf' : ((N+1-j).factorial : ℝ) ≠ 0 := by positivity
  have hp := pow_ne_zero (N+1) hT
  have hp' := pow_ne_zero (N+1-j) hab
  field_simp

/-- All three factorial slots collapse into the original finite
multinomial probability, with every integer endpoint unchanged. -/
theorem rectangle_factorial_collapse (N : ℕ) (t a b : ℝ)
    (hab : a+b ≠ 0) (hT : t+(a+b) ≠ 0) :
    (∑ j ∈ Finset.range (N+2), ∑ h ∈ rectangleOrders N j,
      t^j/(j.factorial : ℝ)*(a^h/(h.factorial : ℝ))*
        (b^(N+1-j-h)/((N+1-j-h).factorial : ℝ))) =
      (t+(a+b))^(N+1)/((N+1).factorial : ℝ)*
        continuousRectangleMass N t a b := by
  unfold continuousRectangleMass rectangleMass
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro h hh
  rw [← mul_assoc]
  exact factorial_atom_eq_mass N j h (by have := Finset.mem_range.mp hj; omega)
    (by have := Finset.mem_range.mp (Finset.mem_filter.mp hh).1; omega) t a b hab hT

/-- The exact complementary factorial rectangle on the same three
coordinates. This is not an identification with the arithmetic rest. -/
def continuousRectangleComplement (N : ℕ) (t a b : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N+2), mass (N+1) j (t/(t+(a+b)))*
    ∑ h ∈ Finset.range (N+1-j+1) \ rectangleOrders N j,
      mass (N+1-j) h (a/(a+b))

/-- Recombination is exact when BOTH fractions use the same coordinates.
This theorem supplies no change of marked-prime measure. -/
theorem rectangle_add_complement (N : ℕ) (t a b : ℝ) (hT : t+(a+b) ≠ 0) :
    continuousRectangleMass N t a b+continuousRectangleComplement N t a b = 1 := by
  have he : 1-(a+b)/(t+(a+b)) = t/(t+(a+b)) := by field_simp; ring
  unfold continuousRectangleMass rectangleMass continuousRectangleComplement
  rw [he,← Finset.sum_add_distrib]
  calc
    _ = ∑ j ∈ Finset.range (N+2), mass (N+1) j (t/(t+(a+b)))*
        ∑ h ∈ Finset.range (N+1-j+1), mass (N+1-j) h (a/(a+b)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [← mul_add,add_comm (∑ h ∈ rectangleOrders N j, _)]
      congr 1
      exact Finset.sum_sdiff
        (show rectangleOrders N j ⊆ Finset.range (N+1-j+1) from Finset.filter_subset _ _)
    _ = 1 := by simp only [mass_total,mul_one]

/-- The marked zero-order boundary of full multinomial mass is explicit.
It cannot be represented by a positive-order Gamma probability. -/
theorem zero_marked_mass (N : ℕ) (t a b : ℝ) (hT : t+(a+b) ≠ 0) :
    mass (N+1) 0 (t/(t+(a+b))) = ((a+b)/(t+(a+b)))^(N+1) := by
  have he : 1-t/(t+(a+b)) = (a+b)/(t+(a+b)) := by field_simp; ring
  simp [mass,he]

/-- Extending the Gamma orders to ALL positive marked orders has mass
one MINUS the zero-order boundary, rather than mass one. -/
theorem positive_marked_mass (N : ℕ) (t a b : ℝ) (hT : t+(a+b) ≠ 0) :
    (∑ j ∈ (Finset.range (N+2)).erase 0,
      mass (N+1) j (t/(t+(a+b)))) =
        1-((a+b)/(t+(a+b)))^(N+1) := by
  have hh := Finset.sum_erase_add (Finset.range (N+2))
    (fun j => mass (N+1) j (t/(t+(a+b)))) (by simp : 0 ∈ Finset.range (N+2))
  rw [mass_total,zero_marked_mass N t a b hT] at hh
  linarith

/-- After factorial collapse, the full positive-order kernel is the
regular divided difference with its zero-order numerator subtracted. -/
theorem positive_factorial_collapse (N : ℕ) (t a b : ℝ)
    (hab : a+b ≠ 0) (hT : t+(a+b) ≠ 0) :
    (∑ j ∈ (Finset.range (N+2)).erase 0, ∑ h ∈ Finset.range (N+1-j+1),
      t^j/(j.factorial : ℝ)*(a^h/(h.factorial : ℝ))*
        (b^(N+1-j-h)/((N+1-j-h).factorial : ℝ))) =
      ((t+(a+b))^(N+1)-(a+b)^(N+1))/((N+1).factorial : ℝ) := by
  have he : 1-(a+b)/(t+(a+b)) = t/(t+(a+b)) := by field_simp; ring
  calc
    _ = (t+(a+b))^(N+1)/((N+1).factorial : ℝ)*
        ∑ j ∈ (Finset.range (N+2)).erase 0, mass (N+1) j (t/(t+(a+b))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjN : j ≤ N+1 := by
        have := Finset.mem_range.mp (Finset.mem_erase.mp hj).2
        omega
      calc
        _ = ((t+(a+b))^(N+1)/((N+1).factorial : ℝ)*
            mass (N+1) j (t/(t+(a+b))))*
              ∑ h ∈ Finset.range (N+1-j+1), mass (N+1-j) h (a/(a+b)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro h hh
          rw [← he]
          exact factorial_atom_eq_mass N j h hjN
            (by have := Finset.mem_range.mp hh; omega) t a b hab hT
        _ = _ := by rw [mass_total,mul_one]
    _ = _ := by
      rw [positive_marked_mass N t a b hT,div_pow]
      field_simp

/-- The existing Fubini theorem supplies integrability of the physical
average itself; no new arithmetic absolute-value estimate is needed. -/
theorem gamma_physical_integrable {u : ℝ} (hu : 0 < u)
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (h16 : ∀ p ∈ A, 16 ≤ p)
    {s : ℂ} (hs : 1/2 < s.re) {N j h : ℕ}
    (hh : h ∈ rectangleOrders N j) (L : ℝ) :
    IntegrableOn (fun t : ℝ => (gammaKernel u j t : ℂ)*
      physicalCofactor A N j h s (L-t)) (Ioi 0) := by
  have hc := cofactor_integrable A h16 hs hh
  have hi := (ZetaRieszSelectedPhysical.gamma_pair_integrable hu j _
    (cofactor_measurable A h16 hs hh) hc.1 hc.2 L).integral_prod_left
  apply (hi.const_mul (-1/(2*(Real.pi : ℂ)))).congr
  filter_upwards with t
  rw [integral_const_mul]
  calc
    _ = (gammaKernel u j t : ℂ)*(-1/(2*(Real.pi : ℂ))*
        ∫ xi : ℝ in Ioi 0,
          ZetaRieszSelectedPhysical.pair
            (ZetaRieszMarkedPrimeCompletion.cofactor A N j h s) (L-t) xi/
              (xi : ℂ)^2) := by ring
    _ = _ := by rw [cofactor_pair_integral A hA h16 hs hh (L-t)]

/-- One integral for the whole selected rectangle, with the marked
factorial normalization already collapsed. Both factorial sums remain
inside the same signed integral. -/
theorem selectedResponse_eq_collapsed_integral {u : ℝ} (hu : 0 < u)
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y L : ℝ) :
    (u : ℂ)^(N+1)*selectedResponse A N u y L =
      -((N+1 : ℕ) : ℂ)/(L : ℂ)*(u : ℂ)^(N+1)*
        ∫ t : ℝ in Ioi 0, (Real.exp (-u*t) : ℂ)*
          ∑ j ∈ Finset.range (N+2), ∑ h ∈ rectangleOrders N j,
            ((t : ℂ)^(j-1)/(j.factorial : ℂ))*
              physicalCofactor A N j h (3/2+Complex.I*y) (L-t) := by
  have hs : (1/2 : ℝ) < (3/2+Complex.I*(y : ℂ)).re := by norm_num
  have hi (j : ℕ) (h : ℕ) (hh : h ∈ rectangleOrders N j) :
      IntegrableOn (fun t : ℝ => ((u : ℂ)^(N+1-j)/(j : ℂ))*
        ((gammaKernel u j t : ℂ)*physicalCofactor A N j h
          (3/2+Complex.I*y) (L-t))) (Ioi 0) :=
    (gamma_physical_integrable hu A hA h16 hs hh L).const_mul _
  rw [selectedResponse_eq_gamma_average hu A hA h16 N y L]
  have he :
      (∑ j ∈ Finset.range (N+2), ∑ h ∈ rectangleOrders N j,
        ((u : ℂ)^(N+1-j)/(j : ℂ))*(∫ t : ℝ in Ioi 0,
          (gammaKernel u j t : ℂ)*physicalCofactor A N j h
            (3/2+Complex.I*y) (L-t))) =
      (u : ℂ)^(N+1)*(∫ t : ℝ in Ioi 0, (Real.exp (-u*t) : ℂ)*
        ∑ j ∈ Finset.range (N+2), ∑ h ∈ rectangleOrders N j,
          ((t : ℂ)^(j-1)/(j.factorial : ℂ))*
            physicalCofactor A N j h (3/2+Complex.I*y) (L-t)) := by
    simp_rw [← integral_const_mul]
    simp_rw [← integral_finsetSum _ (fun h hh => hi _ h hh)]
    rw [← integral_finsetSum _ (fun j _ => integrable_finsetSum _
      (fun h hh => hi j h hh))]
    apply integral_congr_ae
    filter_upwards with t
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro h hh
    rw [← mul_assoc,gamma_factorial_collapse_complex u t
      (ZetaRieszMarkedLogDerivative.marked_order_pos hh)
      (by have := Finset.mem_range.mp hj; omega)]
    ring
  rw [he]
  ring

end
end RiemannGaussian.ZetaRieszGammaCollapse
