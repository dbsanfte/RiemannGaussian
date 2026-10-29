/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1HermiteNodes
import RiemannGaussian.SemiprimeD1ScaledHermite

/-! # Original D.9 from acquired retained-vector local weights
The global identity uses the actual original tapered grid. Returned child jets
are still an internal input whose coefficient refinement must be supplied by
the future recursive caller; no Hermite-answer or weight oracle is assumed.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1HermiteOriginal
open scoped BigOperators
open Polynomial SemiprimeD1WireKernelOriginal SemiprimeD1TaperedLoss
  SemiprimeD1JetRecoveryGrid SemiprimeD1JetRecoveryWeights
  SemiprimeD1HermiteIdentity SemiprimeD1HermiteNodes SemiprimeHermiteRecovery
  SemiprimeJetArray SemiprimeJetRecurrence

/-- Original active-grid cardinal factor, indexed without a node inverse/choice. -/
noncomputable def E (a h u t : ℕ) : ℚ[X] :=
  cardinal (active a h u) (node a) (nodeMultiplicity a h u) t

/-- Actual original alpha=2L as a scalar rational, not an interpolation point. -/
def alpha (a : ℕ) : ℚ := (2:ℚ)^(a+1)

/-- All omitted inactive original factors are literal exponent0; active cardinal
and complete original-grid product are therefore exactly the same polynomial. -/
theorem E_product (a h u t : ℕ) : E a h u t=
    ∏ q∈others a t,((X-C (node a q))*C ((node a t-node a q)⁻¹))^nodeMultiplicity a h u q := by
  unfold E cardinal
  apply Finset.prod_subset
  · intro q hq
    obtain ⟨hqt,hqa⟩ := Finset.mem_erase.mp hq
    obtain ⟨hqr,hqc,_⟩ := Finset.mem_filter.mp hqa
    exact Finset.mem_erase.mpr ⟨hqt,Finset.mem_erase.mpr ⟨hqc,hqr⟩⟩
  · intro q hq hnot
    have hqt := (Finset.mem_erase.mp hq).1
    have hqc := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
    have hqr := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).2
    have hm : nodeMultiplicity a h u q=0 := by
      by_contra hm
      apply hnot
      exact Finset.mem_erase.mpr ⟨hqt,Finset.mem_filter.mpr ⟨hqr,hqc,Nat.pos_of_ne_zero hm⟩⟩
    simp only [hm,pow_zero]

/-- Actual original E_t(0), including signs and unit amplitudes, matches its acquired scalar. -/
theorem E_zero (a h u t : ℕ) : (E a h u t).eval 0=Ezero a h u t := by
  rw [E_product,eval_prod]
  simp only [eval_pow,eval_mul,eval_sub,eval_X,eval_C,zero_sub,Ezero,node,div_eq_mul_inv]

/-- Original scaled local cardinal factor is the actual acquired affine product. -/
theorem E_local (a h u t : ℕ) :
    (E a h u t).comp (SemiprimeD1ScaledHermite.affine (alpha a) (node a t))=localCardinal a h u t := by
  rw [E_product]
  simp only [prod_comp,pow_comp]
  apply Finset.prod_congr rfl
  intro q hq
  have hqt : q≠t := (Finset.mem_erase.mp hq).1
  have hdiff : node a t-node a q≠0 := sub_ne_zero.mpr
    (fun he => hqt ((node_injective a) he.symm))
  have hi : (C (node a t)-C (node a q))*C ((node a t-node a q)⁻¹)=(1:ℚ[X]) := by
    rw [← C_sub,← C_mul,mul_inv_cancel₀ hdiff,C_1]
  congr 1
  simp only [mul_comp,sub_comp,X_comp,C_comp,SemiprimeD1ScaledHermite.affine]
  have he : (C (node a t)+C (alpha a)*X-C (node a q))*C ((node a t-node a q)⁻¹)=
      1+C ((alpha a)/(node a t-node a q))*X := by
    rw [div_eq_mul_inv,C_mul]
    calc
      _ = (C (node a t)-C (node a q))*C ((node a t-node a q)⁻¹)+
          C (alpha a)*C ((node a t-node a q)⁻¹)*X := by ring
      _ = _ := by rw [hi]
  simpa only [localCardinal,alpha,node,Int.cast_pow,Int.cast_ofNat] using he

/-- EXACT ORIGINAL D.9 at zero from only retained scaled packets, with all actual
node/taper/degree conditions discharged. -/
theorem original_scaled_at_zero (a M u : ℕ) (hu : 0<u) (hM : u≤M) (H : ℚ[X])
    (hH : H.natDegree≤M*(2*(2^a)-1)) :
    H.eval 0=∑ t∈active a (height M u) u,Ezero a (height M u) u t*
      (localQuotient
        ((H.comp (SemiprimeD1ScaledHermite.affine (alpha a) (node a t)))%ₘ X^nodeMultiplicity a (height M u) u t)
        (localCardinal a (height M u) u t) (nodeMultiplicity a (height M u) u t)).eval (-(node a t)/alpha a) := by
  have he := SemiprimeD1ScaledHermite.at_zero (active a (height M u) u) (node a)
    (nodeMultiplicity a (height M u) u) (node_injective a).injOn
    (fun t ht => active_positive a (height M u) u t ht) (alpha a) (by unfold alpha;positivity)
    H (hH.trans_lt (original_degree_sufficient a M u hu hM))
  change H.eval 0=∑ t∈active a (height M u) u,(E a (height M u) u t).eval 0*
    (localQuotient _ ((E a (height M u) u t).comp _) _).eval _ at he
  simp_rw [E_zero,E_local] at he
  exact he

/-- Actual retained coefficient array is equal to a scalar polynomial truncation
when its OWN stored coefficients match; no recovered answer is supplied. -/
theorem array_eq_packet (J : ℕ) (H : Array ℚ) (P : ℚ[X]) (hsize : H.size=J)
    (hcoeff : ∀j<J,coefficient H j=P.coeff j) : asPolynomial H=P%ₘ X^J := by
  ext j
  rw [asPolynomial_coeff,coeff_mod_X_pow]
  by_cases hj : j<J
  · simp only [hj,ite_true]
    exact hcoeff j hj
  · simp only [hj,ite_false]
    exact coefficient_zero (by omega)

/-- ORIGINAL acquired local scalar weight arrays recover H(0), given the actual
retained child-jet coefficient refinement. This is the linear-vector stage contract. -/
theorem recover_from_retained_arrays (a M u : ℕ) (hu : 0<u) (hM : u≤M) (H : ℚ[X])
    (hH : H.natDegree≤M*(2*(2^a)-1)) (packets : ℕ→Array ℚ)
    (hsize : ∀t∈active a (height M u) u,(packets t).size=nodeMultiplicity a (height M u) u t)
    (hcoeff : ∀t∈active a (height M u) u,∀j<nodeMultiplicity a (height M u) u t,
      coefficient (packets t) j=(H.comp (SemiprimeD1ScaledHermite.affine (alpha a) (node a t))).coeff j) :
    H.eval 0=∑ t∈active a (height M u) u,∑ j∈Finset.range (nodeMultiplicity a (height M u) u t),
      coefficient (acquire a (height M u) u t).weights j*coefficient (packets t) j := by
  rw [original_scaled_at_zero a M u hu hM H hH]
  apply Finset.sum_congr rfl
  intro t ht
  have hq := active_positive a (height M u) u t ht
  have hp := array_eq_packet _ (packets t) _ (hsize t ht) (hcoeff t ht)
  rw [← hp]
  rw [← SemiprimeHermiteArrayHeight.denominator_truncate (asPolynomial (packets t))
    (localCardinal a (height M u) u t) _ hq (localCardinal_constant a (height M u) u t)]
  exact original_node_formula a (height M u) u t (packets t) hq

/-- Finite FREE original-algebra coordinates recover by the same acquired scalar
weights; no evaluation homomorphism on nilpotent quotients is assumed. -/
theorem recover_coordinates (a M u c : ℕ) (hu : 0<u) (hM : u≤M) (H : Fin c→ℚ[X])
    (hH : ∀d,(H d).natDegree≤M*(2*(2^a)-1)) (packets : Fin c→ℕ→Array ℚ)
    (hsize : ∀d,∀t∈active a (height M u) u,(packets d t).size=nodeMultiplicity a (height M u) u t)
    (hcoeff : ∀d,∀t∈active a (height M u) u,∀j<nodeMultiplicity a (height M u) u t,
      coefficient (packets d t) j=((H d).comp (SemiprimeD1ScaledHermite.affine (alpha a) (node a t))).coeff j) :
    (fun d => (H d).eval 0)=fun d => ∑ t∈active a (height M u) u,
      ∑ j∈Finset.range (nodeMultiplicity a (height M u) u t),
        coefficient (acquire a (height M u) u t).weights j*coefficient (packets d t) j := by
  funext d
  exact recover_from_retained_arrays a M u hu hM (H d) (hH d) (packets d) (hsize d) (hcoeff d)

end RiemannGaussian.SemiprimeD1HermiteOriginal
