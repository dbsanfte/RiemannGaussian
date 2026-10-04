/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSeedHermiteQuotient
import RiemannGaussian.SemiprimeGeometricRows

/-!
# Arithmetic degree cost of geometric interval shift formulas

Endpoint cancellation is valid for the geometric interval family itself.
Its clearing denominator nevertheless needs one root for each original
root lost under shifting. The actual half-interval doubling shift loses
all its roots in both prime fields on the public long branch. A nonzero
clearing polynomial over the composite ring therefore has quadratic
degree even when its coefficients are nonunits.

The geometric coefficient recurrence also proves that every coefficient
of the actual half polynomial is a unit. Its full explicit polynomial
has at least m^2+2 nonzero coefficients; sparse cancellation of those
coefficients does not remove its quadratic source size.

These bounds concern polynomial functional identities in the target X.
They do not exclude interpolation only at the finite original seed
targets, additional state, or other specialized acquisition algorithms.
-/

namespace RiemannGaussian.SemiprimeSeedGeometricRecurrence

open scoped BigOperators
open Polynomial SemiprimeGeometricRows SemiprimeIntervalJet
open SemiprimeSeedSumAcquisition SemiprimeLocalOrderRouting SemiprimeCentreFreeCover
open SemiprimeLongPowerRouting
open SemiprimeWrapIndexRecovery SemiprimeSharedIntervalJet

/-- Literal geometric doubling uses an inverse half-length shift and
an exact unit phase. No evaluated factor is cancelled or inverted. -/
theorem rowPolynomial_doubling {R : Type*} [CommRing R] (alpha : Rˣ) (L : ℕ) :
    rowPolynomial (alpha : R) (L+L)=
      rowPolynomial (alpha : R) L*C (((alpha : R)^L)^L)*
        (rowPolynomial (alpha : R) L).comp (C ((((alpha^L)⁻¹ : Rˣ) : R))*X) := by
  have hi : (alpha : R)^L*((((alpha^L)⁻¹ : Rˣ) : R))=1 := by
    rw [←Units.val_pow_eq_pow_val]
    exact (alpha^L).mul_inv
  have hfactor (u : ℕ) : (X-C ((alpha : R)^(L+u)) : R[X])=
      C ((alpha : R)^L)*(C ((((alpha^L)⁻¹ : Rˣ) : R))*X-C ((alpha : R)^u)) := by
    rw [mul_sub,←mul_assoc,←C_mul,hi,C_1,one_mul,←C_mul,←pow_add]
  have hblock : blockPolynomial (alpha : R) L L=
      C (((alpha : R)^L)^L)*
        (rowPolynomial (alpha : R) L).comp (C ((((alpha^L)⁻¹ : Rˣ) : R))*X) := by
    simp only [blockPolynomial,rowPolynomial,SemiprimeCartesianCompletion.rootPolynomial,
      prod_comp,sub_comp,X_comp,C_comp]
    simp_rw [hfactor]
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_range,←map_pow]
  have hsplit := intervalPolynomial_split (alpha : R) L L
  change rowPolynomial (alpha : R) (L+L)=rowPolynomial (alpha : R) L*
    blockPolynomial (alpha : R) L L at hsplit
  rw [hsplit,hblock]
  ring

/-- Reduced multiplication correctly doubles the geometric interval
once the shifted remainder has also been acquired. Its availability
or acquisition cost is not supplied by this identity. -/
theorem rowPolynomial_doubling_remainder {R : Type*} [CommRing R]
    (alpha : Rˣ) (L : ℕ) (U : R[X]) :
    rowPolynomial (alpha : R) (L+L) %ₘ U=
      ((rowPolynomial (alpha : R) L %ₘ U)*
        ((C (((alpha : R)^L)^L)*
          (rowPolynomial (alpha : R) L).comp (C ((((alpha^L)⁻¹ : Rˣ) : R))*X)) %ₘ U)) %ₘ U := by
  rw [rowPolynomial_doubling,mul_assoc,mul_modByMonic]

/-- Original geometric root polynomials commute with any coefficient
ring homomorphism, including reductions to either hidden prime field. -/
theorem rowPolynomial_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R→+*S) (alpha : R) (L : ℕ) :
    (rowPolynomial alpha L).map f=rowPolynomial (f alpha) L := by
  simp only [rowPolynomial,SemiprimeCartesianCompletion.rootPolynomial,
    Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_pow,
    Polynomial.map_C,map_pow]

/-- Every original root lost under a positive scale shift must be a root
of its clearing denominator. An overlapping shift costs at least d
degrees; a disjoint shift costs the full original degree L. -/
theorem shift_tail_denominator_degree {R : Type*} [CommRing R] [IsDomain R]
    (alpha : R) {L d : ℕ} (hperiod : L+d≤orderOf alpha)
    (A D : R[X]) (hD : D≠0)
    (hrec : A*rowPolynomial alpha L=
      D*(rowPolynomial alpha L).comp (C (alpha^d)*X)) :
    min d L≤D.natDegree := by
  let k := min d L
  have hkL : k≤L := Nat.min_le_right _ _
  have hkd : k≤d := Nat.min_le_left _ _
  have hzero (i : Fin k) : D.eval (alpha^(L-k+i.val))=0 := by
    have hu : L-k+i.val<L := by omega
    have hroot : intervalProduct alpha (alpha^(L-k+i.val)) L=0 :=
      (intervalProduct_zero_iff _ _ _).mpr ⟨L-k+i.val,hu,rfl⟩
    have hnonzero : intervalProduct alpha (alpha^d*alpha^(L-k+i.val)) L≠0 := by
      intro hz
      obtain ⟨v,hv,he⟩ := (intervalProduct_zero_iff _ _ _).mp hz
      rw [←pow_add] at he
      have hfirst : d+(L-k+i.val)<orderOf alpha := by omega
      have hsecond : v<orderOf alpha := by omega
      have heq := pow_injOn_Iio_orderOf hfirst hsecond he
      omega
    have he := congrArg (fun P : R[X] => P.eval (alpha^(L-k+i.val))) hrec
    simp only [eval_mul,eval_comp,eval_X,eval_C,rowPolynomial_eval,hroot,mul_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_right hnonzero
  have hinj : Function.Injective (fun i : Fin k => alpha^(L-k+i.val)) := by
    intro i j he
    have hi : L-k+i.val<orderOf alpha := by omega
    have hj : L-k+j.val<orderOf alpha := by omega
    have heq := pow_injOn_Iio_orderOf hi hj he
    apply Fin.ext
    omega
  by_contra hn
  apply hD
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero D hinj hzero
  simpa only [Fintype.card_fin] using (show D.natDegree<k by omega)

/-- Endpoint cancellation induces an exact neighboring-coefficient
identity without dividing a coefficient or a power difference. -/
theorem geometric_coefficient_recurrence {R : Type*} [CommRing R]
    (alpha : R) (L k : ℕ) :
    alpha^L*(alpha^(k+1)-1)*(rowPolynomial alpha L).coeff (k+1)=
      (alpha^(k+1)-alpha^(L+1))*(rowPolynomial alpha L).coeff k := by
  have hpoly : C alpha*(X*(rowPolynomial alpha L).comp (C alpha*X))-
      C (alpha^L)*(rowPolynomial alpha L).comp (C alpha*X)=
      C (alpha^(L+1))*(X*rowPolynomial alpha L)-C (alpha^L)*rowPolynomial alpha L := by
    rw [pow_succ,C_mul]
    linear_combination adjacent_polynomial_telescoping alpha L
  have he := congrArg (fun P : R[X] => P.coeff (k+1)) hpoly
  simp only [coeff_sub,coeff_C_mul,coeff_X_mul,comp_C_mul_X_coeff] at he
  simp only [pow_succ] at he ⊢
  linear_combination -he

/-- The geometric product's constant coefficient is a unit whenever
its base is a unit, independently of its period. -/
theorem geometric_constant_coefficient_unit {R : Type*} [CommRing R]
    (alpha : Rˣ) (L : ℕ) : IsUnit ((rowPolynomial (alpha : R) L).coeff 0) := by
  induction L with
  | zero =>
    simpa only [rowPolynomial,SemiprimeCartesianCompletion.rootPolynomial,
      Finset.range_zero,Finset.prod_empty,coeff_one_zero] using (isUnit_one : IsUnit (1 : R))
  | succ L ih =>
    change IsUnit ((∏ u∈Finset.range (L+1), (X-C ((alpha : R)^u) : R[X])).coeff 0)
    rw [Finset.prod_range_succ,mul_coeff_zero,coeff_sub,coeff_X_zero,coeff_C_zero,zero_sub]
    exact ih.mul (alpha.isUnit.pow L).neg

/-- When all short base-power differences are units, every coefficient
of the geometric interval polynomial is a unit. Its full polynomial
therefore has no sparse-coefficient cancellation over a nontrivial ring. -/
theorem geometric_coefficients_unit {R : Type*} [CommRing R]
    (alpha : Rˣ) (L : ℕ)
    (hgaps : ∀ i, 0 < i → i ≤ L → IsUnit ((alpha : R)^i-1)) :
    ∀ k≤L, IsUnit ((rowPolynomial (alpha : R) L).coeff k) := by
  intro k
  induction k with
  | zero => intro _; exact geometric_constant_coefficient_unit alpha L
  | succ k ih =>
    intro hk
    have hprevious := ih (by omega : k≤L)
    have hpow : (alpha : R)^(k+1)*(alpha : R)^(L-k)=(alpha : R)^(L+1) := by
      rw [←pow_add]
      congr 1
      omega
    have hfactor : (alpha : R)^(k+1)-(alpha : R)^(L+1)=
        -(alpha : R)^(k+1)*((alpha : R)^(L-k)-1) := by
      linear_combination hpow
    have hnum : IsUnit ((alpha : R)^(k+1)-(alpha : R)^(L+1)) := by
      rw [hfactor]
      exact (alpha.isUnit.pow (k+1)).neg.mul (hgaps (L-k) (by omega) (by omega))
    have hresult := hnum.mul hprevious
    rw [←geometric_coefficient_recurrence (alpha : R) L k] at hresult
    exact isUnit_of_mul_isUnit_right hresult

/-- Inverse doubling shifts move every original root to a disjoint
interval when twice its length stays within the retained period. -/
theorem inverse_interval_nonzero {R : Type*} [CommRing R] [IsDomain R]
    (alpha : Rˣ) {L : ℕ} (hperiod : 2*L≤orderOf (alpha : R)) :
    ∀ u<L, intervalProduct (alpha : R)
      ((((alpha^L)⁻¹ : Rˣ) : R)*(alpha : R)^u) L≠0 := by
  intro u hu hz
  obtain ⟨v,hv,he⟩ := (intervalProduct_zero_iff _ _ _).mp hz
  have hi : ((alpha^L : Rˣ) : R)*(((alpha^L)⁻¹ : Rˣ) : R)=1 :=
    (alpha^L).val_inv
  have he' := congrArg (fun x : R => ((alpha^L : Rˣ) : R)*x) he
  rw [←mul_assoc,hi,one_mul,Units.val_pow_eq_pow_val,←pow_add] at he'
  have hfirst : u<orderOf (alpha : R) := by omega
  have hsecond : L+v<orderOf (alpha : R) := by omega
  have heq := pow_injOn_Iio_orderOf hfirst hsecond he'
  omega

/-- A rational functional identity for the inverse doubling shift also
needs a clearing denominator of at least the full interval degree. -/
theorem inverse_step_denominator_degree {R : Type*} [CommRing R] [IsDomain R]
    (alpha : Rˣ) {L : ℕ} (hperiod : 2*L≤orderOf (alpha : R))
    (A D : R[X]) (hD : D≠0)
    (hrec : A*rowPolynomial (alpha : R) L=
      D*(rowPolynomial (alpha : R) L).comp
        (C (((alpha^L)⁻¹ : Rˣ) : R)*X)) : L≤D.natDegree := by
  exact functional_step_denominator_degree (alpha : R) (((alpha^L)⁻¹ : Rˣ) : R)
    (by omega) A D hD (inverse_interval_nonzero alpha hperiod) hrec

/-- A nonzero polynomial over a distinct-prime semiprime ring has a
nonzero reduction in at least one field, without any unit-coefficient
or monicity hypothesis on that polynomial. -/
theorem nonzero_prime_polynomial_reduction {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (D : (ZMod (p*q))[X]) (hD : D≠0) :
    D.map (ZMod.castHom (dvd_mul_right p q) (ZMod p))≠0 ∨
      D.map (ZMod.castHom (dvd_mul_left q p) (ZMod q))≠0 := by
  by_cases hP : D.map (ZMod.castHom (dvd_mul_right p q) (ZMod p))=0
  · right
    intro hQ
    apply hD
    ext i
    have hPi := congrArg (fun P : (ZMod p)[X] => P.coeff i) hP
    have hQi := congrArg (fun P : (ZMod q)[X] => P.coeff i) hQ
    simp only [coeff_map,coeff_zero] at hPi hQi
    exact eq_of_prime_reductions hp hq hpq (D.coeff i) 0
      (by simpa only [map_zero] using hPi) (by simpa only [map_zero] using hQi)
  · exact Or.inl hP

/-- The cleared functional identity transports to every coefficient
ring before estimating its denominator degree. -/
theorem cleared_step_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R→+*S) (alpha c : R) (L : ℕ) (A D : R[X])
    (hrec : A*rowPolynomial alpha L=D*(rowPolynomial alpha L).comp (C c*X)) :
    A.map f*rowPolynomial (f alpha) L=
      D.map f*(rowPolynomial (f alpha) L).comp (C (f c)*X) := by
  have he := congrArg (fun P : R[X] => P.map f) hrec
  simpa only [Polynomial.map_mul,rowPolynomial_map,Polynomial.map_comp,
    Polynomial.map_C,Polynomial.map_X] using he

/-- A unit inverse-power shift reduces to the same inverse-power shift
in the target ring, preserving its orientation explicitly. -/
theorem unit_map_inverse_power_value {R S : Type*} [CommRing R] [CommRing S]
    (f : R→+*S) (alpha : Rˣ) (L : ℕ) :
    (((((Units.map f.toMonoidHom alpha)^L)⁻¹ : Sˣ) : S))=
      f ((((alpha^L)⁻¹ : Rˣ) : R)) := by
  rw [←map_pow,←map_inv]
  rfl

/-- Inverse cleared interval identities commute with reduction, with
the mapped unit and the exact original inverse shift both retained. -/
theorem inverse_cleared_step_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R→+*S) (alpha : Rˣ) (L : ℕ) (A D : R[X])
    (hrec : A*rowPolynomial (alpha : R) L=
      D*(rowPolynomial (alpha : R) L).comp (C ((((alpha^L)⁻¹ : Rˣ) : R))*X)) :
    A.map f*rowPolynomial ((Units.map f.toMonoidHom alpha : Sˣ) : S) L=
      D.map f*(rowPolynomial ((Units.map f.toMonoidHom alpha : Sˣ) : S) L).comp
        (C (((((Units.map f.toMonoidHom alpha)^L)⁻¹ : Sˣ) : S))*X) := by
  rw [unit_map_inverse_power_value]
  exact cleared_step_map f (alpha : R) ((((alpha^L)⁻¹ : Rˣ) : R)) L A D hrec

/-- The lost-root denominator bound holds over the original composite
ring as soon as the shift stays within both local periods. -/
theorem semiprime_shift_denominator_degree {p q L d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (alpha : ZMod (p*q))
    (hP : L+d≤orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p) alpha))
    (hQ : L+d≤orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q) alpha))
    (A D : (ZMod (p*q))[X]) (hD : D≠0)
    (hrec : A*rowPolynomial alpha L=
      D*(rowPolynomial alpha L).comp (C (alpha^d)*X)) : min d L≤D.natDegree := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  obtain hDP|hDQ := nonzero_prime_polynomial_reduction hp hq hpq D hD
  · have he := cleared_step_map (ZMod.castHom (dvd_mul_right p q) (ZMod p))
      alpha (alpha^d) L A D hrec
    rw [map_pow] at he
    exact (shift_tail_denominator_degree _ hP _ _ hDP he).trans natDegree_map_le
  · have he := cleared_step_map (ZMod.castHom (dvd_mul_left q p) (ZMod q))
      alpha (alpha^d) L A D hrec
    rw [map_pow] at he
    exact (shift_tail_denominator_degree _ hQ _ _ hDQ he).trans natDegree_map_le

/-- Inverse doubling has the same full-degree clearing cost over the
composite ring, even when the denominator survives in only one field. -/
theorem semiprime_inverse_denominator_degree {p q L : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (alpha : (ZMod (p*q))ˣ)
    (hP : 2*L≤orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p) (alpha : ZMod (p*q))))
    (hQ : 2*L≤orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q) (alpha : ZMod (p*q))))
    (A D : (ZMod (p*q))[X]) (hD : D≠0)
    (hrec : A*rowPolynomial (alpha : ZMod (p*q)) L=
      D*(rowPolynomial (alpha : ZMod (p*q)) L).comp
        (C ((((alpha^L)⁻¹ : (ZMod (p*q))ˣ) : ZMod (p*q)))*X)) : L≤D.natDegree := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  obtain hDP|hDQ := nonzero_prime_polynomial_reduction hp hq hpq D hD
  · have he := inverse_cleared_step_map (ZMod.castHom (dvd_mul_right p q) (ZMod p))
      alpha L A D hrec
    have hperiod := hP
    change 2*L≤orderOf (((Units.map
      (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom alpha) : (ZMod p)ˣ) : ZMod p)
      at hperiod
    exact (inverse_step_denominator_degree _ hperiod _ _ hDP he).trans natDegree_map_le
  · have he := inverse_cleared_step_map (ZMod.castHom (dvd_mul_left q p) (ZMod q))
      alpha L A D hrec
    have hperiod := hQ
    change 2*L≤orderOf (((Units.map
      (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom alpha) : (ZMod q)ˣ) : ZMod q)
      at hperiod
    exact (inverse_step_denominator_degree _ hperiod _ _ hDQ he).trans natDegree_map_le

/-- The original padded interval's literal half length for doubling. -/
def seedHalfLength (m : ℕ) : ℕ := seedLength m/2

/-- The actual half remains quadratic, its doubled length stays in the
original interval, and the possible leftover consists of one factor. -/
theorem seedHalfLength_bounds {m : ℕ} (hm : 4≤m) :
    m^2+1≤seedHalfLength m ∧ seedHalfLength m≤2*m^2 ∧
      2*seedHalfLength m≤seedLength m ∧ seedLength m-2*seedHalfLength m≤1 := by
  have hh := seedLength_bounds hm
  unfold seedHalfLength
  omega

/-- The geometric half-interval polynomial is part of the actual
original seed detector, not an arbitrary counterexample polynomial. -/
noncomputable def seedHalfPolynomial {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) : (ZMod N)[X] :=
  rowPolynomial ((seedBase g m : (ZMod N)ˣ) : ZMod N) (seedHalfLength m)

/-- The original half-interval polynomial has its literal exact degree. -/
theorem seedHalfPolynomial_natDegree {N : ℕ} [Nontrivial (ZMod N)]
    (g : (ZMod N)ˣ) (m : ℕ) : (seedHalfPolynomial g m).natDegree=seedHalfLength m := by
  simpa only [seedHalfPolynomial,rowPolynomial,SemiprimeCartesianCompletion.rootPolynomial,
    Finset.card_range] using natDegree_finsetProd_X_sub_C_eq_card (Finset.range (seedHalfLength m))
      (fun i => (((seedBase g m : (ZMod N)ˣ) : ZMod N)^i))

/-- Every base-power difference needed by the half-interval coefficient
recurrence is a unit on the actual long branch, in both hidden fields. -/
theorem long_seedHalf_power_gaps_unit {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    ∀ i, 0 < i → i ≤ seedHalfLength m →
      IsUnit ((((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))^i)-1) := by
  have hperiods := long_seed_interval_periods hm g hlong
  have hhalf := seedHalfLength_bounds hm
  intro i hi hik
  apply isUnit_of_prime_reductions hp hq
  · rw [map_sub,map_pow,map_one]
    apply sub_ne_zero.mpr
    intro hpower
    have hfirst : i<orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
        ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))) := by omega
    have he := pow_injOn_Iio_orderOf hfirst
      (show 0<orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
        ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))) by omega)
      (by simpa only [pow_zero] using hpower)
    omega
  · rw [map_sub,map_pow,map_one]
    apply sub_ne_zero.mpr
    intro hpower
    have hfirst : i<orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
        ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))) := by omega
    have he := pow_injOn_Iio_orderOf hfirst
      (show 0<orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
        ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))) by omega)
      (by simpa only [pow_zero] using hpower)
    omega

/-- Every coefficient of the actual geometric half polynomial is a
unit; the polynomial cannot become sparse by coefficient cancellation. -/
theorem long_seedHalf_coeff_unit {p q m k : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) (hk : k≤seedHalfLength m) :
    IsUnit ((seedHalfPolynomial (projectedUnit g m) m).coeff k) := by
  exact geometric_coefficients_unit (seedBase (projectedUnit g m) m) (seedHalfLength m)
    (long_seedHalf_power_gaps_unit hp hq hm g hlong) k hk

/-- All actual half-interval coefficients are literally nonzero in the
original semiprime ring, not merely nonzero in a selected field. -/
theorem long_seedHalf_coeff_ne_zero {p q m k : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) (hk : k≤seedHalfLength m) :
    (seedHalfPolynomial (projectedUnit g m) m).coeff k≠0 := by
  let : Fact (1<p*q) := ⟨by nlinarith only [hp.one_lt,hq.one_lt]⟩
  exact (long_seedHalf_coeff_unit hp hq hm g hlong hk).ne_zero

/-- The actual half polynomial has exactly K+1 nonzero coefficients,
which is at least m^2+2. This counts the full explicit polynomial,
not a reduced carrier or the size of every possible arithmetic circuit. -/
theorem long_seedHalf_dense_support {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    m^2+2≤(seedHalfPolynomial (projectedUnit g m) m).support.card ∧
      (seedHalfPolynomial (projectedUnit g m) m).support.card=seedHalfLength m+1 := by
  let : Fact (1<p*q) := ⟨by nlinarith only [hp.one_lt,hq.one_lt]⟩
  have hs : (seedHalfPolynomial (projectedUnit g m) m).support=
      Finset.range (seedHalfLength m+1) := by
    ext k
    simp only [mem_support_iff,Finset.mem_range]
    constructor
    · intro hk
      have hle := le_natDegree_of_ne_zero hk
      rw [seedHalfPolynomial_natDegree] at hle
      omega
    · intro hk
      exact long_seedHalf_coeff_ne_zero hp hq hm g hlong (by omega)
  rw [hs,Finset.card_range]
  have hh := (seedHalfLength_bounds hm).1
  exact ⟨by omega,rfl⟩

/-- The forward doubling shift of the actual half-interval polynomial
requires a quadratic-degree denominator on the long branch. -/
theorem long_seedHalf_forward_degree {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (A D : (ZMod (p*q))[X]) (hD : D≠0)
    (hrec : A*seedHalfPolynomial (projectedUnit g m) m=
      D*(seedHalfPolynomial (projectedUnit g m) m).comp
        (C ((((seedBase (projectedUnit g m) m)^(seedHalfLength m) : (ZMod (p*q))ˣ) :
          ZMod (p*q)))*X)) : m^2+1≤D.natDegree := by
  have hperiods := long_seed_interval_periods hm g hlong
  have hhalf := seedHalfLength_bounds hm
  have htwice : seedHalfLength m+seedHalfLength m≤seedLength m := by omega
  have he := semiprime_shift_denominator_degree hp hq hpq
    ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))
    (htwice.trans hperiods.1) (htwice.trans hperiods.2) A D hD
    (by simpa only [seedHalfPolynomial,Units.val_pow_eq_pow_val] using hrec)
  rw [Nat.min_self] at he
  exact hhalf.1.trans he

/-- The inverse shift appearing in literal geometric doubling requires
the same quadratic clearing degree for the actual half interval. -/
theorem long_seedHalf_inverse_degree {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (A D : (ZMod (p*q))[X]) (hD : D≠0)
    (hrec : A*seedHalfPolynomial (projectedUnit g m) m=
      D*(seedHalfPolynomial (projectedUnit g m) m).comp
        (C (((((seedBase (projectedUnit g m) m)^(seedHalfLength m))⁻¹ : (ZMod (p*q))ˣ) :
          ZMod (p*q)))*X)) : m^2+1≤D.natDegree := by
  have hperiods := long_seed_interval_periods hm g hlong
  have hhalf := seedHalfLength_bounds hm
  exact hhalf.1.trans (semiprime_inverse_denominator_degree hp hq hpq
    (seedBase (projectedUnit g m) m) (hhalf.2.2.1.trans hperiods.1)
    (hhalf.2.2.1.trans hperiods.2) A D hD hrec)

/-- The actual matched-width public long output has a dense half
polynomial with unit coefficients and a quadratic clearing degree for
either orientation of a functional doubling shift. -/
theorem actual_public_route_geometric_checkpoint {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      (∀ k≤seedHalfLength m, IsUnit ((seedHalfPolynomial h m).coeff k)) ∧
      (m^2+2≤(seedHalfPolynomial h m).support.card ∧
        (seedHalfPolynomial h m).support.card=seedHalfLength m+1) ∧
      ∀ A D : (ZMod (p*q))[X], D≠0→
        (A*seedHalfPolynomial h m=(D*(seedHalfPolynomial h m).comp
          (C ((((seedBase h m)^(seedHalfLength m) : (ZMod (p*q))ˣ) : ZMod (p*q)))*X)) ∨
        A*seedHalfPolynomial h m=(D*(seedHalfPolynomial h m).comp
          (C (((((seedBase h m)^(seedHalfLength m))⁻¹ : (ZMod (p*q))ˣ) : ZMod (p*q)))*X)))→
        m^2+1≤D.natDegree := by
  have hdata := routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hdata
  obtain ⟨hc,hlong⟩ := hdata
  let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
  have hN := Nat.mul_pos hp.pos hq.pos
  have hbounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hm : 4≤m := hB.trans hbounds.1
  refine ⟨hc,?_⟩
  dsimp only
  refine ⟨?_,long_seedHalf_dense_support hp hq hm _ hlong,?_⟩
  · intro k hk
    exact long_seedHalf_coeff_unit hp hq hm _ hlong hk
  · intro A D hD hrec
    rcases hrec with hforward|hinverse
    · exact long_seedHalf_forward_degree hp hq hpq.ne hm _ hlong A D hD hforward
    · exact long_seedHalf_inverse_degree hp hq hpq.ne hm _ hlong A D hD hinverse

end RiemannGaussian.SemiprimeSeedGeometricRecurrence
