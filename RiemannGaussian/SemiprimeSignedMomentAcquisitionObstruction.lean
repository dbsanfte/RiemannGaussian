/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSeedEnergyAcquisitionObstruction
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic


/-!
# Signed common-point filters retain the original arithmetic energy obstruction

A nonzero polynomial filter in an injective common character can remove
at most its degree many original grid poles. Exact signed label grouping
retains each surviving positive multiplicity. The literal original carry
energy therefore bounds the denominator degree plus the filter degree.

The investigation journal combines this finite source theorem with the
preserved actual infinite family. Its dense signed-carrier acquisition
obstruction holds simultaneously for all widths and full-input adaptive
filters. Separate shared column masks can telescope to small endpoint
carriers; cyclotomic column factors add no new low-index moment gcd signal.
Arbitrary independent signed masks, smaller internal pivots, implicit
representations and the full factorization bit bound remain outside scope.
-/

namespace RiemannGaussian.SemiprimeSignedMomentAcquisitionObstruction

open scoped BigOperators
open Polynomial RiemannGaussian.SemiprimeSeedMomentPoleRetention

/-- A nonzero common-point filter deletes at most its degree many poles
after any injective change of the points used to evaluate the filter. -/
theorem injective_filter_denominator_degree {K : Type*} [Field K]
    (S : Finset K) (mu phi : K → K) (hx : ∀ x ∈ S, x ≠ 0)
    (hmu : ∀ x ∈ S, mu x ≠ 0) (hphi : Set.InjOn phi S)
    (W U V : K[X]) (hW : W ≠ 0) (hU : U.coeff 0 = 1)
    (hUV : (U : PowerSeries K) *
      (∑ x ∈ S, PowerSeries.C (mu x * W.eval (phi x)) * positiveMoments x) =
      (V : PowerSeries K)) :
    S.card ≤ U.natDegree + W.natDegree := by
  classical
  let T := S.filter fun x => W.eval (phi x) ≠ 0
  let Z := S.filter fun x => W.eval (phi x) = 0
  have hsum : (∑ x ∈ T, PowerSeries.C (mu x * W.eval (phi x)) * positiveMoments x) =
      (∑ x ∈ S, PowerSeries.C (mu x * W.eval (phi x)) * positiveMoments x) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hxS hxT
    have hz : W.eval (phi x) = 0 := by
      by_contra hne
      exact hxT (Finset.mem_filter.mpr ⟨hxS, hne⟩)
    simp only [hz, mul_zero, map_zero, zero_mul]
  have hT : T.card ≤ U.natDegree := by
    apply weighted_denominator_degree T (fun x => mu x * W.eval (phi x))
      (fun x hxT => hx x (Finset.mem_filter.mp hxT).1)
      (fun x hxT => mul_ne_zero (hmu x (Finset.mem_filter.mp hxT).1)
        (Finset.mem_filter.mp hxT).2) U V hU
    rw [hsum]
    exact hUV
  have hinj : Set.InjOn phi Z := fun x hxZ y hyZ h =>
    hphi (Finset.mem_filter.mp hxZ).1 (Finset.mem_filter.mp hyZ).1 h
  have hZ : Z.card ≤ W.natDegree := by
    rw [←Finset.card_image_of_injOn hinj]
    apply Polynomial.card_le_degree_of_subset_roots
    intro y hy
    obtain ⟨x, hxZ, rfl⟩ := Finset.mem_image.mp hy
    exact (Polynomial.mem_roots hW).mpr (Finset.mem_filter.mp hxZ).2
  have hcard : S.card = T.card + Z.card := by
    dsimp only [T, Z]
    simpa only [not_not] using
      (Finset.card_filter_add_card_filter_not (s := S)
        (p := fun x => W.eval (phi x) ≠ 0)).symm
  rw [hcard]
  exact Nat.add_le_add hT hZ

/-- Exact weights depending only on the point may be pulled through
label grouping; all original positive multiplicities are preserved. -/
theorem weighted_labelled_moments_group {R ι : Type*} [CommRing R] [DecidableEq R]
    (I : Finset ι) (x : ι → R) (weight : R → R) :
    (∑ i ∈ I, PowerSeries.C (weight (x i)) * positiveMoments (x i)) =
      ∑ y ∈ I.image x, PowerSeries.C
        ((((I.filter fun i => x i = y).card : ℕ) : R) * weight y) * positiveMoments y := by
  classical
  rw [←Finset.sum_fiberwise_of_maps_to
    (fun i hi => Finset.mem_image_of_mem x hi)
    (fun i => PowerSeries.C (weight (x i)) * positiveMoments (x i))]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_congr rfl (fun i hi =>
    congrArg (fun a => PowerSeries.C (weight a) * positiveMoments a)
      (Finset.mem_filter.mp hi).2)]
  ext r
  simp only [Finset.sum_const, nsmul_eq_mul, map_mul]
  simp [mul_assoc]

/-- Signed filtering of a labelled prime-field family retains all but
the filter degree of its distinct poles. Only individual positive fibres
must lie below the characteristic. -/
theorem labelled_injective_filter_denominator_degree {p : ℕ} {ι : Type*}
    (hp : p.Prime) (I : Finset ι) (x : ι → ZMod p) (phi : ZMod p → ZMod p)
    (hfiber : ∀ y ∈ I.image x, (I.filter fun i => x i = y).card < p)
    (hx : ∀ i ∈ I, x i ≠ 0) (hphi : Set.InjOn phi (I.image x))
    (W U V : (ZMod p)[X]) (hW : W ≠ 0) (hU : U.coeff 0 = 1)
    (hUV : (U : PowerSeries (ZMod p)) *
      (∑ i ∈ I, PowerSeries.C (W.eval (phi (x i))) * positiveMoments (x i)) =
      (V : PowerSeries (ZMod p))) :
    (I.image x).card ≤ U.natDegree + W.natDegree := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  rw [weighted_labelled_moments_group I x (fun y => W.eval (phi y))] at hUV
  apply injective_filter_denominator_degree (I.image x)
    (fun y => (((I.filter fun i => x i = y).card : ℕ) : ZMod p)) phi
    (by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact hx i hi)
    (by
      intro y hy
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hy
      have hpos : 0 < (I.filter fun j => x j = y).card :=
        Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, he⟩⟩
      exact fun hz => Nat.not_dvd_of_pos_of_lt hpos
        (hfiber y (Finset.mem_image.mpr ⟨i, hi, he⟩))
        ((ZMod.natCast_eq_zero_iff _ _).mp hz))
    hphi W U V hW hU hUV

/-- The original kind of geometric row grid needs only M<p, because
each row contributes at most once to a local point. The filter may have
arbitrary signed coefficients. -/
theorem geometric_grid_filtered_denominator_degree {p M J : ℕ}
    (hp : p.Prime) (x : Fin M → (ZMod p)ˣ) (beta : (ZMod p)ˣ)
    (hJ : J ≤ orderOf beta) (hM : M < p) (phi : ZMod p → ZMod p)
    (hphi : Set.InjOn phi
      ((Finset.univ : Finset (Fin M × Fin J)).image
        fun ik => (((x ik.1) * beta ^ ik.2.val : (ZMod p)ˣ) : ZMod p)))
    (W U V : (ZMod p)[X]) (hW : W ≠ 0) (hU : U.coeff 0 = 1)
    (hUV : (U : PowerSeries (ZMod p)) *
      (∑ ik : Fin M × Fin J, PowerSeries.C
        (W.eval (phi (((x ik.1) * beta ^ ik.2.val : (ZMod p)ˣ) : ZMod p))) *
        positiveMoments ((((x ik.1) * beta ^ ik.2.val : (ZMod p)ˣ) : ZMod p))) =
      (V : PowerSeries (ZMod p))) :
    ((Finset.univ : Finset (Fin M × Fin J)).image
      fun ik => (((x ik.1) * beta ^ ik.2.val : (ZMod p)ˣ) : ZMod p)).card ≤
        U.natDegree + W.natDegree := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  apply labelled_injective_filter_denominator_degree hp Finset.univ
    (fun ik : Fin M × Fin J => (((x ik.1) * beta ^ ik.2.val : (ZMod p)ˣ) : ZMod p)) phi
    (by
      intro y _
      have hcap := Finset.card_le_card_of_injOn
        (s := ((Finset.univ : Finset (Fin M × Fin J)).filter
          fun ik => (((x ik.1) * beta ^ ik.2.val : (ZMod p)ˣ) : ZMod p) = y))
        (t := (Finset.univ : Finset (Fin M))) (fun ik => ik.1)
        (fun _ _ => Finset.mem_univ _)
        (by
          intro a ha b hb he
          have hpoint : x a.1 * beta ^ a.2.val = x b.1 * beta ^ b.2.val :=
            Units.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
          have hpow : beta ^ a.2.val = beta ^ b.2.val := by
            apply mul_left_cancel (a := x b.1)
            simpa only [he] using hpoint
          have hk : a.2 = b.2 := Fin.ext
            (pow_injOn_Iio_orderOf (a.2.is_lt.trans_le hJ) (b.2.is_lt.trans_le hJ) hpow)
          exact Prod.ext he hk)
      have hc : ((Finset.univ : Finset (Fin M × Fin J)).filter
          fun ik => (((x ik.1) * beta ^ ik.2.val : (ZMod p)ˣ) : ZMod p) = y).card ≤ M := by
        simpa only [Finset.card_univ, Fintype.card_fin] using hcap
      exact hc.trans_lt hM)
    (fun ik _ => (x ik.1 * beta ^ ik.2.val).isUnit.ne_zero)
    hphi W U V hW hU hUV

open scoped Pointwise Combinatorics.Additive
open RiemannGaussian.SemiprimeSeedEnergyAcquisitionObstruction
open RiemannGaussian.SemiprimeGlobalPhaseCancellation
open RiemannGaussian.SemiprimeDenseRowCarries

/-- Coprime powering is injective on a family with a common finite period. -/
theorem power_injective_on_periodic_points {K : Type*} [CommMonoid K]
    (S : Set K) {R e : ℕ} (hR : 0 < R) (hcop : e.Coprime R)
    (hperiod : ∀ x ∈ S, x ^ R = 1) : Set.InjOn (fun x : K => x ^ e) S := by
  by_cases hRone : R = 1
  · intro x hx y hy _
    simpa only [hRone, pow_one] using (hperiod x hx).trans (hperiod y hy).symm
  have hRtwo : 1 < R := by omega
  obtain ⟨k, _, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hRtwo
  have hrecover : ∀ x ∈ S, (x ^ e) ^ k = x := by
    intro x hx
    rw [←pow_mul, ←Nat.mod_add_div (e * k) R, pow_add, pow_mul,
      hperiod x hx, one_pow, mul_one, hk, pow_one]
  intro x hx y hy hxy
  have heq := congrArg (fun t : K => t ^ k) hxy
  rw [hrecover x hx, hrecover y hy] at heq
  exact heq

/-- Evaluation of a polynomial divisor of a unit-valued polynomial is a unit.
This includes cyclotomic or binomial column masks once their gate is proved. -/
theorem polynomial_divisor_eval_isUnit {R : Type*} [CommRing R]
    (P Q : R[X]) (v : R) (hdiv : P ∣ Q) (hQ : IsUnit (Q.eval v)) :
    IsUnit (P.eval v) := by
  obtain ⟨A, hA⟩ := hdiv
  rw [hA, eval_mul] at hQ
  exact isUnit_of_mul_isUnit_left hQ

/-- A prime period cannot divide a product of two positive smaller indices. -/
theorem prime_order_binomial_ne_zero {K : Type*} [Field K]
    (beta : Kˣ) (hR : (orderOf beta).Prime) {r d : ℕ}
    (hr : 0 < r) (hrR : r < orderOf beta)
    (hd : 0 < d) (hdR : d < orderOf beta) :
    (((beta : K) ^ r) ^ d - 1) ≠ 0 := by
  intro he
  have hp : beta ^ (r * d) = 1 := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, pow_mul] using
      (sub_eq_zero.mp he)
  have hdiv := (orderOf_dvd_iff_pow_eq_one).mpr hp
  rcases hR.dvd_mul.mp hdiv with h | h
  · exact Nat.not_dvd_of_pos_of_lt hr hrR h
  · exact Nat.not_dvd_of_pos_of_lt hd hdR h

/-- A signed common-point filtered grid keeps the source-energy tradeoff,
with the exact denominator degree plus the filter's root budget. -/
theorem geometric_filtered_source_energy_tradeoff {p M J : ℕ}
    (hp : p.Prime) (x : Fin M → (ZMod p)ˣ) (beta : (ZMod p)ˣ)
    (hsource : ∀ y ∈ Finset.univ.image x,
      ((Finset.univ : Finset (Fin M)).filter fun i => x i = y).card ≤ 2)
    (hJ : J ≤ orderOf beta) (hJpos : 0 < J) (hM : M < p)
    (w L : ℕ) (hcover : L ≤ w * J) (phi : ZMod p → ZMod p)
    (hphi : Set.InjOn phi
      ((Finset.univ : Finset (Fin M × Fin J)).image
        fun ik => (((x ik.1) * beta ^ ik.2.val : (ZMod p)ˣ) : ZMod p)))
    (W H K : (ZMod p)[X]) (hW : W ≠ 0) (hH : H.coeff 0 = 1)
    (hHK : (H : PowerSeries (ZMod p)) *
      (∑ ik : Fin M × Fin J, PowerSeries.C
        (W.eval (phi (((x ik.1) * beta ^ ik.2.val : (ZMod p)ˣ) : ZMod p))) *
        positiveMoments ((((x ik.1) * beta ^ ik.2.val : (ZMod p)ˣ) : ZMod p))) =
      (K : PowerSeries (ZMod p))) :
    M ^ 4 * L ≤ 16 * w * (H.natDegree + W.natDegree) ^ 2 *
      labelledEnergy Finset.univ x := by
  classical
  let : NeZero p := ⟨hp.ne_zero⟩
  let A := Finset.univ.image x
  let B := Finset.univ.image fun k : Fin J => beta ^ k.val
  have hB : B.card = J := by
    rw [Finset.card_image_of_injective]
    · exact Fintype.card_fin J
    · intro k l he
      apply Fin.ext
      exact pow_injOn_Iio_orderOf (k.is_lt.trans_le hJ) (l.is_lt.trans_le hJ) he
  have hrows : M ≤ 2 * A.card := by
    have h := card_le_fiber_bound_mul_image Finset.univ x 2 hsource
    simpa only [Finset.card_univ, Fintype.card_fin] using h
  have hdeg : (A * B).card ≤ H.natDegree + W.natDegree := by
    rw [geometric_grid_support_card_eq]
    exact geometric_grid_filtered_denominator_degree hp x beta hJ hM phi hphi
      W H K hW hH hHK
  have he := product_support_tradeoff A B (by rw [hB]; exact hJpos)
    w L (H.natDegree + W.natDegree) (labelledEnergy Finset.univ x)
    (by rw [hB]; exact hcover) hdeg (image_self_energy_le_labelled Finset.univ x)
  calc
    _ ≤ (2 * A.card) ^ 4 * L := Nat.mul_le_mul_right L (Nat.pow_le_pow_left hrows 4)
    _ = 16 * (A.card ^ 4 * L) := by ring
    _ ≤ 16 * (w * (H.natDegree + W.natDegree) ^ 2 * labelledEnergy Finset.univ x) :=
      Nat.mul_le_mul_left _ he
    _ = _ := by ring

/-- Literal original row offsets retain the all-width energy obstruction
through signed common-point filtering. Infinitude and bit cost are separate. -/
theorem literal_original_filtered_energy_tradeoff {p N m J : ℕ}
    (hp : p.Prime) (hm : m.Prime) (hN : m.Coprime N)
    (gamma beta : (ZMod p)ˣ) (horder : 8 * m ^ 2 < orderOf gamma)
    (hJ : J ≤ orderOf beta) (hJpos : 0 < J) (hM : m - 1 < p)
    (w L : ℕ) (hcover : L ≤ w * J) (phi : ZMod p → ZMod p)
    (hphi : Set.InjOn phi
      ((Finset.univ : Finset (Fin (m-1) × Fin J)).image fun ik =>
        (((progressionSeed gamma N m (ik.1.val+1)).step *
          beta ^ ik.2.val : (ZMod p)ˣ) : ZMod p)))
    (W H K : (ZMod p)[X]) (hW : W ≠ 0) (hH : H.coeff 0 = 1)
    (hHK : (H : PowerSeries (ZMod p)) *
      (∑ ik : Fin (m-1) × Fin J, PowerSeries.C
        (W.eval (phi (((progressionSeed gamma N m (ik.1.val+1)).step *
          beta ^ ik.2.val : (ZMod p)ˣ) : ZMod p))) *
        positiveMoments (((progressionSeed gamma N m (ik.1.val+1)).step *
          beta ^ ik.2.val : (ZMod p)ˣ) : ZMod p)) = (K : PowerSeries (ZMod p))) :
    (m-1) ^ 4 * L ≤ 16 * w * (H.natDegree + W.natDegree) ^ 2 *
      (nontrivialOffsetEnergy N m + 2 * (m-1) ^ 2) := by
  classical
  let x := fun i : Fin (m-1) => (progressionSeed gamma N m (i.val+1)).step
  have hsource : ∀ y ∈ Finset.univ.image x,
      ((Finset.univ : Finset (Fin (m-1))).filter fun i => x i = y).card ≤ 2 := by
    intro y _
    exact original_seed_fiber_card_le_two gamma hm hN horder y
  have he := geometric_filtered_source_energy_tradeoff hp x beta hsource
    hJ hJpos hM w L hcover phi hphi W H K hW hH hHK
  rw [labelled_original_seed_energy_eq_offset gamma hm horder] at he
  exact he.trans (Nat.mul_le_mul_left _ (offsetEnergy_le_nontrivial_add N m))

/-- The weighted centered series has the literal signed power-sum coefficients. -/
theorem weighted_positive_moments_coeff {R ι : Type*} [CommRing R]
    (I : Finset ι) (x weight : ι → R) {r : ℕ} (hr : 0 < r) :
    PowerSeries.coeff r (∑ i ∈ I, PowerSeries.C (weight i) * positiveMoments (x i)) =
      ∑ i ∈ I, weight i * (x i) ^ r := by
  simp only [map_sum, PowerSeries.coeff_C_mul, positiveMoments, PowerSeries.coeff_mk,
    ite_eq_right (Nat.ne_of_gt hr)]

/-- Finite signed moment-index shifts are common-character point filters,
with every original label retained in the exact sum. -/
theorem signed_moment_shift_identity {R ι : Type*} [CommRing R]
    (I : Finset ι) (x : ι → R) (W : R[X]) (r e : ℕ) :
    (∑ a ∈ Finset.range (W.natDegree + 1), W.coeff a *
      (∑ i ∈ I, (x i) ^ (r + e * a))) =
      ∑ i ∈ I, W.eval ((x i) ^ e) * (x i) ^ r := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [pow_add, pow_mul]
  ring

/-- Shared signed column masks separate from the genuine original seed moment. -/
theorem signed_column_moment_factor {R ι : Type*} [CommRing R]
    (I : Finset ι) (B : Finset ℕ) (x : ι → R) (beta : R) (weight : ℕ → R) (r : ℕ) :
    (∑ j ∈ I, ∑ h ∈ B, weight h * (x j * beta ^ h) ^ r) =
      (∑ j ∈ I, (x j) ^ r) * (∑ h ∈ B, weight h * (beta ^ r) ^ h) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [mul_pow, pow_right_comm beta h r]
  ring

/-- Cyclotomic column factors are units below a local prime period; changing
such a mask adds no zero to an already acquired original seed moment. -/
theorem prime_order_cyclotomic_eval_isUnit {K : Type*} [Field K] (beta : Kˣ)
    (hR : (orderOf beta).Prime) {r d : ℕ}
    (hr : 0 < r) (hrR : r < orderOf beta) (hd : 0 < d) (hdR : d < orderOf beta) :
    IsUnit ((cyclotomic d K).eval ((beta : K) ^ r)) := by
  apply polynomial_divisor_eval_isUnit (cyclotomic d K) (X ^ d - 1) ((beta : K) ^ r)
    (cyclotomic.dvd_X_pow_sub_one d K)
  simp only [eval_sub, eval_pow, eval_X, eval_one]
  exact isUnit_iff_ne_zero.mpr (prime_order_binomial_ne_zero beta hR hr hrR hd hdR)

end RiemannGaussian.SemiprimeSignedMomentAcquisitionObstruction
