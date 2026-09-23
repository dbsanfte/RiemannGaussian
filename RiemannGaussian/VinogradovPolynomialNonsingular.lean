/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovPolynomialConditioning

/-!
# A numerical conditioning bound for the actual nonsingular mixed count

The original positive interval and full tail equations remain literal.
The polynomial-system congruence count pays the nonsingular mixed count
by the residue mixed integral, with the explicit factorial and triangular
prime-power coefficient. This is the last stage of classical `K`-to-`L`
conditioning, and feeds the checked quantitative differencing bound.
-/

namespace RiemannGaussian.VinogradovPolynomialNonsingular
noncomputable section
open scoped BigOperators Classical
open Polynomial MeasureTheory UnitAddTorus VinogradovMeanValue VinogradovShiftedMoment
open VinogradovMomentPartition VinogradovPartitionEnergy VinogradovPolynomialSystems
open VinogradovPolynomialDifferencing VinogradovPolynomialConditioning
open VinogradovMixedMoments VinogradovMixedDifferencing VinogradovDifferenceEnergy
open VinogradovColourProducts

/-- Actual positive interval tuples with distinct residues modulo `p`. -/
abbrev Window (p m P : ℕ) :=
  {x : Fin m → Fin P // Function.Injective (fun j => (((x j).val + 1 : ℕ) : ZMod p))}

/-- Use one finite enumeration throughout the original block identities. -/
local instance windowFintype (p m P : ℕ) : Fintype (Window p m P) := Fintype.ofFinite _

/-- The full integer polynomial frequency of a nonsingular block. -/
def windowFrequency {p m P : ℕ} (d : ℕ) (F : Fin m → ℤ[X]) (x : Window p m P) :
    (Fin d ⊕ Fin m) → ℤ := blockFrequency d F (fun j => (x.val j).val + 1)

/-- Both entire tuple families enter the original configuration frequency. -/
def configurationFrequency {κ : Type*} {p m P : ℕ} (d s : ℕ) (F : Fin m → ℤ[X])
    (u : κ → (Fin d ⊕ Fin m) → ℤ) (z : Window p m P × (Fin s → κ)) :
    (Fin d ⊕ Fin m) → ℤ := windowFrequency d F z.1 + tupleFrequency s u z.2

/-- The literal count of all original equations, with both block
tuples nonsingular and the full original tail retained. -/
def nonsingularCount {κ : Type*} [Fintype κ] (p m d P s : ℕ)
    (F : Fin m → ℤ[X]) (u : κ → (Fin d ⊕ Fin m) → ℤ) : ℕ :=
  differenceCount (configurationFrequency (p := p) (P := P) d s F u) 0

/-- The original normalized Haar measure. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The circle measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The literal mixed integral of the nonsingular block and original tail. -/
def nonsingularMoment {κ : Type*} [Fintype κ] (p m d P s : ℕ)
    (F : Fin m → ℤ[X]) (u : κ → (Fin d ⊕ Fin m) → ℤ) : ℝ :=
  ∫ theta : UnitAddTorus (Fin d ⊕ Fin m),
    ‖polynomial (windowFrequency (p := p) (P := P) d F) (fun _ => 1) theta‖ ^ 2 *
      ‖polynomial u (fun _ => 1) theta‖ ^ (2 * s)

/-- Factor the complete configuration polynomial before taking its norm. -/
theorem configuration_polynomial {κ : Type*} [Fintype κ] {p m P : ℕ}
    (d s : ℕ) (F : Fin m → ℤ[X]) (u : κ → (Fin d ⊕ Fin m) → ℤ)
    (theta : UnitAddTorus (Fin d ⊕ Fin m)) :
    polynomial (configurationFrequency (p := p) (P := P) d s F u) (fun _ => 1) theta =
      polynomial (windowFrequency (p := p) (P := P) d F) (fun _ => 1) theta *
        polynomial u (fun _ => 1) theta ^ s := by
  have ht := VinogradovMixedMoments.tuple_polynomial s u (fun _ => 1) theta
  rw [show tupleWeight s (fun _ : κ => (1 : ℂ)) = (fun _ => 1) by
    funext x
    simp only [tupleWeight, Finset.prod_const_one]] at ht
  unfold configurationFrequency
  simpa only [one_mul, ht] using
    VinogradovProductEnergy.polynomial_prod (windowFrequency (p := p) (P := P) d F)
      (tupleFrequency s u) (fun _ => 1) (fun _ => 1) theta

/-- Orthogonality identifies this integral with the actual integer
count, including every coordinate equation. -/
theorem nonsingularMoment_eq_count {κ : Type*} [Fintype κ]
    (p m d P s : ℕ) (F : Fin m → ℤ[X]) (u : κ → (Fin d ⊕ Fin m) → ℤ) :
    nonsingularMoment p m d P s F u = (nonsingularCount p m d P s F u : ℝ) := by
  let V := configurationFrequency (p := p) (P := P) d s F u
  have he := weightedShift_one V 0
  rw [weightedShift_zero] at he
  have hr := congrArg Complex.re he
  have henergy : (∫ theta : UnitAddTorus (Fin d ⊕ Fin m),
      ‖polynomial V (fun _ => 1) theta‖ ^ 2) = (differenceCount V 0 : ℝ) := by
    simpa only [polynomial, one_mul, Complex.ofReal_re, Complex.natCast_re] using hr
  change _ = (differenceCount V 0 : ℝ)
  rw [← henergy]
  apply integral_congr_ae
  filter_upwards [] with theta
  simp only [V, configuration_polynomial, norm_mul, norm_pow, mul_pow, ← pow_mul,
    Nat.mul_comm s 2]

/-- The complete residue label of a positive original interval entry. -/
def positiveLabel {q : ℕ} (hq : 0 < q) (P : ℕ) (x : Fin P) : Fin q :=
  ⟨(x.val + 1) % q, Nat.mod_lt _ hq⟩

/-- Indexing positive residues instead of zero-based residues only
renames the classes of the original residue energy. -/
theorem positive_colourEnergy {a : Type*} [Fintype a] (P q : ℕ) (hq : 0 < q)
    (v : ℕ → a → ℤ) (theta : UnitAddTorus a) :
    colourEnergy (positiveLabel hq P) (fun x => mFourier (v (x.val + 1)) theta) =
      residueEnergy P q hq v theta := by
  rw [residueEnergy, colourEnergy_eq_pairs, colourEnergy_eq_pairs]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hiff : (i.val + 1) % q = (j.val + 1) % q ↔ i.val % q = j.val % q :=
    (Nat.ModEq.rfl : 1 ≡ 1 [MOD q]).add_iff_right
  simp only [positiveLabel, Fin.mk.injEq, hiff]

/-- An admissible fine colour already enforces the original
nonsingularity condition, so its complete block fibre is unchanged. -/
theorem window_fibre_polynomial {p m d P r : ℕ} (hp : 0 < p) (hr : 1 ≤ r)
    (F : Fin m → ℤ[X]) (c : GoodResidue p m r)
    (theta : UnitAddTorus (Fin d ⊕ Fin m)) :
    polynomial (windowFrequency (p := p) (P := P) d F)
      (targetWeight (fun x => residueTuple hp m r (fun j => (x.val j).val + 1))
        (fun _ => 1) c.val) theta =
      polynomial (tupleFrequency m (fun x : Fin P => fullFrequency d F (x.val + 1)))
        (targetWeight (tupleLabel m (positiveLabel (pow_pos hp r) P)) (fun _ => 1) c.val) theta := by
  apply polynomial_subtype_eq
    (fun x : Fin m → Fin P => Function.Injective (fun j => (((x j).val + 1 : ℕ) : ZMod p)))
    (tupleFrequency m (fun x : Fin P => fullFrequency d F (x.val + 1)))
    (targetWeight (tupleLabel m (positiveLabel (pow_pos hp r) P)) (fun _ => 1) c.val) ?_ theta
  intro x hx
  unfold targetWeight
  apply if_neg
  intro he
  apply hx
  intro i j hij
  apply c.property
  have hi := congrFun he i
  have hj := congrFun he j
  change ((c.val i).val : ZMod p) = ((c.val j).val : ZMod p)
  rw [← hi, ← hj]
  simpa only [tupleLabel, positiveLabel, cast_mod_power_prime hr] using hij

/-- The complete sum of admissible fine-fibre energies is bounded by
the exact original residue energy power, with no endpoint enlargement. -/
theorem fine_energy_le {p m d P r : ℕ} (hp : 0 < p) (hr : 1 ≤ r)
    (F : Fin m → ℤ[X]) (theta : UnitAddTorus (Fin d ⊕ Fin m)) :
    (∑ c : GoodResidue p m r, ‖polynomial (windowFrequency (p := p) (P := P) d F)
      (targetWeight (fun x => residueTuple hp m r (fun j => (x.val j).val + 1))
        (fun _ => 1) c.val) theta‖ ^ 2) ≤
      residueEnergy P (p ^ r) (pow_pos hp r) (fullFrequency d F) theta ^ m := by
  let v := fun x : Fin P => fullFrequency d F (x.val + 1)
  let label := positiveLabel (pow_pos hp r) P
  let E (c : Fin m → Fin (p ^ r)) :=
    ‖polynomial (tupleFrequency m v) (targetWeight (tupleLabel m label) (fun _ => 1) c) theta‖ ^ 2
  calc
    _ = ∑ c : GoodResidue p m r, E c.val := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [window_fibre_polynomial hp hr]
    _ ≤ ∑ c : Fin m → Fin (p ^ r), E c := by
      rw [← Finset.sum_subtype
        (Finset.univ.filter (fun c : Fin m → Fin (p ^ r) =>
          Function.Injective (fun j => ((c j).val : ZMod p)))) (by simp) E]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => sq_nonneg _)
    _ = _ := by
      rw [show (∑ c : Fin m → Fin (p ^ r), E c) =
          colourEnergy label (fun x => mFourier (v x) theta) ^ m from tuple_colour_energy m v label theta]
      rw [positive_colourEnergy]

/-- A fixed block residue leaves the entire original tail polynomial
as a factor of the configuration polynomial. -/
theorem fine_configuration_polynomial {κ : Type*} [Fintype κ] {p m P r : ℕ}
    (hp : 0 < p) (d s : ℕ) (F : Fin m → ℤ[X]) (u : κ → (Fin d ⊕ Fin m) → ℤ)
    (c : GoodResidue p m r) (theta : UnitAddTorus (Fin d ⊕ Fin m)) :
    polynomial (configurationFrequency (p := p) (P := P) d s F u)
      (targetWeight (fun z => residueTuple hp m r (fun j => (z.1.val j).val + 1))
        (fun _ => 1) c.val) theta =
      polynomial (windowFrequency (p := p) (P := P) d F)
        (targetWeight (fun x => residueTuple hp m r (fun j => (x.val j).val + 1))
          (fun _ => 1) c.val) theta * polynomial u (fun _ => 1) theta ^ s := by
  let wb := targetWeight (fun x : Window p m P =>
    residueTuple hp m r (fun j => (x.val j).val + 1)) (fun _ => (1 : ℂ)) c.val
  have hw : targetWeight (fun z : Window p m P × (Fin s → κ) =>
      residueTuple hp m r (fun j => (z.1.val j).val + 1)) (fun _ => (1 : ℂ)) c.val =
        fun z => wb z.1 * (1 : ℂ) := by
    funext z
    simp only [wb, targetWeight, mul_one]
    split_ifs <;> rfl
  have ht := VinogradovMixedMoments.tuple_polynomial s u (fun _ => 1) theta
  rw [show tupleWeight s (fun _ : κ => (1 : ℂ)) = (fun _ => 1) by
    funext x
    simp only [tupleWeight, Finset.prod_const_one]] at ht
  rw [hw]
  change polynomial (fun z : Window p m P × (Fin s → κ) =>
    windowFrequency d F z.1 + tupleFrequency s u z.2) (fun z => wb z.1 * 1) theta = _
  rw [VinogradovProductEnergy.polynomial_prod (windowFrequency (p := p) (P := P) d F)
    (tupleFrequency s u) wb (fun _ => 1) theta, ht]

/-- The original nonsingular mixed integral pays only the proved
factorial and triangular prime-power coefficient before entering the
literal residue mixed moment. The tail divisibility is displayed. -/
theorem nonsingularMoment_le {κ : Type*} [Fintype κ]
    {p m d r T e : ℕ} [Fact p.Prime]
    (hpdeg : d + m < p) (hp2 : 2 < p) (hpT : ¬p ∣ T) (hr1 : 1 ≤ r) (hr : r ≤ d + m)
    {F : Fin m → ℤ[X]} (hF : HasType F d T e) (P s : ℕ)
    (u : κ → (Fin d ⊕ Fin m) → ℤ)
    (hu : ∀ x i, (p : ℤ) ^ min (d + i.val + 1) r ∣ u x (Sum.inr i)) :
    nonsingularMoment p m d P s F u ≤
      ((p ^ ((r - d) * (r - d - 1) / 2) * m.factorial : ℕ) : ℝ) *
        residueMixedMoment m s P (p ^ r) (pow_pos (Fact.out : p.Prime).pos r)
          (fullFrequency d F) u := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let xp (z : Window p m P × (Fin s → κ)) := fun j => (z.1.val j).val + 1
  let tail (z : Window p m P × (Fin s → κ)) := tupleFrequency s u z.2
  have ht (z : Window p m P × (Fin s → κ)) (i : Fin m) :
      (p : ℤ) ^ min (d + i.val + 1) r ∣ tail z (Sum.inr i) := by
    simp only [tail, tupleFrequency, Finset.sum_apply]
    exact Finset.dvd_sum (fun j hj => hu (z.2 j) i)
  have he := configuration_integral_le hpdeg hp2 hpT hr1 hr hF xp tail (fun _ => 1)
    (fun z => z.1.property) ht
  change (∫ theta : UnitAddTorus (Fin d ⊕ Fin m),
      ‖polynomial (configurationFrequency (p := p) (P := P) d s F u) (fun _ => 1) theta‖ ^ 2) ≤
      ((p ^ ((r - d) * (r - d - 1) / 2) * m.factorial : ℕ) : ℝ) *
        ∑ c : GoodResidue p m r, ∫ theta : UnitAddTorus (Fin d ⊕ Fin m),
          ‖polynomial (configurationFrequency (p := p) (P := P) d s F u)
            (targetWeight (fun z => residueTuple hp m r (fun j => (z.1.val j).val + 1))
              (fun _ => 1) c.val) theta‖ ^ 2 at he
  simp only [configuration_polynomial, fine_configuration_polynomial hp,
    norm_mul, norm_pow, mul_pow, ← pow_mul, Nat.mul_comm s 2] at he
  let w (theta : UnitAddTorus (Fin d ⊕ Fin m)) := ‖polynomial u (fun _ => 1) theta‖ ^ (2 * s)
  let wb (c : GoodResidue p m r) := targetWeight (fun x : Window p m P =>
    residueTuple hp m r (fun j => (x.val j).val + 1)) (fun _ => (1 : ℂ)) c.val
  have hw : Continuous w := (continuous_polynomial u (fun _ => 1)).norm.pow _
  have hi (c : GoodResidue p m r) : Integrable (fun theta : UnitAddTorus (Fin d ⊕ Fin m) =>
      ‖polynomial (windowFrequency (p := p) (P := P) d F) (wb c) theta‖ ^ 2 * w theta) :=
    (((continuous_polynomial _ _).norm.pow 2).mul hw).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply he.trans
  apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  calc
    _ = ∫ theta : UnitAddTorus (Fin d ⊕ Fin m),
        ∑ c : GoodResidue p m r,
          ‖polynomial (windowFrequency (p := p) (P := P) d F) (wb c) theta‖ ^ 2 * w theta :=
      (integral_finsetSum _ (fun c _ => hi c)).symm
    _ ≤ _ := by
      apply integral_mono (integrable_finsetSum _ (fun c _ => hi c))
        (((continuous_residueEnergy P (p ^ r) (pow_pos hp r) (fullFrequency d F)).pow m).mul hw
          |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      intro theta
      dsimp only [Pi.mul_apply, Pi.pow_apply]
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (fine_energy_le hp hr1 F theta) (by dsimp [w]; positivity)

/-- The same explicit bound on the literal integer configuration count. -/
theorem nonsingularCount_le {κ : Type*} [Fintype κ]
    {p m d r T e : ℕ} [Fact p.Prime]
    (hpdeg : d + m < p) (hp2 : 2 < p) (hpT : ¬p ∣ T) (hr1 : 1 ≤ r) (hr : r ≤ d + m)
    {F : Fin m → ℤ[X]} (hF : HasType F d T e) (P s : ℕ)
    (u : κ → (Fin d ⊕ Fin m) → ℤ)
    (hu : ∀ x i, (p : ℤ) ^ min (d + i.val + 1) r ∣ u x (Sum.inr i)) :
    (nonsingularCount p m d P s F u : ℝ) ≤
      ((p ^ ((r - d) * (r - d - 1) / 2) * m.factorial : ℕ) : ℝ) *
        residueMixedMoment m s P (p ^ r) (pow_pos (Fact.out : p.Prime).pos r)
          (fullFrequency d F) u := by
  rw [← nonsingularMoment_eq_count]
  exact nonsingularMoment_le hpdeg hp2 hpT hr1 hr hF P s u hu

/-- The literal dilated monomial tail, including every low-degree row. -/
def monomialTail (m d p q Q : ℕ) (x : Fin Q) : (Fin d ⊕ Fin m) → ℤ :=
  Sum.elim (fun i => (((p * q : ℕ) : ℤ) * (x.val + 1)) ^ (i.val + 1))
    (fun i => (((p * q : ℕ) : ℤ) * (x.val + 1)) ^ (d + i.val + 1))

/-- Every required monomial-tail divisibility is proved from its
literal prime dilation, rather than supplied as a hypothesis. -/
theorem monomialTail_dvd (m d p q Q r : ℕ) (x : Fin Q) (i : Fin m) :
    (p : ℤ) ^ min (d + i.val + 1) r ∣ monomialTail m d p q Q x (Sum.inr i) := by
  simp only [monomialTail, Sum.elim_inr, Nat.cast_mul, mul_assoc, mul_pow]
  exact dvd_mul_of_dvd_left (pow_dvd_pow (p : ℤ) (Nat.min_le_left _ _)) _

/-- A numerical conditioning inequality for the actual positive
polynomial and dilated monomial system. No analytic or divisibility
estimate remains as a premise. The endpoint `P` is unchanged. -/
theorem prime_dilated_count_le {p m d r T e : ℕ} [Fact p.Prime]
    (hpdeg : d + m < p) (hp2 : 2 < p) (hpT : ¬p ∣ T) (hr1 : 1 ≤ r) (hr : r ≤ d + m)
    {F : Fin m → ℤ[X]} (hF : HasType F d T e) (P Q q s : ℕ) :
    (nonsingularCount p m d P s F (monomialTail m d p q Q) : ℝ) ≤
      ((p ^ ((r - d) * (r - d - 1) / 2) * m.factorial : ℕ) : ℝ) *
        residueMixedMoment m s P (p ^ r) (pow_pos (Fact.out : p.Prime).pos r)
          (fullFrequency d F) (monomialTail m d p q Q) :=
  nonsingularCount_le hpdeg hp2 hpT hr1 hr hF P s _ (monomialTail_dvd m d p q Q r)

end
end RiemannGaussian.VinogradovPolynomialNonsingular
