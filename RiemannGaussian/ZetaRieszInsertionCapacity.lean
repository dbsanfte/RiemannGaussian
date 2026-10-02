/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszClippedInsertionFloor
import RiemannGaussian.ZetaRieszContinuumCascade
import RiemannGaussian.ZetaRieszExtremePrimeProfile

/-!
# A signed capacity audit for complete finite insertion families

Sum every insertion count before taking a real part. With independent real
weights in `[0,1]`, the outer parity sign and the inner Riesz differences
combine into a positive Bernoulli average of translated hinges. In particular,
the empty channel gives a strictly positive residual when all weights are
strictly below one. This is an exact finite coefficient inequality, not a
prime-density approximation or a bound for the native masked carrier.

The literal carrier has correlated prime inventory, allocation, masks and
phases. None is replaced by these product weights in an application here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszInsertionCapacity
open ZetaRieszContinuumCascade

/-- All insertion counts, including the original empty insertion. -/
def response {ι : Type*} (Q : Finset ι) (a x : ι → ℝ) (d : ℝ) : ℝ :=
  ∑ U ∈ Q.powerset, (-1 : ℝ)^U.card*(∏ i ∈ U,a i)*kernel U x d

/-- Exact weights of the complete finite Bernoulli family. -/
def mass {ι : Type*} [DecidableEq ι] (Q U : Finset ι) (a : ι → ℝ) : ℝ :=
  (∏ i ∈ U,a i)*(∏ i ∈ Q\U,(1-a i))

/-- Parity and finite differences combine BEFORE any norm or positive part. -/
theorem response_insert {ι : Type*} [DecidableEq ι] (Q : Finset ι)
    (a x : ι → ℝ) (d : ℝ) {i : ι} (hi : i ∉ Q) :
    response (insert i Q) a x d =
      (1-a i)*response Q a x d+a i*response Q a x (d-x i) := by
  unfold response
  rw [Finset.sum_powerset_insert hi]
  have he (U : Finset ι) (hU : U ∈ Q.powerset) :
      (-1 : ℝ)^(insert i U).card*(∏ j ∈ insert i U,a j)*kernel (insert i U) x d =
        -a i*((-1 : ℝ)^U.card*(∏ j ∈ U,a j)*kernel U x d)+
          a i*((-1 : ℝ)^U.card*(∏ j ∈ U,a j)*kernel U x (d-x i)) := by
    have hiU : i ∉ U := fun h => hi (Finset.mem_powerset.mp hU h)
    rw [Finset.card_insert_of_notMem hiU,Finset.prod_insert hiU,
      kernel_insert U x d hiU,pow_succ]
    ring
  rw [Finset.sum_congr rfl he,Finset.sum_add_distrib,← Finset.mul_sum,
    ← Finset.mul_sum]
  ring

private theorem average_insert {ι : Type*} [DecidableEq ι] (Q : Finset ι)
    (a x : ι → ℝ) (d : ℝ) {i : ι} (hi : i ∉ Q) :
    (∑ U ∈ (insert i Q).powerset,mass (insert i Q) U a*max 0 (d-∑ j ∈ U,x j)) =
      (1-a i)*(∑ U ∈ Q.powerset,mass Q U a*max 0 (d-∑ j ∈ U,x j))+
        a i*(∑ U ∈ Q.powerset,mass Q U a*max 0 (d-x i-∑ j ∈ U,x j)) := by
  rw [Finset.sum_powerset_insert hi]
  have hleft (U : Finset ι) (hU : U ∈ Q.powerset) :
      mass (insert i Q) U a=(1-a i)*mass Q U a := by
    have hiU : i ∉ U := fun h => hi (Finset.mem_powerset.mp hU h)
    have hiD : i ∉ Q\U := fun h => hi (Finset.mem_sdiff.mp h).1
    rw [mass,Finset.insert_sdiff_of_notMem Q hiU,Finset.prod_insert hiD,mass]
    ring
  have hright (U : Finset ι) (hU : U ∈ Q.powerset) :
      mass (insert i Q) (insert i U) a*max 0 (d-∑ j ∈ insert i U,x j) =
        a i*(mass Q U a*max 0 (d-x i-∑ j ∈ U,x j)) := by
    have hiU : i ∉ U := fun h => hi (Finset.mem_powerset.mp hU h)
    rw [mass,Finset.prod_insert hiU,Finset.insert_sdiff_insert,
      Finset.sdiff_insert_of_notMem hi,Finset.sum_insert hiU]
    have he : d-(x i+∑ j ∈ U,x j)=d-x i-∑ j ∈ U,x j := by ring
    rw [he,mass]
    ring
  have hleft' (U : Finset ι) (hU : U ∈ Q.powerset) :
      mass (insert i Q) U a*max 0 (d-∑ j ∈ U,x j) =
        (1-a i)*(mass Q U a*max 0 (d-∑ j ∈ U,x j)) := by
    rw [hleft U hU,mul_assoc]
  rw [Finset.sum_congr rfl hleft',Finset.sum_congr rfl hright,
    ← Finset.mul_sum,← Finset.mul_sum]

/-- The complete signed all-count response is exactly a positive-weight
hinge average. No insertion count is dropped and the empty channel remains. -/
theorem response_eq_average {ι : Type*} [DecidableEq ι]
    (Q : Finset ι) (a x : ι → ℝ) (d : ℝ) :
    response Q a x d = ∑ U ∈ Q.powerset,mass Q U a*max 0 (d-∑ i ∈ U,x i) := by
  induction Q using Finset.induction_on generalizing d with
  | empty => simp [response,kernel,mass]
  | @insert i Q hi ih =>
    rw [response_insert Q a x d hi,average_insert Q a x d hi,ih,ih]

/-- Joining independent insertion counts cannot reverse the original
hinge sign. This does not assert independence in the literal carrier. -/
theorem response_nonneg {ι : Type*} [DecidableEq ι]
    (Q : Finset ι) (a x : ι → ℝ) (d : ℝ)
    (ha : ∀ i∈Q,0 ≤ a i ∧ a i ≤ 1) : 0 ≤ response Q a x d := by
  rw [response_eq_average]
  apply Finset.sum_nonneg
  intro U hU
  apply mul_nonneg _ (le_max_left _ _)
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun i hi => (ha i (Finset.mem_powerset.mp hU hi)).1)
  · exact Finset.prod_nonneg (fun i hi => sub_nonneg.mpr (ha i (Finset.mem_sdiff.mp hi).1).2)

/-- The joined response is bounded by the ORIGINAL hinge; it is not a
sum of absolute count allowances. -/
theorem response_le_hinge {ι : Type*} [DecidableEq ι]
    (Q : Finset ι) (a x : ι → ℝ) (d : ℝ)
    (ha : ∀ i∈Q,0 ≤ a i ∧ a i ≤ 1) (hx : ∀ i∈Q,0 ≤ x i) :
    response Q a x d ≤ max 0 d := by
  induction Q using Finset.induction_on generalizing d with
  | empty => simp [response,kernel]
  | @insert i Q hi ih =>
    have haQ := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hxQ := fun j hj => hx j (Finset.mem_insert_of_mem hj)
    obtain ⟨hai,hai1⟩ := ha i (Finset.mem_insert_self _ _)
    rw [response_insert Q a x d hi]
    have hb := max_le_max_left 0 (sub_le_self d (hx i (Finset.mem_insert_self _ _)))
    have h1 := mul_le_mul_of_nonneg_left (ih d haQ hxQ) (sub_nonneg.mpr hai1)
    have h2 := mul_le_mul_of_nonneg_left ((ih (d-x i) haQ hxQ).trans hb) hai
    nlinarith

/-- The mean inserted log mass is a NECESSARY capacity test. A small
weighted inventory cannot cancel a larger hinge even with all counts joined. -/
theorem response_ge_mean_deficit {ι : Type*} [DecidableEq ι]
    (Q : Finset ι) (a x : ι → ℝ) (d : ℝ)
    (ha : ∀ i∈Q,0 ≤ a i ∧ a i ≤ 1) :
    max 0 (d-∑ i∈Q,a i*x i) ≤ response Q a x d := by
  have hl : d-∑ i∈Q,a i*x i ≤ response Q a x d := by
    induction Q using Finset.induction_on generalizing d with
    | empty => simp only [response,Finset.powerset_empty,Finset.sum_singleton,
        Finset.card_empty,pow_zero,Finset.prod_empty,kernel,Finset.sum_empty,
        mul_one,one_mul,sub_zero]; exact le_max_right _ _
    | @insert i Q hi ih =>
      have haQ := fun j hj => ha j (Finset.mem_insert_of_mem hj)
      obtain ⟨hai,hai1⟩ := ha i (Finset.mem_insert_self _ _)
      have h1 := mul_le_mul_of_nonneg_left (ih d haQ) (sub_nonneg.mpr hai1)
      have h2 := mul_le_mul_of_nonneg_left (ih (d-x i) haQ) hai
      rw [response_insert Q a x d hi,Finset.sum_insert hi]
      nlinarith
  exact max_le (response_nonneg Q a x d ha) hl

/-- Even a large mean does not remove the empty-cofactor residual. -/
theorem response_ge_empty {ι : Type*} [DecidableEq ι]
    (Q : Finset ι) (a x : ι → ℝ) (d : ℝ)
    (ha : ∀ i∈Q,0 ≤ a i ∧ a i ≤ 1) :
    (∏ i∈Q,(1-a i))*max 0 d ≤ response Q a x d := by
  induction Q using Finset.induction_on generalizing d with
  | empty => simp [response,kernel]
  | @insert i Q hi ih =>
    have haQ := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    obtain ⟨hai,hai1⟩ := ha i (Finset.mem_insert_self _ _)
    have h1 := mul_le_mul_of_nonneg_left (ih d haQ) (sub_nonneg.mpr hai1)
    have h2 := mul_nonneg hai (response_nonneg Q a x (d-x i) haQ)
    rw [response_insert Q a x d hi,Finset.prod_insert hi]
    nlinarith

/-- Finite independent weights below one leave a strictly positive
cofactor response. This refutes exact local annihilation in that model,
not the native floor or cancellation using correlated arithmetic weights. -/
theorem response_pos {ι : Type*} [DecidableEq ι]
    (Q : Finset ι) (a x : ι → ℝ) {d : ℝ} (hd : 0 < d)
    (ha : ∀ i∈Q,0 ≤ a i ∧ a i < 1) : 0 < response Q a x d := by
  have hp : 0 < ∏ i∈Q,(1-a i) := Finset.prod_pos (fun i hi => sub_pos.mpr (ha i hi).2)
  have h := response_ge_empty Q a x d (fun i hi => ⟨(ha i hi).1,(ha i hi).2.le⟩)
  rw [max_eq_right hd.le] at h
  exact (mul_pos hp hd).trans_le h

/-- The audit applies to literal prime logarithms with exact reciprocal
prime weights. It is an arithmetic COEFFICIENT sum, not the masked prime-
owner inventory, factorial carrier or its complex phase. -/
theorem reciprocal_prime_response_pos (Q : Finset ℕ) (hQ : ∀ p∈Q,p.Prime)
    {d : ℝ} (hd : 0 < d) :
    0 < response Q (fun p => (p : ℝ)⁻¹) (fun p => log p) d := by
  apply response_pos Q _ _ hd
  intro p hp
  have hpR : (1 : ℝ) < p := by exact_mod_cast (hQ p hp).one_lt
  exact ⟨inv_nonneg.mpr (by linarith),by rw [inv_lt_one₀ (by linarith : (0 : ℝ) < p)]; exact hpR⟩

/-- The finite response is the EXACT arithmetic cofactor sum when the
old base primes are beyond the hinge. Squarefreeness stays explicit. -/
theorem arithmetic_response_eq (Q : Finset ℕ) (a : ℕ → ℝ)
    (hQ : ∀ p∈Q,p.Prime) (b : ℕ) (d : ℝ)
    (hfull : ∀ U∈Q.powerset,Squarefree (b*∏ p∈U,p))
    (hlarge : ∀ p∈b.primeFactors,d ≤ log p) :
    (∑ U∈Q.powerset,(-1 : ℝ)^U.card*(∏ p∈U,a p)*
      VaughanLogAverage.riesz d (b*∏ p∈U,p)) = response Q a (fun p => log p) d := by
  unfold response
  apply Finset.sum_congr rfl
  intro U hU
  rw [ZetaRieszExtremePrimeProfile.riesz_mul_eq_of_extreme_rough (hfull U hU) hlarge,
    kernel_eq_riesz_prime_product U (fun p hp => hQ p (Finset.mem_powerset.mp hU hp))]

/-- Actual reciprocal-prime coefficients leave at least the empty-channel
mass after ALL selected counts are joined. No prime-owner measure or
complex carrier is approximated by these independent weights. -/
theorem arithmetic_response_lower (Q : Finset ℕ) (hQ : ∀ p∈Q,p.Prime)
    (b : ℕ) {d : ℝ} (hd : 0 ≤ d)
    (hfull : ∀ U∈Q.powerset,Squarefree (b*∏ p∈U,p))
    (hlarge : ∀ p∈b.primeFactors,d ≤ log p) :
    d*(∏ p∈Q,(1-(p : ℝ)⁻¹)) ≤
      ∑ U∈Q.powerset,(-1 : ℝ)^U.card*(∏ p∈U,(p : ℝ)⁻¹)*
        VaughanLogAverage.riesz d (b*∏ p∈U,p) := by
  rw [arithmetic_response_eq Q _ hQ b d hfull hlarge]
  have ha p (hp : p∈Q) : 0 ≤ (p : ℝ)⁻¹ ∧ (p : ℝ)⁻¹ ≤ 1 := by
    have hr : (1 : ℝ) ≤ p := by exact_mod_cast (hQ p hp).one_lt.le
    exact ⟨inv_nonneg.mpr (by linarith),inv_le_one₀ (by linarith) |>.mpr hr⟩
  simpa only [max_eq_right hd,mul_comm] using response_ge_empty Q _ _ d ha

end RiemannGaussian.ZetaRieszInsertionCapacity
