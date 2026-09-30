/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszUnshiftedCofactor

/-!
# The unshifted ordered character is a paid composite cofactor sum

The least-prime ordering, finite prime support, full phase and factorial
rectangle are exact. The singleton cofactor is zero at the actual orders.
-/

namespace RiemannGaussian.ZetaRieszUnshiftedCharacter
noncomputable section
open scoped BigOperators Classical
open Complex Filter MeasureTheory Set Topology
open ZetaRieszMarkedEuler ZetaRieszMarkedEulerError ZetaRieszMarkedSeparation
open ZetaRieszSkewAllocation ZetaRieszUnshiftedCofactor
open ZetaRieszMarkedCompletion

/-- Coordinates consisting of the least prime and its larger prime support. -/
abbrev Index := Σ _r : ℕ, Finset ℕ

/-- A least prime and a nonempty set of larger cofactor primes. -/
def indices (A : Finset ℕ) : Finset Index :=
  A.sigma (fun r => ((tailPrimes A r).powerset).filter Finset.Nonempty)

/-- The arithmetic label reconstructed from the distinct prime support. -/
def label (a : Index) : ℕ := ∏ p ∈ insert a.1 a.2, p

/-- Exactly the composite squarefree cofactor labels on this finite support. -/
def labels (A : Finset ℕ) : Finset ℕ := (indices A).image label

theorem index_data {A : Finset ℕ} {a : Index} (ha : a ∈ indices A) :
    a.1 ∈ A ∧ a.2 ⊆ tailPrimes A a.1 ∧ a.2.Nonempty := by
  obtain ⟨hr,hU⟩ := Finset.mem_sigma.mp ha
  exact ⟨hr,Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1,
    (Finset.mem_filter.mp hU).2⟩

theorem label_data {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) {a : Index}
    (ha : a ∈ indices A) :
    Squarefree (label a) ∧ 1 < label a ∧ ¬(label a).Prime ∧
      (label a).primeFactors = insert a.1 a.2 ∧ (label a).minFac = a.1 := by
  obtain ⟨hr,hU,hUn⟩ := index_data ha
  have hrU : a.1 ∉ a.2 := by
    intro hh
    exact (Finset.mem_filter.mp (hU hh)).2.false
  have hp (p : ℕ) (hp : p ∈ insert a.1 a.2) : p.Prime := by
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hA _ hr
    · exact hA _ (Finset.mem_filter.mp (hU hp)).1
  have hs := squarefree_prime_product (insert a.1 a.2) hp
  have hf : (label a).primeFactors = insert a.1 a.2 := Nat.primeFactors_prod hp
  have hc : 2 ≤ (insert a.1 a.2).card := by
    rw [Finset.card_insert_of_notMem hrU]
    have := Finset.card_pos.mpr hUn
    omega
  have h1 : 1 < label a := by
    have hz : label a ≠ 0 := hs.ne_zero
    have hn : label a ≠ 1 := by
      intro he
      rw [he,Nat.primeFactors_one] at hf
      have := congrArg Finset.card hf
      simp only [Finset.card_empty] at this
      omega
    omega
  refine ⟨hs,h1,?_,hf,?_⟩
  · intro hprime
    have := congrArg Finset.card hf
    rw [hprime.primeFactors,Finset.card_singleton] at this
    omega
  · have hrmem : a.1 ∈ (label a).primeFactors := by rw [hf]; simp
    apply le_antisymm (Nat.minFac_le_of_dvd (hA _ hr).two_le
      (Nat.dvd_of_mem_primeFactors hrmem))
    have hm : (label a).minFac ∈ (label a).primeFactors :=
      (Nat.minFac_prime h1.ne').mem_primeFactors (Nat.minFac_dvd _) hs.ne_zero
    rw [hf] at hm
    rcases Finset.mem_insert.mp hm with he | hm
    · exact he.ge
    · exact (Finset.mem_filter.mp (hU hm)).2.le

theorem labels_data {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime)
    {a : ℕ} (ha : a ∈ labels A) : Squarefree a ∧ 1 < a ∧ ¬a.Prime := by
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
  have hd := label_data hA hb
  exact ⟨hd.1,hd.2.1,hd.2.2.1⟩

theorem label_injective {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) :
    Set.InjOn label (indices A) := by
  intro a ha b hb hab
  have da := label_data hA ha
  have db := label_data hA hb
  have hr : a.1 = b.1 := by rw [← da.2.2.2.2,hab,db.2.2.2.2]
  have hUa : a.1 ∉ a.2 := by
    intro hh; exact (Finset.mem_filter.mp ((index_data ha).2.1 hh)).2.false
  have hUb : b.1 ∉ b.2 := by
    intro hh; exact (Finset.mem_filter.mp ((index_data hb).2.1 hh)).2.false
  have hU : a.2 = b.2 := by
    have he : insert a.1 a.2 = insert b.1 b.2 := by
      rw [← da.2.2.2.1,hab,db.2.2.2.1]
    have hh := congrArg (fun S : Finset ℕ => S.erase a.1) he
    simpa only [hr,Finset.erase_insert hUb,Finset.erase_insert (hr ▸ hUa)] using hh
  cases a; cases b
  simp_all

/-- No completed prime leg occurs in this finite character cofactor. -/
def characterCofactor (A : Finset ℕ) (N j : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  ∑ h ∈ rectangleOrders N j, ∑ r ∈ A, PowerSeries.coeff h (leg s xi r)*
    PowerSeries.coeff (N+1-j-h) (∏ p ∈ tailPrimes A r, (1+leg s xi p))

/-- The ordinary-prime cofactor correction is identically zero. Its
empty middle product cannot fill the actual complementary order. -/
theorem singleton_cofactor_zero (N j r : ℕ) (s : ℂ) (xi : ℝ) :
    (∑ h ∈ rectangleOrders N j, PowerSeries.coeff h (leg s xi r)*
      PowerSeries.coeff (N+1-j-h) (1 : PowerSeries ℂ)) = 0 := by
  apply Finset.sum_eq_zero
  intro h hh
  have hb := (Finset.mem_filter.mp hh).2
  have hz : N+1-j-h ≠ 0 := by omega
  simp [PowerSeries.coeff_one,hz]

theorem characterCofactor_eq_indices (A : Finset ℕ) (N j : ℕ) (s : ℂ) (xi : ℝ) :
    characterCofactor A N j s xi = ∑ a ∈ indices A,
      ∑ h ∈ rectangleOrders N j, PowerSeries.coeff h (leg s xi a.1)*
        PowerSeries.coeff (N+1-j-h) (∏ p ∈ a.2, leg s xi p) := by
  unfold characterCofactor
  rw [Finset.sum_comm,indices,Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro r _hr
  simp_rw [Finset.prod_one_add,map_sum,Finset.mul_sum]
  rw [Finset.sum_comm]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro U hU hnot
  have he : U = ∅ := by
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hU,Finset.nonempty_iff_ne_empty.mpr hne⟩)
  simp only [he,Finset.prod_empty]
  exact singleton_cofactor_zero N j r s xi

/-- An exact arithmetic identity, before Fourier integration or norms. -/
theorem characterCofactor_eq_labels (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (N j : ℕ) (s : ℂ) (xi : ℝ) :
    characterCofactor A N j s xi = ∑ a ∈ labels A,
      ZetaRieszPrimeFourier.primeProduct a xi*allocationKernel N j a s := by
  rw [characterCofactor_eq_indices,labels,Finset.sum_image (label_injective hA)]
  apply Finset.sum_congr rfl
  intro a ha
  have hd := label_data hA ha
  rw [selected_cofactor_identity hd.2.1,hd.2.2.2.1,hd.2.2.2.2]
  have hrU : a.1 ∉ a.2 := by
    intro hh; exact (Finset.mem_filter.mp ((index_data ha).2.1 hh)).2.false
  rw [Finset.erase_insert hrU]

/-- The paired finite character keeps both Fourier signs. -/
def characterPair (A : Finset ℕ) (N j : ℕ) (s : ℂ) (L xi : ℝ) : ℂ :=
  Complex.exp (Complex.I*xi*L)*characterCofactor A N j s xi+
    Complex.exp (-(Complex.I*xi*L))*characterCofactor A N j s (-xi)

theorem characterPair_eq (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (N j : ℕ) (s : ℂ) (L xi : ℝ) :
    characterPair A N j s L xi = cofactorPair (labels A) N j s L xi := by
  simp only [characterPair,characterCofactor_eq_labels A hA,Finset.mul_sum,
    ← Finset.sum_add_distrib,cofactorPair,ZetaRieszPrimeFourier.primePair]
  apply Finset.sum_congr rfl
  intro a _ha
  push_cast
  ring

theorem characterPair_integrable (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (N j : ℕ) (s : ℂ) (L : ℝ) :
    IntegrableOn (fun xi : ℝ => characterPair A N j s L xi/(xi : ℂ)^2) (Ioi 0) := by
  simp_rw [characterPair_eq A hA,cofactorPair,Finset.sum_div,mul_div_assoc]
  apply integrable_finsetSum
  intro a ha
  have hd := labels_data hA ha
  exact (ZetaRieszPrimeFourier.integrable_primePair_div_sq hd.1 (by omega) L).const_mul _

/-- Exact integration identifies the finite ordered character with the
saturated composite response already bounded geometrically. -/
theorem characterPair_integral (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (N j : ℕ) (s : ℂ) (L : ℝ) :
    -(1 : ℂ)/(2*Real.pi)*
      (∫ xi : ℝ in Ioi 0, characterPair A N j s L xi/(xi : ℂ)^2) =
        orderResponse (labels A) N j L s := by
  simp_rw [characterPair_eq A hA]
  simpa only [neg_div] using
    (orderResponse_eq_integral _ (fun a ha => labels_data hA ha) N j s L).symm

end
end RiemannGaussian.ZetaRieszUnshiftedCharacter
