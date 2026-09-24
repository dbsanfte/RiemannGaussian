/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszParityOrderPacket
import RiemannGaussian.ZetaRieszParityOrderPhase

/-!
# Uniform phase arrays on every good allocation

The original rectangle supplies an upper bound on every separate order;
the summed-tail split supplies the lower bound. A finite telescoping
estimate uses the count ceiling without expanding an infinite product.
This does not remove the literal prime-log or Riesz masks.
-/

namespace RiemannGaussian.ZetaRieszParityOrderTail
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszSkewAllocation ZetaRieszParityPacket
open ZetaRieszPrimeEndpoint ZetaRieszWideOwnerAudit ZetaRieszAnnulusJoint
open ZetaRieszPrimeCountFrequency ZetaRieszMatchedMiddle

/-- The small-prime logarithmic derivative adds exactly one order. -/
def legOrder (n : ℕ) (d : ℕ → ℕ) (p : ℕ) : ℕ := d p+if p = n.minFac then 1 else 0

/-- Every individual order in a good literal rectangle meets both
endpoints of the independently proved finite-prime phase band. -/
theorem good_rectangle_orders {N n : ℕ} (hN : 100 ≤ N) (hn : FullParityBox n)
    {d : ℕ → ℕ} (hd : d ∈ rectangleAllocations N n)
    (hg : GoodAllocation n.primeFactors N d) {p : ℕ} (hp : p ∈ n.primeFactors) :
    N ≤ 200*legOrder n d p ∧ 40*legOrder n d p ≤ 27*N := by
  obtain ⟨hdA, hdR⟩ := Finset.mem_filter.mp hd
  have hsum := (Finset.mem_piAntidiag.mp hdA).1
  obtain ⟨_, _, hjlo, hjhi, _, _⟩ := Finset.mem_filter.mp hdR
  have hlow := hg p hp
  have hleg : d p ≤ legOrder n d p ∧ legOrder n d p ≤ d p+1 := by
    unfold legOrder
    split_ifs <;> omega
  constructor
  · omega
  · by_cases he : p = largestPrime n
    · subst p
      omega
    · have hpE : p ∈ n.primeFactors.erase (largestPrime n) := Finset.mem_erase.mpr ⟨he, hp⟩
      have heq := Finset.sum_erase_add n.primeFactors d hn.largest_mem
      rw [hsum] at heq
      have hpart := Finset.single_le_sum (s := n.primeFactors.erase (largestPrime n))
        (f := d) (fun _ _ => Nat.zero_le _) hpE
      omega

/-- A finite telescoping product estimate, with exact parity sign. -/
theorem product_phase_error {ι : Type*} (S : Finset ι) (a : ι → ℂ) {ε : ℝ}
    (hε1 : ε ≤ 1) (ha : ∀ i ∈ S, ‖a i+1‖ ≤ ε) :
    ‖(∏ i ∈ S, a i)-(-1 : ℂ)^S.card‖ ≤ ε*((2 : ℝ)^S.card-1) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hierr := ha i (Finset.mem_insert_self _ _)
    have hS : ∀ j ∈ S, ‖a j+1‖ ≤ ε := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hprod := ih hS
    have hi2 : ‖a i‖ ≤ 2 := by
      have hh := norm_sub_le (a i+1) (1 : ℂ)
      simp only [add_sub_cancel_right, norm_one] at hh
      linarith
    have he : a i*(∏ j ∈ S, a j)-(-1 : ℂ)^(S.card+1) =
        a i*((∏ j ∈ S, a j)-(-1 : ℂ)^S.card)+(a i+1)*(-1 : ℂ)^S.card := by
      rw [pow_succ]
      ring
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, he]
    calc
      _ ≤ ‖a i‖*‖(∏ j ∈ S, a j)-(-1 : ℂ)^S.card‖+‖a i+1‖ := by
        simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one] using
          norm_add_le (a i*((∏ j ∈ S, a j)-(-1 : ℂ)^S.card)) ((a i+1)*(-1 : ℂ)^S.card)
      _ ≤ 2*(ε*((2 : ℝ)^S.card-1))+ε :=
        add_le_add (mul_le_mul hi2 hprod (norm_nonneg _) (by norm_num)) hierr
      _ = _ := by rw [pow_succ]; ring

/-- Under a simple exposed zero, all good arrays have the count-parity
phase uniformly. The remaining masks are not silently removed. -/
theorem eventually_good_product_phase (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (huU : 3/2-rho.1.re ≤ radiusCeiling)
    (hsimple : analyticZetaZeroMultiplicity rho = 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, FullParityBox n →
      ∀ d ∈ rectangleAllocations N n, GoodAllocation n.primeFactors N d →
        ‖(∏ p ∈ n.primeFactors,
          weightedFinite (3/2-rho.1.re) rho.1.im N (legOrder n d p))-
            (-1 : ℂ)^n.primeFactors.card‖ ≤ ε := by
  have he0 : 0 < ε/(2 : ℝ)^39 := by positivity
  have he1 : ε/(2 : ℝ)^39 ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact hε1.trans (by norm_num)
  filter_upwards [ZetaRieszParityOrderPhase.eventually_uniform_parity_phase
    rho hrho hexposed huU he0, eventually_ge_atTop 100] with N hphase hN
  intro n hn d hd hg
  have hb := product_phase_error n.primeFactors
    (fun p => weightedFinite (3/2-rho.1.re) rho.1.im N (legOrder n d p)) he1 (by
      intro p hp
      obtain ⟨hlo, hhi⟩ := good_rectangle_orders hN hn hd hg hp
      simpa only [hsimple, Nat.cast_one] using hphase (legOrder n d p) hlo hhi)
  have hpow : (2 : ℝ)^n.primeFactors.card ≤ (2 : ℝ)^39 :=
    pow_le_pow_right₀ (by norm_num) (fullParityBox_count_le hn)
  apply hb.trans
  calc
    _ ≤ (ε/(2 : ℝ)^39)*(2 : ℝ)^39 :=
      mul_le_mul_of_nonneg_left (by linarith) he0.le
    _ = ε := div_mul_cancel₀ _ (by positivity)

end
end RiemannGaussian.ZetaRieszParityOrderTail
