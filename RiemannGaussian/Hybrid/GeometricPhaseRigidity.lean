import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Rigidity of finite geometric phase sums

Distinct unit-modulus modes cannot cancel asymptotically forever.  More
precisely, if a finite linear combination of the sequences `n ↦ z ^ n`
converges to zero and the modes `z` are distinct points of the unit circle,
then every coefficient vanishes.

The proof deliberately avoids averaging or a Vandermonde inverse.  Removing
one selected mode by the shift difference `S (n + 1) - z * S n` leaves the
same problem on a smaller finite set.  This form is suited to the eta cutoff
asymptotics: after sampling at geometrically growing odd endpoints, distinct
spectral phases become distinct unit-circle modes while faster real-decay
layers can be peeled away separately.
-/

open Filter Topology
open scoped BigOperators

namespace RiemannGaussian

/-- A finite sum of distinct unit-circle geometric modes can tend to zero
only when all of its coefficients are zero. -/
theorem finite_geometric_phase_rigidity
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (mode coefficient : ι → ℂ)
    (hunit : ∀ i ∈ s, ‖mode i‖ = 1)
    (hinj : Set.InjOn mode s)
    (hzero : Tendsto
      (fun n : ℕ ↦ ∑ i ∈ s, coefficient i * mode i ^ n)
      atTop (nhds 0)) :
    ∀ i ∈ s, coefficient i = 0 := by
  classical
  revert mode coefficient
  induction s using Finset.induction_on with
  | empty =>
      intro mode coefficient _hunit _hinj _hzero i hi
      simp at hi
  | @insert a s ha ih =>
      intro mode coefficient hunit hinj hzero
      have hunit_s : ∀ i ∈ s, ‖mode i‖ = 1 := by
        intro i hi
        exact hunit i (Finset.mem_insert_of_mem hi)
      have hinj_s : Set.InjOn mode s :=
        hinj.mono (by intro i hi; exact Finset.mem_insert_of_mem hi)
      have hshift : Tendsto
          (fun n : ℕ ↦
            ∑ i ∈ insert a s, coefficient i * mode i ^ (n + 1))
          atTop (nhds 0) :=
        hzero.comp (tendsto_add_atTop_nat 1)
      have hdifference : Tendsto
          (fun n : ℕ ↦
            ∑ i ∈ s,
              (coefficient i * (mode i - mode a)) * mode i ^ n)
          atTop (nhds 0) := by
        have hsub := hshift.sub (Filter.Tendsto.const_mul (mode a) hzero)
        convert hsub using 1
        · funext n
          simp only [Finset.sum_insert ha, pow_succ]
          symm
          calc
            _ = (∑ i ∈ s, coefficient i * (mode i ^ n * mode i)) -
                  mode a * (∑ i ∈ s, coefficient i * mode i ^ n) := by
                ring
            _ = ∑ i ∈ s,
                  (coefficient i * (mode i ^ n * mode i) -
                    mode a * (coefficient i * mode i ^ n)) := by
                rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            _ = ∑ i ∈ s,
                  (coefficient i * (mode i - mode a)) * mode i ^ n := by
                apply Finset.sum_congr rfl
                intro i _hi
                ring
        · simp
      have hmodified :
          ∀ i ∈ s, coefficient i * (mode i - mode a) = 0 :=
        ih mode (fun i ↦ coefficient i * (mode i - mode a))
          hunit_s hinj_s hdifference
      have hcoefficient_s : ∀ i ∈ s, coefficient i = 0 := by
        intro i hi
        have hmode_ne : mode i ≠ mode a := by
          intro hmode
          have hia : i = a := hinj
            (Finset.mem_insert_of_mem hi) (by simp) hmode
          subst i
          exact ha hi
        exact (mul_eq_zero.mp (hmodified i hi)).resolve_right
          (sub_ne_zero.mpr hmode_ne)
      have hsingle : Tendsto
          (fun n : ℕ ↦ coefficient a * mode a ^ n)
          atTop (nhds 0) := by
        convert hzero using 1
        funext n
        rw [Finset.sum_insert ha]
        have hsum : ∑ i ∈ s, coefficient i * mode i ^ n = 0 :=
          Finset.sum_eq_zero fun i hi ↦ by
            rw [hcoefficient_s i hi, zero_mul]
        rw [hsum, add_zero]
      have hnorm : Tendsto (fun _ : ℕ ↦ ‖coefficient a‖)
          atTop (nhds 0) := by
        convert hsingle.norm using 1
        · funext n
          rw [norm_mul, norm_pow, hunit a (by simp)]
          simp
        · simp
      have hcoefficient_a : coefficient a = 0 := by
        apply norm_eq_zero.mp
        exact tendsto_nhds_unique tendsto_const_nhds hnorm
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hcoefficient_a
      · exact hcoefficient_s i hi

/-- The geometric sequences attached to any finite family of distinct
unit-circle modes are linearly independent in the full sequence space. -/
theorem finite_geometric_phase_linearIndependent
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (mode : ι → ℂ)
    (hunit : ∀ i ∈ s, ‖mode i‖ = 1)
    (hinj : Set.InjOn mode s) :
    LinearIndependent ℂ (fun i : s ↦ fun n : ℕ ↦ mode i ^ n) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coefficient hsum
  have hpoint : ∀ n : ℕ,
      ∑ i, coefficient i * mode i ^ n = 0 := by
    intro n
    have := congrFun hsum n
    simpa using this
  have hzero : Tendsto
      (fun n : ℕ ↦ ∑ i, coefficient i * mode i ^ n)
      atTop (nhds 0) := by
    convert (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ (0 : ℂ)) atTop (nhds 0)) using 1
    funext n
    exact hpoint n
  have hcoeff := finite_geometric_phase_rigidity
    (Finset.univ : Finset s) (fun i ↦ mode i) coefficient
    (by intro i _hi; exact hunit i i.property)
    (by
      intro i _hi j _hj hij
      exact Subtype.ext (hinj i.property j.property hij))
    hzero
  intro i
  exact hcoeff i (by simp)

end RiemannGaussian
