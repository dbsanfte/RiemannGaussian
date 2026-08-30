import RiemannGaussian.Hybrid.EtaGeometricModeSeparation
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Full-window eta decay-mode separation and finite Vandermonde extraction

The raw geometric asymptotic of a centered eta prefix has decay mode
`((q : ℂ)^s)⁻¹`.  Unlike the unit phase alone, this mode retains both parts of
the spectral parameter: its norm is `q ^ (-Re s)`, while its orientation is
the logarithmic phase already separated in the preceding module.

Lean proves that a collision between two distinct complex exponents can occur
at at most one prime base.  Hence one odd prime simultaneously separates the
raw decay modes across an arbitrary finite zeta-zero window, without first
partitioning it by real coordinate.  Distinct real layers are separated by
norm; collisions inside one layer reduce to the checked two-prime phase
rigidity theorem.

For a window of cardinality `d`, the first `d` geometric coordinates form the
corresponding Vandermonde matrix.  Its determinant is nonzero at the selected
prime base.  This is finite exact separation of the limiting geometric modes,
not yet of the literal finite eta-prefix sequences.  The next step is to use
their checked sharp asymptotics to transfer this nonzero determinant to an
eventual finite eta evaluation matrix.
-/

open Complex

namespace RiemannGaussian

noncomputable section

/-- Raw inverse geometric mode governing the centered eta-prefix decay at
base `q`. -/
def etaGeometricDecayMode (q : ℕ) (s : ℂ) : ℂ :=
  ((q : ℂ) ^ s)⁻¹

/-- The raw decay-mode norm records exactly the real part of the exponent. -/
theorem norm_etaGeometricDecayMode
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    ‖etaGeometricDecayMode q s‖ = (q : ℝ) ^ (-s.re) := by
  unfold etaGeometricDecayMode
  have hcast : (q : ℂ) = ((q : ℝ) : ℂ) := by norm_cast
  rw [hcast, norm_inv,
    norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hq)]
  rw [← Real.rpow_neg (by exact_mod_cast hq.le) s.re]

/-- At any base greater than one, equality of raw decay modes forces equality
of their real exponents. -/
theorem etaGeometricDecayMode_eq_imp_re_eq
    {q : ℕ} (hq : 1 < q) {s t : ℂ}
    (hmode : etaGeometricDecayMode q s = etaGeometricDecayMode q t) :
    s.re = t.re := by
  have hnorm := congrArg norm hmode
  rw [norm_etaGeometricDecayMode hq.le,
    norm_etaGeometricDecayMode hq.le] at hnorm
  have hqreal : (1 : ℝ) < q := by exact_mod_cast hq
  exact neg_injective
    ((Real.strictMono_rpow_of_base_gt_one hqreal).injective hnorm)

/-- The normalized unit phase factors as positive real growth times the raw
inverse decay mode. -/
theorem etaGeometricNormalizedMode_eq_real_cpow_mul_decayMode
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    etaGeometricNormalizedMode q s =
      (q : ℂ) ^ (s.re : ℂ) * etaGeometricDecayMode q s := by
  unfold etaGeometricNormalizedMode etaGeometricDecayMode
  rw [Complex.cpow_sub _ _ (by exact_mod_cast hq.ne')]
  rfl

/-- Collisions of two raw complex decay modes at distinct prime bases force
the complete complex exponents to coincide. -/
theorem etaGeometricDecayMode_two_primes_injective
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {s t : ℂ}
    (hmodeP : etaGeometricDecayMode p s = etaGeometricDecayMode p t)
    (hmodeQ : etaGeometricDecayMode q s = etaGeometricDecayMode q t) :
    s = t := by
  have hre : s.re = t.re :=
    etaGeometricDecayMode_eq_imp_re_eq hp.one_lt hmodeP
  have hnormalizedP :
      etaGeometricNormalizedMode p s = etaGeometricNormalizedMode p t := by
    rw [etaGeometricNormalizedMode_eq_real_cpow_mul_decayMode hp.pos,
      etaGeometricNormalizedMode_eq_real_cpow_mul_decayMode hp.pos,
      hre, hmodeP]
  have hnormalizedQ :
      etaGeometricNormalizedMode q s = etaGeometricNormalizedMode q t := by
    rw [etaGeometricNormalizedMode_eq_real_cpow_mul_decayMode hq.pos,
      etaGeometricNormalizedMode_eq_real_cpow_mul_decayMode hq.pos,
      hre, hmodeQ]
  have hphaseP :
      etaLogarithmicUnitPhase p s.im =
        etaLogarithmicUnitPhase p t.im := by
    simpa only [etaGeometricNormalizedMode_eq_phase hp.pos] using hnormalizedP
  have hphaseQ :
      etaLogarithmicUnitPhase q s.im =
        etaLogarithmicUnitPhase q t.im := by
    simpa only [etaGeometricNormalizedMode_eq_phase hq.pos] using hnormalizedQ
  have him := etaLogarithmicUnitPhase_two_primes_injective
    hp hq hpq hphaseP hphaseQ
  apply Complex.ext
  · exact hre
  · exact him

/-- For any fixed pair of distinct complex exponents, at most one prime base
can produce a raw decay-mode collision. -/
theorem etaGeometricDecayMode_collision_prime_unique
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {s t : ℂ} (hst : s ≠ t)
    (hmodeP : etaGeometricDecayMode p s = etaGeometricDecayMode p t)
    (hmodeQ : etaGeometricDecayMode q s = etaGeometricDecayMode q t) :
    p = q := by
  by_contra hpq
  exact hst (etaGeometricDecayMode_two_primes_injective
    hp hq hpq hmodeP hmodeQ)

/-- Every finite injective family of complex exponents has one odd prime base
at which all raw eta decay modes are distinct. -/
theorem exists_prime_etaGeometricDecayMode_injOn
    {ι : Type*} (s : Finset ι) (exponent : ι → ℂ)
    (hexponent : Set.InjOn exponent s) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      Set.InjOn (fun i ↦ etaGeometricDecayMode q (exponent i)) s := by
  classical
  let BadPrime := {q : ℕ // q.Prime ∧
    ¬Set.InjOn (fun i ↦ etaGeometricDecayMode q (exponent i)) s}
  have hcollision : ∀ q : BadPrime,
      ∃ i ∈ s, ∃ j ∈ s,
        etaGeometricDecayMode q (exponent i) =
          etaGeometricDecayMode q (exponent j) ∧ i ≠ j := by
    intro q
    have hnot := q.property.2
    unfold Set.InjOn at hnot
    push Not at hnot
    exact hnot
  choose left hleft right hright hmode hne using hcollision
  let witness : BadPrime → s × s := fun q ↦
    (⟨left q, hleft q⟩, ⟨right q, hright q⟩)
  have hwitness_injective : Function.Injective witness := by
    intro p q hpq
    apply Subtype.ext
    by_contra hpqval
    have hleftEq : left p = left q := by
      exact congrArg (fun z : s × s ↦ z.1.1) hpq
    have hrightEq : right p = right q := by
      exact congrArg (fun z : s × s ↦ z.2.1) hpq
    have hexponent_ne : exponent (left p) ≠ exponent (right p) := by
      intro hexp
      exact hne p (hexponent (hleft p) (hright p) hexp)
    have hmodeQ :
        etaGeometricDecayMode q (exponent (left p)) =
          etaGeometricDecayMode q (exponent (right p)) := by
      rw [hleftEq, hrightEq]
      exact hmode q
    exact hpqval (etaGeometricDecayMode_collision_prime_unique
      p.property.1 q.property.1 hexponent_ne (hmode p) hmodeQ)
  let _ : Finite BadPrime :=
    Finite.of_injective witness hwitness_injective
  let _ : Fintype BadPrime := Fintype.ofFinite BadPrime
  let badValues : Finset ℕ := Finset.univ.image (fun q : BadPrime ↦ q.1)
  let bound : ℕ := badValues.sup id
  obtain ⟨q, hqbound, hqprime⟩ :=
    Nat.exists_infinite_primes (max (bound + 1) 3)
  have hqnotBad : ¬(q.Prime ∧
      ¬Set.InjOn (fun i ↦ etaGeometricDecayMode q (exponent i)) s) := by
    intro hqbad
    let bq : BadPrime := ⟨q, hqbad⟩
    have hqmem : q ∈ badValues := by
      apply Finset.mem_image.mpr
      exact ⟨bq, Finset.mem_univ bq, rfl⟩
    have hqle : q ≤ bound := by
      exact Finset.le_sup (f := id) hqmem
    have hboundlt : bound < q := by
      have : bound + 1 ≤ q :=
        (le_max_left (bound + 1) 3).trans hqbound
      omega
    exact (not_lt_of_ge hqle) hboundlt
  have hqinj : Set.InjOn
      (fun i ↦ etaGeometricDecayMode q (exponent i)) s := by
    by_contra hnot
    exact hqnotBad ⟨hqprime, hnot⟩
  have hqthree : 3 ≤ q :=
    (le_max_right (bound + 1) 3).trans hqbound
  exact ⟨q, hqprime, hqprime.odd_iff.mpr hqthree,
    hqprime.one_lt, hqinj⟩

/-- Every finite nontrivial zeta-zero window has one odd prime base whose raw
eta decay modes are pairwise distinct across the entire window. -/
theorem exists_prime_etaGeometricDecayMode_injOn_zetaZeros
    (s : Finset NontrivialZetaZero) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      Set.InjOn
        (fun rho : NontrivialZetaZero ↦
          etaGeometricDecayMode q rho.val) s := by
  apply exists_prime_etaGeometricDecayMode_injOn s
    (fun rho : NontrivialZetaZero ↦ rho.val)
  intro rho _hrho zeta _hzeta hval
  exact Subtype.ext hval

private noncomputable def finsetEquivFin
    {ι : Type*} (s : Finset ι) : s ≃ Fin s.card :=
  Fintype.equivFinOfCardEq (by simp)

/-- Square evaluation matrix of the raw decay modes on the first `s.card`
geometric coordinates. -/
def etaGeometricDecayModeVandermonde
    (q : ℕ) (s : Finset NontrivialZetaZero) :
    Matrix (Fin s.card) (Fin s.card) ℂ :=
  Matrix.vandermonde (fun i ↦
    etaGeometricDecayMode q ((finsetEquivFin s).symm i).val)

/-- Each entry of the finite raw-mode evaluation matrix is the corresponding
mode raised to its coordinate index. -/
theorem etaGeometricDecayModeVandermonde_apply
    (q : ℕ) (s : Finset NontrivialZetaZero)
    (i j : Fin s.card) :
    etaGeometricDecayModeVandermonde q s i j =
      etaGeometricDecayMode q ((finsetEquivFin s).symm i).val ^ (j : ℕ) :=
  rfl

/-- Pairwise separation of the raw modes makes their first-cardinality
Vandermonde evaluation matrix nonsingular. -/
theorem det_etaGeometricDecayModeVandermonde_ne_zero
    {q : ℕ} {s : Finset NontrivialZetaZero}
    (hinj : Set.InjOn
      (fun rho : NontrivialZetaZero ↦
        etaGeometricDecayMode q rho.val) s) :
    (etaGeometricDecayModeVandermonde q s).det ≠ 0 := by
  apply Matrix.det_vandermonde_ne_zero_iff.mpr
  intro i j hmode
  apply (finsetEquivFin s).symm.injective
  apply Subtype.ext
  exact hinj
    ((finsetEquivFin s).symm i).property
    ((finsetEquivFin s).symm j).property hmode

/-- One odd prime simultaneously separates every raw decay mode in a finite
zeta-zero window and makes the first-cardinality geometric evaluation matrix
nonsingular. -/
theorem exists_prime_det_etaGeometricDecayModeVandermonde_ne_zero
    (s : Finset NontrivialZetaZero) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      (etaGeometricDecayModeVandermonde q s).det ≠ 0 := by
  obtain ⟨q, hqprime, hqodd, hq, hinj⟩ :=
    exists_prime_etaGeometricDecayMode_injOn_zetaZeros s
  exact ⟨q, hqprime, hqodd, hq,
    det_etaGeometricDecayModeVandermonde_ne_zero hinj⟩

end

end RiemannGaussian
