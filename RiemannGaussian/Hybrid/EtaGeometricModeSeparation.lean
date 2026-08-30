import RiemannGaussian.Hybrid.EtaGeometricPhaseSampling
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Prime.Int

/-!
# Collision-free prime bases for eta geometric modes

Geometric sampling turns each eta-tail phase into powers of one complex mode.
To apply finite geometric-phase rigidity, distinct ordinates must give distinct
modes.  This module proves that a phase collision for one pair of distinct
real frequencies can occur at at most one prime base.  The proof compares the
two integer periods forced by a hypothetical collision at two primes and uses
unique factorization of nonzero prime powers.

For a finite injective frequency family, the bad primes therefore inject into
the finite set of ordered frequency pairs.  A larger odd prime supplies a
simultaneously collision-free base.  The normalized complex-power mode is
proved equal to the corresponding unit phase, and the result is specialized
to every finite set of nontrivial zeta zeros lying on one real-coordinate
layer.

This closes prime-base collision avoidance within each real-decay layer.  It
does not yet peel distinct real-decay layers or extract a finite family of
cutoff coordinates from the resulting independent infinite sequences.
-/

open Complex

namespace RiemannGaussian

noncomputable section

/-- Unit complex phase obtained by geometrically sampling a real frequency at
the natural base `q`. -/
def etaLogarithmicUnitPhase (q : ℕ) (gamma : ℝ) : ℂ :=
  Complex.exp (Complex.ofReal (-(gamma * Real.log q)) * I)

/-- The real-decay-normalized geometric mode associated with a complex
exponent. -/
def etaGeometricNormalizedMode (q : ℕ) (s : ℂ) : ℂ :=
  (q : ℂ) ^ ((s.re : ℂ) - s)

/-- Every logarithmic eta phase lies on the complex unit circle. -/
theorem norm_etaLogarithmicUnitPhase (q : ℕ) (gamma : ℝ) :
    ‖etaLogarithmicUnitPhase q gamma‖ = 1 := by
  unfold etaLogarithmicUnitPhase
  rw [Complex.norm_exp]
  have hre :
      (Complex.ofReal (-(gamma * Real.log q)) * I).re = 0 := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero]
  rw [hre, Real.exp_zero]

/-- At a positive natural base, removing the real decay from a complex power
leaves exactly its logarithmic unit phase. -/
theorem etaGeometricNormalizedMode_eq_phase
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    etaGeometricNormalizedMode q s = etaLogarithmicUnitPhase q s.im := by
  unfold etaGeometricNormalizedMode etaLogarithmicUnitPhase
  have hcast : (q : ℂ) = ((q : ℝ) : ℂ) := by norm_cast
  rw [hcast]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hq.ne')]
  apply congrArg Complex.exp
  rw [← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ q)]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im] <;>
    ring

/-- Every positive-base normalized geometric mode has unit norm. -/
theorem norm_etaGeometricNormalizedMode
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    ‖etaGeometricNormalizedMode q s‖ = 1 := by
  rw [etaGeometricNormalizedMode_eq_phase hq,
    norm_etaLogarithmicUnitPhase]

/-- Two frequencies collide at base `q` exactly when their logarithmic phase
difference is an integral multiple of a full turn. -/
theorem etaLogarithmicUnitPhase_eq_iff_exists_int (q : ℕ) (x y : ℝ) :
    etaLogarithmicUnitPhase q x = etaLogarithmicUnitPhase q y ↔
      ∃ k : ℤ, (x - y) * Real.log q = -(2 * Real.pi * k) := by
  rw [etaLogarithmicUnitPhase, etaLogarithmicUnitPhase,
    Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have him : -(x * Real.log q) =
        -(y * Real.log q) + (k : ℝ) * (2 * Real.pi) := by
      simpa only [Complex.add_im, Complex.mul_im, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat,
        Complex.im_ofNat, mul_one, mul_zero, zero_mul, add_zero, zero_add,
        sub_zero] using congrArg Complex.im hk
    linarith
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have him : -(x * Real.log q) =
        -(y * Real.log q) + (k : ℝ) * (2 * Real.pi) := by
      linarith
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat,
        Complex.im_ofNat, mul_one, mul_zero, zero_mul, zero_add, sub_zero]
    · simpa only [Complex.add_im, Complex.mul_im, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat,
        Complex.im_ofNat, mul_one, mul_zero, zero_mul, add_zero, zero_add,
        sub_zero] using him

/-- Collisions at two distinct prime bases force the underlying real
frequencies to coincide. -/
theorem etaLogarithmicUnitPhase_two_primes_injective
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {x y : ℝ}
    (hphaseP : etaLogarithmicUnitPhase p x =
      etaLogarithmicUnitPhase p y)
    (hphaseQ : etaLogarithmicUnitPhase q x =
      etaLogarithmicUnitPhase q y) :
    x = y := by
  by_contra hxy
  obtain ⟨k, hk⟩ :=
    (etaLogarithmicUnitPhase_eq_iff_exists_int p x y).mp hphaseP
  obtain ⟨l, hl⟩ :=
    (etaLogarithmicUnitPhase_eq_iff_exists_int q x y).mp hphaseQ
  have hkne : k ≠ 0 := by
    intro hkzero
    subst k
    simp only [Int.cast_zero, mul_zero, neg_zero] at hk
    have hdelta : x - y = 0 :=
      (mul_eq_zero.mp hk).resolve_right hp.log_ne_zero
    exact hxy (sub_eq_zero.mp hdelta)
  have hlne : l ≠ 0 := by
    intro hlzero
    subst l
    simp only [Int.cast_zero, mul_zero, neg_zero] at hl
    have hdelta : x - y = 0 :=
      (mul_eq_zero.mp hl).resolve_right hq.log_ne_zero
    exact hxy (sub_eq_zero.mp hdelta)
  have hcrossFact :
      (-2 * Real.pi) * ((k : ℝ) * Real.log q) =
        (-2 * Real.pi) * ((l : ℝ) * Real.log p) := by
    calc
      (-2 * Real.pi) * ((k : ℝ) * Real.log q) =
          ((x - y) * Real.log p) * Real.log q := by rw [hk]; ring
      _ = ((x - y) * Real.log q) * Real.log p := by ring
      _ = (-2 * Real.pi) * ((l : ℝ) * Real.log p) := by rw [hl]; ring
  have hfactor : (-2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hcross : (k : ℝ) * Real.log q =
      (l : ℝ) * Real.log p :=
    mul_left_cancel₀ hfactor hcrossFact
  have habs := congrArg abs hcross
  have hkabs : |(k : ℝ)| = (k.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    simp only [Int.cast_natCast]
  have hlabs : |(l : ℝ)| = (l.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    simp only [Int.cast_natCast]
  rw [abs_mul, abs_mul, hkabs, hlabs,
    abs_of_pos hq.log_pos, abs_of_pos hp.log_pos] at habs
  have hexp := congrArg Real.exp habs
  have hpcast : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hqcast : 0 < (q : ℝ) := by exact_mod_cast hq.pos
  rw [Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log hqcast, Real.exp_log hpcast] at hexp
  have hpow : q ^ k.natAbs = p ^ l.natAbs := by
    exact_mod_cast hexp
  have hprimeEq := hq.pow_inj' hp
    (Int.natAbs_ne_zero.mpr hkne) (Int.natAbs_ne_zero.mpr hlne) hpow
  exact hpq hprimeEq.1.symm

/-- For a fixed pair of distinct frequencies, at most one prime base can
produce a phase collision. -/
theorem etaLogarithmicUnitPhase_collision_prime_unique
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {x y : ℝ} (hxy : x ≠ y)
    (hphaseP : etaLogarithmicUnitPhase p x =
      etaLogarithmicUnitPhase p y)
    (hphaseQ : etaLogarithmicUnitPhase q x =
      etaLogarithmicUnitPhase q y) :
    p = q := by
  by_contra hpq
  exact hxy (etaLogarithmicUnitPhase_two_primes_injective
    hp hq hpq hphaseP hphaseQ)

/-- Every finite injective real frequency family admits one odd prime base at
which all logarithmic unit phases remain distinct. -/
theorem exists_prime_etaLogarithmicUnitPhase_injOn
    {ι : Type*} (s : Finset ι) (frequency : ι → ℝ)
    (hfrequency : Set.InjOn frequency s) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      Set.InjOn (fun i ↦ etaLogarithmicUnitPhase q (frequency i)) s := by
  classical
  let BadPrime := {q : ℕ // q.Prime ∧
    ¬Set.InjOn (fun i ↦ etaLogarithmicUnitPhase q (frequency i)) s}
  have hcollision : ∀ q : BadPrime,
      ∃ i ∈ s, ∃ j ∈ s,
        etaLogarithmicUnitPhase q (frequency i) =
          etaLogarithmicUnitPhase q (frequency j) ∧ i ≠ j := by
    intro q
    have hnot := q.property.2
    unfold Set.InjOn at hnot
    push Not at hnot
    exact hnot
  choose left hleft right hright hphase hne using hcollision
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
    have hfrequency_ne : frequency (left p) ≠ frequency (right p) := by
      intro hfreq
      exact hne p (hfrequency (hleft p) (hright p) hfreq)
    have hphaseQ :
        etaLogarithmicUnitPhase q (frequency (left p)) =
          etaLogarithmicUnitPhase q (frequency (right p)) := by
      rw [hleftEq, hrightEq]
      exact hphase q
    exact hpqval (etaLogarithmicUnitPhase_collision_prime_unique
      p.property.1 q.property.1 hfrequency_ne (hphase p) hphaseQ)
  let _ : Finite BadPrime :=
    Finite.of_injective witness hwitness_injective
  let _ : Fintype BadPrime := Fintype.ofFinite BadPrime
  let badValues : Finset ℕ := Finset.univ.image (fun q : BadPrime ↦ q.1)
  let bound : ℕ := badValues.sup id
  obtain ⟨q, hqbound, hqprime⟩ :=
    Nat.exists_infinite_primes (max (bound + 1) 3)
  have hqnotBad : ¬(q.Prime ∧
      ¬Set.InjOn (fun i ↦ etaLogarithmicUnitPhase q (frequency i)) s) := by
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
  have hqinj :
      Set.InjOn (fun i ↦ etaLogarithmicUnitPhase q (frequency i)) s := by
    by_contra hnot
    exact hqnotBad ⟨hqprime, hnot⟩
  have hqthree : 3 ≤ q :=
    (le_max_right (bound + 1) 3).trans hqbound
  exact ⟨q, hqprime, hqprime.odd_iff.mpr hqthree,
    hqprime.one_lt, hqinj⟩

/-- Every finite complex family with distinct imaginary parts admits one odd
prime base at which its normalized geometric modes are distinct. -/
theorem exists_prime_etaGeometricNormalizedMode_injOn
    {ι : Type*} (s : Finset ι) (exponent : ι → ℂ)
    (him : Set.InjOn (fun i ↦ (exponent i).im) s) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      Set.InjOn (fun i ↦ etaGeometricNormalizedMode q (exponent i)) s := by
  obtain ⟨q, hqprime, hqodd, hq, hphase⟩ :=
    exists_prime_etaLogarithmicUnitPhase_injOn
      s (fun i ↦ (exponent i).im) him
  refine ⟨q, hqprime, hqodd, hq, ?_⟩
  intro i hi j hj hmode
  apply hphase hi hj
  simpa only [etaGeometricNormalizedMode_eq_phase hq.le] using hmode

/-- Every finite set of nontrivial zeta zeros on one real-coordinate layer
admits one odd prime base whose normalized geometric modes are pairwise
distinct. -/
theorem exists_prime_etaGeometricNormalizedMode_injOn_zetaZeros_same_re
    (s : Finset NontrivialZetaZero) {sigma : ℝ}
    (hre : ∀ rho : NontrivialZetaZero, rho ∈ s → rho.val.re = sigma) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      Set.InjOn
        (fun rho : NontrivialZetaZero ↦
          etaGeometricNormalizedMode q rho.val) s := by
  have him : Set.InjOn
      (fun rho : NontrivialZetaZero ↦ rho.val.im) s := by
    intro rho hrho zeta hzeta him
    apply Subtype.ext
    apply Complex.ext
    · rw [hre rho hrho, hre zeta hzeta]
    · exact him
  exact exists_prime_etaGeometricNormalizedMode_injOn s
    (fun rho : NontrivialZetaZero ↦ rho.val) him

end

end RiemannGaussian
