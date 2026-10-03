/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCentreFreeCover
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Geometric interval products retain a recoverable collision index

An interval product, its target derivative and its logarithmic base
derivative extract the exponent index in each hidden prime field. When
the product saturates the entire modulus, the resulting CRT index can
still separate the primes. A short ordinary integer-prefix batch recovers
the factor without materializing the geometric interval or a pair matrix.

The optional blocked q-factorial engine computes the three scalars. The
identities below certify their meaning, not that engine or its bit cost.
Evaluating every possible row still has an unresolved total search cost;
no universal one-sixth factoring theorem is claimed.
-/

namespace RiemannGaussian.SemiprimeIntervalJet

open scoped BigOperators
open Polynomial

/-- One interval factor is omitted, retaining every other target. -/
def cofactor {R : Type*} [CommRing R] (alpha x : R) (L u : ℕ) : R :=
  ∏ v ∈ (Finset.range L).erase u, (x-alpha^v)

/-- The original geometric interval detector. -/
def intervalProduct {R : Type*} [CommRing R] (alpha x : R) (L : ℕ) : R :=
  ∏ v ∈ Finset.range L, (x-alpha^v)

/-- First derivative with respect to the target x. -/
def targetDerivative {R : Type*} [CommRing R] (alpha x : R) (L : ℕ) : R :=
  ∑ u ∈ Finset.range L, cofactor alpha x L u

/-- Logarithmic base derivative alpha*d/dalpha, with the target held fixed.
It preserves the original exponent label in every marked term. -/
def baseDerivative {R : Type*} [CommRing R] (alpha x : R) (L : ℕ) : R :=
  -∑ u ∈ Finset.range L, (u : R)*alpha^u*cofactor alpha x L u

/-- The derivative is evaluated on a degree-L target polynomial. -/
theorem targetDerivative_eq_derivative {R : Type*} [CommRing R] (alpha x : R) (L : ℕ) :
    targetDerivative alpha x L =
      (SemiprimeCartesianCompletion.rootPolynomial (Finset.range L) (fun u => alpha^u)).derivative.eval x := by
  simp only [SemiprimeCartesianCompletion.rootPolynomial, derivative_prod_finset,
    derivative_X_sub_C, mul_one, eval_finsetSum, eval_prod, eval_sub, eval_X, eval_C,
    targetDerivative, cofactor]

/-- The marked cofactor sum is exactly the logarithmic base derivative
of the same original product, rather than an endpoint quotient. -/
theorem baseDerivative_eq_derivative {R : Type*} [CommRing R] (alpha x : R) (L : ℕ) :
    baseDerivative alpha x L =
      alpha*(∏ u ∈ Finset.range L, (C x-X^u : R[X])).derivative.eval alpha := by
  simp only [derivative_prod_finset, derivative_sub, derivative_C, derivative_X_pow,
    zero_sub, eval_finsetSum, eval_mul, eval_prod, eval_sub, eval_C, eval_pow, eval_X, eval_neg]
  rw [Finset.mul_sum]
  unfold baseDerivative
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro u _
  unfold cofactor
  by_cases hu : u=0
  · simp [hu]
  · have he : alpha^(u-1)*alpha=alpha^u := by
      rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ u by omega)]
    symm
    calc
      alpha*((∏ v ∈ (Finset.range L).erase u, (x-alpha^v)) *
          -((u : R)*alpha^(u-1))) =
        -((u : R)*(alpha^(u-1)*alpha)*
          (∏ v ∈ (Finset.range L).erase u, (x-alpha^v))) := by ring
      _ = _ := by rw [he]

/-- Products and both derivatives commute with reduction to a hidden field. -/
theorem intervalProduct_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (alpha x : R) (L : ℕ) :
    f (intervalProduct alpha x L)=intervalProduct (f alpha) (f x) L := by
  simp [intervalProduct]

theorem targetDerivative_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (alpha x : R) (L : ℕ) :
    f (targetDerivative alpha x L)=targetDerivative (f alpha) (f x) L := by
  simp [targetDerivative, cofactor]

theorem baseDerivative_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (alpha x : R) (L : ℕ) :
    f (baseDerivative alpha x L)=baseDerivative (f alpha) (f x) L := by
  simp [baseDerivative, cofactor]

/-- The scalar detector retains exactly the original interval's root union. -/
theorem intervalProduct_zero_iff {R : Type*} [CommRing R] [IsDomain R]
    (alpha x : R) (L : ℕ) :
    intervalProduct alpha x L=0 ↔ ∃ u<L, x=alpha^u := by
  simp only [intervalProduct, Finset.prod_eq_zero_iff, Finset.mem_range, sub_eq_zero]

/-- A root in the omitted-factor product kills every incorrectly marked
term. No division or generic position assumption occurs here. -/
theorem cofactor_at_other_root {R : Type*} [CommRing R] (alpha : R)
    {L k u : ℕ} (hk : k<L) (hku : k ≠ u) :
    cofactor alpha (alpha^k) L u=0 := by
  unfold cofactor
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hku, Finset.mem_range.mpr hk⟩) (sub_self _)

/-- The target derivative at an interval root keeps just its cofactor. -/
theorem targetDerivative_at_root {R : Type*} [CommRing R] (alpha : R)
    {L k : ℕ} (hk : k<L) :
    targetDerivative alpha (alpha^k) L=cofactor alpha (alpha^k) L k := by
  unfold targetDerivative
  apply Finset.sum_eq_single k
  · intro u _ huk
    exact cofactor_at_other_root alpha hk huk.symm
  · intro hn
    exact (hn (Finset.mem_range.mpr hk)).elim

/-- The logarithmic derivative retains the integer exponent index. -/
theorem baseDerivative_at_root {R : Type*} [CommRing R] (alpha : R)
    {L k : ℕ} (hk : k<L) :
    baseDerivative alpha (alpha^k) L=
      -(k : R)*alpha^k*targetDerivative alpha (alpha^k) L := by
  rw [targetDerivative_at_root alpha hk]
  unfold baseDerivative
  rw [Finset.sum_eq_single k]
  · ring
  · intro u _ huk
    rw [cofactor_at_other_root alpha hk huk.symm, mul_zero]
  · intro hn
    exact (hn (Finset.mem_range.mpr hk)).elim

/-- A period at least the interval length makes its target powers distinct. -/
theorem interval_powers_injective {R : Type*} [Monoid R] (alpha : R)
    {L : ℕ} (hL : L ≤ orderOf alpha) :
    Function.Injective (fun i : Fin L => alpha^(i : ℕ)) := by
  intro i j he
  apply Fin.ext
  exact pow_injOn_Iio_orderOf (i.isLt.trans_le hL) (j.isLt.trans_le hL) he

/-- Every interval root is simple in a prime field whose period is long. -/
theorem targetDerivative_at_root_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    (alpha : R) {L k : ℕ} (hk : k<L) (hL : L ≤ orderOf alpha) :
    targetDerivative alpha (alpha^k) L ≠ 0 := by
  rw [targetDerivative_at_root alpha hk]
  unfold cofactor
  apply Finset.prod_ne_zero_iff.mpr
  intro u hu
  have hh := Finset.mem_erase.mp hu
  apply sub_ne_zero.mpr
  intro he
  have hku := pow_injOn_Iio_orderOf (hk.trans_le hL)
    ((Finset.mem_range.mp hh.2).trans_le hL) he
  exact hh.1 hku.symm

/-- A nonzero polynomial annihilating the entire distinct interval has
degree at least L. This restricts one representation, not all algorithms. -/
theorem interval_annihilator_degree {R : Type*} [CommRing R] [IsDomain R]
    (alpha : R) {L : ℕ} (hL : L ≤ orderOf alpha) (P : R[X]) (hP : P ≠ 0)
    (hzero : ∀ u<L, P.eval (alpha^u)=0) : L ≤ P.natDegree := by
  by_contra hn
  apply hP
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (interval_powers_injective alpha hL)
  · intro i
    exact hzero i i.isLt
  · simpa using (show P.natDegree<L by omega)

/-- Nonzero reductions in both prime fields certify a public unit over
the semiprime ring, without an assumption about inverses. -/
theorem isUnit_of_prime_reductions {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (x : ZMod (p*q))
    (hP : ZMod.castHom (dvd_mul_right p q) (ZMod p) x ≠ 0)
    (hQ : ZMod.castHom (dvd_mul_left q p) (ZMod q) x ≠ 0) : IsUnit x := by
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  have hpnd : ¬p ∣ x.val := by
    intro hd
    apply hP
    rw [← SemiprimeCentreFreeCover.castHom_val (dvd_mul_right p q)]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have hqnd : ¬q ∣ x.val := by
    intro hd
    apply hQ
    rw [← SemiprimeCentreFreeCover.castHom_val (dvd_mul_left q p)]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have hcop : x.val.Coprime (p*q) :=
    (hp.coprime_iff_not_dvd.mpr hpnd).symm.mul_right
      (hq.coprime_iff_not_dvd.mpr hqnd).symm
  have hu := (ZMod.isUnit_iff_coprime x.val (p*q)).mpr hcop
  simpa only [ZMod.natCast_zmod_val] using hu

/-- A saturated row with distinct local interval powers has a unit
target derivative. Its inverse is a proved public certificate. -/
theorem saturated_targetDerivative_isUnit {p q L : ℕ}
    (hp : p.Prime) (hq : q.Prime) (alpha x : ZMod (p*q))
    (hLP : L ≤ orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p) alpha))
    (hLQ : L ≤ orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q) alpha))
    (hzero : intervalProduct alpha x L=0) :
    IsUnit (targetDerivative alpha x L) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  apply isUnit_of_prime_reductions hp hq
  · rw [targetDerivative_map]
    have hz := congrArg (ZMod.castHom (dvd_mul_right p q) (ZMod p)) hzero
    rw [intervalProduct_map, map_zero, intervalProduct_zero_iff] at hz
    obtain ⟨k, hk, he⟩ := hz
    rw [he]
    exact targetDerivative_at_root_ne_zero _ hk hLP
  · rw [targetDerivative_map]
    have hz := congrArg (ZMod.castHom (dvd_mul_left q p) (ZMod q)) hzero
    rw [intervalProduct_map, map_zero, intervalProduct_zero_iff] at hz
    obtain ⟨k, hk, he⟩ := hz
    rw [he]
    exact targetDerivative_at_root_ne_zero _ hk hLQ

/-- Failed public short-period recovery supplies the required simple
roots in the full centre-free target interval. -/
theorem projected_interval_periods_long {p q B : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hB : 0 < B) (g : (ZMod (p*q))ˣ)
    (hclear : (p*q).gcd ((SemiprimeCentreFreeCover.projectedUnit g B : ZMod (p*q))-1).val=1)
    (hnone : SemiprimeCentreFreeCover.recoverShort
      (SemiprimeCentreFreeCover.projectedUnit g B) (2*B+1)=none) :
    3*B^2+1 ≤ orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      (SemiprimeCentreFreeCover.projectedUnit g B : ZMod (p*q))) ∧
    3*B^2+1 ≤ orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      (SemiprimeCentreFreeCover.projectedUnit g B : ZMod (p*q))) := by
  have hh := SemiprimeCentreFreeCover.failed_projected_short_forces_long hp hq g
    (by omega) hclear hnone
  have hP : orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      (SemiprimeCentreFreeCover.projectedUnit g B : ZMod (p*q))) =
      orderOf (Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom
        (SemiprimeCentreFreeCover.projectedUnit g B)) := by
    exact orderOf_units (y := Units.map
      (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom
      (SemiprimeCentreFreeCover.projectedUnit g B))
  have hQ : orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      (SemiprimeCentreFreeCover.projectedUnit g B : ZMod (p*q))) =
      orderOf (Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom
        (SemiprimeCentreFreeCover.projectedUnit g B)) := by
    exact orderOf_units (y := Units.map
      (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom
      (SemiprimeCentreFreeCover.projectedUnit g B))
  rw [hP, hQ]
  constructor <;> nlinarith [hh.1, hh.2]

/-- A public inverse for x times the target derivative recovers a CRT
index. Its defining equation is checked before the inverse is used. -/
def decodedIndex {R : Type*} [CommRing R] (alpha x : R) (L : ℕ) (denom : Rˣ) : R :=
  -((denom⁻¹ : Rˣ) : R)*baseDerivative alpha x L

/-- The decoded scalar reduces to the literal exponent index at every
simple local root, retaining its orientation between the hidden primes. -/
theorem decodedIndex_map_root {R F : Type*} [CommRing R] [CommRing F]
    (f : R →+* F) (alpha x : R) (L : ℕ) (denom : Rˣ)
    (hdenom : (denom : R)=x*targetDerivative alpha x L)
    {k : ℕ} (hk : k<L) (hroot : f x=(f alpha)^k) :
    f (decodedIndex alpha x L denom)=(k : F) := by
  have hE : f (baseDerivative alpha x L)=
      -(k : F)*f x*f (targetDerivative alpha x L) := by
    rw [baseDerivative_map, targetDerivative_map, hroot]
    exact baseDerivative_at_root (f alpha) hk
  have hd : f (denom : R)=f x*f (targetDerivative alpha x L) := by
    rw [hdenom, map_mul]
  have hinv : f ((denom⁻¹ : Rˣ) : R)*f (denom : R)=1 := by
    rw [← map_mul]
    simp
  unfold decodedIndex
  rw [map_mul, map_neg, hE]
  calc
    -f ((denom⁻¹ : Rˣ) : R)*(-(k : F)*f x*f (targetDerivative alpha x L)) =
        (k : F)*(f ((denom⁻¹ : Rˣ) : R)*f (denom : R)) := by rw [hd]; ring
    _ = (k : F) := by rw [hinv, mul_one]

/-- Different short indices give a proper factor of the original
modulus. The scalar difference now has ordinary integer targets. -/
theorem distinct_index_gcd {p q L k l : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hk : k<L) (hl : l<L) (hLq : L ≤ q) (hkl : k ≠ l)
    (s : ZMod (p*q))
    (hP : ZMod.castHom (dvd_mul_right p q) (ZMod p) s=(k : ZMod p))
    (hQ : ZMod.castHom (dvd_mul_left q p) (ZMod q) s=(l : ZMod q)) :
    (p*q).gcd (s-(k : ZMod (p*q))).val=p := by
  apply SemiprimeCentreFreeCover.separating_residue_gcd hp hq
  · rw [map_sub, map_natCast, hP, sub_self]
  · rw [map_sub, map_natCast, hQ]
    apply sub_ne_zero.mpr
    intro he
    have hh := congrArg ZMod.val he
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (hk.trans_le hLq),
      Nat.mod_eq_of_lt (hl.trans_le hLq)] at hh
    exact hkl hh.symm

/-- Ordinary integer roots for the final short-index batch. -/
def indexRoots (N b : ℕ) : List (ZMod N) :=
  (List.range b).map (fun i => ((i+1 : ℕ) : ZMod N))

/-- Public translated integer points cover b² possible short indices. -/
def indexTargets {N : ℕ} (s : ZMod N) (b : ℕ) : List (ZMod N) :=
  (List.range b).map (fun j => s+1-((j*b : ℕ) : ZMod N))

/-- Complete existing shared-root deflation recovers an index difference. -/
noncomputable def recoverIndex {N : ℕ} (s : ZMod N) (b : ℕ) : Option ℕ :=
  SemiprimeCartesianCompletion.recoverResidueBatch (indexRoots N b).toFinset
    (indexTargets s b)

/-- At most b roots and b points are constructed by this final stage. -/
theorem index_input_lengths {N : ℕ} (s : ZMod N) (b : ℕ) :
    (indexRoots N b).length=b ∧ (indexTargets s b).length=b := by
  simp [indexRoots, indexTargets]

/-- The existing complete shared-root recovery specification charges at
most 2b GCD queries for the index stage, including saturated columns.
Constructing and evaluating its polynomials remains a separate cost. -/
theorem index_recovery_gcd_bound {N : ℕ} (s : ZMod N) (b : ℕ) :
    SemiprimeCartesianCompletion.recoveryGcdCount N
      (fun i => SemiprimeCartesianCompletion.residueLeaves (indexRoots N b).toFinset
        (i : ZMod N))
      (SemiprimeCartesianCompletion.evaluatedColumns (indexRoots N b).toFinset
        (indexTargets s b)) ≤ 2*b := by
  simpa only [indexRoots, indexTargets, List.length_map, List.length_range, two_mul]
    using SemiprimeCartesianCompletion.recoverResidueList_gcd_bound
      (indexRoots N b) (indexTargets s b)

/-- A proper difference against any covered short integer is sufficient
for recovery; global aliases at other points remain harmless. -/
theorem recoverIndex_succeeds {N b k : ℕ} [NeZero N] (s : ZMod N)
    (hk : k<b^2)
    (hproper : SemiprimeGroupSelection.ProperDivisor N
      (N.gcd (s-(k : ZMod N)).val)) :
    ∃ d, recoverIndex s b=some d := by
  have hb : 0 < b := by nlinarith
  let j := k/b
  let i := k%b
  have hj : j<b := by
    apply (Nat.div_lt_iff_lt_mul hb).mpr
    simpa [pow_two] using hk
  have hi : i<b := Nat.mod_lt _ hb
  have he : j*b+i=k := by
    simpa [j, i, Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div k b
  have hx : ((i+1 : ℕ) : ZMod N) ∈ indexRoots N b :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  have ht : s+1-((j*b : ℕ) : ZMod N) ∈ indexTargets s b :=
    List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  apply SemiprimeCartesianCompletion.recoverResidueList_succeeds_of_proper_pair hx ht
  have hres : s+1-((j*b : ℕ) : ZMod N)-((i+1 : ℕ) : ZMod N)=s-(k : ZMod N) := by
    rw [← he]
    push_cast
    ring
  rw [hres]
  exact hproper

/-- Three exact scalars recover a saturated interval row whose two
simple local roots have different indices. No local index is an input
to decodedIndex or recoverIndex. -/
theorem decodedIndex_recovers_distinct_roots {p q L b k l : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hk : k<L) (hl : l<L)
    (hLq : L ≤ q) (hcover : L ≤ b^2) (hkl : k ≠ l)
    (alpha x : ZMod (p*q)) (denom : (ZMod (p*q))ˣ)
    (hdenom : (denom : ZMod (p*q))=x*targetDerivative alpha x L)
    (hP : ZMod.castHom (dvd_mul_right p q) (ZMod p) x=
      (ZMod.castHom (dvd_mul_right p q) (ZMod p) alpha)^k)
    (hQ : ZMod.castHom (dvd_mul_left q p) (ZMod q) x=
      (ZMod.castHom (dvd_mul_left q p) (ZMod q) alpha)^l) :
    ∃ d, recoverIndex (decodedIndex alpha x L denom) b=some d := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  have hDP := decodedIndex_map_root
    (ZMod.castHom (dvd_mul_right p q) (ZMod p)) alpha x L denom hdenom hk hP
  have hDQ := decodedIndex_map_root
    (ZMod.castHom (dvd_mul_left q p) (ZMod q)) alpha x L denom hdenom hl hQ
  apply recoverIndex_succeeds _ (hk.trans_le hcover)
  rw [distinct_index_gcd hp hq hk hl hLq hkl _ hDP hDQ]
  exact ⟨hp.one_lt, by have hh := hq.one_lt; nlinarith [hp.pos], dvd_mul_right p q⟩

/-- A proper original GCD certifies a root in precisely one prime field. -/
theorem prime_reductions_of_gcd {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (z : ZMod (p*q)) (hz : (p*q).gcd z.val=p) :
    ZMod.castHom (dvd_mul_right p q) (ZMod p) z=0 ∧
    ZMod.castHom (dvd_mul_left q p) (ZMod q) z ≠ 0 := by
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  constructor
  · rw [← SemiprimeCentreFreeCover.castHom_val (dvd_mul_right p q)]
    apply (ZMod.natCast_eq_zero_iff _ _).mpr
    simpa only [hz] using Nat.gcd_dvd_right (p*q) z.val
  · intro he
    have hqv : q ∣ z.val := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      rw [SemiprimeCentreFreeCover.castHom_val (dvd_mul_left q p), he]
    have hd : q ∣ p := hz ▸ Nat.dvd_gcd (dvd_mul_left q p) hqv
    have hh := Nat.le_of_dvd hp.pos hd
    omega

/-- For distinct primes, two zero reductions certify zero in the original
ring. This is used before decoding a saturated detector. -/
theorem zero_of_prime_reductions {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (z : ZMod (p*q))
    (hP : ZMod.castHom (dvd_mul_right p q) (ZMod p) z=0)
    (hQ : ZMod.castHom (dvd_mul_left q p) (ZMod q) z=0) : z=0 := by
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  have hpv : p ∣ z.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [SemiprimeCentreFreeCover.castHom_val (dvd_mul_right p q), hP]
  have hqv : q ∣ z.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [SemiprimeCentreFreeCover.castHom_val (dvd_mul_left q p), hQ]
  have hd := ((Nat.coprime_primes hp hq).mpr hpq).mul_dvd_of_dvd_of_dvd hpv hqv
  have hh := (ZMod.natCast_eq_zero_iff z.val (p*q)).mpr hd
  simpa only [ZMod.natCast_zmod_val] using hh

/-- A local unit's period is strictly smaller than its prime modulus. -/
theorem local_unit_period_lt_prime {N p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (alpha : (ZMod N)ˣ) :
    orderOf (ZMod.castHom hpN (ZMod p) (alpha : ZMod N)) < p := by
  let : Fact p.Prime := ⟨hp⟩
  have hne : ZMod.castHom hpN (ZMod p) (alpha : ZMod N) ≠ 0 :=
    (Units.map (ZMod.castHom hpN (ZMod p)).toMonoidHom alpha).ne_zero
  have hd := ZMod.orderOf_dvd_card_sub_one hne
  have hh := Nat.le_of_dvd (show 0 < p-1 by have ht := hp.one_lt; omega) hd
  have ht := hp.one_lt
  omega

/-- A proper original hit remains recoverable when the complete interval
product saturates. The denominator unit is constructed from proved simple
roots; its invertibility and the other local index are not assumptions. -/
theorem saturated_proper_hit_recovers {p q L b k : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (alpha x : (ZMod (p*q))ˣ) (hk : k<L) (hcover : L ≤ b^2)
    (hLP : L ≤ orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      (alpha : ZMod (p*q))))
    (hLQ : L ≤ orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      (alpha : ZMod (p*q))))
    (hhit : (p*q).gcd ((alpha : ZMod (p*q))^k-(x : ZMod (p*q))).val=p)
    (hzero : intervalProduct (alpha : ZMod (p*q)) (x : ZMod (p*q)) L=0) :
    ∃ denom : (ZMod (p*q))ˣ,
      (denom : ZMod (p*q))=(x : ZMod (p*q))*
        targetDerivative (alpha : ZMod (p*q)) (x : ZMod (p*q)) L ∧
      ∃ d, recoverIndex (decodedIndex (alpha : ZMod (p*q))
        (x : ZMod (p*q)) L denom) b=some d := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  have hunit := x.isUnit.mul
    (saturated_targetDerivative_isUnit hp hq _ _ hLP hLQ hzero)
  have hpr := prime_reductions_of_gcd hp hq hpq _ hhit
  simp only [map_sub, map_pow, sub_eq_zero] at hpr
  have hz := congrArg (ZMod.castHom (dvd_mul_left q p) (ZMod q)) hzero
  rw [intervalProduct_map, map_zero, intervalProduct_zero_iff] at hz
  obtain ⟨l, hl, hQ⟩ := hz
  have hkl : k ≠ l := by
    intro he
    rw [← he] at hQ
    exact hpr.2 (sub_eq_zero.mpr hQ.symm)
  refine ⟨hunit.unit, hunit.unit_spec, ?_⟩
  apply decodedIndex_recovers_distinct_roots hp hq hk hl
    (hLQ.trans (local_unit_period_lt_prime hq (dvd_mul_left q p) alpha).le)
    hcover hkl _ _ hunit.unit hunit.unit_spec hpr.1.symm hQ

/-- A row is read through its original product first, then through the
proved unit-denominator index channel if that product is saturated. -/
noncomputable def recoverInterval {N : ℕ} (alpha x : (ZMod N)ˣ) (L b : ℕ) : Option ℕ := by
  classical
  exact
  let P := intervalProduct (alpha : ZMod N) (x : ZMod N) L
  let d := N.gcd P.val
  if 1 < d ∧ d < N then some d
  else if P=0 then
    if h : IsUnit ((x : ZMod N)*targetDerivative (alpha : ZMod N) (x : ZMod N) L) then
      recoverIndex (decodedIndex (alpha : ZMod N) (x : ZMod N) L h.unit) b
    else none
  else none

/-- Every returned factor is proper, including those recovered after a
saturated product. -/
theorem recoverInterval_sound {N L b d : ℕ} (alpha x : (ZMod N)ˣ)
    (h : recoverInterval alpha x L b=some d) :
    SemiprimeGroupSelection.ProperDivisor N d := by
  unfold recoverInterval at h
  dsimp only at h
  split_ifs at h with hp _ _
  · have hd := Option.some.inj h
    subst d
    exact ⟨hp.1, hp.2, Nat.gcd_dvd_left _ _⟩
  · exact SemiprimeCartesianCompletion.recoverResidueBatch_sound h

/-- On the simple-root branch, the three public row scalars preserve
every proper hit in the original interval. No full row-target matrix is
an input to the recovery function. -/
theorem recoverInterval_succeeds_of_proper_hit {p q L b k : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (alpha x : (ZMod (p*q))ˣ) (hk : k<L) (hcover : L ≤ b^2)
    (hLP : L ≤ orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      (alpha : ZMod (p*q))))
    (hLQ : L ≤ orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      (alpha : ZMod (p*q))))
    (hhit : (p*q).gcd ((alpha : ZMod (p*q))^k-(x : ZMod (p*q))).val=p) :
    ∃ d, recoverInterval alpha x L b=some d := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  have hpr := prime_reductions_of_gcd hp hq hpq _ hhit
  simp only [map_sub, map_pow, sub_eq_zero] at hpr
  have hzP : ZMod.castHom (dvd_mul_right p q) (ZMod p)
      (intervalProduct (alpha : ZMod (p*q)) (x : ZMod (p*q)) L)=0 := by
    rw [intervalProduct_map, intervalProduct_zero_iff]
    exact ⟨k, hk, hpr.1.symm⟩
  by_cases hz : intervalProduct (alpha : ZMod (p*q)) (x : ZMod (p*q)) L=0
  · obtain ⟨denom, hdenom, hd⟩ :=
      saturated_proper_hit_recovers hp hq hpq alpha x hk hcover hLP hLQ hhit hz
    have hu : IsUnit ((x : ZMod (p*q))*
        targetDerivative (alpha : ZMod (p*q)) (x : ZMod (p*q)) L) :=
      hdenom ▸ denom.isUnit
    have he : hu.unit=denom := by
      apply Units.ext
      exact hu.unit_spec.trans hdenom.symm
    obtain ⟨d, hd⟩ := hd
    refine ⟨d, ?_⟩
    simp only [recoverInterval, hz, ZMod.val_zero, Nat.gcd_zero_right]
    rw [if_neg (by omega)]
    simp only [ite_true, dif_pos hu, he]
    exact hd
  · have hzQ : ZMod.castHom (dvd_mul_left q p) (ZMod q)
        (intervalProduct (alpha : ZMod (p*q)) (x : ZMod (p*q)) L) ≠ 0 := by
      intro he
      exact hz (zero_of_prime_reductions hp hq hpq.ne _ hzP he)
    have hg := SemiprimeCentreFreeCover.separating_residue_gcd hp hq _ hzP hzQ
    refine ⟨p, ?_⟩
    unfold recoverInterval
    dsimp only
    rw [hg, if_pos]
    exact ⟨hp.one_lt, by have hh := hq.one_lt; nlinarith [hp.pos]⟩

/-- After the public prefix and short-period certificates, at least one
of the B centre-free rows is recoverable through its three scalars. The
constructor receives neither a hidden prime nor its exponent index.
This theorem proves recovery, not a bound on the total row-search cost. -/
theorem exists_recoverable_projected_row {p q B b : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hB : 0 < B) (hbudget : p*q ≤ B^6)
    (hprefix : (p*q).gcd (SemiprimeGroupCoverage.prefixProduct B)=1)
    (hcover : 3*B^2+1 ≤ b^2) (g : (ZMod (p*q))ˣ)
    (hclear : (p*q).gcd ((SemiprimeCentreFreeCover.projectedUnit g B : ZMod (p*q))-1).val=1)
    (hnone : SemiprimeCentreFreeCover.recoverShort
      (SemiprimeCentreFreeCover.projectedUnit g B) (2*B+1)=none) :
    ∃ a : ℕ, 0 < a ∧ a ≤ B ∧
      ∃ d, recoverInterval (SemiprimeCentreFreeCover.projectedUnit g B)
        ((SemiprimeCentreFreeCover.projectedUnit g B)^(a*(p*q)+B^2))
        (3*B^2+1) b=some d := by
  have hlong := SemiprimeCentreFreeCover.failed_projected_short_forces_long hp hq g
    (by omega) hclear hnone
  obtain ⟨a, k, ha, haB, hk, hhit⟩ :=
    SemiprimeCentreFreeCover.exists_projected_proper_hit hp hq hpq hB hbudget hprefix g
      (by nlinarith [hlong.1]) (by nlinarith [hlong.2])
  have hperiods := projected_interval_periods_long hp hq hB g hclear hnone
  refine ⟨a, ha, haB, ?_⟩
  apply recoverInterval_succeeds_of_proper_hit hp hq hpq _ _
    (by omega : k < 3*B^2+1) hcover hperiods.1 hperiods.2
  simpa only [Units.val_pow_eq_pow_val] using hhit

/-- A shared original root produces its literal common index, making
the distinction from two different prime-field roots explicit. -/
theorem decodedIndex_at_global_root {R : Type*} [CommRing R] (alpha : R)
    {L k : ℕ} (hk : k<L) (denom : Rˣ)
    (hdenom : (denom : R)=alpha^k*targetDerivative alpha (alpha^k) L) :
    decodedIndex alpha (alpha^k) L denom=(k : R) := by
  exact decodedIndex_map_root (RingHom.id R) alpha (alpha^k) L denom hdenom hk rfl

/-- Two bounded natural representatives of one prime-field residue are
equal. This permits the public common-index test without private advice. -/
theorem index_eq_of_reduction {N p k : ℕ} [NeZero N] (hpN : p ∣ N)
    (s : ZMod N) (hs : s.val<p) (hk : k<p)
    (he : ZMod.castHom hpN (ZMod p) s=(k : ZMod p)) : s.val=k := by
  rw [← SemiprimeCentreFreeCover.castHom_val hpN] at he
  have hh := congrArg ZMod.val he
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hk] using hh

/-- On the publicly certified simple-root branch, the decoded scalar
lies in the short interval exactly when both fields share one original
root. Skipping this case cannot discard a separating factor hit. -/
theorem decodedIndex_small_iff_shared_root {p q L : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (alpha x : (ZMod (p*q))ˣ)
    (hLP : L ≤ orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      (alpha : ZMod (p*q))))
    (hLQ : L ≤ orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      (alpha : ZMod (p*q))))
    (hzero : intervalProduct (alpha : ZMod (p*q)) (x : ZMod (p*q)) L=0)
    (denom : (ZMod (p*q))ˣ)
    (hdenom : (denom : ZMod (p*q))=(x : ZMod (p*q))*
      targetDerivative (alpha : ZMod (p*q)) (x : ZMod (p*q)) L) :
    (decodedIndex (alpha : ZMod (p*q)) (x : ZMod (p*q)) L denom).val<L ↔
      ∃ k<L, (x : ZMod (p*q))=(alpha : ZMod (p*q))^k := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  have hLp : L<p := hLP.trans_lt (local_unit_period_lt_prime hp (dvd_mul_right p q) alpha)
  have hLq : L<q := hLQ.trans_lt (local_unit_period_lt_prime hq (dvd_mul_left q p) alpha)
  constructor
  · intro hs
    have hzP := congrArg (ZMod.castHom (dvd_mul_right p q) (ZMod p)) hzero
    have hzQ := congrArg (ZMod.castHom (dvd_mul_left q p) (ZMod q)) hzero
    rw [intervalProduct_map, map_zero, intervalProduct_zero_iff] at hzP hzQ
    obtain ⟨k, hk, hP⟩ := hzP
    obtain ⟨l, hl, hQ⟩ := hzQ
    have hsk := index_eq_of_reduction (dvd_mul_right p q) _
      (hs.trans hLp) (hk.trans hLp)
      (decodedIndex_map_root (ZMod.castHom (dvd_mul_right p q) (ZMod p))
        _ _ _ denom hdenom hk hP)
    have hsl := index_eq_of_reduction (dvd_mul_left q p) _
      (hs.trans hLq) (hl.trans hLq)
      (decodedIndex_map_root (ZMod.castHom (dvd_mul_left q p) (ZMod q))
        _ _ _ denom hdenom hl hQ)
    refine ⟨_, hs, sub_eq_zero.mp (zero_of_prime_reductions hp hq hpq.ne _ ?_ ?_)⟩
    · rw [map_sub, map_pow, hsk, hP, sub_self]
    · rw [map_sub, map_pow, hsl, hQ, sub_self]
  · rintro ⟨k, hk, hroot⟩
    have hd : (denom : ZMod (p*q))=(alpha : ZMod (p*q))^k*
        targetDerivative (alpha : ZMod (p*q)) ((alpha : ZMod (p*q))^k) L := by
      simpa only [hroot] using hdenom
    have hkn : k<p*q := by
      have hkp := hk.trans hLp
      have hh := hq.one_lt
      nlinarith [hp.pos]
    rw [hroot, decodedIndex_at_global_root _ hk denom hd, ZMod.val_natCast,
      Nat.mod_eq_of_lt hkn]
    exact hk

/-- Two prime-field reductions identify one CRT residue in the original
semiprime ring. No executable Chinese-remainder computation is trusted. -/
theorem eq_of_prime_reductions {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (z w : ZMod (p*q))
    (hP : ZMod.castHom (dvd_mul_right p q) (ZMod p) z=
      ZMod.castHom (dvd_mul_right p q) (ZMod p) w)
    (hQ : ZMod.castHom (dvd_mul_left q p) (ZMod q) z=
      ZMod.castHom (dvd_mul_left q p) (ZMod q) w) : z=w := by
  apply sub_eq_zero.mp
  apply zero_of_prime_reductions hp hq hpq
  · rw [map_sub, hP, sub_self]
  · rw [map_sub, hQ, sub_self]

set_option maxRecDepth 32768 in
/-- Exact prime-field roots and index arithmetic for the saturated row.
This checks the original public target rather than supplying local indices
as inputs to the decoder. -/
theorem control_saturated_local_roots :
    Nat.Prime 44963 ∧ Nat.Prime 62347 ∧
    (387888406 : ZMod 44963)=(1823692905 : ZMod 44963)^2639 ∧
    (387888406 : ZMod 62347)=(1823692905 : ZMod 62347)^4067 ∧
    (1001733316 : ZMod 44963)=(2639 : ZMod 44963) ∧
    (1001733316 : ZMod 62347)=(4067 : ZMod 62347) ∧
    Nat.gcd 2803308161 (1001733316-2639)=44963 ∧
    Nat.gcd 2803308161 (1001733316-4067)=62347 := by
  norm_num
  reduce_mod_char
  norm_num

/-- The original control interval product is zero over the entire
semiprime, while its target derivative is a unit. Both facts are proved
from distinct local roots and checked periods, without enumerating the
4,333-factor product in Lean. -/
theorem control_saturated_detector :
    intervalProduct (1823692905 : ZMod (44963*62347))
      (387888406 : ZMod (44963*62347)) 4333=0 ∧
    IsUnit (targetDerivative (1823692905 : ZMod (44963*62347))
      (387888406 : ZMod (44963*62347)) 4333) := by
  obtain ⟨hp, hq, hrootP, hrootQ, _⟩ := control_saturated_local_roots
  let : Fact (Nat.Prime 44963) := ⟨hp⟩
  let : Fact (Nat.Prime 62347) := ⟨hq⟩
  have hP : ZMod.castHom (dvd_mul_right 44963 62347) (ZMod 44963)
      (intervalProduct (1823692905 : ZMod (44963*62347))
        (387888406 : ZMod (44963*62347)) 4333)=0 := by
    rw [intervalProduct_map, intervalProduct_zero_iff]
    refine ⟨2639, by norm_num, ?_⟩
    simpa only [map_ofNat] using hrootP
  have hQ : ZMod.castHom (dvd_mul_left 62347 44963) (ZMod 62347)
      (intervalProduct (1823692905 : ZMod (44963*62347))
        (387888406 : ZMod (44963*62347)) 4333)=0 := by
    rw [intervalProduct_map, intervalProduct_zero_iff]
    refine ⟨4067, by norm_num, ?_⟩
    simpa only [map_ofNat] using hrootQ
  have hz := zero_of_prime_reductions hp hq (by norm_num) _ hP hQ
  refine ⟨hz, saturated_targetDerivative_isUnit hp hq _ _ ?_ ?_ hz⟩
  · simp only [map_ofNat, SemiprimeCentreFreeCover.control_long_local_orders.1]
    norm_num
  · simp only [map_ofNat, SemiprimeCentreFreeCover.control_long_local_orders.2.1]
    norm_num

/-- Every checked public denominator for the saturated control decodes
the same explicit CRT index. The result follows from the generic jet
identities, not numerical derivative values supplied by the probe. -/
theorem control_decodedIndex (denom : (ZMod (44963*62347))ˣ)
    (hdenom : (denom : ZMod (44963*62347))=
      (387888406 : ZMod (44963*62347))*
        targetDerivative (1823692905 : ZMod (44963*62347))
          (387888406 : ZMod (44963*62347)) 4333) :
    decodedIndex (1823692905 : ZMod (44963*62347))
      (387888406 : ZMod (44963*62347)) 4333 denom=1001733316 := by
  obtain ⟨hp, hq, hrootP, hrootQ, hindexP, hindexQ, _⟩ := control_saturated_local_roots
  apply eq_of_prime_reductions hp hq (by norm_num)
  · rw [decodedIndex_map_root
      (ZMod.castHom (dvd_mul_right 44963 62347) (ZMod 44963))
      _ _ _ denom hdenom (by norm_num : 2639 < 4333)
      (by simpa only [map_ofNat] using hrootP), map_ofNat, hindexP]
    norm_num
  · rw [decodedIndex_map_root
      (ZMod.castHom (dvd_mul_left 62347 44963) (ZMod 62347))
      _ _ _ denom hdenom (by norm_num : 4067 < 4333)
      (by simpa only [map_ofNat] using hrootQ), map_ofNat, hindexQ]
    norm_num

/-- The saturated control has a public denominator and a recovered
proper factor using only 66 integer roots and 66 integer points. -/
theorem control_saturated_recovery :
    ∃ denom : (ZMod (44963*62347))ˣ,
      (denom : ZMod (44963*62347))=
        (387888406 : ZMod (44963*62347))*
          targetDerivative (1823692905 : ZMod (44963*62347))
            (387888406 : ZMod (44963*62347)) 4333 ∧
      decodedIndex (1823692905 : ZMod (44963*62347))
        (387888406 : ZMod (44963*62347)) 4333 denom=1001733316 ∧
      ∃ d, recoverIndex (decodedIndex (1823692905 : ZMod (44963*62347))
        (387888406 : ZMod (44963*62347)) 4333 denom) 66=some d := by
  obtain ⟨hp, hq, _, _, hindexP, hindexQ, _⟩ := control_saturated_local_roots
  let : NeZero (44963*62347) := ⟨by norm_num⟩
  have hx : IsUnit (387888406 : ZMod (44963*62347)) := by
    change IsUnit ((387888406 : ℕ) : ZMod (44963*62347))
    rw [ZMod.isUnit_iff_coprime]
    norm_num [Nat.coprime_iff_gcd_eq_one]
  have hu := hx.mul control_saturated_detector.2
  have hs := control_decodedIndex hu.unit hu.unit_spec
  refine ⟨hu.unit, hu.unit_spec, hs, ?_⟩
  rw [hs]
  apply recoverIndex_succeeds _ (by norm_num : 2639 < (66 : ℕ)^2)
  rw [distinct_index_gcd hp hq (by norm_num : 2639 < 4333)
    (by norm_num : 4067 < 4333) (by norm_num : 4333 ≤ 62347)
    (by norm_num : 2639 ≠ 4067) (1001733316 : ZMod (44963*62347))
    (by simpa only [map_ofNat, Nat.cast_ofNat] using hindexP)
    (by simpa only [map_ofNat, Nat.cast_ofNat] using hindexQ)]
  exact ⟨hp.one_lt, by norm_num, dvd_mul_right 44963 62347⟩

end RiemannGaussian.SemiprimeIntervalJet
