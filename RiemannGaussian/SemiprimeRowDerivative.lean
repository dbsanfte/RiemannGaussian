/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeEuclidRowFamily

/-!
# Detecting local collisions between retained quadratic rows

Globally deduplicated row values are the roots of one public polynomial.
Its derivative on those same roots is the exact off-diagonal difference
product. The existing deflated-column recovery therefore detects every
proper row-pair hit, including saturated derivative outputs, without an
explicit pair matrix. The original packets survive in the upstream list.

The recovery query bound is linear in the number of distinct roots. It
does not price row construction or polynomial arithmetic, nor prove that
this public family always has a local collision at sixth-root scale.
-/

namespace RiemannGaussian.SemiprimeRowDerivative

open scoped BigOperators
open Polynomial SemiprimeCartesianCompletion SemiprimeEuclidRowFamily

/-- The derivative of the polynomial of distinct whole-ring row values. -/
noncomputable def rowDerivative {R : Type*} [CommRing R]
    (S : Finset R) (t : R) : R := (rootPolynomial S id).derivative.eval t

/-- Evaluation at a retained root needs no division, field assumption,
or generic-position premise. Exactly the diagonal factor is removed. -/
theorem rowDerivative_eq_product {R : Type*} [CommRing R] [DecidableEq R]
    (S : Finset R) {t : R} (ht : t ∈ S) :
    rowDerivative S t = ∏ x ∈ S.erase t, (t-x) := by
  simpa [rowDerivative, rootPolynomial, SemiprimeRoughProjection.collisionPolynomial]
    using SemiprimeRoughProjection.derivative_strips_shared_root S ht

/-- The new row observable is the existing recoverable deflated column
on its own root axis, so the complete saturation proof is reused. -/
theorem rowDerivative_eq_deflated {R : Type*} [CommRing R] [DecidableEq R]
    (S : Finset R) {t : R} (ht : t ∈ S) :
    rowDerivative S t = deflatedColumn S t := by
  simp [deflatedColumn, ht, rowDerivative]

/-- A hidden field sees a zero precisely when two globally unequal rows
share its value. Whole-ring duplicate packets are not false positives. -/
theorem rowDerivative_map_zero_iff {R F : Type*} [CommRing R] [DecidableEq R]
    [CommRing F] [IsDomain F] (φ : R →+* F) (S : Finset R)
    {t : R} (ht : t ∈ S) :
    φ (rowDerivative S t)=0 ↔ ∃ x ∈ S, x ≠ t ∧ φ x=φ t := by
  rw [rowDerivative_eq_deflated S ht]
  exact deflatedColumn_map_zero_iff φ S t

/-- All detector targets are distinct retained row values. The original
packet list is kept by the caller; only this observable deduplicates it. -/
noncomputable def recoverRows {n : ℕ} (S : Finset (ZMod n)) : Option ℕ :=
  recoverResidueBatch S S.toList

theorem recoverRows_sound {n d : ℕ} {S : Finset (ZMod n)}
    (hs : recoverRows S=some d) : SemiprimeGroupSelection.ProperDivisor n d :=
  recoverResidueBatch_sound hs

/-- Any nonunit derivative recovers a proper factor, including full
modulus saturation. This holds for every positive modulus, also squares. -/
theorem recoverRows_succeeds_of_nonunit {n : ℕ} [NeZero n]
    {S : Finset (ZMod n)} {t : ZMod n} (ht : t ∈ S)
    (hh : n.gcd (rowDerivative S t).val ≠ 1) :
    ∃ d, recoverRows S=some d := by
  apply recoverResidueBatch_succeeds_of_nonunit (Finset.mem_toList.mpr ht)
  rwa [← rowDerivative_eq_deflated S ht]

/-- A proper pair cannot be lost to whole-modulus deduplication or to
another prime's collision in the same derivative output. -/
theorem recoverRows_succeeds_of_proper_pair {n : ℕ} [NeZero n]
    {S : Finset (ZMod n)} {x t : ZMod n} (hx : x ∈ S) (ht : t ∈ S)
    (hp : SemiprimeGroupSelection.ProperDivisor n (n.gcd (t-x).val)) :
    ∃ d, recoverRows S=some d :=
  recoverResidueBatch_succeeds_of_proper_pair hx (Finset.mem_toList.mpr ht) hp

private theorem recoverColumns_none_of_units (n : ℕ) (leaves : ℕ → List ℕ)
    (columns : List (ℕ×ℕ)) (hu : ∀ c ∈ columns, n.gcd c.2=1) :
    recoverColumns n leaves columns=none := by
  induction columns with
  | nil => rfl
  | cons c tail ih =>
    rcases c with ⟨t,v⟩
    rw [recoverColumns, if_pos (hu (t,v) (by simp))]
    exact ih (fun c hc => hu c (List.mem_cons_of_mem _ hc))

/-- Exhaustion is equivalent to all original off-diagonal differences
being units. This is a full hit-union identity, not a coverage premise. -/
theorem recoverRows_none_iff {n : ℕ} [NeZero n] (S : Finset (ZMod n)) :
    recoverRows S=none ↔ ∀ t ∈ S, ∀ x ∈ S, x ≠ t → n.gcd (t-x).val=1 := by
  constructor
  · intro hn t ht x hx hne
    by_contra hh
    have hm : (t-x).val ∈ residueLeaves S t :=
      List.mem_map.mpr ⟨x, Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨hne,hx⟩), rfl⟩
    have hg : n.gcd (rowDerivative S t).val ≠ 1 := by
      rw [rowDerivative_eq_deflated S ht, deflatedColumn_gcd_eq]
      intro hu
      exact hh (Nat.coprime_list_prod_right_iff.mp hu (t-x).val hm)
    obtain ⟨d,hd⟩ := recoverRows_succeeds_of_nonunit ht hg
    rw [hn] at hd
    contradiction
  · intro hall
    apply recoverColumns_none_of_units
    intro c hc
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hc
    rw [deflatedColumn_gcd_eq]
    apply Nat.coprime_list_prod_right_iff.mpr
    intro v hv
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
    have hh := Finset.mem_erase.mp (Finset.mem_toList.mp hx)
    exact hall t (Finset.mem_toList.mp ht) x hh.2 hh.1

/-- Over a semiprime the exact exhausted-detector criterion is local
injectivity in both actual prime fields, including when p=q. -/
theorem recoverRows_none_iff_prime_separation {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (S : Finset (ZMod (p*q))) :
    recoverRows S=none ↔ ∀ t ∈ S, ∀ x ∈ S, x ≠ t →
      ZMod.castHom (dvd_mul_right p q) (ZMod p) t ≠
        ZMod.castHom (dvd_mul_right p q) (ZMod p) x ∧
      ZMod.castHom (dvd_mul_left q p) (ZMod q) t ≠
        ZMod.castHom (dvd_mul_left q p) (ZMod q) x := by
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  rw [recoverRows_none_iff]
  constructor
  · intro hall t ht x hx hne
    have hu := (SemiprimeBulkNorm.gcd_one_iff_unit (t-x)).mp (hall t ht x hx hne)
    constructor
    · have hh := hu.map (ZMod.castHom (dvd_mul_right p q) (ZMod p))
      rw [map_sub] at hh
      exact sub_ne_zero.mp hh.ne_zero
    · have hh := hu.map (ZMod.castHom (dvd_mul_left q p) (ZMod q))
      rw [map_sub] at hh
      exact sub_ne_zero.mp hh.ne_zero
  · intro hall t ht x hx hne
    have hs := hall t ht x hx hne
    apply (SemiprimeBulkNorm.gcd_one_iff_unit (t-x)).mpr
    apply SemiprimeIntervalJet.isUnit_of_prime_reductions hp hq
    · simpa only [map_sub] using sub_ne_zero.mpr hs.1
    · simpa only [map_sub] using sub_ne_zero.mpr hs.2

/-- Recovery pays at most two GCD queries per distinct root: one per
derivative and one selected row scan. This is not a bit-clock theorem. -/
theorem recoverRows_gcd_bound {n : ℕ} (S : Finset (ZMod n)) :
    recoveryGcdCount n (fun i => residueLeaves S (i : ZMod n))
      (evaluatedColumns S S.toList) ≤ 2*S.card := by
  simpa only [Finset.length_toList, two_mul] using recoverResidueBatch_gcd_bound S S.toList

/-- Retained original centered packets produce public signed powers.
The field factors are absent from this constructor. -/
def publicRowValues {N : ℕ} (m : ℕ) (g : (ZMod N)ˣ) : List (ZMod N) :=
  (publicPackets N m).map fun w => ((g^packetExponent m w : (ZMod N)ˣ) : ZMod N)

/-- The polynomial fork deduplicates whole-modulus values, while
publicPackets remains available with every original row and shift. -/
def publicRoots {N : ℕ} (m : ℕ) (g : (ZMod N)ˣ) : Finset (ZMod N) :=
  (publicRowValues m g).toFinset

theorem publicRoots_mem_iff {N m : ℕ} (g : (ZMod N)ˣ) (t : ZMod N) :
    t ∈ publicRoots m g ↔ ∃ w ∈ publicPackets N m,
      ((g^packetExponent m w : (ZMod N)ˣ) : ZMod N)=t := by
  simp only [publicRoots, List.mem_toFinset, publicRowValues, List.mem_map]

/-- Every proper original packet-pair hit survives the compression. -/
theorem publicRows_succeeds_of_proper_pair {N m : ℕ} [NeZero N]
    (g : (ZMod N)ˣ) {x t : ZMod N} (hx : x ∈ publicRowValues m g)
    (ht : t ∈ publicRowValues m g)
    (hp : SemiprimeGroupSelection.ProperDivisor N (N.gcd (t-x).val)) :
    ∃ d, recoverRows (publicRoots m g)=some d :=
  recoverRows_succeeds_of_proper_pair (List.mem_toFinset.mpr hx) (List.mem_toFinset.mpr ht) hp

theorem publicRoots_card_le {N m : ℕ} (g : (ZMod N)ˣ) :
    (publicRoots m g).card ≤ (publicPackets N m).length := by
  simpa only [publicRoots, publicRowValues, List.length_map] using
    (publicRowValues m g).toFinset_card_le

/-- The explicit input axes consist of at most one root and one target
per packet. No quadratic pair list is part of this representation. -/
theorem publicRows_input_bound {N m : ℕ} (g : (ZMod N)ˣ) :
    2*(publicRoots m g).card ≤ 2*(publicPackets N m).length :=
  Nat.mul_le_mul_left 2 (publicRoots_card_le g)

/-- Membership can be checked at one public residue, without reducing
the entire family in the kernel. No private residue selector is assumed. -/
theorem publicExponent_mem_of_residue {N m j : ℕ} (hj : j<m) (hc : j.Coprime m)
    {e : ℤ} (he : e ∈ (residuePackets N m j).map (packetExponent m)) :
    e ∈ publicExponents N m := by
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp he
  apply List.mem_map.mpr
  refine ⟨w, ?_, rfl⟩
  apply List.mem_flatMap.mpr
  refine ⟨j,List.mem_range.mpr hj, ?_⟩
  change w ∈ (if j.Coprime m then residuePackets N m j else [])
  rwa [if_pos hc]

theorem publicRowValues_mem_of_exponent {N m : ℕ} (g : (ZMod N)ˣ) {e : ℤ}
    (he : e ∈ publicExponents N m) :
    ((g^e : (ZMod N)ˣ) : ZMod N) ∈ publicRowValues m g := by
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp he
  exact List.mem_map.mpr ⟨w,hw,rfl⟩

set_option maxRecDepth 32768 in
/-- Two literal packets belong to the complete public family that
previously had no collision with any baby index in [-269,269]. -/
theorem control_pair_exponents :
    (5548012844175291 : ℤ) ∈ publicExponents 369867514421371 269 ∧
    (13685097404436363 : ℤ) ∈ publicExponents 369867514421371 269 := by
  constructor
  · apply publicExponent_mem_of_residue (j:=44) (by norm_num) (by norm_num [Nat.Coprime])
    decide +kernel
  · apply publicExponent_mem_of_residue (j:=60) (by norm_num) (by norm_num [Nat.Coprime])
    decide +kernel

/-- Exact public modular powers, checked by kernel arithmetic. -/
theorem control_pair_values :
    ((controlBase^(5548012844175291 : ℤ) : (ZMod (14799739*24991489))ˣ) :
      ZMod (14799739*24991489))=82387083281361 ∧
    ((controlBase^(13685097404436363 : ℤ) : (ZMod (14799739*24991489))ˣ) :
      ZMod (14799739*24991489))=297936993962521 := by
  norm_num only [controlBase, zpow_ofNat, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
  constructor <;> reduce_mod_char

/-- These unequal whole-modulus roots have a proper original pair hit. -/
theorem control_pair_gcd :
    SemiprimeGroupSelection.ProperDivisor (14799739*24991489)
      ((14799739*24991489).gcd
        ((297936993962521-82387083281361 : ZMod (14799739*24991489))).val) := by
  norm_num [SemiprimeGroupSelection.ProperDivisor, ZMod.val_ofNat]

/-- The complete N-only public derivative detector recovers a proper
factor on the literal full-family short-window counterexample. The
private pair is a proof witness; it is not an input to recoverRows. -/
theorem control_derivative_recovers :
    ∃ d, recoverRows (publicRoots 269 controlBase)=some d ∧
      SemiprimeGroupSelection.ProperDivisor (14799739*24991489) d := by
  have hx := publicRowValues_mem_of_exponent controlBase control_pair_exponents.1
  have ht := publicRowValues_mem_of_exponent controlBase control_pair_exponents.2
  rw [control_pair_values.1] at hx
  rw [control_pair_values.2] at ht
  obtain ⟨d,hd⟩ := publicRows_succeeds_of_proper_pair controlBase hx ht control_pair_gcd
  exact ⟨d,hd,recoverRows_sound hd⟩

end RiemannGaussian.SemiprimeRowDerivative
