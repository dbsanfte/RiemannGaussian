/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeRowSpecificDetectorObstruction
import RiemannGaussian.SemiprimeSeedLinearStateObstruction

/-!
# Balanced original seed aggregation loses the proper-factor scalar

On a broad balanced range, the original true-residue index is short for
BOTH hidden primes. The full scalar product is therefore zero modulo the
semiprime for every public unit, without a fixed-state or recurrence premise.
The investigation journal gives an infinite actual long-base-2 family using
the published large-factor density, and a separate short-ratio acquisition
obstruction. Analytic density and infinitude are not Lean axioms here.
-/

namespace RiemannGaussian.SemiprimeBalancedAcquisitionObstruction

open scoped BigOperators
open SemiprimeDenseRowCoverage SemiprimeDenseRowCarries SemiprimeQuotientRows
open SemiprimeGlobalPhaseCancellation SemiprimeSeedSumAcquisition
open SemiprimeSeedFiniteTransfer SemiprimeSeedLinearStateObstruction
open SemiprimeIntervalJet SemiprimeLocalOrderRouting SemiprimeCentreFreeCover
open SemiprimeWrapIndexRecovery SemiprimeWideWrapCoverage

/-- Symmetric size bounds make the original true-residue index short without ordering the factors. -/
theorem balanced_seed_index_bounds {p q m : ℕ} (hm : 4≤m)
    (hp : m^2≤p) (hq : m^2≤q) (hpupper : 2*p≤3*m^3) (hqupper : 2*q≤3*m^3)
    {i : ℤ} (hi : (m : ℤ)^2*i=(seedRow (p*q) m (p%m)).a*p+
      (seedRow (p*q) m (p%m)).b*m-2*(seedRow (p*q) m (p%m)).a*(p%m : ℕ)+q) :
    0 ≤ i ∧ i ≤ (2*m^2+1 : ℕ) := by
  let a : ℤ := (seedRow (p*q) m (p%m)).a
  let b : ℤ := (seedRow (p*q) m (p%m)).b
  have ha0 : 0≤a := by change (0 : ℤ)≤representative (p*q) m (p%m) 1; positivity
  have ha1 : a≤m := by
    change (representative (p*q) m (p%m) 1 : ℤ)≤m
    exact_mod_cast (Nat.mod_lt _ (by omega : 0<m)).le
  have hb := abs_le.mp (denseRow_b_bound (N:=p*q) (m:=m) (j:=p%m) (t:=1) (by omega) false)
  change -(m : ℤ)≤b ∧ b≤m at hb
  have hmz : (4 : ℤ)≤m := by exact_mod_cast hm
  have hmsq : (0 : ℤ)<(m : ℤ)^2 := by positivity
  have hjm : ((p%m : ℕ) : ℤ)≤m-1 := by
    have hh := Nat.mod_lt p (by omega : 0<m)
    omega
  have hpz : (m : ℤ)^2≤p := by exact_mod_cast hp
  have hqz : (m : ℤ)^2≤q := by exact_mod_cast hq
  have hpup : 2*(p : ℤ)≤3*(m : ℤ)^3 := by exact_mod_cast hpupper
  have hqup : 2*(q : ℤ)≤3*(m : ℤ)^3 := by exact_mod_cast hqupper
  have hfactor : (0 : ℤ)≤(p : ℤ)-2*(p%m : ℕ) := by nlinarith only [hmz,hjm,hpz]
  have hapos := mul_nonneg ha0 hfactor
  have hblo := mul_le_mul_of_nonneg_right hb.1 (by omega : (0 : ℤ)≤m)
  have hbhi := mul_le_mul_of_nonneg_right hb.2 (by omega : (0 : ℤ)≤m)
  have hap : 2*a*p≤3*(m : ℤ)^4 := by
    calc
      2*a*p=a*(2*p) := by ring
      _≤a*(3*(m : ℤ)^3) := mul_le_mul_of_nonneg_left hpup ha0
      _≤(m : ℤ)*(3*(m : ℤ)^3) := mul_le_mul_of_nonneg_right ha1 (by positivity)
      _=3*(m : ℤ)^4 := by ring
  have haj := mul_nonneg ha0 (by positivity : (0 : ℤ)≤(p%m : ℕ))
  have hgrowth : 3*(m : ℤ)^3≤(m : ℤ)^4 := by
    nlinarith only [mul_nonneg (show (0 : ℤ)≤(m : ℤ)-3 by omega)
      (show (0 : ℤ)≤(m : ℤ)^3 by positivity)]
  change (m : ℤ)^2*i=a*p+b*m-2*a*(p%m : ℕ)+q at hi
  constructor
  · have hmul : (0 : ℤ)≤(m : ℤ)^2*i := by nlinarith only [hi,hapos,hblo,hqz]
    exact (mul_nonneg_iff_of_pos_left hmsq).mp hmul
  · have hmul : (m : ℤ)^2*i≤(m : ℤ)^2*(2*(m : ℤ)^2+1) := by
      nlinarith only [hi,hap,hbhi,haj,hqup,hgrowth]
    have he := le_of_mul_le_mul_left hmul hmsq
    exact_mod_cast he

/-- The literal original offset residual is forced for either balanced hidden factor. -/
theorem balanced_forced_seed_arithmetic {p q m : ℕ} (hp : 0<p) (hm : 4≤m)
    (hprefixp : m^2≤p) (hprefixq : m^2≤q)
    (hpupper : 2*p≤3*m^3) (hqupper : 2*q≤3*m^3) (hN : m.Coprime (p*q)) :
    ∃ r : ℕ, r≤2*m^2+1 ∧ r<seedLength m ∧
      ((p*q : ℕ) : ℤ)+seedOffset (p*q) m (p%m)-(m : ℤ)^2*r=
        ((p : ℤ)-1)*((q : ℤ)-(representative (p*q) m (p%m) 1 : ℤ)) := by
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  obtain ⟨I,hI,_⟩ := row_index_exists hp hN
    (denseRow_relation (N:=p*q) (j:=p%m) (t:=1) (by omega) hj false)
  have hden : (denseRow (p*q) m (p%m) 1 false).t=(1 : ℤ) := rfl
  rw [hden,one_mul] at hI
  change (m : ℤ)^2*I=(seedRow (p*q) m (p%m)).a*p+
    (seedRow (p*q) m (p%m)).b*m-2*(seedRow (p*q) m (p%m)).a*(p%m : ℕ)+q at hI
  have hbounds := balanced_seed_index_bounds hm hprefixp hprefixq hpupper hqupper hI
  let r := I.toNat
  have hrI : (r : ℤ)=I := Int.toNat_of_nonneg hbounds.1
  have hr : r≤2*m^2+1 := by omega
  refine ⟨r,hr,?_,?_⟩
  · have hl := (seedLength_bounds hm).1
    omega
  · unfold seedOffset
    rw [Nat.cast_mul,hrI]
    change (m : ℤ)^2*I=(representative (p*q) m (p%m) 1 : ℤ)*p+
      (seedRow (p*q) m (p%m)).b*m-
      2*(representative (p*q) m (p%m) 1 : ℤ)*(p%m : ℕ)+q at hI
    linear_combination -hI

/-- Fermat makes the short balanced index an original local hit for every public unit. -/
theorem balanced_forced_seed_prime_hit {p q m : ℕ} (hp : p.Prime) (hm : 4≤m)
    (hprefixp : m^2≤p) (hprefixq : m^2≤q)
    (hpupper : 2*p≤3*m^3) (hqupper : 2*q≤3*m^3) (hN : m.Coprime (p*q))
    (g : (ZMod (p*q))ˣ) :
    ∃ r : ℕ, r≤2*m^2+1 ∧ r<seedLength m ∧
      (progressionSeed g (p*q) m (p%m))∈progressionSeeds g (p*q) m ∧
      ZMod.castHom (dvd_mul_right p q) (ZMod p)
        ((progressionSeed g (p*q) m (p%m)).step : ZMod (p*q))=
      (ZMod.castHom (dvd_mul_right p q) (ZMod p)
        ((seedBase g m : (ZMod (p*q))ˣ) : ZMod (p*q)))^r := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨r,hrbound,hr,hres⟩ := balanced_forced_seed_arithmetic hp.pos hm
    hprefixp hprefixq hpupper hqupper hN
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  have hjpos : 0<p%m := by
    by_contra! hn
    have hz : p%m=0 := by omega
    simp only [hz,Nat.coprime_zero_left] at hj
    omega
  have hperiod : (leftUnit g)^((p : ℤ)-1)=1 := by
    simpa only [←zpow_natCast,Nat.cast_sub hp.one_le,Nat.cast_one] using
      ZMod.units_pow_card_sub_one_eq_one p (leftUnit g)
  have hsum : ((p*q : ℕ) : ℤ)+seedOffset (p*q) m (p%m)=
      (m : ℤ)^2*r+((p : ℤ)-1)*((q : ℤ)-(representative (p*q) m (p%m) 1 : ℤ)) := by
    linarith only [hres]
  have hu : leftUnit (progressionSeed g (p*q) m (p%m)).step=(leftUnit (seedBase g m))^r := by
    rw [seed_step_offset g (by omega) hj]
    simp only [leftUnit,map_zpow,seedBase,map_pow]
    change (leftUnit g)^(((p*q : ℕ) : ℤ)+seedOffset (p*q) m (p%m))=
      ((leftUnit g)^(m^2))^r
    rw [hsum,zpow_add]
    simp only [zpow_mul,hperiod,one_zpow,mul_one,←zpow_natCast,Nat.cast_pow]
  refine ⟨r,hrbound,hr,progressionSeed_mem g hjpos (Nat.mod_lt p (by omega)),?_⟩
  simpa [leftUnit,RingHom.toMonoidHom] using
    congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hu

/-- One forced original row makes the full aggregate zero in that hidden prime field. -/
theorem balanced_seedAggregate_left_zero {p q m : ℕ} (hp : p.Prime) (hm : 4≤m)
    (hprefixp : m^2≤p) (hprefixq : m^2≤q)
    (hpupper : 2*p≤3*m^3) (hqupper : 2*q≤3*m^3) (hN : m.Coprime (p*q))
    (g : (ZMod (p*q))ˣ) :
    ZMod.castHom (dvd_mul_right p q) (ZMod p) (seedAggregate g m 1)=0 := by
  classical
  obtain ⟨r,_,hr,_,hhit⟩ := balanced_forced_seed_prime_hit hp hm hprefixp hprefixq
    hpupper hqupper hN g
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  have hjpos : 0<p%m := by
    by_contra! hn
    have hz : p%m=0 := by omega
    simp only [hz,Nat.coprime_zero_left] at hj
    omega
  unfold seedAggregate SemiprimeQAggregate.rowAggregate
  rw [map_prod]
  apply Finset.prod_eq_zero (i:=p%m-1)
  · apply Finset.mem_range.mpr
    have hlt := Nat.mod_lt p (by omega : 0<m)
    omega
  · dsimp only
    rw [show p%m-1+1=p%m by omega,one_mul]
    rw [intervalProduct_map,hhit]
    unfold intervalProduct
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hr) (sub_self _)

/-- The local aggregate result respects either factorization of the same public modulus. -/
theorem balanced_seedAggregate_projection_zero {N p q m : ℕ} (hp : p.Prime) (hm : 4≤m)
    (hprefixp : m^2≤p) (hprefixq : m^2≤q)
    (hpupper : 2*p≤3*m^3) (hqupper : 2*q≤3*m^3) (hprod : N=p*q)
    (hN : m.Coprime N) (g : (ZMod N)ˣ) (hpN : p∣N) :
    ZMod.castHom hpN (ZMod p) (seedAggregate g m 1)=0 := by
  subst N
  exact balanced_seedAggregate_left_zero hp hm hprefixp hprefixq hpupper hqupper hN g

/-- The full original scalar norm is saturated on the balanced range, without linear-state premises. -/
theorem balanced_seedAggregate_zero {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (hm : 4≤m) (hprefixp : m^2≤p) (hprefixq : m^2≤q)
    (hpupper : 2*p≤3*m^3) (hqupper : 2*q≤3*m^3) (hN : m.Coprime (p*q))
    (g : (ZMod (p*q))ˣ) : seedAggregate g m 1=0 := by
  apply zero_of_prime_reductions hp hq hpq
  · exact balanced_seedAggregate_left_zero hp hm hprefixp hprefixq hpupper hqupper hN g
  · exact balanced_seedAggregate_projection_zero hq hm hprefixq hprefixp hqupper hpupper
      (Nat.mul_comm p q) hN g (dvd_mul_left q p)

/-- A public gcd of that full norm returns the modulus, regardless of acquisition cost. -/
theorem balanced_seedAggregate_gcd_eq_modulus {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (hm : 4≤m) (hprefixp : m^2≤p) (hprefixq : m^2≤q)
    (hpupper : 2*p≤3*m^3) (hqupper : 2*q≤3*m^3) (hN : m.Coprime (p*q))
    (g : (ZMod (p*q))ˣ) : (p*q).gcd (seedAggregate g m 1).val=p*q := by
  rw [balanced_seedAggregate_zero hp hq hpq hm hprefixp hprefixq hpupper hqupper hN g]
  simp only [ZMod.val_zero,Nat.gcd_zero_right]

/-- Proof-side cleared confluent Gram scalar; the second derivative is left arbitrary. -/
noncomputable def clearedGramDiagonal {R : Type*} [CommRing R]
    (alpha x : R) (L : ℕ) (second : R) : R :=
  (targetDerivative alpha x L)^2-intervalProduct alpha x L*second

/-- Clearing the Gram denominator makes every simple original root nonzero in its field. -/
theorem cleared_gram_at_short_root {R : Type*} [CommRing R] [IsDomain R]
    (alpha : R) {L r : ℕ} (hr : r<L) (hperiod : L≤orderOf alpha) (second : R) :
    intervalProduct alpha (alpha^r) L=0 ∧
      clearedGramDiagonal alpha (alpha^r) L second≠0 := by
  have hz : intervalProduct alpha (alpha^r) L=0 := by
    unfold intervalProduct
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hr) (sub_self _)
  refine ⟨hz,?_⟩
  unfold clearedGramDiagonal
  rw [hz,zero_mul,sub_zero]
  exact pow_ne_zero 2 (targetDerivative_at_root_ne_zero alpha hr hperiod)

/-- The cleared RH Gram mask loses the actual forced true-row hit on the public long branch. -/
theorem balanced_true_row_gram_mask_failure {p q m : ℕ} (hp : p.Prime) (hm : 4≤m)
    (hprefixp : m^2≤p) (hprefixq : m^2≤q)
    (hpupper : 2*p≤3*m^3) (hqupper : 2*q≤3*m^3) (hN : m.Coprime (p*q))
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    let f := ZMod.castHom (dvd_mul_right p q) (ZMod p)
    let alpha := f ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))
    let x := f ((progressionSeed (projectedUnit g m) (p*q) m (p%m)).step : ZMod (p*q))
    intervalProduct alpha x (seedLength m)=0 ∧
      ∀ second : ZMod p, clearedGramDiagonal alpha x (seedLength m) second≠0 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨r,_,hr,_,hhit⟩ := balanced_forced_seed_prime_hit hp hm hprefixp hprefixq
    hpupper hqupper hN (projectedUnit g m)
  dsimp only
  rw [hhit]
  have hperiod := (long_seed_interval_periods hm g hlong).1
  constructor
  · exact (cleared_gram_at_short_root _ hr hperiod (0 : ZMod p)).1
  · intro second
    exact (cleared_gram_at_short_root _ hr hperiod second).2

end RiemannGaussian.SemiprimeBalancedAcquisitionObstruction
