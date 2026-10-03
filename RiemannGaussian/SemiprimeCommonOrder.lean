/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeGeometricRows
import Mathlib.Data.Nat.Factors

/-!
# Checked large common orders recover factors without interval rows

A known modulus m dividing both p-1 and q-1 recovers the factors directly
when pq<m^3. Writing p=am+1 and q=bm+1 gives a+b<m; quotient and remainder
of (N-1)/m reveal ab and a+b, followed by one integer square root.
Public prime-divisor power checks certify the common local order.
For a raw-kernel unit, its exact global order already divides both local
group cardinalities. Retaining the sum's wrap label extends reconstruction:
after excluding prime factors at most B^2, a common modulus with m^2≥B^3
needs at most 2B scalar candidates when N≤B^6.
This does not assume that a fast large-order algorithm returns the order
or its factorization. Obtaining those data within the full target cost
and the residual search on other inputs remain open.
-/

namespace RiemannGaussian.SemiprimeCommonOrder

open SemiprimeGroupSelection

/-- Public square preprocessing handles repeated prime factors before
the distinct-prime raw-kernel transport is used. -/
def recoverSquare (N : ℕ) : Option ℕ :=
  if (Nat.sqrt N)^2=N then checkedSignal N (Nat.sqrt N) else none

theorem recoverSquare_sound {N d : ℕ} (hs : recoverSquare N=some d) :
    ProperDivisor N d := by
  unfold recoverSquare at hs
  split_ifs at hs with h
  exact checkedSignal_sound hs

theorem recoverSquare_semiprime_square {p : ℕ} (hp : p.Prime) :
    recoverSquare (p^2)=some p := by
  have hg : (p^2).gcd p=p := Nat.gcd_eq_right (by exact ⟨p, by ring⟩)
  have hproper : 1<p ∧ p<p^2 := ⟨hp.one_lt, by nlinarith [hp.one_lt]⟩
  simp only [recoverSquare, Nat.sqrt_eq', checkedSignal, hg, if_pos hproper, ite_true]

/-- The public quotient retains both coefficient channels. -/
def orderQuotient (N m : ℕ) : ℕ := (N-1)/m

/-- Remainder channel for the sum of the hidden progression indices. -/
def indexSum (N m : ℕ) : ℕ := orderQuotient N m % m

/-- Quotient channel for the product of the hidden progression indices. -/
def indexProduct (N m : ℕ) : ℕ := orderQuotient N m / m

/-- Exact quadratic reconstruction, followed by a separate checked GCD. -/
def commonCandidate (N m : ℕ) : ℕ :=
  m*((indexSum N m-Nat.sqrt (indexSum N m^2-4*indexProduct N m))/2)+1

/-- Every returned value is checked even if the proposed modulus or
quadratic data are invalid. No reference factor enters this routine. -/
def recoverCommon (N m : ℕ) : Option ℕ :=
  if 0<m then checkedSignal N (commonCandidate N m) else none

theorem recoverCommon_sound {N m d : ℕ} (hs : recoverCommon N m=some d) :
    ProperDivisor N d := by
  unfold recoverCommon at hs
  split_ifs at hs with h
  exact checkedSignal_sound hs

/-- A cubic modulus bound prevents the sum channel from wrapping.
Both positive index weights remain in the exact product relation. -/
theorem index_sum_lt_modulus {m a b : ℕ} (ha : 0<a) (hb : 0<b)
    (hN : (m*a+1)*(m*b+1)<m^3) : a+b<m := by
  have hab : a+b≤a*b+1 := by
    have hnonneg : 0≤((a : ℤ)-1)*((b : ℤ)-1) :=
      mul_nonneg (by omega) (by omega)
    exact_mod_cast (show (a : ℤ)+b≤(a : ℤ)*b+1 by nlinarith)
  by_contra hn
  have hsum : m≤a+b := by omega
  have hprod := Nat.mul_le_mul_left (m*m) (hsum.trans hab)
  have hlinear := Nat.mul_le_mul_left m hsum
  nlinarith

/-- The retained quotient is exactly sum plus modulus times product. -/
theorem orderQuotient_encoded {m a b : ℕ} (hm : 0<m) :
    orderQuotient ((m*a+1)*(m*b+1)) m=a+b+m*(a*b) := by
  have he : (m*a+1)*(m*b+1)=m*(a+b+m*(a*b))+1 := by ring
  unfold orderQuotient
  rw [he, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hm]

/-- The cubic condition discharges the sum's zero-wrap requirement. -/
theorem encoded_sum_product {m a b : ℕ} (hm : 0<m) (ha : 0<a) (hb : 0<b)
    (hN : (m*a+1)*(m*b+1)<m^3) :
    indexSum ((m*a+1)*(m*b+1)) m=a+b ∧
      indexProduct ((m*a+1)*(m*b+1)) m=a*b := by
  have hs := index_sum_lt_modulus ha hb hN
  simp [indexSum, indexProduct, orderQuotient_encoded hm,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs, Nat.add_mul_div_left _ _ hm,
    Nat.div_eq_of_lt hs, zero_add]

/-- The discriminant is a literal integer square, with no floating
approximation or negative subtraction silently discarded. -/
theorem index_discriminant_square {a b : ℕ} (hab : a≤b) :
    (a+b)^2-4*(a*b)=(b-a)^2 := by
  have he := Nat.sub_add_cancel hab
  have hle : 4*(a*b)≤(a+b)^2 := by nlinarith
  have hs := Nat.sub_add_cancel hle
  nlinarith

/-- Quotient, remainder and square root reconstruct the smaller
progression member exactly, before its public GCD is taken. -/
theorem commonCandidate_encoded {m a b : ℕ} (hm : 0<m) (ha : 0<a) (hb : 0<b)
    (hab : a≤b) (hN : (m*a+1)*(m*b+1)<m^3) :
    commonCandidate ((m*a+1)*(m*b+1)) m=m*a+1 := by
  obtain ⟨hs, hp⟩ := encoded_sum_product hm ha hb hN
  unfold commonCandidate
  rw [hs, hp, index_discriminant_square hab, Nat.sqrt_eq']
  have he : a+b-(b-a)=2*a := by omega
  rw [he, Nat.mul_div_cancel_left _ (by decide)]

/-- A positive common modulus supplies positive progression indices. -/
theorem common_modulus_indices {p q m : ℕ} (hp : 1<p) (hq : 1<q)
    (hm : 0<m) (hpq : p≤q) (hmp : m∣p-1) (hmq : m∣q-1) :
    ∃ a b : ℕ, 0<a ∧ 0<b ∧ a≤b ∧ p=m*a+1 ∧ q=m*b+1 := by
  obtain ⟨a, ha⟩ := hmp
  obtain ⟨b, hb⟩ := hmq
  have hpa : p=m*a+1 := by omega
  have hqb : q=m*b+1 := by omega
  have ha0 : 0<a := by
    by_contra hn
    have he : a=0 := by omega
    rw [he, Nat.mul_zero] at ha
    omega
  have hb0 : 0<b := by
    by_contra hn
    have he : b=0 := by omega
    rw [he, Nat.mul_zero] at hb
    omega
  have hab : a≤b := by nlinarith
  exact ⟨a, b, ha0, hb0, hab, hpa, hqb⟩

/-- Every semiprime with this actual common modulus is recovered by
the public reconstruction. Prime squares are included. -/
theorem recoverCommon_semiprime {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≤q) (hm : 0<m) (hmp : m∣p-1) (hmq : m∣q-1) (hN : p*q<m^3) :
    recoverCommon (p*q) m=some p := by
  obtain ⟨a, b, ha, hb, hab, hpa, hqb⟩ :=
    common_modulus_indices hp.one_lt hq.one_lt hm hpq hmp hmq
  have hc : commonCandidate (p*q) m=p := by
    rw [hpa, hqb]
    apply commonCandidate_encoded hm ha hb hab
    simpa only [hpa, hqb] using hN
  have hpN : p<p*q := by have hh := hq.one_lt; nlinarith [hp.pos]
  have hg : (p*q).gcd p=p := Nat.gcd_eq_right (dvd_mul_right p q)
  have hproper : 1<p ∧ p<p*q := ⟨hp.one_lt, hpN⟩
  rw [recoverCommon, if_pos hm, hc, checkedSignal, hg, if_pos hproper]

/-- Literal public power-divisor checks certify the local order at
each prime factor. The order value is derived, not hidden advice. -/
theorem local_order_of_public_checks {N p m : ℕ} [NeZero N]
    (hp : p.Prime) (hpN : p∣N) (g : (ZMod N)ˣ) (hm : 0<m) (hpow : g^m=1)
    (hclear : ∀ r, r.Prime → r∣m → N.gcd (((g^(m/r) : (ZMod N)ˣ) : ZMod N)-1).val=1) :
    orderOf (Units.map (ZMod.castHom hpN (ZMod p)).toMonoidHom g)=m := by
  let gp := Units.map (ZMod.castHom hpN (ZMod p)).toMonoidHom g
  have hlocal : gp^m=1 := by
    have he := congrArg (Units.map (ZMod.castHom hpN (ZMod p)).toMonoidHom) hpow
    simpa only [map_pow, map_one] using he
  apply orderOf_eq_of_pow_and_pow_div_prime hm hlocal
  intro r hr hrm he
  have hn := SemiprimeCentreFreeCover.clear_unit_component_order_ne_one hp hpN
    (g^(m/r)) (hclear r hr hrm)
  rw [map_pow] at hn
  exact hn (orderOf_eq_one_iff.mpr he)

/-- Common field cardinality divisibility follows from the public
checks; no prime is an input to the reconstruction algorithm. -/
theorem common_modulus_of_public_checks {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (g : (ZMod (p*q))ˣ) (hm : 0<m) (hpow : g^m=1)
    (hclear : ∀ r, r.Prime → r∣m →
      (p*q).gcd (((g^(m/r) : (ZMod (p*q))ˣ) : ZMod (p*q))-1).val=1) :
    m∣p-1 ∧ m∣q-1 := by
  let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  constructor
  · have he := local_order_of_public_checks hp (dvd_mul_right p q) g hm hpow hclear
    rw [← he]
    exact ZMod.orderOf_units_dvd_card_sub_one _
  · have he := local_order_of_public_checks hq (dvd_mul_left q p) g hm hpow hclear
    rw [← he]
    exact ZMod.orderOf_units_dvd_card_sub_one _

/-- A known sufficiently large common-order certificate recovers the
factor using only its public modulus, with no interval row construction. -/
theorem recoverCommon_of_public_checks {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≤q) (g : (ZMod (p*q))ˣ) (hm : 0<m) (hN : p*q<m^3) (hpow : g^m=1)
    (hclear : ∀ r, r.Prime → r∣m →
      (p*q).gcd (((g^(m/r) : (ZMod (p*q))ˣ) : ZMod (p*q))-1).val=1) :
    recoverCommon (p*q) m=some p := by
  obtain ⟨hmp, hmq⟩ := common_modulus_of_public_checks hp hq g hm hpow hclear
  exact recoverCommon_semiprime hp hq hpq hm hmp hmq hN

/-- In the raw N-1 kernel, both local orders divide the common field
cardinality part even when the two local orders differ. -/
theorem local_kernel_orders_dvd_common {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (g : (ZMod (p*q))ˣ) (hraw : g^(p*q-1)=1) :
    orderOf (Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom g) ∣
      (p-1).gcd (q-1) ∧
    orderOf (Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom g) ∣
      (p-1).gcd (q-1) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  constructor
  · have hpow := congrArg
      (Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom) hraw
    simp only [map_pow, map_one] at hpow
    have hd := Nat.dvd_gcd (ZMod.orderOf_units_dvd_card_sub_one _)
      (orderOf_dvd_of_pow_eq_one hpow)
    rwa [SemiprimeOrderSeparation.gcd_sub_one_mul hp.pos hq.pos] at hd
  · have hpow := congrArg
      (Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom) hraw
    simp only [map_pow, map_one] at hpow
    have hd := Nat.dvd_gcd (ZMod.orderOf_units_dvd_card_sub_one _)
      (orderOf_dvd_of_pow_eq_one hpow)
    rwa [SemiprimeOrderSeparation.gcd_sub_one_mul_right hp.pos hq.pos] at hd

/-- The global order of a raw-kernel unit itself divides both field
cardinalities. Equal local orders are not required; CRT retains both. -/
theorem kernel_global_order_common {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (g : (ZMod (p*q))ˣ) (hraw : g^(p*q-1)=1) :
    orderOf g∣p-1 ∧ orderOf g∣q-1 := by
  obtain ⟨hP, hQ⟩ := local_kernel_orders_dvd_common hp hq g hraw
  have hboth (E : ℕ) (hE : (p-1).gcd (q-1)∣E) : g^E=1 := by
    apply Units.ext
    apply SemiprimeIntervalJet.eq_of_prime_reductions hp hq hpq
    · have hpw := orderOf_dvd_iff_pow_eq_one.mp (hP.trans hE)
      have hv := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hpw
      simpa [RingHom.toMonoidHom] using hv
    · have hpw := orderOf_dvd_iff_pow_eq_one.mp (hQ.trans hE)
      have hv := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hpw
      simpa [RingHom.toMonoidHom] using hv
  exact ⟨orderOf_dvd_of_pow_eq_one (hboth _ (Nat.gcd_dvd_left _ _)),
    orderOf_dvd_of_pow_eq_one (hboth _ (Nat.gcd_dvd_right _ _))⟩

/-- A known large global order rescues a raw-kernel seed directly.
The actual order must still be obtained and charged by the algorithm. -/
theorem recoverCommon_of_kernel_order {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p<q) (g : (ZMod (p*q))ˣ) (hraw : g^(p*q-1)=1)
    (hm : orderOf g=m) (hN : p*q<m^3) : recoverCommon (p*q) m=some p := by
  obtain ⟨hmp, hmq⟩ := kernel_global_order_common hp hq hpq.ne g hraw
  rw [hm] at hmp hmq
  exact recoverCommon_semiprime hp hq hpq.le (hm ▸ orderOf_pos g) hmp hmq hN

/-- Three prime factors beyond the quadratic prefix cannot fit the
sixth-power input budget. Repeated prime factors are included. -/
theorem rough_residual_cases {R B : ℕ} (hR : 0<R) (hbudget : R≤B^6)
    (hrough : ∀ r, r.Prime → r∣R → B^2<r) :
    R=1 ∨ R.Prime ∨ ∃ p q, p.Prime ∧ q.Prime ∧ R=p*q := by
  by_cases h1 : R=1
  · exact Or.inl h1
  right
  let p := R.minFac
  have hp : p.Prime := Nat.minFac_prime h1
  have hpR : p∣R := Nat.minFac_dvd R
  obtain ⟨S, hRS⟩ := hpR
  have hpR : p∣R := ⟨S, hRS⟩
  by_cases hS1 : S=1
  · left
    simpa only [hRS, hS1, mul_one] using hp
  right
  let q := S.minFac
  have hq : q.Prime := Nat.minFac_prime hS1
  have hqS : q∣S := Nat.minFac_dvd S
  have hqR : q∣R := by rw [hRS]; exact dvd_mul_of_dvd_right hqS p
  obtain ⟨T, hST⟩ := hqS
  have hT1 : T=1 := by
    by_contra hn
    let r := T.minFac
    have hr : r.Prime := Nat.minFac_prime hn
    have hrT : r∣T := Nat.minFac_dvd T
    have hrR : r∣R := by
      rw [hRS, hST]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hrT q) p
    have hd : p*q*r∣R := by
      obtain ⟨U, hTU⟩ := hrT
      rw [hRS, hST, hTU]
      refine ⟨U, ?_⟩
      ring
    have hle := Nat.le_of_dvd hR hd
    have hpB : B^2+1≤p := by have hh := hrough p hp hpR; omega
    have hqB : B^2+1≤q := by have hh := hrough q hq hqR; omega
    have hrB : B^2+1≤r := by have hh := hrough r hr hrR; omega
    have hprod := Nat.mul_le_mul (Nat.mul_le_mul hpB hqB) hrB
    nlinarith
  exact ⟨p, q, hp, hq, by simpa only [hST, hT1, mul_one] using hRS⟩

/-- The failed compressed prefix supplies the actual roughness
certificate of the residual; no unproved smoothness estimate is used. -/
theorem rough_residual_cases_after_prefix {R B : ℕ} (hR : 0<R)
    (hbudget : R≤B^6) (hcover : B^2<R)
    (hnone : SemiprimeStrassenPrefix.factorPrefix R B=none) :
    R=1 ∨ R.Prime ∨ ∃ p q, p.Prime ∧ q.Prime ∧ R=p*q := by
  apply rough_residual_cases hR hbudget
  intro r hr hrR
  exact SemiprimeStrassenPrefix.prefix_none_excludes_small_prime hcover hr hrR hnone

/-- A rough residual inside the fourth-power range is actually prime.
The prefix certificate discharges primality without a hidden oracle. -/
theorem rough_residual_prime {R B : ℕ} (hR : 1<R) (hbudget : R≤B^4)
    (hrough : ∀ r, r.Prime → r∣R → B^2<r) : R.Prime := by
  by_contra hn
  have hp := Nat.minFac_prime (show R≠1 by omega)
  have hgt := hrough R.minFac hp (Nat.minFac_dvd R)
  have hsq := Nat.minFac_sq_le_self (show 0<R by omega) hn
  nlinarith

/-- The public prefix and numerical size together certify primality. -/
theorem rough_residual_prime_after_prefix {R B : ℕ} (hR : 1<R)
    (hbudget : R≤B^4) (hcover : B^2<R)
    (hnone : SemiprimeStrassenPrefix.factorPrefix R B=none) : R.Prime := by
  apply rough_residual_prime hR hbudget
  intro r hr hrR
  exact SemiprimeStrassenPrefix.prefix_none_excludes_small_prime hcover hr hrR hnone

/-- After removing the factor two from N-1, any remaining divisor
is smaller than half the original input. This is a strict recursive
size reduction, not an assumption that the recursive work is free. -/
theorem rough_residual_half_bound {N R : ℕ} (hN : 2<N)
    (hd : R∣(N-1)/2) : 2*R<N := by
  have hhalf : 0<(N-1)/2 := by omega
  have hle := Nat.le_of_dvd hhalf hd
  have hh := Nat.div_mul_le_self (N-1) 2
  omega

/-- A nontrivial raw-kernel unit annihilated by a rough exponent has
prime global order beyond B^2. The order's numerical value is still
unknown: this preserves an active prime-order channel, not its factor. -/
theorem rough_kernel_order_prime {p q R B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p<q) (g : (ZMod (p*q))ˣ) (hraw : g^(p*q-1)=1)
    (hpow : g^R=1) (hne : g≠1) (hB : 0<B) (hbudget : p*q≤B^6)
    (hrough : ∀ r, r.Prime → r∣R → B^2<r) :
    (orderOf g).Prime ∧ B^2<orderOf g ∧ p*q<(orderOf g)^3 := by
  have hm : 1<orderOf g := by
    have hh := orderOf_pos g
    have hn : orderOf g≠1 := fun he => hne (orderOf_eq_one_iff.mp he)
    omega
  have hd : orderOf g∣R := orderOf_dvd_of_pow_eq_one hpow
  have hmp := (kernel_global_order_common hp hq hpq.ne g hraw).1
  have hmpBound := Nat.le_of_dvd (show 0<p-1 by have hh:=hp.one_lt; omega) hmp
  have hpB : p≤B^3 := by
    have hpp := Nat.mul_le_mul_left p hpq.le
    have hsq : p^2≤(B^3)^2 := by
      calc
        p^2≤p*q := by simpa only [pow_two] using hpp
        _≤B^6 := hbudget
        _=(B^3)^2 := by ring
    exact (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp hsq
  have hB4 : B^3≤B^4 := by
    have he := Nat.mul_le_mul_left (B^3) (show 1≤B by omega)
    nlinarith
  have hprime : (orderOf g).Prime := by
    apply rough_residual_prime (B:=B) hm (by omega)
    intro r hr hrm
    exact hrough r hr (hrm.trans hd)
  have hgt := hrough (orderOf g) hprime hd
  have hcube : B^6<(orderOf g)^3 := by
    have he := Nat.pow_lt_pow_left hgt (by decide : 3≠0)
    nlinarith
  exact ⟨hprime, hgt, hbudget.trans_lt hcube⟩

/-- Raw-kernel powers make the literal row step adjacent. No prime,
order value or field reduction is needed to expose this cancellation. -/
theorem kernel_row_step {R : Type*} [Monoid R] (alpha : R) {N : ℕ}
    (hN : 1≤N) (hraw : alpha^(N-1)=1) : alpha^N=alpha := by
  have he : N=N-1+1 := by omega
  rw [he, pow_add, hraw, pow_one, one_mul]

/-- The original targets collapse to publicly known interval roots in
the raw kernel. This records the diagonal zero rather than dividing it. -/
theorem kernel_row_target {R : Type*} [Monoid R] (alpha : R) {N : ℕ}
    (hN : 1≤N) (hraw : alpha^(N-1)=1) (a B : ℕ) :
    alpha^(a*N+B^2)=alpha^(a+B^2) := by
  rw [pow_add, Nat.mul_comm a N, pow_mul, kernel_row_step alpha hN hraw, ← pow_add]

/-- Adjacent cancellation on this branch is saturated at every known
diagonal root. The unmarked scalar is globally zero over the full ring. -/
theorem kernel_row_diagonal_zero {R : Type*} [CommRing R] (alpha : R) {N a B L : ℕ}
    (hN : 1≤N) (hraw : alpha^(N-1)=1) (hk : a+B^2<L) :
    SemiprimeIntervalJet.intervalProduct alpha (alpha^(a*N+B^2)) L=0 := by
  rw [kernel_row_target alpha hN hraw]
  unfold SemiprimeIntervalJet.intervalProduct
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hk) (sub_self _)

/-- Even the marked first jet recovers the already public diagonal
label on a raw-kernel row. Cancellation has not created a separating
index: both coefficient channels retain the same exact global identity. -/
theorem kernel_row_mark {R : Type*} [CommRing R] (alpha : R) {N a B L : ℕ}
    (hN : 1≤N) (hraw : alpha^(N-1)=1) (hk : a+B^2<L) :
    SemiprimeIntervalJet.baseDerivative alpha (alpha^(a*N+B^2)) L=
      -((a+B^2 : ℕ) : R)*alpha^(a*N+B^2)*
        SemiprimeIntervalJet.targetDerivative alpha (alpha^(a*N+B^2)) L := by
  rw [kernel_row_target alpha hN hraw]
  exact SemiprimeIntervalJet.baseDerivative_at_root alpha hk

/-- Differentiate the retained polynomial cancellation before evaluating
at its two roots. Both scalar rows vanish, but their first jets obey an
exact cleared relation, including zero endpoints and nonunit bases. -/
theorem adjacent_root_first_jet {R : Type*} [CommRing R]
    (alpha x : R) (L : ℕ)
    (hx : SemiprimeIntervalJet.intervalProduct alpha x L=0)
    (hax : SemiprimeIntervalJet.intervalProduct alpha (alpha*x) L=0) :
    alpha*SemiprimeIntervalJet.targetDerivative alpha (alpha*x) L*(alpha*x-alpha^L)=
      alpha^L*(alpha*x-1)*SemiprimeIntervalJet.targetDerivative alpha x L := by
  have hd (z : R) : (SemiprimeGeometricRows.rowPolynomial alpha L).derivative.eval z=
      SemiprimeIntervalJet.targetDerivative alpha z L := by
    simpa only [SemiprimeGeometricRows.rowPolynomial] using
      (SemiprimeIntervalJet.targetDerivative_eq_derivative alpha z L).symm
  have he := congrArg Polynomial.derivative
    (SemiprimeGeometricRows.adjacent_polynomial_telescoping alpha L)
  have hev := congrArg (fun Q : Polynomial R => Q.eval x) he
  simpa only [Polynomial.derivative_mul, Polynomial.derivative_comp,
    Polynomial.derivative_sub, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.derivative_one, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero,
    Polynomial.eval_one, mul_zero, zero_mul, zero_add, add_zero, sub_zero,
    SemiprimeGeometricRows.rowPolynomial_eval, hd, hx, hax, mul_one] using hev

/-- The zero-safe first-jet cancellation applies to adjacent literal
rows of the retained raw-kernel base. A row update may divide by its
endpoint only after a separate public unit check. -/
theorem kernel_row_first_jet_step {R : Type*} [CommRing R] (alpha : R)
    {N a B L : ℕ} (hN : 1≤N) (hraw : alpha^(N-1)=1) (hk : a+1+B^2<L) :
    alpha*SemiprimeIntervalJet.targetDerivative alpha (alpha^((a+1)*N+B^2)) L*
        (alpha^((a+1)*N+B^2)-alpha^L)=
      alpha^L*(alpha^((a+1)*N+B^2)-1)*
        SemiprimeIntervalJet.targetDerivative alpha (alpha^(a*N+B^2)) L := by
  have hstep : alpha*alpha^(a*N+B^2)=alpha^((a+1)*N+B^2) := by
    rw [kernel_row_target alpha hN hraw a B, kernel_row_target alpha hN hraw (a+1) B,
      ← pow_succ']
    congr 1
    omega
  have hx := kernel_row_diagonal_zero alpha hN hraw (show a+B^2<L by omega)
  have hax : SemiprimeIntervalJet.intervalProduct alpha (alpha*alpha^(a*N+B^2)) L=0 := by
    rw [hstep]
    exact kernel_row_diagonal_zero alpha hN hraw hk
  simpa only [hstep] using adjacent_root_first_jet alpha (alpha^(a*N+B^2)) L hx hax

/-- These are the complete prime divisors of the saved base-3 order. -/
theorem control_order_prime_divisors {r : ℕ} (hr : r.Prime) (hd : r∣207) :
    r=3 ∨ r=23 := by
  have he : (207 : ℕ)=3^2*23 := by norm_num
  rw [he] at hd
  obtain h3 | h23 := hr.dvd_mul.mp hd
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp
      (hr.dvd_of_dvd_pow h3))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h23)

set_option maxRecDepth 32768 in
/-- Exact public powers certify order 207; all prime-divisor tests
are nontrivial over the original composite ring. -/
theorem control_base_three_order_powers :
    (3 : ZMod 1373653)^207=1 ∧ (3 : ZMod 1373653)^69≠1 ∧
      (3 : ZMod 1373653)^9≠1 := by
  norm_num
  reduce_mod_char
  decide

/-- A raw-kernel base has a known global order above the quadratic
prefix width on the actual saved semiprime, with no local-order input. -/
theorem control_base_three_kernel_order (g : (ZMod 1373653)ˣ)
    (hg : (g : ZMod 1373653)=3) :
    orderOf g=207 ∧ g^(1373653-1)=1 := by
  obtain ⟨hpw, hn3, hn23⟩ := control_base_three_order_powers
  have hpow : g^207=1 := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, hg, Units.val_one] using hpw
  constructor
  · apply orderOf_eq_of_pow_and_pow_div_prime (by decide) hpow
    intro r hr hrdiv he
    have hv := congrArg (fun u : (ZMod 1373653)ˣ => (u : ZMod 1373653)) he
    simp only [Units.val_pow_eq_pow_val, hg, Units.val_one] at hv
    obtain rfl | rfl := control_order_prime_divisors hr hrdiv
    · exact hn3 hv
    · exact hn23 hv
  · apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, hg, Units.val_one] using
      SemiprimeStagedSeed.control_raw_seed_factor.2.1

/-- The known-order route factors the saved raw-kernel input directly:
index sum 12, index product 32 and discriminant 16 recover 829. -/
theorem control_common_order_recovery :
    indexSum 1373653 207=12 ∧ indexProduct 1373653 207=32 ∧
    (1373653 : ℕ)<207^3 ∧ (11 : ℕ)^2<207 ∧
    recoverCommon 1373653 207=some 829 := by
  norm_num [indexSum, indexProduct, orderQuotient, recoverCommon,
    commonCandidate, checkedSignal]

/-- The public power certificate, actual raw-kernel property and
generic reconstruction theorem form one checked chain for the control. -/
theorem control_kernel_certificate_recovers (g : (ZMod 1373653)ˣ)
    (hg : (g : ZMod 1373653)=3) : recoverCommon 1373653 207=some 829 := by
  obtain ⟨hm, hraw⟩ := control_base_three_kernel_order g hg
  exact recoverCommon_of_kernel_order (p:=829) (q:=1657)
    (by norm_num) (by norm_num) (by norm_num) g hraw hm (by norm_num)

/-- Retain the B original polynomial columns at the original modulus;
subsequent residual moduli use reductions of this same source. -/
noncomputable def retainedPrefixValues (M B : ℕ) : List ℕ :=
  (SemiprimeStrassenPrefix.blockColumns M B).map Prod.snd

theorem retainedPrefixValues_length (M B : ℕ) :
    (retainedPrefixValues M B).length=B := by
  simp only [retainedPrefixValues, List.length_map,
    SemiprimeStrassenPrefix.blockColumns_length]

/-- Dividing the modulus preserves each original block value exactly
after reduction. One polynomial source can serve every residual divisor. -/
theorem retainedPrefixValues_downcast {M R B : ℕ} (hd : R∣M) :
    (retainedPrefixValues M B).map (fun v => v%R)=retainedPrefixValues R B := by
  simp only [retainedPrefixValues, SemiprimeStrassenPrefix.blockColumns, List.map_map]
  apply List.map_congr_left
  intro j _
  dsimp only [Function.comp_apply]
  rw [SemiprimeStrassenPrefix.blockPolynomial_eval,
    SemiprimeStrassenPrefix.blockPolynomial_eval, ZMod.val_natCast,
    ZMod.val_natCast, Nat.mod_mod_of_dvd _ hd]

/-- The same retained original column supplies the exact GCD at every
residual divisor; no repeated polynomial construction is required. -/
theorem retained_column_gcd {M R B j : ℕ} (hd : R∣M) :
    R.gcd ((SemiprimeStrassenPrefix.blockPolynomial (R:=ZMod M) B).eval
      ((j*B : ℕ) : ZMod M)).val=R.gcd ((B*(j+1)).descFactorial B) := by
  rw [SemiprimeStrassenPrefix.blockPolynomial_eval, ZMod.val_natCast,
    Nat.gcd_rec R _, Nat.mod_mod_of_dvd _ hd, ← Nat.gcd_rec R _]

/-- Retain the wrap count rather than assuming the sum channel does not
wrap: sum adds t*m and the product channel subtracts that same t. -/
def wrappedCandidate (N m t : ℕ) : ℕ :=
  let s := indexSum N m+t*m
  let v := indexProduct N m-t
  m*((s-Nat.sqrt (s^2-4*v))/2)+1

/-- The earlier zero-wrap source is an exact slice of the richer family. -/
theorem wrappedCandidate_zero (N m : ℕ) : wrappedCandidate N m 0=commonCandidate N m := by
  simp [wrappedCandidate, commonCandidate]

/-- Exact quadratic candidates for every public wrap label. -/
def recoverWrapped (N m B : ℕ) : Option ℕ :=
  if 0<m then SemiprimeCartesianCompletion.scanProper N
    ((List.range (2*B)).map (wrappedCandidate N m)) else none

theorem recoverWrapped_sound {N m B d : ℕ} (hs : recoverWrapped N m B=some d) :
    ProperDivisor N d := by
  unfold recoverWrapped at hs
  split_ifs at hs with hm
  exact SemiprimeCartesianCompletion.scanProper_sound hs

/-- This family costs at most 2B checked GCD queries and constructs no
geometric residual rows. This excludes obtaining the known modulus. -/
theorem recoverWrapped_gcd_count (N m B : ℕ) :
    SemiprimeCartesianCompletion.scanGcdCount N
      ((List.range (2*B)).map (wrappedCandidate N m))≤2*B := by
  have he := SemiprimeCartesianCompletion.scanGcdCount_le N
    ((List.range (2*B)).map (wrappedCandidate N m))
  simpa only [List.length_map, List.length_range] using he

/-- Keeping the actual wrap count recovers both hidden coefficients
even when the zero-wrap quadratic would lose them. -/
theorem wrapped_sum_product_encoded {m a b : ℕ} (hm : 0<m) :
    indexSum ((m*a+1)*(m*b+1)) m+((a+b)/m)*m=a+b ∧
    indexProduct ((m*a+1)*(m*b+1)) m-(a+b)/m=a*b := by
  simp only [indexSum, indexProduct, orderQuotient_encoded hm,
    Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hm,
    Nat.add_sub_cancel_left]
  constructor
  · simpa only [Nat.mul_comm] using Nat.mod_add_div (a+b) m
  · trivial

/-- The correctly labeled wrapped quadratic reconstructs the original
factor exactly; no nonwrapping assumption remains. -/
theorem wrappedCandidate_encoded {m a b : ℕ} (hm : 0<m) (hab : a≤b) :
    wrappedCandidate ((m*a+1)*(m*b+1)) m ((a+b)/m)=m*a+1 := by
  obtain ⟨hs, hp⟩ := wrapped_sum_product_encoded (a:=a) (b:=b) hm
  simp only [wrappedCandidate, hs, hp]
  rw [index_discriminant_square hab, Nat.sqrt_eq']
  have he : a+b-(b-a)=2*a := by omega
  rw [he, Nat.mul_div_cancel_left _ (by decide)]

/-- On the quadratic-prefix complement, a common modulus whose square
reaches B^3 needs fewer than 2B wrap labels. The hidden factors are used
only to prove coverage of the public enumeration. -/
theorem wrap_label_bound {p q m B a b : ℕ} (hq : 0<q)
    (hpq : p≤q) (hB : 0<B) (hsmall : B^2<p) (hbudget : p*q≤B^6)
    (hsize : B^3≤m^2) (hpa : p=m*a+1) (hqb : q=m*b+1) :
    (a+b)/m<2*B := by
  have hqB : q<B^4 := by
    have he := Nat.mul_lt_mul_of_pos_right hsmall hq
    by_contra hn
    have hle := Nat.mul_le_mul_left (B^2) (show B^4≤q by omega)
    have hB2 : 0<B^2 := pow_pos hB 2
    nlinarith
  have hsum : p+q<2*B^4 := by omega
  have hdiv := Nat.div_mul_le_self (a+b) m
  have hmul := Nat.mul_le_mul_left m hdiv
  by_contra hn
  have ht : 2*B≤(a+b)/m := by omega
  have htB := Nat.mul_le_mul_right (B^3) ht
  have htM := Nat.mul_le_mul_left ((a+b)/m) hsize
  have hB3 : 0<B^3 := pow_pos hB 3
  nlinarith

/-- A sufficiently large actual common modulus factors every semiprime
on the prefix complement using the bounded public wrap scan. -/
theorem recoverWrapped_semiprime {p q m B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≤q) (hm : 0<m) (hB : 0<B) (hsmall : B^2<p)
    (hbudget : p*q≤B^6) (hsize : B^3≤m^2) (hmp : m∣p-1) (hmq : m∣q-1) :
    ∃ d, recoverWrapped (p*q) m B=some d := by
  obtain ⟨a, b, _, _, hab, hpa, hqb⟩ :=
    common_modulus_indices hp.one_lt hq.one_lt hm hpq hmp hmq
  have ht := wrap_label_bound hq.pos hpq hB hsmall hbudget hsize hpa hqb
  have hc : wrappedCandidate (p*q) m ((a+b)/m)=p := by
    rw [hpa, hqb]
    exact wrappedCandidate_encoded hm hab
  cases hs : recoverWrapped (p*q) m B with
  | some d => exact ⟨d, rfl⟩
  | none =>
    have hn : SemiprimeCartesianCompletion.scanProper (p*q)
        ((List.range (2*B)).map (wrappedCandidate (p*q) m))=none := by
      simpa only [recoverWrapped, if_pos hm] using hs
    have hmem : p ∈ (List.range (2*B)).map (wrappedCandidate (p*q) m) :=
      List.mem_map.mpr ⟨(a+b)/m, List.mem_range.mpr ht, hc⟩
    have he := (SemiprimeCartesianCompletion.scanProper_none_iff _ _).mp hn p hmem
    have hproper : 1<p ∧ p<p*q := ⟨hp.one_lt, by have hh := hq.one_lt; nlinarith⟩
    rw [checkedSignal, Nat.gcd_eq_right (dvd_mul_right p q), if_pos hproper] at he
    contradiction

/-- Failed prefix recovery and an actual known raw-kernel order
discharge all hidden arithmetic premises of the public wrap scan. -/
theorem recoverWrapped_kernel_after_prefix {p q m B : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p<q) (g : (ZMod (p*q))ˣ)
    (hraw : g^(p*q-1)=1) (hm : orderOf g=m) (hB : 0<B)
    (hcover : B^2<p*q) (hbudget : p*q≤B^6) (hsize : B^3≤m^2)
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q) B=none) :
    ∃ d, recoverWrapped (p*q) m B=some d := by
  obtain ⟨hmp, hmq⟩ := kernel_global_order_common hp hq hpq.ne g hraw
  rw [hm] at hmp hmq
  apply recoverWrapped_semiprime hp hq hpq.le (hm ▸ orderOf_pos g) hB _
    hbudget hsize hmp hmq
  exact SemiprimeStrassenPrefix.prefix_none_excludes_small_prime hcover hp
    (dvd_mul_right p q) hnone

/-- The complete prime-divisor set for the wrapped order control. -/
theorem control_wrapped_order_prime_divisors {r : ℕ} (hr : r.Prime) (hd : r∣40) :
    r=2 ∨ r=5 := by
  have he : (40 : ℕ)=2^3*5 := by norm_num
  rw [he] at hd
  obtain h2 | h5 := hr.dvd_mul.mp hd
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp
      (hr.dvd_of_dvd_pow h2))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h5)

/-- The public literal base has order 40 over the original semiprime. -/
theorem control_wrapped_order_powers :
    (508038 : ZMod 769841)^40=1 ∧ (508038 : ZMod 769841)^20≠1 ∧
      (508038 : ZMod 769841)^8≠1 := by
  norm_num
  reduce_mod_char
  decide

/-- The raw-kernel and exact-order properties follow from public
power checks even though the order is below the cubic threshold. -/
theorem control_wrapped_kernel_order (g : (ZMod 769841)ˣ)
    (hg : (g : ZMod 769841)=508038) : orderOf g=40 ∧ g^(769841-1)=1 := by
  obtain ⟨hpw, hn2, hn5⟩ := control_wrapped_order_powers
  have hpow : g^40=1 := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, hg, Units.val_one] using hpw
  constructor
  · apply orderOf_eq_of_pow_and_pow_div_prime (by decide) hpow
    intro r hr hrdiv he
    have hv := congrArg (fun u : (ZMod 769841)ˣ => (u : ZMod 769841)) he
    simp only [Units.val_pow_eq_pow_val, hg, Units.val_one] at hv
    obtain rfl | rfl := control_wrapped_order_prime_divisors hr hrdiv
    · exact hn2 hv
    · exact hn5 hv
  · have he : (769841-1 : ℕ)=40*19246 := by norm_num
    rw [he, pow_mul, hpow, one_pow]

set_option maxRecDepth 32768 in
/-- Zero-wrap reconstruction misses the factor. Retaining the actual
wrap label restores sum 46 and product 480, and recovers 641. -/
theorem control_wrapped_recovery :
    Nat.Prime 641 ∧ Nat.Prime 1201 ∧ 641*1201=769841 ∧
    indexSum 769841 40=6 ∧ indexProduct 769841 40=481 ∧
    recoverCommon 769841 40=none ∧ wrappedCandidate 769841 40 1=641 ∧
    recoverWrapped 769841 40 10=some 641 := by
  norm_num [indexSum, indexProduct, orderQuotient, recoverCommon,
    commonCandidate, wrappedCandidate, recoverWrapped,
    SemiprimeCartesianCompletion.scanProper, checkedSignal,
    List.range_eq_range', List.range'_succ]

set_option maxRecDepth 32768 in
/-- The generic bounded-wrap guarantee applies to the actual control;
the common order, prefix complement and every size premise are checked. -/
theorem control_wrapped_certificate_recovers (g : (ZMod 769841)ˣ)
    (hg : (g : ZMod 769841)=508038) : ∃ d, recoverWrapped 769841 40 10=some d := by
  obtain ⟨hm, hraw⟩ := control_wrapped_kernel_order g hg
  apply recoverWrapped_kernel_after_prefix (p:=641) (q:=1201)
    (by norm_num) (by norm_num) (by norm_num) g hraw hm
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  apply (SemiprimeStrassenPrefix.prefix_none_iff_clear (by norm_num)).mpr
  norm_num [SemiprimeGroupCoverage.prefixProduct_eq_factorial]

set_option maxRecDepth 32768 in
/-- A genuine small-order kernel misses every bounded wrap candidate.
This is outside the size premise of recoverWrapped_semiprime. -/
theorem control_small_order_wrap_exhausted :
    Nat.Prime 17 ∧ Nat.Prime 41 ∧ 17*41=697 ∧ (3 : ℕ)^2<17 ∧
    (2 : ℕ)^2<3^3 ∧ ((17-1)/2+(41-1)/2)/2=14 ∧
    recoverWrapped 697 2 3=none := by
  norm_num [recoverWrapped, wrappedCandidate, indexSum, indexProduct,
    orderQuotient, SemiprimeCartesianCompletion.scanProper, checkedSignal,
    List.range_eq_range', List.range'_succ]

set_option maxRecDepth 32768 in
/-- A rough N-1 remainder can hide an actually useful prime order.
The literal public power checks certify order 29 if that value is proposed;
the charged partial-factorization routine does not discover it on this control. -/
theorem control_active_rough_order_powers :
    (4 : ZMod 13747)^29=1 ∧ (4 : ZMod 13747)≠1 := by
  norm_num
  reduce_mod_char
  decide

/-- Exact order and raw-kernel properties derived from the proposed
public prime-order certificate in the unresolved control. -/
theorem control_active_rough_kernel_order (g : (ZMod 13747)ˣ)
    (hg : (g : ZMod 13747)=4) : orderOf g=29 ∧ g^(13747-1)=1 := by
  obtain ⟨hpw, hne⟩ := control_active_rough_order_powers
  have hpow : g^29=1 := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, hg, Units.val_one] using hpw
  constructor
  · apply orderOf_eq_of_pow_and_pow_div_prime (by decide) hpow
    intro r hr hd he
    have her : r=29 := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hd
    subst r
    have hv := congrArg (fun u : (ZMod 13747)ˣ => (u : ZMod 13747)) he
    exact hne (by simpa only [Units.val_pow_eq_pow_val, hg, Units.val_one,
      Nat.div_self (by decide : 0<29), pow_one] using hv)
  · have he : (13747-1 : ℕ)=29*474 := by norm_num
    rw [he, pow_mul, hpow, one_pow]

set_option maxRecDepth 32768 in
/-- The active rough control is on the prefix complement and its
unknown residual lies beyond the proved fourth-power prime certificate.
A known order 29 would recover 59 directly, but is not supplied for free. -/
theorem control_active_rough_reconstruction :
    Nat.Prime 59 ∧ Nat.Prime 233 ∧ 59*233=13747 ∧
    (13747-1 : ℕ)=2*3*2291 ∧ 2291=29*79 ∧ (5 : ℕ)^4<2291 ∧
    (5 : ℕ)^2<59 ∧ 13747≤(5 : ℕ)^6 ∧
    Nat.gcd 2291 (Nat.factorial (5^2))=1 ∧ recoverCommon 13747 29=some 59 := by
  norm_num [recoverCommon, commonCandidate, indexSum, indexProduct, orderQuotient,
    checkedSignal]

end RiemannGaussian.SemiprimeCommonOrder
