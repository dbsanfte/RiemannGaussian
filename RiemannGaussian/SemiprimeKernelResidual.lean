/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeLocalOrderRouting

/-!
# Public small-prime stripping and residual kernel extraction

Reuse one additive prefix source at all residual divisors of N-1. Its
first nonunit column supplies one small integer leaf, whose minimal prime
factor is inside the quadratic prefix. Logarithmic fuel removes every
such prime factor. The remaining active kernel channel has prime order;
its large rough residual is a strictly smaller semiprime, not a free oracle.
The full one-sixth extractor and bit backend remain research frontiers.
-/

namespace RiemannGaussian.SemiprimeKernelResidual

open SemiprimeGroupSelection SemiprimeCartesianCompletion SemiprimeStrassenPrefix
open SemiprimeLocalOrderRouting

/-- Select a nonunit column from the cached original prefix source. -/
def nonunitColumn (R : ℕ) (columns : List (ℕ × ℕ)) : Option (ℕ × ℕ) :=
  columns.find? (fun c => decide (R.gcd c.2≠1))

/-- Expand only the selected block and retain its first nonunit leaf. -/
def nonunitLeaf (R B j : ℕ) : Option ℕ :=
  (blockLeaves R B j).find? (fun v => decide (1<R.gcd v))

/-- Each original cached column keeps its label and exact residual GCD. -/
theorem retained_column_data {E R B : ℕ} (hd : R∣E) {c : ℕ × ℕ}
    (hc : c∈blockColumns E B) :
    c.1<B ∧ R.gcd c.2=R.gcd (blockLeaves R B c.1).prod := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
  refine ⟨List.mem_range.mp hj, ?_⟩
  dsimp only
  rw [SemiprimeCommonOrder.retained_column_gcd hd,
    ← block_column_gcd_eq_descFactorial R B j, block_column_gcd_eq]

/-- A nonunit retained column always has a proper small leaf when the
quadratic prefix is below the current residual. -/
theorem nonunitLeaf_succeeds {E R B j v : ℕ} (hd : R∣E) (hcover : B^2<R)
    (hc : (j,v)∈blockColumns E B) (hunit : R.gcd v≠1) :
    ∃ k, nonunitLeaf R B j=some k := by
  obtain ⟨hj, he⟩ := retained_column_data hd hc
  obtain ⟨k, hk, hproper⟩ := proper_leaf_of_product_gcd
    (blockLeaves_bounds hcover hj) (he ▸ hunit)
  cases hs : nonunitLeaf R B j with
  | some k' => exact ⟨k', rfl⟩
  | none =>
    have hn := List.find?_eq_none.mp hs k hk
    simp only [decide_eq_true_eq] at hn
    exact False.elim (hn hproper.1)

/-- A small prime is derived from a small retained leaf, never from
trial factorization of the full exponent. -/
def smallPrimeChoice (B : ℕ) (columns : List (ℕ × ℕ)) (R : ℕ) : Option ℕ :=
  if R≤1 then none else if R≤B^2 then some R.minFac else
    match nonunitColumn R columns with
    | none => none
    | some (j,_) =>
      match nonunitLeaf R B j with
      | none => none
      | some k => some (R.gcd k).minFac

/-- Every chosen value is an actual small prime factor of the residual. -/
theorem smallPrimeChoice_some {E R B r : ℕ} (hd : R∣E) (hR : 0<R)
    (hs : smallPrimeChoice B (blockColumns E B) R=some r) :
    r.Prime ∧ r∣R ∧ r≤B^2 := by
  unfold smallPrimeChoice at hs
  split_ifs at hs with hone hsmall
  · have he : R.minFac=r := Option.some.inj hs
    rw [← he]
    exact ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd R, (Nat.minFac_le hR).trans hsmall⟩
  · cases hc : nonunitColumn R (blockColumns E B) with
    | none => simp only [hc] at hs; contradiction
    | some c =>
      obtain ⟨j,v⟩ := c
      simp only [hc] at hs
      cases hl : nonunitLeaf R B j with
      | none => simp only [hl] at hs; contradiction
      | some k =>
        simp only [hl, Option.some.injEq] at hs
        have hcol := List.mem_of_find?_eq_some hc
        have hj := (retained_column_data hd hcol).1
        have hmem := List.mem_of_find?_eq_some hl
        have hgt : 1<R.gcd k := by
          simpa only [decide_eq_true_eq] using List.find?_some hl
        have hkpos := (blockLeaves_bounds (by omega : B^2<R) hj k hmem).1
        obtain ⟨i, hi, he⟩ := List.mem_map.mp hmem
        have hb := block_integer_bounds (List.mem_range.mp hi) hj
        have hk : k≤B^2 := by
          rw [← he, Nat.mod_eq_of_lt (hb.2.trans_lt (by omega : B^2<R))]
          exact hb.2
        rw [← hs]
        exact ⟨Nat.minFac_prime (by omega),
          (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _),
          (Nat.minFac_le (by omega)).trans ((Nat.gcd_le_right R hkpos).trans hk)⟩

/-- Exhausting this actual cached scan certifies quadratic roughness.
An empty selected leaf is excluded by the retained polynomial identity. -/
theorem smallPrimeChoice_none {E R B : ℕ} (hd : R∣E) (hR : 0<R)
    (hs : smallPrimeChoice B (blockColumns E B) R=none) :
    ∀ r, r.Prime → r∣R → B^2<r := by
  intro r hr hrR
  unfold smallPrimeChoice at hs
  split_ifs at hs with hone hsmall
  · have he : R=1 := by omega
    exact False.elim (hr.not_dvd_one (he ▸ hrR))
  · have hcover : B^2<R := by omega
    cases hc : nonunitColumn R (blockColumns E B) with
    | some c =>
      obtain ⟨j,v⟩ := c
      have hmem := List.mem_of_find?_eq_some hc
      have hnonunit : R.gcd v≠1 := by
        simpa only [decide_eq_true_eq] using List.find?_some hc
      obtain ⟨k, hk⟩ := nonunitLeaf_succeeds hd hcover hmem hnonunit
      simp only [hc, hk] at hs
      contradiction
    | none =>
      by_contra hn
      have hrB : r≤B^2 := by omega
      obtain ⟨j,i,hj,hi,he⟩ := prefix_integer_decomposition hr.pos hrB
      let c : ℕ × ℕ := (j,
        ((blockPolynomial (R:=ZMod E) B).eval ((j*B : ℕ) : ZMod E)).val)
      have hmem : c∈blockColumns E B :=
        List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
      have hunit : R.gcd c.2=1 := by
        have hh := List.find?_eq_none.mp hc c hmem
        simpa only [decide_eq_true_eq, not_not] using hh
      have hproduct : R.gcd (blockLeaves R B j).prod=1 := by
        rw [← (retained_column_data hd hmem).2]
        exact hunit
      have hleaf : r∈blockLeaves R B j := by
        apply List.mem_map.mpr
        exact ⟨i, List.mem_range.mpr hi, by rw [← he, Nat.mod_eq_of_lt (hrB.trans_lt hcover)]⟩
      have hcoprime := Nat.coprime_list_prod_right_iff.mp hproduct r hleaf
      change R.gcd r=1 at hcoprime
      rw [Nat.gcd_eq_right hrR] at hcoprime
      exact hr.ne_one hcoprime

/-- Remove one certified small prime per stage, retaining multiplicity.
The polynomial columns are an immutable input reused by every stage. -/
def smallPrimeLoop (B : ℕ) (columns : List (ℕ × ℕ)) : ℕ → ℕ → ℕ × List ℕ
  | 0, R => (R,[])
  | fuel+1, R =>
    match smallPrimeChoice B columns R with
    | none => (R,[])
    | some r =>
      let result := smallPrimeLoop B columns fuel (R/r)
      (result.1,r::result.2)

/-- Logarithmic fuel suffices for an exact public smooth/rough split.
The prime list is derived by the scan, not supplied as factorization advice. -/
theorem smallPrimeLoop_complete {E R B fuel : ℕ} (hd : R∣E) (hR : 0<R)
    (hpay : R≤2^fuel) :
    let result := smallPrimeLoop B (blockColumns E B) fuel R
    0<result.1 ∧ result.1∣R ∧ result.2.prod*result.1=R ∧
      (∀ r∈result.2, r.Prime ∧ r≤B^2) ∧
      (∀ r, r.Prime → r∣result.1 → B^2<r) ∧ result.2.length≤fuel := by
  induction fuel generalizing R with
  | zero =>
    have he : R=1 := by
      have h1 : R≤1 := by simpa only [pow_zero] using hpay
      omega
    dsimp only [smallPrimeLoop]
    refine ⟨hR, dvd_refl _, by simp, by simp, ?_, by simp⟩
    intro r hr hrR
    exact False.elim (hr.not_dvd_one (he ▸ hrR))
  | succ fuel ih =>
    cases hs : smallPrimeChoice B (blockColumns E B) R with
    | none =>
      simp only [smallPrimeLoop, hs]
      exact ⟨hR, dvd_refl _, by simp, by simp, smallPrimeChoice_none hd hR hs, by simp⟩
    | some r =>
      obtain ⟨hr, hrR, hrB⟩ := smallPrimeChoice_some hd hR hs
      have hquot : 0<R/r := Nat.div_pos (Nat.le_of_dvd hR hrR) hr.pos
      have hdiv : R/r∣R := Nat.div_dvd_of_dvd hrR
      have hmul : r*(R/r)=R := Nat.mul_div_cancel' hrR
      have hnewpay : R/r≤2^fuel := by
        have htwo := Nat.mul_le_mul_right (R/r) hr.two_le
        rw [pow_succ] at hpay
        nlinarith
      obtain ⟨hpos, hfactor, hencoded, hprimes, hrough, hlength⟩ :=
        ih (hdiv.trans hd) hquot hnewpay
      simp only [smallPrimeLoop, hs]
      refine ⟨hpos, hfactor.trans hdiv, ?_, ?_, hrough, ?_⟩
      · simp only [List.prod_cons]
        rw [Nat.mul_assoc, hencoded, hmul]
      · intro s hs
        rcases List.mem_cons.mp hs with he | hmem
        · subst s; exact ⟨hr, hrB⟩
        · exact hprimes s hmem
      · simp only [List.length_cons]
        omega

/-- One public cached prefix source and logarithmically many small-prime
stages split an exponent. No prime or factor oracle is an input. -/
noncomputable def splitSmall (E B : ℕ) : ℕ × List ℕ :=
  smallPrimeLoop B (blockColumns E B) (Nat.clog 2 (E+1)) E

/-- The literal public split certifies its residual and complete known
small-prime list, including repeated factors. -/
theorem splitSmall_complete {E B : ℕ} (hE : 0<E) :
    0<(splitSmall E B).1 ∧ (splitSmall E B).1∣E ∧
      (splitSmall E B).2.prod*(splitSmall E B).1=E ∧
      (∀ r∈(splitSmall E B).2, r.Prime ∧ r≤B^2) ∧
      (∀ r, r.Prime → r∣(splitSmall E B).1 → B^2<r) ∧
      (splitSmall E B).2.length≤Nat.clog 2 (E+1) := by
  exact smallPrimeLoop_complete (dvd_refl E) hE
    ((Nat.le_succ E).trans (Nat.le_pow_clog (by decide) (E+1)))

/-- With the factor two actually stripped, the residual divides the
half exponent. This is derived from the public split, not supplied advice. -/
theorem splitSmall_dvd_half {E B : ℕ} (hE : 0<E) (heven : 2∣E) (hB : 2≤B) :
    (splitSmall E B).1∣E/2 := by
  obtain ⟨hpos, hd, hencoded, _, hrough, _⟩ := splitSmall_complete (B:=B) hE
  have hnot : ¬2∣(splitSmall E B).1 := by
    intro htwo
    have hgt := hrough 2 Nat.prime_two htwo
    nlinarith
  have hjoined : 2∣(splitSmall E B).2.prod*(splitSmall E B).1 := by
    rw [hencoded]
    exact heven
  have hprod : 2∣(splitSmall E B).2.prod :=
    (Nat.prime_two.dvd_mul.mp hjoined).resolve_right hnot
  have htwice : 2*(splitSmall E B).1∣E := by
    obtain ⟨t, ht⟩ := hprod
    refine ⟨t, ?_⟩
    calc
      E=(splitSmall E B).2.prod*(splitSmall E B).1 := hencoded.symm
      _=(2*t)*(splitSmall E B).1 := by rw [ht]
      _=2*(splitSmall E B).1*t := by ring
  exact (Nat.dvd_div_iff_mul_dvd heven).mpr htwice

/-- An actual N-1 split gives a strictly smaller-than-half residual. -/
theorem splitSmall_half_bound {N B : ℕ} (hN : 2<N) (heven : 2∣N-1) (hB : 2≤B) :
    2*(splitSmall (N-1) B).1<N :=
  SemiprimeCommonOrder.rough_residual_half_bound hN
    (splitSmall_dvd_half (by omega) heven hB)

/-- Derive an exact order from a complete retained prime list. Each
stage either removes the prime or moves to the same unit's prime power. -/
def orderFromPrimes {G : Type*} [Group G] [DecidableEq G] (g : G) : List ℕ → ℕ
  | [] => 1
  | r::tail =>
    if g^tail.prod=1 then orderFromPrimes g tail else r*orderFromPrimes (g^r) tail

/-- Known prime multiplicities and public powers suffice to recover the
order; the large annihilator is never trial-factorized in this procedure. -/
theorem orderFromPrimes_eq_order {G : Type*} [Group G] [Finite G] [DecidableEq G]
    (g : G) {primes : List ℕ} (hprimes : ∀ r∈primes, r.Prime)
    (hpow : g^primes.prod=1) : orderFromPrimes g primes=orderOf g := by
  induction primes generalizing g with
  | nil =>
    have hg : g=1 := by simpa using hpow
    simp [orderFromPrimes, hg]
  | cons r tail ih =>
    have hr := hprimes r (by simp)
    have htail : ∀ s∈tail, s.Prime := fun s hs => hprimes s (List.mem_cons_of_mem _ hs)
    by_cases he : g^tail.prod=1
    · simp only [orderFromPrimes, if_pos he]
      exact ih g htail he
    · have hnext : (g^r)^tail.prod=1 := by
        simpa only [List.prod_cons, pow_mul] using hpow
      have hdiv : r∣orderOf g := by
        by_contra hn
        have hc := (hr.coprime_iff_not_dvd.mpr hn).symm
        have hd := orderOf_dvd_of_pow_eq_one hpow
        rw [List.prod_cons] at hd
        exact he (orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_of_dvd_mul_left hd))
      simp only [orderFromPrimes, if_neg he]
      rw [ih (g^r) htail hnext, orderOf_pow, Nat.gcd_eq_right hdiv,
        Nat.mul_div_cancel' hdiv]

/-- Count modular powers in the actual retained-prime recursion. -/
def orderFromPrimesPowerCount {G : Type*} [Group G] [DecidableEq G]
    (g : G) : List ℕ → ℕ
  | [] => 0
  | r::tail =>
    if g^tail.prod=1 then 1+orderFromPrimesPowerCount g tail
    else 2+orderFromPrimesPowerCount (g^r) tail

/-- At most two powers per supplied prime record, including multiplicity. -/
theorem orderFromPrimesPowerCount_le {G : Type*} [Group G] [DecidableEq G]
    (g : G) (primes : List ℕ) : orderFromPrimesPowerCount g primes≤2*primes.length := by
  induction primes generalizing g with
  | nil => simp [orderFromPrimesPowerCount]
  | cons r tail ih =>
    have hfirst := ih g
    have hsecond := ih (g^r)
    simp only [orderFromPrimesPowerCount, List.length_cons]
    split_ifs <;> omega

/-- Predicate evaluations made by the exact first-match scan. -/
def findQueryCount {α : Type*} (test : α → Bool) : List α → ℕ
  | [] => 0
  | a::tail => 1+if test a then 0 else findQueryCount test tail

theorem findQueryCount_le {α : Type*} (test : α → Bool) (values : List α) :
    findQueryCount test values≤values.length := by
  induction values with
  | nil => rfl
  | cons a tail ih =>
    simp only [findQueryCount, List.length_cons]
    split_ifs <;> omega

/-- GCD queries of one small-prime stage, including recomputation of
the chosen leaf GCD before its bounded minimal-prime search. -/
def smallPrimeGcdCount (B : ℕ) (columns : List (ℕ × ℕ)) (R : ℕ) : ℕ :=
  if R≤1 then 0 else if R≤B^2 then 0 else
    findQueryCount (fun c => decide (R.gcd c.2≠1)) columns +
      match nonunitColumn R columns with
      | none => 0
      | some (j,_) =>
        findQueryCount (fun v => decide (1<R.gcd v)) (blockLeaves R B j) +
          match nonunitLeaf R B j with
          | none => 0
          | some _ => 1

/-- One cached B-column stage makes at most 2B+1 GCD queries. -/
theorem smallPrimeGcdCount_le (E B R : ℕ) :
    smallPrimeGcdCount B (blockColumns E B) R≤2*B+1 := by
  have hc := findQueryCount_le (fun c : ℕ × ℕ => decide (R.gcd c.2≠1)) (blockColumns E B)
  rw [blockColumns_length] at hc
  have hl (j : ℕ) := findQueryCount_le (fun v => decide (1<R.gcd v)) (blockLeaves R B j)
  have hlen (j : ℕ) : (blockLeaves R B j).length=B := by simp [blockLeaves]
  simp only [hlen] at hl
  unfold smallPrimeGcdCount
  split_ifs
  · omega
  · omega
  · cases hs : nonunitColumn R (blockColumns E B) with
    | none => simp only; omega
    | some c =>
      obtain ⟨j,v⟩ := c
      simp only
      have hleaf := hl j
      cases hh : nonunitLeaf R B j <;> simp only <;> omega

/-- Count GCD queries along the actual small-prime loop. -/
def smallPrimeLoopGcdCount (B : ℕ) (columns : List (ℕ × ℕ)) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel+1, R =>
    smallPrimeGcdCount B columns R +
      match smallPrimeChoice B columns R with
      | none => 0
      | some r => smallPrimeLoopGcdCount B columns fuel (R/r)

/-- The complete public split pays logarithmically many linear-width
GCD stages. Trial division and polynomial bit arithmetic are separate. -/
theorem smallPrimeLoopGcdCount_le (E B fuel R : ℕ) :
    smallPrimeLoopGcdCount B (blockColumns E B) fuel R≤(2*B+1)*fuel := by
  induction fuel generalizing R with
  | zero => simp [smallPrimeLoopGcdCount]
  | succ fuel ih =>
    have hstage := smallPrimeGcdCount_le E B R
    rw [smallPrimeLoopGcdCount]
    cases hs : smallPrimeChoice B (blockColumns E B) R with
    | none => simp only; nlinarith
    | some r =>
      simp only
      have htail := ih (R/r)
      nlinarith

/-- The N-only exponent split's actual GCD budget. -/
theorem splitSmall_gcd_budget (E B : ℕ) :
    smallPrimeLoopGcdCount B (blockColumns E B) (Nat.clog 2 (E+1)) E≤
      (2*B+1)*Nat.clog 2 (E+1) := smallPrimeLoopGcdCount_le _ _ _ _

/-- A proper divisor of a two-prime product is one of its prime factors,
including repeated primes; no primality oracle is needed by the consumer. -/
theorem proper_divisor_prime_product {u v d : ℕ} (hu : u.Prime) (hv : v.Prime)
    (hd : ProperDivisor (u*v) d) : d=u ∨ d=v := by
  have hdgt := hd.1
  obtain ⟨e, he⟩ := hd.2.2
  have hegt : 1<e := by
    have hprod : d<d*e := by simpa only [he] using hd.2.1
    nlinarith [hd.1]
  have hud : u∣d*e := he ▸ dvd_mul_right u v
  rcases hu.dvd_mul.mp hud with hud | hue
  · obtain ⟨t, ht⟩ := hud
    have hve : v=t*e := by
      rw [ht, Nat.mul_assoc] at he
      exact Nat.eq_of_mul_eq_mul_left hu.pos he
    have hev : e∣v := ⟨t, by rw [hve]; ring⟩
    have hevEq : e=v := ((Nat.dvd_prime hv).mp hev).resolve_left (by omega)
    left
    rw [hevEq] at he
    exact (Nat.eq_of_mul_eq_mul_right hv.pos he).symm
  · obtain ⟨t, ht⟩ := hue
    have hvt : v=d*t := by
      rw [ht, Nat.mul_left_comm d u t] at he
      exact Nat.eq_of_mul_eq_mul_left hu.pos he
    have hdv : d∣v := ⟨t, hvt⟩
    exact Or.inr (((Nat.dvd_prime hv).mp hdv).resolve_left (by omega))

/-- Identify which supplied residual factor is the active prime order. -/
def selectedOrder {N : ℕ} (h : (ZMod N)ˣ) (R d : ℕ) : ℕ :=
  if h^d=1 then d else R/d

/-- One public power chooses the exact active order from a checked factor
of the residual semiprime. No numerical order is supplied to the routine. -/
theorem selectedOrder_eq_order {N u v d : ℕ} (hu : u.Prime) (hv : v.Prime)
    (h : (ZMod N)ˣ) (horder : (orderOf h).Prime) (hpow : h^(u*v)=1)
    (hd : ProperDivisor (u*v) d) : selectedOrder h (u*v) d=orderOf h := by
  have hdprime : d.Prime := (proper_divisor_prime_product hu hv hd).elim
    (fun he => he ▸ hu) (fun he => he ▸ hv)
  have hquotprime : ((u*v)/d).Prime := by
    rcases proper_divisor_prime_product hu hv hd with he | he
    · rw [he, Nat.mul_div_cancel_left _ hu.pos]; exact hv
    · rw [he, Nat.mul_comm u v, Nat.mul_div_cancel_left _ hv.pos]; exact hu
  unfold selectedOrder
  split_ifs with htest
  · exact ((Nat.prime_dvd_prime_iff_eq horder hdprime).mp
      (orderOf_dvd_of_pow_eq_one htest)).symm
  · have hdiv : orderOf h∣d*((u*v)/d) := by
      rw [Nat.mul_div_cancel' hd.2.2]
      exact orderOf_dvd_of_pow_eq_one hpow
    have hnot : ¬orderOf h∣d := fun hh => htest (orderOf_dvd_iff_pow_eq_one.mp hh)
    have hquot := (horder.dvd_mul.mp hdiv).resolve_left hnot
    exact ((Nat.prime_dvd_prime_iff_eq horder hquotprime).mp hquot).symm

/-- Exact quadratic recovery from a factor of the smaller residual. -/
noncomputable def recoverResidual {N : ℕ} (h : (ZMod N)ˣ) (R d : ℕ) : Option ℕ :=
  SemiprimeCommonOrder.recoverCommon N (selectedOrder h R d)

theorem recoverResidual_sound {N R d f : ℕ} (h : (ZMod N)ˣ)
    (hs : recoverResidual h R d=some f) : ProperDivisor N f :=
  SemiprimeCommonOrder.recoverCommon_sound hs

/-- Local-period information bounds both prime cardinalities directly. -/
theorem kernel_card_bounds {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (g : (ZMod (p*q))ˣ) (hdata : KernelData g B) :
    (2*B)^2<p-1 ∧ (2*B)^2<q-1 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  exact ⟨hdata.2.1.1.trans_le (Nat.le_of_dvd (by have h:=hp.one_lt; omega)
      (ZMod.orderOf_units_dvd_card_sub_one (leftUnit g))),
    hdata.2.1.2.trans_le (Nat.le_of_dvd (by have h:=hq.one_lt; omega)
      (ZMod.orderOf_units_dvd_card_sub_one (rightUnit g)))⟩

/-- Every retained kernel case has an odd input, so its exponent really
contains two and the residual split has the proved half-size reduction. -/
theorem kernel_even_exponent {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 0<B) (g : (ZMod (p*q))ˣ) (hdata : KernelData g B) : 2∣p*q-1 := by
  obtain ⟨hP,hQ⟩ := kernel_card_bounds hp hq g hdata
  have hp2 : p≠2 := by intro he; rw [he] at hP; norm_num at hP; nlinarith
  have hq2 : q≠2 := by intro he; rw [he] at hQ; norm_num at hQ; nlinarith
  obtain ⟨a, ha⟩ := (hp.odd_of_ne_two hp2).mul (hq.odd_of_ne_two hq2)
  exact ⟨a, by omega⟩

/-- A common order is below the cubic width, whichever prime is smaller. -/
theorem common_order_lt_cube {p q B m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hbudget : p*q≤B^6) (hmp : m∣p-1) (hmq : m∣q-1) : m<B^3 := by
  have hpone := hp.one_lt
  have hqone := hq.one_lt
  have hP := Nat.le_of_dvd (show 0<p-1 by have h:=hp.one_lt; omega) hmp
  have hQ := Nat.le_of_dvd (show 0<q-1 by have h:=hq.one_lt; omega) hmq
  rcases le_total p q with hpq | hqp
  · have h := SemiprimeProgressionPrefix.smaller_factor_le_cube hpq hbudget
    omega
  · have h := SemiprimeProgressionPrefix.smaller_factor_le_cube hqp
      (by simpa only [Nat.mul_comm q p] using hbudget)
    omega

/-- Retain the original unit's public smooth projection as a richer
carrier than just the unresolved residual integer. -/
noncomputable def activeUnit {N : ℕ} (g : (ZMod N)ˣ) (B : ℕ) : (ZMod N)ˣ :=
  g^((splitSmall (N-1) B).2.prod)

/-- Complete factor-bearing information of an active rough kernel unit. -/
def ActiveData (p q R : ℕ) (h : (ZMod (p*q))ˣ) : Prop :=
  h^(p*q-1)=1 ∧ h^R=1 ∧ h≠1 ∧ (orderOf h).Prime ∧
    orderOf h∣p-1 ∧ orderOf h∣q-1 ∧ p*q<(orderOf h)^3

/-- Every nontrivial active projection has prime common order. Its
value is still unknown; this theorem does not perform an order search. -/
theorem activeUnit_certificate {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 0<B) (hbudget : p*q≤B^6) (g : (ZMod (p*q))ˣ)
    (hdata : KernelData g B) (hne : activeUnit g B≠1) :
    ActiveData p q (splitSmall (p*q-1) B).1 (activeUnit g B) := by
  let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have hE : 0<p*q-1 := by
    have hN : 4≤p*q := by nlinarith [hp.two_le, hq.two_le]
    omega
  obtain ⟨_, _, hencoded, _, hrough, _⟩ := splitSmall_complete (B:=B) hE
  have hraw : (activeUnit g B)^(p*q-1)=1 := by
    unfold activeUnit
    rw [← pow_mul, Nat.mul_comm _ (p*q-1), pow_mul, hdata.1, one_pow]
  have hpow : (activeUnit g B)^(splitSmall (p*q-1) B).1=1 := by
    unfold activeUnit
    rw [← pow_mul, hencoded, hdata.1]
  have hmp : orderOf (activeUnit g B)∣p-1 := (orderOf_pow_dvd _).trans hdata.2.2.1
  have hmq : orderOf (activeUnit g B)∣q-1 := (orderOf_pow_dvd _).trans hdata.2.2.2
  have horderpos : 1<orderOf (activeUnit g B) := by
    have hpos := orderOf_pos (activeUnit g B)
    have hnot : orderOf (activeUnit g B)≠1 := fun he => hne (orderOf_eq_one_iff.mp he)
    omega
  have hdiv := orderOf_dvd_of_pow_eq_one hpow
  have hbound := common_order_lt_cube hp hq hbudget hmp hmq
  have hB4 : B^3≤B^4 := by nlinarith [Nat.mul_le_mul_left (B^3) (show 1≤B by omega)]
  have hprime : (orderOf (activeUnit g B)).Prime := by
    apply SemiprimeCommonOrder.rough_residual_prime (B:=B) horderpos (by omega)
    intro r hr hd
    exact hrough r hr (hd.trans hdiv)
  have hgt := hrough _ hprime hdiv
  have hcube : p*q<(orderOf (activeUnit g B))^3 := by
    calc
      p*q≤B^6 := hbudget
      _=(B^2)^3 := by ring
      _<(orderOf (activeUnit g B))^3 := Nat.pow_lt_pow_left hgt (by decide)
  exact ⟨hraw, hpow, hne, hprime, hmp, hmq, hcube⟩

/-- The large active residual is necessarily semiprime, rather than
possibly prime. The active common-order bound discharges that ambiguity. -/
theorem active_large_residual_semiprime {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 0<B) (hbudget : p*q≤B^6) (g : (ZMod (p*q))ˣ)
    (hdata : KernelData g B) (hne : activeUnit g B≠1)
    (hlarge : B^4<(splitSmall (p*q-1) B).1) :
    ∃ u v, u.Prime ∧ v.Prime ∧ (splitSmall (p*q-1) B).1=u*v := by
  have hE : 0<p*q-1 := by
    have hN : 4≤p*q := by nlinarith [hp.two_le, hq.two_le]
    omega
  obtain ⟨hpos, hd, _, _, hrough, _⟩ := splitSmall_complete (B:=B) hE
  have hRbudget := (Nat.le_of_dvd hE hd).trans ((Nat.sub_le _ _).trans hbudget)
  have hactive := activeUnit_certificate hp hq hB hbudget g hdata hne
  rcases SemiprimeCommonOrder.rough_residual_cases hpos hRbudget hrough with h1 | hprime | htwo
  · have hpw := hactive.2.1
    rw [h1, pow_one] at hpw
    exact False.elim (hne hpw)
  · have he : orderOf (activeUnit g B)=(splitSmall (p*q-1) B).1 :=
      (Nat.prime_dvd_prime_iff_eq hactive.2.2.2.1 hprime).mp
        (orderOf_dvd_of_pow_eq_one hactive.2.1)
    have hb := common_order_lt_cube hp hq hbudget hactive.2.2.2.2.1 hactive.2.2.2.2.2.1
    rw [he] at hb
    have hB4 : B^3≤B^4 := by nlinarith [Nat.mul_le_mul_left (B^3) (show 1≤B by omega)]
    omega
  · exact htwo

/-- Exact common-order recovery is independent of the proof-side order
of the two primes. The runtime accepts only N and the known modulus. -/
theorem recoverCommon_succeeds {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hm : 0<m) (hmp : m∣p-1) (hmq : m∣q-1) (hN : p*q<m^3) :
    ∃ f, SemiprimeCommonOrder.recoverCommon (p*q) m=some f := by
  rcases le_total p q with hpq | hqp
  · exact ⟨p, SemiprimeCommonOrder.recoverCommon_semiprime hp hq hpq hm hmp hmq hN⟩
  · have hs := SemiprimeCommonOrder.recoverCommon_semiprime hq hp hqp hm hmq hmp
      (by simpa only [Nat.mul_comm q p] using hN)
    exact ⟨q, by simpa only [Nat.mul_comm q p] using hs⟩

/-- Any checked factor of the smaller residual transports to a proper
factor of the original input, through one public order-selection power. -/
theorem recoverResidual_semiprime {p q R u v d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hu : u.Prime) (hv : v.Prime) (hR : R=u*v) (h : (ZMod (p*q))ˣ)
    (hdata : ActiveData p q R h) (hd : ProperDivisor R d) :
    ∃ f, recoverResidual h R d=some f := by
  have he : selectedOrder h R d=orderOf h := by
    subst R
    exact selectedOrder_eq_order hu hv h hdata.2.2.2.1 hdata.2.1 hd
  unfold recoverResidual
  rw [he]
  exact recoverCommon_succeeds hp hq hdata.2.2.2.1.pos
    hdata.2.2.2.2.1 hdata.2.2.2.2.2.1 hdata.2.2.2.2.2.2

/-- The smooth projection's trivial branch obtains the exact original
common order from the retained list, then uses one quadratic candidate. -/
theorem smooth_kernel_recovers {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hbudget : p*q≤B^6) (g : (ZMod (p*q))ˣ)
    (hdata : KernelData g B) (hsmooth : activeUnit g B=1) :
    ∃ d, SemiprimeCommonOrder.recoverCommon (p*q)
      (orderFromPrimes g (splitSmall (p*q-1) B).2)=some d := by
  let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have hE : 0<p*q-1 := by
    have hN : 4≤p*q := by nlinarith [hp.two_le, hq.two_le]
    omega
  have hlist := (splitSmall_complete (B:=B) hE).2.2.2.1
  have hm : orderFromPrimes g (splitSmall (p*q-1) B).2=orderOf g :=
    orderFromPrimes_eq_order g (fun r hr => (hlist r hr).1) hsmooth
  have hleft : orderOf (leftUnit g)∣orderOf g := by
    apply orderOf_dvd_of_pow_eq_one
    simpa only [leftUnit, map_pow, map_one] using
      congrArg (Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom)
        (pow_orderOf_eq_one g)
  have hglobal := hdata.2.1.1.trans_le (Nat.le_of_dvd (orderOf_pos g) hleft)
  have hlarge : B^2<orderOf g := by nlinarith
  have hcube : p*q<(orderOf g)^3 := by
    calc
      p*q≤B^6 := hbudget
      _=(B^2)^3 := by ring
      _<(orderOf g)^3 := Nat.pow_lt_pow_left hlarge (by decide)
  rw [hm]
  exact recoverCommon_succeeds hp hq (orderOf_pos g) hdata.2.2.1 hdata.2.2.2 hcube

/-- A factor, or one smaller residual with its retained active unit and
the actual child routing result. No child solver is assumed free. -/
inductive KernelRoute (N : ℕ) where
  | factor (d : ℕ)
  | residual (R : ℕ) (original active : (ZMod N)ˣ) (primes : List ℕ)
      (child : SemiprimeLocalOrderRouting.Route)
  | unresolved

/-- The complete certificate of a residual task, retaining its transport
back to the original input as well as the child result. -/
def GoodKernel (p q : ℕ) : KernelRoute (p*q) → Prop
  | .factor d => ProperDivisor (p*q) d
  | .residual R g h primes child => 2*R<p*q ∧
      (g^(p*q-1)=1 ∧ h=g^primes.prod ∧ primes.prod*R=p*q-1 ∧
        ∀ r∈primes, r.Prime) ∧
      (∃ u v, u.Prime ∧ v.Prime ∧ R=u*v ∧
        SemiprimeLocalOrderRouting.GoodRoute u v
          (SemiprimeLehmanCoverage.sixthWidth R) child) ∧ ActiveData p q R h
  | .unresolved => False

/-- Preserve an independently checked factor option in the kernel route. -/
def kernelFactor {N : ℕ} : Option ℕ → KernelRoute N
  | some d => .factor d
  | none => .unresolved

/-- Public kernel handling uses one cached split, known-prime powers,
and at most one smaller-input public routing call. -/
noncomputable def kernelRoute {N : ℕ} (g : (ZMod N)ˣ) (B : ℕ) : KernelRoute N :=
  let split := splitSmall (N-1) B
  let h := g^split.2.prod
  if h=1 then
    kernelFactor (SemiprimeCommonOrder.recoverCommon N (orderFromPrimes g split.2))
  else if split.1≤B^4 then kernelFactor (SemiprimeCommonOrder.recoverCommon N split.1) else
    match SemiprimeLocalOrderRouting.publicRoute split.1 with
    | .factor d => kernelFactor (recoverResidual h split.1 d)
    | child => .residual split.1 g h split.2 child

/-- Every certified kernel is factored or routed to a certified semiprime
below half the original input, with a proved factor-transport carrier. -/
theorem kernelRoute_semiprime {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 0<B) (hbudget : p*q≤B^6) (g : (ZMod (p*q))ˣ)
    (hdata : KernelData g B) : GoodKernel p q (kernelRoute g B) := by
  have hN : 4≤p*q := by nlinarith [hp.two_le, hq.two_le]
  have hE : 0<p*q-1 := by omega
  have hB2 : 2≤B := by
    by_contra hn
    have hB1 : B≤1 := by omega
    have hb : B^6≤1 := (Nat.pow_le_pow_left hB1 6).trans (by norm_num)
    omega
  obtain ⟨hRpos, _, hencoded, hknown, hrough, _⟩ := splitSmall_complete (B:=B) hE
  unfold kernelRoute
  dsimp only
  rw [← activeUnit]
  by_cases hsmooth : activeUnit g B=1
  · rw [if_pos hsmooth]
    obtain ⟨d, hd⟩ := smooth_kernel_recovers hp hq hbudget g hdata hsmooth
    rw [hd]
    exact SemiprimeCommonOrder.recoverCommon_sound hd
  · rw [if_neg hsmooth]
    have hactive := activeUnit_certificate hp hq hB hbudget g hdata hsmooth
    by_cases hsmall : (splitSmall (p*q-1) B).1≤B^4
    · rw [if_pos hsmall]
      have hR1 : 1<(splitSmall (p*q-1) B).1 := by
        have hnot : (splitSmall (p*q-1) B).1≠1 := by
          intro he
          have hpow := hactive.2.1
          rw [he, pow_one] at hpow
          exact hsmooth hpow
        omega
      have hprime := SemiprimeCommonOrder.rough_residual_prime hR1 hsmall hrough
      have he : orderOf (activeUnit g B)=(splitSmall (p*q-1) B).1 :=
        (Nat.prime_dvd_prime_iff_eq hactive.2.2.2.1 hprime).mp
          (orderOf_dvd_of_pow_eq_one hactive.2.1)
      obtain ⟨f,hf⟩ := recoverCommon_succeeds hp hq hprime.pos
        (he ▸ hactive.2.2.2.2.1) (he ▸ hactive.2.2.2.2.2.1)
        (he ▸ hactive.2.2.2.2.2.2)
      rw [hf]
      exact SemiprimeCommonOrder.recoverCommon_sound hf
    · rw [if_neg hsmall]
      obtain ⟨u,v,hu,hv,hR⟩ := active_large_residual_semiprime hp hq hB hbudget g hdata
        hsmooth (by omega)
      have hhalf := splitSmall_half_bound (show 2<p*q by omega)
        (kernel_even_exponent hp hq hB g hdata) hB2
      have hsource : g^(p*q-1)=1 ∧ activeUnit g B=g^(splitSmall (p*q-1) B).2.prod ∧
          (splitSmall (p*q-1) B).2.prod*(splitSmall (p*q-1) B).1=p*q-1 ∧
          ∀ r∈(splitSmall (p*q-1) B).2, r.Prime :=
        ⟨hdata.1, rfl, hencoded, fun r hr => (hknown r hr).1⟩
      have hchild : SemiprimeLocalOrderRouting.GoodRoute u v
          (SemiprimeLehmanCoverage.sixthWidth (splitSmall (p*q-1) B).1)
          (SemiprimeLocalOrderRouting.publicRoute (splitSmall (p*q-1) B).1) := by
        rw [hR]
        exact SemiprimeLocalOrderRouting.publicRoute_semiprime hu hv
      cases hr : SemiprimeLocalOrderRouting.publicRoute (splitSmall (p*q-1) B).1 with
      | factor d =>
        rw [hr] at hchild
        have hd : ProperDivisor (splitSmall (p*q-1) B).1 d := by
          rw [hR]
          exact hchild
        obtain ⟨f,hf⟩ := recoverResidual_semiprime hp hq hu hv hR (activeUnit g B) hactive hd
        dsimp only
        rw [hf]
        exact recoverResidual_sound (activeUnit g B) hf
      | kernelBase k =>
        rw [hr] at hchild
        exact ⟨hhalf, hsource, ⟨u,v,hu,hv,hR,hchild⟩, hactive⟩
      | longBase k =>
        rw [hr] at hchild
        exact ⟨hhalf, hsource, ⟨u,v,hu,hv,hR,hchild⟩, hactive⟩
      | unresolved =>
        rw [hr] at hchild
        exact False.elim hchild

/-- Every factor of a pending residual can be transported using the
retained active unit. This is recovery correctness, not a free child solve. -/
theorem residual_transport {p q R : ℕ} (hp : p.Prime) (hq : q.Prime)
    (g h : (ZMod (p*q))ˣ) (primes : List ℕ) (child : SemiprimeLocalOrderRouting.Route)
    (hgood : GoodKernel p q (.residual R g h primes child)) {d : ℕ} (hd : ProperDivisor R d) :
    ∃ f, recoverResidual h R d=some f ∧ ProperDivisor (p*q) f := by
  obtain ⟨_, _, ⟨u,v,hu,hv,hR,_⟩, hactive⟩ := hgood
  obtain ⟨f,hf⟩ := recoverResidual_semiprime hp hq hu hv hR h hactive hd
  exact ⟨f,hf,recoverResidual_sound h hf⟩

/-- N-only extension of the preceding route; original kernels are handled
by the certified public split and smaller-input procedure. -/
noncomputable def publicRoute (N : ℕ) :
    SemiprimeLocalOrderRouting.Route ⊕ KernelRoute N :=
  match SemiprimeLocalOrderRouting.publicRoute N with
  | .kernelBase k =>
    if hc : k.Coprime N then
      .inr (kernelRoute (ZMod.unitOfCoprime k hc) (SemiprimeLehmanCoverage.sixthWidth N))
    else .inl .unresolved
  | other => .inl other

/-- The original-input kernel branch is eliminated: a result is a factor,
an original projected-long certificate, or a certified smaller residual. -/
def GoodRoute (p q B : ℕ) :
    SemiprimeLocalOrderRouting.Route ⊕ KernelRoute (p*q) → Prop
  | .inl route => SemiprimeLocalOrderRouting.GoodRoute p q B route ∧
      ∀ k, route≠.kernelBase k
  | .inr result => GoodKernel p q result

/-- Universal N-only factor-or-projected-long-or-smaller-semiprime routing.
The smaller task and all bit costs remain charged research obligations. -/
theorem publicRoute_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    GoodRoute p q (SemiprimeLehmanCoverage.sixthWidth (p*q)) (publicRoute (p*q)) := by
  have hbudget := SemiprimeLehmanCoverage.sixthWidth_upper (p*q)
  have hB : 0<SemiprimeLehmanCoverage.sixthWidth (p*q) := by
    by_contra hn
    have he : SemiprimeLehmanCoverage.sixthWidth (p*q)=0 := by omega
    rw [he] at hbudget
    have hpos := Nat.mul_pos hp.pos hq.pos
    norm_num only [zero_pow (by decide : 6≠0)] at hbudget
    omega
  have hprevious := SemiprimeLocalOrderRouting.publicRoute_semiprime hp hq
  unfold publicRoute
  cases hr : SemiprimeLocalOrderRouting.publicRoute (p*q) with
  | factor d =>
    rw [hr] at hprevious
    exact ⟨hprevious, by intro k he; cases he⟩
  | kernelBase k =>
    rw [hr] at hprevious
    obtain ⟨hc,hdata⟩ := hprevious
    dsimp only
    rw [dif_pos hc]
    exact kernelRoute_semiprime hp hq hB hbudget _ hdata
  | longBase k =>
    rw [hr] at hprevious
    exact ⟨hprevious, by intro j he; cases he⟩
  | unresolved =>
    rw [hr] at hprevious
    exact False.elim hprevious

/-- Exact arithmetic for the saved kernel that the preceding rough-order
routine left unresolved. The residual lies beyond the prime-only cutoff. -/
theorem control_residual_arithmetic :
    Nat.Prime 29759 ∧ Nat.Prime 119033 ∧ Nat.Prime 14879 ∧ Nat.Prime 39679 ∧
    29759*119033=3542303047 ∧ 6*590383841=3542303047-1 ∧
    14879*39679=590383841 ∧ 39^6<3542303047 ∧ 3542303047≤40^6 ∧
    40^4<590383841 ∧ 2*590383841<3542303047 := by
  norm_num

set_option maxRecDepth 32768 in
/-- The retained active value distinguishes the two residual prime factors.
These are kernel-checked powers, not supplied orders. -/
theorem control_residual_powers :
    (64 : ZMod (29759*119033))^14879=1 ∧
    (64 : ZMod (29759*119033))^39679≠1 := by
  constructor
  · reduce_mod_char
  · reduce_mod_char
    decide

/-- A child factor 39679 selects the other prime by one public power test. -/
theorem control_residual_selected (g : (ZMod (29759*119033))ˣ)
    (hg : (g : ZMod (29759*119033))=64) :
    selectedOrder g 590383841 39679=14879 := by
  have hnot : g^39679≠1 := by
    intro he
    have hv := congrArg (fun u : (ZMod (29759*119033))ˣ =>
      (u : ZMod (29759*119033))) he
    simp only [Units.val_pow_eq_pow_val, hg, Units.val_one] at hv
    exact control_residual_powers.2 hv
  rw [selectedOrder, if_neg hnot]

/-- The selected common order recovers the original proper factor from a
single quadratic candidate. The child routing computation remains charged. -/
theorem control_residual_recovery (g : (ZMod (29759*119033))ˣ)
    (hg : (g : ZMod (29759*119033))=64) :
    recoverResidual g 590383841 39679=some 29759 := by
  unfold recoverResidual
  rw [control_residual_selected g hg]
  exact SemiprimeCommonOrder.recoverCommon_semiprime
    control_residual_arithmetic.1 control_residual_arithmetic.2.1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end RiemannGaussian.SemiprimeKernelResidual
