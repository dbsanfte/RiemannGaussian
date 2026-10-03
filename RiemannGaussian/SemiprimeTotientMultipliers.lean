/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitPowerWalk
import Mathlib.Data.Finset.Card

/-!
# Signed multiplier coverage of the remaining quarter-offset leaves

Pigeonhole supplies a short signed multiple of the smaller local offset.
Its multiplier is small enough that the corresponding global exponent
cannot wrap. Thus it gives a proper field collision. Only public centre
powers and the existing residue axes enter the detector; local orders are
proof-side witnesses. The expanded target family remains quadratic, and
its fast implicit evaluation and the full one-sixth bit theorem remain open.
-/

namespace RiemannGaussian.SemiprimeTotientMultipliers

open SemiprimeGroupSelection SemiprimeLocalOrderRouting SemiprimeLongPowerRouting
open SemiprimeTotientWindow SemiprimeTotientResidues SemiprimeCartesianCompletion

/-- Equal quotient bins have distance strictly below their positive width. -/
theorem same_bin_distance {a b H : ℕ} (hH : 0<H) (he : a/H=b/H) :
    a-b<H ∧ b-a<H := by
  have ha := Nat.mod_add_div a H
  have hb := Nat.mod_add_div b H
  have hra := Nat.mod_lt a hH
  have hrb := Nat.mod_lt b hH
  rw [he] at ha
  omega

private theorem short_multiple_of_bin_pair {r H d i j K : ℕ}
    (hr : 0<r) (hH : 0<H) (hij : i<j) (hj : j≤K)
    (he : (i*d%r)/H=(j*d%r)/H) :
    ∃ k t : ℕ, 0<k ∧ k≤K ∧ t<H ∧
      (k*d%r=t ∨ r∣k*d+t) := by
  let k := j-i
  let a := i*d%r
  let b := j*d%r
  have hk : 0<k := by dsimp [k]; omega
  have hkK : k≤K := by dsimp [k]; omega
  have hclose := same_bin_distance hH he
  have hmod : (k*d+a)%r=b := by
    dsimp only [a,b]
    rw [Nat.add_mod_mod]
    have hsum : k*d+i*d=j*d := by
      dsimp only [k]
      have h := Nat.sub_add_cancel hij.le
      nlinarith
    rw [hsum]
  have hsum := Nat.mod_add_div (k*d+a) r
  rw [hmod] at hsum
  by_cases hab : a≤b
  · let t := b-a
    have ht : t<H := hclose.2
    have heq : k*d=t+r*((k*d+a)/r) := by dsimp only [t]; omega
    have htr : t<r := by have hb := Nat.mod_lt (j*d) hr; dsimp only [b,t]; omega
    refine ⟨k,t,hk,hkK,ht,Or.inl ?_⟩
    rw [heq,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt htr]
  · let t := a-b
    have ht : t<H := hclose.1
    have heq : k*d+t=r*((k*d+a)/r) := by dsimp only [t]; omega
    exact ⟨k,t,hk,hkK,ht,Or.inr ⟨(k*d+a)/r,heq⟩⟩

/-- A complete bin argument gives a short signed multiple, with its actual
multiplier bound. No order or offset is supplied to a public search. -/
theorem exists_short_signed_multiple {r H : ℕ} (hr : 0<r) (hH : 0<H) (d : ℕ) :
    ∃ k t : ℕ, 0<k ∧ k≤r/H+1 ∧ k*H≤r+H ∧ t<H ∧
      (k*d%r=t ∨ r∣k*d+t) := by
  let K := r/H+1
  have htop : r<K*H := by
    have he := Nat.mod_add_div r H
    have hm := Nat.mod_lt r hH
    dsimp only [K]
    nlinarith
  have hmap : Set.MapsTo (fun i : ℕ => (i*d%r)/H)
      (Finset.range (K+1)) (Finset.range K) := by
    intro i _hi
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hH).mpr
    exact (Nat.mod_lt (i*d) hr).trans htop
  obtain ⟨i,hi,j,hj,hne,he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by simp only [Finset.card_range]; omega :
      (Finset.range K).card<(Finset.range (K+1)).card) hmap
  have hiK : i≤K := by have h := Finset.mem_range.mp hi; omega
  have hjK : j≤K := by have h := Finset.mem_range.mp hj; omega
  have hex : ∃ k t : ℕ, 0<k ∧ k≤K ∧ t<H ∧ (k*d%r=t ∨ r∣k*d+t) := by
    rcases lt_or_gt_of_ne hne with hlt|hgt
    · exact short_multiple_of_bin_pair hr hH hlt hjK he
    · exact short_multiple_of_bin_pair hr hH hgt hiK he.symm
  obtain ⟨k,t,hk,hkK,ht,hrel⟩ := hex
  have hprod : k*H≤r+H := by
    have hm := Nat.mul_le_mul_right H hkK
    have hd := Nat.div_mul_le_self r H
    dsimp only [K] at hm
    nlinarith
  exact ⟨k,t,hk,hkK,hprod,ht,hrel⟩

/-- The actual factor-sum offset retains its quarter-sum bound. -/
theorem quarterOffset_sum_bound (p q : ℕ) : 4*quarterOffset p q≤p+q := by
  have h := Nat.div_mul_le_self (p+q-2*(p*q).sqrt) 4
  unfold quarterOffset
  omega

/-- Multipliers obtained from the smaller local period cannot make the
literal offset wrap around the much larger global period. -/
theorem multiplier_offset_bound {p q B k d : ℕ} (hB : 0<B)
    (hpq : p≤q) (hbudget : p*q≤B^6)
    (hk : k*(2*B)^2≤2*p) (hd : 4*d≤p+q) : k*d≤B^4 := by
  have hprod := Nat.mul_le_mul hk hd
  have hs : 2*p*(p+q)≤4*(p*q) := by
    have hp2 := Nat.mul_le_mul_left p hpq
    nlinarith
  have he : (k*(2*B)^2)*(4*d)=16*(k*d*B^2) := by ring
  rw [he] at hprod
  have hn := hprod.trans hs
  have hsmall : k*d*B^2≤p*q := by omega
  have hmul : (k*d)*B^2≤B^4*B^2 := by
    calc _≤p*q := hsmall
         _≤B^6 := hbudget
         _=B^4*B^2 := by ring
  exact le_of_mul_le_mul_right hmul (pow_pos hB 2)

/-- A smaller factor and its long local period give a bounded multiplier
and a short signed relation. Only the public B is used to enumerate it. -/
theorem smaller_period_short_multiple {p q B r d : ℕ} (hB : 0<B)
    (hpq : p≤q) (hbudget : p*q≤B^6) (hr : (2*B)^2<r)
    (hrp : r≤p-1) (hd : 4*d≤p+q) :
    ∃ k t : ℕ, 0<k ∧ k≤B ∧ t<(2*B)^2 ∧ k*d≤B^4 ∧
      (k*d%r=t ∨ r∣k*d+t) := by
  have hH : 0<(2*B)^2 := pow_pos (by omega) 2
  have hp3 : p≤B^3 := by
    have hs : p^2≤(B^3)^2 := by
      calc p^2=p*p := pow_two p
           _≤p*q := Nat.mul_le_mul_left p hpq
           _≤B^6 := hbudget
           _=(B^3)^2 := by ring
    simpa only [Nat.sqrt_eq'] using Nat.sqrt_le_sqrt hs
  have hrlt : r<B*((2*B)^2) := by
    have hb3 : 0<B^3 := pow_pos hB 3
    have hr3 : r≤B^3 := (hrp.trans (Nat.sub_le p 1)).trans hp3
    have he : B*((2*B)^2)=4*B^3 := by ring
    rw [he]
    omega
  obtain ⟨k,t,hk,hkK,hkH,ht,hrel⟩ :=
    exists_short_signed_multiple (r:=r) (by omega) hH d
  have hdiv : r/((2*B)^2)<B := (Nat.div_lt_iff_lt_mul hH).mpr hrlt
  have hkB : k≤B := by omega
  have hkP : k*(2*B)^2≤2*p := by omega
  exact ⟨k,t,hk,hkB,ht,multiplier_offset_bound hB hpq hbudget hkP hd,hrel⟩

/-- A cached centre power supplies both signed multiplier orientations. -/
def signedOrbitPoint {G : Type*} [Group G] (z : G) (k : ℕ) (negative : Bool) : G :=
  if negative=true then (z^k)⁻¹ else z^k

/-- Signed orbit points commute with the actual local reduction maps. -/
theorem signedOrbitPoint_map {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (z : G) (k : ℕ) (negative : Bool) :
    φ (signedOrbitPoint z k negative)=signedOrbitPoint (φ z) k negative := by
  cases negative <;> simp only [signedOrbitPoint,Bool.false_eq_true,if_false,if_true,
    map_pow,map_inv]

/-- The cached centre point uses the literal offset power when their
already-proved equality is available. -/
theorem signedOrbitPoint_power {G : Type*} [Group G] (h : G) (d k : ℕ)
    (negative : Bool) :
    signedOrbitPoint (h^d) k negative=
      if negative=true then (h^(k*d))⁻¹ else h^(k*d) := by
  simp only [signedOrbitPoint,←pow_mul,Nat.mul_comm d k]

/-- A short signed modular relation gives an actual local group equality. -/
theorem signed_relation_power {G : Type*} [Group G] (h : G) (k d t : ℕ)
    (hrel : k*d%orderOf h=t ∨ orderOf h∣k*d+t) :
    ∃ negative : Bool,signedOrbitPoint (h^d) k negative=h^t := by
  rcases hrel with hmod|hdiv
  · refine ⟨false,?_⟩
    rw [signedOrbitPoint_power]
    simp only [Bool.false_eq_true,if_false]
    have he := pow_mod_orderOf h (k*d)
    rw [hmod] at he
    exact he.symm
  · refine ⟨true,?_⟩
    rw [signedOrbitPoint_power]
    simp only [if_true]
    have he : h^(k*d)*h^t=1 := by
      rw [←pow_add]
      exact orderOf_dvd_iff_pow_eq_one.mp hdiv
    calc (h^(k*d))⁻¹=(h^(k*d))⁻¹*(h^(k*d)*h^t) := by rw [he,mul_one]
         _=h^t := by rw [←mul_assoc,inv_mul_cancel,one_mul]

/-- The retained coprime long local periods give a quantitative global
order bound, rather than a supplied or computed period. -/
theorem core_global_order_lower {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 0<B) (h : (ZMod (p*q))ˣ) (hc : CoreData p q B h) :
    16*B^4<orderOf h := by
  have he := global_order_eq_lcm hp hq (core_distinct hB h hc) h
  rw [hc.2.1.lcm_eq_mul] at he
  rw [he]
  have hn : 0<orderOf (rightUnit h) := orderOf_pos _
  calc 16*B^4=(2*B)^2*(2*B)^2 := by ring
       _≤(2*B)^2*orderOf (rightUnit h) := Nat.mul_le_mul_left _ hc.1.2.le
       _<orderOf (leftUnit h)*orderOf (rightUnit h) :=
         Nat.mul_lt_mul_of_pos_right hc.1.1 hn

/-- A bounded unwrapped multiple cannot equal either short orientation
globally when the literal offset is outside the original window. -/
theorem signed_global_ne {G : Type*} [Group G] (h : G) {B k d t : ℕ}
    (hB : 2≤B) (hM : 16*B^4<orderOf h) (hk : 0<k)
    (hd : (2*B)^2≤d) (ht : t<(2*B)^2) (hkd : k*d≤B^4)
    (negative : Bool) : signedOrbitPoint (h^d) k negative≠h^t := by
  have hb2 : 0<B^2 := pow_pos (by omega) 2
  have hbb : B^2≤B^4 := by
    have he : (B^2)^2=B^4 := by ring
    have hs : B^2≤(B^2)^2 := by nlinarith only [hb2]
    rwa [he] at hs
  have htM : t<orderOf h := by nlinarith
  have hkdM : k*d<orderOf h := by omega
  have hdle : d≤k*d := by nlinarith
  have hsum : k*d+t<orderOf h := by nlinarith
  have hpos : 0<k*d+t := by nlinarith
  rw [signedOrbitPoint_power]
  cases negative with
  | false =>
    simp only [Bool.false_eq_true,if_false]
    intro he
    have hi := pow_injOn_Iio_orderOf (x:=h) hkdM htM he
    omega
  | true =>
    simp only [if_true]
    intro he
    have hp : h^(k*d+t)=1 := by
      rw [pow_add,←he,mul_inv_cancel]
    have hi := pow_injOn_Iio_orderOf (x:=h) hsum (by omega : 0<orderOf h)
      (by simpa only [pow_zero] using hp)
    omega

/-- Every failed quarter window has a signed multiplier relation in at
least one field, with no global equality at that same labelled point. -/
theorem exists_signed_field_relation {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h) (hn : recoverQuarter h B=none) :
    ∃ k t : ℕ, ∃ negative : Bool, 0<k ∧ k≤B ∧ t<(2*B)^2 ∧
      signedOrbitPoint (h^(quarterCentre (p*q))) k negative≠h^t ∧
      (leftUnit (signedOrbitPoint (h^(quarterCentre (p*q))) k negative)=(leftUnit h)^t ∨
       rightUnit (signedOrbitPoint (h^(quarterCentre (p*q))) k negative)=(rightUnit h)^t) := by
  have he := quarter_power_offset hp hq hB hbudget h hc
  have hd : (2*B)^2≤quarterOffset p q := by
    have hg := recoverQuarter_none_gap hp hq hB hbudget h hc hn
    unfold quarterOffset
    omega
  have hsum := quarterOffset_sum_bound p q
  have hM := core_global_order_lower hp hq (by omega) h hc
  have hcards := local_card_divisors hp hq h
  by_cases hpq : p≤q
  · have hrp : orderOf (leftUnit h)≤p-1 :=
      Nat.le_of_dvd (by have hh:=hp.one_lt; omega) hcards.1
    obtain ⟨k,t,hk,hkB,ht,hkd,hrel⟩ := smaller_period_short_multiple (by omega)
      hpq hbudget hc.1.1 hrp hsum
    obtain ⟨negative,hpow⟩ := signed_relation_power (leftUnit h) k (quarterOffset p q) t hrel
    have hne := signed_global_ne h hB hM hk hd ht hkd negative
    rw [he] at hne
    refine ⟨k,t,negative,hk,hkB,ht,hne,Or.inl ?_⟩
    change Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom
      (signedOrbitPoint (h^(quarterCentre (p*q))) k negative)=_
    rw [signedOrbitPoint_map]
    have hh : Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom
        (h^(quarterCentre (p*q)))=(leftUnit h)^(quarterOffset p q) := by
      rw [←he,map_pow]
      rfl
    rw [hh]
    exact hpow
  · have hqp : q≤p := by omega
    have hrq : orderOf (rightUnit h)≤q-1 :=
      Nat.le_of_dvd (by have hh:=hq.one_lt; omega) hcards.2
    obtain ⟨k,t,hk,hkB,ht,hkd,hrel⟩ := smaller_period_short_multiple (by omega)
      hqp (by simpa only [Nat.mul_comm] using hbudget) hc.1.2 hrq (by omega :
        4*quarterOffset p q≤q+p)
    obtain ⟨negative,hpow⟩ := signed_relation_power (rightUnit h) k (quarterOffset p q) t hrel
    have hne := signed_global_ne h hB hM hk hd ht hkd negative
    rw [he] at hne
    refine ⟨k,t,negative,hk,hkB,ht,hne,Or.inr ?_⟩
    change Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom
      (signedOrbitPoint (h^(quarterCentre (p*q))) k negative)=_
    rw [signedOrbitPoint_map]
    have hh : Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom
        (h^(quarterCentre (p*q)))=(rightUnit h)^(quarterOffset p q) := by
      rw [←he,map_pow]
      rfl
    rw [hh]
    exact hpow

/-- Splitting a short exponent into baby and block labels preserves the
exact group equality after the block step is removed. -/
theorem shifted_relation {G : Type*} [Group G] (h z : G) {b i j t : ℕ}
    (hde : i+b*j=t) (hz : z=h^t) : z*(h^(b*j))⁻¹=h^i := by
  rw [hz,←hde,pow_add,mul_assoc,mul_inv_cancel,mul_one]

/-- The signed multiplier's original shifted residual, in the public ring. -/
def multiplierResidual {N : ℕ} (h : (ZMod N)ˣ) (C b k : ℕ)
    (negative : Bool) (i j : ℕ) : ZMod N :=
  ((signedOrbitPoint (h^C) k negative*(h^(b*j))⁻¹ : (ZMod N)ˣ) : ZMod N)-(h^i : ZMod N)

/-- A globally unequal signed point gives a nonzero original shifted
residual; no actual field collision is discarded by the normalization. -/
theorem multiplierResidual_ne_zero {N C b k i j t : ℕ} (h : (ZMod N)ˣ)
    (negative : Bool) (hde : i+b*j=t)
    (hne : signedOrbitPoint (h^C) k negative≠h^t) :
    multiplierResidual h C b k negative i j≠0 := by
  intro hz
  have hu : signedOrbitPoint (h^C) k negative*(h^(b*j))⁻¹=h^i :=
    Units.ext (sub_eq_zero.mp hz)
  have he := congrArg (fun u : (ZMod N)ˣ => u*h^(b*j)) hu
  simp only [mul_assoc,inv_mul_cancel,mul_one,←pow_add] at he
  rw [hde] at he
  exact hne he

/-- Universal proper-pair coverage on every failed long quarter-window
leaf. The multiplier, sign and labels are proof objects, not detector inputs. -/
theorem exists_multiplier_proper_pair {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h) (hn : recoverQuarter h B=none) :
    ∃ k : ℕ, ∃ negative : Bool, ∃ i j : ℕ,
      0<k ∧ k≤B ∧ i<2*B ∧ j<2*B ∧
      ProperDivisor (p*q) ((p*q).gcd (multiplierResidual h (quarterCentre (p*q))
        (2*B) k negative i j).val) := by
  let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  obtain ⟨k,t,negative,hk,hkB,ht,hne,hfield⟩ :=
    exists_signed_field_relation hp hq hB hbudget h hc hn
  let b := 2*B
  let i := t%b
  let j := t/b
  have hb : 0<b := by dsimp [b]; omega
  have hi : i<b := Nat.mod_lt t hb
  have hj : j<b := (Nat.div_lt_iff_lt_mul hb).mpr (by simpa only [b,pow_two] using ht)
  have hde : i+b*j=t := Nat.mod_add_div t b
  have hz := multiplierResidual_ne_zero h negative hde hne
  refine ⟨k,negative,i,j,hk,hkB,hi,hj,?_⟩
  rcases hfield with hleft|hright
  · have hu : leftUnit (signedOrbitPoint (h^(quarterCentre (p*q))) k negative*
        (h^(b*j))⁻¹)=leftUnit (h^i) := by
      change Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom
        (_*_) = Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom (h^i)
      rw [map_mul,map_inv,map_pow,map_pow]
      exact shifted_relation (leftUnit h) _ hde hleft
    have heq := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hu
    have hlocal : ZMod.castHom (dvd_mul_right p q) (ZMod p)
        (multiplierResidual h (quarterCentre (p*q)) b k negative i j)=0 := by
      change ZMod.castHom _ (ZMod p) (_-_)=0
      rw [map_sub]
      exact sub_eq_zero.mpr heq
    exact proper_gcd_of_reduction (dvd_mul_right p q) hp.one_lt _ hz hlocal
  · have hu : rightUnit (signedOrbitPoint (h^(quarterCentre (p*q))) k negative*
        (h^(b*j))⁻¹)=rightUnit (h^i) := by
      change Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom
        (_*_) = Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom (h^i)
      rw [map_mul,map_inv,map_pow,map_pow]
      exact shifted_relation (rightUnit h) _ hde hright
    have heq := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hu
    have hlocal : ZMod.castHom (dvd_mul_left q p) (ZMod q)
        (multiplierResidual h (quarterCentre (p*q)) b k negative i j)=0 := by
      change ZMod.castHom _ (ZMod q) (_-_)=0
      rw [map_sub]
      exact sub_eq_zero.mpr heq
    exact proper_gcd_of_reduction (dvd_mul_left q p) hq.one_lt _ hz hlocal

/-- Cache both orientations of centre multiples k=1,...,B. The only
centre input is the preceding public target, not a hidden local offset. -/
def centreList {N : ℕ} (z : (ZMod N)ˣ) (B : ℕ) : List (ZMod N) :=
  (List.range B).flatMap fun index =>
    [((z^(index+1) : (ZMod N)ˣ) : ZMod N),(((z^(index+1))⁻¹ : (ZMod N)ˣ) : ZMod N)]

/-- Every signed multiplier in the public range is retained in the cache. -/
theorem signedOrbitPoint_mem_centreList {N k B : ℕ} (z : (ZMod N)ˣ)
    (hk : 0<k) (hkB : k≤B) (negative : Bool) :
    ((signedOrbitPoint z k negative : (ZMod N)ˣ) : ZMod N)∈centreList z B := by
  apply List.mem_flatMap.mpr
  refine ⟨k-1,List.mem_range.mpr (by omega),?_⟩
  have he : k-1+1=k := by omega
  rw [he]
  cases negative <;> simp [signedOrbitPoint]

/-- Both orientations have one retained centre per actual multiplier. -/
theorem centreList_length {N : ℕ} (z : (ZMod N)ˣ) (B : ℕ) :
    (centreList z B).length=2*B := by
  induction B with
  | zero => simp only [centreList,List.range_zero,List.flatMap_nil,List.length_nil,Nat.mul_zero]
  | succ B ih =>
    simp only [centreList,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.length_append,List.length_cons,List.length_nil]
    change (centreList z B).length+2=2*(B+1)
    rw [ih]
    omega

/-- Normalize the actual cached giant residues by the cached target
inverse. These are the existing block steps, not newly supplied powers. -/
def cachedSteps {N : ℕ} (window : SemiprimeTotientWindow.Source N) : List (ZMod N) :=
  (windowRoots window).map fun root => ((window.target⁻¹ : (ZMod N)ˣ) : ZMod N)*root

/-- Every original block label is present after the paid normalization. -/
theorem blockStep_mem_cachedSteps {N B j : ℕ} [NeZero N] (h : (ZMod N)ˣ)
    (hj : j<2*B) : (((h^((2*B)*j))⁻¹ : (ZMod N)ˣ) : ZMod N)∈
      cachedSteps (buildSource h B) := by
  apply List.mem_map.mpr
  refine ⟨((h^(quarterCentre N)*(h^((2*B)*j))⁻¹ : (ZMod N)ˣ) : ZMod N),
    shifted_mem_windowRoots h hj,?_⟩
  change (((h^(quarterCentre N))⁻¹ : (ZMod N)ˣ) : ZMod N)*
    ((h^(quarterCentre N)*(h^((2*B)*j))⁻¹ : (ZMod N)ˣ) : ZMod N)=_
  rw [←Units.val_mul]
  congr 1
  rw [←mul_assoc,inv_mul_cancel,one_mul]

/-- Stream one row of scaled targets at a time against the SAME distinct
baby-root set. Successful rows stop the search before later construction. -/
noncomputable def recoverCentreRows {N : ℕ} (roots : Finset (ZMod N))
    (steps : List (ZMod N)) : List (ZMod N) → Option ℕ
  | [] => none
  | centre::tail =>
    match recoverResidueBatch roots (steps.map fun step => centre*step) with
    | some factor => some factor
    | none => recoverCentreRows roots steps tail

/-- Every streamed row result is checked as a proper divisor. -/
theorem recoverCentreRows_sound {N d : ℕ} (roots : Finset (ZMod N))
    (steps centres : List (ZMod N)) (hf : recoverCentreRows roots steps centres=some d) :
    ProperDivisor N d := by
  induction centres with
  | nil => simp only [recoverCentreRows] at hf; contradiction
  | cons centre tail ih =>
    rw [recoverCentreRows] at hf
    cases hs : recoverResidueBatch roots (steps.map fun step => centre*step) with
    | some f =>
      simp only [hs] at hf
      exact recoverResidueBatch_sound (hf ▸ hs)
    | none => simp only [hs] at hf; exact ih hf

/-- A successful listed row is reached unless an earlier proper factor
has already stopped the stream. -/
theorem recoverCentreRows_succeeds {N : ℕ} (roots : Finset (ZMod N))
    (steps centres : List (ZMod N)) {centre : ZMod N} (hc : centre∈centres)
    {f : ℕ} (hf : recoverResidueBatch roots (steps.map fun step => centre*step)=some f) :
    ∃ d,recoverCentreRows roots steps centres=some d := by
  induction centres with
  | nil => simp only [List.not_mem_nil] at hc
  | cons first tail ih =>
    rw [recoverCentreRows]
    cases hs : recoverResidueBatch roots (steps.map fun step => first*step) with
    | some d => exact ⟨d,rfl⟩
    | none =>
      rcases List.mem_cons.mp hc with he|ht
      · subst centre
        rw [hs] at hf
        contradiction
      · exact ih ht

/-- GCD queries in the actual streamed rows, including the possible lazy
deflated-root scan. Each visited row keeps its existing complete price. -/
noncomputable def centreGcdCount {N : ℕ} (roots : Finset (ZMod N))
    (steps : List (ZMod N)) : List (ZMod N) → ℕ
  | [] => 0
  | centre::tail =>
    let targets := steps.map fun step => centre*step
    let cost := recoveryGcdCount N (fun i => residueLeaves roots (i : ZMod N))
      (evaluatedColumns roots targets)
    match recoverResidueBatch roots targets with
    | some _ => cost
    | none => cost+centreGcdCount roots steps tail

/-- Streamed recovery's literal upper bound remains quadratic for the
full multiplier family. Polynomial and target construction are separate. -/
theorem centreGcdCount_bound {N : ℕ} (roots : Finset (ZMod N))
    (steps centres : List (ZMod N)) :
    centreGcdCount roots steps centres≤centres.length*(roots.card+steps.length) := by
  induction centres with
  | nil => simp only [centreGcdCount,List.length_nil,Nat.zero_mul,le_refl]
  | cons centre tail ih =>
    have hc := recoverResidueBatch_gcd_bound roots (steps.map fun step => centre*step)
    simp only [List.length_map] at hc
    rw [centreGcdCount]
    split <;> dsimp only [List.length_cons] <;> nlinarith

/-- The actual compact multiplier source retains three scalar caches,
one distinct root set and its streamed factor result. No pair grid is input. -/
structure MultiplierSource (N : ℕ) where
  /-- Existing baby residues, used as detector roots. -/
  roots : List (ZMod N)
  /-- Normalized existing block-step residues. -/
  steps : List (ZMod N)
  /-- Both orientations of the actual centre powers. -/
  centres : List (ZMod N)
  /-- One deterministic distinct-root set shared by every row. -/
  distinct : Finset (ZMod N)
  /-- The checked factor obtained by the actual row stream. -/
  factor : Option ℕ

/-- Reuse a preceding window and stream the public multiplier range.
All target products and row evaluations still need their own bit price. -/
noncomputable def buildMultiplierSource {N : ℕ}
    (window : SemiprimeTotientWindow.Source N) (B : ℕ) : MultiplierSource N :=
  let roots := windowTargets window
  let steps := cachedSteps window
  let centres := centreList window.target B
  let distinct := roots.toFinset
  ⟨roots,steps,centres,distinct,recoverCentreRows distinct steps centres⟩

/-- Every multiplier-source result is a proper divisor of its actual leaf. -/
theorem buildMultiplierSource_sound {N d B : ℕ} (window : SemiprimeTotientWindow.Source N)
    (hf : (buildMultiplierSource window B).factor=some d) : ProperDivisor N d :=
  recoverCentreRows_sound _ _ _ hf

/-- The compact source contains three 2B-entry lists and at most 2B
distinct polynomial roots. Expanded evaluation points are not free. -/
theorem buildMultiplierSource_budget {N : ℕ} (h : (ZMod N)ˣ) (B : ℕ) :
    (buildMultiplierSource (buildSource h B) B).roots.length=2*B ∧
    (buildMultiplierSource (buildSource h B) B).steps.length=2*B ∧
    (buildMultiplierSource (buildSource h B) B).centres.length=2*B ∧
    (buildMultiplierSource (buildSource h B) B).distinct.card≤2*B := by
  have hr := (buildResidueSource_budget h B).2.1
  have hs := (buildResidueSource_budget h B).1
  change (windowRoots (buildSource h B)).length=2*B at hs
  have hc := centreList_length (h^(quarterCentre N)) B
  refine ⟨hr,?_,hc,?_⟩
  · simpa only [buildMultiplierSource,cachedSteps,List.length_map] using hs
  · exact ((windowTargets (buildSource h B)).toFinset_card_le).trans_eq hr

/-- Every failed long quarter window is recovered by the actual compact
source and row stream. This is universal correctness, not a sixth-root cost. -/
theorem buildMultiplierSource_complete {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h) (hn : recoverQuarter h B=none) :
    ∃ d,(buildMultiplierSource (buildSource h B) B).factor=some d := by
  let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  obtain ⟨k,negative,i,j,hk,hkB,hi,hj,hproper⟩ :=
    exists_multiplier_proper_pair hp hq hB hbudget h hc hn
  let centre : ZMod (p*q) :=
    ((signedOrbitPoint (h^(quarterCentre (p*q))) k negative : (ZMod (p*q))ˣ) : ZMod (p*q))
  let step : ZMod (p*q) := (((h^((2*B)*j))⁻¹ : (ZMod (p*q))ˣ) : ZMod (p*q))
  have hcentre : centre∈centreList (h^(quarterCentre (p*q))) B :=
    signedOrbitPoint_mem_centreList _ hk hkB negative
  have hstep : step∈cachedSteps (buildSource h B) := blockStep_mem_cachedSteps h hj
  have hpoint : centre*step∈(cachedSteps (buildSource h B)).map (fun s => centre*s) :=
    List.mem_map.mpr ⟨step,hstep,rfl⟩
  have hgcd : ProperDivisor (p*q) ((p*q).gcd (centre*step-(h^i : ZMod (p*q))).val) := by
    simpa only [centre,step,multiplierResidual,Units.val_mul] using hproper
  obtain ⟨f,hf⟩ := recoverResidueList_succeeds_of_proper_pair
    (baby_mem_windowTargets h hi) hpoint hgcd
  exact recoverCentreRows_succeeds _ _ _ hcentre hf

/-- The fixed detector polynomial has degree at most 2B. Its evaluation
on all signed multiplier rows still requires an explicit algorithm and price. -/
theorem buildMultiplierSource_degree {N : ℕ} [Nontrivial (ZMod N)]
    (h : (ZMod N)ˣ) (B : ℕ) :
    (rootPolynomial (buildMultiplierSource (buildSource h B) B).distinct id).natDegree≤2*B := by
  have he : (rootPolynomial (buildMultiplierSource (buildSource h B) B).distinct id).natDegree=
      (buildMultiplierSource (buildSource h B) B).distinct.card :=
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card _ _
  rw [he]
  exact (buildMultiplierSource_budget h B).2.2.2

/-- The expanded target family is literally quadratic despite the three
linear caches. A compact description does not make all evaluations free. -/
theorem buildMultiplierSource_expanded_points {N : ℕ} (h : (ZMod N)ˣ) (B : ℕ) :
    (buildMultiplierSource (buildSource h B) B).centres.length*
      (buildMultiplierSource (buildSource h B) B).steps.length=4*B^2 := by
  obtain ⟨_,hs,hc,_⟩ := buildMultiplierSource_budget h B
  rw [hs,hc]
  ring

/-- Every possible visited row, its column GCDs and its lazy leaf scans
retain a conservative 8B² query bound. This is not a sixth-root bound. -/
theorem buildMultiplierSource_gcd_bound {N : ℕ} (h : (ZMod N)ˣ) (B : ℕ) :
    centreGcdCount (buildMultiplierSource (buildSource h B) B).distinct
      (buildMultiplierSource (buildSource h B) B).steps
      (buildMultiplierSource (buildSource h B) B).centres≤8*B^2 := by
  obtain ⟨_,hs,hc,hd⟩ := buildMultiplierSource_budget h B
  have hb := centreGcdCount_bound
    (buildMultiplierSource (buildSource h B) B).distinct
    (buildMultiplierSource (buildSource h B) B).steps
    (buildMultiplierSource (buildSource h B) B).centres
  rw [hs,hc] at hb
  nlinarith

/-- Certification from the actual preceding public route is sufficient
for complete multiplier recovery on its failed window. -/
theorem windowCertified_multiplier_complete {N : ℕ} {window : SemiprimeTotientWindow.Source N}
    (hc : WindowCertified window) (hn : window.factor=none) :
    ∃ d,(buildMultiplierSource window (SemiprimeLehmanCoverage.sixthWidth N)).factor=some d := by
  cases hc with
  | @remaining p q g h z s hp hq hdata =>
    have hN : 4≤p*q := by nlinarith [hp.two_le,hq.two_le]
    have hcore : CoreData p q (SemiprimeLehmanCoverage.sixthWidth (p*q)) h := by
      rw [hdata.2.1]
      exact projected_core g hdata.1
    exact buildMultiplierSource_complete hp hq (sixthWidth_ge_two hN)
      (SemiprimeLehmanCoverage.sixthWidth_upper _) h hcore hn

/-- Refine only a failed original-input residue packet, reusing its
actual window and its public leaf width. -/
noncomputable def packetSource {N : ℕ} (parent : SemiprimeTotientResidues.Packet N) :
    Option (MultiplierSource (SemiprimeKernelDescent.leafInput parent.parent.parent.source)) :=
  match parent.factor with
  | some _ => none
  | none => parent.parent.source.map fun window =>
    buildMultiplierSource window
      (SemiprimeLehmanCoverage.sixthWidth (SemiprimeKernelDescent.leafInput parent.parent.parent.source))

/-- Transport a new proper leaf candidate through every retained parent
frame; a previously recovered original factor is reused directly. -/
noncomputable def factorWithMultiplier {N : ℕ} (parent : SemiprimeTotientResidues.Packet N)
    (source : Option (MultiplierSource (SemiprimeKernelDescent.leafInput parent.parent.parent.source))) :
    Option ℕ :=
  match parent.factor with
  | some d => some d
  | none => match source with
    | none => none
    | some source => match source.factor with
      | none => none
      | some d => transportCandidate parent.parent.parent.source d

/-- Preserve the complete old route, cached window and actual new row
stream alongside the checked original-input factor. -/
structure Packet (N : ℕ) where
  /-- Previous residue packet, including all original descent frames. -/
  parent : SemiprimeTotientResidues.Packet N
  /-- Actual multiplier source on the remaining leaf, when needed. -/
  source : Option (MultiplierSource (SemiprimeKernelDescent.leafInput parent.parent.parent.source))
  /-- Checked factor of the original input. -/
  factor : Option ℕ

/-- The full public specification receives N alone. No factors, orders,
offsets, local witness or preconstructed cache are detector inputs. -/
noncomputable def publicPacket (N : ℕ) : Packet N :=
  let parent := SemiprimeTotientResidues.publicPacket N
  let source := packetSource parent
  ⟨parent,source,factorWithMultiplier parent source⟩

/-- Every new full-route factor is proper for the original input. -/
theorem publicPacket_sound {p q d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hf : (publicPacket (p*q)).factor=some d) : ProperDivisor (p*q) d := by
  dsimp only [publicPacket] at hf
  unfold factorWithMultiplier at hf
  cases hold : (SemiprimeTotientResidues.publicPacket (p*q)).factor with
  | some f =>
    simp only [hold] at hf
    have hproper := SemiprimeTotientResidues.publicPacket_sound hp hq hold
    rwa [Option.some.inj hf] at hproper
  | none =>
    simp only [hold] at hf
    cases hs : packetSource (SemiprimeTotientResidues.publicPacket (p*q)) with
    | none => simp only [hs] at hf; contradiction
    | some source =>
      simp only [hs] at hf
      cases hd : source.factor with
      | none => simp only [hd] at hf; contradiction
      | some f =>
        simp only [hd] at hf
        exact transportCandidate_sound (SemiprimeKernelDescent.publicTrace_certified hp hq) hf

/-- Universal recovery for all semiprimes, including squares and every
factor ratio, through the original N-only route. The row cost remains quadratic. -/
theorem publicPacket_complete {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ∃ d,(publicPacket (p*q)).factor=some d ∧ ProperDivisor (p*q) d := by
  cases hold : (SemiprimeTotientResidues.publicPacket (p*q)).factor with
  | some d =>
    have he : (publicPacket (p*q)).factor=some d := by
      simp only [publicPacket,factorWithMultiplier,hold]
    exact ⟨d,he,publicPacket_sound hp hq he⟩
  | none =>
    obtain ⟨d,hd,_⟩ | ⟨hn,window,hw,hc,hfailed,_⟩ := SemiprimeTotientWindow.publicPacket_cases hp hq
    · have he : (SemiprimeTotientResidues.publicPacket (p*q)).factor=some d := by
        simp only [SemiprimeTotientResidues.publicPacket,factorWithResidue,hd]
      rw [hold] at he
      contradiction
    · obtain ⟨d,hd⟩ := windowCertified_multiplier_complete hc hfailed
      have hs : packetSource (SemiprimeTotientResidues.publicPacket (p*q))=
          some (buildMultiplierSource window
            (SemiprimeLehmanCoverage.sixthWidth
              (SemiprimeKernelDescent.leafInput
                (SemiprimeTotientWindow.publicPacket (p*q)).parent.source))) := by
        rw [packetSource,hold]
        change (SemiprimeTotientWindow.publicPacket (p*q)).source.map _=_
        rw [hw]
        rfl
      obtain ⟨f,hf,_⟩ := transportCandidate_complete
        (SemiprimeKernelDescent.publicTrace_certified hp hq)
        (buildMultiplierSource_sound window hd)
      have he : (publicPacket (p*q)).factor=some f := by
        simp only [publicPacket,factorWithMultiplier,hold,hs,hd]
        exact hf
      exact ⟨f,he,publicPacket_sound hp hq he⟩

/-- The public result is never a failure on any semiprime. This asserts
correctness only; no every-run sixth-root bit price is hidden in the statement. -/
theorem publicPacket_ne_none {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (publicPacket (p*q)).factor≠none := by
  obtain ⟨d,hd,_⟩ := publicPacket_complete hp hq
  rw [hd]
  exact Option.some_ne_none d

/-- Certification bounds the actual three caches and every streamed GCD
query by the remaining leaf's width. It supplies no evaluation bit oracle. -/
theorem windowCertified_multiplier_budget {N : ℕ} {window : SemiprimeTotientWindow.Source N}
    (hc : WindowCertified window) :
    let source := buildMultiplierSource window (SemiprimeLehmanCoverage.sixthWidth N)
    source.roots.length=2*SemiprimeLehmanCoverage.sixthWidth N ∧
    source.steps.length=2*SemiprimeLehmanCoverage.sixthWidth N ∧
    source.centres.length=2*SemiprimeLehmanCoverage.sixthWidth N ∧
    source.distinct.card≤2*SemiprimeLehmanCoverage.sixthWidth N ∧
    centreGcdCount source.distinct source.steps source.centres≤
      8*(SemiprimeLehmanCoverage.sixthWidth N)^2 := by
  cases hc with
  | remaining hp hq hdata =>
    obtain ⟨hr,hs,hc,hd⟩ := buildMultiplierSource_budget _ _
    exact ⟨hr,hs,hc,hd,buildMultiplierSource_gcd_bound _ _⟩

/-- The three actually retained caches stay linear in the ORIGINAL
input's width after every descent; the added query upper bound is quadratic. -/
theorem publicPacket_source_budget {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {source : MultiplierSource
      (SemiprimeKernelDescent.leafInput (publicPacket (p*q)).parent.parent.parent.source)}
    (hs : (publicPacket (p*q)).source=some source) :
    source.roots.length≤2*SemiprimeLehmanCoverage.sixthWidth (p*q) ∧
    source.steps.length≤2*SemiprimeLehmanCoverage.sixthWidth (p*q) ∧
    source.centres.length≤2*SemiprimeLehmanCoverage.sixthWidth (p*q) ∧
    source.distinct.card≤2*SemiprimeLehmanCoverage.sixthWidth (p*q) ∧
    centreGcdCount source.distinct source.steps source.centres≤
      8*(SemiprimeLehmanCoverage.sixthWidth (p*q))^2 := by
  change packetSource (SemiprimeTotientResidues.publicPacket (p*q))=some source at hs
  have hold : (SemiprimeTotientResidues.publicPacket (p*q)).factor=none := by
    cases hf : (SemiprimeTotientResidues.publicPacket (p*q)).factor with
    | none => rfl
    | some d => simp only [packetSource,hf] at hs; contradiction
  obtain ⟨d,hd,_⟩ | ⟨_,window,hw,hc,_,_⟩ := SemiprimeTotientWindow.publicPacket_cases hp hq
  · have he : (SemiprimeTotientResidues.publicPacket (p*q)).factor=some d := by
      simp only [SemiprimeTotientResidues.publicPacket,factorWithResidue,hd]
    rw [hold] at he
    contradiction
  · rw [packetSource,hold] at hs
    change (SemiprimeTotientWindow.publicPacket (p*q)).source.map _=some source at hs
    rw [hw] at hs
    have he := Option.some.inj hs
    rw [←he]
    dsimp only [SemiprimeTotientResidues.publicPacket]
    have hb := windowCertified_multiplier_budget hc
    have hm := SemiprimeKernelDescent.sixthWidth_mono
      (certified_leaf_input_le (SemiprimeKernelDescent.publicTrace_certified hp hq))
    change SemiprimeLehmanCoverage.sixthWidth
      (SemiprimeKernelDescent.leafInput (SemiprimeTotientWindow.publicPacket (p*q)).parent.source)≤
        SemiprimeLehmanCoverage.sixthWidth (p*q) at hm
    obtain ⟨hr,hstep,hcentre,hcard,hgcd⟩ := hb
    exact ⟨hr.le.trans (Nat.mul_le_mul_left 2 hm),
      hstep.le.trans (Nat.mul_le_mul_left 2 hm),
      hcentre.le.trans (Nat.mul_le_mul_left 2 hm),
      hcard.trans (Nat.mul_le_mul_left 2 hm),
      hgcd.trans (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hm 2))⟩

end RiemannGaussian.SemiprimeTotientMultipliers
