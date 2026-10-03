/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMultiplierNorm

/-!
# First nonunit norm and one late derivative recovery

The bounded multiplier witness also controls every preceding signed
centre. None can be a shared global interval root. Consequently the
first nonunit norm is recoverable: retain scalar products on the whole
family, and construct derivative channels only for a saturated winner.
The explicit norm source still has B^(3/2) inputs. GCD-query counts do
not certify polynomial construction or the full one-sixth bit rate.
-/

namespace RiemannGaussian.SemiprimeFirstNorm

open SemiprimeGroupSelection SemiprimeLocalOrderRouting SemiprimeLongPowerRouting
open SemiprimeTotientWindow SemiprimeTotientResidues SemiprimeTotientMultipliers
open SemiprimeIntervalJet SemiprimeMultiplierNorm SemiprimeCartesianCompletion
open SemiprimeSharedIntervalJet

/-- Public index order: positive and negative orientations of each multiplier. -/
def indexedPoint {G : Type*} [Group G] (z : G) (i : ℕ) : G :=
  signedOrbitPoint z (i/2+1) (decide (i%2=1))

/-- Actual list index of either orientation of a positive multiplier. -/
def signedIndex (k : ℕ) (negative : Bool) : ℕ :=
  2*(k-1)+(if negative=true then 1 else 0)

/-- The explicit index preserves the original signed target. -/
theorem indexedPoint_signedIndex {G : Type*} [Group G] (z : G)
    {k : ℕ} (hk : 0<k) (negative : Bool) :
    indexedPoint z (signedIndex k negative)=signedOrbitPoint z k negative := by
  have h0 : (2*(k-1))/2+1=k := by omega
  have h1 : (2*(k-1)+1)/2+1=k := by omega
  have hr0 : (2*(k-1))%2=0 := by omega
  have hr1 : (2*(k-1)+1)%2=1 := by omega
  cases negative with
  | false =>
    simp only [signedIndex,Bool.false_eq_true,if_false,Nat.add_zero,indexedPoint]
    rw [h0,hr0]
    rfl
  | true =>
    simp only [signedIndex,if_true,indexedPoint]
    rw [h1,hr1]
    rfl

/-- Both orientations fit inside the public cache. -/
theorem signedIndex_lt {k B : ℕ} (hk : 0<k) (hkB : k≤B) (negative : Bool) :
    signedIndex k negative<2*B := by
  cases negative <;> simp only [signedIndex,Bool.false_eq_true,if_false,if_true] <;> omega

/-- Earlier public indices have no larger multiplier. -/
theorem indexed_multiplier_le {i k : ℕ} (negative : Bool)
    (hk : 0<k) (hi : i≤signedIndex k negative) : i/2+1≤k := by
  cases negative <;> simp only [signedIndex,Bool.false_eq_true,if_false,if_true] at hi <;> omega

/-- An offset block computed from one shared scalar baby polynomial.
The definition contains no derivative or jet construction. -/
def scalarBlock {R : Type*} [CommRing R] (alpha : Rˣ) (x : R) (o m : ℕ) : R :=
  ((alpha : R)^o)^m*
    intervalProduct (alpha : R) (x*(((alpha^o)⁻¹ : Rˣ) : R)) m

/-- Unit phase rescaling retains every original offset factor. -/
theorem scalarBlock_exact {R : Type*} [CommRing R] (alpha : Rˣ) (x : R) (o m : ℕ) :
    scalarBlock alpha x o m=blockProduct (alpha : R) x o m := by
  let z := x*(((alpha^o)⁻¹ : Rˣ) : R)
  have hz : (alpha : R)^o*z=x := by
    dsimp only [z]
    rw [mul_comm x,←mul_assoc,←Units.val_pow_eq_pow_val,←Units.val_mul]
    simp only [mul_inv_cancel,Units.val_one,one_mul]
  have hp := blockProduct_rescale (alpha : R) z o m
  rw [hz] at hp
  exact hp.symm

/-- Scalar product recurrence over shared full blocks. No derivative
channels are constructed or passed through the recurrence. -/
def scalarBlocks {R : Type*} [CommRing R] (alpha : Rˣ) (x : R) (m : ℕ) : ℕ → R
  | 0 => 1
  | J+1 => scalarBlocks alpha x m J*scalarBlock alpha x (J*m) m

/-- The scalar full-block recurrence is the original exact interval product. -/
theorem scalarBlocks_exact {R : Type*} [CommRing R] (alpha : Rˣ) (x : R) (m J : ℕ) :
    scalarBlocks alpha x m J=intervalProduct (alpha : R) x (J*m) := by
  induction J with
  | zero => simp [scalarBlocks,intervalProduct]
  | succ J ih =>
    rw [scalarBlocks,ih,scalarBlock_exact]
    have hs := intervalProduct_split (alpha : R) x (J*m) m
    rw [Nat.succ_mul]
    exact hs.symm

/-- Full scalar blocks followed by one exact shared scalar tail. -/
def scalarSharedProduct {R : Type*} [CommRing R] (alpha : Rˣ) (x : R) (L m : ℕ) : R :=
  scalarBlocks alpha x m (L/m)*scalarBlock alpha x ((L/m)*m) (L%m)

/-- The scalar-only construction computes the complete original norm
at every width, without padding. The public backend uses positive widths. -/
theorem scalarSharedProduct_exact {R : Type*} [CommRing R] (alpha : Rˣ) (x : R)
    (L m : ℕ) :
    scalarSharedProduct alpha x L m=intervalProduct (alpha : R) x L := by
  have hde : (L/m)*m+L%m=L := by simpa only [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div L m
  rw [scalarSharedProduct,scalarBlocks_exact,scalarBlock_exact]
  have hs := intervalProduct_split (alpha : R) x ((L/m)*m) (L%m)
  rw [hde] at hs
  exact hs.symm

/-- Scalar-only norms agree with the richer three-channel carrier.
The exact channels remain available downstream for the selected row. -/
theorem scalarSharedProduct_eq_jet {R : Type*} [CommRing R] (alpha : Rˣ) (x : R)
    (L : ℕ) {m : ℕ} (hm : 0<m) :
    scalarSharedProduct alpha x L m=(exactSharedJet alpha x L m).1 := by
  rw [scalarSharedProduct_exact alpha x L m,exactSharedJet_exact alpha x L hm]

/-- Exact scalar norm, constructed without either derivative channel. -/
noncomputable def normProduct {N : ℕ} (window : SemiprimeTotientWindow.Source N)
    (B i : ℕ) : ZMod N :=
  scalarSharedProduct window.active ((indexedPoint window.target i : (ZMod N)ˣ) : ZMod N)
    (normLength B) (normWidth B (2*B))

/-- The scalar source is precisely the original interval product. -/
theorem normProduct_exact {N : ℕ} (window : SemiprimeTotientWindow.Source N)
    (B i : ℕ) :
    normProduct window B i=intervalProduct (window.active : ZMod N)
      ((indexedPoint window.target i : (ZMod N)ˣ) : ZMod N) (normLength B) := by
  exact scalarSharedProduct_exact _ _ _ _

/-- Retain the actual public scalar cache before selecting a winner. -/
noncomputable def productCache {N : ℕ} (window : SemiprimeTotientWindow.Source N)
    (B : ℕ) : List (ZMod N) := (List.range (2*B)).map (normProduct window B)

/-- The norm cache has exactly the complete signed family length. -/
theorem productCache_length {N : ℕ} (window : SemiprimeTotientWindow.Source N) (B : ℕ) :
    (productCache window B).length=2*B := by simp only [productCache,List.length_map,List.length_range]

/-- Public cache access agrees with the exact norm at every valid index. -/
theorem productCache_getD {N B i : ℕ} (window : SemiprimeTotientWindow.Source N)
    (hi : i<2*B) : (productCache window B)[i]?.getD 0=normProduct window B i := by
  simp [productCache,hi]

/-- Every inspected norm pays one GCD. The selected index and that
already computed GCD are returned together, with the actual query count. -/
def scanFrom {N : ℕ} (value : ℕ → ZMod N) (start : ℕ) :
    ℕ → Option (ℕ×ℕ)×ℕ
  | 0 => (none,0)
  | fuel+1 =>
    let d := N.gcd (value start).val
    if d=1 then
      let next := scanFrom value (start+1) fuel
      (next.1,next.2+1)
    else (some (start,d),1)

/-- Every selected entry has the retained GCD, lies in the inspected
range and is nonunit. Selection does not use a hidden prime. -/
theorem scanFrom_sound {N : ℕ} (value : ℕ → ZMod N) {start fuel i d : ℕ}
    (hs : (scanFrom value start fuel).1=some (i,d)) :
    start ≤ i ∧ i < start+fuel ∧ d = N.gcd (value i).val ∧ d ≠ 1 := by
  induction fuel generalizing start with
  | zero => simp only [scanFrom] at hs; contradiction
  | succ fuel ih =>
    dsimp only [scanFrom] at hs
    split_ifs at hs with hg
    · obtain ⟨hlo,hhi,hd,hne⟩ := ih hs
      exact ⟨by omega,by omega,hd,hne⟩
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hs)
      exact ⟨le_rfl,by omega,rfl,hg⟩

/-- A nonunit in the public range forces selection at or before its
index, even if an earlier nonunit already stops the scan. -/
theorem scanFrom_exists_le {N : ℕ} (value : ℕ → ZMod N) {start fuel w : ℕ}
    (hwlo : start≤w) (hwhi : w<start+fuel) (hw : N.gcd (value w).val≠1) :
    ∃ i d,(scanFrom value start fuel).1=some (i,d) ∧ i≤w := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
    by_cases hg : N.gcd (value start).val=1
    · have hwne : w≠start := by intro he; subst w; exact hw hg
      obtain ⟨i,d,hs,hi⟩ := ih (start:=start+1) (by omega) (by omega)
      exact ⟨i,d,by simp only [scanFrom,hg,if_true,hs],hi⟩
    · exact ⟨start,N.gcd (value start).val,by simp only [scanFrom,hg,if_false],hwlo⟩

/-- The GCD trace counts at most one query per available norm. -/
theorem scanFrom_gcd_bound {N : ℕ} (value : ℕ → ZMod N) (start fuel : ℕ) :
    (scanFrom value start fuel).2≤fuel := by
  induction fuel generalizing start with
  | zero => simp only [scanFrom]; omega
  | succ fuel ih =>
    dsimp only [scanFrom]
    split_ifs
    · have h := ih (start+1); omega
    · omega

/-- A zero image modulo a nontrivial divisor makes the actual norm
GCD nonunit. No field factor is an input to the scan. -/
theorem reduction_zero_nonunit {N r : ℕ} [NeZero N] (hr : r∣N) (hr1 : 1<r)
    (z : ZMod N) (hz : ZMod.castHom hr (ZMod r) z=0) : N.gcd z.val≠1 := by
  have hv : r∣z.val := by
    apply (ZMod.natCast_eq_zero_iff _ r).mp
    rwa [SemiprimeCentreFreeCover.castHom_val hr]
  have hd := Nat.dvd_gcd hr hv
  intro he
  rw [he] at hd
  have hle := Nat.le_of_dvd (by decide : 0<1) hd
  omega

/-- Every nonunit semiprime norm has an interval root in at least one
prime field. This covers both a proper norm and complete saturation. -/
theorem nonunit_interval_has_root {p q L : ℕ} (hp : p.Prime) (hq : q.Prime)
    (alpha x : (ZMod (p*q))ˣ)
    (hn : (p*q).gcd (intervalProduct (alpha : ZMod (p*q)) (x : ZMod (p*q)) L).val≠1) :
    ∃ t,L>t ∧
      (ZMod.castHom (dvd_mul_right p q) (ZMod p) (x : ZMod (p*q))=
          (ZMod.castHom (dvd_mul_right p q) (ZMod p) (alpha : ZMod (p*q)))^t ∨
       ZMod.castHom (dvd_mul_left q p) (ZMod q) (x : ZMod (p*q))=
          (ZMod.castHom (dvd_mul_left q p) (ZMod q) (alpha : ZMod (p*q)))^t) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  let P := intervalProduct (alpha : ZMod (p*q)) (x : ZMod (p*q)) L
  have hz : ZMod.castHom (dvd_mul_right p q) (ZMod p) P=0 ∨
      ZMod.castHom (dvd_mul_left q p) (ZMod q) P=0 := by
    by_contra he
    have hne := not_or.mp he
    have hu := isUnit_of_prime_reductions hp hq P hne.1 hne.2
    have hc : P.val.Coprime (p*q) := (ZMod.isUnit_iff_coprime P.val (p*q)).mp
      (by simpa only [ZMod.natCast_zmod_val] using hu)
    exact hn hc.symm.gcd_eq_one
  rcases hz with hleft|hright
  · rw [intervalProduct_map,intervalProduct_zero_iff] at hleft
    obtain ⟨t,ht,hroot⟩ := hleft
    exact ⟨t,ht,Or.inl hroot⟩
  · rw [intervalProduct_map,intervalProduct_zero_iff] at hright
    obtain ⟨t,ht,hroot⟩ := hright
    exact ⟨t,ht,Or.inr hroot⟩

/-- Keep the offset-size information in the existing pigeonhole
witness. It controls the whole preceding scan, not only its own row. -/
theorem exists_bounded_field_relation {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h) :
    ∃ k t : ℕ, ∃ negative : Bool, 0<k ∧ k≤B ∧ k*quarterOffset p q≤B^4 ∧
      t<normLength B ∧
      (leftUnit (signedOrbitPoint (h^(quarterCentre (p*q))) k negative)=(leftUnit h)^t ∨
       rightUnit (signedOrbitPoint (h^(quarterCentre (p*q))) k negative)=(rightUnit h)^t) := by
  have he := quarter_power_offset hp hq hB hbudget h hc
  have hsum := quarterOffset_sum_bound p q
  have hcards := local_card_divisors hp hq h
  by_cases hpq : p≤q
  · have hrp : orderOf (leftUnit h)≤p-1 :=
      Nat.le_of_dvd (by have hh:=hp.one_lt; omega) hcards.1
    obtain ⟨k,t,hk,hkB,ht,hkd,hrel⟩ := smaller_period_short_multiple (by omega)
      hpq hbudget hc.1.1 hrp hsum
    obtain ⟨negative,hpow⟩ := signed_relation_power (leftUnit h) k (quarterOffset p q) t hrel
    refine ⟨k,t,negative,hk,hkB,hkd,ht,Or.inl ?_⟩
    change Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom
      (signedOrbitPoint (h^(quarterCentre (p*q))) k negative)=_
    rw [signedOrbitPoint_map,←he,map_pow]
    exact hpow
  · have hqp : q≤p := by omega
    have hrq : orderOf (rightUnit h)≤q-1 :=
      Nat.le_of_dvd (by have hh:=hq.one_lt; omega) hcards.2
    obtain ⟨k,t,hk,hkB,ht,hkd,hrel⟩ := smaller_period_short_multiple (by omega)
      hqp (by simpa only [Nat.mul_comm] using hbudget) hc.1.2 hrq (by omega :
        4*quarterOffset p q≤q+p)
    obtain ⟨negative,hpow⟩ := signed_relation_power (rightUnit h) k (quarterOffset p q) t hrel
    refine ⟨k,t,negative,hk,hkB,hkd,ht,Or.inr ?_⟩
    change Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom
      (signedOrbitPoint (h^(quarterCentre (p*q))) k negative)=_
    rw [signedOrbitPoint_map,←he,map_pow]
    exact hpow

/-- An arbitrary earlier signed point cannot be a global short root
before the bounded witness. This is derived from the retained core. -/
theorem preceding_point_ne {p q B k i t : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h) (hn : recoverQuarter h B=none)
    (hkd : k*quarterOffset p q≤B^4) (hi : i/2+1≤k) (ht : t<normLength B) :
    indexedPoint (h^(quarterCentre (p*q))) i≠h^t := by
  have he := quarter_power_offset hp hq hB hbudget h hc
  have hd : (2*B)^2≤quarterOffset p q := by
    have hg := recoverQuarter_none_gap hp hq hB hbudget h hc hn
    unfold quarterOffset
    omega
  rw [indexedPoint,←he]
  exact signed_global_ne h hB (core_global_order_lower hp hq (by omega) h hc)
    (by omega) hd ht ((Nat.mul_le_mul_right _ hi).trans hkd) _

/-- Complete scalar-cache scan. No long interval powers are rebuilt by the scanner. -/
noncomputable def scanCache {N : ℕ} (window : SemiprimeTotientWindow.Source N) (B : ℕ) :
    Option (ℕ×ℕ)×ℕ :=
  let values := productCache window B
  scanFrom (fun i => values[i]?.getD 0) 0 (2*B)

/-- Every selected cache record carries its exact scalar norm GCD. -/
theorem scanCache_sound {N B i d : ℕ} (window : SemiprimeTotientWindow.Source N)
    (hs : (scanCache window B).1=some (i,d)) :
    i<2*B ∧ d=N.gcd (normProduct window B i).val ∧ d≠1 := by
  obtain ⟨_,hi,hd,hne⟩ := scanFrom_sound _ hs
  have hib : i<2*B := by simpa only [zero_add] using hi
  exact ⟨hib,by simpa only [productCache_getD window hib] using hd,hne⟩

/-- The complete first-norm scan has a linear GCD-query bound. -/
theorem scanCache_gcd_bound {N : ℕ} (window : SemiprimeTotientWindow.Source N) (B : ℕ) :
    (scanCache window B).2≤2*B := scanFrom_gcd_bound _ _ _

/-- Exact derivatives are constructed only on the saturated selected
row. A proper product GCD is already retained by the scan. -/
noncomputable def recoverSelected {N : ℕ} (window : SemiprimeTotientWindow.Source N)
    (B i d : ℕ) : Option ℕ :=
  if 1<d ∧ d<N then some d
  else if normProduct window B i=0 then
    recoverNormJet (indexedPoint window.target i) (2*B)
      (exactSharedJet window.active ((indexedPoint window.target i : (ZMod N)ˣ) : ZMod N)
        (normLength B) (normWidth B 1))
  else none

/-- A selected exact norm has the same recovery meaning as the full
three-channel interval specification, without computing clear-row derivatives. -/
theorem recoverSelected_exact {N B i d : ℕ} (window : SemiprimeTotientWindow.Source N)
    (hd : d=N.gcd (normProduct window B i).val) :
    recoverSelected window B i d=
      recoverInterval window.active (indexedPoint window.target i) (normLength B) (2*B) := by
  subst d
  simp only [recoverSelected,normProduct_exact,exactSharedJet_exact _ _ _ (normWidth_pos B 1),
    recoverNormJet_exact,recoverInterval]
  split_ifs <;> rfl

/-- The first public nonunit norm is always recoverable on an actual
remaining core; no bad shared global row can stop the scan before the witness. -/
theorem first_norm_complete {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h) (hn : recoverQuarter h B=none) :
    ∃ i d f,(scanCache (buildSource h B) B).1=some (i,d) ∧
      recoverSelected (buildSource h B) B i d=some f := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  obtain ⟨k,t,negative,hk,hkB,hkd,ht,hfield⟩ := exists_bounded_field_relation hp hq hB hbudget h hc
  let w := signedIndex k negative
  have hw : w<2*B := signedIndex_lt hk hkB negative
  have hwfield :
      ZMod.castHom (dvd_mul_right p q) (ZMod p) (normProduct (buildSource h B) B w)=0 ∨
      ZMod.castHom (dvd_mul_left q p) (ZMod q) (normProduct (buildSource h B) B w)=0 := by
    rw [normProduct_exact]
    dsimp only [buildSource]
    rw [indexedPoint_signedIndex _ hk]
    rcases hfield with hleft|hright
    · left
      rw [intervalProduct_map,intervalProduct_zero_iff]
      refine ⟨t,ht,?_⟩
      simpa [leftUnit] using congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hleft
    · right
      rw [intervalProduct_map,intervalProduct_zero_iff]
      refine ⟨t,ht,?_⟩
      simpa [rightUnit] using congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hright
  have hwn : (p*q).gcd (normProduct (buildSource h B) B w).val≠1 := by
    rcases hwfield with hleft|hright
    · exact reduction_zero_nonunit (dvd_mul_right p q) hp.one_lt _ hleft
    · exact reduction_zero_nonunit (dvd_mul_left q p) hq.one_lt _ hright
  obtain ⟨i,d,hs,hiw⟩ := scanFrom_exists_le
    (fun i => (productCache (buildSource h B) B)[i]?.getD 0) (by omega : 0≤w)
    (by simpa only [zero_add] using hw) (by simpa only [productCache_getD _ hw] using hwn)
  have hs' : (scanCache (buildSource h B) B).1=some (i,d) := hs
  obtain ⟨hi,hd,hne⟩ := scanCache_sound _ hs'
  have hnP : (p*q).gcd (normProduct (buildSource h B) B i).val≠1 := by omega
  rw [normProduct_exact] at hnP
  obtain ⟨s,hsL,hroot⟩ := nonunit_interval_has_root hp hq h
    (indexedPoint (h^(quarterCentre (p*q))) i) hnP
  have hneGlobal := preceding_point_ne hp hq hB hbudget h hc hn hkd
    (indexed_multiplier_le negative hk hiw) hsL
  have hLP : normLength B≤orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p) (h : ZMod (p*q))) := by
    have he : orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p) (h : ZMod (p*q)))=
        orderOf (leftUnit h) := orderOf_units (y:=leftUnit h)
    rw [he]
    exact hc.1.1.le
  have hLQ : normLength B≤orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q) (h : ZMod (p*q))) := by
    have he : orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q) (h : ZMod (p*q)))=
        orderOf (rightUnit h) := orderOf_units (y:=rightUnit h)
    rw [he]
    exact hc.1.2.le
  obtain ⟨f,hf⟩ := recoverInterval_of_local_root hp hq (core_distinct (by omega) h hc) h _ hsL
    le_rfl hLP hLQ hneGlobal hroot
  exact ⟨i,d,f,hs',by rw [recoverSelected_exact _ hd]; exact hf⟩

/-- A three-channel recovery query trace: one norm GCD, a denominator
GCD on saturation, then at most one existing integer-index recovery. -/
noncomputable def jetGcdCount {N : ℕ} (x : (ZMod N)ˣ) (b : ℕ)
    (jet : ZMod N×ZMod N×ZMod N) : ℕ := by
  classical
  exact
    let d := N.gcd jet.1.val
    if 1<d ∧ d<N then 1
    else if jet.1=0 then
      if hu : IsUnit ((x : ZMod N)*jet.2.1) then
        let s := -((hu.unit⁻¹ : (ZMod N)ˣ) : ZMod N)*jet.2.2
        2+recoveryGcdCount N (fun i => residueLeaves (indexRoots N b).toFinset (i : ZMod N))
          (evaluatedColumns (indexRoots N b).toFinset (indexTargets s b))
      else 2
    else 1

/-- The single late consumer has at most 2b+2 GCD queries. This is a
query bound, not a cost certificate for constructing its polynomial inputs. -/
theorem jetGcdCount_bound {N : ℕ} (x : (ZMod N)ˣ) (b : ℕ)
    (jet : ZMod N×ZMod N×ZMod N) : jetGcdCount x b jet≤2*b+2 := by
  unfold jetGcdCount
  dsimp only
  split_ifs with _ _ hu
  · omega
  · have h := index_recovery_gcd_bound (-((hu.unit⁻¹ : (ZMod N)ˣ) : ZMod N)*jet.2.2) b
    omega
  · omega
  · omega

/-- At most one chosen row receives a derivative jet. Proper product
GCDs use the already computed scan result without this construction. -/
noncomputable def lateJet {N : ℕ} (window : SemiprimeTotientWindow.Source N) (B : ℕ)
    (choice : Option (ℕ×ℕ)) : Option ((ZMod N)ˣ×(ZMod N×ZMod N×ZMod N)) :=
  match choice with
  | none => none
  | some (i,d) =>
    if 1<d ∧ d<N then none
    else if normProduct window B i=0 then
      some (indexedPoint window.target i,
        exactSharedJet window.active ((indexedPoint window.target i : (ZMod N)ˣ) : ZMod N)
          (normLength B) (normWidth B 1))
    else none

/-- A proper selected GCD skips every derivative channel. -/
theorem lateJet_none_of_proper {N B i d : ℕ} (window : SemiprimeTotientWindow.Source N)
    (hd : 1<d ∧ d<N) : lateJet window B (some (i,d))=none := by
  simp [lateJet,hd]

/-- Consume the retained GCD or the one actual late jet. -/
noncomputable def factorFromChoice (N b : ℕ) (choice : Option (ℕ×ℕ))
    (jet : Option ((ZMod N)ˣ×(ZMod N×ZMod N×ZMod N))) : Option ℕ :=
  match choice with
  | none => none
  | some (_,d) => if 1<d ∧ d<N then some d
    else jet.bind (fun row => recoverNormJet row.1 b row.2)

/-- The retained late-jet implementation agrees with selected interval recovery. -/
theorem factorFromChoice_exact {N B i d : ℕ} (window : SemiprimeTotientWindow.Source N) :
    factorFromChoice N (2*B) (some (i,d)) (lateJet window B (some (i,d)))=
      recoverSelected window B i d := by
  unfold factorFromChoice lateJet recoverSelected
  dsimp only
  split_ifs <;> rfl

/-- Full scalar cache, actual selected record and at most one late jet. -/
structure Source (N : ℕ) where
  /-- All original scalar norms; derivatives are absent from the cache. -/
  products : List (ZMod N)
  /-- Selected index/GCD and actual recursive scan query count. -/
  scan : Option (ℕ×ℕ)×ℕ
  /-- Retained derivative channels only for a saturated selected row. -/
  jet : Option ((ZMod N)ˣ×(ZMod N×ZMod N×ZMod N))
  /-- Proper candidate of the current descent leaf. -/
  factor : Option ℕ
  /-- Scan queries plus the optional single consumer query trace. -/
  gcdQueries : ℕ

/-- Construct and consume the actual scalar/late-jet public source.
The chosen derivatives are retained once and passed into their consumer. -/
noncomputable def buildFirstSource {N : ℕ} (window : SemiprimeTotientWindow.Source N)
    (B : ℕ) : Source N :=
  let products := productCache window B
  let scan := scanFrom (fun i => products[i]?.getD 0) 0 (2*B)
  let jet := lateJet window B scan.1
  let factor := factorFromChoice N (2*B) scan.1 jet
  let extra := jet.map (fun row => jetGcdCount row.1 (2*B) row.2)
  ⟨products,scan,jet,factor,scan.2+extra.getD 0⟩

/-- The actual source factor follows exactly its first nonunit choice. -/
theorem buildFirstSource_factor {N : ℕ} (window : SemiprimeTotientWindow.Source N) (B : ℕ) :
    (buildFirstSource window B).factor=
      (scanCache window B).1.bind (fun row => recoverSelected window B row.1 row.2) := by
  dsimp only [buildFirstSource]
  change factorFromChoice N (2*B) (scanCache window B).1
    (lateJet window B (scanCache window B).1)=_
  cases hs : (scanCache window B).1 with
  | none => rfl
  | some row => exact factorFromChoice_exact window

/-- The actual source retains only 2B scalar products before selection. -/
theorem buildFirstSource_products_length {N : ℕ} (window : SemiprimeTotientWindow.Source N) (B : ℕ) :
    (buildFirstSource window B).products.length=2*B := productCache_length window B

/-- The whole actual source uses at most 6B+2 GCD queries. The only
integer-index batch belongs to the one late consumer. -/
theorem buildFirstSource_gcd_bound {N : ℕ} (window : SemiprimeTotientWindow.Source N) (B : ℕ) :
    (buildFirstSource window B).gcdQueries≤6*B+2 := by
  dsimp only [buildFirstSource]
  change (scanCache window B).2+
    ((lateJet window B (scanCache window B).1).map (fun row => jetGcdCount row.1 (2*B) row.2)).getD 0≤_
  have hs := scanCache_gcd_bound window B
  cases hj : lateJet window B (scanCache window B).1 with
  | none => simp only [Option.map_none,Option.getD_none]; omega
  | some row =>
    simp only [Option.map_some,Option.getD_some]
    have h := jetGcdCount_bound row.1 (2*B) row.2
    omega

/-- The one late row has only a quadratic squared degree/point
budget, hence linear-width input scale. The main scalar cache remains larger. -/
theorem lateJet_input_bound {B : ℕ} (hB : 0<B) :
    (normInputs B 1 (normWidth B 1))^2≤128*B^2+32 := by
  have h := normInputs_squared_bound hB (by omega : 1≤2*B)
  convert h using 1
  unfold normLength
  ring

/-- Every actual first-norm source result is a proper leaf factor. -/
theorem buildFirstSource_sound {N B f : ℕ} (window : SemiprimeTotientWindow.Source N)
    (hf : (buildFirstSource window B).factor=some f) : ProperDivisor N f := by
  rw [buildFirstSource_factor] at hf
  cases hs : (scanCache window B).1 with
  | none => simp only [hs,Option.bind_none] at hf; contradiction
  | some row =>
    obtain ⟨_,hd,_⟩ := scanCache_sound window hs
    simp only [hs,Option.bind_some] at hf
    rw [recoverSelected_exact window hd] at hf
    exact recoverInterval_sound _ _ hf

/-- The real first-norm construction factors every failed certified core. -/
theorem buildFirstSource_complete {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h) (hn : recoverQuarter h B=none) :
    ∃ f,(buildFirstSource (buildSource h B) B).factor=some f := by
  obtain ⟨i,d,f,hs,hf⟩ := first_norm_complete hp hq hB hbudget h hc hn
  exact ⟨f,by rw [buildFirstSource_factor,hs]; exact hf⟩

/-- The certified remaining public window discharges every local
first-norm coverage premise at its actual public sixth width. -/
theorem windowCertified_first_complete {N : ℕ} {window : SemiprimeTotientWindow.Source N}
    (hc : WindowCertified window) (hn : window.factor=none) :
    ∃ f,(buildFirstSource window (SemiprimeLehmanCoverage.sixthWidth N)).factor=some f := by
  cases hc with
  | @remaining p q g h z s hp hq hdata =>
    have hN : 4≤p*q := by nlinarith [hp.two_le,hq.two_le]
    have hcore : CoreData p q (SemiprimeLehmanCoverage.sixthWidth (p*q)) h := by
      rw [hdata.2.1]
      exact projected_core g hdata.1
    exact buildFirstSource_complete hp hq (sixthWidth_ge_two hN)
      (SemiprimeLehmanCoverage.sixthWidth_upper _) h hcore hn

/-- Public first-norm source on the retained remaining leaf. -/
noncomputable def packetSource {N : ℕ} (parent : SemiprimeTotientResidues.Packet N) :
    Option (Source (SemiprimeKernelDescent.leafInput parent.parent.parent.source)) :=
  match parent.factor with
  | some _ => none
  | none => parent.parent.source.map fun window => buildFirstSource window
    (SemiprimeLehmanCoverage.sixthWidth (SemiprimeKernelDescent.leafInput parent.parent.parent.source))

/-- The actually retained public source inherits its linear GCD-query
bound at the actual descent leaf's public sixth width. -/
theorem packetSource_gcd_bound {N : ℕ} (parent : SemiprimeTotientResidues.Packet N)
    {source : Source (SemiprimeKernelDescent.leafInput parent.parent.parent.source)}
    (hs : packetSource parent=some source) :
    source.gcdQueries≤6*SemiprimeLehmanCoverage.sixthWidth
      (SemiprimeKernelDescent.leafInput parent.parent.parent.source)+2 := by
  unfold packetSource at hs
  cases hp : parent.factor with
  | some d => simp only [hp] at hs; contradiction
  | none =>
    simp only [hp] at hs
    cases hw : parent.parent.source with
    | none => simp only [hw,Option.map_none] at hs; contradiction
    | some window =>
      simp only [hw,Option.map_some] at hs
      obtain rfl := Option.some.inj hs
      exact buildFirstSource_gcd_bound window _

/-- Preserve preceding successes or transport the first norm candidate
through every original descent frame. -/
noncomputable def factorWithFirstNorm {N : ℕ} (parent : SemiprimeTotientResidues.Packet N)
    (source : Option (Source (SemiprimeKernelDescent.leafInput parent.parent.parent.source))) : Option ℕ :=
  match parent.factor with
  | some d => some d
  | none => match source with
    | none => none
    | some source => source.factor.bind (transportCandidate parent.parent.parent.source)

/-- Original-input public packet retaining the full preceding route. -/
structure Packet (N : ℕ) where
  /-- Public preceding packet, before expanded rows or three-channel norms. -/
  parent : SemiprimeTotientResidues.Packet N
  /-- Scalar cache and at most one late jet on the actual remaining leaf. -/
  source : Option (Source (SemiprimeKernelDescent.leafInput parent.parent.parent.source))
  /-- Proper candidate of the original input. -/
  factor : Option ℕ

/-- N alone constructs the complete first-norm public specification. -/
noncomputable def publicPacket (N : ℕ) : Packet N :=
  let parent := SemiprimeTotientResidues.publicPacket N
  let source := packetSource parent
  ⟨parent,source,factorWithFirstNorm parent source⟩

/-- Every public first-norm output is proper for the original input. -/
theorem publicPacket_sound {p q d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hf : (publicPacket (p*q)).factor=some d) : ProperDivisor (p*q) d := by
  dsimp only [publicPacket] at hf
  unfold factorWithFirstNorm at hf
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
      | none => simp only [hd,Option.bind_none] at hf; contradiction
      | some f =>
        simp only [hd,Option.bind_some] at hf
        exact transportCandidate_sound (SemiprimeKernelDescent.publicTrace_certified hp hq) hf

/-- The first-norm route factors every semiprime, including squares
and arbitrary ratios. The universal one-sixth bit theorem remains open. -/
theorem publicPacket_complete {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ∃ d,(publicPacket (p*q)).factor=some d ∧ ProperDivisor (p*q) d := by
  cases hold : (SemiprimeTotientResidues.publicPacket (p*q)).factor with
  | some d =>
    have he : (publicPacket (p*q)).factor=some d := by
      simp only [publicPacket,factorWithFirstNorm,hold]
    exact ⟨d,he,publicPacket_sound hp hq he⟩
  | none =>
    obtain ⟨d,hd,_⟩ | ⟨_,window,hw,hc,hfailed,_⟩ := SemiprimeTotientWindow.publicPacket_cases hp hq
    · have he : (SemiprimeTotientResidues.publicPacket (p*q)).factor=some d := by
        simp only [SemiprimeTotientResidues.publicPacket,factorWithResidue,hd]
      rw [hold] at he
      contradiction
    · obtain ⟨d,hd⟩ := windowCertified_first_complete hc hfailed
      have hs : packetSource (SemiprimeTotientResidues.publicPacket (p*q))=
          some (buildFirstSource window
            (SemiprimeLehmanCoverage.sixthWidth
              (SemiprimeKernelDescent.leafInput
                (SemiprimeTotientWindow.publicPacket (p*q)).parent.source))) := by
        rw [packetSource,hold]
        change (SemiprimeTotientWindow.publicPacket (p*q)).source.map _=_
        rw [hw]
        rfl
      obtain ⟨f,hf,_⟩ := transportCandidate_complete
        (SemiprimeKernelDescent.publicTrace_certified hp hq) (buildFirstSource_sound _ hd)
      have he : (publicPacket (p*q)).factor=some f := by
        simp only [publicPacket,factorWithFirstNorm,hold,hs]
        dsimp only [SemiprimeTotientResidues.publicPacket]
        rw [hd]
        exact hf
      exact ⟨f,he,publicPacket_sound hp hq he⟩

end RiemannGaussian.SemiprimeFirstNorm
