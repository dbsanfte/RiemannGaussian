/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeTotientMultipliers
import RiemannGaussian.SemiprimeSharedIntervalJet

/-!
# Exact shared norms for the complete signed multiplier family

One long interval product and its two derivatives replace each row of
individual collision columns. Full blocks and one shared short tail keep
the interval exact; no simple-root range is silently enlarged by padding.
The explicit shared degree/point inputs have B^(3/2) scale. Their native
polynomial backend and the full one-sixth bit theorem remain open.
-/

namespace RiemannGaussian.SemiprimeMultiplierNorm

open scoped BigOperators
open SemiprimeGroupSelection SemiprimeLocalOrderRouting SemiprimeLongPowerRouting
open SemiprimeTotientWindow SemiprimeTotientResidues SemiprimeTotientMultipliers
open SemiprimeIntervalJet SemiprimeSharedIntervalJet SemiprimeCartesianCompletion

/-- The original complete short-exponent interval, with no new padding. -/
def normLength (B : ℕ) : ℕ := (2*B)^2

/-- The public shared baby width for R actual signed centres. -/
def normWidth (B R : ℕ) : ℕ := Nat.sqrt (R*normLength B)+1

/-- Every actual width is positive, including empty groups. -/
theorem normWidth_pos (B R : ℕ) : 0<normWidth B R := by
  unfold normWidth
  omega

/-- Count both polynomial degrees, full-block points and short-tail
points. The tail's roots are shared rather than repeated for every row. -/
def normInputs (B R m : ℕ) : ℕ := m+R*(normLength B/m)+normLength B%m+R

/-- On the public complete family, the chosen width fits inside the
original interval. No long-period buffer is required for an exact tail. -/
theorem normWidth_le_length {B R : ℕ} (hB : 0<B) (hR : R≤2*B) :
    normWidth B R≤normLength B := by
  have hL : 2*B<normLength B := by unfold normLength; nlinarith
  have hpos : 0<normLength B := by unfold normLength; positivity
  have hs : R*normLength B<(normLength B)^2 := by
    nlinarith [Nat.mul_lt_mul_of_pos_right (lt_of_le_of_lt hR hL) hpos]
  have hroot := Nat.sqrt_lt'.mpr hs
  unfold normWidth
  omega

/-- One shared group uses at most four times its actually selected
baby width across both polynomial and point sources. -/
theorem normInputs_bound {B R : ℕ} (hB : 0<B) (hR : R≤2*B) :
    normInputs B R (normWidth B R)≤4*normWidth B R := by
  let m := normWidth B R
  have hm : 0<m := normWidth_pos B R
  have hs : R*normLength B<m*m := by
    simpa only [m,normWidth,pow_two] using Nat.lt_succ_sqrt (R*normLength B)
  have hd := Nat.mul_le_mul_left R (Nat.div_mul_le_self (normLength B) m)
  have hdiv : R*(normLength B/m)<m := by
    apply (Nat.mul_lt_mul_left hm).mp
    nlinarith
  have hRL : R≤normLength B := by
    have hL : 2*B≤normLength B := by unfold normLength; nlinarith
    exact hR.trans hL
  have hRroot : R<m := by
    have h := Nat.le_sqrt'.mpr (show R^2≤R*normLength B by nlinarith)
    dsimp only [m,normWidth]
    omega
  have ht := Nat.mod_lt (normLength B) hm
  change m+R*(normLength B/m)+normLength B%m+R≤4*m
  omega

/-- The squared source bound exposes the actual B^(3/2) full-family
scale; it cannot be mistaken for a linear-width bound. -/
theorem normInputs_squared_bound {B R : ℕ} (hB : 0<B) (hR : R≤2*B) :
    (normInputs B R (normWidth B R))^2≤32*R*normLength B+32 := by
  have hb := normInputs_bound hB hR
  have hs := Nat.sqrt_le' (R*normLength B)
  have hm : (normWidth B R)^2≤2*(R*normLength B)+2 := by
    unfold normWidth
    nlinarith [sq_nonneg ((Nat.sqrt (R*normLength B) : ℤ)-1)]
  nlinarith [Nat.mul_self_le_mul_self hb]

/-- Even the exact-tail reshape's explicit lists cannot be linear in B
for all 2B centres. This restricts this representation, not every norm algorithm. -/
theorem normInputs_full_floor {B m : ℕ} (hB : 0<B) (hm : 0<m) :
    32*B^3<(normInputs B (2*B) m)^2 := by
  have he := Nat.mod_add_div (normLength B) m
  have ht := Nat.mod_lt (normLength B) hm
  have hcover : normLength B<m*(normLength B/m+1) := by nlinarith
  have hp := Nat.mul_lt_mul_of_pos_left hcover (show 0<2*B by omega)
  have hpN : 8*B^3<m*(2*B*(normLength B/m+1)) := by
    calc 8*B^3=2*B*normLength B := by unfold normLength; ring
         _<2*B*(m*(normLength B/m+1)) := hp
         _=m*(2*B*(normLength B/m+1)) := by ring
  have hZ : 32*(B : ℤ)^3<((m : ℤ)+(2*B*(normLength B/m+1) : ℕ))^2 := by
    have hpZ : 8*(B : ℤ)^3<(m : ℤ)*(2*B*(normLength B/m+1) : ℕ) := by exact_mod_cast hpN
    nlinarith [sq_nonneg ((m : ℤ)-(2*B*(normLength B/m+1) : ℕ))]
  have hN : 32*B^3<(m+2*B*(normLength B/m+1))^2 := by exact_mod_cast hZ
  have hle : m+2*B*(normLength B/m+1)≤normInputs B (2*B) m := by
    unfold normInputs
    rw [Nat.mul_add,Nat.mul_one]
    omega
  exact hN.trans_le (Nat.pow_le_pow_left hle 2)

/-- Full shared blocks followed by one exact tail. Product-rule
composition retains the norm and both label channels. -/
noncomputable def exactSharedJet {R : Type*} [CommRing R]
    (alpha : Rˣ) (x : R) (L m : ℕ) : R×R×R :=
  combineJets (sharedBlockedJet alpha x m (L/m))
    (blockJet (alpha : R) x ((L/m)*m) (L%m))

/-- The two shared parts compute the original long interval exactly,
including its zero norm and both derivatives. -/
theorem exactSharedJet_exact {R : Type*} [CommRing R] (alpha : Rˣ) (x : R)
    (L : ℕ) {m : ℕ} (hm : 0<m) :
    exactSharedJet alpha x L m=(intervalProduct (alpha : R) x L,
      targetDerivative (alpha : R) x L,baseDerivative (alpha : R) x L) := by
  have hde : (L/m)*m+L%m=L := by simpa only [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div L m
  rw [exactSharedJet,sharedBlockedJet_exact alpha x hm]
  have hp := intervalProduct_split (alpha : R) x ((L/m)*m) (L%m)
  have hd := targetDerivative_split (alpha : R) x ((L/m)*m) (L%m)
  have he := baseDerivative_split (alpha : R) x ((L/m)*m) (L%m)
  rw [hde] at hp hd he
  exact Prod.ext hp.symm (Prod.ext hd.symm he.symm)

/-- An arbitrary-offset tail is evaluated with one shared short baby
polynomial and its two derivatives. -/
noncomputable def offsetJet {R : Type*} [CommRing R] (alpha : Rˣ) (x : R)
    (o m : ℕ) : R×R×R :=
  let z := x*(((alpha^o)⁻¹ : Rˣ) : R)
  let c := (alpha : R)^o
  let p := intervalProduct (alpha : R) z m
  let d := targetDerivative (alpha : R) z m
  let e := baseDerivative (alpha : R) z m
  (c^m*p,c^m*(((alpha^o)⁻¹ : Rˣ) : R)*d,
    c^m*((o : R)*(m : R)*p+e-(o : R)*z*d))

/-- The shared tail's phase and marked offset recover every original
tail factor and both derivatives, with no nonunit division. -/
theorem offsetJet_exact {R : Type*} [CommRing R] (alpha : Rˣ) (x : R)
    (o : ℕ) {m : ℕ} (hm : 0<m) :
    offsetJet alpha x o m=blockJet (alpha : R) x o m := by
  let z := x*(((alpha^o)⁻¹ : Rˣ) : R)
  have hz : (alpha : R)^o*z=x := by
    dsimp only [z]
    rw [mul_comm x,←mul_assoc,←Units.val_pow_eq_pow_val,←Units.val_mul]
    simp only [mul_inv_cancel,Units.val_one,one_mul]
  have hphase : ((alpha : R)^o)^m*((((alpha^o)⁻¹ : Rˣ) : R))=((alpha : R)^o)^(m-1) := by
    have he : ((alpha : R)^o)^m=((alpha : R)^o)^(m-1)*(alpha : R)^o := by
      rw [←pow_succ,Nat.sub_add_cancel hm]
    rw [he,mul_assoc,←Units.val_pow_eq_pow_val,←Units.val_mul]
    simp only [mul_inv_cancel,Units.val_one,mul_one]
  have hp := blockProduct_rescale (alpha : R) z o m
  have hd := blockTargetDerivative_rescale (alpha : R) z o m
  have he := blockBaseDerivative_rescale (alpha : R) z o hm
  rw [hz] at hp hd he
  unfold offsetJet blockJet
  dsimp only
  rw [hp,hd,he,hphase]

/-- An exact interval norm preserves a nonshared local collision on
either side. This discharges recovery without knowing which prime is smaller. -/
theorem recoverInterval_of_local_root {p q L b t : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (alpha x : (ZMod (p*q))ˣ) (ht : t<L) (hcover : L≤b^2)
    (hLP : L≤orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p) (alpha : ZMod (p*q))))
    (hLQ : L≤orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q) (alpha : ZMod (p*q))))
    (hne : x≠alpha^t)
    (hfield : ZMod.castHom (dvd_mul_right p q) (ZMod p) (x : ZMod (p*q))=
        (ZMod.castHom (dvd_mul_right p q) (ZMod p) (alpha : ZMod (p*q)))^t ∨
      ZMod.castHom (dvd_mul_left q p) (ZMod q) (x : ZMod (p*q))=
        (ZMod.castHom (dvd_mul_left q p) (ZMod q) (alpha : ZMod (p*q)))^t) :
    ∃ d,recoverInterval alpha x L b=some d := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  by_cases hz : intervalProduct (alpha : ZMod (p*q)) (x : ZMod (p*q)) L=0
  · have hu := x.isUnit.mul (saturated_targetDerivative_isUnit hp hq _ _ hLP hLQ hz)
    have hzP := congrArg (ZMod.castHom (dvd_mul_right p q) (ZMod p)) hz
    have hzQ := congrArg (ZMod.castHom (dvd_mul_left q p) (ZMod q)) hz
    rw [intervalProduct_map,map_zero,intervalProduct_zero_iff] at hzP hzQ
    obtain ⟨k,hk,hP⟩ := hzP
    obtain ⟨l,hl,hQ⟩ := hzQ
    have hkl : k≠l := by
      intro he
      have hx : (x : ZMod (p*q))=(alpha : ZMod (p*q))^k :=
        eq_of_prime_reductions hp hq hpq _ _
          (by simpa only [map_pow] using hP) (by simpa only [map_pow,he] using hQ)
      have htk : t=k := by
        rcases hfield with hleft|hright
        · exact pow_injOn_Iio_orderOf (ht.trans_le hLP) (hk.trans_le hLP) (hleft.symm.trans hP)
        · exact pow_injOn_Iio_orderOf (ht.trans_le hLQ) (hk.trans_le hLQ)
            (hright.symm.trans (by simpa only [←he] using hQ))
      exact hne (Units.ext (by simpa only [Units.val_pow_eq_pow_val,htk] using hx))
    obtain ⟨d,hd⟩ := decodedIndex_recovers_distinct_roots hp hq hk hl
      (hLQ.trans (local_unit_period_lt_prime hq (dvd_mul_left q p) alpha).le)
      hcover hkl _ _ hu.unit hu.unit_spec hP hQ
    refine ⟨d,?_⟩
    simp only [recoverInterval,hz,ZMod.val_zero,Nat.gcd_zero_right]
    rw [if_neg (by omega)]
    simp only [ite_true,dif_pos hu]
    exact hd
  · have hproper : ProperDivisor (p*q) ((p*q).gcd
        (intervalProduct (alpha : ZMod (p*q)) (x : ZMod (p*q)) L).val) := by
      rcases hfield with hleft|hright
      · apply proper_gcd_of_reduction (dvd_mul_right p q) hp.one_lt _ hz
        rw [intervalProduct_map,intervalProduct_zero_iff]
        exact ⟨t,ht,hleft⟩
      · apply proper_gcd_of_reduction (dvd_mul_left q p) hq.one_lt _ hz
        rw [intervalProduct_map,intervalProduct_zero_iff]
        exact ⟨t,ht,hright⟩
    refine ⟨(p*q).gcd (intervalProduct (alpha : ZMod (p*q)) (x : ZMod (p*q)) L).val,?_⟩
    unfold recoverInterval
    dsimp only
    rw [if_pos ⟨hproper.1,hproper.2.1⟩]

/-- Every failed long quarter window has a recoverable signed centre
using the exact norm and its two derivatives. -/
theorem exists_recoverable_norm {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h) (hn : recoverQuarter h B=none) :
    ∃ k : ℕ, ∃ negative : Bool, 0<k ∧ k≤B ∧
      ∃ d,recoverInterval h (signedOrbitPoint (h^(quarterCentre (p*q))) k negative)
        (normLength B) (2*B)=some d := by
  obtain ⟨k,t,negative,hk,hkB,ht,hne,hfield⟩ :=
    exists_signed_field_relation hp hq hB hbudget h hc hn
  refine ⟨k,negative,hk,hkB,?_⟩
  have hLP : normLength B≤orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      (h : ZMod (p*q))) := by
    have he : orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p) (h : ZMod (p*q)))=
        orderOf (leftUnit h) := orderOf_units (y:=leftUnit h)
    rw [he]
    exact hc.1.1.le
  have hLQ : normLength B≤orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      (h : ZMod (p*q))) := by
    have he : orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q) (h : ZMod (p*q)))=
        orderOf (rightUnit h) := orderOf_units (y:=rightUnit h)
    rw [he]
    exact hc.1.2.le
  apply recoverInterval_of_local_root hp hq (core_distinct (by omega) h hc) h _ ht
    le_rfl hLP hLQ hne
  rcases hfield with hleft|hright
  · left
    have he := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hleft
    simpa [leftUnit] using he
  · right
    have he := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hright
    simpa [rightUnit] using he

/-- Recover from three actual computed scalars. The long interval is
not reconstructed by this consumer. -/
noncomputable def recoverNormJet {N : ℕ} (x : (ZMod N)ˣ) (b : ℕ)
    (jet : ZMod N×ZMod N×ZMod N) : Option ℕ := by
  classical
  exact
    let d := N.gcd jet.1.val
    if 1<d ∧ d<N then some d
    else if jet.1=0 then
      if h : IsUnit ((x : ZMod N)*jet.2.1) then
        recoverIndex (-((h.unit⁻¹ : (ZMod N)ˣ) : ZMod N)*jet.2.2) b
      else none
    else none

/-- Exact norm channels reproduce the original interval recovery
specification, including saturated and shared rows. -/
theorem recoverNormJet_exact {N L b : ℕ} (alpha x : (ZMod N)ˣ) :
    recoverNormJet x b (intervalProduct (alpha : ZMod N) (x : ZMod N) L,
      targetDerivative (alpha : ZMod N) (x : ZMod N) L,
      baseDerivative (alpha : ZMod N) (x : ZMod N) L)=recoverInterval alpha x L b := rfl

/-- Every returned norm candidate is checked as a proper divisor,
independently of how its three input channels were computed. -/
theorem recoverNormJet_sound {N b d : ℕ} (x : (ZMod N)ˣ)
    (jet : ZMod N×ZMod N×ZMod N) (hf : recoverNormJet x b jet=some d) :
    ProperDivisor N d := by
  unfold recoverNormJet at hf
  dsimp only at hf
  split_ifs at hf with hp _ _
  · have he := Option.some.inj hf
    subst d
    exact ⟨hp.1,hp.2,Nat.gcd_dvd_left _ _⟩
  · exact recoverResidueBatch_sound hf

/-- Keep both signed centre powers as units for the norm denominator.
Only the cached public centre and B construct this list. -/
def unitCentres {N : ℕ} (z : (ZMod N)ˣ) (B : ℕ) : List (ZMod N)ˣ :=
  (List.range B).flatMap fun index => [z^(index+1),(z^(index+1))⁻¹]

/-- The new cache is exactly the previously proved signed residue cache. -/
theorem unitCentres_values {N : ℕ} (z : (ZMod N)ˣ) (B : ℕ) :
    (unitCentres z B).map (fun x : (ZMod N)ˣ => (x : ZMod N))=centreList z B := by
  simp only [unitCentres,centreList,List.map_flatMap,List.map_cons,List.map_nil]

/-- All actual signed multipliers remain in the unit cache. -/
theorem signedPoint_mem_unitCentres {N B k : ℕ} (z : (ZMod N)ˣ)
    (hk : 0<k) (hkB : k≤B) (negative : Bool) :
    signedOrbitPoint z k negative∈unitCentres z B := by
  apply List.mem_flatMap.mpr
  refine ⟨k-1,List.mem_range.mpr (by omega),?_⟩
  have he : k-1+1=k := by omega
  rw [he]
  cases negative <;> simp [signedOrbitPoint]

/-- The unit cache has the same actual 2B length as its residue cache. -/
theorem unitCentres_length {N : ℕ} (z : (ZMod N)ˣ) (B : ℕ) :
    (unitCentres z B).length=2*B := by
  have h := congrArg List.length (unitCentres_values z B)
  simpa only [List.length_map,centreList_length] using h

/-- Stream already-computed labelled norm triples, stopping on the
first proper candidate. -/
noncomputable def recoverNormRows {N : ℕ} (b : ℕ) :
    List ((ZMod N)ˣ×(ZMod N×ZMod N×ZMod N)) → Option ℕ
  | [] => none
  | row::tail => match recoverNormJet row.1 b row.2 with
    | some d => some d
    | none => recoverNormRows b tail

/-- Every successful norm stream returns a proper factor. -/
theorem recoverNormRows_sound {N b d : ℕ}
    (rows : List ((ZMod N)ˣ×(ZMod N×ZMod N×ZMod N)))
    (hf : recoverNormRows b rows=some d) : ProperDivisor N d := by
  induction rows with
  | nil => simp only [recoverNormRows] at hf; contradiction
  | cons row tail ih =>
    rw [recoverNormRows] at hf
    cases hs : recoverNormJet row.1 b row.2 with
    | some f => simp only [hs] at hf; exact recoverNormJet_sound _ _ (hf ▸ hs)
    | none => simp only [hs] at hf; exact ih hf

/-- A successful computed row is reached unless a preceding factor
already ended the stream. -/
theorem recoverNormRows_succeeds {N b : ℕ}
    (rows : List ((ZMod N)ˣ×(ZMod N×ZMod N×ZMod N)))
    {row : (ZMod N)ˣ×(ZMod N×ZMod N×ZMod N)} (hr : row∈rows)
    {f : ℕ} (hf : recoverNormJet row.1 b row.2=some f) :
    ∃ d,recoverNormRows b rows=some d := by
  induction rows with
  | nil => simp only [List.not_mem_nil] at hr
  | cons first tail ih =>
    rw [recoverNormRows]
    cases hs : recoverNormJet first.1 b first.2 with
    | some d => exact ⟨d,rfl⟩
    | none =>
      rcases List.mem_cons.mp hr with he|ht
      · subst row
        rw [hs] at hf
        contradiction
      · exact ih ht

/-- Construct exact shared norms on the cached centre family, including
the shared tail. Local periods and collision indices are not inputs. -/
noncomputable def normRows {N : ℕ} (window : SemiprimeTotientWindow.Source N) (B : ℕ) :
    List ((ZMod N)ˣ×(ZMod N×ZMod N×ZMod N)) :=
  (unitCentres window.target B).map fun x =>
    (x,exactSharedJet window.active (x : ZMod N) (normLength B) (normWidth B (2*B)))

/-- Every failed certified quarter window is recovered by the actual
exact norm rows; all three channels enter the scalar consumer. -/
theorem normRows_complete {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h) (hn : recoverQuarter h B=none) :
    ∃ d,recoverNormRows (2*B) (normRows (buildSource h B) B)=some d := by
  obtain ⟨k,negative,hk,hkB,d,hd⟩ := exists_recoverable_norm hp hq hB hbudget h hc hn
  let x := signedOrbitPoint (h^(quarterCentre (p*q))) k negative
  have hx : x∈unitCentres (h^(quarterCentre (p*q))) B := signedPoint_mem_unitCentres _ hk hkB negative
  have hm : 0<normWidth B (2*B) := normWidth_pos B (2*B)
  let row := (x,exactSharedJet h (x : ZMod (p*q)) (normLength B) (normWidth B (2*B)))
  have hr : row∈normRows (buildSource h B) B := List.mem_map.mpr ⟨x,hx,rfl⟩
  apply recoverNormRows_succeeds _ hr
  simpa only [row,exactSharedJet_exact h _ _ hm,recoverNormJet_exact] using hd

/-- Exactly 2B labelled triples are constructed; individual pair
columns and long interval powers are absent from the retained output. -/
theorem normRows_length {N : ℕ} (window : SemiprimeTotientWindow.Source N) (B : ℕ) :
    (normRows window B).length=2*B := by
  simp only [normRows,List.length_map,unitCentres_length]

/-- The complete explicit shared construction has a cubic squared
input bound, equivalent to B^(3/2) scale rather than the required B scale. -/
theorem normRows_input_bound {B : ℕ} (hB : 0<B) :
    (normInputs B (2*B) (normWidth B (2*B)))^2≤256*B^3+32 := by
  have h := normInputs_squared_bound hB (le_refl (2*B))
  convert h using 1
  unfold normLength
  ring

/-- An actual certified remaining window supplies complete exact-norm
recovery at its public leaf width. -/
theorem windowCertified_norm_complete {N : ℕ} {window : SemiprimeTotientWindow.Source N}
    (hc : WindowCertified window) (hn : window.factor=none) :
    ∃ d,recoverNormRows (2*SemiprimeLehmanCoverage.sixthWidth N)
      (normRows window (SemiprimeLehmanCoverage.sixthWidth N))=some d := by
  cases hc with
  | @remaining p q g h z s hp hq hdata =>
    have hN : 4≤p*q := by nlinarith [hp.two_le,hq.two_le]
    have hcore : CoreData p q (SemiprimeLehmanCoverage.sixthWidth (p*q)) h := by
      rw [hdata.2.1]
      exact projected_core g hdata.1
    exact normRows_complete hp hq (sixthWidth_ge_two hN)
      (SemiprimeLehmanCoverage.sixthWidth_upper _) h hcore hn

/-- Retain the actual remaining norm triples. Successful original
packets skip their construction. -/
noncomputable def packetRows {N : ℕ} (parent : SemiprimeTotientResidues.Packet N) :
    Option (List ((ZMod (SemiprimeKernelDescent.leafInput parent.parent.parent.source))ˣ×
      (ZMod (SemiprimeKernelDescent.leafInput parent.parent.parent.source)×
       ZMod (SemiprimeKernelDescent.leafInput parent.parent.parent.source)×
       ZMod (SemiprimeKernelDescent.leafInput parent.parent.parent.source)))) :=
  match parent.factor with
  | some _ => none
  | none => parent.parent.source.map fun window => normRows window
    (SemiprimeLehmanCoverage.sixthWidth (SemiprimeKernelDescent.leafInput parent.parent.parent.source))

/-- Reuse an old original factor or transport the first exact-norm
factor through all preceding descent frames. -/
noncomputable def factorWithNorm {N : ℕ} (parent : SemiprimeTotientResidues.Packet N)
    (rows : Option (List ((ZMod (SemiprimeKernelDescent.leafInput parent.parent.parent.source))ˣ×
      (ZMod (SemiprimeKernelDescent.leafInput parent.parent.parent.source)×
       ZMod (SemiprimeKernelDescent.leafInput parent.parent.parent.source)×
       ZMod (SemiprimeKernelDescent.leafInput parent.parent.parent.source))))) : Option ℕ :=
  match parent.factor with
  | some d => some d
  | none => match rows with
    | none => none
    | some rows => match recoverNormRows
        (2*SemiprimeLehmanCoverage.sixthWidth (SemiprimeKernelDescent.leafInput parent.parent.parent.source)) rows with
      | none => none
      | some d => transportCandidate parent.parent.parent.source d

/-- Full original-input packet with computed norm triples and the
complete retained preceding public route. -/
structure Packet (N : ℕ) where
  /-- Preceding residue packet, before the expanded multiplier stream. -/
  parent : SemiprimeTotientResidues.Packet N
  /-- Actual norm triples on the preceding remaining leaf. -/
  rows : Option (List ((ZMod (SemiprimeKernelDescent.leafInput parent.parent.parent.source))ˣ×
      (ZMod (SemiprimeKernelDescent.leafInput parent.parent.parent.source)×
       ZMod (SemiprimeKernelDescent.leafInput parent.parent.parent.source)×
       ZMod (SemiprimeKernelDescent.leafInput parent.parent.parent.source))))
  /-- Checked factor of the original input. -/
  factor : Option ℕ

/-- N alone constructs the full exact-norm public specification. The
quadratic multiplier stream is replaced rather than paid before this stage. -/
noncomputable def publicPacket (N : ℕ) : Packet N :=
  let parent := SemiprimeTotientResidues.publicPacket N
  let rows := packetRows parent
  ⟨parent,rows,factorWithNorm parent rows⟩

/-- Every exact-norm public result is proper for the original input. -/
theorem publicPacket_sound {p q d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hf : (publicPacket (p*q)).factor=some d) : ProperDivisor (p*q) d := by
  dsimp only [publicPacket] at hf
  unfold factorWithNorm at hf
  cases hold : (SemiprimeTotientResidues.publicPacket (p*q)).factor with
  | some f =>
    simp only [hold] at hf
    have hproper := SemiprimeTotientResidues.publicPacket_sound hp hq hold
    rwa [Option.some.inj hf] at hproper
  | none =>
    simp only [hold] at hf
    cases hs : packetRows (SemiprimeTotientResidues.publicPacket (p*q)) with
    | none => simp only [hs] at hf; contradiction
    | some rows =>
      simp only [hs] at hf
      cases hd : recoverNormRows
          (2*SemiprimeLehmanCoverage.sixthWidth
            (SemiprimeKernelDescent.leafInput
              (SemiprimeTotientResidues.publicPacket (p*q)).parent.parent.source)) rows with
      | none => simp only [hd] at hf; contradiction
      | some f =>
        simp only [hd] at hf
        exact transportCandidate_sound (SemiprimeKernelDescent.publicTrace_certified hp hq) hf

/-- Exact shared norms factor every semiprime through the public route,
including squares and arbitrary ratios. The complete sixth-root bit price is open. -/
theorem publicPacket_complete {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ∃ d,(publicPacket (p*q)).factor=some d ∧ ProperDivisor (p*q) d := by
  cases hold : (SemiprimeTotientResidues.publicPacket (p*q)).factor with
  | some d =>
    have he : (publicPacket (p*q)).factor=some d := by
      simp only [publicPacket,factorWithNorm,hold]
    exact ⟨d,he,publicPacket_sound hp hq he⟩
  | none =>
    obtain ⟨d,hd,_⟩ | ⟨_,window,hw,hc,hfailed,_⟩ := SemiprimeTotientWindow.publicPacket_cases hp hq
    · have he : (SemiprimeTotientResidues.publicPacket (p*q)).factor=some d := by
        simp only [SemiprimeTotientResidues.publicPacket,factorWithResidue,hd]
      rw [hold] at he
      contradiction
    · obtain ⟨d,hd⟩ := windowCertified_norm_complete hc hfailed
      have hs : packetRows (SemiprimeTotientResidues.publicPacket (p*q))=
          some (normRows window
            (SemiprimeLehmanCoverage.sixthWidth
              (SemiprimeKernelDescent.leafInput
                (SemiprimeTotientWindow.publicPacket (p*q)).parent.source))) := by
        rw [packetRows,hold]
        change (SemiprimeTotientWindow.publicPacket (p*q)).source.map _=_
        rw [hw]
        rfl
      obtain ⟨f,hf,_⟩ := transportCandidate_complete
        (SemiprimeKernelDescent.publicTrace_certified hp hq) (recoverNormRows_sound _ hd)
      have he : (publicPacket (p*q)).factor=some f := by
        simp only [publicPacket,factorWithNorm,hold,hs]
        dsimp only [SemiprimeTotientResidues.publicPacket]
        rw [hd]
        exact hf
      exact ⟨f,he,publicPacket_sound hp hq he⟩

end RiemannGaussian.SemiprimeMultiplierNorm
