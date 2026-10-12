/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorCrossUnitCancellation
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Native p-free binomial units: exact recurrence and source gate

Extraction retains every carry valuation. It never replaces a binomial
unit by its possibly zero raw residue. The exact two-column recurrence
keeps both unit endpoints and every actual divisibility crossing.
Nonresonant internal Fourier codes are therefore source-small, not new
zero detectors. No nonlinear hypothetical-zero source is inferred for
the resonant or microscopic-frequency unit trace.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical Topology
namespace RiemannGaussian.ArithmeticOperatorPFreeUnitAudit
open Complex Filter ArithmeticOperatorCrossUnitCancellation

/-- The literal integer after removing its complete p-adic valuation. -/
def unitPart (p n : ℕ) : ℕ := n / p ^ padicValNat p n

theorem valuation_unit_reconstruction (p n : ℕ) :
    p ^ padicValNat p n * unitPart p n=n := by
  exact Nat.mul_div_cancel' pow_padicValNat_dvd

theorem unitPart_pos {p n : ℕ} (hp : p.Prime) (hn : 0<n) : 0<unitPart p n := by
  exact Nat.div_pos (Nat.le_of_dvd hn pow_padicValNat_dvd) (Nat.pow_pos hp.pos)

theorem unitPart_not_dvd {p n : ℕ} (hp : p.Prime) (hn : n≠0) : ¬p∣unitPart p n := by
  let : Fact p.Prime := ⟨hp⟩
  intro hd
  apply pow_succ_padicValNat_not_dvd (p := p) hn
  have hr := valuation_unit_reconstruction p n
  have hd' : p^(padicValNat p n+1)∣p^padicValNat p n*unitPart p n := by
    simpa only [pow_succ] using mul_dvd_mul_left (p^padicValNat p n) hd
  rwa [hr] at hd'

theorem unitPart_of_not_dvd {p n : ℕ} (h : ¬p∣n) : unitPart p n=n := by
  simp [unitPart,padicValNat.eq_zero_of_not_dvd h]

theorem unitPart_mul {p a b : ℕ} (hp : p.Prime) (ha : a≠0) (hb : b≠0) :
    unitPart p (a*b)=unitPart p a*unitPart p b := by
  let : Fact p.Prime := ⟨hp⟩
  apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hp.pos)
  calc
    _ = a*b := valuation_unit_reconstruction p (a*b)
    _ = (p^padicValNat p a*unitPart p a)*(p^padicValNat p b*unitPart p b) := by
      rw [valuation_unit_reconstruction,valuation_unit_reconstruction]
    _ = p^padicValNat p (a*b)*(unitPart p a*unitPart p b) := by
      rw [padicValNat.mul ha hb,pow_add]
      ring

/-- Exact adjacent carry balance, stated additively to avoid truncating a valuation drop. -/
theorem choose_valuation_balance {p n k : ℕ} (hp : p.Prime) (hk : k<n) :
    padicValNat p (n.choose (k+1))+padicValNat p (k+1)=
      padicValNat p (n.choose k)+padicValNat p (n-k) := by
  let : Fact p.Prime := ⟨hp⟩
  have h := congrArg (padicValNat p) (Nat.choose_succ_right_eq n k)
  rw [padicValNat.mul (Nat.choose_ne_zero (by omega)) (by omega),
    padicValNat.mul (Nat.choose_ne_zero hk.le) (by omega)] at h
  exact h

/-- The full integer recurrence, including actual jump factors. -/
theorem choose_unit_recurrence {p n k : ℕ} (hp : p.Prime) (hk : k<n) :
    unitPart p (n.choose (k+1))*unitPart p (k+1)=
      unitPart p (n.choose k)*unitPart p (n-k) := by
  have h := congrArg (unitPart p) (Nat.choose_succ_right_eq n k)
  rw [unitPart_mul hp (Nat.choose_ne_zero (by omega)) (by omega),
    unitPart_mul hp (Nat.choose_ne_zero hk.le) (by omega)] at h
  exact h

/-- Literal positive-order binomial unit; zero raw residues are not removed. -/
def binomialUnit (p D k : ℕ) : ℕ := unitPart p ((D-1).choose k)

theorem binomialUnit_zero (p D : ℕ) : binomialUnit p D 0=1 := by
  simp [binomialUnit,unitPart]

theorem binomialUnit_last (p D : ℕ) : binomialUnit p D (D-1)=1 := by
  simp [binomialUnit,unitPart]

theorem binomialUnit_ne_zero_mod {p D k : ℕ} (hp : p.Prime) (hk : k≤D-1) :
    (binomialUnit p D k : ZMod p)≠0 := by
  exact fun h => unitPart_not_dvd hp (Nat.choose_ne_zero hk)
    ((ZMod.natCast_eq_zero_iff _ _).mp h)

theorem before_crossing_not_dvd {p D k : ℕ} (hD : 0<D) (hpd : p∣D)
    (hk : k<D-1) (hpk : ¬p∣k+1) : ¬p∣D-1-k := by
  intro hd
  have he : (D-1-k)+(k+1)=D := by omega
  apply hpk
  apply (Nat.dvd_add_iff_right hd).mpr
  rwa [he]

/-- Unlike raw Lucas residues, both adjacent p-free columns are units.
The sign recurrence uses the exact n=D-1 congruence only away from jumps. -/
theorem binomialUnit_succ_mod {p D k : ℕ} (hp : p.Prime) (hD : 0<D)
    (hpd : p∣D) (hk : k<D-1) (hpk : ¬p∣k+1) :
    (binomialUnit p D (k+1) : ZMod p)=-(binomialUnit p D k : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  have hn := before_crossing_not_dvd hD hpd hk hpk
  have hr := choose_unit_recurrence hp hk
  rw [unitPart_of_not_dvd hpk,unitPart_of_not_dvd hn] at hr
  have hz := congrArg (fun a : ℕ => (a : ZMod p)) hr
  simp only [Nat.cast_mul] at hz
  have he : (D-1-k)+(k+1)=D := by omega
  have hd : (D : ZMod p)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpd
  have ht : ((D-1-k : ℕ) : ZMod p)=-((k+1 : ℕ) : ZMod p) := by
    have ha := congrArg (fun a : ℕ => (a : ZMod p)) he
    simp only [Nat.cast_add] at ha
    rw [hd] at ha
    exact eq_neg_of_add_eq_zero_left (by simpa only [Nat.cast_add,Nat.cast_one] using ha)
  have hb : ((k+1 : ℕ) : ZMod p)≠0 := by
    exact fun h => hpk ((ZMod.natCast_eq_zero_iff _ _).mp h)
  apply mul_right_cancel₀ hb
  simpa only [ht,mul_neg,neg_mul,binomialUnit] using hz

theorem binomialUnit_valuation_stable {p D k : ℕ} (hp : p.Prime) (hD : 0<D)
    (hpd : p∣D) (hk : k<D-1) (hpk : ¬p∣k+1) :
    padicValNat p ((D-1).choose (k+1))=padicValNat p ((D-1).choose k) := by
  have hv := choose_valuation_balance hp hk
  rw [padicValNat.eq_zero_of_not_dvd hpk,
    padicValNat.eq_zero_of_not_dvd (before_crossing_not_dvd hD hpd hk hpk),
    add_zero,add_zero] at hv
  exact hv

/-- Joined characters of both genuine p-free columns on the same native row. -/
def unitAtom {p q : ℕ} (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q)
    (D k : ℕ) : ℂ := χ (binomialUnit p D k)*η (binomialUnit q D k)

/-- The actual two-character parity; internal coding must use this gap. -/
def resonance {p q : ℕ} (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q) : ℂ :=
  χ (-1)*η (-1)

theorem unitColumn_succ {p D k : ℕ} (hp : p.Prime) (hD : 0<D)
    (hpd : p∣D) (hk : k<D-1) (χ : DirichletCharacter ℂ p) (hpk : ¬p∣k+1) :
    χ (binomialUnit p D (k+1))=χ (-1)*χ (binomialUnit p D k) := by
  rw [binomialUnit_succ_mod hp hD hpd hk hpk]
  rw [show -(binomialUnit p D k : ZMod p)=(-1)*(binomialUnit p D k : ZMod p) by ring,
    map_mul]

theorem unitAtom_succ {p q D k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hD : 0<D) (hpd : p∣D) (hqd : q∣D) (hk : k<D-1)
    (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q)
    (hpk : ¬p∣k+1) (hqk : ¬q∣k+1) :
    unitAtom χ η D (k+1)=resonance χ η*unitAtom χ η D k := by
  unfold unitAtom resonance
  rw [unitColumn_succ hp hD hpd hk χ hpk,unitColumn_succ hq hD hqd hk η hqk]
  ring

theorem norm_unitAtom_le {p q : ℕ} (χ : DirichletCharacter ℂ p)
    (η : DirichletCharacter ℂ q) (D k : ℕ) : ‖unitAtom χ η D k‖≤1 := by
  unfold unitAtom
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (η.norm_le_one _)).trans (χ.norm_le_one _)

theorem norm_resonance_le {p q : ℕ} (χ : DirichletCharacter ℂ p)
    (η : DirichletCharacter ℂ q) : ‖resonance χ η‖≤1 := by
  unfold resonance
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (η.norm_le_one _)).trans (χ.norm_le_one _)

/-- Every native valuation/unit crossing; no upper digit or proper power deleted. -/
def crossingOrders (p q D : ℕ) : Finset ℕ :=
  (Finset.range (D-1)).filter (fun k => p∣k+1 ∨ q∣k+1)

theorem crossingOrders_card_le (p q D : ℕ) :
    (crossingOrders p q D).card≤D/p+D/q := by
  have hs (r : ℕ) : ((Finset.range (D-1)).filter (fun k => r∣k+1)).card≤D/r := by
    rw [←Nat.card_multiples D r]
    apply Finset.card_le_card
    intro k hk
    have h := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      ((Finset.mem_range.mp h.1).trans_le (Nat.sub_le _ _)),h.2⟩
  unfold crossingOrders
  rw [Finset.filter_or]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hs p) (hs q))

theorem sum_geometric_defects (H : ℕ) (sigma lambda : ℂ) (f : ℕ → ℂ) :
    (1-sigma*lambda)*(∑ k∈Finset.range (H+1),lambda^k*f k)=
      f 0-sigma*lambda^(H+1)*f H+
        ∑ k∈Finset.range H,lambda^(k+1)*(f (k+1)-sigma*f k) := by
  induction H with
  | zero => simp;ring
  | succ H ih =>
    rw [Finset.sum_range_succ,mul_add,ih,Finset.sum_range_succ,pow_succ]
    ring

/-- Complete internally coded native row including both unit endpoints. -/
def codedUnitTrace {p q : ℕ} (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q)
    (D : ℕ) (lambda : ℂ) : ℂ :=
  (∑ k∈Finset.range D,lambda^k*unitAtom χ η D k)/(D : ℂ)

/-- Exact joined identity before taking norms. Both endpoints are actual units,
and every jump retains the complete p-free character and valuation data. -/
theorem codedUnitTrace_defect_identity {p q D : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hD : 0<D) (hpd : p∣D) (hqd : q∣D)
    (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q) (lambda : ℂ) :
    (1-resonance χ η*lambda)*((D : ℂ)*codedUnitTrace χ η D lambda)=
      1-resonance χ η*lambda^D+
        ∑ k∈crossingOrders p q D,
          lambda^(k+1)*(unitAtom χ η D (k+1)-resonance χ η*unitAtom χ η D k) := by
  have hD0 : (D : ℂ)≠0 := by exact_mod_cast hD.ne'
  have he : D-1+1=D := by omega
  have ht := sum_geometric_defects (D-1) (resonance χ η) lambda (unitAtom χ η D)
  rw [he] at ht
  have hfirst : unitAtom χ η D 0=1 := by simp [unitAtom,binomialUnit_zero]
  have hlast : unitAtom χ η D (D-1)=1 := by simp [unitAtom,binomialUnit_last]
  have hj : (∑ k∈Finset.range (D-1),
      lambda^(k+1)*(unitAtom χ η D (k+1)-resonance χ η*unitAtom χ η D k))=
      ∑ k∈crossingOrders p q D,
        lambda^(k+1)*(unitAtom χ η D (k+1)-resonance χ η*unitAtom χ η D k) := by
    unfold crossingOrders
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs with h
    · rfl
    · rw [unitAtom_succ hp hq hD hpd hqd (Finset.mem_range.mp hk)
        χ η (not_or.mp h).1 (not_or.mp h).2]
      simp
  rw [hfirst,hlast,hj] at ht
  simpa only [codedUnitTrace,mul_div_cancel₀ _ hD0,mul_one] using ht

/-- The actual resonance gap controls the full p-free trace. Raw residue
support is never used; the finite theorem includes every common prime-power row. -/
theorem norm_codedUnitTrace_le {p q D : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hD : 0<D) (hpd : p∣D) (hqd : q∣D)
    (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q)
    {lambda : ℂ} (hlambda : ‖lambda‖≤1)
    (hgap : 0<‖1-resonance χ η*lambda‖) :
    ‖codedUnitTrace χ η D lambda‖≤
      (2/(D : ℝ)+2/(p : ℝ)+2/(q : ℝ))/‖1-resonance χ η*lambda‖ := by
  have hpow (k : ℕ) : ‖lambda^k‖≤1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hlambda
  have hdefect (k : ℕ) :
      ‖lambda^(k+1)*(unitAtom χ η D (k+1)-resonance χ η*unitAtom χ η D k)‖≤2 := by
    rw [norm_mul]
    have hr : ‖resonance χ η*unitAtom χ η D k‖≤1 := by
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (norm_unitAtom_le χ η D k)).trans
        (norm_resonance_le χ η)
    have hd := (norm_sub_le _ _).trans
      (add_le_add (norm_unitAtom_le χ η D (k+1)) hr)
    exact (mul_le_of_le_one_left (norm_nonneg _) (hpow (k+1))).trans (by linarith)
  have hbound : ‖1-resonance χ η*lambda^D+
      ∑ k∈crossingOrders p q D,
        lambda^(k+1)*(unitAtom χ η D (k+1)-resonance χ η*unitAtom χ η D k)‖≤
        2+2*((D/p : ℕ)+(D/q : ℕ)) := by
    have hhead : ‖1-resonance χ η*lambda^D‖≤2 := by
      apply (norm_sub_le _ _).trans
      rw [norm_one,norm_mul]
      have hm := (mul_le_of_le_one_right (norm_nonneg _) (hpow D)).trans
        (norm_resonance_le χ η)
      linarith
    have hc : ((crossingOrders p q D).card : ℝ)≤(D/p : ℕ)+(D/q : ℕ) :=
      by exact_mod_cast crossingOrders_card_le p q D
    calc
      _ ≤ ‖1-resonance χ η*lambda^D‖+
        ‖∑ k∈crossingOrders p q D,
          lambda^(k+1)*(unitAtom χ η D (k+1)-resonance χ η*unitAtom χ η D k)‖ := norm_add_le _ _
      _ ≤ 2+∑ k∈crossingOrders p q D,
          ‖lambda^(k+1)*(unitAtom χ η D (k+1)-resonance χ η*unitAtom χ η D k)‖ :=
        add_le_add hhead (norm_sum_le _ _)
      _ ≤ 2+∑ _k∈crossingOrders p q D,(2 : ℝ) :=
        add_le_add_right (Finset.sum_le_sum (fun k _ => hdefect k)) _
      _ ≤ _ := by simp only [Finset.sum_const,nsmul_eq_mul];linarith
  have hid := congrArg norm (codedUnitTrace_defect_identity hp hq hD hpd hqd χ η lambda)
  rw [norm_mul,norm_mul,Complex.norm_natCast] at hid
  have hD0 : (0 : ℝ)<D := by exact_mod_cast hD
  have hp0 : (0 : ℝ)<p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ)<q := by exact_mod_cast hq.pos
  have hdp : ((D/p : ℕ) : ℝ)=(D : ℝ)/(p : ℝ) := Nat.cast_div hpd (by positivity)
  have hdq : ((D/q : ℕ) : ℝ)=(D : ℝ)/(q : ℝ) := Nat.cast_div hqd (by positivity)
  apply (le_div_iff₀ hgap).mpr
  have hh : ‖codedUnitTrace χ η D lambda‖*‖1-resonance χ η*lambda‖*(D : ℝ)≤
      2+2*((D/p : ℕ)+(D/q : ℕ)) := by nlinarith [hbound]
  have hquot := (le_div_iff₀ hD0).mpr hh
  rw [hdp,hdq] at hquot
  convert hquot using 1
  field_simp
  ring

/-- Resonance is not a decay theorem: the complete identity only constrains
the signed crossing sum, with both boundary terms retained. -/
theorem resonant_crossing_identity {p q D : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hD : 0<D) (hpd : p∣D) (hqd : q∣D)
    (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q)
    {lambda : ℂ} (hres : resonance χ η*lambda=1) :
    (∑ k∈crossingOrders p q D,
      lambda^(k+1)*(unitAtom χ η D (k+1)-resonance χ η*unitAtom χ η D k))=
      resonance χ η*lambda^D-1 := by
  have h := codedUnitTrace_defect_identity hp hq hD hpd hqd χ η lambda
  rw [hres,sub_self,zero_mul] at h
  linear_combination -h

/-- A bounded correlated exterior coefficient includes the full physical
phase and any native outer mask. No condition is imposed on its sign. -/
def unitPacket (P Q : Finset ℕ) (χ η : (p : ℕ) → DirichletCharacter ℂ p)
    (coefficient lambda : ℕ → ℕ → ℂ) : ℂ :=
  ∑ p∈P,∑ q∈Q,coefficient p q*codedUnitTrace (χ p) (η q) (p*q) (lambda p q)

/-- Whole native balanced-pair bound after exact inner row cancellation.
It includes the diagonal and prime two; actual source is not assumed. -/
theorem norm_unitPacket_le (P Q : Finset ℕ) (χ η : (p : ℕ) → DirichletCharacter ℂ p)
    (coefficient lambda : ℕ → ℕ → ℂ) {B : ℕ} (hB : 0<B) {W g : ℝ}
    (hW : 0≤W) (hg : 0<g)
    (hP : ∀ p∈P,p.Prime ∧ B≤p) (hQ : ∀ q∈Q,q.Prime ∧ B≤q)
    (hpc : P.card≤2*B) (hqc : Q.card≤2*B)
    (hc : ∀ p∈P,∀ q∈Q,‖coefficient p q‖≤W)
    (hl : ∀ p∈P,∀ q∈Q,‖lambda p q‖≤1)
    (hgap : ∀ p∈P,∀ q∈Q,g≤‖1-resonance (χ p) (η q)*lambda p q‖) :
    ‖unitPacket P Q χ η coefficient lambda‖≤24*W*(B : ℝ)/g := by
  have hb : (0 : ℝ)<B := by exact_mod_cast hB
  have ht (p : ℕ) (hp : p∈P) (q : ℕ) (hq : q∈Q) :
      ‖coefficient p q*codedUnitTrace (χ p) (η q) (p*q) (lambda p q)‖≤W*(6/B/g) := by
    have hpm := hP p hp
    have hqm := hQ q hq
    have hpB : (B : ℝ)≤p := by exact_mod_cast hpm.2
    have hqB : (B : ℝ)≤q := by exact_mod_cast hqm.2
    have hpqB : (B : ℝ)≤(p*q : ℕ) := by
      exact_mod_cast hpm.2.trans (Nat.le_mul_of_pos_right p hqm.1.pos)
    have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ)≤2) hb hpqB
    have h2 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ)≤2) hb hpB
    have h3 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ)≤2) hb hqB
    have hs : 2/(p*q : ℕ)+2/(p : ℝ)+2/(q : ℝ)≤6/(B : ℝ) := by
      simp only [div_eq_mul_inv] at h1 h2 h3 ⊢
      linarith
    have hg' := hg.trans_le (hgap p hp q hq)
    have hnorm : ‖codedUnitTrace (χ p) (η q) (p*q) (lambda p q)‖≤6/B/g := by
      calc
        _ ≤ (2/(p*q : ℕ)+2/(p : ℝ)+2/(q : ℝ))/
            ‖1-resonance (χ p) (η q)*lambda p q‖ :=
          norm_codedUnitTrace_le hpm.1 hqm.1 (Nat.mul_pos hpm.1.pos hqm.1.pos)
            (dvd_mul_right p q) (dvd_mul_left q p) _ _ (hl p hp q hq) hg'
        _ ≤ (6/B)/‖1-resonance (χ p) (η q)*lambda p q‖ :=
          div_le_div_of_nonneg_right hs hg'.le
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hg (hgap p hp q hq)
    rw [norm_mul]
    exact mul_le_mul (hc p hp q hq) hnorm (norm_nonneg _) hW
  unfold unitPacket
  calc
    _ ≤ ∑ p∈P,∑ q∈Q,‖coefficient p q*codedUnitTrace (χ p) (η q) (p*q) (lambda p q)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p _ => norm_sum_le _ _))
    _ ≤ ∑ _p∈P,∑ _q∈Q,W*(6/B/g) :=
      Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun q hq => ht p hp q hq))
    _ = (P.card : ℝ)*Q.card*(W*(6/B/g)) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ (2*B : ℕ)*(2*B : ℕ)*(W*(6/B/g)) := by
      gcongr
    _ = _ := by push_cast;field_simp;ring

/-- A native whole-packet source gate. The current p-free cancellation
class is source-blind whenever its actual gap beats the indicated rate.
Every exterior phase/mask may move; no hypothetical-zero response is granted. -/
theorem tendsto_unitPacket_source_zero {beta eps : ℝ} (hb : 1+eps<2*beta)
    (P Q : ℕ → Finset ℕ) (χ η : (p : ℕ) → DirichletCharacter ℂ p)
    (coefficient lambda : ℕ → ℕ → ℕ → ℂ)
    (hnative : ∀ᶠ J in atTop,
      (∀ p∈P J,p.Prime ∧ 2^J≤p) ∧ (∀ q∈Q J,q.Prime ∧ 2^J≤q) ∧
      (P J).card≤2*2^J ∧ (Q J).card≤2*2^J ∧
      (∀ p∈P J,∀ q∈Q J,‖coefficient J p q‖≤((J+1 : ℕ) : ℝ)^2) ∧
      (∀ p∈P J,∀ q∈Q J,‖lambda J p q‖≤1) ∧
      (∀ p∈P J,∀ q∈Q J,Real.exp (-eps*Real.log 2)^J≤
        ‖1-resonance (χ p) (η q)*lambda J p q‖)) :
    Tendsto (fun J : ℕ => ((Real.exp (-2*beta*Real.log 2)^J : ℝ) : ℂ)*
      unitPacket (P J) (Q J) χ η (coefficient J) (lambda J)) atTop (𝓝 0) := by
  let a := Real.exp ((1+eps-2*beta)*Real.log 2)
  have ha : 0<a := Real.exp_pos _
  have ha1 : a<1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by linarith)
    (Real.log_pos (by norm_num)))
  have hrate : a=Real.exp (-2*beta*Real.log 2)*2/Real.exp (-eps*Real.log 2) := by
    unfold a
    rw [show (1+eps-2*beta)*Real.log 2=
      (-2*beta*Real.log 2+Real.log 2)-(-eps*Real.log 2) by ring,
      Real.exp_sub,Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ)<2)]
  have ht := (ArithmeticOperatorFloorInverseAudit.tendsto_shifted_polynomial_geometric 2 ha ha1).const_mul 24
  apply squeeze_zero_norm' (a := fun J : ℕ => 24*((J+1 : ℕ) : ℝ)^2*a^J) _
    (by simpa only [mul_zero,mul_assoc] using ht)
  filter_upwards [hnative] with J hn
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (Real.exp_pos _).le _)]
  calc
    _ ≤ Real.exp (-2*beta*Real.log 2)^J*
        (24*((J+1 : ℕ) : ℝ)^2*(2^J : ℕ)/Real.exp (-eps*Real.log 2)^J) :=
      mul_le_mul_of_nonneg_left (norm_unitPacket_le (P J) (Q J) χ η
        (coefficient J) (lambda J) (by positivity) (sq_nonneg _) (by positivity)
        hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2.1
        hn.2.2.2.2.2.2) (by positivity)
    _ = _ := by rw [hrate,div_pow,mul_pow,Nat.cast_pow,Nat.cast_ofNat];ring

theorem unitPacket_nonzero_source_impossible {beta eps : ℝ} (hb : 1+eps<2*beta)
    (P Q : ℕ → Finset ℕ) (χ η : (p : ℕ) → DirichletCharacter ℂ p)
    (coefficient lambda : ℕ → ℕ → ℕ → ℂ)
    (hnative : ∀ᶠ J in atTop,
      (∀ p∈P J,p.Prime ∧ 2^J≤p) ∧ (∀ q∈Q J,q.Prime ∧ 2^J≤q) ∧
      (P J).card≤2*2^J ∧ (Q J).card≤2*2^J ∧
      (∀ p∈P J,∀ q∈Q J,‖coefficient J p q‖≤((J+1 : ℕ) : ℝ)^2) ∧
      (∀ p∈P J,∀ q∈Q J,‖lambda J p q‖≤1) ∧
      (∀ p∈P J,∀ q∈Q J,Real.exp (-eps*Real.log 2)^J≤
        ‖1-resonance (χ p) (η q)*lambda J p q‖)) {v : ℂ} (hv : v≠0) :
    ¬Tendsto (fun J : ℕ => ((Real.exp (-2*beta*Real.log 2)^J : ℝ) : ℂ)*
      unitPacket (P J) (Q J) χ η (coefficient J) (lambda J)) atTop (𝓝 v) := by
  intro hs
  exact hv (tendsto_nhds_unique hs (tendsto_unitPacket_source_zero hb P Q χ η coefficient lambda hnative))

end RiemannGaussian.ArithmeticOperatorPFreeUnitAudit

#lint+ in RiemannGaussian.ArithmeticOperatorPFreeUnitAudit

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty p-free unit audit."
  logInfo m!"P-free unit audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-pfree-unit"
  IO.FS.writeFile ".lake/arithmetic-operator-pfree-unit/axioms.json"
    (Json.mkObj [("scope",toJson "exact native p-free binomial recurrences and nonresonant source gate; no actual resonant zero response or nonlinear prime estimate inferred"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
