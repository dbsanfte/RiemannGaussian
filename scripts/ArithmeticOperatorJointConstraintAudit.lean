/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorCrossUnitCancellation
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Native common-row Fourier codes: a quantitative source barrier

Both genuine prime columns, their Lucas upper digits, every quotient jump
and the two unit endpoints remain in the same literal binomial row.
Internal Fourier coding cannot detect an off-line source when its ACTUAL
gap from the character resonance is large enough. This is a scoped
source-gate failure. No source for resonant same-parity rows is inferred.

The finite identity includes proper-prime-power common row lengths.
The terminal native packet below is explicitly an ordinary-prime PAIR
packet; no summed proper-power complement is silently paid.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical Topology
namespace RiemannGaussian.ArithmeticOperatorJointConstraintAudit
open Complex Filter ArithmeticOperatorCrossUnitCancellation SuzukiCarryCorrelation

/-- The literal product character parity, before any Fourier projection. -/
def resonance {p q : ℕ} (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q) : ℂ :=
  χ (-1)*η (-1)

/-- Internal Fourier phase, not a replacement for either exterior prime phase. -/
def internalPhase (theta : ℝ) : ℂ := Complex.exp (I*theta)

theorem norm_internalPhase (theta : ℝ) : ‖internalPhase theta‖=1 := by
  simp [internalPhase,Complex.norm_exp]

theorem norm_resonance_le {p q : ℕ} (χ : DirichletCharacter ℂ p)
    (η : DirichletCharacter ℂ q) : ‖resonance χ η‖≤1 := by
  unfold resonance
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (η.norm_le_one _)).trans (χ.norm_le_one _)

theorem resonance_eq_one_or_neg_one {p q : ℕ} (χ : DirichletCharacter ℂ p)
    (η : DirichletCharacter ℂ q) : resonance χ η=1 ∨ resonance χ η=-1 := by
  have hx : χ (-1)*χ (-1)=1 := by rw [←map_mul];simp
  have hy : η (-1)*η (-1)=1 := by rw [←map_mul];simp
  have hs : resonance χ η^2=1 := by
    calc
      _ = (χ (-1)*χ (-1))*(η (-1)*η (-1)) := by unfold resonance;ring
      _ = 1 := by rw [hx,hy,mul_one]
  have hz : (resonance χ η-1)*(resonance χ η+1)=0 := by
    calc
      _ = resonance χ η^2-1 := by ring
      _ = 0 := by rw [hs,sub_self]
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (add_eq_zero_iff_eq_neg.mp h)

/-- Every actual adjacent transition where one of the two upper digits changes. -/
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

/-- All character parities have the same exact native recurrence away from jumps. -/
theorem atom_succ {p q D k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hD : 0<D) (hpd : p∣D) (hqd : q∣D)
    (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q)
    (hpk : ¬p∣k+1) (hqk : ¬q∣k+1) :
    atom χ η D (k+1)=resonance χ η*atom χ η D k := by
  unfold atom resonance
  rw [column_succ hp hD hpd χ hpk,column_succ hq hD hqd η hqk]
  ring

theorem sum_geometric_defects (H : ℕ) (sigma lambda : ℂ) (f : ℕ → ℂ) :
    (1-sigma*lambda)*(∑ k∈Finset.range (H+1),lambda^k*f k)=
      f 0-sigma*lambda^(H+1)*f H+
        ∑ k∈Finset.range H,lambda^(k+1)*(f (k+1)-sigma*f k) := by
  induction H with
  | zero => simp;ring
  | succ H ih =>
    rw [Finset.sum_range_succ]
    rw [mul_add,ih]
    rw [Finset.sum_range_succ]
    rw [pow_succ]
    ring

/-- The complete internal Fourier projection, with the original row endpoints. -/
def codedTrace {p q : ℕ} (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q)
    (D : ℕ) (lambda : ℂ) : ℂ :=
  (∑ k∈Finset.range D,lambda^k*atom χ η D k)/(D : ℂ)

/-- Exact joined source preflight. Only literal crossing terms survive;
no period, residue, endpoint or phase has been completed away. -/
theorem codedTrace_defect_identity {p q D : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hD : 0<D) (hpd : p∣D) (hqd : q∣D)
    (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q) (lambda : ℂ) :
    (1-resonance χ η*lambda)*((D : ℂ)*codedTrace χ η D lambda)=
      1-resonance χ η*lambda^D+
        ∑ k∈crossingOrders p q D,
          lambda^(k+1)*(atom χ η D (k+1)-resonance χ η*atom χ η D k) := by
  have hD0 : (D : ℂ)≠0 := by exact_mod_cast hD.ne'
  have he : D-1+1=D := by omega
  have ht := sum_geometric_defects (D-1) (resonance χ η) lambda (atom χ η D)
  rw [he] at ht
  have hfirst : atom χ η D 0=1 := by simp [atom]
  have hlast : atom χ η D (D-1)=1 := by simp [atom]
  have hj : (∑ k∈Finset.range (D-1),
      lambda^(k+1)*(atom χ η D (k+1)-resonance χ η*atom χ η D k))=
      ∑ k∈crossingOrders p q D,
        lambda^(k+1)*(atom χ η D (k+1)-resonance χ η*atom χ η D k) := by
    unfold crossingOrders
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs with h
    · rfl
    · rw [atom_succ hp hq hD hpd hqd χ η (not_or.mp h).1 (not_or.mp h).2]
      simp
  rw [hfirst,hlast,hj] at ht
  simpa only [codedTrace,mul_div_cancel₀ _ hD0,mul_one] using ht

/-- Quantitative estimate AFTER the exact native cancellation. The gap
is the actual complex resonance gap, not an asserted frequency heuristic. -/
theorem norm_codedTrace_le {p q D : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hD : 0<D) (hpd : p∣D) (hqd : q∣D)
    (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q)
    {lambda : ℂ} (hlambda : ‖lambda‖≤1)
    (hgap : 0<‖1-resonance χ η*lambda‖) :
    ‖codedTrace χ η D lambda‖≤
      (2/(D : ℝ)+2/(p : ℝ)+2/(q : ℝ))/‖1-resonance χ η*lambda‖ := by
  have hpow (k : ℕ) : ‖lambda^k‖≤1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hlambda
  have hdefect (k : ℕ) :
      ‖lambda^(k+1)*(atom χ η D (k+1)-resonance χ η*atom χ η D k)‖≤2 := by
    rw [norm_mul]
    have hr : ‖resonance χ η*atom χ η D k‖≤1 := by
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (norm_atom_le χ η D k)).trans
        (norm_resonance_le χ η)
    have hd := (norm_sub_le _ _).trans
      (add_le_add (norm_atom_le χ η D (k+1)) hr)
    exact (mul_le_of_le_one_left (norm_nonneg _) (hpow (k+1))).trans (by linarith)
  have hbound : ‖1-resonance χ η*lambda^D+
      ∑ k∈crossingOrders p q D,
        lambda^(k+1)*(atom χ η D (k+1)-resonance χ η*atom χ η D k)‖≤
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
          lambda^(k+1)*(atom χ η D (k+1)-resonance χ η*atom χ η D k)‖ := norm_add_le _ _
      _ ≤ 2+∑ k∈crossingOrders p q D,
          ‖lambda^(k+1)*(atom χ η D (k+1)-resonance χ η*atom χ η D k)‖ :=
        add_le_add hhead (norm_sum_le _ _)
      _ ≤ 2+∑ _k∈crossingOrders p q D,(2 : ℝ) :=
        add_le_add_right (Finset.sum_le_sum (fun k _ => hdefect k)) _
      _ ≤ _ := by simp only [Finset.sum_const,nsmul_eq_mul];linarith
  have hid := congrArg norm (codedTrace_defect_identity hp hq hD hpd hqd χ η lambda)
  rw [norm_mul,norm_mul,Complex.norm_natCast] at hid
  have hD0 : (0 : ℝ)<D := by exact_mod_cast hD
  have hp0 : (0 : ℝ)<p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ)<q := by exact_mod_cast hq.pos
  have hdp : ((D/p : ℕ) : ℝ)=(D : ℝ)/(p : ℝ) := Nat.cast_div hpd (by positivity)
  have hdq : ((D/q : ℕ) : ℝ)=(D : ℝ)/(q : ℝ) := Nat.cast_div hqd (by positivity)
  apply (le_div_iff₀ hgap).mpr
  have hh : ‖codedTrace χ η D lambda‖*‖1-resonance χ η*lambda‖*(D : ℝ)≤
      2+2*((D/p : ℕ)+(D/q : ℕ)) := by nlinarith [hbound]
  have hquot := (le_div_iff₀ hD0).mpr hh
  rw [hdp,hdq] at hquot
  convert hquot using 1
  field_simp
  ring

/-- Same-parity native rows are source-small away from the actual zero-frequency resonance. -/
theorem norm_codedTrace_fourier_same {p q D : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hD : 0<D) (hpd : p∣D) (hqd : q∣D)
    (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q)
    (hsign : resonance χ η=1) (theta : ℝ) (hgap : 0<‖1-internalPhase theta‖) :
    ‖codedTrace χ η D (internalPhase theta)‖≤
      (2/(D : ℝ)+2/(p : ℝ)+2/(q : ℝ))/‖1-internalPhase theta‖ := by
  have hg : 0<‖1-resonance χ η*internalPhase theta‖ := by simpa [hsign] using hgap
  simpa only [hsign,one_mul] using
    norm_codedTrace_le hp hq hD hpd hqd χ η (norm_internalPhase theta).le hg

/-- Opposite-parity native rows are source-small away from their actual pi-frequency resonance. -/
theorem norm_codedTrace_fourier_opposite {p q D : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hD : 0<D) (hpd : p∣D) (hqd : q∣D)
    (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q)
    (hsign : resonance χ η=-1) (theta : ℝ) (hgap : 0<‖1+internalPhase theta‖) :
    ‖codedTrace χ η D (internalPhase theta)‖≤
      (2/(D : ℝ)+2/(p : ℝ)+2/(q : ℝ))/‖1+internalPhase theta‖ := by
  have hg : 0<‖1-resonance χ η*internalPhase theta‖ := by simpa [hsign] using hgap
  simpa only [hsign,neg_one_mul,sub_neg_eq_add] using
    norm_codedTrace_le hp hq hD hpd hqd χ η (norm_internalPhase theta).le hg

/-- All positive proper-prime-power exponents are permitted in the EXACT
finite row estimate; no upper Lucas digit or prime power is removed. -/
theorem norm_codedTrace_primePower_row_le {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : 0<r) (hs : 0<s) (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q)
    (theta : ℝ) (hgap : 0<‖1-resonance χ η*internalPhase theta‖) :
    ‖codedTrace χ η (p^r*q^s) (internalPhase theta)‖≤
      (2/(p^r*q^s : ℕ)+2/(p : ℝ)+2/(q : ℝ))/‖1-resonance χ η*internalPhase theta‖ := by
  exact norm_codedTrace_le hp hq
    (Nat.mul_pos (Nat.pow_pos hp.pos) (Nat.pow_pos hq.pos))
    (dvd_mul_of_dvd_left (dvd_pow_self p hr.ne') _)
    (dvd_mul_of_dvd_right (dvd_pow_self q hs.ne') _) χ η (norm_internalPhase theta).le hgap

/-- A genuine internal Fourier code on the literal row. -/
def quadraticCodedTrace (p q : ℕ) (theta : ℝ) : ℂ :=
  if h : p.Prime ∧ q.Prime then
    (let : Fact p.Prime := ⟨h.1⟩;let : Fact q.Prime := ⟨h.2⟩;
      codedTrace (quadraticColumn p) (quadraticColumn q) (p*q) (internalPhase theta)) else 0

/-- The actual gap for BOTH parity classes. Zero frequency is resonant
in the same-parity case, and pi frequency is resonant in the opposite case. -/
def quadraticGap (p q : ℕ) (theta : ℝ) : ℝ :=
  if h : p.Prime ∧ q.Prime then
    (let : Fact p.Prime := ⟨h.1⟩;let : Fact q.Prime := ⟨h.2⟩;
      ‖1-resonance (quadraticColumn p) (quadraticColumn q)*internalPhase theta‖) else 0

theorem norm_quadraticCodedTrace_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (theta : ℝ) (hgap : 0<quadraticGap p q theta) :
    ‖quadraticCodedTrace p q theta‖≤
      (2/(p*q : ℕ)+2/(p : ℝ)+2/(q : ℝ))/quadraticGap p q theta := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  have hpq : p.Prime ∧ q.Prime := ⟨hp,hq⟩
  simp only [quadraticCodedTrace,quadraticGap,dite_eq_left hpq] at hgap ⊢
  exact norm_codedTrace_le hp hq (Nat.mul_pos hp.pos hq.pos)
    (dvd_mul_right p q) (dvd_mul_left q p) _ _ (norm_internalPhase theta).le hgap

/-- Both genuine character parities are covered by this exact spectral gap. -/
theorem quadraticGap_ge_min {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (theta : ℝ) :
    min ‖1-internalPhase theta‖ ‖1+internalPhase theta‖≤quadraticGap p q theta := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  rw [quadraticGap,dite_eq_left (show p.Prime ∧ q.Prime from ⟨hp,hq⟩)]
  change min ‖1-internalPhase theta‖ ‖1+internalPhase theta‖≤
    ‖1-resonance (quadraticColumn p) (quadraticColumn q)*internalPhase theta‖
  rcases resonance_eq_one_or_neg_one (quadraticColumn p) (quadraticColumn q) with hs | hs
  · rw [hs,one_mul]
    exact min_le_left _ _
  · rw [hs,neg_one_mul,sub_neg_eq_add]
    exact min_le_right _ _

/-- All native ordinary primes, with no deletion of either parity class or prime two. -/
def allPrimeBand (J : ℕ) : Finset ℕ :=
  (Finset.range (2^(J+1))).filter (fun p => 2^J≤p ∧ p.Prime)

theorem allPrimeBand_mem {J p : ℕ} (hp : p∈allPrimeBand J) :
    p<2^(J+1) ∧ 2^J≤p ∧ p.Prime := by
  have h := Finset.mem_filter.mp hp
  exact ⟨Finset.mem_range.mp h.1,h.2⟩

theorem allPrimeBand_card_le (J : ℕ) : (allPrimeBand J).card≤2^(J+1) := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

/-- The original integer label scale is retained, not replaced by a completed CRT period. -/
theorem native_pair_scale {J p q : ℕ} (hp : p∈allPrimeBand J)
    (hq : q∈allPrimeBand J) : 2^(2*J)≤p*q ∧ p*q<2^(2*J+2) := by
  have hpm := allPrimeBand_mem hp
  have hqm := allPrimeBand_mem hq
  have hlo := Nat.mul_le_mul hpm.2.1 hqm.2.1
  have hhi := Nat.mul_lt_mul_of_pos_left hqm.1 hpm.2.2.pos
  have hhi' := Nat.mul_lt_mul_of_pos_right hpm.1 (by positivity : 0<2^(J+1))
  have hpows : 2^(2*J)=2^J*2^J := by rw [show 2*J=J+J by omega,pow_add]
  have hpow' : 2^(2*J+2)=2^(J+1)*2^(J+1) := by
    rw [show 2*J+2=(J+1)+(J+1) by omega,pow_add]
  exact ⟨hpows ▸ hlo,hpow' ▸ hhi.trans hhi'⟩

theorem vonMangoldt_allBand_le {J p : ℕ} (hp : p∈allPrimeBand J) :
    ArithmeticFunction.vonMangoldt p≤(J+1 : ℕ) := by
  have hm := allPrimeBand_mem hp
  have hl : Real.log (p : ℝ)≤Real.log (2^(J+1) : ℕ) :=
    Real.log_le_log (by exact_mod_cast hm.2.2.pos) (by exact_mod_cast hm.1.le)
  have hlog2 : Real.log 2≤1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    norm_num at h
    exact h
  have hpow : Real.log (2^(J+1) : ℕ)=(J+1 : ℕ)*Real.log 2 := by
    rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  exact ArithmeticFunction.vonMangoldt_le_log.trans (hl.trans (by
    rw [hpow]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) hlog2))

theorem codedTrace_allBand_le {J p q : ℕ}
    (hp : p∈allPrimeBand J) (hq : q∈allPrimeBand J) (theta : ℝ)
    {g : ℝ} (hg : 0<g) (hgap : g≤quadraticGap p q theta) :
    ‖quadraticCodedTrace p q theta‖≤6/(2^J : ℕ)/g := by
  have hpm := allPrimeBand_mem hp
  have hqm := allPrimeBand_mem hq
  have hB : (0 : ℝ)<(2^J : ℕ) := by positivity
  have hpB : ((2^J : ℕ) : ℝ)≤p := by exact_mod_cast hpm.2.1
  have hqB : ((2^J : ℕ) : ℝ)≤q := by exact_mod_cast hqm.2.1
  have hpqB : ((2^J : ℕ) : ℝ)≤(p*q : ℕ) := by
    exact_mod_cast hpm.2.1.trans (Nat.le_mul_of_pos_right p hqm.2.2.pos)
  have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ)≤2) hB hpqB
  have h2 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ)≤2) hB hpB
  have h3 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ)≤2) hB hqB
  have hsum : 2/(p*q : ℕ)+2/(p : ℝ)+2/(q : ℝ)≤6/(2^J : ℕ) := by
    simp only [div_eq_mul_inv] at h1 h2 h3 ⊢
    linarith
  calc
    _ ≤ (2/(p*q : ℕ)+2/(p : ℝ)+2/(q : ℝ))/quadraticGap p q theta :=
      norm_quadraticCodedTrace_le hpm.2.2 hqm.2.2 theta (hg.trans_le hgap)
    _ ≤ (6/(2^J : ℕ))/quadraticGap p q theta :=
      div_le_div_of_nonneg_right hsum (hg.trans_le hgap).le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hg hgap

/-- Whole actual balanced pair packet. The diagonal is explicitly absent;
both character parities and the FULL exterior physical phase remain. -/
def fourierPacket (J : ℕ) (y : ℝ) (theta : ℕ → ℕ → ℝ)
    (mask : ℕ → ℕ → ℂ) : ℂ :=
  ∑ p∈allPrimeBand J,∑ q∈allPrimeBand J,
    if p≠q then (ArithmeticFunction.vonMangoldt p : ℂ)*
      (ArithmeticFunction.vonMangoldt q : ℂ)*primePhase y (p*q)*mask p q*
      quadraticCodedTrace p q (theta p q) else 0

/-- No cofinal source is inferred here: this is the direct native Fourier
source-barrier estimate after exact row cancellation. -/
theorem norm_fourierPacket_le (J : ℕ) (y : ℝ) (theta : ℕ → ℕ → ℝ)
    (mask : ℕ → ℕ → ℂ) {g : ℝ} (hg : 0<g)
    (hm : ∀ p∈allPrimeBand J,∀ q∈allPrimeBand J,p≠q → ‖mask p q‖≤1)
    (hgap : ∀ p∈allPrimeBand J,∀ q∈allPrimeBand J,p≠q → g≤quadraticGap p q (theta p q)) :
    ‖fourierPacket J y theta mask‖≤24*((J+1 : ℕ) : ℝ)^2*(2^J : ℕ)/g := by
  have hterm (p : ℕ) (hp : p∈allPrimeBand J) (q : ℕ) (hq : q∈allPrimeBand J) :
      ‖if p≠q then (ArithmeticFunction.vonMangoldt p : ℂ)*
        (ArithmeticFunction.vonMangoldt q : ℂ)*primePhase y (p*q)*mask p q*
        quadraticCodedTrace p q (theta p q) else 0‖≤
      ((J+1 : ℕ) : ℝ)^2*(6/(2^J : ℕ)/g) := by
    by_cases hne : p≠q
    · rw [ite_eq_left hne]
      simp only [norm_mul,Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,norm_primePhase,mul_one]
      have hL : ArithmeticFunction.vonMangoldt p*ArithmeticFunction.vonMangoldt q≤
          ((J+1 : ℕ) : ℝ)^2 := by
        simpa only [pow_two] using mul_le_mul (vonMangoldt_allBand_le hp)
          (vonMangoldt_allBand_le hq) ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
      have hM := mul_le_of_le_one_right
        (mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := p))
          (ArithmeticFunction.vonMangoldt_nonneg (n := q))) (hm p hp q hq hne)
      exact mul_le_mul (hM.trans hL) (codedTrace_allBand_le hp hq (theta p q) hg
        (hgap p hp q hq hne)) (norm_nonneg _) (sq_nonneg _)
    · rw [ite_eq_right hne,norm_zero]
      positivity
  unfold fourierPacket
  calc
    _ ≤ ∑ p∈allPrimeBand J,∑ q∈allPrimeBand J,
        ‖if p≠q then (ArithmeticFunction.vonMangoldt p : ℂ)*
          (ArithmeticFunction.vonMangoldt q : ℂ)*primePhase y (p*q)*mask p q*
          quadraticCodedTrace p q (theta p q) else 0‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p _ => norm_sum_le _ _))
    _ ≤ ∑ _p∈allPrimeBand J,∑ _q∈allPrimeBand J,
        ((J+1 : ℕ) : ℝ)^2*(6/(2^J : ℕ)/g) :=
      Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun q hq => hterm p hp q hq))
    _ = ((allPrimeBand J).card : ℝ)*(allPrimeBand J).card*
        (((J+1 : ℕ) : ℝ)^2*(6/(2^J : ℕ)/g)) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ ((2^(J+1) : ℕ) : ℝ)*(2^(J+1) : ℕ)*
        (((J+1 : ℕ) : ℝ)^2*(6/(2^J : ℕ)/g)) := by
      gcongr
      · exact_mod_cast allPrimeBand_card_le J
      · exact_mod_cast allPrimeBand_card_le J
    _ = _ := by
      have h2 : ((2^J : ℕ) : ℝ)≠0 := by positivity
      rw [pow_succ]
      push_cast
      field_simp
      ring

/-- Actual gap hypothesis, allowed eventually. Frequency heuristics are
not substituted for the literal gap. Heights and outside masks may move. -/
theorem tendsto_fourierPacket_source_zero {beta eta : ℝ} (hb : 1+eta<2*beta)
    (y : ℕ → ℝ) (theta : ℕ → ℕ → ℕ → ℝ) (mask : ℕ → ℕ → ℕ → ℂ)
    (hm : ∀ᶠ J in atTop,∀ p∈allPrimeBand J,∀ q∈allPrimeBand J,p≠q → ‖mask J p q‖≤1)
    (hgap : ∀ᶠ J in atTop,∀ p∈allPrimeBand J,∀ q∈allPrimeBand J,p≠q →
      Real.exp (-eta*Real.log 2)^J≤quadraticGap p q (theta J p q)) :
    Tendsto (fun J : ℕ => ((Real.exp (-2*beta*Real.log 2)^J : ℝ) : ℂ)*
      fourierPacket J (y J) (theta J) (mask J)) atTop (𝓝 0) := by
  let a := Real.exp ((1+eta-2*beta)*Real.log 2)
  have ha : 0<a := Real.exp_pos _
  have ha1 : a<1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by linarith)
    (Real.log_pos (by norm_num)))
  have hrate : a=Real.exp (-2*beta*Real.log 2)*2/Real.exp (-eta*Real.log 2) := by
    unfold a
    rw [show (1+eta-2*beta)*Real.log 2=
      (-2*beta*Real.log 2+Real.log 2)-(-eta*Real.log 2) by ring,
      Real.exp_sub,Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ)<2)]
  have ht := (ArithmeticOperatorFloorInverseAudit.tendsto_shifted_polynomial_geometric 2 ha ha1).const_mul 24
  apply squeeze_zero_norm' (a := fun J : ℕ => 24*((J+1 : ℕ) : ℝ)^2*a^J) _
    (by simpa only [mul_zero,mul_assoc] using ht)
  filter_upwards [hm,hgap] with J hm hgap
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (Real.exp_pos _).le _)]
  calc
    _ ≤ Real.exp (-2*beta*Real.log 2)^J*
        (24*((J+1 : ℕ) : ℝ)^2*(2^J : ℕ)/Real.exp (-eta*Real.log 2)^J) :=
      mul_le_mul_of_nonneg_left (norm_fourierPacket_le J _ _ _ (by positivity) hm hgap) (by positivity)
    _ = _ := by rw [hrate,div_pow,mul_pow,Nat.cast_pow,Nat.cast_ofNat];ring

/-- A separated internal code cannot retain a nonzero off-line zero mode.
This closes only the named source-small class, not resonant same-parity rows. -/
theorem fourierPacket_nonzero_source_impossible {beta eta : ℝ} (hb : 1+eta<2*beta)
    (y : ℕ → ℝ) (theta : ℕ → ℕ → ℕ → ℝ) (mask : ℕ → ℕ → ℕ → ℂ)
    (hm : ∀ᶠ J in atTop,∀ p∈allPrimeBand J,∀ q∈allPrimeBand J,p≠q → ‖mask J p q‖≤1)
    (hgap : ∀ᶠ J in atTop,∀ p∈allPrimeBand J,∀ q∈allPrimeBand J,p≠q →
      Real.exp (-eta*Real.log 2)^J≤quadraticGap p q (theta J p q))
    {v : ℂ} (hv : v≠0) :
    ¬Tendsto (fun J : ℕ => ((Real.exp (-2*beta*Real.log 2)^J : ℝ) : ℂ)*
      fourierPacket J (y J) (theta J) (mask J)) atTop (𝓝 v) := by
  intro hs
  exact hv (tendsto_nhds_unique hs (tendsto_fourierPacket_source_zero hb y theta mask hm hgap))

/-- Every fixed POSITIVE actual gap is source-blind at every beta>1/2.
The hypotheses are eventual, so no impossible J=0 condition is hidden. -/
theorem tendsto_fourierPacket_source_zero_fixed_gap {beta g : ℝ} (hb : 1/2<beta)
    (hg : 0<g) (y : ℕ → ℝ) (theta : ℕ → ℕ → ℕ → ℝ) (mask : ℕ → ℕ → ℕ → ℂ)
    (hm : ∀ᶠ J in atTop,∀ p∈allPrimeBand J,∀ q∈allPrimeBand J,p≠q → ‖mask J p q‖≤1)
    (hgap : ∀ᶠ J in atTop,∀ p∈allPrimeBand J,∀ q∈allPrimeBand J,p≠q →
      g≤quadraticGap p q (theta J p q)) :
    Tendsto (fun J : ℕ => ((Real.exp (-2*beta*Real.log 2)^J : ℝ) : ℂ)*
      fourierPacket J (y J) (theta J) (mask J)) atTop (𝓝 0) := by
  let eta := beta-1/2
  have heta : 0<eta := by dsimp [eta];linarith
  have he : Real.exp (-eta*Real.log 2)<1 := Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (neg_neg_of_pos heta) (Real.log_pos (by norm_num)))
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le he
  have hsmall : ∀ᶠ J : ℕ in atTop,Real.exp (-eta*Real.log 2)^J≤g := by
    filter_upwards [ht.eventually_lt_const hg] with J hJ
    exact hJ.le
  apply tendsto_fourierPacket_source_zero (eta := eta) (by dsimp [eta];linarith) y theta mask hm
  filter_upwards [hgap,hsmall] with J hgap hsmall
  intro p hp q hq hne
  exact hsmall.trans (hgap p hp q hq hne)

/-- A fixed native internal Fourier modulation away from BOTH actual
parity resonances cannot detect ANY source beta>1/2. No prime statistics
or separate complete-prime source limits enter this theorem. -/
theorem tendsto_fixed_fourier_code_source_zero {beta : ℝ} (hb : 1/2<beta)
    (theta : ℝ) (hcode : internalPhase theta≠1 ∧ internalPhase theta≠-1)
    (y : ℕ → ℝ) (mask : ℕ → ℕ → ℕ → ℂ)
    (hm : ∀ᶠ J in atTop,∀ p∈allPrimeBand J,∀ q∈allPrimeBand J,p≠q → ‖mask J p q‖≤1) :
    Tendsto (fun J : ℕ => ((Real.exp (-2*beta*Real.log 2)^J : ℝ) : ℂ)*
      fourierPacket J (y J) (fun _ _ => theta) (mask J)) atTop (𝓝 0) := by
  have h1 : 0<‖1-internalPhase theta‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hcode.1.symm)
  have h2 : 0<‖1+internalPhase theta‖ := by
    apply norm_pos_iff.mpr
    intro h
    exact hcode.2 (by linear_combination h)
  apply tendsto_fourierPacket_source_zero_fixed_gap hb (lt_min h1 h2) y
    (fun _ _ _ => theta) mask hm
  filter_upwards [] with J
  intro p hp q hq _
  exact quadraticGap_ge_min (allPrimeBand_mem hp).2.2 (allPrimeBand_mem hq).2.2 theta

end RiemannGaussian.ArithmeticOperatorJointConstraintAudit

#lint+ in RiemannGaussian.ArithmeticOperatorJointConstraintAudit

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
  unless declarations>0 do throwError "Empty joint-constraint audit."
  logInfo m!"Joint-constraint audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-joint-constraint"
  IO.FS.writeFile ".lake/arithmetic-operator-joint-constraint/axioms.json"
    (Json.mkObj [("scope",toJson "native common-row internal Fourier source barrier; resonant same-parity source and proper-power aggregate not inferred"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
