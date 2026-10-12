/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorLucasUnitAudit
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Coupled opposite-parity binomial rows: exact cancellation and source gate

Both actual prime columns and upper-digit residues are retained. Opposite
character parity cancels adjacent atoms away from native quotient jumps.
The finite theorem permits every odd common-multiple row length, including
proper prime-power lengths. No universal PSD or zeta source is inferred.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical Topology
namespace RiemannGaussian.ArithmeticOperatorCrossUnitCancellation
open Complex Filter ArithmeticOperatorLucasUnitAudit SuzukiCarryCorrelation

/-- Two literal residue columns on the SAME complete binomial row. -/
def atom {p q : ℕ} (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q)
    (D k : ℕ) : ℂ :=
  χ (((D-1).choose k : ℕ) : ZMod p)*η (((D-1).choose k : ℕ) : ZMod q)

/-- Normalized complete coupled row, including its final unit endpoint. -/
def pairTrace {p q : ℕ} (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q)
    (D : ℕ) : ℂ := (∑ k∈Finset.range D,atom χ η D k)/(D : ℂ)

/-- The precise surviving adjacent pairs; no modulus period is completed. -/
def jumpOrders (p q D : ℕ) : Finset ℕ :=
  (Finset.range (D/2)).filter (fun i => p∣2*i+1 ∨ q∣2*i+1)

theorem encoded_first_digit {p D : ℕ} (hp : p.Prime) (hD : 0<D) (hpd : p∣D)
    (χ : DirichletCharacter ℂ p) (k : ℕ) :
    χ (((D-1).choose k : ℕ) : ZMod p)=
      χ ((-1 : ZMod p)^(k%p))*χ (((D/p-1).choose (k/p) : ℕ) : ZMod p) := by
  have ha : 0<D/p := Nat.div_pos (Nat.le_of_dvd hD hpd) hp.pos
  have he : p*(D/p)=D := Nat.mul_div_cancel' hpd
  have hc := commonRow_first_digit hp ha k
  rw [he] at hc
  rw [hc,map_mul]

theorem quotient_stable {p k : ℕ} (hp : 0<p) (hj : ¬p∣k+1) :
    (k+1)/p=k/p ∧ (k+1)%p=k%p+1 := by
  have hd : (k+1)/p=k/p := by
    rw [Nat.succ_div]
    simp only [hj,ite_false,add_zero]
  have hm : (k+1)%p=(k%p+1)%p := by
    rw [Nat.add_mod]
    by_cases hp1 : p=1
    · subst p
      norm_num
    · rw [Nat.mod_eq_of_lt (by omega : 1<p)]
  have hn : (k+1)%p≠0 := by
    intro hz
    exact hj (Nat.dvd_of_mod_eq_zero hz)
  have hk : k%p<p := Nat.mod_lt _ hp
  have hlt : k%p+1<p := by
    by_contra h
    have he : k%p+1=p := by omega
    rw [hm,he,Nat.mod_self] at hn
    contradiction
  exact ⟨hd,by rw [hm,Nat.mod_eq_of_lt hlt]⟩

/-- A true adjacent relation in a native column, with the upper binomial factor unchanged. -/
theorem column_succ {p D k : ℕ} (hp : p.Prime) (hD : 0<D) (hpd : p∣D)
    (χ : DirichletCharacter ℂ p) (hj : ¬p∣k+1) :
    χ (((D-1).choose (k+1) : ℕ) : ZMod p)=
      χ (-1)*χ (((D-1).choose k : ℕ) : ZMod p) := by
  have hs := quotient_stable hp.pos hj
  rw [encoded_first_digit hp hD hpd,encoded_first_digit hp hD hpd,hs.1,hs.2,
    pow_succ,map_mul]
  ring

/-- Exact signed cancellation before any norm, at all non-crossing adjacent atoms. -/
theorem atom_pair_eq_zero {p q D k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hD : 0<D) (hpd : p∣D) (hqd : q∣D)
    (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q)
    (hsign : χ (-1)*η (-1)=-1) (hpk : ¬p∣k+1) (hqk : ¬q∣k+1) :
    atom χ η D k+atom χ η D (k+1)=0 := by
  unfold atom
  rw [column_succ hp hD hpd χ hpk,column_succ hq hD hqd η hqk]
  calc
    _ = (1+χ (-1)*η (-1))*(χ (((D-1).choose k : ℕ) : ZMod p)*
      η (((D-1).choose k : ℕ) : ZMod q)) := by ring
    _ = 0 := by rw [hsign]; ring

theorem sum_range_pairs (H : ℕ) (f : ℕ → ℂ) :
    (∑ k∈Finset.range (2*H),f k)=∑ i∈Finset.range H,(f (2*i)+f (2*i+1)) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Nat.mul_succ,Finset.sum_range_add,Finset.sum_range_succ,ih]
    simp only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,zero_add,Nat.add_zero]

/-- Entire coupled signed row equals ONLY its literal crossing pairs and the unit endpoint. -/
theorem sum_atom_eq_jumps {p q D : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hD : 0<D) (hodd : D%2=1) (hpd : p∣D) (hqd : q∣D)
    (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q)
    (hsign : χ (-1)*η (-1)=-1) :
    (∑ k∈Finset.range D,atom χ η D k)=
      1+∑ i∈jumpOrders p q D,(atom χ η D (2*i)+atom χ η D (2*i+1)) := by
  have he : D=2*(D/2)+1 := by omega
  have hlast : atom χ η D (D-1)=1 := by simp only [atom,Nat.choose_self,Nat.cast_one,map_one,mul_one]
  have hj : (∑ i∈Finset.range (D/2),(atom χ η D (2*i)+atom χ η D (2*i+1)))=
      ∑ i∈jumpOrders p q D,(atom χ η D (2*i)+atom χ η D (2*i+1)) := by
    unfold jumpOrders
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : p∣2*i+1 ∨ q∣2*i+1
    · rw [ite_eq_left hi]
    · rw [ite_eq_right hi]
      exact atom_pair_eq_zero hp hq hD hpd hqd χ η hsign
        (not_or.mp hi).1 (not_or.mp hi).2
  nth_rw 1 [he]
  rw [Finset.sum_range_succ,sum_range_pairs,hj,
    show 2*(D/2)=D-1 by omega,hlast]
  ring

theorem jumpOrders_card_le (p q D : ℕ) :
    (jumpOrders p q D).card≤D/p+D/q := by
  have hs (r : ℕ) : ((Finset.range (D/2)).filter (fun i => r∣2*i+1)).card≤D/r := by
    let A := (Finset.range (D/2)).filter (fun i => r∣2*i+1)
    have hsub : A.image (fun i => 2*i) ⊆ (Finset.range D).filter (fun k => r∣k+1) := by
      intro k hk
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
      have hi' := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
        have him := Finset.mem_range.mp hi'.1
        omega),hi'.2⟩
    have hc : (A.image (fun i => 2*i)).card=A.card :=
      Finset.card_image_of_injective _ (by intro i j hij; change 2*i=2*j at hij; omega)
    rw [←Nat.card_multiples D r]
    exact hc ▸ Finset.card_le_card hsub
  unfold jumpOrders
  rw [Finset.filter_or]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hs p) (hs q))

theorem norm_atom_le {p q : ℕ} (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q)
    (D k : ℕ) : ‖atom χ η D k‖≤1 := by
  unfold atom
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (η.norm_le_one _)).trans (χ.norm_le_one _)

/-- A uniform coupled estimate. It includes all prime-power lengths and all upper residues. -/
theorem norm_pairTrace_le {p q D : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hD : 0<D) (hodd : D%2=1) (hpd : p∣D) (hqd : q∣D)
    (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q)
    (hsign : χ (-1)*η (-1)=-1) :
    ‖pairTrace χ η D‖≤1/(D : ℝ)+2/(p : ℝ)+2/(q : ℝ) := by
  have hsum : ‖∑ i∈jumpOrders p q D,(atom χ η D (2*i)+atom χ η D (2*i+1))‖≤
      2*(jumpOrders p q D).card := by
    calc
      _ ≤ ∑ i∈jumpOrders p q D,‖atom χ η D (2*i)+atom χ η D (2*i+1)‖ := norm_sum_le _ _
      _ ≤ ∑ _i∈jumpOrders p q D,(2 : ℝ) := Finset.sum_le_sum (fun i _ =>
        (norm_add_le _ _).trans (by linarith [norm_atom_le χ η D (2*i),norm_atom_le χ η D (2*i+1)]))
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  have hb : ‖∑ k∈Finset.range D,atom χ η D k‖≤1+2*((D/p : ℕ)+(D/q : ℕ)) := by
    rw [sum_atom_eq_jumps hp hq hD hodd hpd hqd χ η hsign]
    calc
      _ ≤ ‖(1 : ℂ)‖+‖∑ i∈jumpOrders p q D,(atom χ η D (2*i)+atom χ η D (2*i+1))‖ := norm_add_le _ _
      _ ≤ _ := by
        simp only [norm_one]
        have hc : ((jumpOrders p q D).card : ℝ)≤(D/p : ℕ)+(D/q : ℕ) :=
          by exact_mod_cast jumpOrders_card_le p q D
        linarith
  unfold pairTrace
  rw [norm_div,Complex.norm_natCast]
  have hD0 : (0 : ℝ)<D := by exact_mod_cast hD
  have hp0 : (0 : ℝ)<p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ)<q := by exact_mod_cast hq.pos
  have hdp : ((D/p : ℕ) : ℝ)=(D : ℝ)/(p : ℝ) := Nat.cast_div hpd (by positivity)
  have hdq : ((D/q : ℕ) : ℝ)=(D : ℝ)/(q : ℝ) := Nat.cast_div hqd (by positivity)
  calc
    _ ≤ (1+2*((D/p : ℕ)+(D/q : ℕ)))/(D : ℝ) := div_le_div_of_nonneg_right hb hD0.le
    _ = _ := by
      simp only [hdp,hdq]
      field_simp [hD0.ne',hp0.ne',hq0.ne']
      ring

/-- The actual ordinary-prime quadratic residue column. -/
def quadraticColumn (p : ℕ) [Fact p.Prime] : DirichletCharacter ℂ p :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

theorem quadraticColumn_int (p : ℕ) [Fact p.Prime] (a : ℤ) :
    quadraticColumn p (a : ZMod p)=(legendreSym p a : ℂ) := rfl

theorem quadratic_opposite {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp4 : p%4=3) (hq4 : q%4=1) :
    quadraticColumn p (-1)*quadraticColumn q (-1)=-1 := by
  have hp2 : p≠2 := by omega
  have hq2 : q≠2 := by omega
  have hpmod : p%2=1 := by omega
  have hqmod : q%2=1 := by omega
  rw [show (-1 : ZMod p)=((-1 : ℤ) : ZMod p) by norm_cast,
    show (-1 : ZMod q)=((-1 : ℤ) : ZMod q) by norm_cast,
    quadraticColumn_int p (-1),quadraticColumn_int q (-1),legendreSym.at_neg_one hp2,
    legendreSym.at_neg_one hq2,ZMod.χ₄_nat_eq_if_mod_four,ZMod.χ₄_nat_eq_if_mod_four]
  norm_num [hp4,hq4,hpmod,hqmod]

/-- The same exact coupled cancellation covers every positive pair of prime-power exponents. -/
theorem norm_quadratic_primePower_row_le {p q r s : ℕ}
    [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hp4 : p%4=3) (hq4 : q%4=1) (hr : 0<r) (hs : 0<s) :
    ‖pairTrace (quadraticColumn p) (quadraticColumn q) (p^r*q^s)‖≤
      1/(p^r*q^s : ℕ)+2/(p : ℝ)+2/(q : ℝ) := by
  have hpmod : p%2=1 := by omega
  have hqmod : q%2=1 := by omega
  have hodd : (p^r*q^s)%2=1 := by
    have hpr : p^r%2=1 := by rw [Nat.pow_mod,hpmod]; norm_num
    have hqs : q^s%2=1 := by rw [Nat.pow_mod,hqmod]; norm_num
    rw [Nat.mul_mod,hpr,hqs]
  exact norm_pairTrace_le hp.out hq.out (Nat.mul_pos (Nat.pow_pos hp.out.pos) (Nat.pow_pos hq.out.pos))
    hodd (dvd_mul_of_dvd_left (dvd_pow_self p hr.ne') _)
    (dvd_mul_of_dvd_right (dvd_pow_self q hs.ne') _) _ _ (quadratic_opposite hp4 hq4)

/-- Totalized literal ordinary-prime pair trace. -/
def quadraticTrace (p q : ℕ) : ℂ :=
  if h : p.Prime ∧ q.Prime then
    (let : Fact p.Prime := ⟨h.1⟩;let : Fact q.Prime := ⟨h.2⟩;
      pairTrace (quadraticColumn p) (quadraticColumn q) (p*q)) else 0

theorem quadraticTrace_norm {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp4 : p%4=3) (hq4 : q%4=1) :
    ‖quadraticTrace p q‖≤1/(p*q : ℕ)+2/(p : ℝ)+2/(q : ℝ) := by
  unfold quadraticTrace
  rw [dite_eq_left ⟨hp,hq⟩]
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  simpa only [pow_one] using norm_quadratic_primePower_row_le hp4 hq4 (by decide : 0<1) (by decide : 0<1)

/-- The actual balanced native prime band, with a literal quadratic-parity condition. -/
def primeBand (J residue : ℕ) : Finset ℕ :=
  (Finset.range (2^(J+1))).filter (fun p => 2^J≤p ∧ p.Prime ∧ p%4=residue)

/-- Whole coupled actual prime sum. The mask is outside the complete binomial row. -/
def balancedPacket (J : ℕ) (y : ℝ) (mask : ℕ → ℕ → ℂ) : ℂ :=
  ∑ p∈primeBand J 3,∑ q∈primeBand J 1,
    (ArithmeticFunction.vonMangoldt p : ℂ)*(ArithmeticFunction.vonMangoldt q : ℂ)*
      primePhase y (p*q)*mask p q*quadraticTrace p q

theorem primeBand_mem {J residue p : ℕ} (hp : p∈primeBand J residue) :
    p<2^(J+1) ∧ 2^J≤p ∧ p.Prime ∧ p%4=residue := by
  have h := Finset.mem_filter.mp hp
  exact ⟨Finset.mem_range.mp h.1,h.2⟩

theorem primeBand_card_le (J residue : ℕ) : (primeBand J residue).card≤2^(J+1) := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

theorem vonMangoldt_band_le {J residue p : ℕ} (hp : p∈primeBand J residue) :
    ArithmeticFunction.vonMangoldt p≤(J+1 : ℕ) := by
  have hm := primeBand_mem hp
  have hl : Real.log (p : ℝ)≤Real.log (2^(J+1) : ℕ) :=
    Real.log_le_log (by exact_mod_cast hm.2.2.1.pos) (by exact_mod_cast hm.1.le)
  have hlog2 : Real.log 2≤1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    norm_num at h
    exact h
  have hpow : Real.log (2^(J+1) : ℕ)=(J+1 : ℕ)*Real.log 2 := by
    rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  exact ArithmeticFunction.vonMangoldt_le_log.trans (hl.trans (by
    rw [hpow]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) hlog2))

theorem quadraticTrace_band_le {J p q : ℕ}
    (hp : p∈primeBand J 3) (hq : q∈primeBand J 1) :
    ‖quadraticTrace p q‖≤5/(2^J : ℕ) := by
  have hpm := primeBand_mem hp
  have hqm := primeBand_mem hq
  have hB : (0 : ℝ)<(2^J : ℕ) := by exact_mod_cast (Nat.pow_pos (by decide : 0<(2 : ℕ)))
  have hpB : ((2^J : ℕ) : ℝ)≤p := by exact_mod_cast hpm.2.1
  have hqB : ((2^J : ℕ) : ℝ)≤q := by exact_mod_cast hqm.2.1
  have hpqB : ((2^J : ℕ) : ℝ)≤(p*q : ℕ) := by
    exact_mod_cast (hpm.2.1.trans (Nat.le_mul_of_pos_right p hqm.2.2.1.pos))
  have h1 := one_div_le_one_div_of_le hB hpqB
  have h2 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ)≤2) hB hpB
  have h3 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ)≤2) hB hqB
  have hh := quadraticTrace_norm hpm.2.2.1 hqm.2.2.1 hpm.2.2.2 hqm.2.2.2
  simp only [div_eq_mul_inv] at h1 h2 h3 hh ⊢
  linarith

/-- The complete opposite-parity packet is square-root sized, uniformly in every actual height. -/
theorem norm_balancedPacket_le (J : ℕ) (y : ℝ) (mask : ℕ → ℕ → ℂ)
    (hm : ∀ p∈primeBand J 3,∀ q∈primeBand J 1,‖mask p q‖≤1) :
    ‖balancedPacket J y mask‖≤20*((J+1 : ℕ) : ℝ)^2*(2^J : ℕ) := by
  have hterm (p : ℕ) (hp : p∈primeBand J 3) (q : ℕ) (hq : q∈primeBand J 1) :
      ‖(ArithmeticFunction.vonMangoldt p : ℂ)*(ArithmeticFunction.vonMangoldt q : ℂ)*
        primePhase y (p*q)*mask p q*quadraticTrace p q‖≤
          ((J+1 : ℕ) : ℝ)^2*(5/(2^J : ℕ)) := by
    simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      norm_primePhase,mul_one]
    have hL : ArithmeticFunction.vonMangoldt p*ArithmeticFunction.vonMangoldt q≤((J+1 : ℕ) : ℝ)^2 := by
      simpa only [pow_two] using mul_le_mul (vonMangoldt_band_le hp) (vonMangoldt_band_le hq)
        ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
    have hM := mul_le_of_le_one_right
      (mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := p))
        (ArithmeticFunction.vonMangoldt_nonneg (n := q))) (hm p hp q hq)
    exact mul_le_mul (hM.trans hL) (quadraticTrace_band_le hp hq) (norm_nonneg _) (sq_nonneg _)
  unfold balancedPacket
  calc
    _ ≤ ∑ p∈primeBand J 3,∑ q∈primeBand J 1,
        ‖(ArithmeticFunction.vonMangoldt p : ℂ)*(ArithmeticFunction.vonMangoldt q : ℂ)*
          primePhase y (p*q)*mask p q*quadraticTrace p q‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p _ => norm_sum_le _ _))
    _ ≤ ∑ _p∈primeBand J 3,∑ _q∈primeBand J 1,
        ((J+1 : ℕ) : ℝ)^2*(5/(2^J : ℕ)) :=
      Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun q hq => hterm p hp q hq))
    _ = ((primeBand J 3).card : ℝ)*(primeBand J 1).card*
        (((J+1 : ℕ) : ℝ)^2*(5/(2^J : ℕ))) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ ((2^(J+1) : ℕ) : ℝ)*(2^(J+1) : ℕ)*
        (((J+1 : ℕ) : ℝ)^2*(5/(2^J : ℕ))) := by
      gcongr
      · exact_mod_cast primeBand_card_le J 3
      · exact_mod_cast primeBand_card_le J 1
    _ = _ := by
      have h2 : ((2^J : ℕ) : ℝ)≠0 := by positivity
      rw [pow_succ]
      push_cast
      field_simp
      ring

/-- The whole literal balanced packet misses every positive-power zero signal above one half. -/
theorem tendsto_balancedPacket_source_zero {beta : ℝ} (hb : 1/2<beta)
    (y : ℕ → ℝ) (mask : ℕ → ℕ → ℕ → ℂ)
    (hm : ∀ J,∀ p∈primeBand J 3,∀ q∈primeBand J 1,‖mask J p q‖≤1) :
    Tendsto (fun J : ℕ => ((Real.exp (-2*beta*Real.log 2)^J : ℝ) : ℂ)*
      balancedPacket J (y J) (mask J)) atTop (𝓝 0) := by
  let a := Real.exp ((1-2*beta)*Real.log 2)
  have ha : 0<a := Real.exp_pos _
  have ha1 : a<1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by linarith)
    (Real.log_pos (by norm_num)))
  have hrate : a=Real.exp (-2*beta*Real.log 2)*2 := by
    unfold a
    rw [show (1-2*beta)*Real.log 2=-2*beta*Real.log 2+Real.log 2 by ring,
      Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ)<2)]
  have ht := (ArithmeticOperatorFloorInverseAudit.tendsto_shifted_polynomial_geometric 2 ha ha1).const_mul 20
  apply squeeze_zero_norm (fun J => ?_) (by simpa only [mul_zero] using ht)
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (Real.exp_pos _).le _)]
  calc
    _ ≤ Real.exp (-2*beta*Real.log 2)^J*(20*((J+1 : ℕ) : ℝ)^2*(2^J : ℕ)) :=
      mul_le_mul_of_nonneg_left (norm_balancedPacket_le J _ _ (hm J)) (by positivity)
    _ = _ := by rw [hrate,mul_pow,Nat.cast_pow,Nat.cast_ofNat]; ring

/-- Source gate rejection is exact and uniform for the entire bounded outside-mask class. -/
theorem balancedPacket_nonzero_source_impossible {beta : ℝ} (hb : 1/2<beta)
    (y : ℕ → ℝ) (mask : ℕ → ℕ → ℕ → ℂ)
    (hm : ∀ J,∀ p∈primeBand J 3,∀ q∈primeBand J 1,‖mask J p q‖≤1)
    {v : ℂ} (hv : v≠0) :
    ¬Tendsto (fun J : ℕ => ((Real.exp (-2*beta*Real.log 2)^J : ℝ) : ℂ)*
      balancedPacket J (y J) (mask J)) atTop (𝓝 v) := by
  intro hs
  exact hv (tendsto_nhds_unique hs (tendsto_balancedPacket_source_zero hb y mask hm))

end RiemannGaussian.ArithmeticOperatorCrossUnitCancellation

#lint+ in RiemannGaussian.ArithmeticOperatorCrossUnitCancellation

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty cross-unit cancellation audit."
  logInfo m!"Cross-unit cancellation: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-cross-cancellation"
  IO.FS.writeFile ".lake/arithmetic-operator-cross-cancellation/axioms.json"
    (Json.mkObj [("scope",toJson "literal opposite-parity common binomial rows and balanced ordinary-prime source rejection"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
