/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointPrimeCells

/-!
# A literal interior four/five-prime population payment

Concrete ordered cofactor cells turn the finite-family comparison into an
independent signed payment, with no numerical surplus premise. The favorable
five-prime cell pays the whole adverse four-prime selection and leaves a
positive factorial-kernel reserve. A bounded phase translation supplies such
a window eventually at every fixed nonzero height on the original dyadic
schedule. The full complementary core stays signed. This one interior
population is not a payment of the whole angular region or the joint floor.
-/

namespace RiemannGaussian.ZetaRieszCellCompensation
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic ZetaRieszFourPrimeCells
open ZetaRieszJointPrimeCells

/-- Concrete adverse cofactor logs, scaled by the exact total-log window
start rather than by a frozen saddle point. -/
def fourLo (t : ℝ) : Fin 3 → ℝ := ![3/50*t,23/100*t,6/25*t]

/-- The three adverse cofactor windows each have relative width 1/1000. -/
def fourWidth (t : ℝ) : Fin 3 → ℝ := fun _ => t/1000

/-- A favorable ordered five-prime cell separated from the four-prime
population by prime count. No prime or complete series is added. -/
def fiveLo (t : ℝ) : Fin 4 → ℝ := ![3/50*t,7/100*t,11/50*t,49/200*t]

/-- The four favorable cofactor windows each have relative width 1/250. -/
def fiveWidth (t : ℝ) : Fin 4 → ℝ := fun _ => t/250

private theorem five_cap_lower {L t h : ℝ} (ht : 0 < t) (hh : h ≤ t/1000)
    (hLlo : (17/25 : ℝ)*t ≤ L) (hLhi : L ≤ (18/25 : ℝ)*t) :
    (3/50 : ℝ)*t ≤ ZetaRieszFivePrimeCells.boxCap L t h (fiveLo t)
      (fun i => fiveLo t i+fiveWidth t i) := by
  have h₁ : (29/1000 : ℝ)*t ≤ min ((3/50 : ℝ)*t)
      (max 0 (min (L-t-h+(11/50 : ℝ)*t+(7/100 : ℝ)*t+(3/50 : ℝ)*t)
        (t-L-((11/50 : ℝ)*t+t/250)))) := by
    apply le_min (by linarith)
    apply le_trans _ (le_max_right _ _)
    apply le_min <;> linarith
  have h₂ : (31/1000 : ℝ)*t ≤ min ((3/50 : ℝ)*t)
      (max 0 (min (L-t-h+(49/200 : ℝ)*t+(7/100 : ℝ)*t+(3/50 : ℝ)*t)
        (t-L-((49/200 : ℝ)*t+t/250)))) := by
    apply le_min (by linarith)
    apply le_trans _ (le_max_right _ _)
    apply le_min <;> linarith
  unfold ZetaRieszFivePrimeCells.boxCap fiveLo fiveWidth
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  have h₃ : 0 ≤ min ((3/50 : ℝ)*t) (max 0
      (min (L-((49/200 : ℝ)*t+t/250)-((11/50 : ℝ)*t+t/250))
        ((49/200 : ℝ)*t+(11/50 : ℝ)*t+(7/100 : ℝ)*t+(3/50 : ℝ)*t-L))) :=
    le_min (by positivity) (le_max_left _ _)
  linarith

/-- The concrete favorable cell has a uniform angular credit, already
including the proved allocation and prime-population factor 997/1000. -/
theorem five_angular_credit {L t h : ℝ} (ht : 0 < t) (hh : h ≤ t/1000)
    (hLlo : (17/25 : ℝ)*t ≤ L) (hLhi : L ≤ (18/25 : ℝ)*t) :
    (1/6000000 : ℝ) ≤
      (997/1000 : ℝ)*(t/L)*ZetaRieszFivePrimeCells.boxCap L t h (fiveLo t)
        (fun i => fiveLo t i+fiveWidth t i)*
        (1/(t-∑ i, fiveLo t i))*(∏ i, fiveWidth t i/(fiveLo t i+fiveWidth t i)) := by
  have hL : 0 < L := lt_of_lt_of_le (by positivity) hLlo
  have hratio : (25/18 : ℝ) ≤ t/L := (le_div_iff₀ hL).mpr (by nlinarith)
  have hc := five_cap_lower ht hh hLlo hLhi
  have hmul := mul_le_mul_of_nonneg_left (mul_le_mul hratio hc
    (by positivity : (0 : ℝ) ≤ (3/50)*t) (div_nonneg ht.le hL.le))
    (by norm_num : (0 : ℝ) ≤ 997/1000)
  have hv : 0 < t-∑ i, fiveLo t i := by
    norm_num [Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,fiveLo,Fin.sum_univ_four]
    linarith
  have hprod : 0 ≤ ∏ i, fiveWidth t i/(fiveLo t i+fiveWidth t i) := by
    apply Finset.prod_nonneg
    intro i _
    fin_cases i <;> norm_num [Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,fiveLo,fiveWidth] <;> positivity
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hmul (one_div_nonneg.mpr hv.le)) hprod
  have he : (997/1000 : ℝ)*((25/18)*((3/50)*t))*(1/(t-∑ i, fiveLo t i))*
      (∏ i, fiveWidth t i/(fiveLo t i+fiveWidth t i)) = 997/5014820160 := by
    norm_num [Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,fiveLo,fiveWidth,Fin.sum_univ_four,Fin.prod_univ_four]
    ring_nf
    field_simp [ht.ne']
  apply (by norm_num : (1/6000000 : ℝ) ≤ 997/5014820160).trans
  rw [← he]
  simpa only [mul_assoc] using hb

/-- The whole adverse cell has a uniform debit including all four prime
counts. This is an upper bound for its exact positive-coefficient cap. -/
theorem four_angular_debit {L t h : ℝ} (ht : 0 < t)
    (hhu : h ≤ t/1000) (hLlo : (17/25 : ℝ)*t ≤ L) :
    (501/500 : ℝ)*((t+h)/L)*ZetaRieszFourPrimeCells.boxCap L t h (fourLo t)
      (fun i => fourLo t i+fourWidth t i)*
      (1/(t-∑ i, (fourLo t i+fourWidth t i)))*(∏ i, fourWidth t i/fourLo t i) ≤
      (1/16000000 : ℝ) := by
  have hL : 0 < L := lt_of_lt_of_le (by positivity) hLlo
  have hratio : (t+h)/L ≤ (1001/1000 : ℝ)*(25/17) :=
    (div_le_iff₀ hL).mpr (by nlinarith)
  have hc : ZetaRieszFourPrimeCells.boxCap L t h (fourLo t)
      (fun i => fourLo t i+fourWidth t i) ≤ (61/1000 : ℝ)*t := by
    exact (min_le_left _ _).trans_eq (by norm_num [Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,fourLo,fourWidth]; ring)
  have hcap0 := ZetaRieszFourPrimeCells.boxCap_nonneg L t h
    (lo := fourLo t) (hi := fun i => fourLo t i+fourWidth t i)
    (by norm_num [Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,fourLo,fourWidth]; positivity)
  have hmul := mul_le_mul_of_nonneg_left (mul_le_mul hratio hc hcap0 (by norm_num))
    (by norm_num : (0 : ℝ) ≤ 501/500)
  have hv : 0 < t-∑ i, (fourLo t i+fourWidth t i) := by
    norm_num [Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,fourLo,fourWidth,Fin.sum_univ_three]
    linarith
  have hprod : 0 ≤ ∏ i, fourWidth t i/fourLo t i := by
    apply Finset.prod_nonneg
    intro i _
    fin_cases i <;> norm_num [Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,fourLo,fourWidth] <;> positivity
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hmul (one_div_nonneg.mpr hv.le)) hprod
  have he : (501/500 : ℝ)*(((1001/1000)*(25/17))*((61/1000)*t))*
      (1/(t-∑ i, (fourLo t i+fourWidth t i)))*(∏ i, fourWidth t i/fourLo t i) =
      10197187/175293120000000 := by
    norm_num [Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,fourLo,fourWidth,Fin.sum_univ_three,Fin.prod_univ_three]
    ring_nf
    field_simp [ht.ne']
  apply le_trans _ (by norm_num : (10197187/175293120000000 : ℝ) ≤ 1/16000000)
  rw [← he]
  simpa only [mul_assoc] using hb

/-- The conservative upper and lower factorial envelopes are directly
comparable with the ORIGINAL moment, on one fixed total-log interval. -/
theorem radial_envelopes {N : ℕ} {t h : ℝ} (ht : 0 < t) (hNt : (N : ℝ) ≤ t)
    (hh : 0 ≤ h) (hhu : h ≤ 1/100000) :
    Real.exp (-t/2)*(t+h)^N/N.factorial ≤
      (11/10 : ℝ)*(Real.exp (-(t+h)/2)*t^N/N.factorial) := by
  have hth : 0 < t+h := by linarith
  have hlog := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hth ht)) (Nat.cast_nonneg N)
  rw [Real.log_div hth.ne' ht.ne'] at hlog
  have hratio : (N : ℝ)/t ≤ 1 := (div_le_iff₀ ht).mpr (by linarith)
  have hid : (N : ℝ)*((t+h)/t-1) = h*((N : ℝ)/t) := by field_simp; ring
  rw [hid] at hlog
  have hexp : -t/2+(N : ℝ)*Real.log (t+h) ≤
      (1/100 : ℝ)+(-(t+h)/2+(N : ℝ)*Real.log t) := by
    nlinarith [mul_le_mul_of_nonneg_left hratio hh]
  have hpow (x : ℝ) (hx : 0 < x) : x^N = Real.exp ((N : ℝ)*Real.log x) := by
    rw [Real.exp_nat_mul,Real.exp_log hx]
  rw [hpow t ht,hpow (t+h) hth,← Real.exp_add,← Real.exp_add]
  have hb : Real.exp (1/100 : ℝ) ≤ 11/10 :=
    (Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1/100)
      (by norm_num : (1/100 : ℝ) < 1)).trans (by norm_num)
  calc
    _ ≤ Real.exp ((1/100 : ℝ)+(-(t+h)/2+(N : ℝ)*Real.log t))/N.factorial :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = Real.exp (1/100 : ℝ)*(Real.exp (-(t+h)/2+(N : ℝ)*Real.log t)/N.factorial) := by
      rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (by positivity)


/-- A strict quantitative surplus for the concrete cells, using the same
moment and phase window. It includes both population costs and a conservative
radial/phase comparison, without any hypothetical-zero assumption. -/
theorem cell_budget {N : ℕ} {L t h y : ℝ}
    (ht : 1 ≤ t) (hNt : (N : ℝ) ≤ t) (hh : 0 ≤ h) (hhu : h ≤ 1/100000)
    (hLlo : (17/25 : ℝ)*t ≤ L) (hLhi : L ≤ (18/25 : ℝ)*t)
    (hphase : Real.cos (y*t) ≤ -(1/2 : ℝ)) (hε : |y| * h ≤ 1/10000) :
    (1/40000000 : ℝ)*(Real.exp (-(t+h)/2)*t^N/N.factorial)*
      max 0 (-Real.cos (y*t)-|y| * h)*h ≤
      cellCredit N L t h y (fiveLo t) (fiveWidth t)-
        cellDebit N L t h y (fourLo t) (fourWidth t) := by
  let Vm := Real.exp (-(t+h)/2)*t^N/N.factorial
  let Vp := Real.exp (-t/2)*(t+h)^N/N.factorial
  let φm := max 0 (-Real.cos (y*t)-|y| * h)
  let φp := max 0 (-Real.cos (y*t))+|y| * h
  let B := Vm*φm*h
  have ht0 : 0 < t := by linarith
  have hsmall : h ≤ t/1000 := by linarith
  have hVm : 0 ≤ Vm := by dsimp [Vm]; positivity
  have hVp : 0 ≤ Vp := by dsimp [Vp]; positivity
  have hφm : 0 ≤ φm := le_max_left _ _
  have hφp : 0 ≤ φp := add_nonneg (le_max_left _ _) (mul_nonneg (abs_nonneg y) hh)
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg hVm hφm) hh
  have hφ : φp ≤ 2*φm := by
    dsimp [φp,φm]
    rw [max_eq_right (by linarith : 0 ≤ -Real.cos (y*t)),
      max_eq_right (by linarith : 0 ≤ -Real.cos (y*t)-|y| * h)]
    linarith
  have hrad : Vp ≤ (11/10 : ℝ)*Vm := radial_envelopes ht0 hNt hh hhu
  have hsc := mul_le_mul_of_nonneg_right (mul_le_mul hrad hφ hφp (by positivity)) hh
  have hsc' : Vp*φp*h ≤ (11/5 : ℝ)*B := by dsimp [B]; nlinarith only [hsc]
  have hcredit : B/6000000 ≤ cellCredit N L t h y (fiveLo t) (fiveWidth t) := by
    have hh' := mul_le_mul_of_nonneg_right (five_angular_credit ht0 hsmall hLlo hLhi) hB
    convert hh' using 1 <;> first | rfl | (dsimp [cellCredit,B,Vm,φm]; ring)
  have hdebit : cellDebit N L t h y (fourLo t) (fourWidth t) ≤ (11/5 : ℝ)*B/16000000 := by
    have hh' := mul_le_mul_of_nonneg_right (four_angular_debit ht0 hsmall hLlo)
      (show 0 ≤ Vp*φp*h by positivity)
    have hs' := mul_le_mul_of_nonneg_left hsc' (by norm_num : (0 : ℝ) ≤ 1/16000000)
    have hd : cellDebit N L t h y (fourLo t) (fourWidth t) ≤
        (1/16000000 : ℝ)*(Vp*φp*h) := by
      convert hh' using 1 <;> first | rfl | (dsimp [cellDebit,Vp,φp]; ring)
    exact (hd.trans hs').trans_eq (by ring)
  change (1/40000000 : ℝ)*Vm*φm*h ≤ _
  have he : (1/40000000 : ℝ)*Vm*φm*h = B/40000000 := by dsimp [B]; ring
  rw [he]
  linarith

/-- Actual moving lengths lie in the concrete compensation chamber
throughout each literal core window. The radial variable is not frozen. -/
theorem eventually_core_chamber {u h : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      1 ≤ t ∧ (17/25 : ℝ)*t ≤ SquarefreeVaughanLogSource.length u N ∧
        SquarefreeVaughanLogSource.length u N ≤ (18/25 : ℝ)*t := by
  filter_upwards [ZetaRieszFivePrimePairSupply.eventually_core_cutoff_ratio hu.le hU,
    eventually_ge_atTop (1 : ℕ)] with N hN hn t htlo hthi
  have hnR : (1 : ℝ) ≤ N := by exact_mod_cast hn
  have ht : 1 ≤ t := by nlinarith
  have hth : 0 < t+h := by linarith
  have hcut := hN (t+h) (by linarith) hthi
  have hlow := (le_div_iff₀ hth).mp hcut.1
  have hhigh := (div_le_iff₀ hth).mp hcut.2
  exact ⟨ht,by nlinarith,by nlinarith⟩

/-- The concrete cells satisfy every ordering, saturation and population
condition for the exact finite-family comparison. -/
theorem cell_geometry {N : ℕ} {L t h : ℝ} (ht : 1 ≤ t)
    (hNt : (N : ℝ) ≤ t) (hhu : h ≤ 1/100000)
    (hLlo : (17/25 : ℝ)*t ≤ L) (hLhi : L ≤ (18/25 : ℝ)*t) :
    ((∀ a, (1/100 : ℝ)*N ≤ fourLo t a) ∧
      (∀ a, (1/1000 : ℝ)*N ≤ fourWidth t a) ∧
      (∀ a b, a < b → fourLo t a+fourWidth t a ≤ fourLo t b) ∧
      (1/100 : ℝ)*N ≤ t-(∑ a, (fourLo t a+fourWidth t a)) ∧
      fourLo t 2+fourWidth t 2 ≤ t-(∑ a, (fourLo t a+fourWidth t a))) ∧
    ((∀ a, (1/100 : ℝ)*N ≤ fiveLo t a) ∧
      (∀ a, (1/1000 : ℝ)*N ≤ fiveWidth t a) ∧
      (∀ a b, a < b → fiveLo t a+fiveWidth t a ≤ fiveLo t b) ∧
      (1/100 : ℝ)*N ≤ t-(∑ a, (fiveLo t a+fiveWidth t a)) ∧
      fiveLo t 3+fiveWidth t 3 ≤ t-(∑ a, (fiveLo t a+fiveWidth t a)) ∧
      t-(∑ a, fiveLo t a)+h ≤ (9/16 : ℝ)*t ∧
      t-fiveLo t 3-fiveLo t 2+h ≤ L ∧
      L ≤ t-(fiveLo t 1+fiveWidth t 1)-(fiveLo t 0+fiveWidth t 0)) := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  constructor
  · refine ⟨?_,?_,?_,?_,?_⟩
    · intro a; fin_cases a <;> norm_num [Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,fourLo] <;> nlinarith
    · intro a; norm_num [fourWidth]; nlinarith
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp at hab <;> norm_num [Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,fourLo,fourWidth] <;> linarith
    · norm_num [Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,fourLo,fourWidth,Fin.sum_univ_three]; nlinarith
    · norm_num [Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,fourLo,fourWidth,Fin.sum_univ_three]; nlinarith
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro a; fin_cases a <;> norm_num [Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,fiveLo] <;> nlinarith
    · intro a; norm_num [fiveWidth]; nlinarith
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp at hab <;> norm_num [Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,fiveLo,fiveWidth] <;> linarith
    · norm_num [Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,fiveLo,fiveWidth,Fin.sum_univ_four]; nlinarith
    · norm_num [Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,fiveLo,fiveWidth,Fin.sum_univ_four]; nlinarith
    · norm_num [Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,fiveLo,Fin.sum_univ_four]; linarith
    · norm_num [Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,fiveLo]; linarith
    · norm_num [Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,fiveLo,fiveWidth]; linarith

/-- A genuine arithmetic compensation theorem: the selected five-prime
cell pays the entire adverse four-prime cell and leaves an explicit positive
surplus on each interior negative phase window. Every other core label stays
signed. This is one concrete population payment, not the whole joint floor. -/
theorem eventually_paired_core_floor {u h : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let D4 := adverseCell S L t h y (fourLo t) (fourWidth t)
      let D5 := supplyCell t h y (fiveLo t) (fiveWidth t)
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      Real.cos (y*t) ≤ -(1/2 : ℝ) → |y| * h ≤ 1/10000 →
      (∑ n ∈ S\(D4 ∪ D5),
        residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (1/40000000 : ℝ)*(Real.exp (-(t+h)/2)*t^N/N.factorial)*
          max 0 (-Real.cos (y*t)-|y| * h)*h ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  filter_upwards [eventually_joint_cell_family_floor hu hU hh hhu
      (by norm_num : (0 : ℝ) < 1/100) (by norm_num : (0 : ℝ) < 1/1000)
      (ι := ℕ) (κ := ℕ),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_core_chamber hu hU hh hhu)] with j hfloor hch t y
  dsimp only
  intro htlo hthi hphase hε
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  have hN : (N : ℝ) ≤ t := by dsimp [N]; nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have ht := hch t htlo hthi
  have hg := cell_geometry ht.1 hN hhu ht.2.1 ht.2.2
  have hf := hfloor {0} {0} (fun _ => fourLo t) (fun _ => fourWidth t)
    (fun _ => fiveLo t) (fun _ => fiveWidth t) t y htlo hthi
    (fun _ _ => hg.1) (fun _ _ => hg.2)
    (by intro a ha b hb hab; simp only [Finset.mem_singleton] at ha hb; omega)
  simp only [Finset.singleton_biUnion,Finset.sum_singleton] at hf
  have hb := cell_budget ht.1 hN hh.le hhu ht.2.1 ht.2.2 hphase hε
  linarith


/-- The explicit payment occurs eventually at every fixed nonzero height.
A bounded radial translation supplies a genuine favorable phase window;
its surplus is strictly positive, and the entire complementary carrier stays
signed. The beginning of this regime is existential. -/
theorem eventually_fixed_height_payment {u y : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : y ≠ 0) :
    ∃ h C : ℝ, 0 < h ∧ h ≤ 1/100000 ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℝ, 0 ≤ v ∧ v ≤ C ∧
        let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
        let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
        let t := 2*(N : ℝ)+v
        let L := SquarefreeVaughanLogSource.length u N
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let S := ZetaRieszParityPacket.coreBand u N K
        let D4 := adverseCell S L t h y (fourLo t) (fourWidth t)
        let D5 := supplyCell t h y (fiveLo t) (fiveWidth t)
        let V := Real.exp (-(t+h)/2)*t^N/N.factorial
        0 < V*h/100000000 ∧
          (∑ n ∈ S\(D4 ∪ D5),
            residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
              V*h/100000000 ≤ (ZetaRieszParityPacket.coreResponse u y N K).re := by
  obtain ⟨h,hh,hhu,_harc,hε₅⟩ := ZetaRieszPhaseBudget.exists_fixed_phase_width y
  obtain ⟨h₀,C,hh₀,hC,hphase⟩ := ZetaRieszCompensationSupply.exists_negative_phase_window hy
  have hε : |y| * h ≤ 1/10000 := by nlinarith [abs_nonneg y]
  refine ⟨h,C,hh,hhu,hC,?_⟩
  have htend : Tendsto (fun j => (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j : ℝ))
      atTop atTop := (tendsto_natCast_atTop_atTop (R := ℝ)).comp
        ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder
  filter_upwards [eventually_paired_core_floor hu hU hh hhu,
    htend.eventually_ge_atTop (100*(C+h+1))] with j hfloor hsize
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  obtain ⟨v,hv,hvC,hcos⟩ := hphase (2*(N : ℝ))
  let t := 2*(N : ℝ)+v
  have hNR : (1 : ℝ) ≤ N := by dsimp [N]; nlinarith
  have ht : 1 ≤ t := by dsimp [t]; nlinarith
  have htlo : (39/20 : ℝ)*N ≤ t := by dsimp [t]; nlinarith
  have hthi : t+h ≤ (203/100 : ℝ)*N := by dsimp [t,N]; nlinarith
  have hp : Real.cos (y*t) ≤ -(1/2 : ℝ) := hcos t le_rfl (by dsimp [t]; linarith)
  have hf := hfloor t y htlo hthi hp hε
  refine ⟨v,hv,hvC,?_⟩
  dsimp only
  have hV : 0 < Real.exp (-(t+h)/2)*t^N/N.factorial := by
    have ht0 : 0 < t := by linarith
    positivity
  have hφ : (2/5 : ℝ) ≤ max 0 (-Real.cos (y*t)-|y| * h) := by
    exact (show (2/5 : ℝ) ≤ -Real.cos (y*t)-|y| * h by linarith).trans (le_max_right _ _)
  have hb := mul_le_mul_of_nonneg_left hφ
    (show 0 ≤ (1/40000000 : ℝ)*(Real.exp (-(t+h)/2)*t^N/N.factorial)*h by positivity)
  refine ⟨by positivity,?_⟩
  change _ ≤ (ZetaRieszParityPacket.coreResponse u y N
    (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).re
  nlinarith only [hf,hb]

end
end RiemannGaussian.ZetaRieszCellCompensation
