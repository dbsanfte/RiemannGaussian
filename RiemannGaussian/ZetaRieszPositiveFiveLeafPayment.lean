/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPositiveFiveCellPayment

/-!
# Quantitative literal cost of an accepted positive-five leaf

The checked cap integral pays all five ordinary-prime sums. Endpoint
inflation tends to zero before the fixed arithmetic budget is spent.
-/

namespace RiemannGaussian.ZetaRieszPositiveFiveLeafPayment
noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators Classical
open ZetaRieszPositiveFiveCover ZetaRieszPositiveFiveCells
open ZetaRieszPositiveFiveCellPayment

/-- A nonempty accepted leaf pays its literal prime sum with a fixed
`1.003` counting factor and an arbitrarily small local arithmetic slack.
The threshold is uniform in the original masked set and moving length. -/
theorem eventually_active_leaf_mass_upper {lo hi owner : ℚ} {B : Cover.Box} {w : ℚ × ℚ}
    (hcheck : ZetaRieszPositiveFiveCover.check lo hi owner B w = true)
    (hwidth : ∀ i, (B i).1 < (B i).2)
    (hactive : ¬ ((B 2).2 ≤ (B 1).1 ∨ (cap lo hi B w.1 w.2).height ≤ offset lo B ∨
      (cap lo hi B w.1 w.2).b ≤ offset lo B))
    (hlo : (2 : ℝ) ≤ 3*(lo : ℝ)) (hhi : 4*(hi : ℝ) ≤ 3)
    {h δ ε : ℝ} (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (S : Finset ℕ) (L t : ℝ),
      (N : ℝ) ≤ t → (lo : ℝ)*(t+h) ≤ L → L ≤ (hi : ℝ)*t →
      (∑ n ∈ population B S L t h δ,
        max 0 (SquarefreeVaughanLogSource.coefficient L n).re/(n : ℝ)) ≤
        ((1003/1000 : ℝ)*(Cover.area B*w.2 : ℚ)+ε)*h := by
  have hc := hcheck
  simp only [ZetaRieszPositiveFiveCover.check,Bool.and_eq_true,decide_eq_true_eq] at hc
  have hv := hc.1.1
  have hw : (0 : ℝ) ≤ w.2 := by exact_mod_cast hc.1.2
  have hl : (0 : ℝ) < lo := by exact_mod_cast hv.1
  let l : Fin 3 → ℝ := fun i => (B i).1
  let d : Fin 3 → ℝ := fun i => (B i).2-(B i).1
  have hlpos (i : Fin 3) : 0 < l i := by dsimp [l]; exact_mod_cast (hv.2.2.2.1 i).1
  have hdpos (i : Fin 3) : 0 < d i := by dsimp [d]; exact_mod_cast sub_pos.mpr (hwidth i)
  have hupos (i : Fin 3) : (0 : ℝ) < (B i).2 :=
    (hlpos i).trans (by dsimp [l]; exact_mod_cast hwidth i)
  let R : ℝ := (cap lo hi B w.1 w.2).b
  let Q : ℝ := (cap lo hi B w.1 w.2).total
  let r : ℝ := offset lo B
  let c : ℝ := (cap lo hi B w.1 w.2).height-offset lo B
  have hr : 0 ≤ r := by dsimp [r]; exact_mod_cast (le_max_left 0 _ : (0 : ℚ) ≤ offset lo B)
  have hc0 : 0 ≤ c := by
    dsimp [c,cap]
    push_cast
    simpa only [add_sub_cancel_left] using
      (le_max_left 0 (min ((hi : ℝ)-(B 0).1) (1+2*(B 0).2-3*(lo : ℝ))))
  have hR : 0 < R := by
    have h := not_or.mp (not_or.mp hactive).2
    have hb : offset lo B < (cap lo hi B w.1 w.2).b := lt_of_not_ge h.2
    have hb' : r < R := by dsimp [r,R]; exact_mod_cast hb
    exact hr.trans_lt hb'
  obtain ⟨hRQ,hint⟩ := checked_cap_integral_le hcheck hactive
  change R < Q at hRQ
  have hsum : ((B 0).2 : ℝ)+(B 1).2+(B 2).2 < 1 := by exact_mod_cast hv.2.2.2.2.2
  have hR1 : R < 1 := by
    have hRle : R ≤ (B 1).2 := by dsimp [R,cap]; push_cast; exact min_le_left _ _
    linarith only [hRle,hsum,hupos 0,hupos 2]
  have hQ1 : Q < 1 := by dsimp [Q,cap]; push_cast; linarith only [hupos 0,hupos 1,hupos 2]
  have hQ0 : 0 < Q := hR.trans hRQ
  let den : ℝ := (lo : ℝ)*l 0*l 1*l 2
  let J : ℝ := (w.2 : ℝ)*den
  let V : ℝ := ∏ i, d i/l i
  have hden : 0 < den := by dsimp [den]; exact mul_pos (mul_pos (mul_pos hl (hlpos 0)) (hlpos 1)) (hlpos 2)
  have hJ : 0 ≤ J := mul_nonneg hw hden.le
  have hV : 0 < V := Finset.prod_pos (fun i _ => div_pos (hdpos i) (hlpos i))
  have hI : (∫ x : ℝ in 0..R, max 0 (min (x-r) c)/(x*(Q-x))) ≤ J := hint
  let fee : ℝ → ℝ := fun η => (1+η)/(lo : ℝ)*
    ((1001/1000 : ℝ)*(1+η)^3*V)*(10001/10000 : ℝ)*
      ((10003/10000 : ℝ)*((1+2*η/(Q-R))*J+2*η/(Q-R))+η)
  have harea : (0 : ℝ) ≤ (Cover.area B*w.2 : ℚ) := by
    push_cast
    apply mul_nonneg _ hw
    exact_mod_cast Finset.prod_nonneg (fun i _ => (hwidth i).le |> sub_nonneg.mpr)
  have hfee0 : fee 0 < (1003/1000 : ℝ)*(Cover.area B*w.2 : ℚ)+ε := by
    have he : fee 0 = ((1001/1000 : ℝ)*(10001/10000)*(10003/10000))*
        (Cover.area B*w.2 : ℚ) := by
      have hl0 : ((B 0).1 : ℝ) ≠ 0 := (hlpos 0).ne'
      have hl1 : ((B 1).1 : ℝ) ≠ 0 := (hlpos 1).ne'
      have hl2 : ((B 2).1 : ℝ) ≠ 0 := (hlpos 2).ne'
      dsimp [fee,V,J,den,l,d,Cover.area]
      simp only [Rat.cast_mul,Rat.cast_sub,Fin.prod_univ_three]
      norm_num
      field_simp [hl0,hl1,hl2,hl.ne']
      ring
    rw [he]
    nlinarith only [harea,hε]
  have hcont : ContinuousAt fee 0 := by dsimp [fee]; fun_prop
  have hseq := hcont.tendsto.comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hfev := hseq.eventually (eventually_lt_nhds hfee0)
  have hsmall := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (eventually_lt_nhds (show (0 : ℝ) < min 1 ((Q-R)/4) by positivity))
  obtain ⟨m,hm,hms⟩ := (hfev.and hsmall).exists
  let η : ℝ := 1/((m : ℝ)+1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η < 1 := (lt_min_iff.mp hms).1
  have hηgap : η ≤ (Q-R)/4 := (lt_min_iff.mp hms).2.le
  have hfee : fee η ≤ (1003/1000 : ℝ)*(Cover.area B*w.2 : ℚ)+ε := hm.le
  let a : ℝ := min (δ/2) (R/2)
  have ha : 0 < a := lt_min (half_pos hδ) (half_pos hR)
  have haδ : a ≤ δ := (min_le_left _ _).trans (by linarith only [hδ])
  have haR : a < R+η := (min_le_right _ _).trans_lt (by linarith only [hR,hη])
  have hpadgap : R+η < Q-η := by linarith only [hRQ,hηgap]
  let α : ℝ := min (l 0) (min (l 1) (l 2))
  let β : ℝ := min (d 0) (min (d 1) (d 2))
  have hα : 0 < α := lt_min (hlpos 0) (lt_min (hlpos 1) (hlpos 2))
  have hβ : 0 < β := lt_min (hdpos 0) (lt_min (hdpos 1) (hdpos 2))
  have hαi (i : Fin 3) : α ≤ l i := by
    fin_cases i
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hβi (i : Fin 3) : β ≤ d i := by
    fin_cases i
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hlarge : ∀ᶠ N : ℕ in atTop, h ≤ η*(N : ℝ) := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (h/η))]
      with N hN
    simpa only [mul_comm] using (div_le_iff₀ hη).mp hN
  have hlargei : ∀ᶠ N : ℕ in atTop, ∀ i : Fin 3, h*(B i).2 ≤ η*N*d i := by
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop (h*(B i).2/(η*d i)))] with N hN
    have hb := (div_le_iff₀ (mul_pos hη (hdpos i))).mp hN
    nlinarith only [hb]
  have hpaid := ZetaRieszPositiveFivePrimeTransfer.padded_fibre_integral_le hR hRQ hr hc0 hη.le hηgap
  have hpadI : (∫ x : ℝ in 0..R+η, max 0 (min (x-r) c)/(x*(Q-η-x))) ≤
      (1+2*η/(Q-R))*J+2*η/(Q-R) :=
    hpaid.trans (add_le_add (mul_le_mul_of_nonneg_left hI
      (by positivity : 0 ≤ 1+2*η/(Q-R))) le_rfl)
  filter_upwards [eventually_weightedPrimeMass_full_upper hh hhu hα hβ ha haR hpadgap hr hc0 hη,
    hlarge,hlargei,eventually_ge_atTop (1 : ℕ)]
    with N hprime hlarge hlargei hN S L t hNt hLlo hLhi
  have hNr : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have ht : 0 < t := hNr.trans_le hNt
  have hht : h ≤ η*t := hlarge.trans (mul_le_mul_of_nonneg_left hNt hη.le)
  have hlasti (i : Fin 3) : h*(B i).2 ≤ η*t*d i :=
    (hlargei i).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hNt hη.le) (hdpos i).le)
  have hgeom : R*(t+h) ≤ t*(R+η) := by nlinarith only [hht,mul_le_mul_of_nonneg_left hR1.le hh.le]
  have hsumouter : (∑ i, (outerLower B t i+outerWidth B t h i)) ≤ t*(1-(Q-η)) := by
    simp only [outerLower,outerWidth,Fin.sum_univ_three]
    dsimp [Q,cap]
    push_cast
    nlinarith only [hht,mul_le_mul_of_nonneg_left hsum.le hh.le]
  have hlower (i : Fin 3) : α*N ≤ outerLower B t i := by
    dsimp [outerLower]
    exact mul_le_mul (hαi i) hNt hNr.le (hlpos i).le |>.trans_eq (mul_comm _ _)
  have hwidth' (i : Fin 3) : β*N ≤ outerWidth B t h i := by
    have hb := mul_le_mul (hβi i) hNt hNr.le (hdpos i).le
    dsimp [outerWidth]
    change β*N ≤ t*d i+h*(B i).2
    nlinarith only [hb,mul_nonneg hh.le (hupos i).le]
  have hratio (i : Fin 3) : outerWidth B t h i/outerLower B t i ≤ (1+η)*(d i/l i) := by
    apply (div_le_iff₀ (mul_pos ht (hlpos i))).mpr
    have he : (1+η)*(d i/l i)*(t*l i) = (1+η)*t*d i := by
      field_simp [(hlpos i).ne']
    rw [he]
    change t*d i+h*(B i).2 ≤ _
    nlinarith only [hlasti i]
  have hprod : (∏ i, outerWidth B t h i/outerLower B t i) ≤ (1+η)^3*V := by
    have h := Finset.prod_le_prod (s := Finset.univ) (fun i _ => div_nonneg
      ((mul_pos hβ hNr).le.trans (hwidth' i)) ((mul_pos hα hNr).le.trans (hlower i)))
      (fun i _ => hratio i)
    simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using h
  let F : ℝ := (10003/10000 : ℝ)*((1+2*η/(Q-R))*J+2*η/(Q-R))+η
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hprim := hprime (outerLower B t) (outerWidth B t h) t hNt hlower hwidth' hsumouter
  have hprim' : weightedPrimeMass (outerLower B t) (outerWidth B t h) a (R+η) r c t h ≤
      ((1001/1000 : ℝ)*(1+η)^3*V)*((10001/10000 : ℝ)*h/t)*F := by
    apply hprim.trans
    apply mul_le_mul
    · apply mul_le_mul_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ (10001/10000 : ℝ)*h/t)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 1001/1000)
    · exact add_le_add (mul_le_mul_of_nonneg_left hpadI (by norm_num : (0 : ℝ) ≤ 10003/10000)) le_rfl
    · have hnonneg : 0 ≤ ∫ x : ℝ in 0..R+η, max 0 (min (x-r) c)/(x*(Q-η-x)) := by
        apply intervalIntegral.integral_nonneg (by linarith only [hR,hη])
        intro x hx
        exact div_nonneg (le_max_left _ _) (mul_nonneg hx.1 (by linarith only [hx.2,hpadgap]))
      positivity
    · positivity
  have hmass := population_mass_le_primeMass hv w hlo hhi S ht hh.le haδ hδ.le hgeom hLlo hLhi
  calc
    _ ≤ ((t+h)/(lo : ℝ))*weightedPrimeMass (outerLower B t) (outerWidth B t h) a (R+η) r c t h := hmass
    _ ≤ ((t+h)/(lo : ℝ))*
        (((1001/1000 : ℝ)*(1+η)^3*V)*((10001/10000 : ℝ)*h/t)*F) :=
      mul_le_mul_of_nonneg_left hprim' (by positivity)
    _ ≤ (t*(1+η)/(lo : ℝ))*
        (((1001/1000 : ℝ)*(1+η)^3*V)*((10001/10000 : ℝ)*h/t)*F) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by nlinarith only [hht]) hl.le)
        (by positivity)
    _ = fee η*h := by dsimp [fee,F]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hfee hh.le

end
end RiemannGaussian.ZetaRieszPositiveFiveLeafPayment
