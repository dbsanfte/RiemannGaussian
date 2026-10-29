/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WeightedTuples

/-! Finite geometric potential for the actually acquired weighted menu. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1WeightedPotential
open SemiprimeD1WeightedTuples
open scoped BigOperators

/-- Finite geometric majorant; no infinite-product oracle is used. -/
theorem finite_geometric_le {x : ℝ} (hx : 0≤x) (hx1 : x<1) (n : ℕ) :
    (∑ i∈Finset.range n,x^i)≤ (1-x)⁻¹ := by
  have he := geom_sum_mul_neg x n
  have hp : 0≤x^n := pow_nonneg hx _
  rw [← one_div]
  apply (le_div_iff₀ (sub_pos.mpr hx1)).mpr
  simpa only [one_div] using (show (∑ i∈Finset.range n,x^i)*(1-x)≤1 by linarith)

/-- Literal finite Euler normalizer, one factor per acquired positive mode. -/
noncomputable def normalizer (ws : List ℕ) (a : ℝ) : ℝ :=
  (ws.map fun (w : ℕ) => (1-Real.exp (-a*w))⁻¹).prod

/-- Every factor and normalizer is positive for original positive weights. -/
theorem normalizer_pos {ws : List ℕ} {a : ℝ} (ha : 0<a) (hw : ∀w∈ws,0<w) :
    0<normalizer ws a := by
  apply List.prod_pos
  intro x hx
  obtain ⟨w,hw',rfl⟩ := List.mem_map.mp hx
  apply inv_pos.mpr
  apply sub_pos.mpr
  rw [Real.exp_lt_one_iff]
  have hp : (0:ℝ)<w := Nat.cast_pos.mpr (hw w hw')
  nlinarith

/-- Exact coefficient-free finite potential bound for the executed menu. -/
theorem length_le_potential {ws : List ℕ} {a : ℝ} (ha : 0<a)
    (hw : ∀w∈ws,0<w) (P : ℕ) :
    ((tuples ws P).length:ℝ)≤ Real.exp (a*P)*normalizer ws a := by
  induction ws generalizing P with
  | nil => simp [tuples,normalizer];positivity
  | cons w ws ih =>
    have hwp := hw w (by simp)
    have hws : ∀v∈ws,0<v := fun v hv => hw v (by simp [hv])
    have hn := (normalizer_pos ha hws).le
    have hx0 : 0≤ Real.exp (-a*w) := (Real.exp_pos _).le
    have hx1 : Real.exp (-a*w)<1 := by
      rw [Real.exp_lt_one_iff]
      have : (0:ℝ)<w := Nat.cast_pos.mpr hwp
      nlinarith
    have hterm (e : ℕ) (he : e∈Finset.range (P/w+1)) :
      ((tuples ws (P-w*e)).length:ℝ)≤
        Real.exp (a*P)*(Real.exp (-a*w))^e*normalizer ws a := by
      have hm : w*e≤P := by
        have hd : e≤P/w := by have := Finset.mem_range.mp he;omega
        simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hwp).mp hd
      have hexp : Real.exp (a*(P-w*e:ℕ))=Real.exp (a*P)*(Real.exp (-a*w))^e := by
        rw [Nat.cast_sub hm,Nat.cast_mul,← Real.exp_nat_mul,← Real.exp_add]
        congr 1
        ring
      simpa only [hexp] using ih hws (P-w*e)
    have hsum := Finset.sum_le_sum hterm
    have hgeom := finite_geometric_le hx0 hx1 (P/w+1)
    have hfinal := mul_le_mul_of_nonneg_left hgeom
      (mul_nonneg (Real.exp_pos (a*P)).le hn)
    have hlen : ((tuples (w::ws) P).length:ℝ)=
      ∑e∈Finset.range (P/w+1),((tuples ws (P-w*e)).length:ℝ) := by
      simp only [tuples,List.length_flatMap,List.length_map,Nat.cast_list_sum,List.map_map]
      change ((List.range (P/w+1)).map fun e => ((tuples ws (P-w*e)).length:ℝ)).sum = _
      rw [← List.sum_toFinset _ List.nodup_range,List.toFinset_range]
    rw [hlen]
    calc
      _ ≤ ∑e∈Finset.range (P/w+1),Real.exp (a*P)*(Real.exp (-a*w))^e*normalizer ws a := hsum
      _ = (Real.exp (a*P)*normalizer ws a)*(∑e∈Finset.range (P/w+1),(Real.exp (-a*w))^e) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        ring
      _ ≤ (Real.exp (a*P)*normalizer ws a)*(1-Real.exp (-a*w))⁻¹ := hfinal
      _ = Real.exp (a*P)*normalizer (w::ws) a := by simp [normalizer];ring

/-- Exact regrouping by the actual acquired finite weight list. -/
theorem sum_by_count (ws : List ℕ) (s : Finset ℕ) (f : ℕ→ℝ)
    (hs : ∀w∈ws,w∈s) :
    (ws.map f).sum=∑w∈s,(ws.count w:ℝ)*f w := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    have hw := hs w (by simp)
    have ht : ∀v∈ws,v∈s := fun v hv => hs v (by simp [hv])
    simp only [List.map_cons,List.sum_cons,ih ht,List.count_cons]
    simp [Nat.cast_add,add_mul,Finset.sum_add_distrib,ite_mul,hw,add_comm]

/-- Each positive mode contributes the finite Euler logarithm. -/
noncomputable def logFactor (a : ℝ) (w : ℕ) : ℝ := -Real.log (1-Real.exp (-a*w))

/-- The zero weight has zero formal log factor; it is excluded from runtime input. -/
theorem logFactor_nonneg {a : ℝ} (ha : 0<a) (w : ℕ) : 0≤logFactor a w := by
  cases w with
  | zero => simp [logFactor]
  | succ w =>
    have he : Real.exp (-a*(w+1:ℕ))<1 := by
      rw [Real.exp_lt_one_iff]
      have : (0:ℝ)<(w+1:ℕ) := by positivity
      nlinarith
    have hp := Real.exp_pos (-a*(w+1:ℕ))
    have hh : Real.log (1-Real.exp (-a*(w+1:ℕ)))≤0 :=
      Real.log_nonpos (by linarith) (by linarith)
    exact neg_nonneg.mpr hh

/-- No analytic infinite product is needed for the acquired finite normalizer. -/
theorem normalizer_exp {ws : List ℕ} {a : ℝ} (ha : 0<a) (hw : ∀w∈ws,0<w) :
    normalizer ws a=Real.exp ((ws.map (logFactor a)).sum) := by
  induction ws with
  | nil => simp [normalizer]
  | cons w ws ih =>
    have hp : 0<w := hw w (by simp)
    have ht : ∀v∈ws,0<v := fun v hv => hw v (by simp [hv])
    have he : Real.exp (-a*w)<1 := by
      rw [Real.exp_lt_one_iff]
      have : (0:ℝ)<w := Nat.cast_pos.mpr hp
      nlinarith
    simp only [normalizer,List.map_cons,List.prod_cons,List.sum_cons,Real.exp_add] at *
    rw [ih ht]
    simp only [logFactor,Real.exp_neg,Real.exp_log (sub_pos.mpr he)]

/-- Finite multiplicity grouping exposes exactly the per-weight source bound. -/
theorem logsum_multiplicity {ws : List ℕ} {a : ℝ} (ha : 0<a) (K B : ℕ)
    (hw : ∀w∈ws,w≤K) (hb : ∀w,(ws.count w)≤B) :
    (ws.map (logFactor a)).sum≤(B:ℝ)*∑j∈Finset.range K,logFactor a (j+1) := by
  rw [sum_by_count ws (Finset.range (K+1)) (logFactor a)
    (fun w h => Finset.mem_range.mpr (by have := hw w h;omega))]
  calc
    _ ≤ ∑w∈Finset.range (K+1),(B:ℝ)*logFactor a w := by
      apply Finset.sum_le_sum
      intro w hw'
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hb w) (logFactor_nonneg ha w)
    _ = (B:ℝ)*∑w∈Finset.range (K+1),logFactor a w := by rw [Finset.mul_sum]
    _ = (B:ℝ)*∑j∈Finset.range K,logFactor a (j+1) := by
      rw [Finset.sum_range_succ']
      simp [logFactor]

/-- Exact useful nonoptimal balancing, avoiding a ceiling on mode multiplicity. -/
theorem balance_exponent {B P : ℝ} (hB : 0<B) (hP : 0<P) :
    (Real.sqrt B/Real.sqrt P)*P+2*B/(Real.sqrt B/Real.sqrt P)=3*Real.sqrt (B*P) := by
  let b := Real.sqrt B
  let p := Real.sqrt P
  have hb : b≠0 := ne_of_gt (Real.sqrt_pos.mpr hB)
  have hp : p≠0 := ne_of_gt (Real.sqrt_pos.mpr hP)
  have hb2 : b*b=B := by simpa [b,pow_two] using Real.sq_sqrt hB.le
  have hp2 : p*p=P := by simpa [p,pow_two] using Real.sq_sqrt hP.le
  have ht1 : b/p*P=b*p := by rw [←hp2];field_simp
  have ht2 : 2*B/(b/p)=2*b*p := by rw [←hb2];field_simp
  rw [Real.sqrt_mul hB.le]
  change b/p*P+2*B/(b/p)=3*(b*p)
  rw [ht1,ht2]
  ring

end RiemannGaussian.SemiprimeD1WeightedPotential
