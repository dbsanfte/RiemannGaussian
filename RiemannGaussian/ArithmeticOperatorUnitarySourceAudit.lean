/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorUnitaryInverseAudit
import RiemannGaussian.ZetaSquarefreeEulerResponse
import Mathlib.NumberTheory.ArithmeticFunction.LFunction

/-!
# Genuine source preflight for the full coprime logarithmic inverse

The ordinary-Mobius coprime inverse is compared with a literal ordinary
convolution. No restricted signed estimate is inferred from that comparison.
-/

namespace RiemannGaussian.ArithmeticOperatorUnitarySourceAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorUnitaryInverseAudit
open scoped BigOperators Topology LSeries.notation

/-- Exact six-period local Mangoldt multiplier suggested by the probe. -/
def orderWeight (k : ℕ) : ℝ :=
  if k%6=1 ∨ k%6=4 then 1 else if k%6=2 ∨ k%6=3 then 2 else 0

private theorem orderWeight_zero : orderWeight 0=0 := by norm_num [orderWeight]

private theorem orderWeight_step (k : ℕ) :
    orderWeight (k+2)-orderWeight (k+1)+orderWeight k=1 := by
  have hk : k%6<6 := Nat.mod_lt _ (by norm_num)
  interval_cases h : k%6 <;> norm_num [orderWeight,Nat.add_mod,h]

private theorem weight_prefix (k : ℕ) :
    (∑ i∈Finset.range (k+1),orderWeight i)-orderWeight (k-1)=(k : ℝ) := by
  induction k with
  | zero => simp [orderWeight_zero]
  | succ k ih =>
    cases k with
    | zero => norm_num [orderWeight,Finset.sum_range_succ]
    | succ k =>
      have hs := orderWeight_step k
      rw [show (k+1)-1=k by omega] at ih
      rw [Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at *
      linarith

/-- The prime-power row includes EVERY positive exponent. -/
def primePowerRow (n : ℕ) : ℝ :=
  orderWeight (n.factorization n.minFac)*ArithmeticFunction.vonMangoldt n

private theorem primePowerRow_zero : primePowerRow 0=0 := by simp [primePowerRow]

private theorem primePowerRow_one : primePowerRow 1=0 := by simp [primePowerRow]

theorem primePowerRow_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0<k) :
    primePowerRow (p^k)=orderWeight k*Real.log p := by
  rw [primePowerRow,hp.pow_minFac hk.ne',Nat.factorization_pow_self hp,
    ArithmeticFunction.vonMangoldt_apply_pow hk.ne',ArithmeticFunction.vonMangoldt_apply_prime hp]

private theorem primePowerRow_not_prime_pow {n : ℕ} (hn : ¬IsPrimePow n) :
    primePowerRow n=0 := by
  rw [primePowerRow,ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn,mul_zero]

private theorem primePowerRow_coprime_mul {a b : ℕ} (hc : a.Coprime b)
    (ha : a≠1) (hb : b≠1) : primePowerRow (a*b)=0 := by
  apply primePowerRow_not_prime_pow
  intro hpow
  have ha0 : 0<a := Nat.pos_of_ne_zero (fun h => hpow.ne_zero (by simp [h]))
  have hb0 : 0<b := Nat.pos_of_ne_zero (fun h => hpow.ne_zero (by simp [h]))
  have ha1 : 1<a := by omega
  have hb1 : 1<b := by omega
  rcases (hc.isPrimePow_dvd_mul hpow).mp (dvd_refl (a*b)) with hd | hd
  · have hle := Nat.le_of_dvd ha0 hd
    nlinarith
  · have hle := Nat.le_of_dvd hb0 hd
    nlinarith

private theorem constantInverse_zero : constantInverse 0=0 := by
  simp [constantInverse,inverseJet,ArithmeticOperatorUnitaryInverseAudit.unitary]

private theorem constantInverse_one : constantInverse 1=1 := by
  simp [constantInverse,inverseJet,ArithmeticOperatorUnitaryInverseAudit.unitary,muJet,gammaJet]

private theorem constantInverse_mul {a b : ℕ} (hc : a.Coprime b) :
    constantInverse (a*b)=constantInverse a*constantInverse b := by
  exact congrArg TrivSqZeroExt.fst (inverseJet_mul hc)

private theorem constantInverse_power {p k : ℕ} (hp : p.Prime) :
    constantInverse (p^k)=if k=1 then 0 else 1 := by
  by_cases hk : k=0
  · simp [hk,constantInverse_one]
  exact constantInverse_prime_pow hp (Nat.pos_of_ne_zero hk)

private def baseJet : ArithmeticFunction (TrivSqZeroExt ℝ ℝ) :=
  ⟨fun n => TrivSqZeroExt.inl (constantInverse n),by simp [constantInverse_zero]⟩

private theorem baseJet_multiplicative : baseJet.IsMultiplicative := by
  refine ⟨by simp [baseJet,constantInverse_one],?_⟩
  intro a b hc
  simp only [baseJet,ArithmeticFunction.coe_mk,constantInverse_mul hc,
    TrivSqZeroExt.inl_mul]

private def rowJet : ArithmeticFunction (TrivSqZeroExt ℝ ℝ) :=
  ⟨fun n => TrivSqZeroExt.inr (primePowerRow n),by simp [primePowerRow_zero]⟩

private def primitiveJet : ArithmeticFunction (TrivSqZeroExt ℝ ℝ) := 1+rowJet

private theorem primitiveJet_multiplicative : primitiveJet.IsMultiplicative := by
  have hone : primitiveJet 1=1 := by
    change (if (1 : ℕ)=1 then (1 : TrivSqZeroExt ℝ ℝ) else 0)+
      TrivSqZeroExt.inr (primePowerRow 1)=1
    rw [ite_eq_left rfl,primePowerRow_one,TrivSqZeroExt.inr_zero,add_zero]
  refine ⟨hone,?_⟩
  intro a b hc
  by_cases ha : a=1
  · subst a; rw [one_mul,hone,one_mul]
  by_cases hb : b=1
  · subst b; rw [mul_one,hone,mul_one]
  have hab : a*b≠1 := fun h => ha (mul_eq_one.mp h).1
  change ((if a*b=1 then (1 : TrivSqZeroExt ℝ ℝ) else 0)+
    TrivSqZeroExt.inr (primePowerRow (a*b)))=
    ((if a=1 then (1 : TrivSqZeroExt ℝ ℝ) else 0)+TrivSqZeroExt.inr (primePowerRow a))*
    ((if b=1 then (1 : TrivSqZeroExt ℝ ℝ) else 0)+TrivSqZeroExt.inr (primePowerRow b))
  rw [ite_eq_right ha,ite_eq_right hb,ite_eq_right hab,zero_add,zero_add,zero_add,
    primePowerRow_coprime_mul hc ha hb,TrivSqZeroExt.inr_zero,TrivSqZeroExt.inr_mul_inr]

/-- Full ordinary convolution in the original cofactor coordinates. -/
def ordinaryJoined (n : ℕ) : ℝ :=
  ∑ da∈n.divisorsAntidiagonal,constantInverse da.1*primePowerRow da.2

private theorem productJet_fst (n : ℕ) :
    ((baseJet*primitiveJet) n).fst=constantInverse n := by
  rw [primitiveJet,Distrib.left_distrib baseJet 1 rowJet,mul_one baseJet,ArithmeticFunction.add_apply,
    TrivSqZeroExt.fst_add,ArithmeticFunction.mul_apply,TrivSqZeroExt.fst_sum]
  simp [baseJet,rowJet,TrivSqZeroExt.fst_mul]

private theorem productJet_snd (n : ℕ) :
    ((baseJet*primitiveJet) n).snd=ordinaryJoined n := by
  rw [primitiveJet,Distrib.left_distrib baseJet 1 rowJet,mul_one baseJet,ArithmeticFunction.add_apply,
    TrivSqZeroExt.snd_add,ArithmeticFunction.mul_apply,TrivSqZeroExt.snd_sum]
  simp only [baseJet,rowJet,ArithmeticFunction.coe_mk,TrivSqZeroExt.snd_inl,
    zero_add,ordinaryJoined]
  apply Finset.sum_congr rfl
  intro da _
  simp [TrivSqZeroExt.snd_mul]


private theorem primePowerRow_power {p k : ℕ} (hp : p.Prime) :
    primePowerRow (p^k)=orderWeight k*Real.log p := by
  by_cases hk : k=0
  · simp [hk,primePowerRow_one,orderWeight_zero]
  exact primePowerRow_prime_pow hp (Nat.pos_of_ne_zero hk)

private theorem sum_prime_pow {R : Type*} [AddCommMonoid R] {p : ℕ}
    (hp : p.Prime) (k : ℕ) (F : ℕ → ℕ → R) :
    (∑ da∈(p^k).divisorsAntidiagonal,F da.1 da.2)=
      ∑ i∈Finset.range (k+1),F (p^i) (p^(k-i)) := by
  symm
  apply Finset.sum_nbij (fun i => (p^i,p^(k-i)))
  · intro i hi
    have hik : i≤k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    exact Nat.mem_divisorsAntidiagonal.mpr
      ⟨by rw [← pow_add,Nat.add_sub_of_le hik],pow_ne_zero _ hp.ne_zero⟩
  · intro i _ j _ he
    exact (Nat.pow_right_inj hp.one_lt).mp (congrArg Prod.fst he)
  · intro da hda
    obtain ⟨i,hi,he⟩ := (Nat.mem_divisors_prime_pow hp k).mp
      (Nat.fst_mem_divisors_of_mem_antidiagonal hda)
    obtain ⟨j,_,hf⟩ := (Nat.mem_divisors_prime_pow hp k).mp
      (Nat.snd_mem_divisors_of_mem_antidiagonal hda)
    have hs : i+j=k := (Nat.pow_right_inj hp.one_lt).mp (by
      rw [pow_add,← he,← hf]; exact (Nat.mem_divisorsAntidiagonal.mp hda).1)
    refine ⟨i,Finset.mem_range.mpr (by omega),?_⟩
    apply Prod.ext
    · exact he.symm
    · change p^(k-i)=da.2
      rw [show k-i=j by omega]; exact hf.symm
  · intro i _
    rfl

private theorem weight_slots (k : ℕ) :
    (∑ i∈Finset.range (k+1),(if k-i=1 then (0 : ℝ) else 1)*orderWeight i)=(k : ℝ) := by
  by_cases hk : k=0
  · simp [hk,orderWeight_zero]
  have he (i : ℕ) (hi : i∈Finset.range (k+1)) :
      (if k-i=1 then (0 : ℝ) else 1)*orderWeight i=
        orderWeight i-(if i=k-1 then orderWeight i else 0) := by
    have hle : i≤k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hs : k-i=1 ↔ i=k-1 := by omega
    by_cases h : i=k-1
    · rw [ite_eq_left (hs.mpr h),ite_eq_left h]; ring
    · rw [ite_eq_right (fun h' => h (hs.mp h')),ite_eq_right h]; ring
  rw [Finset.sum_congr rfl he,Finset.sum_sub_distrib,Finset.sum_ite_eq',
    ite_eq_left (Finset.mem_range.mpr (by omega : k-1<k+1))]
  exact weight_prefix k

private theorem ordinaryJoined_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ordinaryJoined (p^k)=(k : ℝ)*Real.log p := by
  unfold ordinaryJoined
  conv_lhs => rw [← Nat.map_swap_divisorsAntidiagonal,Finset.sum_map]
  change (∑ da∈(p^k).divisorsAntidiagonal,constantInverse da.2*primePowerRow da.1)=_
  rw [sum_prime_pow hp k (fun a b => constantInverse b*primePowerRow a)]
  simp_rw [constantInverse_power hp,primePowerRow_power hp,← mul_assoc]
  rw [← Finset.sum_mul,weight_slots]

private def actualJet : ArithmeticFunction (TrivSqZeroExt ℝ ℝ) :=
  ⟨inverseJet,by simp [inverseJet,ArithmeticOperatorUnitaryInverseAudit.unitary]⟩

private theorem actualJet_multiplicative : actualJet.IsMultiplicative := by
  refine ⟨by simp [actualJet,inverseJet,ArithmeticOperatorUnitaryInverseAudit.unitary,muJet,gammaJet],?_⟩
  intro a b hc
  exact inverseJet_mul hc

/-- The complete coprime inverse is EXACTLY a full ordinary convolution.
This is proved on all integer labels, not by truncating an Euler product. -/
theorem logInverse_eq_ordinaryJoined (n : ℕ) : logInverse n=ordinaryJoined n := by
  have he : actualJet=baseJet*primitiveJet := by
    apply (actualJet_multiplicative.eq_iff_eq_on_prime_powers actualJet
      (baseJet*primitiveJet) (baseJet_multiplicative.mul primitiveJet_multiplicative)).mpr
    intro p k hp
    apply TrivSqZeroExt.ext
    · change constantInverse (p^k)=((baseJet*primitiveJet) (p^k)).fst
      exact (productJet_fst _).symm
    · change logInverse (p^k)=((baseJet*primitiveJet) (p^k)).snd
      rw [productJet_snd,ordinaryJoined_prime_pow hp]
      by_cases hk : k=0
      · simp [hk,logInverse,inverseJet,ArithmeticOperatorUnitaryInverseAudit.unitary,muJet,gammaJet]
      exact logInverse_prime_pow hp (Nat.pos_of_ne_zero hk)
  have h := congrArg (fun f : ArithmeticFunction (TrivSqZeroExt ℝ ℝ) => (f n).snd) he
  exact h.trans (productJet_snd n)

/-- Correction after the actual Mangoldt row is isolated. -/
def properCorrection (n : ℕ) : ℝ :=
  primePowerRow n-ArithmeticFunction.vonMangoldt n

private theorem orderWeight_bounds (k : ℕ) : 0≤orderWeight k ∧ orderWeight k≤2 := by
  unfold orderWeight
  split_ifs <;> norm_num

/-- Every ordinary prime is unchanged by the full six-period row. -/
theorem properCorrection_prime {p : ℕ} (hp : p.Prime) : properCorrection p=0 := by
  have he := primePowerRow_prime_pow hp (by norm_num : 0<1)
  simp only [pow_one] at he
  rw [properCorrection,he,ArithmeticFunction.vonMangoldt_apply_prime hp]
  norm_num [orderWeight]

/-- The correction is supported on proper powers and its entire
absolute coefficient is dominated by the ALREADY PAID proper-power row. -/
theorem abs_properCorrection_le (n : ℕ) :
    |properCorrection n|≤zetaProperPrimePowerCoefficient n := by
  by_cases hp : n.Prime
  · rw [properCorrection_prime hp,zetaProperPrimePowerCoefficient,ite_eq_left hp,abs_zero]
  rw [zetaProperPrimePowerCoefficient,ite_eq_right hp,properCorrection,primePowerRow,
    ← sub_one_mul,abs_mul,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hw := orderWeight_bounds (n.factorization n.minFac)
  have habs : |orderWeight (n.factorization n.minFac)-1|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
  simpa only [one_mul] using mul_le_mul_of_nonneg_right habs ArithmeticFunction.vonMangoldt_nonneg

/-- Whole-label phase and every arbitrary physical test/mask survive
the convolution join. No norm is used to separate its two factors. -/
theorem native_convolution_eq (X : ℕ) (y : ℝ) (test : ℕ → ℂ) :
    (∑ n∈Finset.Icc 1 X,test n*phasedLogInverse y n)=
      ∑ n∈Finset.Icc 1 X,test n*SuzukiCarryCorrelation.primePhase y n*
        ∑ da∈n.divisorsAntidiagonal,
          (constantInverse da.1 : ℂ)*
            ((ArithmeticFunction.vonMangoldt da.2 : ℂ)+(properCorrection da.2 : ℂ)) := by
  apply Finset.sum_congr rfl
  intro n _
  rw [phasedLogInverse,logInverse_eq_ordinaryJoined,ordinaryJoined,Complex.ofReal_sum]
  have he (da : ℕ × ℕ) : ((constantInverse da.1*primePowerRow da.2 : ℝ) : ℂ)=
      (constantInverse da.1 : ℂ)*
        ((ArithmeticFunction.vonMangoldt da.2 : ℂ)+(properCorrection da.2 : ℂ)) := by
    rw [properCorrection]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun da _ => he da)]
  ring


/-- The regular correction is a genuinely convergent arithmetic
Dirichlet series right of one half, with every proper power retained. -/
def regularCorrection (s : ℂ) : ℂ :=
  LSeries (fun n => (properCorrection n : ℂ)) s

theorem correction_summable {s : ℂ} (hs : 1/2<s.re) :
    LSeriesSummable (fun n => (properCorrection n : ℂ)) s := by
  change Summable (LSeries.term (fun n => (properCorrection n : ℂ)) s)
  apply summable_norm_iff.mp
  apply (LSeriesSummable_zetaProperPrimePower hs).norm.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  by_cases hn : n=0
  · simp [hn,LSeries.term]
  rw [LSeries.term_of_ne_zero hn,LSeries.term_of_ne_zero hn,norm_div,norm_div,
    Complex.norm_real,Real.norm_eq_abs,Complex.norm_real,
    Real.norm_of_nonneg (zetaProperPrimePowerCoefficient_nonneg n)]
  exact div_le_div_of_nonneg_right (abs_properCorrection_le n) (norm_nonneg _)

private theorem correction_abscissa :
    LSeries.abscissaOfAbsConv (fun n => (properCorrection n : ℂ))≤(1/2 : ℝ) := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1/2)
  intro y hy
  exact correction_summable (by simpa using hy)

theorem regularCorrection_analytic {s : ℂ} (hs : 1/2<s.re) :
    AnalyticAt ℂ regularCorrection s :=
  LSeries_analyticOnNhd _ s (lt_of_le_of_lt correction_abscissa (by exact_mod_cast hs))

private theorem constantInverse_le_one (n : ℕ) : constantInverse n≤1 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp [constantInverse_zero]
  | one => rw [constantInverse_one]
  | prime_pow p k hp hk => rw [constantInverse_prime_pow hp hk]; split_ifs <;> norm_num
  | coprime a b _ _ hc ha hb =>
    rw [constantInverse_mul hc]
    calc
      _ ≤ 1*constantInverse b := mul_le_mul_of_nonneg_right ha (inverse_coordinates_nonneg b).1
      _ ≤ 1 := by simpa only [one_mul] using hb

/-- Genuine powerful-label Euler factor. -/
def powerfulResponse (s : ℂ) : ℂ :=
  riemannZeta (2*s)*riemannZeta (3*s)/riemannZeta (6*s)

theorem powerfulResponse_analytic {s : ℂ} (hs : 1/2<s.re) :
    AnalyticAt ℂ powerfulResponse s := by
  have h2 : 1<(2*s).re := by norm_num; linarith
  have h3 : 1<(3*s).re := by norm_num; linarith
  have h6 : 1<(6*s).re := by norm_num; linarith
  have hA (j : ℂ) (hj : 1<(j*s).re) :
      AnalyticAt ℂ (fun z : ℂ => riemannZeta (j*z)) s := by
    have hne : j*s≠1 := fun he => by rw [he] at hj; norm_num at hj
    exact (analyticOn_riemannZeta _ (by simpa using hne)).comp
      (analyticAt_const.mul analyticAt_id)
  exact ((hA 2 h2).mul (hA 3 h3)).div (hA 6 h6) (riemannZeta_ne_zero_of_one_lt_re h6)

theorem powerfulResponse_ne_zero {s : ℂ} (hs : 1/2<s.re) :
    powerfulResponse s≠0 := by
  apply div_ne_zero
  · exact mul_ne_zero (riemannZeta_ne_zero_of_one_lt_re (by norm_num; linarith))
      (riemannZeta_ne_zero_of_one_lt_re (by norm_num; linarith))
  · exact riemannZeta_ne_zero_of_one_lt_re (by norm_num; linarith)

private theorem base_summable {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (fun n => (constantInverse n : ℂ)) s := by
  apply LSeriesSummable_of_le_const_mul_rpow hs
  refine ⟨1,fun n _ => ?_⟩
  simpa only [sub_self,Real.rpow_zero,mul_one,Complex.norm_real,
    Real.norm_of_nonneg (inverse_coordinates_nonneg n).1] using constantInverse_le_one n

private theorem base_euler_hasProd {s : ℂ} (hs : 1<s.re) :
    HasProd (fun p : Nat.Primes => (1-(p : ℂ)^(-s))⁻¹-(p : ℂ)^(-s))
      (LSeries (fun n => (constantInverse n : ℂ)) s) := by
  let g := riemannZetaSummandHom (ne_zero_of_one_lt_re hs)
  let f : ℕ → ℂ := fun n => (constantInverse n : ℂ)*g n
  have hsum : Summable (fun n => ‖f n‖) := by
    apply (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro n
    dsimp only [f,g]
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (inverse_coordinates_nonneg n).1]
    exact (mul_le_mul_of_nonneg_right (constantInverse_le_one n) (norm_nonneg _)).trans_eq (one_mul _)
  have h1 : f 1=1 := by simp [f,constantInverse_one]
  have h0 : f 0=0 := by simp [f,constantInverse_zero]
  have hmul {m n : ℕ} (hc : m.Coprime n) : f (m*n)=f m*f n := by
    simp only [f,constantInverse_mul hc,Complex.ofReal_mul,map_mul]
    ring
  have h := EulerProduct.eulerProduct_hasProd h1 (fun {_ _} hc => hmul hc) hsum h0
  have hlocal (p : Nat.Primes) :
      (∑' k : ℕ,f (p.val^k))=(1-(p : ℂ)^(-s))⁻¹-(p : ℂ)^(-s) := by
    let t : ℂ := (p : ℂ)^(-s)
    have hp := (summable_riemannZetaSummand hs).of_norm.norm_lt_one
      (f := g.toMonoidHom) p.property.one_lt
    change ‖t‖<1 at hp
    have he (k : ℕ) : f (p.val^k)=t^k-(if k=1 then t else 0) := by
      dsimp only [f,t]
      rw [constantInverse_power p.property,map_pow]
      by_cases hk : k=1
      · simp [hk,g,riemannZetaSummandHom]
      · simp [hk,g,riemannZetaSummandHom]
    have ht := (hasSum_geometric_of_norm_lt_one hp).sub (hasSum_ite_eq 1 t)
    have heq : HasSum (fun k => f (p.val^k)) ((1-t)⁻¹-t) := ht.congr_fun he
    exact heq.tsum_eq
  simp only [hlocal] at h
  convert h using 1
  rw [LSeries]
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · simp [hn,LSeries.term,f,constantInverse_zero]
  · simp [f,g,riemannZetaSummandHom,LSeries.term_of_ne_zero hn,Complex.cpow_neg,div_eq_mul_inv]

private theorem local_powerful_factor {s : ℂ} (hs : 1<s.re) (p : Nat.Primes) :
    ((1-(p : ℂ)^(-s))⁻¹-(p : ℂ)^(-s))*(1-(p : ℂ)^(-(6*s)))⁻¹=
      (1-(p : ℂ)^(-(2*s)))⁻¹*(1-(p : ℂ)^(-(3*s)))⁻¹ := by
  let t : ℂ := (p : ℂ)^(-s)
  have ht := (summable_riemannZetaSummand hs).of_norm.norm_lt_one
    (f := (riemannZetaSummandHom (ne_zero_of_one_lt_re hs)).toMonoidHom) p.property.one_lt
  change ‖t‖<1 at ht
  have hne (k : ℕ) (hk : 0<k) : 1-t^k≠0 := by
    intro he
    have he' : t^k=1 := sub_eq_zero.mp he |>.symm
    have hlt := pow_lt_one₀ (norm_nonneg t) ht hk.ne'
    rw [← norm_pow,he',norm_one] at hlt
    exact lt_irrefl _ hlt
  have hc (k : ℕ) : (p.val : ℂ)^(-((k : ℂ)*s))=t^k := by
    rw [show -((k : ℂ)*s)=(k : ℂ)*(-s) by ring,Complex.cpow_nat_mul]
  have hc6 := hc 6
  have hc2 := hc 2
  have hc3 := hc 3
  norm_num only [Nat.cast_ofNat] at hc6 hc2 hc3
  change ((1-(p.val : ℂ)^(-s))⁻¹-(p.val : ℂ)^(-s))*
    (1-(p.val : ℂ)^(-(6*s)))⁻¹=
      (1-(p.val : ℂ)^(-(2*s)))⁻¹*(1-(p.val : ℂ)^(-(3*s)))⁻¹
  rw [hc6,hc2,hc3]
  change ((1-t)⁻¹-t)*(1-t^6)⁻¹=(1-t^2)⁻¹*(1-t^3)⁻¹
  have ht1 : 1-t≠0 := by simpa using hne 1 (by norm_num)
  field_simp [ht1,hne 2 (by norm_num),hne 3 (by norm_num),hne 6 (by norm_num)]
  ring

/-- Genuine Euler identity for the ACTUAL constant inverse coordinate.
No series convergence to the left of Re(s)>1 is asserted here. -/
theorem base_euler {s : ℂ} (hs : 1<s.re) :
    LSeries (fun n => (constantInverse n : ℂ)) s=powerfulResponse s := by
  have h2 : 1<(2*s).re := by norm_num; linarith
  have h3 : 1<(3*s).re := by norm_num; linarith
  have h6 : 1<(6*s).re := by norm_num; linarith
  have hP := (base_euler_hasProd hs).mul (riemannZeta_eulerProduct_hasProd h6)
  simp only [local_powerful_factor hs] at hP
  have he := hP.unique ((riemannZeta_eulerProduct_hasProd h2).mul (riemannZeta_eulerProduct_hasProd h3))
  exact (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re h6)).mpr he

/-- Actual meromorphic source of the full nonsquarefree inverse.
Its regular term is the convergent proper-power correction. -/
def response (s : ℂ) : ℂ :=
  powerfulResponse s*(-logDeriv riemannZeta s+regularCorrection s)

/-- Complete arithmetic Dirichlet-series identity with all prime powers,
before any continuation into the candidate zero strip. -/
theorem euler_response {s : ℂ} (hs : 1<s.re) :
    LSeries (fun n => (logInverse n : ℂ)) s=response s := by
  let b : ℕ → ℂ := fun n => (constantInverse n : ℂ)
  let w : ℕ → ℂ := fun n => (primePowerRow n : ℂ)
  have hw : w=(fun n => (ArithmeticFunction.vonMangoldt n : ℂ))+
      (fun n => (properCorrection n : ℂ)) := by
    funext n
    dsimp [w,properCorrection]
    push_cast
    ring
  have hMangoldt : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (lt_of_le_of_lt
      abscissaOfAbsConv_vonMangoldt_le_one (by exact_mod_cast hs))
  have hws : LSeriesSummable w s := by
    rw [hw]
    exact hMangoldt.add (correction_summable (by linarith))
  have he : (fun n => (logInverse n : ℂ))=b ⍟ w := by
    funext n
    rw [logInverse_eq_ordinaryJoined,ordinaryJoined,LSeries.convolution_def]
    push_cast
    rfl
  rw [he,LSeries_convolution' (base_summable hs) hws,hw,LSeries_add hMangoldt
    (correction_summable (by linarith)),base_euler hs]
  have hvalue : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s=-logDeriv riemannZeta s := by
    simpa only [logDeriv_apply,neg_div] using
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  rw [hvalue,response,regularCorrection]


/-- Twisting is at the original WHOLE integer label, including every
cofactor and proper power; the Euler identity keeps the full height. -/
theorem phased_euler_response (y : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeries (phasedLogInverse y) s=response (s+I*y) := by
  change LSeries (fun n => (logInverse n : ℂ)*SuzukiCarryCorrelation.primePhase y n) s=_
  rw [ArithmeticOperatorGammaTwistAudit.LSeries_primePhase,euler_response (by simpa using hs)]

/-- A genuine right-half zero has the original nonzero negative
multiplicity residue, multiplied by an analytic NONZERO powerful factor.
No exposure, simple-zero premise or finite-cutoff asymptotic is used. -/
theorem actual_zero_source (rho : NontrivialZetaZero) (hrho : 1/2<rho.1.re) :
    Tendsto (fun s : ℂ => (s-rho.1)*response s) (𝓝[≠] rho.1)
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)*powerfulResponse rho.1)) := by
  have hLog := (AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt
    (analyticAt_riemannZeta_nontrivialZero rho)
    (analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho)).neg
  have hSub : Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa only [sub_self] using (show Tendsto (fun s : ℂ => s-rho.1)
      (𝓝[≠] rho.1) (𝓝 (rho.1-rho.1)) from
        (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hG : Tendsto powerfulResponse (𝓝[≠] rho.1) (𝓝 (powerfulResponse rho.1)) :=
    (powerfulResponse_analytic hrho).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hE : Tendsto regularCorrection (𝓝[≠] rho.1) (𝓝 (regularCorrection rho.1)) :=
    (regularCorrection_analytic hrho).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht := hG.mul (hLog.add (hSub.mul hE))
  convert ht using 1
  · funext s
    rw [response]
    ring
  · simp only [zero_mul,add_zero,analyticZetaZeroMultiplicity,mul_comm]

theorem actual_zero_source_ne_zero (rho : NontrivialZetaZero) (hrho : 1/2<rho.1.re) :
    -(analyticZetaZeroMultiplicity rho : ℂ)*powerfulResponse rho.1≠0 :=
  mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (analyticZetaZeroMultiplicity_positive rho).ne'))
    (powerfulResponse_ne_zero hrho)

/-- Pole centering retains every actual right-half zero source. -/
def centeredResponse (s : ℂ) : ℂ := (s-1)*response s

/-- Removal of density as an actual analytic GERM; it is not a claim
that the original coefficient series converges at the pole. -/
theorem centered_density_analytic :
    ∃ E : ℂ → ℂ,AnalyticAt ℂ E 1 ∧ centeredResponse=ᶠ[𝓝[≠] (1 : ℂ)] E := by
  have hA := differentiable_riemannZeta₁.analyticAt (1 : ℂ)
  have hne : riemannZeta₁ (1 : ℂ)≠0 := by simp [riemannZeta₁_one]
  have hLD : AnalyticAt ℂ (logDeriv riemannZeta₁) 1 := hA.deriv.div hA hne
  have hR := regularCorrection_analytic (s := (1 : ℂ)) (by norm_num)
  have hG := powerfulResponse_analytic (s := (1 : ℂ)) (by norm_num)
  refine ⟨fun s => powerfulResponse s*(1+(s-1)*(regularCorrection s-logDeriv riemannZeta₁ s)),
    hG.mul (analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul (hR.sub hLD))),?_⟩
  filter_upwards [hA.continuousAt.eventually_ne hne |>.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hns (hs : s≠1)
  have hz : riemannZeta s≠0 := by
    intro he
    apply hns
    rw [riemannZeta₁_eq_sub_one_mul hs,he,mul_zero]
  rw [centeredResponse,response,neg_logDeriv_riemannZeta_eq_pole_sub hs hz]
  field_simp [sub_ne_zero.mpr hs]
  ring

theorem centered_actual_zero_source (rho : NontrivialZetaZero) (hrho : 1/2<rho.1.re) :
    Tendsto (fun s : ℂ => (s-rho.1)*centeredResponse s) (𝓝[≠] rho.1)
      (𝓝 ((rho.1-1)*(-(analyticZetaZeroMultiplicity rho : ℂ)*powerfulResponse rho.1))) := by
  have hSub : Tendsto (fun s : ℂ => s-1) (𝓝[≠] rho.1) (𝓝 (rho.1-1)) :=
    (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  convert hSub.mul (actual_zero_source rho hrho) using 1
  funext s
  rw [centeredResponse]
  ring

theorem centered_actual_zero_source_ne_zero (rho : NontrivialZetaZero) (hrho : 1/2<rho.1.re) :
    (rho.1-1)*(-(analyticZetaZeroMultiplicity rho : ℂ)*powerfulResponse rho.1)≠0 :=
  mul_ne_zero (sub_ne_zero.mpr rho.2.2.2) (actual_zero_source_ne_zero rho hrho)

/-- Exact strength audit. Holomorphy of the FULL inverse response is
the original right-half nonvanishing question, not a new arithmetic
consequence of its nonnegative coefficient classification. -/
theorem response_removable_iff_nonvanishing {s : ℂ} (hs : 1/2<s.re) (hs1 : s≠1) :
    (∃ E : ℂ → ℂ,AnalyticAt ℂ E s ∧ response=ᶠ[𝓝[≠] s] E) ↔ riemannZeta s≠0 := by
  constructor
  · intro ⟨E,hE,he⟩ hz
    let rho : NontrivialZetaZero := ⟨s,hz,by
      rintro ⟨n,hn⟩
      have h := congrArg Complex.re hn
      norm_num [Complex.mul_re] at h
      nlinarith [Nat.cast_nonneg (α := ℝ) n],hs1⟩
    have hSource := actual_zero_source rho hs
    have hSub : Tendsto (fun z : ℂ => z-s) (𝓝[≠] s) (𝓝 0) := by
      simpa only [sub_self] using (show Tendsto (fun z : ℂ => z-s)
        (𝓝[≠] s) (𝓝 (s-s)) from
          (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    have hZero : Tendsto (fun z : ℂ => (z-s)*response z) (𝓝[≠] s) (𝓝 0) := by
      have hELimit : Tendsto E (𝓝[≠] s) (𝓝 (E s)) :=
        hE.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have ht := hSub.mul hELimit
      simp only [zero_mul] at ht
      exact ht.congr' (Filter.EventuallyEq.rfl.mul he.symm)
    exact actual_zero_source_ne_zero rho hs (tendsto_nhds_unique hSource hZero)
  · intro hz
    have hA := analyticOn_riemannZeta s (by simpa using hs1)
    have hLD : AnalyticAt ℂ (logDeriv riemannZeta) s := hA.deriv.div hA hz
    exact ⟨response,(powerfulResponse_analytic hs).mul
      (hLD.neg.add (regularCorrection_analytic hs)),Filter.EventuallyEq.rfl⟩

/-- Arbitrary inputs after the full convolution has been joined.
They are NOT assumed to be actual Gamma rows or prime Euler systems. -/
def freePrefix (X : ℕ) (y : ℝ) (test w : ℕ → ℂ) : ℂ :=
  ∑ n∈Finset.Icc 1 X,test n*SuzukiCarryCorrelation.primePhase y n*
    ∑ da∈n.divisorsAntidiagonal,(constantInverse da.1 : ℂ)*w da.2

/-- Signed powerful-cofactor kernel, with the original physical divided
cutoff, whole-label phase and arbitrary outer mask still present. -/
def cofactorKernel (X : ℕ) (y : ℝ) (test : ℕ → ℂ) (d : ℕ) : ℂ :=
  ∑ a∈Finset.Icc 1 (X/d),(constantInverse a : ℂ)*test (d*a)*
    SuzukiCarryCorrelation.primePhase y (d*a)

/-- This entire convolution observation is one scalar input test.
No prime-specific estimate follows from reindexing it. -/
theorem freePrefix_eq_scalar (X : ℕ) (y : ℝ) (test w : ℕ → ℂ) :
    freePrefix X y test w=∑ d∈Finset.Icc 1 X,w d*cofactorKernel X y test d := by
  have he : freePrefix X y test w=
      ∑ n∈Finset.Icc 1 X,∑ da∈n.divisorsAntidiagonal,
        w da.1*(constantInverse da.2 : ℂ)*test (da.1*da.2)*
          SuzukiCarryCorrelation.primePhase y (da.1*da.2) := by
    unfold freePrefix
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.mul_sum]
    conv_lhs => rw [← Nat.map_swap_divisorsAntidiagonal,Finset.sum_map]
    apply Finset.sum_congr rfl
    intro da hda
    change test n*SuzukiCarryCorrelation.primePhase y n*
      ((constantInverse da.2 : ℂ)*w da.1)=_
    rw [(Nat.mem_divisorsAntidiagonal.mp hda).1]
    ring
  rw [he,sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix X
    (fun d a => w d*(constantInverse a : ℂ)*test (d*a)*
      SuzukiCarryCorrelation.primePhase y (d*a))]
  apply Finset.sum_congr rfl
  intro d _
  rw [cofactorKernel,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem bound_forall_free_inputs_iff (X : ℕ) (y : ℝ) (test : ℕ → ℂ) (B : ℝ) :
    (∀ w,‖freePrefix X y test w‖≤B) ↔
      0≤B ∧ ∀ d∈Finset.Icc 1 X,cofactorKernel X y test d=0 := by
  simp_rw [freePrefix_eq_scalar]
  exact ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff _ _ _

/-- Actual coefficients are a specialization, not an arbitrary-input
Gamma or generalized-prime premise. The proper correction remains explicit. -/
theorem actual_prefix_eq (X : ℕ) (y : ℝ) (test : ℕ → ℂ) :
    (∑ n∈Finset.Icc 1 X,test n*phasedLogInverse y n)=
      ∑ d∈Finset.Icc 1 X,
        ((ArithmeticFunction.vonMangoldt d : ℂ)+(properCorrection d : ℂ))*
          cofactorKernel X y test d := by
  rw [native_convolution_eq]
  change freePrefix X y test
    (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)+(properCorrection d : ℂ))=_
  exact freePrefix_eq_scalar _ _ _ _

end
end RiemannGaussian.ArithmeticOperatorUnitarySourceAudit
