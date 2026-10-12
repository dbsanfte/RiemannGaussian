/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorLucasUnitAudit
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Fixed-cofactor quadratic unit codes: literal row and source audit

The cofactor residue is retained before the finite row is joined. A
threefold row reduces exactly to a fixed mod-eight prime profile and an
explicit endpoint. No growing-cofactor estimate is inferred from this.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical Topology
namespace RiemannGaussian.ArithmeticOperatorCrossUnitAudit
open Complex Filter ArithmeticOperatorLucasUnitAudit

/-- Exact complete common row with a multiplicative residue code. -/
def commonTrace (p a : ℕ) (χ : MulChar (ZMod p) ℂ) : ℂ :=
  (∑ k∈Finset.range (p*a),χ (((p*a-1).choose k : ℕ) : ZMod p))/(p*a : ℕ)

/-- Reindexing keeps every native lower-digit endpoint. -/
theorem sum_range_blocks (p a : ℕ) (f : ℕ → ℂ) :
    (∑ k∈Finset.range (p*a),f k)=
      ∑ h∈Finset.range a,∑ b∈Finset.range p,f (p*h+b) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.mul_succ,Finset.sum_range_add,Finset.sum_range_succ,ih]

/-- Threefold rows retain the upper value chi(2); it is not replaced by parity. -/
theorem commonTrace_three_eq {p : ℕ} (hp : p.Prime) (χ : MulChar (ZMod p) ℂ) :
    commonTrace p 3 χ=(2+χ 2)/3*rowTrace p 1 χ := by
  have hrow (h b : ℕ) (hb : b<p) :
      χ (((p*3-1).choose (p*h+b) : ℕ) : ZMod p)=
        χ ((-1 : ZMod p)^b)*χ (((2 : ℕ).choose h : ℕ) : ZMod p) := by
    rw [commonRow_first_digit hp (by omega : 0<3),map_mul]
    simp only [Nat.add_comm (p*h) b,Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hb,Nat.add_mul_div_left _ _ hp.pos,Nat.div_eq_of_lt hb,zero_add]
  have hnum : (∑ k∈Finset.range (p*3),χ (((p*3-1).choose k : ℕ) : ZMod p))=
      (2+χ 2)*(∑ b∈Finset.range p,χ ((-1 : ZMod p)^b)) := by
    rw [sum_range_blocks]
    calc
      _ = ∑ h∈Finset.range 3,(∑ b∈Finset.range p,χ ((-1 : ZMod p)^b))*
          χ (((2 : ℕ).choose h : ℕ) : ZMod p) := by
        apply Finset.sum_congr rfl
        intro h _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b hb
        exact hrow h b (Finset.mem_range.mp hb)
      _ = _ := by
        simp only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,
          Nat.choose_zero_right,Nat.choose_one_right,Nat.choose_self,Nat.cast_one,
          Nat.cast_ofNat,map_one,mul_one,zero_add]
        ring
  have hbase : (∑ b∈Finset.range p,χ ((-1 : ZMod p)^b))=(p : ℂ)*rowTrace p 1 χ := by
    unfold rowTrace
    simp only [pow_one]
    have hs : (∑ b∈Finset.range p,χ (unitRow p 1 b))=
        ∑ b∈Finset.range p,χ ((-1 : ZMod p)^b) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [unitRow_eq_sign hp 1 (by simpa using Finset.mem_range.mp hb)]
    rw [hs]
    have hpz : (p : ℂ)≠0 := by exact_mod_cast hp.ne_zero
    field_simp
  unfold commonTrace
  rw [hnum,hbase]
  have hpz : (p : ℂ)≠0 := by exact_mod_cast hp.ne_zero
  push_cast
  field_simp

/-- Quadratic residue code with the ordinary integer prime modulus. -/
def quadCode (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

theorem quadCode_int (p : ℕ) [Fact p.Prime] (a : ℤ) :
    quadCode p (a : ZMod p)=(legendreSym p a : ℂ) := rfl

/-- Fixed residue profile, extended by zero at even integers. -/
def bulkEight (n : ℕ) : ℂ :=
  if n%8=1 then 1 else if n%8=5 then 1/3 else 0

/-- Exact lower-digit endpoint in the threefold quadratic row. -/
def threeEndpoint (p : ℕ) : ℂ :=
  (2+(ZMod.χ₈ p : ℂ))*(1-(ZMod.χ₄ p : ℂ))/(6*(p : ℂ))

/-- The main fixed-cofactor profile uses only the ordinary mod-eight residue. -/
theorem bulkEight_eq_characters {n : ℕ} (hn : n%2=1) :
    bulkEight n=(2+(ZMod.χ₈ n : ℂ))*(1+(ZMod.χ₄ n : ℂ))/6 := by
  rw [ZMod.χ₈_nat_eq_if_mod_eight,ZMod.χ₄_nat_eq_if_mod_four]
  have h8 := Nat.mod_lt n (by omega : 0<8)
  have h82 : n%8%2=1 := by omega
  have h4 : n%4=(n%8)%4 := by omega
  rw [h4]
  unfold bulkEight
  interval_cases h : n%8 <;> norm_num [h,hn] at *

/-- Exact fixed-cofactor collapse for every odd ordinary prime, with its endpoint retained. -/
theorem commonTrace_three_quad_eq (p : ℕ) [hp : Fact p.Prime] (hp2 : p≠2) :
    commonTrace p 3 (quadCode p)=bulkEight p+threeEndpoint p := by
  rw [commonTrace_three_eq hp.out,rowTrace_eq hp.out]
  have hodd := hp.out.eq_two_or_odd.resolve_left hp2
  rw [ite_eq_left (by simpa only [pow_one] using hodd)]
  simp only [pow_one]
  have hneg : quadCode p (-1)=(ZMod.χ₄ p : ℂ) := by
    rw [show (-1 : ZMod p)=((-1 : ℤ) : ZMod p) by norm_cast,
      quadCode_int,legendreSym.at_neg_one hp2]
  have htwo : quadCode p 2=(ZMod.χ₈ p : ℂ) := by
    rw [show (2 : ZMod p)=((2 : ℤ) : ZMod p) by norm_cast,
      quadCode_int,legendreSym.at_two hp2]
  rw [htwo,bulkEight_eq_characters hodd]
  unfold alphabetMean threeEndpoint
  rw [map_one,hneg]
  ring

/-- The literal quadratic code, totalized by zero outside ordinary integer primes. -/
def threeQuadTrace (p : ℕ) : ℂ :=
  if hp : p.Prime then (let : Fact p.Prime := ⟨hp⟩;commonTrace p 3 (quadCode p)) else 0

theorem threeQuadTrace_prime {p : ℕ} (hp : p.Prime) (hp2 : p≠2) :
    threeQuadTrace p=bulkEight p+threeEndpoint p := by
  unfold threeQuadTrace
  rw [dite_eq_left hp]
  have : Fact p.Prime := ⟨hp⟩
  exact commonTrace_three_quad_eq p hp2

/-- Joined identity with arbitrary complex prime phases and no independent code allowances. -/
theorem fixed_three_join (P : Finset ℕ) (hP : ∀ p∈P,p.Prime ∧ p≠2)
    (w : ℕ → ℂ) :
    (∑ p∈P,w p*threeQuadTrace p)=
      (∑ p∈P,w p*bulkEight p)+(∑ p∈P,w p*threeEndpoint p) := by
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [threeQuadTrace_prime (hP p hp).1 (hP p hp).2]
  ring

/-- Mod-four quadratic character lifted as an exact integer table on mod eight. -/
def intFourEight : MulChar (ZMod 8) ℤ where
  toFun a := ZMod.χ₄ (a.val : ZMod 4)
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

/-- Actual Dirichlet character of level eight coming from minus one. -/
def charFour : DirichletCharacter ℂ 8 := intFourEight.ringHomComp (Int.castRingHom ℂ)

/-- Actual Dirichlet character of level eight coming from two. -/
def charTwo : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)

/-- Actual Dirichlet character of level eight coming from minus two. -/
def charNegTwo : DirichletCharacter ℂ 8 := ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ)

theorem charFour_ne_one : charFour≠1 := by
  intro h
  have he := congrArg (fun χ : DirichletCharacter ℂ 8 => χ 3) h
  have hv : charFour 3=(-1 : ℂ) := by
    have hi : intFourEight 3=(-1 : ℤ) := by decide
    change (intFourEight 3 : ℂ)=-1
    rw [hi]
    norm_num
  have hu : IsUnit (3 : ZMod 8) := (ZMod.isUnit_iff_coprime 3 8).mpr (by decide)
  rw [hv,MulChar.one_apply hu] at he
  norm_num at he

theorem charTwo_ne_one : charTwo≠1 := by
  intro h
  have he := congrArg (fun χ : DirichletCharacter ℂ 8 => χ 3) h
  have hv : charTwo 3=(-1 : ℂ) := by
    have hi : ZMod.χ₈ 3=(-1 : ℤ) := by decide
    change (ZMod.χ₈ 3 : ℂ)=-1
    rw [hi]
    norm_num
  have hu : IsUnit (3 : ZMod 8) := (ZMod.isUnit_iff_coprime 3 8).mpr (by decide)
  rw [hv,MulChar.one_apply hu] at he
  norm_num at he

theorem charNegTwo_ne_one : charNegTwo≠1 := by
  intro h
  have he := congrArg (fun χ : DirichletCharacter ℂ 8 => χ 5) h
  have hv : charNegTwo 5=(-1 : ℂ) := by
    have hi : ZMod.χ₈' 5=(-1 : ℤ) := by decide
    change (ZMod.χ₈' 5 : ℂ)=-1
    rw [hi]
    norm_num
  have hu : IsUnit (5 : ZMod 8) := (ZMod.isUnit_iff_coprime 5 8).mpr (by decide)
  rw [hv,MulChar.one_apply hu] at he
  norm_num at he

/-- Exact positive character combination, including all nonunit residue classes. -/
theorem bulkEight_character_eq (n : ℕ) :
    bulkEight n=(2*(1 : DirichletCharacter ℂ 8) n+2*charFour n+
      charTwo n+charNegTwo n)/6 := by
  have hfinite (a : ZMod 8) :
      bulkEight a.val=(2*(1 : DirichletCharacter ℂ 8) a+2*charFour a+
        charTwo a+charNegTwo a)/6 := by
    have hu : IsUnit a ↔ a.val%2=1 := by
      rw [←ZMod.natCast_zmod_val a,ZMod.isUnit_iff_coprime]
      have hf : ∀ b : ZMod 8,b.val.Coprime 8 ↔ b.val%2=1 := by decide
      simpa only [ZMod.natCast_zmod_val] using hf a
    have hp : (1 : DirichletCharacter ℂ 8) a=
        ((if a.val%2=1 then 1 else 0 : ℤ) : ℂ) := by
      change (MulChar.trivial (ZMod 8) ℂ) a=_
      simp only [MulChar.trivial_apply,hu]
      split_ifs <;> norm_num
    have hi : 2*(if a.val%2=1 then 1 else 0 : ℤ)+2*intFourEight a+
        ZMod.χ₈ a+ZMod.χ₈' a=(if a.val=1 then 6 else if a.val=5 then 2 else 0) := by
      have hf : ∀ b : ZMod 8,2*(if b.val%2=1 then 1 else 0 : ℤ)+2*intFourEight b+
          ZMod.χ₈ b+ZMod.χ₈' b=(if b.val=1 then 6 else if b.val=5 then 2 else 0) := by
        decide
      exact hf a
    have hc := congrArg (fun z : ℤ => (z : ℂ)) hi
    have hb : ((if a.val=1 then 6 else if a.val=5 then 2 else 0 : ℤ) : ℂ)=
        6*bulkEight a.val := by
      unfold bulkEight
      rw [Nat.mod_eq_of_lt a.val_lt]
      split_ifs <;> norm_num
    simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat] at hc
    rw [hb] at hc
    rw [hp]
    change bulkEight a.val=(2*((if a.val%2=1 then 1 else 0 : ℤ) : ℂ)+
      2*(intFourEight a : ℂ)+(ZMod.χ₈ a : ℂ)+(ZMod.χ₈' a : ℂ))/6
    linear_combination -hc/6
  have h := hfinite (n : ZMod 8)
  simpa only [ZMod.val_natCast,bulkEight,Nat.mod_mod] using h

/-- Completed all-power response of the literal fixed residue profile. -/
def completeResponse (s : ℂ) : ℂ :=
  -(2*logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 8)) s+
    2*logDeriv charFour.LFunction s+logDeriv charTwo.LFunction s+
      logDeriv charNegTwo.LFunction s)/6

/-- The whole finite code is a scalar character profile for arbitrary signed weights. -/
theorem bulkEight_join (X : ℕ) (w : ℕ → ℂ) :
    (∑ n∈Finset.Icc 1 X,w n*bulkEight n)=
      (2*(∑ n∈Finset.Icc 1 X,w n*(1 : DirichletCharacter ℂ 8) n)+
        2*(∑ n∈Finset.Icc 1 X,w n*charFour n)+
        (∑ n∈Finset.Icc 1 X,w n*charTwo n)+
        (∑ n∈Finset.Icc 1 X,w n*charNegTwo n))/6 := by
  have he (n : ℕ) : w n*bulkEight n=
      (2*(w n*(1 : DirichletCharacter ℂ 8) n)+2*(w n*charFour n)+
        w n*charTwo n+w n*charNegTwo n)/6 := by
    rw [bulkEight_character_eq]
    ring
  simp only [he]
  rw [←Finset.sum_div]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum]

/-- The endpoint is small for every positive ordinary prime; both quadratic codes stay joined. -/
theorem norm_threeEndpoint_le {p : ℕ} (hp : 0<p) :
    ‖threeEndpoint p‖≤1/(p : ℝ) := by
  have h8 : ‖(ZMod.χ₈ p : ℂ)‖≤1 := charTwo.norm_le_one (p : ZMod 8)
  have h4 : ‖(ZMod.χ₄ p : ℂ)‖≤1 :=
    DirichletCharacter.norm_le_one
      (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ 4) (p : ZMod 4)
  have h8a : ‖2+(ZMod.χ₈ p : ℂ)‖≤3 := by
    calc
      _ ≤ ‖(2 : ℂ)‖+‖(ZMod.χ₈ p : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 := by norm_num at *; linarith
  have h4a : ‖1-(ZMod.χ₄ p : ℂ)‖≤2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖+‖(ZMod.χ₄ p : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 := by norm_num at *; linarith
  unfold threeEndpoint
  rw [norm_div,norm_mul,norm_mul]
  norm_num only [Complex.norm_natCast,Complex.norm_ofNat]
  have hpR : (0 : ℝ)<p := by exact_mod_cast hp
  calc
    _ ≤ (3*2)/(6*(p : ℝ)) :=
      div_le_div_of_nonneg_right (mul_le_mul h8a h4a (norm_nonneg _) (by norm_num))
        (by positivity)
    _ = 1/(p : ℝ) := by field_simp [hpR.ne']; ring

/-- Prime two is a separate literal head, not an omitted residue endpoint. -/
theorem threeQuadTrace_two : threeQuadTrace 2=2/3 := by
  unfold threeQuadTrace
  rw [dite_eq_left (by decide : Nat.Prime 2)]
  rw [commonTrace_three_eq (by decide),rowTrace_eq (by decide)]
  unfold alphabetMean
  rw [show (2 : ZMod 2)=0 by decide,show (-1 : ZMod 2)=1 by decide]
  norm_num [MulChar.map_zero]

/-- Uniform finite residue density; this is an integer table, not a prime-distribution claim. -/
theorem bulkEight_residue_density : (∑ a : ZMod 8,bulkEight a.val)=4/3 := by
  have hi : (∑ a : ZMod 8,if a.val=1 then (6 : ℤ) else if a.val=5 then 2 else 0)=8 := by
    decide
  have hc := congrArg (fun z : ℤ => (z : ℂ)) hi
  have hb (a : ZMod 8) : 6*bulkEight a.val=
      ((if a.val=1 then 6 else if a.val=5 then 2 else 0 : ℤ) : ℂ) := by
    unfold bulkEight
    rw [Nat.mod_eq_of_lt a.val_lt]
    split_ifs <;> norm_num
  have hs : 6*(∑ a : ZMod 8,bulkEight a.val)=8 := by
    rw [Finset.mul_sum]
    simp_rw [hb]
    simpa only [Int.cast_sum,Int.cast_ofNat] using hc
  linear_combination hs/6

/-- Nonprincipal analytic orders are finite, proved from their actual nonzero Euler value. -/
theorem nonprincipal_order_ne_top (χ : DirichletCharacter ℂ 8) (hχ : χ≠1) (s : ℂ) :
    analyticOrderAt χ.LFunction s≠⊤ := by
  intro htop
  have ha : AnalyticOnNhd ℂ χ.LFunction Set.univ := fun w _ =>
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt w
  have he : χ.LFunction=(0 : ℂ → ℂ) := ha.eq_of_eventuallyEq
    analyticOnNhd_const (analyticOrderAt_eq_top.mp htop)
  have hn : χ.LFunction (2 : ℂ)≠0 := by
    rw [χ.LFunction_eq_LSeries (by norm_num)]
    exact χ.LSeries_ne_zero_of_one_lt_re (by norm_num)
  exact hn (by rw [he]; rfl)

/-- The single excluded Euler factor for the principal level-eight character. -/
def twoFactor (s : ℂ) : ℂ := 1-(2 : ℂ)^(-s)

theorem analyticAt_twoFactor (s : ℂ) : AnalyticAt ℂ twoFactor s := by
  let : NeZero (2 : ℂ) := ⟨by norm_num⟩
  exact analyticAt_const.sub
    (AnalyticAt.comp ((differentiable_const_cpow_of_neZero (2 : ℂ)).analyticAt (-s))
      analyticAt_id.neg)

theorem twoFactor_ne_zero {s : ℂ} (hs : 0<s.re) : twoFactor s≠0 := by
  have hn : ‖(2 : ℂ)^(-s)‖<1 := by
    rw [show (2 : ℂ)=((2 : ℕ) : ℂ) by norm_num,
      Complex.norm_natCast_cpow_of_pos (by norm_num : 0<(2 : ℕ))]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by simpa using hs)
  intro h
  have he := congrArg norm (sub_eq_zero.mp h)
  simp only [norm_one] at he
  linarith

theorem principal_eq {s : ℂ} (hs : s≠1) :
    (1 : DirichletCharacter ℂ 8).LFunction s=twoFactor s*riemannZeta s := by
  change DirichletCharacter.LFunctionTrivChar 8 s=_
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs,
    show (8 : ℕ).primeFactors={2} by
      convert Nat.primeFactors_prime_pow (by decide : (3 : ℕ)≠0) (by decide : Nat.Prime 2) using 1]
  simp only [Finset.prod_singleton,twoFactor,Nat.cast_ofNat]

theorem analyticAt_principal {s : ℂ} (hs : s≠1) :
    AnalyticAt ℂ (1 : DirichletCharacter ℂ 8).LFunction s := by
  have hd : DifferentiableOn ℂ (1 : DirichletCharacter ℂ 8).LFunction
      ({(1 : ℂ)}ᶜ) := fun w hw =>
    ((1 : DirichletCharacter ℂ 8).differentiableAt_LFunction w (Or.inl hw)).differentiableWithinAt
  exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hs)

/-- The principal part retains exactly the genuine zeta multiplicity. -/
theorem principal_order (rho : NontrivialZetaZero) :
    analyticOrderAt (1 : DirichletCharacter ℂ 8).LFunction rho.1=
      analyticOrderAt riemannZeta rho.1 := by
  have hg : (1 : DirichletCharacter ℂ 8).LFunction=ᶠ[𝓝 rho.1]
      twoFactor*riemannZeta := by
    filter_upwards [isOpen_compl_singleton.mem_nhds rho.2.2.2] with s hs
    exact principal_eq hs
  rw [analyticOrderAt_congr hg,
    analyticOrderAt_mul (analyticAt_twoFactor rho.1)
      (analyticAt_riemannZeta_nontrivialZero rho),
    analyticOrderAt_eq_zero.mpr (Or.inr (twoFactor_ne_zero
      (NontrivialZetaZero.zero_lt_re rho))),zero_add]

/-- All actual L-divisor multiplicities add with the same sign. -/
def sourceMass (rho : NontrivialZetaZero) : ℝ :=
  (analyticZetaZeroMultiplicity rho : ℝ)/3+
    (analyticOrderNatAt charFour.LFunction rho.1 : ℝ)/3+
    (analyticOrderNatAt charTwo.LFunction rho.1 : ℝ)/6+
    (analyticOrderNatAt charNegTwo.LFunction rho.1 : ℝ)/6

/-- Exact nonzero source, without exposure or an assumption excluding simultaneous L-zeros. -/
theorem tendsto_completeResponse_residue (rho : NontrivialZetaZero) :
    Tendsto (fun s : ℂ => (s-rho.1)*completeResponse s) (𝓝[≠] rho.1)
      (𝓝 (-(sourceMass rho : ℂ))) := by
  have hp := (AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt
    (analyticAt_principal rho.2.2.2)
    (by rw [principal_order rho]; exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho))
  have hm : analyticOrderNatAt (1 : DirichletCharacter ℂ 8).LFunction rho.1=
      analyticZetaZeroMultiplicity rho := by
    unfold analyticOrderNatAt analyticZetaZeroMultiplicity
    rw [principal_order rho]
    rfl
  rw [hm] at hp
  have hc (χ : DirichletCharacter ℂ 8) (hχ : χ≠1) :=
    AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt
      ((DirichletCharacter.differentiable_LFunction hχ).analyticAt rho.1)
      (nonprincipal_order_ne_top χ hχ rho.1)
  have h := (((hp.const_mul 2).add ((hc charFour charFour_ne_one).const_mul 2)).add
    (hc charTwo charTwo_ne_one)).add (hc charNegTwo charNegTwo_ne_one)
  have hh := h.neg.div_const 6
  convert hh using 1
  · funext s
    unfold completeResponse
    ring
  · simp only [sourceMass,Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_natCast,
      Complex.ofReal_ofNat]
    ring

theorem sourceMass_lower (rho : NontrivialZetaZero) :
    (analyticZetaZeroMultiplicity rho : ℝ)/3≤sourceMass rho := by
  unfold sourceMass
  have h4 : (0 : ℝ)≤analyticOrderNatAt charFour.LFunction rho.1 := Nat.cast_nonneg _
  have h2 : (0 : ℝ)≤analyticOrderNatAt charTwo.LFunction rho.1 := Nat.cast_nonneg _
  have hn : (0 : ℝ)≤analyticOrderNatAt charNegTwo.LFunction rho.1 := Nat.cast_nonneg _
  linarith

theorem sourceMass_pos (rho : NontrivialZetaZero) : 0<sourceMass rho := by
  have hp : (0 : ℝ)<analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  linarith [sourceMass_lower rho]

theorem sourceMass_ne_zero (rho : NontrivialZetaZero) : (sourceMass rho : ℂ)≠0 := by
  exact_mod_cast (sourceMass_pos rho).ne'

/-- All prime powers are included in the completed fixed-filter coefficient. -/
def bulkCoefficient (n : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ)*bulkEight n

theorem norm_bulkEight_le (n : ℕ) : ‖bulkEight n‖≤1 := by
  unfold bulkEight
  split_ifs <;> norm_num

theorem bulkCoefficient_summable {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable bulkCoefficient s := by
  apply Summable.of_norm
  apply (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm.of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro n
  apply LSeries.norm_term_le
  unfold bulkCoefficient
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_bulkEight_le n)

/-- Exact convergent Euler response, including every proper prime power. -/
theorem bulk_euler {s : ℂ} (hs : 1<s.re) : LSeries bulkCoefficient s=completeResponse s := by
  let f (χ : DirichletCharacter ℂ 8) : ℕ → ℂ :=
    fun n => χ n*(ArithmeticFunction.vonMangoldt n : ℂ)
  have hf (χ : DirichletCharacter ℂ 8) : LSeriesSummable (f χ) s :=
    χ.LSeriesSummable_twist_vonMangoldt hs
  have he (χ : DirichletCharacter ℂ 8) : LSeries (f χ) s=-logDeriv χ.LFunction s := by
    change LSeries ((fun n : ℕ => χ n)*(fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s=_
    rw [χ.LSeries_twist_vonMangoldt_eq hs,
      ←χ.deriv_LFunction_eq_deriv_LSeries hs,←χ.LFunction_eq_LSeries hs]
    simp only [logDeriv_apply,neg_div]
  have hj : bulkCoefficient=(1/6 : ℂ) •
      ((2 : ℂ) • f 1+(2 : ℂ) • f charFour+f charTwo+f charNegTwo) := by
    funext n
    simp only [bulkCoefficient,Pi.add_apply,Pi.smul_apply,smul_eq_mul,f]
    rw [bulkEight_character_eq]
    ring
  rw [hj,LSeries_smul,LSeries_add (((hf 1).smul 2).add ((hf charFour).smul 2)|>.add (hf charTwo))
    (hf charNegTwo),LSeries_add (((hf 1).smul 2).add ((hf charFour).smul 2)) (hf charTwo),
    LSeries_add ((hf 1).smul 2) ((hf charFour).smul 2),LSeries_smul,LSeries_smul,
    he 1,he charFour,he charTwo,he charNegTwo]
  unfold completeResponse
  ring

/-- Every original height phase is retained before the Euler continuation. -/
theorem phased_bulk_euler (y : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeries (fun n => bulkCoefficient n*SuzukiCarryCorrelation.primePhase y n) s=
      completeResponse (s+I*y) := by
  rw [ArithmeticOperatorGammaTwistAudit.LSeries_primePhase,bulk_euler (by simpa using hs)]

/-- Pole-centered response; this subtraction does not touch any genuine zero residue. -/
def centeredResponse (s : ℂ) : ℂ := completeResponse s-1/(3*(s-1))

theorem tendsto_centeredResponse_residue (rho : NontrivialZetaZero) :
    Tendsto (fun s : ℂ => (s-rho.1)*centeredResponse s) (𝓝[≠] rho.1)
      (𝓝 (-(sourceMass rho : ℂ))) := by
  have ht : Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa using (show Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 (rho.1-rho.1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hc : ContinuousAt (fun s : ℂ => 1/(3*(s-1))) rho.1 :=
    continuousAt_const.div (continuousAt_const.mul (continuousAt_id.sub continuousAt_const))
      (mul_ne_zero (by norm_num) (sub_ne_zero.mpr rho.2.2.2))
  have h := (tendsto_completeResponse_residue rho).sub
    (ht.mul (hc.tendsto.mono_left nhdsWithin_le_nhds))
  simpa only [centeredResponse,mul_sub,zero_mul,sub_zero] using h

/-- Entire filled numerator of the principal L-function at its density pole. -/
def filledPrincipal (s : ℂ) : ℂ := twoFactor s*riemannZeta₁ s

theorem analyticAt_filledPrincipal (s : ℂ) : AnalyticAt ℂ filledPrincipal s :=
  (analyticAt_twoFactor s).mul (differentiable_riemannZeta₁.analyticAt s)

theorem filledPrincipal_one_ne_zero : filledPrincipal 1≠0 := by
  unfold filledPrincipal
  rw [riemannZeta₁_one,mul_one]
  exact twoFactor_ne_zero (by norm_num)

/-- Exact principal pole removal on its punctured domain. -/
theorem principal_filled_eq {s : ℂ} (hs : s≠1) :
    (1 : DirichletCharacter ℂ 8).LFunction s=filledPrincipal s/(s-1) := by
  rw [principal_eq hs,riemannZeta_eq_inv_sub_mul hs]
  unfold filledPrincipal
  ring

/-- The whole centered response has a genuine analytic germ at the density point. -/
theorem centeredResponse_density_germ :
    centeredResponse=ᶠ[𝓝[≠] (1 : ℂ)]
      (fun s => -(2*logDeriv filledPrincipal s+2*logDeriv charFour.LFunction s+
        logDeriv charTwo.LFunction s+logDeriv charNegTwo.LFunction s)/6) := by
  have hlog : logDeriv (1 : DirichletCharacter ℂ 8).LFunction=ᶠ[𝓝[≠] (1 : ℂ)]
      logDeriv (fun s : ℂ => filledPrincipal s/(s-1)) :=
    logDeriv_congr_nhdsNE (by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact principal_filled_eq hs)
  have hn : ∀ᶠ s in 𝓝 (1 : ℂ),filledPrincipal s≠0 :=
    (analyticAt_filledPrincipal 1).continuousAt.eventually_ne filledPrincipal_one_ne_zero
  filter_upwards [hlog,hn.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with s hl hns hs
  have hneq : s≠1 := hs
  unfold centeredResponse completeResponse
  rw [hl,logDeriv_fun_div (g := fun w : ℂ => w-1) s hns (sub_ne_zero.mpr hneq)
    (analyticAt_filledPrincipal s).differentiableAt (by fun_prop)]
  simp only [logDeriv_apply,deriv_sub_const,deriv_id'',one_div]
  field_simp [sub_ne_zero.mpr hneq]
  ring

theorem analyticAt_density_fill :
    AnalyticAt ℂ (fun s => -(2*logDeriv filledPrincipal s+2*logDeriv charFour.LFunction s+
      logDeriv charTwo.LFunction s+logDeriv charNegTwo.LFunction s)/6) 1 := by
  have hlog (χ : DirichletCharacter ℂ 8) (hχ : χ≠1) :
      AnalyticAt ℂ (logDeriv χ.LFunction) 1 := by
    have ha := (DirichletCharacter.differentiable_LFunction hχ).analyticAt (1 : ℂ)
    exact ha.deriv.div ha (χ.LFunction_apply_one_ne_zero hχ)
  have hp := (analyticAt_filledPrincipal 1).deriv.div (analyticAt_filledPrincipal 1)
    filledPrincipal_one_ne_zero
  exact ((((analyticAt_const.mul hp).add
    (analyticAt_const.mul (hlog charFour charFour_ne_one))).add
      (hlog charTwo charTwo_ne_one)).add (hlog charNegTwo charNegTwo_ne_one)).neg.div_const

/-- Pole cancellation is exact; the remaining density germ is locally bounded. -/
theorem tendsto_centered_density_residue :
    Tendsto (fun s : ℂ => (s-1)*centeredResponse s) (𝓝[≠] 1) (𝓝 0) := by
  have ht : Tendsto (fun s : ℂ => s-1) (𝓝[≠] 1) (𝓝 0) := by
    simpa using (show Tendsto (fun s : ℂ => s-1) (𝓝[≠] 1) (𝓝 ((1 : ℂ)-1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have h := ht.mul (analyticAt_density_fill.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [zero_mul] at h
  exact h.congr' (centeredResponse_density_germ.symm.mono (fun s he =>
    congrArg (fun v : ℂ => (s-1)*v) he))

/-- Endpoint at ordinary odd primes only. -/
def endpointCoefficient (n : ℕ) : ℂ :=
  if n.Prime ∧ n≠2 then (ArithmeticFunction.vonMangoldt n : ℂ)*threeEndpoint n else 0

/-- Explicit proper-prime-power correction, with the same fixed residue code. -/
def properCoefficient (n : ℕ) : ℂ := (zetaProperPrimePowerCoefficient n : ℂ)*bulkEight n

/-- The separate literal prime-two head. -/
def headCoefficient (n : ℕ) : ℂ :=
  if n=2 then (ArithmeticFunction.vonMangoldt 2 : ℂ)*(2/3) else 0

/-- Actual ordinary-prime binomial-row coefficient. -/
def rowCoefficient (n : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ)*threeQuadTrace n

/-- No prime, proper power or head is discarded in the literal completion bridge. -/
theorem rowCoefficient_eq (n : ℕ) :
    rowCoefficient n=bulkCoefficient n-properCoefficient n+endpointCoefficient n+headCoefficient n := by
  by_cases hn2 : n=2
  · subst n
    simp only [rowCoefficient,threeQuadTrace_two,bulkCoefficient,properCoefficient,
      zetaProperPrimePowerCoefficient,endpointCoefficient,headCoefficient]
    norm_num [bulkEight]
  · by_cases hp : n.Prime
    · rw [rowCoefficient,threeQuadTrace_prime hp hn2]
      simp [bulkCoefficient,properCoefficient,zetaProperPrimePowerCoefficient,
        endpointCoefficient,headCoefficient,hp,hn2]
      ring
    · simp [rowCoefficient,threeQuadTrace,hp,bulkCoefficient,properCoefficient,
        zetaProperPrimePowerCoefficient,endpointCoefficient,headCoefficient,hn2]

theorem endpointCoefficient_norm (n : ℕ) :
    ‖endpointCoefficient n‖≤‖(ArithmeticFunction.vonMangoldt n : ℂ)/(n : ℂ)‖ := by
  unfold endpointCoefficient
  split_ifs with hn
  · rw [norm_mul,norm_div,Complex.norm_natCast]
    calc
      _ ≤ ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖*(1/(n : ℝ)) :=
        mul_le_mul_of_nonneg_left (norm_threeEndpoint_le hn.1.pos)
          (norm_nonneg (ArithmeticFunction.vonMangoldt n : ℂ))
      _ = ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖/(n : ℝ) := by ring
  · simpa only [norm_zero] using
      norm_nonneg ((ArithmeticFunction.vonMangoldt n : ℂ)/(n : ℂ))

theorem endpoint_summable {s : ℂ} (hs : 0<s.re) : LSeriesSummable endpointCoefficient s := by
  let g : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)/(n : ℂ)
  have ht (n : ℕ) : LSeries.term g s n=
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s+1) n := by
    by_cases hn : n=0
    · subst n
      simp only [LSeries.term_zero]
    · have hnC : (n : ℂ)≠0 := by exact_mod_cast hn
      rw [LSeries.term_of_ne_zero hn,LSeries.term_of_ne_zero hn,cpow_add s 1 hnC,cpow_one]
      dsimp [g]
      ring
  have hg : LSeriesSummable g s :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simp; linarith : 1<(s+1).re)).congr
      (fun n => (ht n).symm)
  apply Summable.of_norm
  exact hg.norm.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n =>
    LSeries.norm_term_le s (endpointCoefficient_norm n))

theorem proper_summable {s : ℂ} (hs : 1/2<s.re) : LSeriesSummable properCoefficient s := by
  apply Summable.of_norm
  apply (LSeriesSummable_zetaProperPrimePower hs).norm.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  apply LSeries.norm_term_le
  unfold properCoefficient
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_bulkEight_le n)

theorem analyticAt_endpoint {s : ℂ} (hs : 0<s.re) : AnalyticAt ℂ (LSeries endpointCoefficient) s := by
  have ha : LSeries.abscissaOfAbsConv endpointCoefficient≤(0 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun y hy =>
      endpoint_summable (by simpa using hy))
  exact LSeries_analyticOnNhd _ _ (lt_of_le_of_lt ha (by exact_mod_cast hs))

theorem analyticAt_proper {s : ℂ} (hs : 1/2<s.re) : AnalyticAt ℂ (LSeries properCoefficient) s := by
  have ha : LSeries.abscissaOfAbsConv properCoefficient≤(1/2 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun y hy =>
      proper_summable (by simpa using hy))
  exact LSeries_analyticOnNhd _ _ (lt_of_le_of_lt ha (by exact_mod_cast hs))

theorem head_summable (s : ℂ) : LSeriesSummable headCoefficient s := by
  apply summable_of_ne_finset_zero (s := {2})
  intro n hn
  have hn2 : n≠2 := by simpa only [Finset.mem_singleton] using hn
  simp only [LSeries.term,headCoefficient,ite_eq_right hn2,zero_div,ite_self]

/-- The literal finite head is entire, even where the bulk Euler series needs continuation. -/
theorem head_euler (s : ℂ) : LSeries headCoefficient s=
    (ArithmeticFunction.vonMangoldt 2 : ℂ)*(2/3)*(2 : ℂ)^(-s) := by
  unfold LSeries
  rw [tsum_eq_single 2]
  · simp only [LSeries.term_of_ne_zero (by decide : (2 : ℕ)≠0),headCoefficient,ite_true,
      Nat.cast_ofNat,cpow_neg,div_eq_mul_inv]
  · intro n hn
    simp only [LSeries.term,headCoefficient,ite_eq_right hn,zero_div,ite_self]

theorem analyticAt_head (s : ℂ) : AnalyticAt ℂ (LSeries headCoefficient) s := by
  have he : LSeries headCoefficient=(fun w =>
      (ArithmeticFunction.vonMangoldt 2 : ℂ)*(2/3)*(2 : ℂ)^(-w)) := funext head_euler
  rw [he]
  let : NeZero (2 : ℂ) := ⟨by norm_num⟩
  exact analyticAt_const.mul
    (AnalyticAt.comp ((differentiable_const_cpow_of_neZero (2 : ℂ)).analyticAt (-s))
      analyticAt_id.neg)

/-- Analytic continuation of the ordinary-prime literal row, not a convergent Euler sum in the strip. -/
def rowResponse (s : ℂ) : ℂ :=
  completeResponse s-LSeries properCoefficient s+LSeries endpointCoefficient s+LSeries headCoefficient s

theorem row_euler {s : ℂ} (hs : 1<s.re) : LSeries rowCoefficient s=rowResponse s := by
  have hj : rowCoefficient=bulkCoefficient-properCoefficient+endpointCoefficient+headCoefficient := by
    funext n
    exact rowCoefficient_eq n
  have hb := bulkCoefficient_summable hs
  have hp := proper_summable (by linarith : 1/2<s.re)
  have he := endpoint_summable (by linarith : 0<s.re)
  rw [hj,LSeries_add ((hb.sub hp).add he) (head_summable s),LSeries_add (hb.sub hp) he,
    LSeries_sub hb hp,bulk_euler hs,rowResponse]

theorem phased_row_euler (y : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeries (fun n => rowCoefficient n*SuzukiCarryCorrelation.primePhase y n) s=rowResponse (s+I*y) := by
  rw [ArithmeticOperatorGammaTwistAudit.LSeries_primePhase,row_euler (by simpa using hs)]

/-- Literal ordinary-prime source survives every explicitly paid completion correction. -/
theorem tendsto_rowResponse_residue (rho : NontrivialZetaZero) (hrho : 1/2<rho.1.re) :
    Tendsto (fun s : ℂ => (s-rho.1)*rowResponse s) (𝓝[≠] rho.1)
      (𝓝 (-(sourceMass rho : ℂ))) := by
  have ht : Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa using (show Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 (rho.1-rho.1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hp := ht.mul ((analyticAt_proper hrho).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have he := ht.mul ((analyticAt_endpoint (NontrivialZetaZero.zero_lt_re rho)).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds)
  have hh := ht.mul ((analyticAt_head rho.1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have h := (((tendsto_completeResponse_residue rho).sub hp).add he).add hh
  simpa only [rowResponse,mul_add,mul_sub,zero_mul,sub_zero,add_zero] using h

/-- The completed source detector cannot be holomorphic through an actual right-half zero. -/
theorem not_analyticAt_rowResponse (rho : NontrivialZetaZero) (hrho : 1/2<rho.1.re) :
    ¬AnalyticAt ℂ rowResponse rho.1 := by
  intro ha
  have ht : Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa using (show Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 (rho.1-rho.1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hz := ht.mul (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [zero_mul] at hz
  exact neg_ne_zero.mpr (sourceMass_ne_zero rho)
    (tendsto_nhds_unique (tendsto_rowResponse_residue rho hrho) hz)

/-- The exact completion correction is analytic in the whole right half of the zero strip. -/
def regularCorrection (s : ℂ) : ℂ :=
  -LSeries properCoefficient s+LSeries endpointCoefficient s+LSeries headCoefficient s

theorem analyticAt_regularCorrection {s : ℂ} (hs : 1/2<s.re) :
    AnalyticAt ℂ regularCorrection s :=
  (((analyticAt_proper hs).neg).add (analyticAt_endpoint (by linarith))).add (analyticAt_head s)

/-- Density subtraction for the actual ordinary-prime row, without changing its arithmetic code. -/
def centeredRowResponse (s : ℂ) : ℂ := centeredResponse s+regularCorrection s

theorem centeredRowResponse_eq (s : ℂ) :
    centeredRowResponse s=rowResponse s-1/(3*(s-1)) := by
  unfold centeredRowResponse rowResponse centeredResponse regularCorrection
  ring

theorem tendsto_centeredRowResponse_residue (rho : NontrivialZetaZero) (hrho : 1/2<rho.1.re) :
    Tendsto (fun s : ℂ => (s-rho.1)*centeredRowResponse s) (𝓝[≠] rho.1)
      (𝓝 (-(sourceMass rho : ℂ))) := by
  have ht : Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa using (show Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 (rho.1-rho.1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hc := ht.mul ((analyticAt_regularCorrection hrho).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds)
  simpa only [centeredRowResponse,mul_add,zero_mul,add_zero] using
    (tendsto_centeredResponse_residue rho).add hc

theorem tendsto_centeredRow_density_residue :
    Tendsto (fun s : ℂ => (s-1)*centeredRowResponse s) (𝓝[≠] 1) (𝓝 0) := by
  have ht : Tendsto (fun s : ℂ => s-1) (𝓝[≠] 1) (𝓝 0) := by
    simpa using (show Tendsto (fun s : ℂ => s-1) (𝓝[≠] 1) (𝓝 ((1 : ℂ)-1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hc := ht.mul ((analyticAt_regularCorrection (by norm_num : 1/2<(1 : ℂ).re)).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds)
  simpa only [centeredRowResponse,mul_add,zero_mul,zero_add] using
    tendsto_centered_density_residue.add hc

/-- A literal prime in the surviving unit residue class has a full, non-small row trace. -/
theorem threeQuadTrace_seventeen : threeQuadTrace 17=1 := by
  rw [threeQuadTrace_prime (by decide : Nat.Prime 17) (by decide : (17 : ℕ)≠2)]
  norm_num [bulkEight,threeEndpoint,ZMod.χ₈_nat_eq_if_mod_eight,ZMod.χ₄_nat_eq_if_mod_four]

/-- The surviving code is exactly one on every ordinary prime congruent to one modulo eight. -/
theorem threeQuadTrace_mod_one {p : ℕ} (hp : p.Prime) (hm : p%8=1) :
    threeQuadTrace p=1 := by
  have hp2 : p≠2 := by omega
  have hm4 : p%4=1 := by omega
  have hm2 : p%2=1 := by omega
  rw [threeQuadTrace_prime hp hp2,threeEndpoint,ZMod.χ₈_nat_eq_if_mod_eight,
    ZMod.χ₄_nat_eq_if_mod_four]
  norm_num [bulkEight,hm,hm4,hm2]

/-- This exact non-small code occurs beyond every head, by the proved ordinary Dirichlet theorem. -/
theorem exists_prime_trace_one (H : ℕ) : ∃ p>H,p.Prime ∧ threeQuadTrace p=1 := by
  obtain ⟨p,hpH,hp,hm⟩ := Nat.forall_exists_prime_gt_and_modEq H
    (q := 8) (a := 1) (by decide) (by decide)
  refine ⟨p,hpH,hp,threeQuadTrace_mod_one hp ?_⟩
  simpa only [Nat.ModEq,Nat.mod_eq_of_lt (by decide : 1<8)] using hm

/-- The finite row identity alone cannot constrain arbitrary outer weights, even at an actual prime. -/
theorem arbitrary_weight_unbounded {B : ℝ} (hB : 0≤B) :
    ∃ w : ℕ → ℂ,B<‖∑ p∈({17} : Finset ℕ),w p*threeQuadTrace p‖ := by
  refine ⟨fun _ => ((B+1 : ℝ) : ℂ),?_⟩
  rw [Finset.sum_singleton,threeQuadTrace_seventeen,mul_one,Complex.norm_real,
    Real.norm_of_nonneg (by linarith : 0≤B+1)]
  linarith

/-- No identity-only bound for arbitrary outer weights is gained by deleting any finite head. -/
theorem arbitrary_weight_unbounded_beyond_head (H : ℕ) {B : ℝ} (hB : 0≤B) :
    ∃ p>H,p.Prime ∧ ∃ w : ℕ → ℂ,
      B<‖∑ n∈({p} : Finset ℕ),w n*threeQuadTrace n‖ := by
  obtain ⟨p,hpH,hp,ht⟩ := exists_prime_trace_one H
  refine ⟨p,hpH,hp,fun _ => ((B+1 : ℝ) : ℂ),?_⟩
  rw [Finset.sum_singleton,ht,mul_one,Complex.norm_real,
    Real.norm_of_nonneg (by linarith : 0≤B+1)]
  linarith

end RiemannGaussian.ArithmeticOperatorCrossUnitAudit

#lint+ in RiemannGaussian.ArithmeticOperatorCrossUnitAudit

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
  unless declarations > 0 do throwError "Empty cross-unit audit."
  logInfo m!"Cross-unit audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-cross-unit"
  IO.FS.writeFile ".lake/arithmetic-operator-cross-unit/axioms.json"
    (Json.mkObj [("scope",toJson "literal fixed-cofactor-three quadratic binomial code and source/collapse gate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
