/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorComparableDigitalAudit

/-!
# Exact finite correlation of the native ternary factorial code

The code is the literal digit/factorial code from ComparableDigital. Cyclic
finite correlations obey exact digit recurrences. Two consecutive one digits
contract the two-component recurrence; no prime-weight estimate or spectral
limit is asserted here. The moving-scale source gate is documented separately.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
namespace OpenAIReview.TernaryCorrelation
open ComparableDigital

/-- Appending an actual base-three digit, including the zero head. -/
theorem code_mul_add (w : ℂ) (n d : ℕ) (hd : d<3) :
    ternaryCode w (3*n+d)=w^d*ternaryCode w n := by
  by_cases h : d=0 ∧ n=0
  · rcases h with ⟨rfl,rfl⟩
    simp [ternaryCode,ternaryDigits]
  · have hne : d≠0 ∨ n≠0 := by omega
    rw [show 3*n+d=d+3*n by omega]
    simp [ternaryCode,ternaryDigits,Nat.digits_add 3 (by norm_num) d n hd hne,
      pow_add]

/-- Finite cyclic approximation retaining exactly M low ternary digits. -/
def periodCode (w : ℂ) (M n : ℕ) : ℂ := ternaryCode w (n%3^M)

/-- Exact remainder decomposition, without an asymptotic carry error. -/
theorem mod_three_block {P : ℕ} (hP : 0<P) (n d : ℕ) (hd : d<3) :
    (3*n+d)%(3*P)=3*(n%P)+d := by
  have hn := Nat.mod_lt n hP
  have he : 3*n+d=(3*(n%P)+d)+(n/P)*(3*P) := by
    have h := Nat.mod_add_div n P
    nlinarith
  rw [he,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt]
  omega

/-- Native finite digit recurrence; no free sequence is introduced. -/
theorem periodCode_mul_add (w : ℂ) (M n d : ℕ) (hd : d<3) :
    periodCode w (M+1) (3*n+d)=w^d*periodCode w M n := by
  rw [periodCode,pow_succ',mod_three_block (by positivity) n d hd,code_mul_add w _ d hd]
  rfl

/-- A literal cyclic correlation summand. -/
def correlationTerm (w : ℂ) (M h n : ℕ) : ℂ :=
  periodCode w M (n+h)*star (periodCode w M n)

/-- The finite cyclic average, not its infinite-volume limit. -/
def cyclicCorrelation (w : ℂ) (M h : ℕ) : ℂ :=
  (∑ n∈Finset.range (3^M),correlationTerm w M h n)/(3^M : ℂ)

/-- Exact partition into all three residue classes. -/
theorem sum_three_blocks (P : ℕ) (f : ℕ → ℂ) :
    (∑ n∈Finset.range (3*P),f n)=
      ∑ n∈Finset.range P,(f (3*n)+f (3*n+1)+f (3*n+2)) := by
  induction P with
  | zero => simp
  | succ P ih =>
    rw [show 3*(P+1)=3*P+1+1+1 by omega]
    simp only [Finset.sum_range_succ]
    rw [ih]
    ring

/-- A primitive cubic phase has unit norm. -/
theorem cubic_norm {w : ℂ} (hw : w^2+w+1=0) : ‖w‖=1 := by
  have h3 : w^3=1 := by linear_combination (w-1)*hw
  exact Complex.norm_eq_one_of_pow_eq_one h3 (by norm_num : (3 : ℕ)≠0)

/-- Conjugation is the second cubic power, with the actual complex norm. -/
theorem cubic_star {w : ℂ} (hw : w^2+w+1=0) : star w=w^2 := by
  have hn := cubic_norm hw
  have hunit : w*star w=1 := by
    simp only [Complex.star_def,Complex.mul_conj',hn,one_pow,Complex.ofReal_one]
  have h3 : w^3=1 := by linear_combination (w-1)*hw
  have hne : w≠0 := by intro he; simp [he] at h3
  apply mul_left_cancel₀ hne
  rw [hunit]
  linear_combination -h3

/-- The cubic phase across a carry is unchanged, including wraparound. -/
theorem digit_phase {w : ℂ} (hw : w^2+w+1=0) (r d : ℕ) :
    w^((r+d)%3)*star (w^r)=w^d := by
  have h3 : w^3=1 := by linear_combination (w-1)*hw
  have hunit : w*star w=1 := by
    simp only [Complex.star_def,Complex.mul_conj',cubic_norm hw,one_pow,
      Complex.ofReal_one]
  rw [← pow_eq_pow_mod (r+d) h3,pow_add,star_pow]
  calc
    (w^r*w^d)*(star w)^r=w^d*(w*star w)^r := by rw [mul_pow]; ring
    _=w^d := by rw [hunit]; simp only [one_pow,mul_one]

/-- Exact literal carry in a finite cyclic correlation summand. -/
theorem term_digits {w : ℂ} (hw : w^2+w+1=0) (M h n d r : ℕ)
    (hr : r<3) :
    correlationTerm w (M+1) (3*h+d) (3*n+r)=
      w^d*correlationTerm w M (h+(r+d)/3) n := by
  have he : 3*n+r+(3*h+d)=3*(n+h+(r+d)/3)+(r+d)%3 := by omega
  rw [correlationTerm,he,periodCode_mul_add w M _ _ (Nat.mod_lt _ (by norm_num)),
    periodCode_mul_add w M n r hr,star_mul]
  calc
    _=(w^((r+d)%3)*star (w^r))*
      (periodCode w M (n+h+(r+d)/3)*star (periodCode w M n)) := by ring
    _=w^d*correlationTerm w M (h+(r+d)/3) n := by
      rw [digit_phase hw]
      simp only [correlationTerm,Nat.add_assoc]

/-- Exact finite digit recurrence. There is no boundary allowance. -/
theorem correlation_digits {w : ℂ} (hw : w^2+w+1=0) (M h d : ℕ)
    (hd : d<3) :
    cyclicCorrelation w (M+1) (3*h+d)=
      w^d*((3-d : ℕ)*cyclicCorrelation w M h+
        (d : ℂ)*cyclicCorrelation w M (h+1))/3 := by
  have hP : (3^M : ℂ)≠0 := pow_ne_zero _ (by norm_num)
  have he0 (n : ℕ) : correlationTerm w (M+1) (3*h+d) (3*n)=
      w^d*correlationTerm w M h n := by
    simpa only [Nat.add_zero,Nat.zero_add,Nat.div_eq_of_lt hd] using
      term_digits hw M h n d 0 (by norm_num)
  have he1 (n : ℕ) := term_digits hw M h n d 1 (by norm_num)
  have he2 (n : ℕ) := term_digits hw M h n d 2 (by norm_num)
  unfold cyclicCorrelation
  rw [pow_succ',sum_three_blocks]
  simp_rw [he0,he1,he2]
  interval_cases d <;>
    norm_num only [Nat.reduceAdd,Nat.reduceDiv,Nat.reduceSub,Nat.cast_ofNat,
      Nat.cast_zero,Nat.cast_one,Nat.add_zero,zero_mul,one_mul,pow_zero,pow_one] <;>
    simp only [Finset.sum_add_distrib,← Finset.mul_sum] <;>
    rw [pow_succ'] <;> field_simp <;> ring

/-- The native digit-one transfer on two adjacent correlations. -/
def oneStep (w : ℂ) (v : ℂ × ℂ) : ℂ × ℂ :=
  ((2*w*v.1+w*v.2)/3,(w^2*v.1+2*w^2*v.2)/3)

/-- Two digit-one transitions expose cancellation of cubic phases exactly. -/
theorem oneStep_twice {w : ℂ} (hw : w^2+w+1=0) (v : ℂ × ℂ) :
    oneStep w (oneStep w v)=
      (((1+4*w^2)*v.1+(2+2*w^2)*v.2)/9,
        ((2+2*w)*v.1+(1+4*w)*v.2)/9) := by
  have h3 : w^3=1 := by linear_combination (w-1)*hw
  have h4 : w^4=w := by calc
    w^4=w^3*w := by ring
    _=w := by rw [h3,one_mul]
  apply Prod.ext <;> dsimp [oneStep] <;> ring_nf <;> simp only [h3,h4] <;> ring

/-- A two-entry complex row estimate, used only after exact phase cancellation. -/
theorem norm_row_seven {a b x y : ℂ} (ha : ‖a‖≤5) (hb : ‖b‖≤2) :
    ‖(a*x+b*y)/9‖≤(7/9 : ℝ)*max ‖x‖ ‖y‖ := by
  calc
    ‖(a*x+b*y)/9‖=‖a*x+b*y‖/9 := by rw [norm_div]; norm_num
    _≤(‖a‖*‖x‖+‖b‖*‖y‖)/9 := by
      gcongr
      simpa only [norm_mul] using norm_add_le (a*x) (b*y)
    _≤(5*‖x‖+2*‖y‖)/9 := by gcongr
    _≤(7/9 : ℝ)*max ‖x‖ ‖y‖ := by
      have hx := le_max_left ‖x‖ ‖y‖
      have hy := le_max_right ‖x‖ ‖y‖
      linarith

/-- A strict rational contraction for the actual two-one-digit block.
The sharper constant (sqrt 13+2)/9 is unnecessary for this finite gate. -/
theorem oneStep_twice_norm {w : ℂ} (hw : w^2+w+1=0) (v : ℂ × ℂ) :
    ‖oneStep w (oneStep w v)‖≤(7/9 : ℝ)*‖v‖ := by
  have hn := cubic_norm hw
  have ha : ‖(1+4*w^2 : ℂ)‖≤5 := by
    calc
      _≤‖(1 : ℂ)‖+‖4*w^2‖ := norm_add_le _ _
      _=5 := by norm_num [norm_mul,norm_pow,hn]
  have hb : ‖(2+2*w^2 : ℂ)‖≤2 := by
    have he : (2+2*w^2 : ℂ)= -2*w := by linear_combination 2*hw
    rw [he]
    norm_num [norm_mul,hn]
  have hc : ‖(1+4*w : ℂ)‖≤5 := by
    calc
      _≤‖(1 : ℂ)‖+‖4*w‖ := norm_add_le _ _
      _=5 := by norm_num [norm_mul,hn]
  have hd : ‖(2+2*w : ℂ)‖≤2 := by
    have he : (2+2*w : ℂ)= -2*w^2 := by linear_combination 2*hw
    rw [he]
    norm_num [norm_mul,norm_pow,hn]
  rw [oneStep_twice hw]
  change max _ _≤(7/9 : ℝ)*max ‖v.1‖ ‖v.2‖
  apply max_le
  · exact norm_row_seven ha hb
  · simpa only [add_comm,max_comm] using
      (norm_row_seven (x:=v.2) (y:=v.1) hc hd)

/-- Adjacent correlations of the actual finite factorial/digit code. -/
def cyclicPair (w : ℂ) (M h : ℕ) : ℂ × ℂ :=
  (cyclicCorrelation w M h,cyclicCorrelation w M (h+1))

/-- The transfer matrix is exactly the native finite recurrence. -/
theorem cyclicPair_one {w : ℂ} (hw : w^2+w+1=0) (M h : ℕ) :
    cyclicPair w (M+1) (3*h+1)=oneStep w (cyclicPair w M h) := by
  apply Prod.ext
  · change cyclicCorrelation w (M+1) (3*h+1)=_
    rw [correlation_digits hw M h 1 (by norm_num)]
    norm_num only [Nat.reduceSub,Nat.cast_ofNat,pow_one,one_mul,oneStep,cyclicPair]
    ring
  · change cyclicCorrelation w (M+1) (3*h+1+1)=_
    rw [show 3*h+1+1=3*h+2 by omega,correlation_digits hw M h 2 (by norm_num)]
    norm_num only [Nat.reduceSub,Nat.cast_ofNat,Nat.cast_one,one_mul,oneStep,cyclicPair]
    ring

/-- A genuine finite cyclic correlation gains a fixed factor at each 11 block. -/
theorem cyclicPair_two_ones_norm {w : ℂ} (hw : w^2+w+1=0) (M h : ℕ) :
    ‖cyclicPair w (M+2) (9*h+4)‖≤(7/9 : ℝ)*‖cyclicPair w M h‖ := by
  rw [show M+2=(M+1)+1 by omega,show 9*h+4=3*(3*h+1)+1 by omega,
    cyclicPair_one hw,cyclicPair_one hw]
  exact oneStep_twice_norm hw _

/-- Append paired one digits without replacing finite correlations by limits. -/
def onesIndex : ℕ → ℕ → ℕ
  | 0,h => h
  | j+1,h => 9*onesIndex j h+4

/-- Geometric contraction for every finite repeated one-digit block. -/
theorem cyclicPair_ones_norm {w : ℂ} (hw : w^2+w+1=0) (M h j : ℕ) :
    ‖cyclicPair w (M+2*j) (onesIndex j h)‖≤
      (7/9 : ℝ)^j*‖cyclicPair w M h‖ := by
  induction j with
  | zero => simp [onesIndex]
  | succ j ih =>
    rw [show M+2*(j+1)=(M+2*j)+2 by omega,onesIndex]
    calc
      _≤(7/9 : ℝ)*‖cyclicPair w (M+2*j) (onesIndex j h)‖ :=
        cyclicPair_two_ones_norm hw _ _
      _≤(7/9 : ℝ)*((7/9 : ℝ)^j*‖cyclicPair w M h‖) := by gcongr
      _=(7/9 : ℝ)^(j+1)*‖cyclicPair w M h‖ := by rw [pow_succ]; ring

/-- The zero-digit finite cycle starts at (1,1), not the infinite-volume state. -/
theorem cyclicPair_zero (w : ℂ) (h : ℕ) : cyclicPair w 0 h=(1,1) := by
  simp [cyclicPair,cyclicCorrelation,correlationTerm,periodCode,ternaryCode,ternaryDigits,
    Nat.mod_one]

/-- The actual primitive phase and finite initial condition give explicit decay. -/
theorem native_ones_norm (j : ℕ) :
    ‖cyclicPair omega (2*j) (onesIndex j 0)‖≤(7/9 : ℝ)^j := by
  simpa only [Nat.zero_add,cyclicPair_zero,Prod.norm_def,norm_one,max_self,mul_one] using
    cyclicPair_ones_norm omega_cubic 0 0 j

end OpenAIReview.TernaryCorrelation

#lint+ in OpenAIReview.TernaryCorrelation

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
  unless declarations>0 do throwError "Empty ternary-correlation audit."
  logInfo m!"Ternary-correlation audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-ternary-correlation-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-ternary-correlation-gate/axioms.json"
    (Json.mkObj [("scope",toJson "literal finite factorial/digit cyclic recurrence and geometric 11-block contraction; no spectral limit, prime estimate or RH assertion"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("details",Json.arr reports)]).pretty
