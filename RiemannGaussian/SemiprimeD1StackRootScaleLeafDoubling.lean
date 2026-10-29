/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScaleLeafPrimitives
/-! # Twenty paid physical doublings of the actually acquired input width -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
namespace RiemannGaussian.SemiprimeD1StackRootScaleLeafDoubling
open SemiprimeD1StackRootScaleLeaf SemiprimeD1StackRootScaleLeafPrimitives
open SemiprimeD1StackProcedureTrace
/-- Only the real scale and currently reused quotient/work word vary. -/
def data (base : Stack→List Bool) (n q : Nat) : Stack→List Bool :=
  Function.update (Function.update base (aux .scale) (D.unary n)) (divStack .quotient) (D.unary q)
/-- Fixed finite current-round label, never an input-length counter. -/
def phase (p : Fin 20) : Label :=.double ⟨p.val,by omega⟩
/-- The current fixed round contains only actual pop/push instructions. -/
theorem phase_code (p : Fin 20) :
    program (phase p)=.base (.pop (aux .scale) (.restore p) (.doublePush1 p) (.doublePush1 p)) :=by
  simp [program,phase,p.isLt]
/-- Each old metadata marker is physically popped and replaced by TWO work markers. -/
theorem consume (p : Fin 20) (base : Stack→List Bool) (n q : Nat) :
    Runs program (3*n+1) (phase p) (data base n q) (.restore p) (data base 0 (q+2*n)) :=by
  induction n generalizing q with
  | zero=>
    apply one_base program (phase p) (.restore p)
      (.pop (aux .scale) (.restore p) (.doublePush1 p) (.doublePush1 p)) _ _ (phase_code p)
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · rcases k with k|k
        · cases k <;> rfl
        · cases k <;> rfl
  | succ n ih=>
    have h0:Runs program 1 (phase p) (data base (n+1) q) (.doublePush1 p) (data base n q):=by
      apply one_base program (phase p) (.doublePush1 p)
        (.pop (aux .scale) (.restore p) (.doublePush1 p) (.doublePush1 p)) _ _ (phase_code p)
      · rfl
      · funext k;rcases k with k|k
        · rfl
        · rcases k with k|k
          · cases k <;> rfl
          · cases k <;> rfl
    have h1:=push (.doublePush1 p) (.doublePush2 p) (divStack .quotient) (data base n q) rfl
    have he1:Function.update (data base n q) (divStack .quotient) (true::data base n q (divStack .quotient))=
        data base n (q+1):=by
      funext k;rcases k with k|k
      · rfl
      · rcases k with k|k
        · cases k <;> rfl
        · cases k <;> rfl
    rw [he1] at h1
    have h2:=push (.doublePush2 p) (phase p) (divStack .quotient) (data base n (q+1)) rfl
    have he2:Function.update (data base n (q+1)) (divStack .quotient)
        (true::data base n (q+1) (divStack .quotient))=data base n (q+2):=by
      funext k;rcases k with k|k
      · rfl
      · rcases k with k|k
        · cases k <;> rfl
        · cases k <;> rfl
    rw [he2] at h2
    have h:=join (join (join h0 h1) h2) (ih (q+2))
    have ht:((1+1)+1)+(3*n+1)=3*(n+1)+1:=by omega
    have hq:q+2+2*n=q+2*(n+1):=by omega
    rw [ht,hq] at h
    exact h
/-- Both actual scan phases restore the doubled word and clear its work role. -/
theorem double_run (p : Fin 20) (base : Stack→List Bool) (n : Nat) :
    Runs program (7*n+2) (phase p) (data base n 0)
      (.double ⟨p.val+1,by omega⟩) (data base (2*n) 0) :=by
  have h0:=consume p base n 0
  simp only [Nat.zero_add] at h0
  have h1:=SemiprimeD1StackPhysicalLoops.move_unary program (.restore p) (.restorePush p)
    (.double ⟨p.val+1,by omega⟩) (divStack .quotient) (aux .scale) (by decide) rfl rfl base (2*n) []
  have he0:Function.update (Function.update base (aux .scale) []) (divStack .quotient) (D.unary (2*n))=
      data base 0 (2*n):=rfl
  have he1:Function.update (Function.update base (aux .scale) (D.unary (2*n)++[]))
      (divStack .quotient) []=data base (2*n) 0:=by rw [List.append_nil];rfl
  dsimp only [D.unary] at he0 he1
  rw [he0,he1] at h1
  have h:=join h0 h1
  have ht:(3*n+1)+(2*(2*n)+1)=7*n+2:=by omega
  rw [ht] at h
  exact h
/-- Exact physically executed clock for a bounded number of fixed doubling phases. -/
def runTime (n rounds : Nat) : Nat :=7*n*(2^rounds-1)+2*rounds
/-- Exact recurrence of the actual source clocks, including all EOF reads. -/
theorem runTime_step (n r : Nat) :runTime n (r+1)=(7*n+2)+runTime (2*n) r :=by
  have hp:1≤2^r:=Nat.one_le_two_pow
  have hs:2^r-1+1=2^r:=Nat.sub_add_cancel hp
  have hp':1≤2^(r+1):=Nat.one_le_two_pow
  have hs':2^(r+1)-1+1=2^(r+1):=Nat.sub_add_cancel hp'
  unfold runTime
  rw [pow_succ] at hs' ⊢
  have he0:=congrArg (fun x:Nat=>14*n*x) hs
  have he1:=congrArg (fun x:Nat=>7*n*x) hs'
  nlinarith
/-- Static bounded round index; no input counter is put in a program label. -/
def index (r : Nat) (_hr : r≤20) : Fin 21 :=⟨20-r,by omega⟩
/-- The full twenty-round source scans and writes every acquired scale marker. -/
theorem rounds (base : Stack→List Bool) (r : Nat) (hr : r≤20) (n : Nat) :
    Runs program (runTime n r) (.double (index r hr)) (data base n 0)
      (.double 20) (data base (2^r*n) 0) :=by
  induction r generalizing n with
  | zero=>
    have hi:index 0 hr=(20:Fin 21):=by apply Fin.ext;rfl
    rw [hi]
    simpa only [runTime,pow_zero,Nat.sub_self,Nat.mul_zero,Nat.zero_add,Nat.one_mul] using runs_refl program (.double 20) (data base n 0)
  | succ r ih=>
    let p:Fin 20:=⟨20-(r+1),by omega⟩
    have hp:phase p=.double (index (r+1) hr):=by apply congrArg Label.double;apply Fin.ext;rfl
    have hn:Label.double ⟨p.val+1,by omega⟩=.double (index r (by omega)):=by
      apply congrArg Label.double
      apply Fin.ext
      dsimp [p,index]
      omega
    have h0:=double_run p base n
    rw [hp,hn] at h0
    have h1:=ih (by omega) (2*n)
    have h:=join h0 h1
    have ht:(7*n+2)+runTime (2*n) r=runTime n (r+1):=(runTime_step n r).symm
    have hv:2^r*(2*n)=2^(r+1)*n:=by rw [pow_succ,Nat.mul_assoc]
    rw [ht,hv] at h
    exact h
/-- Fully paid linear original-width envelope for the fixed twenty rounds. -/
theorem twenty_time (n : Nat) :runTime n 20≤8000000*(n+1) :=by norm_num [runTime];omega
end RiemannGaussian.SemiprimeD1StackRootScaleLeafDoubling
