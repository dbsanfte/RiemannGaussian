/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseGeometrySubtract
/-! # Real low-bit scan, paid padding cleanup, and zero-order reset -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1StackPhaseGeometryValuation
open SemiprimeD1StackPhaseGeometry SemiprimeD1StackPhaseGeometryArithmetic
open SemiprimeD1StackPhaseGeometryPrimitives SemiprimeD1StackProcedureTrace
/-- Exact order/scan fields; original inputs, binary powers and magnitude are retained. -/
def scanData (a t mag sign xs : List Bool) (n : Nat) (zero : List Bool) : Stack→List Bool :=
  data a t [] (powerWord a.length) (powerWord (a.length+1)) sign zero (List.replicate n true) xs [] [] mag
/-- Provisional prefix count contributes only if a real one bit is eventually seen. -/
def scanOrder (xs : List Bool) (n : Nat) : Nat :=if SemiprimeBitArithmetic.bitValue xs=0 then 0 else n+valuation xs
/-- Exact scan result, including the actual singleton zero flag. -/
def scanResult (a t mag sign xs : List Bool) (n : Nat) : Stack→List Bool :=
  scanData a t mag sign [] (scanOrder xs n) [decide (SemiprimeBitArithmetic.bitValue xs=0)]
/-- One actual low zero writes exactly one provisional order marker. -/
theorem false_step (a t mag sign xs : List Bool) (n : Nat) :
    Runs program 2 .scan (scanData a t mag sign (false::xs) n [])
      .scan (scanData a t mag sign xs (n+1) []) :=by
  have h0:Runs program 1 .scan (scanData a t mag sign (false::xs) n [])
      .increment (scanData a t mag sign xs n []):=by
    apply one_base program .scan .increment (.pop (aux .scan) .clearOrder .increment .clearScan) _ _ rfl
    · rfl
    · funext k;rcases k with k|k <;> cases k <;> rfl
  have h1:=push .increment .scan (aux .order) true (scanData a t mag sign xs n []) rfl
  have he:Function.update (scanData a t mag sign xs n []) (aux .order)
      (true::scanData a t mag sign xs n [] (aux .order))=scanData a t mag sign xs (n+1) []:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h1
  exact join h0 h1
/-- EOF physically drains ALL provisional order markers, so padded zero has order0. -/
theorem empty_run (a t mag sign : List Bool) (n : Nat) :
    Runs program (n+3) .scan (scanData a t mag sign [] n [])
      .done (scanData a t mag sign [] 0 [true]) :=by
  have h0:Runs program 1 .scan (scanData a t mag sign [] n [])
      .clearOrder (scanData a t mag sign [] n []):=by
    apply one_base program .scan .clearOrder (.pop (aux .scan) .clearOrder .increment .clearScan) _ _ rfl
    · rfl
    · funext k;rcases k with k|k <;> cases k <;> rfl
  have h1:=SemiprimeD1StackPhysicalLoops.drain program .clearOrder (.saveZero true) (aux .order)
    rfl (scanData a t mag sign [] n []) (List.replicate n true)
  have hi:Function.update (scanData a t mag sign [] n []) (aux .order) (List.replicate n true)=
      scanData a t mag sign [] n []:=Function.update_eq_self _ _
  have ho:Function.update (scanData a t mag sign [] n []) (aux .order) []=
      scanData a t mag sign [] 0 []:=by funext k;rcases k with k|k <;> cases k <;> rfl
  rw [hi,ho,List.length_replicate] at h1
  have h2:=push (.saveZero true) .done (aux .zero) true (scanData a t mag sign [] 0 []) rfl
  have he:Function.update (scanData a t mag sign [] 0 []) (aux .zero)
      (true::scanData a t mag sign [] 0 [] (aux .zero))=scanData a t mag sign [] 0 [true]:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h2
  convert join (join h0 h1) h2 using 1
  omega
/-- After the first actual one, EVERY remaining padding/data cell is physically erased. -/
theorem true_run (a t mag sign xs : List Bool) (n : Nat) :
    Runs program (xs.length+3) .scan (scanData a t mag sign (true::xs) n [])
      .done (scanData a t mag sign [] n [false]) :=by
  have h0:Runs program 1 .scan (scanData a t mag sign (true::xs) n [])
      .clearScan (scanData a t mag sign xs n []):=by
    apply one_base program .scan .clearScan (.pop (aux .scan) .clearOrder .increment .clearScan) _ _ rfl
    · rfl
    · funext k;rcases k with k|k <;> cases k <;> rfl
  have h1:=SemiprimeD1StackPhysicalLoops.drain program .clearScan (.saveZero false) (aux .scan)
    rfl (scanData a t mag sign xs n []) xs
  have hi:Function.update (scanData a t mag sign xs n []) (aux .scan) xs=
      scanData a t mag sign xs n []:=Function.update_eq_self _ _
  have ho:Function.update (scanData a t mag sign xs n []) (aux .scan) []=
      scanData a t mag sign [] n []:=by funext k;rcases k with k|k <;> cases k <;> rfl
  rw [hi,ho] at h1
  have h2:=push (.saveZero false) .done (aux .zero) false (scanData a t mag sign [] n []) rfl
  have he:Function.update (scanData a t mag sign [] n []) (aux .zero)
      (false::scanData a t mag sign [] n [] (aux .zero))=scanData a t mag sign [] n [false]:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h2
  convert join (join h0 h1) h2 using 1
  omega
/-- Whole actual scan is linear in ALL physical input/padding and prior count cells. -/
theorem scan_run (a t mag sign xs : List Bool) (n : Nat) :
    ∃q≤10*(xs.length+1)+2*n,Runs program q .scan (scanData a t mag sign xs n [])
      .done (scanResult a t mag sign xs n) :=by
  induction xs generalizing n with
  | nil=>
    refine ⟨n+3,by simp only [List.length_nil];omega,?_⟩
    exact empty_run a t mag sign n
  | cons b xs ih=>
    cases b with
    | true=>
      refine ⟨xs.length+3,by simp only [List.length_cons];omega,?_⟩
      have hz:SemiprimeBitArithmetic.bitValue (true::xs)≠0:=by
        change 1+2*SemiprimeBitArithmetic.bitValue xs≠0
        omega
      have he:scanResult a t mag sign (true::xs) n=scanData a t mag sign [] n [false]:=by
        simp only [scanResult,scanOrder,hz,ite_false,valuation,Nat.add_zero,decide_false]
      rw [he]
      exact true_run a t mag sign xs n
    | false=>
      obtain ⟨q,hq,hr⟩:=ih (n+1)
      have hh:=join (false_step a t mag sign xs n) hr
      have hz:(SemiprimeBitArithmetic.bitValue (false::xs)=0)↔SemiprimeBitArithmetic.bitValue xs=0:=by
        change (0+2*SemiprimeBitArithmetic.bitValue xs=0)↔_
        omega
      have ho:scanOrder (false::xs) n=scanOrder xs (n+1):=by
        unfold scanOrder
        simp only [hz]
        by_cases h:SemiprimeBitArithmetic.bitValue xs=0
        · simp only [h,ite_true]
        · simp only [h,ite_false,valuation]
          omega
      have he:scanResult a t mag sign (false::xs) n=scanResult a t mag sign xs (n+1):=by
        unfold scanResult
        rw [ho]
        simp only [hz]
      refine ⟨2+q,by simp only [List.length_cons];omega,?_⟩
      rw [he]
      exact hh
end RiemannGaussian.SemiprimeD1StackPhaseGeometryValuation
