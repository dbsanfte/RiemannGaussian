/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldFiniteCheck
/-!
# Kernel-checked Rosser prime-count cells: batch 1 of eight

The literal lists are proved complete by primality checks on every input
integer. Every logarithmic margin is reduced in the kernel. Small proof
boundaries retain completed work and keep cold-build memory bounded.
-/

set_option Elab.async false
namespace RiemannGaussian.RosserSchoenfeldFiniteBounds
open Real RosserSchoenfeldComparison
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- The exact count of all primes through this checked endpoint. -/
theorem count_67 : Nat.primeCounting 67 = 19 := by
  simp only [Nat.primeCounting, Nat.primeCounting', Nat.count, List.countP_eq_length_filter]
  change (List.filter (fun p => decide (Nat.Prime p)) [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67]).length = 19
  norm_num [List.filter_cons]


private theorem block_000 : primeBlock 68 3 = [] := by
  change List.filter (fun p => decide (Nat.Prime p)) [68, 69, 70] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_70 : Nat.primeCounting 70 = 19 := by
  exact primeCounting_step_of_block (by decide) count_67 block_000 (by decide)
private theorem checked_000 : check 67 70 19 19 = true := by decide +kernel
private theorem cell_000 {x : ℝ} (hx : x ∈ Set.Icc (67 : ℝ) 70) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_67.symm count_70.symm checked_000 hx


private theorem block_001 : primeBlock 71 1 = [71] := by
  change List.filter (fun p => decide (Nat.Prime p)) [71] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_71 : Nat.primeCounting 71 = 20 := by
  exact primeCounting_step_of_block (by decide) count_70 block_001 (by decide)
private theorem checked_001 : check 70 71 19 20 = true := by decide +kernel
private theorem cell_001 {x : ℝ} (hx : x ∈ Set.Icc (70 : ℝ) 71) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_70.symm count_71.symm checked_001 hx


private theorem block_002 : primeBlock 72 4 = [73] := by
  change List.filter (fun p => decide (Nat.Prime p)) [72, 73, 74, 75] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_75 : Nat.primeCounting 75 = 21 := by
  exact primeCounting_step_of_block (by decide) count_71 block_002 (by decide)
private theorem checked_002 : check 71 75 20 21 = true := by decide +kernel
private theorem cell_002 {x : ℝ} (hx : x ∈ Set.Icc (71 : ℝ) 75) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_71.symm count_75.symm checked_002 hx


private theorem block_003 : primeBlock 76 5 = [79] := by
  change List.filter (fun p => decide (Nat.Prime p)) [76, 77, 78, 79, 80] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_80 : Nat.primeCounting 80 = 22 := by
  exact primeCounting_step_of_block (by decide) count_75 block_003 (by decide)
private theorem checked_003 : check 75 80 21 22 = true := by decide +kernel
private theorem cell_003 {x : ℝ} (hx : x ∈ Set.Icc (75 : ℝ) 80) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_75.symm count_80.symm checked_003 hx


private theorem block_004 : primeBlock 81 5 = [83] := by
  change List.filter (fun p => decide (Nat.Prime p)) [81, 82, 83, 84, 85] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_85 : Nat.primeCounting 85 = 23 := by
  exact primeCounting_step_of_block (by decide) count_80 block_004 (by decide)
private theorem checked_004 : check 80 85 22 23 = true := by decide +kernel
private theorem cell_004 {x : ℝ} (hx : x ∈ Set.Icc (80 : ℝ) 85) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_80.symm count_85.symm checked_004 hx


private theorem block_005 : primeBlock 86 5 = [89] := by
  change List.filter (fun p => decide (Nat.Prime p)) [86, 87, 88, 89, 90] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_90 : Nat.primeCounting 90 = 24 := by
  exact primeCounting_step_of_block (by decide) count_85 block_005 (by decide)
private theorem checked_005 : check 85 90 23 24 = true := by decide +kernel
private theorem cell_005 {x : ℝ} (hx : x ∈ Set.Icc (85 : ℝ) 90) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_85.symm count_90.symm checked_005 hx


private theorem block_006 : primeBlock 91 5 = [] := by
  change List.filter (fun p => decide (Nat.Prime p)) [91, 92, 93, 94, 95] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_95 : Nat.primeCounting 95 = 24 := by
  exact primeCounting_step_of_block (by decide) count_90 block_006 (by decide)
private theorem checked_006 : check 90 95 24 24 = true := by decide +kernel
private theorem cell_006 {x : ℝ} (hx : x ∈ Set.Icc (90 : ℝ) 95) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_90.symm count_95.symm checked_006 hx


private theorem block_007 : primeBlock 96 2 = [97] := by
  change List.filter (fun p => decide (Nat.Prime p)) [96, 97] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_97 : Nat.primeCounting 97 = 25 := by
  exact primeCounting_step_of_block (by decide) count_95 block_007 (by decide)
private theorem checked_007 : check 95 97 24 25 = true := by decide +kernel
private theorem cell_007 {x : ℝ} (hx : x ∈ Set.Icc (95 : ℝ) 97) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_95.symm count_97.symm checked_007 hx


private theorem block_008 : primeBlock 98 4 = [101] := by
  change List.filter (fun p => decide (Nat.Prime p)) [98, 99, 100, 101] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_101 : Nat.primeCounting 101 = 26 := by
  exact primeCounting_step_of_block (by decide) count_97 block_008 (by decide)
private theorem checked_008 : check 97 101 25 26 = true := by decide +kernel
private theorem cell_008 {x : ℝ} (hx : x ∈ Set.Icc (97 : ℝ) 101) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_97.symm count_101.symm checked_008 hx


private theorem block_009 : primeBlock 102 5 = [103] := by
  change List.filter (fun p => decide (Nat.Prime p)) [102, 103, 104, 105, 106] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_106 : Nat.primeCounting 106 = 27 := by
  exact primeCounting_step_of_block (by decide) count_101 block_009 (by decide)
private theorem checked_009 : check 101 106 26 27 = true := by decide +kernel
private theorem cell_009 {x : ℝ} (hx : x ∈ Set.Icc (101 : ℝ) 106) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_101.symm count_106.symm checked_009 hx


private theorem block_010 : primeBlock 107 6 = [107, 109] := by
  change List.filter (fun p => decide (Nat.Prime p)) [107, 108, 109, 110, 111, 112] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_112 : Nat.primeCounting 112 = 29 := by
  exact primeCounting_step_of_block (by decide) count_106 block_010 (by decide)
private theorem checked_010 : check 106 112 27 29 = true := by decide +kernel
private theorem cell_010 {x : ℝ} (hx : x ∈ Set.Icc (106 : ℝ) 112) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_106.symm count_112.symm checked_010 hx


private theorem block_011 : primeBlock 113 10 = [113] := by
  change List.filter (fun p => decide (Nat.Prime p)) [113, 114, 115, 116, 117, 118, 119, 120, 121, 122] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_122 : Nat.primeCounting 122 = 30 := by
  exact primeCounting_step_of_block (by decide) count_112 block_011 (by decide)
private theorem checked_011 : check 112 122 29 30 = true := by decide +kernel
private theorem cell_011 {x : ℝ} (hx : x ∈ Set.Icc (112 : ℝ) 122) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_112.symm count_122.symm checked_011 hx


private theorem block_012 : primeBlock 123 7 = [127] := by
  change List.filter (fun p => decide (Nat.Prime p)) [123, 124, 125, 126, 127, 128, 129] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_129 : Nat.primeCounting 129 = 31 := by
  exact primeCounting_step_of_block (by decide) count_122 block_012 (by decide)
private theorem checked_012 : check 122 129 30 31 = true := by decide +kernel
private theorem cell_012 {x : ℝ} (hx : x ∈ Set.Icc (122 : ℝ) 129) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_122.symm count_129.symm checked_012 hx


private theorem block_013 : primeBlock 130 6 = [131] := by
  change List.filter (fun p => decide (Nat.Prime p)) [130, 131, 132, 133, 134, 135] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_135 : Nat.primeCounting 135 = 32 := by
  exact primeCounting_step_of_block (by decide) count_129 block_013 (by decide)
private theorem checked_013 : check 129 135 31 32 = true := by decide +kernel
private theorem cell_013 {x : ℝ} (hx : x ∈ Set.Icc (129 : ℝ) 135) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_129.symm count_135.symm checked_013 hx


private theorem block_014 : primeBlock 136 5 = [137, 139] := by
  change List.filter (fun p => decide (Nat.Prime p)) [136, 137, 138, 139, 140] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_140 : Nat.primeCounting 140 = 34 := by
  exact primeCounting_step_of_block (by decide) count_135 block_014 (by decide)
private theorem checked_014 : check 135 140 32 34 = true := by decide +kernel
private theorem cell_014 {x : ℝ} (hx : x ∈ Set.Icc (135 : ℝ) 140) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_135.symm count_140.symm checked_014 hx


private theorem block_015 : primeBlock 141 11 = [149, 151] := by
  change List.filter (fun p => decide (Nat.Prime p)) [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_151 : Nat.primeCounting 151 = 36 := by
  exact primeCounting_step_of_block (by decide) count_140 block_015 (by decide)
private theorem checked_015 : check 140 151 34 36 = true := by decide +kernel
private theorem cell_015 {x : ℝ} (hx : x ∈ Set.Icc (140 : ℝ) 151) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_140.symm count_151.symm checked_015 hx


private theorem block_016 : primeBlock 152 11 = [157] := by
  change List.filter (fun p => decide (Nat.Prime p)) [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_162 : Nat.primeCounting 162 = 37 := by
  exact primeCounting_step_of_block (by decide) count_151 block_016 (by decide)
private theorem checked_016 : check 151 162 36 37 = true := by decide +kernel
private theorem cell_016 {x : ℝ} (hx : x ∈ Set.Icc (151 : ℝ) 162) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_151.symm count_162.symm checked_016 hx


private theorem range_000_002 :
    ∀ x ∈ Set.Icc (67 : ℝ) 71,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_000 hx) (fun _ hx => cell_001 hx)

private theorem range_002_004 :
    ∀ x ∈ Set.Icc (71 : ℝ) 80,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_002 hx) (fun _ hx => cell_003 hx)

private theorem range_000_004 :
    ∀ x ∈ Set.Icc (67 : ℝ) 80,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_000_002 range_002_004

private theorem range_004_006 :
    ∀ x ∈ Set.Icc (80 : ℝ) 90,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_004 hx) (fun _ hx => cell_005 hx)

private theorem range_006_008 :
    ∀ x ∈ Set.Icc (90 : ℝ) 97,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_006 hx) (fun _ hx => cell_007 hx)

private theorem range_004_008 :
    ∀ x ∈ Set.Icc (80 : ℝ) 97,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_004_006 range_006_008

private theorem range_000_008 :
    ∀ x ∈ Set.Icc (67 : ℝ) 97,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_000_004 range_004_008

private theorem range_008_010 :
    ∀ x ∈ Set.Icc (97 : ℝ) 106,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_008 hx) (fun _ hx => cell_009 hx)

private theorem range_010_012 :
    ∀ x ∈ Set.Icc (106 : ℝ) 122,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_010 hx) (fun _ hx => cell_011 hx)

private theorem range_008_012 :
    ∀ x ∈ Set.Icc (97 : ℝ) 122,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_008_010 range_010_012

private theorem range_012_014 :
    ∀ x ∈ Set.Icc (122 : ℝ) 135,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_012 hx) (fun _ hx => cell_013 hx)

private theorem range_015_017 :
    ∀ x ∈ Set.Icc (140 : ℝ) 162,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_015 hx) (fun _ hx => cell_016 hx)

private theorem range_014_017 :
    ∀ x ∈ Set.Icc (135 : ℝ) 162,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_014 hx) range_015_017

private theorem range_012_017 :
    ∀ x ∈ Set.Icc (122 : ℝ) 162,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_012_014 range_014_017

private theorem range_008_017 :
    ∀ x ∈ Set.Icc (97 : ℝ) 162,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_008_012 range_012_017

private theorem range_000_017 :
    ∀ x ∈ Set.Icc (67 : ℝ) 162,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_000_008 range_008_017

/-- The original strict count bounds throughout this complete batch of real cells. -/
theorem bounds_chunk00 :
    ∀ x ∈ Set.Icc (67 : ℝ) 162,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  range_000_017
private def catalog67 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67]
private theorem catalog_complete_67 : primeBlock 0 68 = catalog67 := by
  change List.filter (fun p => decide (Nat.Prime p)) [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67] = _
  norm_num [List.filter_cons, catalog67]

private def catalog70 : List ℕ := catalog67 ++ []
private theorem catalog_complete_70 : primeBlock 0 71 = catalog70 :=
  primeBlock_append_of_eq (by decide) catalog_complete_67 block_000 rfl

private def catalog71 : List ℕ := catalog70 ++ [71]
private theorem catalog_complete_71 : primeBlock 0 72 = catalog71 :=
  primeBlock_append_of_eq (by decide) catalog_complete_70 block_001 rfl

private def catalog75 : List ℕ := catalog71 ++ [73]
private theorem catalog_complete_75 : primeBlock 0 76 = catalog75 :=
  primeBlock_append_of_eq (by decide) catalog_complete_71 block_002 rfl

private def catalog80 : List ℕ := catalog75 ++ [79]
private theorem catalog_complete_80 : primeBlock 0 81 = catalog80 :=
  primeBlock_append_of_eq (by decide) catalog_complete_75 block_003 rfl

private def catalog85 : List ℕ := catalog80 ++ [83]
private theorem catalog_complete_85 : primeBlock 0 86 = catalog85 :=
  primeBlock_append_of_eq (by decide) catalog_complete_80 block_004 rfl

private def catalog90 : List ℕ := catalog85 ++ [89]
private theorem catalog_complete_90 : primeBlock 0 91 = catalog90 :=
  primeBlock_append_of_eq (by decide) catalog_complete_85 block_005 rfl

private def catalog95 : List ℕ := catalog90 ++ []
private theorem catalog_complete_95 : primeBlock 0 96 = catalog95 :=
  primeBlock_append_of_eq (by decide) catalog_complete_90 block_006 rfl

private def catalog97 : List ℕ := catalog95 ++ [97]
private theorem catalog_complete_97 : primeBlock 0 98 = catalog97 :=
  primeBlock_append_of_eq (by decide) catalog_complete_95 block_007 rfl

private def catalog101 : List ℕ := catalog97 ++ [101]
private theorem catalog_complete_101 : primeBlock 0 102 = catalog101 :=
  primeBlock_append_of_eq (by decide) catalog_complete_97 block_008 rfl

private def catalog106 : List ℕ := catalog101 ++ [103]
private theorem catalog_complete_106 : primeBlock 0 107 = catalog106 :=
  primeBlock_append_of_eq (by decide) catalog_complete_101 block_009 rfl

private def catalog112 : List ℕ := catalog106 ++ [107, 109]
private theorem catalog_complete_112 : primeBlock 0 113 = catalog112 :=
  primeBlock_append_of_eq (by decide) catalog_complete_106 block_010 rfl

private def catalog122 : List ℕ := catalog112 ++ [113]
private theorem catalog_complete_122 : primeBlock 0 123 = catalog122 :=
  primeBlock_append_of_eq (by decide) catalog_complete_112 block_011 rfl

private def catalog129 : List ℕ := catalog122 ++ [127]
private theorem catalog_complete_129 : primeBlock 0 130 = catalog129 :=
  primeBlock_append_of_eq (by decide) catalog_complete_122 block_012 rfl

private def catalog135 : List ℕ := catalog129 ++ [131]
private theorem catalog_complete_135 : primeBlock 0 136 = catalog135 :=
  primeBlock_append_of_eq (by decide) catalog_complete_129 block_013 rfl

private def catalog140 : List ℕ := catalog135 ++ [137, 139]
private theorem catalog_complete_140 : primeBlock 0 141 = catalog140 :=
  primeBlock_append_of_eq (by decide) catalog_complete_135 block_014 rfl

private def catalog151 : List ℕ := catalog140 ++ [149, 151]
private theorem catalog_complete_151 : primeBlock 0 152 = catalog151 :=
  primeBlock_append_of_eq (by decide) catalog_complete_140 block_015 rfl

/-- The exact complete prime catalog through this batch endpoint. -/
def catalog162 : List ℕ := catalog151 ++ [157]
/-- This catalog contains every prime through its endpoint, exactly once. -/
theorem catalog_complete_162 : primeBlock 0 163 = catalog162 :=
  primeBlock_append_of_eq (by decide) catalog_complete_151 block_016 rfl

end RiemannGaussian.RosserSchoenfeldFiniteBounds
