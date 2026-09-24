/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldFiniteData00
/-!
# Kernel-checked Rosser prime-count cells: batch 2 of eight

The literal lists are proved complete by primality checks on every input
integer. Every logarithmic margin is reduced in the kernel. Small proof
boundaries retain completed work and keep cold-build memory bounded.
-/

set_option Elab.async false
namespace RiemannGaussian.RosserSchoenfeldFiniteBounds
open Real RosserSchoenfeldComparison
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

private theorem block_017 : primeBlock 163 7 = [163, 167] := by
  change List.filter (fun p => decide (Nat.Prime p)) [163, 164, 165, 166, 167, 168, 169] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_169 : Nat.primeCounting 169 = 39 := by
  exact primeCounting_step_of_block (by decide) count_162 block_017 (by decide)
private theorem checked_017 : check 162 169 37 39 = true := by decide +kernel
private theorem cell_017 {x : ℝ} (hx : x ∈ Set.Icc (162 : ℝ) 169) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_162.symm count_169.symm checked_017 hx


private theorem block_018 : primeBlock 170 11 = [173, 179] := by
  change List.filter (fun p => decide (Nat.Prime p)) [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_180 : Nat.primeCounting 180 = 41 := by
  exact primeCounting_step_of_block (by decide) count_169 block_018 (by decide)
private theorem checked_018 : check 169 180 39 41 = true := by decide +kernel
private theorem cell_018 {x : ℝ} (hx : x ∈ Set.Icc (169 : ℝ) 180) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_169.symm count_180.symm checked_018 hx


private theorem block_019 : primeBlock 181 12 = [181, 191] := by
  change List.filter (fun p => decide (Nat.Prime p)) [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_192 : Nat.primeCounting 192 = 43 := by
  exact primeCounting_step_of_block (by decide) count_180 block_019 (by decide)
private theorem checked_019 : check 180 192 41 43 = true := by decide +kernel
private theorem cell_019 {x : ℝ} (hx : x ∈ Set.Icc (180 : ℝ) 192) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_180.symm count_192.symm checked_019 hx


private theorem block_020 : primeBlock 193 12 = [193, 197, 199] := by
  change List.filter (fun p => decide (Nat.Prime p)) [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_204 : Nat.primeCounting 204 = 46 := by
  exact primeCounting_step_of_block (by decide) count_192 block_020 (by decide)
private theorem checked_020 : check 192 204 43 46 = true := by decide +kernel
private theorem cell_020 {x : ℝ} (hx : x ∈ Set.Icc (192 : ℝ) 204) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_192.symm count_204.symm checked_020 hx


private theorem block_021 : primeBlock 205 17 = [211] := by
  change List.filter (fun p => decide (Nat.Prime p)) [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_221 : Nat.primeCounting 221 = 47 := by
  exact primeCounting_step_of_block (by decide) count_204 block_021 (by decide)
private theorem checked_021 : check 204 221 46 47 = true := by decide +kernel
private theorem cell_021 {x : ℝ} (hx : x ∈ Set.Icc (204 : ℝ) 221) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_204.symm count_221.symm checked_021 hx


private theorem block_022 : primeBlock 222 9 = [223, 227, 229] := by
  change List.filter (fun p => decide (Nat.Prime p)) [222, 223, 224, 225, 226, 227, 228, 229, 230] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_230 : Nat.primeCounting 230 = 50 := by
  exact primeCounting_step_of_block (by decide) count_221 block_022 (by decide)
private theorem checked_022 : check 221 230 47 50 = true := by decide +kernel
private theorem cell_022 {x : ℝ} (hx : x ∈ Set.Icc (221 : ℝ) 230) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_221.symm count_230.symm checked_022 hx


private theorem block_023 : primeBlock 231 16 = [233, 239, 241] := by
  change List.filter (fun p => decide (Nat.Prime p)) [231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_246 : Nat.primeCounting 246 = 53 := by
  exact primeCounting_step_of_block (by decide) count_230 block_023 (by decide)
private theorem checked_023 : check 230 246 50 53 = true := by decide +kernel
private theorem cell_023 {x : ℝ} (hx : x ∈ Set.Icc (230 : ℝ) 246) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_230.symm count_246.symm checked_023 hx


private theorem block_024 : primeBlock 247 17 = [251, 257, 263] := by
  change List.filter (fun p => decide (Nat.Prime p)) [247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_263 : Nat.primeCounting 263 = 56 := by
  exact primeCounting_step_of_block (by decide) count_246 block_024 (by decide)
private theorem checked_024 : check 246 263 53 56 = true := by decide +kernel
private theorem cell_024 {x : ℝ} (hx : x ∈ Set.Icc (246 : ℝ) 263) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_246.symm count_263.symm checked_024 hx


private theorem block_025 : primeBlock 264 17 = [269, 271, 277] := by
  change List.filter (fun p => decide (Nat.Prime p)) [264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_280 : Nat.primeCounting 280 = 59 := by
  exact primeCounting_step_of_block (by decide) count_263 block_025 (by decide)
private theorem checked_025 : check 263 280 56 59 = true := by decide +kernel
private theorem cell_025 {x : ℝ} (hx : x ∈ Set.Icc (263 : ℝ) 280) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_263.symm count_280.symm checked_025 hx


private theorem block_026 : primeBlock 281 20 = [281, 283, 293] := by
  change List.filter (fun p => decide (Nat.Prime p)) [281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_300 : Nat.primeCounting 300 = 62 := by
  exact primeCounting_step_of_block (by decide) count_280 block_026 (by decide)
private theorem checked_026 : check 280 300 59 62 = true := by decide +kernel
private theorem cell_026 {x : ℝ} (hx : x ∈ Set.Icc (280 : ℝ) 300) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_280.symm count_300.symm checked_026 hx


private theorem block_027 : primeBlock 301 16 = [307, 311, 313] := by
  change List.filter (fun p => decide (Nat.Prime p)) [301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_316 : Nat.primeCounting 316 = 65 := by
  exact primeCounting_step_of_block (by decide) count_300 block_027 (by decide)
private theorem checked_027 : check 300 316 62 65 = true := by decide +kernel
private theorem cell_027 {x : ℝ} (hx : x ∈ Set.Icc (300 : ℝ) 316) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_300.symm count_316.symm checked_027 hx


private theorem block_028 : primeBlock 317 25 = [317, 331, 337] := by
  change List.filter (fun p => decide (Nat.Prime p)) [317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_341 : Nat.primeCounting 341 = 68 := by
  exact primeCounting_step_of_block (by decide) count_316 block_028 (by decide)
private theorem checked_028 : check 316 341 65 68 = true := by decide +kernel
private theorem cell_028 {x : ℝ} (hx : x ∈ Set.Icc (316 : ℝ) 341) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_316.symm count_341.symm checked_028 hx


private theorem block_029 : primeBlock 342 21 = [347, 349, 353, 359] := by
  change List.filter (fun p => decide (Nat.Prime p)) [342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_362 : Nat.primeCounting 362 = 72 := by
  exact primeCounting_step_of_block (by decide) count_341 block_029 (by decide)
private theorem checked_029 : check 341 362 68 72 = true := by decide +kernel
private theorem cell_029 {x : ℝ} (hx : x ∈ Set.Icc (341 : ℝ) 362) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_341.symm count_362.symm checked_029 hx


private theorem block_030 : primeBlock 363 26 = [367, 373, 379, 383] := by
  change List.filter (fun p => decide (Nat.Prime p)) [363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_388 : Nat.primeCounting 388 = 76 := by
  exact primeCounting_step_of_block (by decide) count_362 block_030 (by decide)
private theorem checked_030 : check 362 388 72 76 = true := by decide +kernel
private theorem cell_030 {x : ℝ} (hx : x ∈ Set.Icc (362 : ℝ) 388) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_362.symm count_388.symm checked_030 hx


private theorem block_031 : primeBlock 389 27 = [389, 397, 401, 409] := by
  change List.filter (fun p => decide (Nat.Prime p)) [389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_415 : Nat.primeCounting 415 = 80 := by
  exact primeCounting_step_of_block (by decide) count_388 block_031 (by decide)
private theorem checked_031 : check 388 415 76 80 = true := by decide +kernel
private theorem cell_031 {x : ℝ} (hx : x ∈ Set.Icc (388 : ℝ) 415) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_388.symm count_415.symm checked_031 hx


private theorem block_032 : primeBlock 416 24 = [419, 421, 431, 433, 439] := by
  change List.filter (fun p => decide (Nat.Prime p)) [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_439 : Nat.primeCounting 439 = 85 := by
  exact primeCounting_step_of_block (by decide) count_415 block_032 (by decide)
private theorem checked_032 : check 415 439 80 85 = true := by decide +kernel
private theorem cell_032 {x : ℝ} (hx : x ∈ Set.Icc (415 : ℝ) 439) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_415.symm count_439.symm checked_032 hx


private theorem block_033 : primeBlock 440 23 = [443, 449, 457, 461] := by
  change List.filter (fun p => decide (Nat.Prime p)) [440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_462 : Nat.primeCounting 462 = 89 := by
  exact primeCounting_step_of_block (by decide) count_439 block_033 (by decide)
private theorem checked_033 : check 439 462 85 89 = true := by decide +kernel
private theorem cell_033 {x : ℝ} (hx : x ∈ Set.Icc (439 : ℝ) 462) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_439.symm count_462.symm checked_033 hx


private theorem range_017_019 :
    ∀ x ∈ Set.Icc (162 : ℝ) 180,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_017 hx) (fun _ hx => cell_018 hx)

private theorem range_019_021 :
    ∀ x ∈ Set.Icc (180 : ℝ) 204,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_019 hx) (fun _ hx => cell_020 hx)

private theorem range_017_021 :
    ∀ x ∈ Set.Icc (162 : ℝ) 204,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_017_019 range_019_021

private theorem range_021_023 :
    ∀ x ∈ Set.Icc (204 : ℝ) 230,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_021 hx) (fun _ hx => cell_022 hx)

private theorem range_023_025 :
    ∀ x ∈ Set.Icc (230 : ℝ) 263,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_023 hx) (fun _ hx => cell_024 hx)

private theorem range_021_025 :
    ∀ x ∈ Set.Icc (204 : ℝ) 263,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_021_023 range_023_025

private theorem range_017_025 :
    ∀ x ∈ Set.Icc (162 : ℝ) 263,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_017_021 range_021_025

private theorem range_025_027 :
    ∀ x ∈ Set.Icc (263 : ℝ) 300,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_025 hx) (fun _ hx => cell_026 hx)

private theorem range_027_029 :
    ∀ x ∈ Set.Icc (300 : ℝ) 341,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_027 hx) (fun _ hx => cell_028 hx)

private theorem range_025_029 :
    ∀ x ∈ Set.Icc (263 : ℝ) 341,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_025_027 range_027_029

private theorem range_029_031 :
    ∀ x ∈ Set.Icc (341 : ℝ) 388,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_029 hx) (fun _ hx => cell_030 hx)

private theorem range_032_034 :
    ∀ x ∈ Set.Icc (415 : ℝ) 462,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_032 hx) (fun _ hx => cell_033 hx)

private theorem range_031_034 :
    ∀ x ∈ Set.Icc (388 : ℝ) 462,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_031 hx) range_032_034

private theorem range_029_034 :
    ∀ x ∈ Set.Icc (341 : ℝ) 462,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_029_031 range_031_034

private theorem range_025_034 :
    ∀ x ∈ Set.Icc (263 : ℝ) 462,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_025_029 range_029_034

private theorem range_017_034 :
    ∀ x ∈ Set.Icc (162 : ℝ) 462,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_017_025 range_025_034

/-- The original strict count bounds throughout this complete batch of real cells. -/
theorem bounds_chunk01 :
    ∀ x ∈ Set.Icc (162 : ℝ) 462,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  range_017_034
private def catalog169 : List ℕ := catalog162 ++ [163, 167]
private theorem catalog_complete_169 : primeBlock 0 170 = catalog169 :=
  primeBlock_append_of_eq (by decide) catalog_complete_162 block_017 rfl

private def catalog180 : List ℕ := catalog169 ++ [173, 179]
private theorem catalog_complete_180 : primeBlock 0 181 = catalog180 :=
  primeBlock_append_of_eq (by decide) catalog_complete_169 block_018 rfl

private def catalog192 : List ℕ := catalog180 ++ [181, 191]
private theorem catalog_complete_192 : primeBlock 0 193 = catalog192 :=
  primeBlock_append_of_eq (by decide) catalog_complete_180 block_019 rfl

private def catalog204 : List ℕ := catalog192 ++ [193, 197, 199]
private theorem catalog_complete_204 : primeBlock 0 205 = catalog204 :=
  primeBlock_append_of_eq (by decide) catalog_complete_192 block_020 rfl

private def catalog221 : List ℕ := catalog204 ++ [211]
private theorem catalog_complete_221 : primeBlock 0 222 = catalog221 :=
  primeBlock_append_of_eq (by decide) catalog_complete_204 block_021 rfl

private def catalog230 : List ℕ := catalog221 ++ [223, 227, 229]
private theorem catalog_complete_230 : primeBlock 0 231 = catalog230 :=
  primeBlock_append_of_eq (by decide) catalog_complete_221 block_022 rfl

private def catalog246 : List ℕ := catalog230 ++ [233, 239, 241]
private theorem catalog_complete_246 : primeBlock 0 247 = catalog246 :=
  primeBlock_append_of_eq (by decide) catalog_complete_230 block_023 rfl

private def catalog263 : List ℕ := catalog246 ++ [251, 257, 263]
private theorem catalog_complete_263 : primeBlock 0 264 = catalog263 :=
  primeBlock_append_of_eq (by decide) catalog_complete_246 block_024 rfl

private def catalog280 : List ℕ := catalog263 ++ [269, 271, 277]
private theorem catalog_complete_280 : primeBlock 0 281 = catalog280 :=
  primeBlock_append_of_eq (by decide) catalog_complete_263 block_025 rfl

private def catalog300 : List ℕ := catalog280 ++ [281, 283, 293]
private theorem catalog_complete_300 : primeBlock 0 301 = catalog300 :=
  primeBlock_append_of_eq (by decide) catalog_complete_280 block_026 rfl

private def catalog316 : List ℕ := catalog300 ++ [307, 311, 313]
private theorem catalog_complete_316 : primeBlock 0 317 = catalog316 :=
  primeBlock_append_of_eq (by decide) catalog_complete_300 block_027 rfl

private def catalog341 : List ℕ := catalog316 ++ [317, 331, 337]
private theorem catalog_complete_341 : primeBlock 0 342 = catalog341 :=
  primeBlock_append_of_eq (by decide) catalog_complete_316 block_028 rfl

private def catalog362 : List ℕ := catalog341 ++ [347, 349, 353, 359]
private theorem catalog_complete_362 : primeBlock 0 363 = catalog362 :=
  primeBlock_append_of_eq (by decide) catalog_complete_341 block_029 rfl

private def catalog388 : List ℕ := catalog362 ++ [367, 373, 379, 383]
private theorem catalog_complete_388 : primeBlock 0 389 = catalog388 :=
  primeBlock_append_of_eq (by decide) catalog_complete_362 block_030 rfl

private def catalog415 : List ℕ := catalog388 ++ [389, 397, 401, 409]
private theorem catalog_complete_415 : primeBlock 0 416 = catalog415 :=
  primeBlock_append_of_eq (by decide) catalog_complete_388 block_031 rfl

private def catalog439 : List ℕ := catalog415 ++ [419, 421, 431, 433, 439]
private theorem catalog_complete_439 : primeBlock 0 440 = catalog439 :=
  primeBlock_append_of_eq (by decide) catalog_complete_415 block_032 rfl

/-- The exact complete prime catalog through this batch endpoint. -/
def catalog462 : List ℕ := catalog439 ++ [443, 449, 457, 461]
/-- This catalog contains every prime through its endpoint, exactly once. -/
theorem catalog_complete_462 : primeBlock 0 463 = catalog462 :=
  primeBlock_append_of_eq (by decide) catalog_complete_439 block_033 rfl

end RiemannGaussian.RosserSchoenfeldFiniteBounds
