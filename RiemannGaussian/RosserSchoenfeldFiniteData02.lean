/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldFiniteData01
/-!
# Kernel-checked Rosser prime-count cells: batch 3 of eight

The literal lists are proved complete by primality checks on every input
integer. Every logarithmic margin is reduced in the kernel. Small proof
boundaries retain completed work and keep cold-build memory bounded.
-/

set_option Elab.async false
namespace RiemannGaussian.RosserSchoenfeldFiniteBounds
open Real RosserSchoenfeldComparison
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

private theorem block_034 : primeBlock 463 24 = [463, 467, 479] := by
  change List.filter (fun p => decide (Nat.Prime p)) [463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_486 : Nat.primeCounting 486 = 92 := by
  exact primeCounting_step_of_block (by decide) count_462 block_034 (by decide)
private theorem checked_034 : check 462 486 89 92 = true := by decide +kernel
private theorem cell_034 {x : ℝ} (hx : x ∈ Set.Icc (462 : ℝ) 486) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_462.symm count_486.symm checked_034 hx


private theorem block_035 : primeBlock 487 22 = [487, 491, 499, 503] := by
  change List.filter (fun p => decide (Nat.Prime p)) [487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_508 : Nat.primeCounting 508 = 96 := by
  exact primeCounting_step_of_block (by decide) count_486 block_035 (by decide)
private theorem checked_035 : check 486 508 92 96 = true := by decide +kernel
private theorem cell_035 {x : ℝ} (hx : x ∈ Set.Icc (486 : ℝ) 508) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_486.symm count_508.symm checked_035 hx


private theorem block_036 : primeBlock 509 32 = [509, 521, 523] := by
  change List.filter (fun p => decide (Nat.Prime p)) [509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_540 : Nat.primeCounting 540 = 99 := by
  exact primeCounting_step_of_block (by decide) count_508 block_036 (by decide)
private theorem checked_036 : check 508 540 96 99 = true := by decide +kernel
private theorem cell_036 {x : ℝ} (hx : x ∈ Set.Icc (508 : ℝ) 540) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_508.symm count_540.symm checked_036 hx


private theorem block_037 : primeBlock 541 33 = [541, 547, 557, 563, 569, 571] := by
  change List.filter (fun p => decide (Nat.Prime p)) [541, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_573 : Nat.primeCounting 573 = 105 := by
  exact primeCounting_step_of_block (by decide) count_540 block_037 (by decide)
private theorem checked_037 : check 540 573 99 105 = true := by decide +kernel
private theorem cell_037 {x : ℝ} (hx : x ∈ Set.Icc (540 : ℝ) 573) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_540.symm count_573.symm checked_037 hx


private theorem block_038 : primeBlock 574 33 = [577, 587, 593, 599, 601] := by
  change List.filter (fun p => decide (Nat.Prime p)) [574, 575, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_606 : Nat.primeCounting 606 = 110 := by
  exact primeCounting_step_of_block (by decide) count_573 block_038 (by decide)
private theorem checked_038 : check 573 606 105 110 = true := by decide +kernel
private theorem cell_038 {x : ℝ} (hx : x ∈ Set.Icc (573 : ℝ) 606) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_573.symm count_606.symm checked_038 hx


private theorem block_039 : primeBlock 607 34 = [607, 613, 617, 619, 631] := by
  change List.filter (fun p => decide (Nat.Prime p)) [607, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639, 640] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_640 : Nat.primeCounting 640 = 115 := by
  exact primeCounting_step_of_block (by decide) count_606 block_039 (by decide)
private theorem checked_039 : check 606 640 110 115 = true := by decide +kernel
private theorem cell_039 {x : ℝ} (hx : x ∈ Set.Icc (606 : ℝ) 640) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_606.symm count_640.symm checked_039 hx


private theorem block_040 : primeBlock 641 30 = [641, 643, 647, 653, 659, 661] := by
  change List.filter (fun p => decide (Nat.Prime p)) [641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_670 : Nat.primeCounting 670 = 121 := by
  exact primeCounting_step_of_block (by decide) count_640 block_040 (by decide)
private theorem checked_040 : check 640 670 115 121 = true := by decide +kernel
private theorem cell_040 {x : ℝ} (hx : x ∈ Set.Icc (640 : ℝ) 670) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_640.symm count_670.symm checked_040 hx


private theorem block_041 : primeBlock 671 30 = [673, 677, 683, 691] := by
  change List.filter (fun p => decide (Nat.Prime p)) [671, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_700 : Nat.primeCounting 700 = 125 := by
  exact primeCounting_step_of_block (by decide) count_670 block_041 (by decide)
private theorem checked_041 : check 670 700 121 125 = true := by decide +kernel
private theorem cell_041 {x : ℝ} (hx : x ∈ Set.Icc (670 : ℝ) 700) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_670.symm count_700.symm checked_041 hx


private theorem block_042 : primeBlock 701 38 = [701, 709, 719, 727, 733] := by
  change List.filter (fun p => decide (Nat.Prime p)) [701, 702, 703, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735, 736, 737, 738] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_738 : Nat.primeCounting 738 = 130 := by
  exact primeCounting_step_of_block (by decide) count_700 block_042 (by decide)
private theorem checked_042 : check 700 738 125 130 = true := by decide +kernel
private theorem cell_042 {x : ℝ} (hx : x ∈ Set.Icc (700 : ℝ) 738) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_700.symm count_738.symm checked_042 hx


private theorem block_043 : primeBlock 739 34 = [739, 743, 751, 757, 761, 769] := by
  change List.filter (fun p => decide (Nat.Prime p)) [739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767, 768, 769, 770, 771, 772] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_772 : Nat.primeCounting 772 = 136 := by
  exact primeCounting_step_of_block (by decide) count_738 block_043 (by decide)
private theorem checked_043 : check 738 772 130 136 = true := by decide +kernel
private theorem cell_043 {x : ℝ} (hx : x ∈ Set.Icc (738 : ℝ) 772) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_738.symm count_772.symm checked_043 hx


private theorem block_044 : primeBlock 773 41 = [773, 787, 797, 809, 811] := by
  change List.filter (fun p => decide (Nat.Prime p)) [773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799, 800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_813 : Nat.primeCounting 813 = 141 := by
  exact primeCounting_step_of_block (by decide) count_772 block_044 (by decide)
private theorem checked_044 : check 772 813 136 141 = true := by decide +kernel
private theorem cell_044 {x : ℝ} (hx : x ∈ Set.Icc (772 : ℝ) 813) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_772.symm count_813.symm checked_044 hx


private theorem block_045 : primeBlock 814 43 = [821, 823, 827, 829, 839, 853] := by
  change List.filter (fun p => decide (Nat.Prime p)) [814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831, 832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855, 856] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_856 : Nat.primeCounting 856 = 147 := by
  exact primeCounting_step_of_block (by decide) count_813 block_045 (by decide)
private theorem checked_045 : check 813 856 141 147 = true := by decide +kernel
private theorem cell_045 {x : ℝ} (hx : x ∈ Set.Icc (813 : ℝ) 856) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_813.symm count_856.symm checked_045 hx


private theorem block_046 : primeBlock 857 30 = [857, 859, 863, 877, 881, 883] := by
  change List.filter (fun p => decide (Nat.Prime p)) [857, 858, 859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_886 : Nat.primeCounting 886 = 153 := by
  exact primeCounting_step_of_block (by decide) count_856 block_046 (by decide)
private theorem checked_046 : check 856 886 147 153 = true := by decide +kernel
private theorem cell_046 {x : ℝ} (hx : x ∈ Set.Icc (856 : ℝ) 886) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_856.symm count_886.symm checked_046 hx


private theorem block_047 : primeBlock 887 46 = [887, 907, 911, 919, 929] := by
  change List.filter (fun p => decide (Nat.Prime p)) [887, 888, 889, 890, 891, 892, 893, 894, 895, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927, 928, 929, 930, 931, 932] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_932 : Nat.primeCounting 932 = 158 := by
  exact primeCounting_step_of_block (by decide) count_886 block_047 (by decide)
private theorem checked_047 : check 886 932 153 158 = true := by decide +kernel
private theorem cell_047 {x : ℝ} (hx : x ∈ Set.Icc (886 : ℝ) 932) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_886.symm count_932.symm checked_047 hx


private theorem block_048 : primeBlock 933 44 = [937, 941, 947, 953, 967, 971] := by
  change List.filter (fun p => decide (Nat.Prime p)) [933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_976 : Nat.primeCounting 976 = 164 := by
  exact primeCounting_step_of_block (by decide) count_932 block_048 (by decide)
private theorem checked_048 : check 932 976 158 164 = true := by decide +kernel
private theorem cell_048 {x : ℝ} (hx : x ∈ Set.Icc (932 : ℝ) 976) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_932.symm count_976.symm checked_048 hx


private theorem block_049 : primeBlock 977 44 = [977, 983, 991, 997, 1009, 1013, 1019] := by
  change List.filter (fun p => decide (Nat.Prime p)) [977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_1020 : Nat.primeCounting 1020 = 171 := by
  exact primeCounting_step_of_block (by decide) count_976 block_049 (by decide)
private theorem checked_049 : check 976 1020 164 171 = true := by decide +kernel
private theorem cell_049 {x : ℝ} (hx : x ∈ Set.Icc (976 : ℝ) 1020) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_976.symm count_1020.symm checked_049 hx


private theorem block_050 : primeBlock 1021 40 = [1021, 1031, 1033, 1039, 1049, 1051] := by
  change List.filter (fun p => decide (Nat.Prime p)) [1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055, 1056, 1057, 1058, 1059, 1060] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_1060 : Nat.primeCounting 1060 = 177 := by
  exact primeCounting_step_of_block (by decide) count_1020 block_050 (by decide)
private theorem checked_050 : check 1020 1060 171 177 = true := by decide +kernel
private theorem cell_050 {x : ℝ} (hx : x ∈ Set.Icc (1020 : ℝ) 1060) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_1020.symm count_1060.symm checked_050 hx


private theorem range_034_036 :
    ∀ x ∈ Set.Icc (462 : ℝ) 508,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_034 hx) (fun _ hx => cell_035 hx)

private theorem range_036_038 :
    ∀ x ∈ Set.Icc (508 : ℝ) 573,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_036 hx) (fun _ hx => cell_037 hx)

private theorem range_034_038 :
    ∀ x ∈ Set.Icc (462 : ℝ) 573,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_034_036 range_036_038

private theorem range_038_040 :
    ∀ x ∈ Set.Icc (573 : ℝ) 640,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_038 hx) (fun _ hx => cell_039 hx)

private theorem range_040_042 :
    ∀ x ∈ Set.Icc (640 : ℝ) 700,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_040 hx) (fun _ hx => cell_041 hx)

private theorem range_038_042 :
    ∀ x ∈ Set.Icc (573 : ℝ) 700,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_038_040 range_040_042

private theorem range_034_042 :
    ∀ x ∈ Set.Icc (462 : ℝ) 700,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_034_038 range_038_042

private theorem range_042_044 :
    ∀ x ∈ Set.Icc (700 : ℝ) 772,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_042 hx) (fun _ hx => cell_043 hx)

private theorem range_044_046 :
    ∀ x ∈ Set.Icc (772 : ℝ) 856,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_044 hx) (fun _ hx => cell_045 hx)

private theorem range_042_046 :
    ∀ x ∈ Set.Icc (700 : ℝ) 856,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_042_044 range_044_046

private theorem range_046_048 :
    ∀ x ∈ Set.Icc (856 : ℝ) 932,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_046 hx) (fun _ hx => cell_047 hx)

private theorem range_049_051 :
    ∀ x ∈ Set.Icc (976 : ℝ) 1060,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_049 hx) (fun _ hx => cell_050 hx)

private theorem range_048_051 :
    ∀ x ∈ Set.Icc (932 : ℝ) 1060,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_048 hx) range_049_051

private theorem range_046_051 :
    ∀ x ∈ Set.Icc (856 : ℝ) 1060,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_046_048 range_048_051

private theorem range_042_051 :
    ∀ x ∈ Set.Icc (700 : ℝ) 1060,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_042_046 range_046_051

private theorem range_034_051 :
    ∀ x ∈ Set.Icc (462 : ℝ) 1060,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_034_042 range_042_051

/-- The original strict count bounds throughout this complete batch of real cells. -/
theorem bounds_chunk02 :
    ∀ x ∈ Set.Icc (462 : ℝ) 1060,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  range_034_051
private def catalog486 : List ℕ := catalog462 ++ [463, 467, 479]
private theorem catalog_complete_486 : primeBlock 0 487 = catalog486 :=
  primeBlock_append_of_eq (by decide) catalog_complete_462 block_034 rfl

private def catalog508 : List ℕ := catalog486 ++ [487, 491, 499, 503]
private theorem catalog_complete_508 : primeBlock 0 509 = catalog508 :=
  primeBlock_append_of_eq (by decide) catalog_complete_486 block_035 rfl

private def catalog540 : List ℕ := catalog508 ++ [509, 521, 523]
private theorem catalog_complete_540 : primeBlock 0 541 = catalog540 :=
  primeBlock_append_of_eq (by decide) catalog_complete_508 block_036 rfl

private def catalog573 : List ℕ := catalog540 ++ [541, 547, 557, 563, 569, 571]
private theorem catalog_complete_573 : primeBlock 0 574 = catalog573 :=
  primeBlock_append_of_eq (by decide) catalog_complete_540 block_037 rfl

private def catalog606 : List ℕ := catalog573 ++ [577, 587, 593, 599, 601]
private theorem catalog_complete_606 : primeBlock 0 607 = catalog606 :=
  primeBlock_append_of_eq (by decide) catalog_complete_573 block_038 rfl

private def catalog640 : List ℕ := catalog606 ++ [607, 613, 617, 619, 631]
private theorem catalog_complete_640 : primeBlock 0 641 = catalog640 :=
  primeBlock_append_of_eq (by decide) catalog_complete_606 block_039 rfl

private def catalog670 : List ℕ := catalog640 ++ [641, 643, 647, 653, 659, 661]
private theorem catalog_complete_670 : primeBlock 0 671 = catalog670 :=
  primeBlock_append_of_eq (by decide) catalog_complete_640 block_040 rfl

private def catalog700 : List ℕ := catalog670 ++ [673, 677, 683, 691]
private theorem catalog_complete_700 : primeBlock 0 701 = catalog700 :=
  primeBlock_append_of_eq (by decide) catalog_complete_670 block_041 rfl

private def catalog738 : List ℕ := catalog700 ++ [701, 709, 719, 727, 733]
private theorem catalog_complete_738 : primeBlock 0 739 = catalog738 :=
  primeBlock_append_of_eq (by decide) catalog_complete_700 block_042 rfl

private def catalog772 : List ℕ := catalog738 ++ [739, 743, 751, 757, 761, 769]
private theorem catalog_complete_772 : primeBlock 0 773 = catalog772 :=
  primeBlock_append_of_eq (by decide) catalog_complete_738 block_043 rfl

private def catalog813 : List ℕ := catalog772 ++ [773, 787, 797, 809, 811]
private theorem catalog_complete_813 : primeBlock 0 814 = catalog813 :=
  primeBlock_append_of_eq (by decide) catalog_complete_772 block_044 rfl

private def catalog856 : List ℕ := catalog813 ++ [821, 823, 827, 829, 839, 853]
private theorem catalog_complete_856 : primeBlock 0 857 = catalog856 :=
  primeBlock_append_of_eq (by decide) catalog_complete_813 block_045 rfl

private def catalog886 : List ℕ := catalog856 ++ [857, 859, 863, 877, 881, 883]
private theorem catalog_complete_886 : primeBlock 0 887 = catalog886 :=
  primeBlock_append_of_eq (by decide) catalog_complete_856 block_046 rfl

private def catalog932 : List ℕ := catalog886 ++ [887, 907, 911, 919, 929]
private theorem catalog_complete_932 : primeBlock 0 933 = catalog932 :=
  primeBlock_append_of_eq (by decide) catalog_complete_886 block_047 rfl

private def catalog976 : List ℕ := catalog932 ++ [937, 941, 947, 953, 967, 971]
private theorem catalog_complete_976 : primeBlock 0 977 = catalog976 :=
  primeBlock_append_of_eq (by decide) catalog_complete_932 block_048 rfl

private def catalog1020 : List ℕ := catalog976 ++ [977, 983, 991, 997, 1009, 1013, 1019]
private theorem catalog_complete_1020 : primeBlock 0 1021 = catalog1020 :=
  primeBlock_append_of_eq (by decide) catalog_complete_976 block_049 rfl

/-- The exact complete prime catalog through this batch endpoint. -/
def catalog1060 : List ℕ := catalog1020 ++ [1021, 1031, 1033, 1039, 1049, 1051]
/-- This catalog contains every prime through its endpoint, exactly once. -/
theorem catalog_complete_1060 : primeBlock 0 1061 = catalog1060 :=
  primeBlock_append_of_eq (by decide) catalog_complete_1020 block_050 rfl

end RiemannGaussian.RosserSchoenfeldFiniteBounds
