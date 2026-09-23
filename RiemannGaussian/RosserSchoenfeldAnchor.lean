/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Checked anchor for the Rosser--Schoenfeld prime-counting comparison

Section 7 of Rosser and Schoenfeld (1962) anchors its comparison integral
at 1451. The prime count and primorial comparisons below are checked by
kernel reduction. The logarithmic enclosures use proved exponential bounds;
no decimal prime table or numerical transcendental evaluation is assumed.
-/

namespace RiemannGaussian.RosserSchoenfeldAnchor
noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

private def anchorPrimeList : List ℕ :=
  [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
    89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
    181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271,
    277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379,
    383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479,
    487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599,
    601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
    709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823,
    827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941,
    947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049,
    1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151,
    1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249,
    1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361,
    1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451]

private theorem anchorPrimeList_nodup : anchorPrimeList.Nodup := by
  have h : anchorPrimeList.IsChain (· < ·) := by decide +kernel
  exact (List.isChain_iff_pairwise.mp h).imp (fun h => ne_of_lt h)

private def anchorPrimes : Finset ℕ := anchorPrimeList.toFinset

private def primeBlock (a n : ℕ) : List ℕ :=
  (List.range' a n).filter (fun p => decide (Nat.Prime p))

private theorem primeBlock_add (a m n : ℕ) :
    primeBlock a (m + n) = primeBlock a m ++ primeBlock (a + m) n := by
  unfold primeBlock
  rw [← List.range'_append_1, List.filter_append]

private theorem primeBlock_00 : primeBlock 0 64 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63] = _
  norm_num [List.filter_cons]

private theorem primeBlock_01 : primeBlock 64 64 = [67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127] = _
  norm_num [List.filter_cons]

private theorem primeBlock_02 : primeBlock 128 64 = [131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191] = _
  norm_num [List.filter_cons]

private theorem primeBlock_03 : primeBlock 192 64 = [193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255] = _
  norm_num [List.filter_cons]

private theorem primeBlock_04 : primeBlock 256 64 = [257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319] = _
  norm_num [List.filter_cons]

private theorem primeBlock_05 : primeBlock 320 64 = [331, 337, 347, 349, 353, 359, 367, 373, 379, 383] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383] = _
  norm_num [List.filter_cons]

private theorem primeBlock_06 : primeBlock 384 64 = [389, 397, 401, 409, 419, 421, 431, 433, 439, 443] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447] = _
  norm_num [List.filter_cons]

private theorem primeBlock_07 : primeBlock 448 64 = [449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511] = _
  norm_num [List.filter_cons]

private theorem primeBlock_08 : primeBlock 512 64 = [521, 523, 541, 547, 557, 563, 569, 571] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575] = _
  norm_num [List.filter_cons]

private theorem primeBlock_09 : primeBlock 576 64 = [577, 587, 593, 599, 601, 607, 613, 617, 619, 631] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639] = _
  norm_num [List.filter_cons]

private theorem primeBlock_10 : primeBlock 640 64 = [641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703] = _
  norm_num [List.filter_cons]

private theorem primeBlock_11 : primeBlock 704 64 = [709, 719, 727, 733, 739, 743, 751, 757, 761] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735, 736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767] = _
  norm_num [List.filter_cons]

private theorem primeBlock_12 : primeBlock 768 64 = [769, 773, 787, 797, 809, 811, 821, 823, 827, 829] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799, 800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831] = _
  norm_num [List.filter_cons]

private theorem primeBlock_13 : primeBlock 832 64 = [839, 853, 857, 859, 863, 877, 881, 883, 887] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895] = _
  norm_num [List.filter_cons]

private theorem primeBlock_14 : primeBlock 896 64 = [907, 911, 919, 929, 937, 941, 947, 953] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959] = _
  norm_num [List.filter_cons]

private theorem primeBlock_15 : primeBlock 960 64 = [967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023] = _
  norm_num [List.filter_cons]

private theorem primeBlock_16 : primeBlock 1024 64 = [1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071, 1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087] = _
  norm_num [List.filter_cons]

private theorem primeBlock_17 : primeBlock 1088 64 = [1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103, 1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119, 1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135, 1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151] = _
  norm_num [List.filter_cons]

private theorem primeBlock_18 : primeBlock 1152 64 = [1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167, 1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183, 1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199, 1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215] = _
  norm_num [List.filter_cons]

private theorem primeBlock_19 : primeBlock 1216 64 = [1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [1216, 1217, 1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231, 1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247, 1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263, 1264, 1265, 1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1279] = _
  norm_num [List.filter_cons]

private theorem primeBlock_20 : primeBlock 1280 64 = [1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295, 1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311, 1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327, 1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343] = _
  norm_num [List.filter_cons]

private theorem primeBlock_21 : primeBlock 1344 64 = [1361, 1367, 1373, 1381, 1399] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353, 1354, 1355, 1356, 1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375, 1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391, 1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407] = _
  norm_num [List.filter_cons]

private theorem primeBlock_22 : primeBlock 1408 44 = [1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451] := by
  change List.filter (fun p => decide (Nat.Prime p))
    [1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423, 1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439, 1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1450, 1451] = _
  norm_num [List.filter_cons]

private theorem complete_primeBlock : primeBlock 0 1452 = anchorPrimeList := by
  rw [show 1452 = 64 + 1388 by rfl, primeBlock_add, primeBlock_00]
  norm_num only [Nat.reduceAdd]
  rw [show 1388 = 64 + 1324 by rfl, primeBlock_add, primeBlock_01]
  norm_num only [Nat.reduceAdd]
  rw [show 1324 = 64 + 1260 by rfl, primeBlock_add, primeBlock_02]
  norm_num only [Nat.reduceAdd]
  rw [show 1260 = 64 + 1196 by rfl, primeBlock_add, primeBlock_03]
  norm_num only [Nat.reduceAdd]
  rw [show 1196 = 64 + 1132 by rfl, primeBlock_add, primeBlock_04]
  norm_num only [Nat.reduceAdd]
  rw [show 1132 = 64 + 1068 by rfl, primeBlock_add, primeBlock_05]
  norm_num only [Nat.reduceAdd]
  rw [show 1068 = 64 + 1004 by rfl, primeBlock_add, primeBlock_06]
  norm_num only [Nat.reduceAdd]
  rw [show 1004 = 64 + 940 by rfl, primeBlock_add, primeBlock_07]
  norm_num only [Nat.reduceAdd]
  rw [show 940 = 64 + 876 by rfl, primeBlock_add, primeBlock_08]
  norm_num only [Nat.reduceAdd]
  rw [show 876 = 64 + 812 by rfl, primeBlock_add, primeBlock_09]
  norm_num only [Nat.reduceAdd]
  rw [show 812 = 64 + 748 by rfl, primeBlock_add, primeBlock_10]
  norm_num only [Nat.reduceAdd]
  rw [show 748 = 64 + 684 by rfl, primeBlock_add, primeBlock_11]
  norm_num only [Nat.reduceAdd]
  rw [show 684 = 64 + 620 by rfl, primeBlock_add, primeBlock_12]
  norm_num only [Nat.reduceAdd]
  rw [show 620 = 64 + 556 by rfl, primeBlock_add, primeBlock_13]
  norm_num only [Nat.reduceAdd]
  rw [show 556 = 64 + 492 by rfl, primeBlock_add, primeBlock_14]
  norm_num only [Nat.reduceAdd]
  rw [show 492 = 64 + 428 by rfl, primeBlock_add, primeBlock_15]
  norm_num only [Nat.reduceAdd]
  rw [show 428 = 64 + 364 by rfl, primeBlock_add, primeBlock_16]
  norm_num only [Nat.reduceAdd]
  rw [show 364 = 64 + 300 by rfl, primeBlock_add, primeBlock_17]
  norm_num only [Nat.reduceAdd]
  rw [show 300 = 64 + 236 by rfl, primeBlock_add, primeBlock_18]
  norm_num only [Nat.reduceAdd]
  rw [show 236 = 64 + 172 by rfl, primeBlock_add, primeBlock_19]
  norm_num only [Nat.reduceAdd]
  rw [show 172 = 64 + 108 by rfl, primeBlock_add, primeBlock_20]
  norm_num only [Nat.reduceAdd]
  rw [show 108 = 64 + 44 by rfl, primeBlock_add, primeBlock_21]
  norm_num only [Nat.reduceAdd]
  rw [primeBlock_22]
  rfl

private theorem primesLE_anchor : Nat.primesLE 1451 = anchorPrimes := by
  have h (n : ℕ) : Nat.primesLE n = (primeBlock 0 (n + 1)).toFinset := by
    ext p
    simp [Nat.mem_primesLE, primeBlock, List.mem_range', and_comm]
  rw [h, show (1451 : ℕ) + 1 = 1452 by rfl, complete_primeBlock]
  rfl

/-- The exact prime count used at the source's anchor. -/
theorem primeCounting_anchor : Nat.primeCounting 1451 = 230 := by
  rw [← Nat.primesLE_card_eq_primeCounting, primesLE_anchor,
    anchorPrimes, List.toFinset_card_of_nodup anchorPrimeList_nodup]
  rfl

private theorem primorial_anchor : primorial 1451 = 2946824303299385926285217954255898461380758037675315706473372035854590825869939973355083668673025519361996548505120090899495509825441920971792765926855920089836386527041256045559967782850605615907940821619292337933234787941369551938108608433802393065872560036303993066200354649204017422460139428137847766848998696245513974150414107106872842198815117175228869327318321610454745284429301492623235915878061329655588584953794976535654241614142469591682259697196747067846140854804788776319334312242631670045557387220130390610441632521320992003936720159243434591993288841688392592955410373779932643572446458370830 := by
  rw [primorial_eq_prod_primesLE, primesLE_anchor, anchorPrimes,
    List.prod_toFinset _ anchorPrimeList_nodup]
  norm_num [anchorPrimeList]

private theorem primorial_lower : 11 ^ 1360 < 4 ^ 1360 * primorial 1451 := by
  rw [primorial_anchor]
  norm_num

private theorem primorial_upper : 10 ^ 1410 * primorial 1451 < 27 ^ 1410 := by
  rw [primorial_anchor]
  norm_num

/-- A rational lower enclosure sufficient for all three anchored comparisons. -/
theorem theta_anchor_lower : (1360 : ℝ) < Chebyshev.theta 1451 := by
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_ofNat]
  apply (Real.lt_log_iff_exp_lt (Nat.cast_pos.mpr (primorial_pos 1451))).mpr
  have he : Real.exp 1 ≤ (11 / 4 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le he 1360
  rw [← Real.exp_nat_mul] at hp
  simp only [Nat.cast_ofNat, mul_one] at hp
  refine hp.trans_lt ?_
  rw [div_pow, div_lt_iff₀ (by positivity)]
  have hh : ((11 ^ 1360 : ℕ) : ℝ) < ((4 ^ 1360 * primorial 1451 : ℕ) : ℝ) :=
    Nat.cast_lt.mpr primorial_lower
  simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hh

/-- A rational upper enclosure sufficient for the lower prime-counting comparison. -/
theorem theta_anchor_upper : Chebyshev.theta 1451 < (1410 : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_ofNat]
  apply (Real.log_lt_iff_lt_exp (Nat.cast_pos.mpr (primorial_pos 1451))).mpr
  have he : (27 / 10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10) he 1410
  rw [← Real.exp_nat_mul] at hp
  simp only [Nat.cast_ofNat, mul_one] at hp
  refine lt_of_lt_of_le ?_ hp
  rw [div_pow, lt_div_iff₀ (by positivity)]
  have hh : ((10 ^ 1410 * primorial 1451 : ℕ) : ℝ) < ((27 ^ 1410 : ℕ) : ℝ) :=
    Nat.cast_lt.mpr primorial_upper
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm] using hh

/-- Lower logarithmic enclosure at the literal anchor. -/
theorem log_anchor_lower : (36 / 5 : ℝ) ≤ Real.log 1451 := by
  have he : Real.exp 1 ≤ (68 / 25 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le he 36
  rw [← Real.exp_nat_mul] at hp
  simp only [Nat.cast_ofNat, mul_one] at hp
  have hh : Real.exp 36 ≤ (1451 : ℝ) ^ 5 := hp.trans (by norm_num)
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1451), ← Real.exp_nat_mul,
    Real.exp_le_exp] at hh
  norm_num at hh
  linarith

/-- Upper logarithmic enclosure at the literal anchor. -/
theorem log_anchor_upper : Real.log 1451 ≤ (73 / 10 : ℝ) := by
  have he : (19 / 7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 19 / 7) he 73
  rw [← Real.exp_nat_mul] at hp
  simp only [Nat.cast_ofNat, mul_one] at hp
  have hh : (1451 : ℝ) ^ 10 ≤ Real.exp 73 := (by norm_num :
    (1451 : ℝ) ^ 10 ≤ (19 / 7) ^ 73).trans hp
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1451), ← Real.exp_nat_mul,
    Real.exp_le_exp] at hh
  norm_num at hh
  linarith

/-- The paper's decimal starting point has logarithm at least eighteen. -/
theorem log_ten_pow_eight_lower : (18 : ℝ) ≤ Real.log (10 ^ 8) := by
  apply (Real.le_log_iff_exp_le (by positivity)).mpr
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le
    (show Real.exp 1 ≤ (11 / 4 : ℝ) by linarith [Real.exp_one_lt_d9]) 18
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  linarith

end
end RiemannGaussian.RosserSchoenfeldAnchor
