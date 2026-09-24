/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldFiniteData02
/-!
# Kernel-checked Rosser prime-count cells: batch 4 of eight

The literal lists are proved complete by primality checks on every input
integer. Every logarithmic margin is reduced in the kernel. Small proof
boundaries retain completed work and keep cold-build memory bounded.
-/

set_option Elab.async false
namespace RiemannGaussian.RosserSchoenfeldFiniteBounds
open Real RosserSchoenfeldComparison
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

private theorem block_051 : primeBlock 1061 36 = [1061, 1063, 1069, 1087, 1091, 1093] := by
  change List.filter (fun p => decide (Nat.Prime p)) [1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071, 1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087, 1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_1096 : Nat.primeCounting 1096 = 183 := by
  exact primeCounting_step_of_block (by decide) count_1060 block_051 (by decide)
private theorem checked_051 : check 1060 1096 177 183 = true := by decide +kernel
private theorem cell_051 {x : ℝ} (hx : x ∈ Set.Icc (1060 : ℝ) 1096) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_1060.symm count_1096.symm checked_051 hx


private theorem block_052 : primeBlock 1097 40 = [1097, 1103, 1109, 1117, 1123, 1129] := by
  change List.filter (fun p => decide (Nat.Prime p)) [1097, 1098, 1099, 1100, 1101, 1102, 1103, 1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119, 1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135, 1136] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_1136 : Nat.primeCounting 1136 = 189 := by
  exact primeCounting_step_of_block (by decide) count_1096 block_052 (by decide)
private theorem checked_052 : check 1096 1136 183 189 = true := by decide +kernel
private theorem cell_052 {x : ℝ} (hx : x ∈ Set.Icc (1096 : ℝ) 1136) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_1096.symm count_1136.symm checked_052 hx


private theorem block_053 : primeBlock 1137 50 = [1151, 1153, 1163, 1171, 1181] := by
  change List.filter (fun p => decide (Nat.Prime p)) [1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151, 1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167, 1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183, 1184, 1185, 1186] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_1186 : Nat.primeCounting 1186 = 194 := by
  exact primeCounting_step_of_block (by decide) count_1136 block_053 (by decide)
private theorem checked_053 : check 1136 1186 189 194 = true := by decide +kernel
private theorem cell_053 {x : ℝ} (hx : x ∈ Set.Icc (1136 : ℝ) 1186) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_1136.symm count_1186.symm checked_053 hx


private theorem block_054 : primeBlock 1187 44 = [1187, 1193, 1201, 1213, 1217, 1223, 1229] := by
  change List.filter (fun p => decide (Nat.Prime p)) [1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199, 1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215, 1216, 1217, 1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_1230 : Nat.primeCounting 1230 = 201 := by
  exact primeCounting_step_of_block (by decide) count_1186 block_054 (by decide)
private theorem checked_054 : check 1186 1230 194 201 = true := by decide +kernel
private theorem cell_054 {x : ℝ} (hx : x ∈ Set.Icc (1186 : ℝ) 1230) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_1186.symm count_1230.symm checked_054 hx


private theorem block_055 : primeBlock 1231 52 = [1231, 1237, 1249, 1259, 1277, 1279] := by
  change List.filter (fun p => decide (Nat.Prime p)) [1231, 1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247, 1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263, 1264, 1265, 1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1279, 1280, 1281, 1282] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_1282 : Nat.primeCounting 1282 = 207 := by
  exact primeCounting_step_of_block (by decide) count_1230 block_055 (by decide)
private theorem checked_055 : check 1230 1282 201 207 = true := by decide +kernel
private theorem cell_055 {x : ℝ} (hx : x ∈ Set.Icc (1230 : ℝ) 1282) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_1230.symm count_1282.symm checked_055 hx


private theorem block_056 : primeBlock 1283 38 = [1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319] := by
  change List.filter (fun p => decide (Nat.Prime p)) [1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295, 1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311, 1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_1320 : Nat.primeCounting 1320 = 215 := by
  exact primeCounting_step_of_block (by decide) count_1282 block_056 (by decide)
private theorem checked_056 : check 1282 1320 207 215 = true := by decide +kernel
private theorem cell_056 {x : ℝ} (hx : x ∈ Set.Icc (1282 : ℝ) 1320) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_1282.symm count_1320.symm checked_056 hx


private theorem block_057 : primeBlock 1321 60 = [1321, 1327, 1361, 1367, 1373] := by
  change List.filter (fun p => decide (Nat.Prime p)) [1321, 1322, 1323, 1324, 1325, 1326, 1327, 1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343, 1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353, 1354, 1355, 1356, 1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375, 1376, 1377, 1378, 1379, 1380] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_1380 : Nat.primeCounting 1380 = 220 := by
  exact primeCounting_step_of_block (by decide) count_1320 block_057 (by decide)
private theorem checked_057 : check 1320 1380 215 220 = true := by decide +kernel
private theorem cell_057 {x : ℝ} (hx : x ∈ Set.Icc (1320 : ℝ) 1380) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_1320.symm count_1380.symm checked_057 hx


private theorem block_058 : primeBlock 1381 66 = [1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439] := by
  change List.filter (fun p => decide (Nat.Prime p)) [1381, 1382, 1383, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391, 1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407, 1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423, 1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439, 1440, 1441, 1442, 1443, 1444, 1445, 1446] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_1446 : Nat.primeCounting 1446 = 228 := by
  exact primeCounting_step_of_block (by decide) count_1380 block_058 (by decide)
private theorem checked_058 : check 1380 1446 220 228 = true := by decide +kernel
private theorem cell_058 {x : ℝ} (hx : x ∈ Set.Icc (1380 : ℝ) 1446) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_1380.symm count_1446.symm checked_058 hx


private theorem block_059 : primeBlock 1447 52 = [1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493] := by
  change List.filter (fun p => decide (Nat.Prime p)) [1447, 1448, 1449, 1450, 1451, 1452, 1453, 1454, 1455, 1456, 1457, 1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470, 1471, 1472, 1473, 1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 1487, 1488, 1489, 1490, 1491, 1492, 1493, 1494, 1495, 1496, 1497, 1498] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_1498 : Nat.primeCounting 1498 = 238 := by
  exact primeCounting_step_of_block (by decide) count_1446 block_059 (by decide)
private theorem checked_059 : check 1446 1498 228 238 = true := by decide +kernel
private theorem cell_059 {x : ℝ} (hx : x ∈ Set.Icc (1446 : ℝ) 1498) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_1446.symm count_1498.symm checked_059 hx


private theorem block_060 : primeBlock 1499 60 = [1499, 1511, 1523, 1531, 1543, 1549, 1553] := by
  change List.filter (fun p => decide (Nat.Prime p)) [1499, 1500, 1501, 1502, 1503, 1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519, 1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535, 1536, 1537, 1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551, 1552, 1553, 1554, 1555, 1556, 1557, 1558] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_1558 : Nat.primeCounting 1558 = 245 := by
  exact primeCounting_step_of_block (by decide) count_1498 block_060 (by decide)
private theorem checked_060 : check 1498 1558 238 245 = true := by decide +kernel
private theorem cell_060 {x : ℝ} (hx : x ∈ Set.Icc (1498 : ℝ) 1558) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_1498.symm count_1558.symm checked_060 hx


private theorem block_061 : primeBlock 1559 50 = [1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607] := by
  change List.filter (fun p => decide (Nat.Prime p)) [1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567, 1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599, 1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_1608 : Nat.primeCounting 1608 = 253 := by
  exact primeCounting_step_of_block (by decide) count_1558 block_061 (by decide)
private theorem checked_061 : check 1558 1608 245 253 = true := by decide +kernel
private theorem cell_061 {x : ℝ} (hx : x ∈ Set.Icc (1558 : ℝ) 1608) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_1558.symm count_1608.symm checked_061 hx


private theorem block_062 : primeBlock 1609 54 = [1609, 1613, 1619, 1621, 1627, 1637, 1657] := by
  change List.filter (fun p => decide (Nat.Prime p)) [1609, 1610, 1611, 1612, 1613, 1614, 1615, 1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631, 1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647, 1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_1662 : Nat.primeCounting 1662 = 260 := by
  exact primeCounting_step_of_block (by decide) count_1608 block_062 (by decide)
private theorem checked_062 : check 1608 1662 253 260 = true := by decide +kernel
private theorem cell_062 {x : ℝ} (hx : x ∈ Set.Icc (1608 : ℝ) 1662) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_1608.symm count_1662.symm checked_062 hx


private theorem block_063 : primeBlock 1663 58 = [1663, 1667, 1669, 1693, 1697, 1699, 1709] := by
  change List.filter (fun p => decide (Nat.Prime p)) [1663, 1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679, 1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695, 1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711, 1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_1720 : Nat.primeCounting 1720 = 267 := by
  exact primeCounting_step_of_block (by decide) count_1662 block_063 (by decide)
private theorem checked_063 : check 1662 1720 260 267 = true := by decide +kernel
private theorem cell_063 {x : ℝ} (hx : x ∈ Set.Icc (1662 : ℝ) 1720) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_1662.symm count_1720.symm checked_063 hx


private theorem block_064 : primeBlock 1721 62 = [1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777] := by
  change List.filter (fun p => decide (Nat.Prime p)) [1721, 1722, 1723, 1724, 1725, 1726, 1727, 1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743, 1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759, 1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775, 1776, 1777, 1778, 1779, 1780, 1781, 1782] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_1782 : Nat.primeCounting 1782 = 275 := by
  exact primeCounting_step_of_block (by decide) count_1720 block_064 (by decide)
private theorem checked_064 : check 1720 1782 267 275 = true := by decide +kernel
private theorem cell_064 {x : ℝ} (hx : x ∈ Set.Icc (1720 : ℝ) 1782) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_1720.symm count_1782.symm checked_064 hx


private theorem block_065 : primeBlock 1783 78 = [1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847] := by
  change List.filter (fun p => decide (Nat.Prime p)) [1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791, 1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807, 1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823, 1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839, 1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855, 1856, 1857, 1858, 1859, 1860] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_1860 : Nat.primeCounting 1860 = 283 := by
  exact primeCounting_step_of_block (by decide) count_1782 block_065 (by decide)
private theorem checked_065 : check 1782 1860 275 283 = true := by decide +kernel
private theorem cell_065 {x : ℝ} (hx : x ∈ Set.Icc (1782 : ℝ) 1860) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_1782.symm count_1860.symm checked_065 hx


private theorem block_066 : primeBlock 1861 72 = [1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931] := by
  change List.filter (fun p => decide (Nat.Prime p)) [1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871, 1872, 1873, 1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881, 1882, 1883, 1884, 1885, 1886, 1887, 1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903, 1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919, 1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_1932 : Nat.primeCounting 1932 = 294 := by
  exact primeCounting_step_of_block (by decide) count_1860 block_066 (by decide)
private theorem checked_066 : check 1860 1932 283 294 = true := by decide +kernel
private theorem cell_066 {x : ℝ} (hx : x ∈ Set.Icc (1860 : ℝ) 1932) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_1860.symm count_1932.symm checked_066 hx


private theorem block_067 : primeBlock 1933 78 = [1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003] := by
  change List.filter (fun p => decide (Nat.Prime p)) [1933, 1934, 1935, 1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950, 1951, 1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967, 1968, 1969, 1970, 1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979, 1980, 1981, 1982, 1983, 1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999, 2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_2010 : Nat.primeCounting 2010 = 304 := by
  exact primeCounting_step_of_block (by decide) count_1932 block_067 (by decide)
private theorem checked_067 : check 1932 2010 294 304 = true := by decide +kernel
private theorem cell_067 {x : ℝ} (hx : x ∈ Set.Icc (1932 : ℝ) 2010) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_1932.symm count_2010.symm checked_067 hx


private theorem range_051_053 :
    ∀ x ∈ Set.Icc (1060 : ℝ) 1136,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_051 hx) (fun _ hx => cell_052 hx)

private theorem range_053_055 :
    ∀ x ∈ Set.Icc (1136 : ℝ) 1230,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_053 hx) (fun _ hx => cell_054 hx)

private theorem range_051_055 :
    ∀ x ∈ Set.Icc (1060 : ℝ) 1230,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_051_053 range_053_055

private theorem range_055_057 :
    ∀ x ∈ Set.Icc (1230 : ℝ) 1320,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_055 hx) (fun _ hx => cell_056 hx)

private theorem range_057_059 :
    ∀ x ∈ Set.Icc (1320 : ℝ) 1446,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_057 hx) (fun _ hx => cell_058 hx)

private theorem range_055_059 :
    ∀ x ∈ Set.Icc (1230 : ℝ) 1446,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_055_057 range_057_059

private theorem range_051_059 :
    ∀ x ∈ Set.Icc (1060 : ℝ) 1446,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_051_055 range_055_059

private theorem range_059_061 :
    ∀ x ∈ Set.Icc (1446 : ℝ) 1558,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_059 hx) (fun _ hx => cell_060 hx)

private theorem range_061_063 :
    ∀ x ∈ Set.Icc (1558 : ℝ) 1662,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_061 hx) (fun _ hx => cell_062 hx)

private theorem range_059_063 :
    ∀ x ∈ Set.Icc (1446 : ℝ) 1662,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_059_061 range_061_063

private theorem range_063_065 :
    ∀ x ∈ Set.Icc (1662 : ℝ) 1782,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_063 hx) (fun _ hx => cell_064 hx)

private theorem range_066_068 :
    ∀ x ∈ Set.Icc (1860 : ℝ) 2010,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_066 hx) (fun _ hx => cell_067 hx)

private theorem range_065_068 :
    ∀ x ∈ Set.Icc (1782 : ℝ) 2010,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_065 hx) range_066_068

private theorem range_063_068 :
    ∀ x ∈ Set.Icc (1662 : ℝ) 2010,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_063_065 range_065_068

private theorem range_059_068 :
    ∀ x ∈ Set.Icc (1446 : ℝ) 2010,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_059_063 range_063_068

private theorem range_051_068 :
    ∀ x ∈ Set.Icc (1060 : ℝ) 2010,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_051_059 range_059_068

/-- The original strict count bounds throughout this complete batch of real cells. -/
theorem bounds_chunk03 :
    ∀ x ∈ Set.Icc (1060 : ℝ) 2010,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  range_051_068
private def catalog1096 : List ℕ := catalog1060 ++ [1061, 1063, 1069, 1087, 1091, 1093]
private theorem catalog_complete_1096 : primeBlock 0 1097 = catalog1096 :=
  primeBlock_append_of_eq (by decide) catalog_complete_1060 block_051 rfl

private def catalog1136 : List ℕ := catalog1096 ++ [1097, 1103, 1109, 1117, 1123, 1129]
private theorem catalog_complete_1136 : primeBlock 0 1137 = catalog1136 :=
  primeBlock_append_of_eq (by decide) catalog_complete_1096 block_052 rfl

private def catalog1186 : List ℕ := catalog1136 ++ [1151, 1153, 1163, 1171, 1181]
private theorem catalog_complete_1186 : primeBlock 0 1187 = catalog1186 :=
  primeBlock_append_of_eq (by decide) catalog_complete_1136 block_053 rfl

private def catalog1230 : List ℕ := catalog1186 ++ [1187, 1193, 1201, 1213, 1217, 1223, 1229]
private theorem catalog_complete_1230 : primeBlock 0 1231 = catalog1230 :=
  primeBlock_append_of_eq (by decide) catalog_complete_1186 block_054 rfl

private def catalog1282 : List ℕ := catalog1230 ++ [1231, 1237, 1249, 1259, 1277, 1279]
private theorem catalog_complete_1282 : primeBlock 0 1283 = catalog1282 :=
  primeBlock_append_of_eq (by decide) catalog_complete_1230 block_055 rfl

private def catalog1320 : List ℕ := catalog1282 ++ [1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319]
private theorem catalog_complete_1320 : primeBlock 0 1321 = catalog1320 :=
  primeBlock_append_of_eq (by decide) catalog_complete_1282 block_056 rfl

private def catalog1380 : List ℕ := catalog1320 ++ [1321, 1327, 1361, 1367, 1373]
private theorem catalog_complete_1380 : primeBlock 0 1381 = catalog1380 :=
  primeBlock_append_of_eq (by decide) catalog_complete_1320 block_057 rfl

private def catalog1446 : List ℕ := catalog1380 ++ [1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439]
private theorem catalog_complete_1446 : primeBlock 0 1447 = catalog1446 :=
  primeBlock_append_of_eq (by decide) catalog_complete_1380 block_058 rfl

private def catalog1498 : List ℕ := catalog1446 ++ [1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493]
private theorem catalog_complete_1498 : primeBlock 0 1499 = catalog1498 :=
  primeBlock_append_of_eq (by decide) catalog_complete_1446 block_059 rfl

private def catalog1558 : List ℕ := catalog1498 ++ [1499, 1511, 1523, 1531, 1543, 1549, 1553]
private theorem catalog_complete_1558 : primeBlock 0 1559 = catalog1558 :=
  primeBlock_append_of_eq (by decide) catalog_complete_1498 block_060 rfl

private def catalog1608 : List ℕ := catalog1558 ++ [1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607]
private theorem catalog_complete_1608 : primeBlock 0 1609 = catalog1608 :=
  primeBlock_append_of_eq (by decide) catalog_complete_1558 block_061 rfl

private def catalog1662 : List ℕ := catalog1608 ++ [1609, 1613, 1619, 1621, 1627, 1637, 1657]
private theorem catalog_complete_1662 : primeBlock 0 1663 = catalog1662 :=
  primeBlock_append_of_eq (by decide) catalog_complete_1608 block_062 rfl

private def catalog1720 : List ℕ := catalog1662 ++ [1663, 1667, 1669, 1693, 1697, 1699, 1709]
private theorem catalog_complete_1720 : primeBlock 0 1721 = catalog1720 :=
  primeBlock_append_of_eq (by decide) catalog_complete_1662 block_063 rfl

private def catalog1782 : List ℕ := catalog1720 ++ [1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777]
private theorem catalog_complete_1782 : primeBlock 0 1783 = catalog1782 :=
  primeBlock_append_of_eq (by decide) catalog_complete_1720 block_064 rfl

private def catalog1860 : List ℕ := catalog1782 ++ [1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847]
private theorem catalog_complete_1860 : primeBlock 0 1861 = catalog1860 :=
  primeBlock_append_of_eq (by decide) catalog_complete_1782 block_065 rfl

private def catalog1932 : List ℕ := catalog1860 ++ [1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931]
private theorem catalog_complete_1932 : primeBlock 0 1933 = catalog1932 :=
  primeBlock_append_of_eq (by decide) catalog_complete_1860 block_066 rfl

/-- The exact complete prime catalog through this batch endpoint. -/
def catalog2010 : List ℕ := catalog1932 ++ [1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003]
/-- This catalog contains every prime through its endpoint, exactly once. -/
theorem catalog_complete_2010 : primeBlock 0 2011 = catalog2010 :=
  primeBlock_append_of_eq (by decide) catalog_complete_1932 block_067 rfl

end RiemannGaussian.RosserSchoenfeldFiniteBounds
