/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldFiniteData03
/-!
# Kernel-checked Rosser prime-count cells: batch 5 of eight

The literal lists are proved complete by primality checks on every input
integer. Every logarithmic margin is reduced in the kernel. Small proof
boundaries retain completed work and keep cold-build memory bounded.
-/

set_option Elab.async false
namespace RiemannGaussian.RosserSchoenfeldFiniteBounds
open Real RosserSchoenfeldComparison
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

private theorem block_068 : primeBlock 2011 76 = [2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083] := by
  change List.filter (fun p => decide (Nat.Prime p)) [2011, 2012, 2013, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031, 2032, 2033, 2034, 2035, 2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046, 2047, 2048, 2049, 2050, 2051, 2052, 2053, 2054, 2055, 2056, 2057, 2058, 2059, 2060, 2061, 2062, 2063, 2064, 2065, 2066, 2067, 2068, 2069, 2070, 2071, 2072, 2073, 2074, 2075, 2076, 2077, 2078, 2079, 2080, 2081, 2082, 2083, 2084, 2085, 2086] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_2086 : Nat.primeCounting 2086 = 314 := by
  exact primeCounting_step_of_block (by decide) count_2010 block_068 (by decide)
private theorem checked_068 : check 2010 2086 304 314 = true := by decide +kernel
private theorem cell_068 {x : ℝ} (hx : x ∈ Set.Icc (2010 : ℝ) 2086) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_2010.symm count_2086.symm checked_068 hx


private theorem block_069 : primeBlock 2087 66 = [2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143] := by
  change List.filter (fun p => decide (Nat.Prime p)) [2087, 2088, 2089, 2090, 2091, 2092, 2093, 2094, 2095, 2096, 2097, 2098, 2099, 2100, 2101, 2102, 2103, 2104, 2105, 2106, 2107, 2108, 2109, 2110, 2111, 2112, 2113, 2114, 2115, 2116, 2117, 2118, 2119, 2120, 2121, 2122, 2123, 2124, 2125, 2126, 2127, 2128, 2129, 2130, 2131, 2132, 2133, 2134, 2135, 2136, 2137, 2138, 2139, 2140, 2141, 2142, 2143, 2144, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2152] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_2152 : Nat.primeCounting 2152 = 324 := by
  exact primeCounting_step_of_block (by decide) count_2086 block_069 (by decide)
private theorem checked_069 : check 2086 2152 314 324 = true := by decide +kernel
private theorem cell_069 {x : ℝ} (hx : x ∈ Set.Icc (2086 : ℝ) 2152) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_2086.symm count_2152.symm checked_069 hx


private theorem block_070 : primeBlock 2153 90 = [2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239] := by
  change List.filter (fun p => decide (Nat.Prime p)) [2153, 2154, 2155, 2156, 2157, 2158, 2159, 2160, 2161, 2162, 2163, 2164, 2165, 2166, 2167, 2168, 2169, 2170, 2171, 2172, 2173, 2174, 2175, 2176, 2177, 2178, 2179, 2180, 2181, 2182, 2183, 2184, 2185, 2186, 2187, 2188, 2189, 2190, 2191, 2192, 2193, 2194, 2195, 2196, 2197, 2198, 2199, 2200, 2201, 2202, 2203, 2204, 2205, 2206, 2207, 2208, 2209, 2210, 2211, 2212, 2213, 2214, 2215, 2216, 2217, 2218, 2219, 2220, 2221, 2222, 2223, 2224, 2225, 2226, 2227, 2228, 2229, 2230, 2231, 2232, 2233, 2234, 2235, 2236, 2237, 2238, 2239, 2240, 2241, 2242] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_2242 : Nat.primeCounting 2242 = 333 := by
  exact primeCounting_step_of_block (by decide) count_2152 block_070 (by decide)
private theorem checked_070 : check 2152 2242 324 333 = true := by decide +kernel
private theorem cell_070 {x : ℝ} (hx : x ∈ Set.Icc (2152 : ℝ) 2242) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_2152.symm count_2242.symm checked_070 hx


private theorem block_071 : primeBlock 2243 92 = [2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333] := by
  change List.filter (fun p => decide (Nat.Prime p)) [2243, 2244, 2245, 2246, 2247, 2248, 2249, 2250, 2251, 2252, 2253, 2254, 2255, 2256, 2257, 2258, 2259, 2260, 2261, 2262, 2263, 2264, 2265, 2266, 2267, 2268, 2269, 2270, 2271, 2272, 2273, 2274, 2275, 2276, 2277, 2278, 2279, 2280, 2281, 2282, 2283, 2284, 2285, 2286, 2287, 2288, 2289, 2290, 2291, 2292, 2293, 2294, 2295, 2296, 2297, 2298, 2299, 2300, 2301, 2302, 2303, 2304, 2305, 2306, 2307, 2308, 2309, 2310, 2311, 2312, 2313, 2314, 2315, 2316, 2317, 2318, 2319, 2320, 2321, 2322, 2323, 2324, 2325, 2326, 2327, 2328, 2329, 2330, 2331, 2332, 2333, 2334] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_2334 : Nat.primeCounting 2334 = 345 := by
  exact primeCounting_step_of_block (by decide) count_2242 block_071 (by decide)
private theorem checked_071 : check 2242 2334 333 345 = true := by decide +kernel
private theorem cell_071 {x : ℝ} (hx : x ∈ Set.Icc (2242 : ℝ) 2334) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_2242.symm count_2334.symm checked_071 hx


private theorem block_072 : primeBlock 2335 76 = [2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399] := by
  change List.filter (fun p => decide (Nat.Prime p)) [2335, 2336, 2337, 2338, 2339, 2340, 2341, 2342, 2343, 2344, 2345, 2346, 2347, 2348, 2349, 2350, 2351, 2352, 2353, 2354, 2355, 2356, 2357, 2358, 2359, 2360, 2361, 2362, 2363, 2364, 2365, 2366, 2367, 2368, 2369, 2370, 2371, 2372, 2373, 2374, 2375, 2376, 2377, 2378, 2379, 2380, 2381, 2382, 2383, 2384, 2385, 2386, 2387, 2388, 2389, 2390, 2391, 2392, 2393, 2394, 2395, 2396, 2397, 2398, 2399, 2400, 2401, 2402, 2403, 2404, 2405, 2406, 2407, 2408, 2409, 2410] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_2410 : Nat.primeCounting 2410 = 357 := by
  exact primeCounting_step_of_block (by decide) count_2334 block_072 (by decide)
private theorem checked_072 : check 2334 2410 345 357 = true := by decide +kernel
private theorem cell_072 {x : ℝ} (hx : x ∈ Set.Icc (2334 : ℝ) 2410) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_2334.symm count_2410.symm checked_072 hx


private theorem block_073 : primeBlock 2411 92 = [2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477] := by
  change List.filter (fun p => decide (Nat.Prime p)) [2411, 2412, 2413, 2414, 2415, 2416, 2417, 2418, 2419, 2420, 2421, 2422, 2423, 2424, 2425, 2426, 2427, 2428, 2429, 2430, 2431, 2432, 2433, 2434, 2435, 2436, 2437, 2438, 2439, 2440, 2441, 2442, 2443, 2444, 2445, 2446, 2447, 2448, 2449, 2450, 2451, 2452, 2453, 2454, 2455, 2456, 2457, 2458, 2459, 2460, 2461, 2462, 2463, 2464, 2465, 2466, 2467, 2468, 2469, 2470, 2471, 2472, 2473, 2474, 2475, 2476, 2477, 2478, 2479, 2480, 2481, 2482, 2483, 2484, 2485, 2486, 2487, 2488, 2489, 2490, 2491, 2492, 2493, 2494, 2495, 2496, 2497, 2498, 2499, 2500, 2501, 2502] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_2502 : Nat.primeCounting 2502 = 367 := by
  exact primeCounting_step_of_block (by decide) count_2410 block_073 (by decide)
private theorem checked_073 : check 2410 2502 357 367 = true := by decide +kernel
private theorem cell_073 {x : ℝ} (hx : x ∈ Set.Icc (2410 : ℝ) 2502) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_2410.symm count_2502.symm checked_073 hx


private theorem block_074 : primeBlock 2503 106 = [2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593] := by
  change List.filter (fun p => decide (Nat.Prime p)) [2503, 2504, 2505, 2506, 2507, 2508, 2509, 2510, 2511, 2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527, 2528, 2529, 2530, 2531, 2532, 2533, 2534, 2535, 2536, 2537, 2538, 2539, 2540, 2541, 2542, 2543, 2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556, 2557, 2558, 2559, 2560, 2561, 2562, 2563, 2564, 2565, 2566, 2567, 2568, 2569, 2570, 2571, 2572, 2573, 2574, 2575, 2576, 2577, 2578, 2579, 2580, 2581, 2582, 2583, 2584, 2585, 2586, 2587, 2588, 2589, 2590, 2591, 2592, 2593, 2594, 2595, 2596, 2597, 2598, 2599, 2600, 2601, 2602, 2603, 2604, 2605, 2606, 2607, 2608] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_2608 : Nat.primeCounting 2608 = 378 := by
  exact primeCounting_step_of_block (by decide) count_2502 block_074 (by decide)
private theorem checked_074 : check 2502 2608 367 378 = true := by decide +kernel
private theorem cell_074 {x : ℝ} (hx : x ∈ Set.Icc (2502 : ℝ) 2608) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_2502.symm count_2608.symm checked_074 hx


private theorem block_075 : primeBlock 2609 90 = [2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693] := by
  change List.filter (fun p => decide (Nat.Prime p)) [2609, 2610, 2611, 2612, 2613, 2614, 2615, 2616, 2617, 2618, 2619, 2620, 2621, 2622, 2623, 2624, 2625, 2626, 2627, 2628, 2629, 2630, 2631, 2632, 2633, 2634, 2635, 2636, 2637, 2638, 2639, 2640, 2641, 2642, 2643, 2644, 2645, 2646, 2647, 2648, 2649, 2650, 2651, 2652, 2653, 2654, 2655, 2656, 2657, 2658, 2659, 2660, 2661, 2662, 2663, 2664, 2665, 2666, 2667, 2668, 2669, 2670, 2671, 2672, 2673, 2674, 2675, 2676, 2677, 2678, 2679, 2680, 2681, 2682, 2683, 2684, 2685, 2686, 2687, 2688, 2689, 2690, 2691, 2692, 2693, 2694, 2695, 2696, 2697, 2698] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_2698 : Nat.primeCounting 2698 = 392 := by
  exact primeCounting_step_of_block (by decide) count_2608 block_075 (by decide)
private theorem checked_075 : check 2608 2698 378 392 = true := by decide +kernel
private theorem cell_075 {x : ℝ} (hx : x ∈ Set.Icc (2608 : ℝ) 2698) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_2608.symm count_2698.symm checked_075 hx


private theorem block_076 : primeBlock 2699 90 = [2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777] := by
  change List.filter (fun p => decide (Nat.Prime p)) [2699, 2700, 2701, 2702, 2703, 2704, 2705, 2706, 2707, 2708, 2709, 2710, 2711, 2712, 2713, 2714, 2715, 2716, 2717, 2718, 2719, 2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727, 2728, 2729, 2730, 2731, 2732, 2733, 2734, 2735, 2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745, 2746, 2747, 2748, 2749, 2750, 2751, 2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760, 2761, 2762, 2763, 2764, 2765, 2766, 2767, 2768, 2769, 2770, 2771, 2772, 2773, 2774, 2775, 2776, 2777, 2778, 2779, 2780, 2781, 2782, 2783, 2784, 2785, 2786, 2787, 2788] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_2788 : Nat.primeCounting 2788 = 404 := by
  exact primeCounting_step_of_block (by decide) count_2698 block_076 (by decide)
private theorem checked_076 : check 2698 2788 392 404 = true := by decide +kernel
private theorem cell_076 {x : ℝ} (hx : x ∈ Set.Icc (2698 : ℝ) 2788) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_2698.symm count_2788.symm checked_076 hx


private theorem block_077 : primeBlock 2789 88 = [2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861] := by
  change List.filter (fun p => decide (Nat.Prime p)) [2789, 2790, 2791, 2792, 2793, 2794, 2795, 2796, 2797, 2798, 2799, 2800, 2801, 2802, 2803, 2804, 2805, 2806, 2807, 2808, 2809, 2810, 2811, 2812, 2813, 2814, 2815, 2816, 2817, 2818, 2819, 2820, 2821, 2822, 2823, 2824, 2825, 2826, 2827, 2828, 2829, 2830, 2831, 2832, 2833, 2834, 2835, 2836, 2837, 2838, 2839, 2840, 2841, 2842, 2843, 2844, 2845, 2846, 2847, 2848, 2849, 2850, 2851, 2852, 2853, 2854, 2855, 2856, 2857, 2858, 2859, 2860, 2861, 2862, 2863, 2864, 2865, 2866, 2867, 2868, 2869, 2870, 2871, 2872, 2873, 2874, 2875, 2876] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_2876 : Nat.primeCounting 2876 = 416 := by
  exact primeCounting_step_of_block (by decide) count_2788 block_077 (by decide)
private theorem checked_077 : check 2788 2876 404 416 = true := by decide +kernel
private theorem cell_077 {x : ℝ} (hx : x ∈ Set.Icc (2788 : ℝ) 2876) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_2788.symm count_2876.symm checked_077 hx


private theorem block_078 : primeBlock 2877 92 = [2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963] := by
  change List.filter (fun p => decide (Nat.Prime p)) [2877, 2878, 2879, 2880, 2881, 2882, 2883, 2884, 2885, 2886, 2887, 2888, 2889, 2890, 2891, 2892, 2893, 2894, 2895, 2896, 2897, 2898, 2899, 2900, 2901, 2902, 2903, 2904, 2905, 2906, 2907, 2908, 2909, 2910, 2911, 2912, 2913, 2914, 2915, 2916, 2917, 2918, 2919, 2920, 2921, 2922, 2923, 2924, 2925, 2926, 2927, 2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940, 2941, 2942, 2943, 2944, 2945, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959, 2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967, 2968] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_2968 : Nat.primeCounting 2968 = 427 := by
  exact primeCounting_step_of_block (by decide) count_2876 block_078 (by decide)
private theorem checked_078 : check 2876 2968 416 427 = true := by decide +kernel
private theorem cell_078 {x : ℝ} (hx : x ∈ Set.Icc (2876 : ℝ) 2968) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_2876.symm count_2968.symm checked_078 hx


private theorem block_079 : primeBlock 2969 98 = [2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061] := by
  change List.filter (fun p => decide (Nat.Prime p)) [2969, 2970, 2971, 2972, 2973, 2974, 2975, 2976, 2977, 2978, 2979, 2980, 2981, 2982, 2983, 2984, 2985, 2986, 2987, 2988, 2989, 2990, 2991, 2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007, 3008, 3009, 3010, 3011, 3012, 3013, 3014, 3015, 3016, 3017, 3018, 3019, 3020, 3021, 3022, 3023, 3024, 3025, 3026, 3027, 3028, 3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036, 3037, 3038, 3039, 3040, 3041, 3042, 3043, 3044, 3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052, 3053, 3054, 3055, 3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_3066 : Nat.primeCounting 3066 = 438 := by
  exact primeCounting_step_of_block (by decide) count_2968 block_079 (by decide)
private theorem checked_079 : check 2968 3066 427 438 = true := by decide +kernel
private theorem cell_079 {x : ℝ} (hx : x ∈ Set.Icc (2968 : ℝ) 3066) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_2968.symm count_3066.symm checked_079 hx


private theorem block_080 : primeBlock 3067 120 = [3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181] := by
  change List.filter (fun p => decide (Nat.Prime p)) [3067, 3068, 3069, 3070, 3071, 3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087, 3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103, 3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119, 3120, 3121, 3122, 3123, 3124, 3125, 3126, 3127, 3128, 3129, 3130, 3131, 3132, 3133, 3134, 3135, 3136, 3137, 3138, 3139, 3140, 3141, 3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151, 3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159, 3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167, 3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183, 3184, 3185, 3186] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_3186 : Nat.primeCounting 3186 = 450 := by
  exact primeCounting_step_of_block (by decide) count_3066 block_080 (by decide)
private theorem checked_080 : check 3066 3186 438 450 = true := by decide +kernel
private theorem cell_080 {x : ℝ} (hx : x ∈ Set.Icc (3066 : ℝ) 3186) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_3066.symm count_3186.symm checked_080 hx


private theorem block_081 : primeBlock 3187 126 = [3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307] := by
  change List.filter (fun p => decide (Nat.Prime p)) [3187, 3188, 3189, 3190, 3191, 3192, 3193, 3194, 3195, 3196, 3197, 3198, 3199, 3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209, 3210, 3211, 3212, 3213, 3214, 3215, 3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3231, 3232, 3233, 3234, 3235, 3236, 3237, 3238, 3239, 3240, 3241, 3242, 3243, 3244, 3245, 3246, 3247, 3248, 3249, 3250, 3251, 3252, 3253, 3254, 3255, 3256, 3257, 3258, 3259, 3260, 3261, 3262, 3263, 3264, 3265, 3266, 3267, 3268, 3269, 3270, 3271, 3272, 3273, 3274, 3275, 3276, 3277, 3278, 3279, 3280, 3281, 3282, 3283, 3284, 3285, 3286, 3287, 3288, 3289, 3290, 3291, 3292, 3293, 3294, 3295, 3296, 3297, 3298, 3299, 3300, 3301, 3302, 3303, 3304, 3305, 3306, 3307, 3308, 3309, 3310, 3311, 3312] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_3312 : Nat.primeCounting 3312 = 465 := by
  exact primeCounting_step_of_block (by decide) count_3186 block_081 (by decide)
private theorem checked_081 : check 3186 3312 450 465 = true := by decide +kernel
private theorem cell_081 {x : ℝ} (hx : x ∈ Set.Icc (3186 : ℝ) 3312) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_3186.symm count_3312.symm checked_081 hx


private theorem block_082 : primeBlock 3313 136 = [3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433] := by
  change List.filter (fun p => decide (Nat.Prime p)) [3313, 3314, 3315, 3316, 3317, 3318, 3319, 3320, 3321, 3322, 3323, 3324, 3325, 3326, 3327, 3328, 3329, 3330, 3331, 3332, 3333, 3334, 3335, 3336, 3337, 3338, 3339, 3340, 3341, 3342, 3343, 3344, 3345, 3346, 3347, 3348, 3349, 3350, 3351, 3352, 3353, 3354, 3355, 3356, 3357, 3358, 3359, 3360, 3361, 3362, 3363, 3364, 3365, 3366, 3367, 3368, 3369, 3370, 3371, 3372, 3373, 3374, 3375, 3376, 3377, 3378, 3379, 3380, 3381, 3382, 3383, 3384, 3385, 3386, 3387, 3388, 3389, 3390, 3391, 3392, 3393, 3394, 3395, 3396, 3397, 3398, 3399, 3400, 3401, 3402, 3403, 3404, 3405, 3406, 3407, 3408, 3409, 3410, 3411, 3412, 3413, 3414, 3415, 3416, 3417, 3418, 3419, 3420, 3421, 3422, 3423, 3424, 3425, 3426, 3427, 3428, 3429, 3430, 3431, 3432, 3433, 3434, 3435, 3436, 3437, 3438, 3439, 3440, 3441, 3442, 3443, 3444, 3445, 3446, 3447, 3448] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_3448 : Nat.primeCounting 3448 = 481 := by
  exact primeCounting_step_of_block (by decide) count_3312 block_082 (by decide)
private theorem checked_082 : check 3312 3448 465 481 = true := by decide +kernel
private theorem cell_082 {x : ℝ} (hx : x ∈ Set.Icc (3312 : ℝ) 3448) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_3312.symm count_3448.symm checked_082 hx


private theorem block_083 : primeBlock 3449 111 = [3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559] := by
  change List.filter (fun p => decide (Nat.Prime p)) [3449, 3450, 3451, 3452, 3453, 3454, 3455, 3456, 3457, 3458, 3459, 3460, 3461, 3462, 3463, 3464, 3465, 3466, 3467, 3468, 3469, 3470, 3471, 3472, 3473, 3474, 3475, 3476, 3477, 3478, 3479, 3480, 3481, 3482, 3483, 3484, 3485, 3486, 3487, 3488, 3489, 3490, 3491, 3492, 3493, 3494, 3495, 3496, 3497, 3498, 3499, 3500, 3501, 3502, 3503, 3504, 3505, 3506, 3507, 3508, 3509, 3510, 3511, 3512, 3513, 3514, 3515, 3516, 3517, 3518, 3519, 3520, 3521, 3522, 3523, 3524, 3525, 3526, 3527, 3528, 3529, 3530, 3531, 3532, 3533, 3534, 3535, 3536, 3537, 3538, 3539, 3540, 3541, 3542, 3543, 3544, 3545, 3546, 3547, 3548, 3549, 3550, 3551, 3552, 3553, 3554, 3555, 3556, 3557, 3558, 3559] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_3559 : Nat.primeCounting 3559 = 499 := by
  exact primeCounting_step_of_block (by decide) count_3448 block_083 (by decide)
private theorem checked_083 : check 3448 3559 481 499 = true := by decide +kernel
private theorem cell_083 {x : ℝ} (hx : x ∈ Set.Icc (3448 : ℝ) 3559) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_3448.symm count_3559.symm checked_083 hx


private theorem block_084 : primeBlock 3560 113 = [3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671] := by
  change List.filter (fun p => decide (Nat.Prime p)) [3560, 3561, 3562, 3563, 3564, 3565, 3566, 3567, 3568, 3569, 3570, 3571, 3572, 3573, 3574, 3575, 3576, 3577, 3578, 3579, 3580, 3581, 3582, 3583, 3584, 3585, 3586, 3587, 3588, 3589, 3590, 3591, 3592, 3593, 3594, 3595, 3596, 3597, 3598, 3599, 3600, 3601, 3602, 3603, 3604, 3605, 3606, 3607, 3608, 3609, 3610, 3611, 3612, 3613, 3614, 3615, 3616, 3617, 3618, 3619, 3620, 3621, 3622, 3623, 3624, 3625, 3626, 3627, 3628, 3629, 3630, 3631, 3632, 3633, 3634, 3635, 3636, 3637, 3638, 3639, 3640, 3641, 3642, 3643, 3644, 3645, 3646, 3647, 3648, 3649, 3650, 3651, 3652, 3653, 3654, 3655, 3656, 3657, 3658, 3659, 3660, 3661, 3662, 3663, 3664, 3665, 3666, 3667, 3668, 3669, 3670, 3671, 3672] = _
  norm_num [List.filter_cons]
/-- The exact count of all primes through this checked endpoint. -/
theorem count_3672 : Nat.primeCounting 3672 = 512 := by
  exact primeCounting_step_of_block (by decide) count_3559 block_084 (by decide)
private theorem checked_084 : check 3559 3672 499 512 = true := by decide +kernel
private theorem cell_084 {x : ℝ} (hx : x ∈ Set.Icc (3559 : ℝ) 3672) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  comparison_on_cell (by decide) (by decide) count_3559.symm count_3672.symm checked_084 hx


private theorem range_068_070 :
    ∀ x ∈ Set.Icc (2010 : ℝ) 2152,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_068 hx) (fun _ hx => cell_069 hx)

private theorem range_070_072 :
    ∀ x ∈ Set.Icc (2152 : ℝ) 2334,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_070 hx) (fun _ hx => cell_071 hx)

private theorem range_068_072 :
    ∀ x ∈ Set.Icc (2010 : ℝ) 2334,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_068_070 range_070_072

private theorem range_072_074 :
    ∀ x ∈ Set.Icc (2334 : ℝ) 2502,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_072 hx) (fun _ hx => cell_073 hx)

private theorem range_074_076 :
    ∀ x ∈ Set.Icc (2502 : ℝ) 2698,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_074 hx) (fun _ hx => cell_075 hx)

private theorem range_072_076 :
    ∀ x ∈ Set.Icc (2334 : ℝ) 2698,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_072_074 range_074_076

private theorem range_068_076 :
    ∀ x ∈ Set.Icc (2010 : ℝ) 2698,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_068_072 range_072_076

private theorem range_076_078 :
    ∀ x ∈ Set.Icc (2698 : ℝ) 2876,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_076 hx) (fun _ hx => cell_077 hx)

private theorem range_078_080 :
    ∀ x ∈ Set.Icc (2876 : ℝ) 3066,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_078 hx) (fun _ hx => cell_079 hx)

private theorem range_076_080 :
    ∀ x ∈ Set.Icc (2698 : ℝ) 3066,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_076_078 range_078_080

private theorem range_080_082 :
    ∀ x ∈ Set.Icc (3066 : ℝ) 3312,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_080 hx) (fun _ hx => cell_081 hx)

private theorem range_083_085 :
    ∀ x ∈ Set.Icc (3448 : ℝ) 3672,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_083 hx) (fun _ hx => cell_084 hx)

private theorem range_082_085 :
    ∀ x ∈ Set.Icc (3312 : ℝ) 3672,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join (fun _ hx => cell_082 hx) range_083_085

private theorem range_080_085 :
    ∀ x ∈ Set.Icc (3066 : ℝ) 3672,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_080_082 range_082_085

private theorem range_076_085 :
    ∀ x ∈ Set.Icc (2698 : ℝ) 3672,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_076_080 range_080_085

private theorem range_068_085 :
    ∀ x ∈ Set.Icc (2010 : ℝ) 3672,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  join range_068_076 range_076_085

/-- The original strict count bounds throughout this complete batch of real cells. -/
theorem bounds_chunk04 :
    ∀ x ∈ Set.Icc (2010 : ℝ) 3672,
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x :=
  range_068_085
private def catalog2086 : List ℕ := catalog2010 ++ [2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083]
private theorem catalog_complete_2086 : primeBlock 0 2087 = catalog2086 :=
  primeBlock_append_of_eq (by decide) catalog_complete_2010 block_068 rfl

private def catalog2152 : List ℕ := catalog2086 ++ [2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143]
private theorem catalog_complete_2152 : primeBlock 0 2153 = catalog2152 :=
  primeBlock_append_of_eq (by decide) catalog_complete_2086 block_069 rfl

private def catalog2242 : List ℕ := catalog2152 ++ [2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239]
private theorem catalog_complete_2242 : primeBlock 0 2243 = catalog2242 :=
  primeBlock_append_of_eq (by decide) catalog_complete_2152 block_070 rfl

private def catalog2334 : List ℕ := catalog2242 ++ [2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333]
private theorem catalog_complete_2334 : primeBlock 0 2335 = catalog2334 :=
  primeBlock_append_of_eq (by decide) catalog_complete_2242 block_071 rfl

private def catalog2410 : List ℕ := catalog2334 ++ [2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399]
private theorem catalog_complete_2410 : primeBlock 0 2411 = catalog2410 :=
  primeBlock_append_of_eq (by decide) catalog_complete_2334 block_072 rfl

private def catalog2502 : List ℕ := catalog2410 ++ [2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477]
private theorem catalog_complete_2502 : primeBlock 0 2503 = catalog2502 :=
  primeBlock_append_of_eq (by decide) catalog_complete_2410 block_073 rfl

private def catalog2608 : List ℕ := catalog2502 ++ [2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593]
private theorem catalog_complete_2608 : primeBlock 0 2609 = catalog2608 :=
  primeBlock_append_of_eq (by decide) catalog_complete_2502 block_074 rfl

private def catalog2698 : List ℕ := catalog2608 ++ [2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693]
private theorem catalog_complete_2698 : primeBlock 0 2699 = catalog2698 :=
  primeBlock_append_of_eq (by decide) catalog_complete_2608 block_075 rfl

private def catalog2788 : List ℕ := catalog2698 ++ [2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777]
private theorem catalog_complete_2788 : primeBlock 0 2789 = catalog2788 :=
  primeBlock_append_of_eq (by decide) catalog_complete_2698 block_076 rfl

private def catalog2876 : List ℕ := catalog2788 ++ [2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861]
private theorem catalog_complete_2876 : primeBlock 0 2877 = catalog2876 :=
  primeBlock_append_of_eq (by decide) catalog_complete_2788 block_077 rfl

private def catalog2968 : List ℕ := catalog2876 ++ [2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963]
private theorem catalog_complete_2968 : primeBlock 0 2969 = catalog2968 :=
  primeBlock_append_of_eq (by decide) catalog_complete_2876 block_078 rfl

private def catalog3066 : List ℕ := catalog2968 ++ [2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061]
private theorem catalog_complete_3066 : primeBlock 0 3067 = catalog3066 :=
  primeBlock_append_of_eq (by decide) catalog_complete_2968 block_079 rfl

private def catalog3186 : List ℕ := catalog3066 ++ [3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181]
private theorem catalog_complete_3186 : primeBlock 0 3187 = catalog3186 :=
  primeBlock_append_of_eq (by decide) catalog_complete_3066 block_080 rfl

private def catalog3312 : List ℕ := catalog3186 ++ [3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307]
private theorem catalog_complete_3312 : primeBlock 0 3313 = catalog3312 :=
  primeBlock_append_of_eq (by decide) catalog_complete_3186 block_081 rfl

private def catalog3448 : List ℕ := catalog3312 ++ [3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433]
private theorem catalog_complete_3448 : primeBlock 0 3449 = catalog3448 :=
  primeBlock_append_of_eq (by decide) catalog_complete_3312 block_082 rfl

private def catalog3559 : List ℕ := catalog3448 ++ [3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559]
private theorem catalog_complete_3559 : primeBlock 0 3560 = catalog3559 :=
  primeBlock_append_of_eq (by decide) catalog_complete_3448 block_083 rfl

/-- The exact complete prime catalog through this batch endpoint. -/
def catalog3672 : List ℕ := catalog3559 ++ [3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671]
/-- This catalog contains every prime through its endpoint, exactly once. -/
theorem catalog_complete_3672 : primeBlock 0 3673 = catalog3672 :=
  primeBlock_append_of_eq (by decide) catalog_complete_3559 block_084 rfl

end RiemannGaussian.RosserSchoenfeldFiniteBounds
