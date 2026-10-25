# Whole unit Gauss aggregate reference implementation

`composite_gauss_aggregate.py` loads the frozen `PackedGauss` ONLY from the supplied `--repo-root` plus the repository-relative reviewed path. It neither alters the dependency nor requires hidden factors. Its public input is N, prime ell, and any odd m>=3 dividing ell−1. The chosen ell=2m+1 case and general odd-order case are both supported. It screens every prime divisor of m and ell separately, returning an explicit PUBLIC_FACTOR outcome; a composite semiprime cannot saturate these individual prime screens.

The core actually acquires U=−C_m, D, D^−1, E0, three W_s=U^(−ms), the whole unit-target product U^(−mS)D^(A+Nh), and the weighted quotient product U^A D^(−A). It records A,S,h and unit pair descriptors. U^−1 is acquired as bar(U)D^(−m), retaining the trivial component. Each pair is represented by

    delta_s E0 + ell^(a+N)(W_s−delta_s E0), delta_s=(−1)^s.

No per-pair vector is expanded in the core. Nine length-m output vectors and O(m) row/scalar descriptors are output. The explicit `expand_pair_for_test` helper is used only in controls; expanding every pair is not part of the near-linear claim. Rows were independently cross-checked against the coordinated `composite_colours.canonical_rows` on their common fields.

`test_composite_gauss_aggregate.py` uses small known split field primes only as an independent oracle. It directly sums the additive/character Gauss sums in those fields, and constructs native T_j as g_1^ellrow g_j^a g_(j^-1)^N. This is algebraically the corrected target, since the g_(N/j) factor cancels the denominator of rho_(j^-1)(C_N). Hence the oracle tests actual character components without constructing targets from the asserted pair or whole-product formula. It includes the trivial character, primitive characters, and nontrivial proper-divisor characters for composite orders 9 and 15. It also checks the weighted C_j product independently. Four parameter cases are conventions/exception checks, not success-frequency evidence.

Run:

    /path/to/plot-venv/bin/python test_composite_gauss_aggregate.py \
      --repo-root /path/to/riemann/formal --json-out aggregate-controls.json

The saved run passed: 72 character-component whole and weighted comparisons, 234 direct pair comparisons, including 20 proper-divisor components; four primewise public-factor controls and three invalid-input controls. Maximum packed degree was 14. The N=3*5,m=15 control specifically checks the case where a combined gcd would saturate but separate prime screens return a proper factor.

The reference arithmetic follows the reviewed quasi-linear byte-Kronecker cyclic convolution primitive. Acquiring C_m takes logarithmically many O(ell) histograms and quasi-linear length-m convolutions. Constant-many signed vector powers use the paid conjugate inverse; O(m) row/scalar powers have O(log N)-bit exponents. Thus theoretical bit cost is soft O(ell+m), conditional on the already supplied prime/character metadata, or soft O(u) with the composite supply sieve proved in the adjacent report. This is an algorithmic bit accounting, not a certified Python/GMP timing bound. Trial division/public primitive-root search in the frozen constructor stays within soft ell. No broad benchmark was run.

Scope: unit aggregate and three-vector shared pairs only. The code does not acquire H, target-minus-seed products, their traces, a universal factor, or a factoring-rate improvement.
