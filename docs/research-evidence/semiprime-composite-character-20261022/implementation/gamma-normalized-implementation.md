# Original-gamma normalized aggregate reference

22 October 2026. `gamma_normalized_aggregate.py` and its separate test file import the reviewed aggregate and frozen PackedGauss via explicit `--repo-root`. Previously reviewed files are unchanged. Public inputs are N, ell, odd m|ell−1, and an explicit scalar unit t. The original scalar is gamma=t²; there is no root-extraction oracle. The reference does not certify any prepared-order property of t or gamma.

The core first handles gcd(t,N): a proper gcd returns PUBLIC_FACTOR; gcd=N returns SATURATED_PUBLIC_UNIT, accurately indicating the failed supplied-unit contract rather than manufacturing a factor. The imported core retains its separate known-prime screens for m and ell. All remaining formulas use certified units.

Using the paid U=−C_m and whole-algebra D, the new core acquires

    V=t^m U²D^(−m),  V^−1=bar(V)gamma^(−m),
    qh=V^m,          qh^−1=bar(qh)gamma^(−m²).

It outputs the three common W_s=qh^(−s), s=0,1,2, plus scalar descriptors gamma^(N+a_j),s_j. It actually acquires the whole vector gamma^(A+Nh)qh^(−S) and the weighted normalized quotient vector (V/gamma)^A. No target family or per-pair vector is expanded by the core. Nine normalized vector entries in the output (some intentionally shared/duplicated, such as W_1=qh_inverse) plus O(m) descriptors are accounted for; the imported base's constant number of old vectors is also paid. The test-only selected-pair expansion helper is not used in acquisition.

The separately exposed `ce_inverse(pg,E,coefficients=None)` handles ALL nonnegative E for ODD character order (including k=1). It explicitly rejects even order because the Gauss norm formula used here assumes chi(−1)=1. It acquires the standard E-th-power-trivial projector P_E, forms D_E=P_E+(1−P_E)ell, and returns bar(C_E)D_E D^(−E). This uses no generic polynomial inverse. If coefficients are supplied, they must be the actual C_E under the helper's documented contract. E=0, nonunit E modulo m, E divisible by m, and nontrivial proper-divisor character components all retain their exact correction. Negative E is rejected because the underlying quotient-acquisition API takes nonnegative exponents.

Theoretical cost is soft O(ell+m), retaining polylogarithmic N and parameter-size factors: a constant number of packed acquisitions/conjugations/vector powers, logarithmically many histogram passes for each requested C_E, O(m) scalar powers and row descriptors. A single helper inversion is also soft O(ell+m), or soft O(m) with actual C_E already acquired. This is the reviewed fast-integer algorithmic ledger, not a certified bound for Python/GMP runtime. With the independently audited ell-first composite supply it is soft O(N^(1/6)). Reconstructing a second public character table in the wrapper is another O(ell) term, not a hidden per-row setup.

## Controls and saved result

`test_gamma_normalized_aggregate.py` directly sums Gauss sums in small split fields, using known factors ONLY in the oracle. It sets h_a=t*g_a/g_-a, builds native targets h_1^ellrow h_j^a h_(j^-1)^N, and compares the actual acquired outputs. Thus the expected targets are not generated from the pair/whole formulas being tested. It checks trivial, primitive and proper-divisor character components, including composite m=9 and 15. The direct quotient inverse checks also compare against g_1^E/g_E, in addition to verifying the full cyclic coefficient product is one.

Saved `gamma-normalized-controls.json`: PASS. Four parameter cases, 72 whole and weighted component comparisons, 234 direct pair comparisons, including 20 proper-divisor components; 27 full-vector inverse checks and 498 inverse-component comparisons. Two proper public-factor controls, three t-saturation controls one rejected-negative-E control and one even-order rejection control passed. Maximum packed degree 14. These are exact convention/exception controls, not success-rate or coverage evidence, and no broad benchmark was performed.

Run:

    /path/to/plot-venv/bin/python test_gamma_normalized_aggregate.py \
      --repo-root /path/to/riemann/formal --json-out gamma-normalized-controls.json

The identities remove auxiliary amplitudes from the acquired UNIT aggregates and use the original explicitly supplied gamma. They do not compute H, target-minus-seed products, trace families, a same-leaf intersection, or a locator. No universal factoring-rate improvement is claimed.
