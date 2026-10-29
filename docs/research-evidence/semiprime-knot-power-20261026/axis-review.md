# Independent review: axis short factorial

26 October 2026. Read-only review of axis-shortfactorial.md; no experiments or repository edits.

**PASS, with the stated conditional scope.** The cyclic-dilogarithm identity and singular-quotient diagnosis are correct. The soft D^(2/5) branch is a genuine conditional smooth-order factoring algorithm on the cited prepared controller's survivor; it is not an all-order axis oracle.

## Coprimality is licensed by the actual cited interface

I checked the original pinned source, not merely the scalar catalogue's paraphrase:

`/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/uniform-setup-and-query-interface.md`

Its SHA256 is exactly `4c4efaba5c3a09dd4ca1a87801e44212d5fcd2570ff26ec5f193f71589ec0d46`, matching scalar-catalogue.md. Section 1 explicitly promises odd coprime beta orders >16k² and large q orders. Section 3 constructs beta=gamma^(N-1) and justifies coprimality: if g=gcd(P-1,Q-1), projected orders divide (P-1)/g and (Q-1)/g, which are coprime. Indeed gcd(P-1,N-1)=g, and similarly for Q. Its common-order-one branch supplies the short annihilator N-1 of the earlier gamma to the licensed extractor. Section 4 screens the actual beta^(k²). Sections 1–4 allow the supplied composite scale k and require neither the later prime-modulus catalogue nor a separate small-factor prefix.

Thus r=beta^k inherits coprime local orders and ord(r)>=ord(q)>16k². This is an existing classical algorithmic interface; the source explicitly does not claim automatic compiled controller/backend integration. The axis report should continue to identify that interface assumption, rather than infer coprimality merely from large odd orders. Its present explicit qualification does so.

## Algebra and endpoint checks

The horizontal tile is exactly the interval k+epsilon through k(m+1)+epsilon-1, length D=km. Because its start is positive and below either local order, a local zero occurs iff that order is <=B, with B the upper endpoint. Both local zeros are equivalent to global zero for squarefree N. This applies to the complete displayed tile, not automatically every pruned/vertical family; the report preserves this distinction.

For C_n(x)=product_(j=1)^(n-1)(1-r^j x)^j, shifting indices gives

    C_n(rx) product_(j=1)^(n-1)(1-r^j x)
      = (1-r^n x)^(n-1) C_n(x).

Multiplication by 1-x gives equation (3). At r^n=1, this reduces to C_n(rx)/C_n(x)=(1-x)^n/(1-x^n) where the quotient exists, exactly the integer-power form of Garoufalidis–Kashaev's Section 1.2 cyclic relation. I checked arXiv:1411.6062v2 (27 April 2015), equations (9) and the displayed functional equation following it: https://arxiv.org/pdf/1411.6062 . The arbitrary-r cleared identity does not need a primitive root or fractional powers.

For the actual x=r^(A+1), the short endpoint exponents A+1, A+D+1 and D are positive O(log N)-bit integers. A saturated gcd supplies beta^(k e)=1 with nonzero short k e, so the pinned short extractor is applicable. If the r^D-1 check continues with gcd 1, r is not a D-th root at either prime. Even unit endpoint checks do not guarantee C_D(rx) is a unit. Interior vanishing can make both sides zero, so division cannot acquire the missing product. The n=0,1 exceptions are correctly separated.

## Smooth-order branch and its exact success statement

Let y=ceil(B^(2/5)). The successive prime powers ell^floor(log_ell B) are each <=B. Sieving, modular powering and one gcd per prime cost soft O(y) operations, with the corresponding soft O(y log N) bit cost at residue size log N. Since B=Theta(km), m=Theta(k^(3/2)), y=Theta(k), this fits the target setup budget. It never materializes the wide integer E_y.

If a local order d<=B is y-smooth, then d divides E_y. At the first step killing either local order, simultaneous killing would require the newly introduced prime ell to divide both orders: neither was killed before, and that step changes no other prime valuation. Coprimality excludes this, so the gcd is proper. This proves the claimed conditional factoring guarantee even when the other local order exceeds B or is not smooth. It does not determine all order thresholds, and cannot be used to report a zero bit when the scan has no hit.

Without coprimality this argument fails, and the accumulated exponent can have soft O(y) bits rather than polylogarithmic length; a saturated accumulated-exponent branch is not automatically covered by the short-annihilator interface. The report correctly says so. On this actual controller survivor, however, that saturation is impossible.

After a no-hit scan, any d<=B must have a prime factor >y; it has at most two such factors counted with multiplicity because y^3>B. This is only a residual-order classification. It does not provide the remaining prime or two-prime search in soft k. The stated all-order division-free monic BSGS fallback remains soft sqrt(D), and its restriction/localization costs do not change that exponent.

No genuine algebraic gap was found. The limited positive result is: **on the explicitly cited coprime-order prepared branch, one soft-k scan factors N if either local r-order is <=B and B^(2/5)-smooth.** All remaining orders, full-family coverage and the general scalar norm remain unpaid by this candidate.
