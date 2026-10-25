# Selected readout: a new deterministic structured-solve contract, with its input exposed

24 October 2026. Scratch only. A March 2026 primary theorem removes the randomized generic-rank prerequisite for several supplied-generator linear-system problems. Its exact specialization below is valid but does not acquire the native two-cofactor readout faster. No alternative cheaply initialized generator was obtained in this pass. No query or factoring exponent improvement is claimed.

## New primary theorem and actual supported operator

Sara Khichane and Vincent Neiger, *Matrices with displacement structure: a deterministic approach for linear systems and nullspace bases*, arXiv:2603.02425, submitted 2 March 2026:
https://arxiv.org/abs/2603.02425
https://arxiv.org/pdf/2603.02425
Cached `sources/khichane-neiger-2026.pdf`, SHA256 `6f8256f25eeb11c1dc3b67e8f91bd1c58b8c3f40f2261c5c268738fb7e51b4bf`.

Theorem 1 and Theorem 25/Algorithm 3 solve a system and describe its nullspace deterministically over an arbitrary effective FIELD from supplied displacement generators G,H and right-hand side. For the Toeplitz-like case the operator is exactly Delta(A)=A-S_(m,0) A S_(n,0)^t. The bound is

    O(alpha^(omega-1) [M(m) log m + M(n) log² n])

field operations; no generic rank profile or random preconditioner is required. Vandermonde/Cauchy cases have their explicit distinctness/disjointness assumptions. The paper does not silently include every cyclic Sylvester operator; p3 expressly distinguishes possible extensions. The actual nilpotent Stein specialization below avoids that issue.

## Execute on the native regularized Bezout matrix

Use the old actual setup in `/tmp/semiprime-quotient-gradient-20261024/weak-readout.md`, SHA256 `6d324cd99fa32427de877666e82fb67cc60c857c49e2eecbaa9ad2526e1d9bd1`: F is monic degree J, G is the monic geometric-root polynomial of degree L, h=G mod F, K=Bez(F,h). Let f be the length-J vector of lower coefficients of F, R reversal, S lower nilpotent shift, and e0,e_last the first and last coordinate vectors. For J>=3 put

    D=(K+e0 e0^t) R.

The old identities SK-KS^t=f h^t-h f^t and K e_last=h give the EXACT new operator conversion

    D-SDS^t
      =h(e0+SRf)^t-f(SRh)^t+e0 e_last^t.          (1)

Indeed set D0=KR. Then SD0-D0S=(f h^t-h f^t)R, use SS^t=I-e0e0^t, and add the Stein displacement of e0 e_last^t, which is itself. Thus (1) is a supplied rank-at-most-three generator for precisely the paper's operator, with no unverified conversion or spectral separation. Its coefficient arrays cost soft J ONCE h is actually supplied. J<=2 is handled directly as a fixed-size case; for J>=3 the three supplied columns satisfy the theorem's alpha<=J input bound.

Solve Dz=e0 and set x=Rz. At a simple unique common root V, the old kernel calculation gives (K+e0e0^t)(1,V,...,V^(J-1))^t=e0, so a tag interpolant w gives the desired weak tag w^t x locally. This is the pre-existing unit-regularized consumer, not a newly acquired cofactor. All J output coordinates fit soft J.

Crucially, the FIRST COLUMN of the left side of (1) is exactly h: S^t e0=0 and D e0=(K+e0e0^t)e_last=h. Therefore providing an arbitrary explicit generator for THIS matrix, not just the displayed factorization, permits recovering h in O(alpha J) operations. A short q-product circuit is not this generator input. This is a statement about this particular proposed interface, not about all structured representations or selected-output algorithms.

Current zero-safe acquisition of h costs soft(J+sqrt(JL)); the deterministic structured solve afterward costs soft J. Once h is known, the pre-existing guarded polynomial gcd already locates the unique root in soft J, so the new solver is not an additional query advance. Replacing its generators by acquired short coefficient ends has not been shown to preserve the matrix or its local tag kernel.

The effective-field hypothesis is not a blanket obstruction to a composite adaptation. In the actual quadratic algebra with Jacobi(D,N)=-1, at least one local component is a field. Classify each encountered coefficient: invert unit norm; a proper norm gcd factors N; if norm is zero modulo N, the field-side element is zero, and either a coordinate gcd factors N or both coordinates are globally zero. On a no-factor trace this distinguishes global zero from units and makes the field-algorithm branches valid in every simple component. This supplies the usual guarded adaptation at logarithmic bit cost per field test; it still requires the complete actual generators. No unknown local field is supplied as input.

## A tempting 2025/2026 circuit lead has an explicit gap notice

Andrews, Kumar and Rai, *Modular composition & polynomial GCD in the border of small, shallow circuits*, ECCC TR25-171:
https://eccc.weizmann.ac.il/report/2025/171/
Original PDF cache `sources/eccc-2025-171.pdf`, SHA256 `6bc58fb6ea165c5704396d52675f35cd601cda11a792dfc23c2d01b0f85b7139`.

The PRIMARY report landing page's revision #1, dated 28 January 2026, explicitly announces a gap in Theorems 6.2 and 6.4 and says all results rely on those theorems. The downloaded original PDF's apparent small border-resultant/composition claims are therefore not used. Landing page cached as `sources/eccc-2025-171-status.html`, SHA256 `8d528c7c854902770154a27214d9a5855b6ac6053225a4701ccf0ae3ec596ae1`. Independently of that gap, a border circuit from explicit coefficient vectors is not already a finite exact composite-ring selected-coefficient evaluator.

This pass records these two genuinely new source contracts and the fully initialized Stein-generator conversion. Earlier q-holonomic blocking, q-suitable search oracles, analytic gamma products, explicit-array spiroids, formal composition, and circuit-GCD results are prior audits and are not counted again. The original covered degree-J query and its restrictions/witness recovery remain unchanged.
