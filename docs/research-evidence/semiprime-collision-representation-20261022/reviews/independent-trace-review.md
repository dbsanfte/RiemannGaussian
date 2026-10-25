# Independent review: weighted rational traces and native orbit representation

22 October 2026. Read `weighted-rational-trace.md` and `orbit-representation.md`. Verdict: PASS for the fixed-weight primitive, its claimed soft-m construction, and the explicitly limited native applications. This is a genuine new acquired mixed-power primitive. No formal backend, examples or source-file changes.

## 1. Resolvent identity and residue sign

Let A=(Z/N)[X]/(X^m-1), m odd, gcd(m,N)=1; gamma,t are units, t²=gamma, 1+gamma^m a unit. For canonical degree<m B, put g=X(X+gamma), h=g-zt(1+gamma X)=X²+cX+d, c=gamma(1-zt), d=-zt. Since X and X+gamma are units in A, the formal resolvent is exactly

    F(z)=Tr_A(Bg/h)=sum_(a>=0)Tr_A(BR^a)z^a,
    R=t(1+gamma X)/(X(X+gamma)).

Monic division Bg=hV+U gives deg V<=m-1 and U=U0+U1X. The trace of V is mV(0): every exponent1,...,m-1 has zero regular cyclic trace. At X=0, Bg has constant0 while h(0)=-zt, hence U0=ztV(0) exactly. This confirms the PLUS quotient term m*t^-1*(U0/z), and establishes z-divisibility without inverting z.

For the remaining sum, f=X^m-1 has f'=mX^(m-1). The rational differential U f'/(h f) has zero residue at infinity. Its residues on f are U(omega)/h(omega); on h they are U(beta)f'(beta)/(h'(beta)f(beta)). As f(beta)=-(1-beta^m), the two minus signs cancel in the residue theorem. A monic quadratic's dual coefficient functional is sum K(beta)/h'(beta)=[X]K. Therefore

    F=m*t^-1*(U0/z)+m[X](U X^(m-1)(1-X^m)^-1 modh)

has the reported POSITIVE sign. This identity can be cleared of resultant denominators and specialized universally. The production algorithm does not choose roots or invert a discriminant, so double roots under an unrelated specialization cause no unsupported division.

At z=0, h=X(X+gamma), and Norm_C(1-X^m)=1+gamma^m. The reported quadratic conjugate and norm formulas are exact. Scalar formal-series inversion has a checked unit constant coefficient. With prepared odd-order gamma, gamma^m is never -1 locally, so this unit condition is automatic; otherwise its scalar gcd is explicitly guarded.

## 2. Precision and actual soft-m acquisition

To output F modulo z^m, U0 must be known through coefficient z^m, hence U needs precision z^(m+1). The report correctly keeps this extra coefficient before the exact shift. The second resolvent term needs only z^m. One should not truncate U at z^m and then claim the final highest moment; that would lose it.

The balanced evaluation tree is a real algorithm for Bg modh, not a hidden generic division. For a block of s scalar coefficients, powers of X in the quadratic algebra have z-degree O(s); each balanced combine uses O(s)-length scalar polynomial arithmetic. There are O(m/s) such blocks at that level, so summed degree is O(m). Shared powers X^(2^r) require only a logarithmic squaring chain with geometrically growing degree. Consequently construction is soft O(m), with soft O(m) total stored level data. Computing X^m,X^(m-1), scalar norm inversion and the final products similarly uses O(log m) quadratic-algebra operations on length-O(m) series. Input B is one acquired m-vector and output is exactly m scalar traces, both O(m log N) bits. All coefficient arithmetic is reduced modulo N.

Thus the claimed fixed-weight sequence Tr(BR^a), 0<=a<m, is acquired in soft O(m) native bit work under fast scalar polynomial multiplication. The result survives composite odd m as well: regular cyclic trace is m times constant coefficient and X^m-1 is separable because gcd(m,N)=1. No prime-m field identity enters this primitive. This does not certify an interpreter's runtime or a quadratic multiplication backend.

## 3. Orbit-family identities and the new paid diagonal

The denominator-cleared family is correctly

    (X^j+gamma)(B-rho_j W)=(gamma B-t)+X^j(B-t gamma).

Its two arrays are acquired and denominators are units. The fixed-array matching/localization consumer is an inherited separate theorem; this review verifies that the family fits its algebraic input, not a new proof of that consumer. B=W^N is one paid vector, but the true Frobenius equality has unknown extra Q exponent, so this family alone is not native coverage.

The coordinate change X=(t-gamma W)/(W-t gamma) and its degree-m relation are correct; the leading scalar is -(gamma^m+1), a certified unit. The defect identity involving rho_(j²) and rho_a retains ordinary INTEGER powering; it does not erase its varying degree.

For b=cN modulo m, the selected power-piece identity is exact cyclic arithmetic:

    [X^b]rho_(j²)(W^a_j)=CT[(W/X^c)^a_j].

For c=1, the norm denominator is gamma^m+1 because m is odd and Norm(X)=1. If the quadratic h has roots beta1,beta2, its resultant against X^m-1 equals (beta1^m-1)(beta2^m-1)=p^m-S_m+1. Therefore the stated sign, constant Delta(0)=1 and logarithmic derivative -Delta'/Delta=sum_(a>=1)Tr(R^a)z^(a-1) are correct. To recover a<m, the listed precisions suffice; trace at a=0 is m. No division by a or a! is needed. All trivial and proper-order roots are included by the REGULAR trace.

The stronger fixed-weight theorem means a dense B is NOT itself an obstruction when it is truly fixed. Tr(BR^a) is now paid. This is an actual acquisition advance beyond unweighted trace or determinant coefficients.

## 4. Which native weighting remains unacquired

For the ACTUAL coefficient after rho_(j²), a=a_j and b=N modulo m,

    [X^b] B rho_(j²)(W^a)
      =CT[rho_(a/b)(B) R^a]
      =sum_k B_k CT[(X^(k/b)R)^a].

These equalities are correct, including cyclic wraps. They are NOT the fixed-B sequence just proved: rho_(a/b)(B) changes with a. Alternatively the sum requests many different slopes k/b, whereas the quadratic resolvent pays one fixed rational R. In addition the full corrected source retains its ell_j-dependent power/permutation. Neither a full native diagonal nor its collision query follows from the fixed-weight primitive. The report states this limitation accurately.

The discussion that nontrivial x cycles through all m roots as k varies assumes PRIME m, as stated at the beginning of orbit-representation.md. Under the new composite selector a root of proper order d cycles through d roots with repetitions. Do not import that particular prime-root denominator description unchanged. It does not affect the weighted primitive, and the primitive can be safely used for composite m as described above. Similarly the scalar-wrap comparison's binomial pivots are units under retained hidden primes>16m²; gcd(m,N)=1 alone would not certify every such coefficient for arbitrary small N.

## 5. Source and recovery limits

No trace equality is promoted to whole-local-algebra equality or same-leaf paired support. The native whole-local source and original scalar decoder remain necessary. A varying-weight sum, low-degree carrier equation, or determinant denominator is not the missing acquired numerator. Formal scalar-parameter differentiation cannot preserve a finite-field Frobenius identity without a separate source theorem; the report's warning is correct.

Overall: the fixed arbitrary-weight rational trace algorithm is mathematically sound and genuinely soft-m, with exact precision and unit safeguards. The unweighted native power-piece diagonal is paid; the automorphism-varying weight and ell_j factor are the precise remaining contraction. This review supplies no full collision-query or rate claim. The positive-kernel decision gap is likewise not counted as a complexity gain by itself.
