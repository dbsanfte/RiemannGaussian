# Independent review: arithmetic selector and revised Schur boundary gate

26 October2026. Bounded paper audit; no tests or source/repository edits. **Scoped PASS** for arithmetic-selector.md and the revised cyclic-reciprocity.md Section6. No soft-k residue supplier is established.

## Exact lift and affine image

Writing P=j+ku,Q=c+kv and D_N=(N-jc)/k gives D_N=jv+cu+kuv exactly. With a=kt+cb and delta0=2kC-N, direct expansion yields BOTH equivalent expressions

    h=Cb-((P-1)/2)*(bv-t)
     =[a(P-1)+b(Q+delta0)]/(2k).

The first formula proves integrality without modular division. Since k=2R, (P-1)/2=s_j+Ru. Modulo R this gives h=Cb+s_j(t-bv), and D_N=jv+cu modulo R gives the printed alpha and gamma with the correct positive gamma sign. All modular inverses concern known3-units. When j=2 mod3 and3 does not divide b, gamma is a unit and the necessary congruence image is the whole Z/R by a bijection in u. The report explicitly does NOT assert that all these formal lifts are actual prime divisors or actual proof vectors for one N.

For a nonunit gamma the exact image is alpha+gcd(gamma,R) Z/R, equivalently the printed3-adic valuation class (with v3(0)=infinity). The omitted2-primary bookkeeping does not secretly shrink the3-primary image. Complete affine-coset aggregation partitions the original h interval and returns its original one-row product, including its literal omission. No new coverage restriction follows.

The symmetric beta equality is correct, but the rough-order statement is CONDITIONAL. The current native kernel interface is not assumed rough. On a genuinely rough branch, the claimed quotient-character obstruction has the correct direction: x modR descends from exponents modulo a cyclic order r only if R|r, not when gcd(R,r)=1. This is not used as an unconditional arithmetic or discrete-log lower bound.

## Finite cancellation valuation and supplied-order count

For f_e(epsilon)=1-(1-epsilon)q^e, at a local prime its epsilon valuation is exactly1 when ord(q)|e and0 otherwise. Products therefore count all local collisions with multiplicity, including literal factors until those are explicitly removed. Taking valuations in the cleared finite rectangle identity yields the displayed MIXED DIFFERENCE of counts; puncturing adds the translated deleted-factor corrections. The report correctly does not presume these valuations available modulo N or identify a boundary count with the covered bulk count.

For supplied exact local order d, the floor difference counts multiples of d in[Cb-T,Cb+T] exactly, including negative endpoints. Summing over b is an ordinary affine floor sum. Euclidean floor-sum evaluation has polynomial logarithmic bit cost; subtracting the known literal-zero count gives the punctured count. Subinterval counts allow binary selection and then a nonzero multiple in the selected interval. This is not a new supplier: q^d-1 already yields a proper gcd or a saturated nonzero short annihilator. Its exact inherited recovery cost is T_ext=soft O(N^(31/192)), once, not polylogarithmic merely from label bit length.

## Revised cyclic-reciprocity Section6

The unbalanced partition lambda_i=A+(C-1)(r-i),i<=r has the stated Weyl cross-block exponents A+C(r-i)+(j-r). Thus the cleared identity(10), including q^n(lambda), is correct. The complete-symmetric Gaussian identity gives D_n*h_d=(q^(d+1);q)_(n-1); d_ij and all interval endpoints are correct. Their row intersection is exactly[A+Cb+1,A+Cb+s], yielding H=diag(Z_i)U without division, and each U entry has exactly r-1 endpoint factors. Its full array costs soft r²=soft k to acquire.

The formal cancellation giving(13) is valid BEFORE specialization. For exponent d<s, its net power in D_n^r V_s/V_n is0; at d=s it is0; at d=s+t,1<=t<r, it is t. Consequently

    det U=q^n(lambda)*V_r(q^C)
                       *product_(t=1)^(r-1)(1-q^(s+t))^t

is an actual division-free polynomial identity, including all composite-ring collisions. The r=2 sign and monomial check agree with q^A(1-q^C)(1-q^(s+1)). No unit assumption on the long D_n or V_n was used in this FORMAL cancellation.

Hence acquiring and screening det U needs only O(r) actual factors,1-q^(Cd) and1-q^(s+t), with positive nonzero exponent labels HCd and H(s+t). A nonunit is a legal factor/extractor event; on continuation det U is a known unit. This costs soft(r+T_ext), and there is NO need to screen the entire q-prefix through n-1 for this boundary gate. This does not itself discharge an independent b=0/full-coverage clock screen, nor does a unit determinant certify every leading elimination pivot or give an uncharged inverse action.

On the unit-gate branch det H has exactly Zpos's local zero/nonunit predicate. H's diagonal Z_i factors are still the original long products; the acquired U does not initialize them. The report distinguishes this from recovering the Schur value by dividing by possibly nonunit D_n. The retained soft(r+sqrt(rs))=soft N^(1/4) completed readout and the absence of a target-rate claim are correct. This is a real paid boundary-core handoff with an honest remaining implicit diagonal, not an evaluated full matrix norm.
