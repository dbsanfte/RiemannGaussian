# A zero-safe reduction from the two gradients back to the scalar product

24 October 2026. Scratch mathematical report. The executed candidate is to acquire only the two unweighted first derivatives of the geometric product. There is an exact two-call reduction back to the full scalar product, using only the public unit q^L-1 and softly linear extra work. It applies to a uniform gradient interface, and also to the actual native family if the interface supports one common q-shift and the stated boundary checks. This is a useful completed interface reduction, not a faster endpoint algorithm or a general complexity lower bound. The retained executable query costs soft(J+sqrt(JL)); no whole-cost improvement was obtained here.

## 1. Actual input and the candidate

Let B be the acquired commutative quadratic algebra over Z/NZ. The same identities hold over any commutative ring. We have a unit q with 1-q^r certified units for 1<=r<=16H, H=k², L=3H+2, and an acquired monic F of degree J>=2, with separated unit roots and retained native labels. Set

    E(F)=prod_(0<=i<L) F(q^i),
    T_s(F)=sum_(0<=i<L) q^(si) prod_(r!=i) F(q^r), s=0,1.

They are the two coefficients in

    prod_i [F(q^i)+e+h q^i]=E(F)+e T_0(F)+h T_1(F),
    e²=eh=h²=0.                                      (1)

The preceding packet supplies the initialized state (A,T0,T1)=(1,0,0), with step (F(x)A,F(x)T0+A,F(x)T1+xA). That exact zero-safe execution is credited to cofactor-contraction.md, not claimed anew. Its two derivative outputs suffice for the validated unique-hit consumer. The candidate tested here is whether computing ONLY those outputs, without the scalar component, gives an easier uniform operation. The following exact reduction identifies the additional closure contract required for that strategy.

## 2. The two-call identity, including all zeros

Write F_q(X)=F(qX), a=F(1), b=F(q^L). Then

    (q^L-1)E(F)
      =a [q T_1(F_q)-T_0(F_q)]
                        +b [T_0(F)-T_1(F)].          (2)

In particular neither a nor b is inverted.

Here is a proof over the UNIVERSAL polynomial ring, so no field, nonvanishing or cancellation assumption is hidden. For arbitrary coefficient variables of F and deformation variables u,v, shifting the finite product gives the exact identity

    (F(1)+u+v) E((F+u+vX)_q)
       =(F(q^L)+u+v q^L) E(F+u+vX).                 (3)

The constant deformation coefficient of E((F+u+vX)_q) is T0(F_q), while its linear deformation coefficient in v is q T1(F_q). Taking the coefficients of u and v in (3), respectively, gives

    a T0(F_q)-b T0(F)=E(F)-E(F_q),
    q a T1(F_q)-b T1(F)=q^L E(F)-E(F_q).

Subtract the first equality from the second. This is (2), with NO cancellation of a, b, E or any hit factor. Thus it specializes to every zero pattern in B, including E=0, and even to rings with nilpotents. Dividing only by the already certified unit q^L-1 yields the desired scalar.

If the gradient routine requires MONIC input, supply

    F_tilde(X)=q^(-J) F(qX).

It is acquired by scaling J+1 coefficients and has unit-separated roots V_j/q. Homogeneity gives

    T_s(F_q)=q^[J(L-1)] T_s(F_tilde),  s=0,1.        (4)

This exponent follows from the L-1 factors in EVERY omitted-factor summand, rather than L factors. The concrete algorithm is therefore:

1. Acquire a,b by evaluating F at 1,q^L, acquire F_tilde, and compute the public q powers and inverse (q^L-1)^-1.
2. Obtain the exact pair (T0,T1) for F and for F_tilde; a proper factor returned by either routine completes the factoring branch instead.
3. Rescale the second pair by (4) and apply (2).

All supplementary work is soft J ring/bit work at the packet's logarithmic coefficient sizes. Two gradient calls of cost C(J,L) give a scalar E call of cost soft(J+C(J,L)), with no expanded L-vector, no q-factorial start and no result-dependent division. This is an actual initialized reduction, not an oracle that supplies its own missing inputs. It does NOT compute either gradient pair in soft k by itself.

## 3. Native one-shift closure and original witnesses

A routine valid for arbitrary separated F automatically accepts F_tilde. A routine proved only for the exact original native rows does not automatically have that closure. It must explicitly support the common scaling V_j -> V_j/q, equivalently the same original rows on the shifted interval 1,...,L, and return the actual gradients, not merely an unspecified successful ratio. Unit separation and the q guards are preserved by this scaling; native membership and any other denominator conditions remain part of its contract.

On the actual branch with F(1) and F(q^L) certified units, an original unique hit I in [0,L) satisfies 1<=I<L. The shifted query has exactly the same local hit, at new index I-1; no old endpoint is lost and no new hit enters at L. Its label is still the original row, and any located new index i maps to original index i+1. A hypothetical shifted-query consumer must honor this map. The auxiliary value F(q^L) is screened as a coefficient value; a nonunit there is not silently sent to the old [0,L) leaf decoder. Proper norm gcds are already factors; otherwise an unverified boundary can cause optional decline.

For completeness, the actual smaller-nonsplit native inequalities strengthen the availability of this boundary branch. For a repaired minus row let

    1<=a_j<2k,  -9H/2<ell_j<H/2,
    P<=k³,  Q<H²/16,  P,Q>16H.

At this prime the odd scalar and torus orders divide P-1 and P+1, respectively, are coprime, and each exceeds 16H. Their product R exceeds 256H². The same local exponent congruences used in the existing unique-hit proof imply at ANY candidate index i under discussion

    R divides K_i=a_j P+Q+ell_j-H i.                (5)

At i=0, we have 0<K_0<3H². At i=L=3H+2,

    -3H²-13H/2 < K_L < -15H²/16-3H/2 <0.

For H>=1 both nonzero magnitudes are below R, contradicting (5). Hence no native minus row hits either endpoint 0 or L at the smaller nonsplit prime. Both F(1) and F(q^L) are therefore units at that local field; their B/R norms are nonzero there. Screening either norm returns a proper factor or a global unit, NEVER saturation on a continuing good orientation. Wrong orientations may still decline. This proof uses the actual original rows and inequalities; it does not assume a bound for arbitrary added roots, arbitrary shifts or all larger intervals.

Consequently a gradient algorithm established on this native family AND its one common q-shift cannot infer a uniform cost advantage merely from omitting E: (2) computes E at the same asymptotic cost on the continuing good branch. Conversely this is not a lower bound and does not rule out a native algorithm exploiting further structure, or an output contract weaker than the exact pair of gradient values. The orientation palette's QRH premise remains exactly its previously stated conditional premise.

## 4. Forward differentiation: exact circuit contract and attribution

A straight-line circuit computing E for arbitrary nearby independent coefficients can be run in the rank-three algebra in (1). Every operation costs a constant number of B operations. For an intermediate unit a+e b+h c the inverse is

    a^-1-e b a^-2-h c a^-2.

Thus a division-free circuit, or one whose actual divisors are certified units, gives the gradient pair with constant overhead and soft J input initialization. Data-dependent branches must be frozen on a branch with a valid formal identity in the independent deformation variables. A native-only routine that happens to output the correct scalar at its valid points cannot automatically be differentiated off that native set. The full product or a state entry cannot be inverted at a collision. These are the previously established AD guards, retained here rather than weakened.

Primary attribution: Walter Baur and Volker Strassen, *The complexity of partial derivatives*, Theoretical Computer Science 22 (1983), 317–330:
https://doi.org/10.1016/0304-3975(83)90110-X
https://web.vu.lt/mif/s.jukna/tropical/Baur-Strassen.pdf

The paper assumes an infinite field and rational functions. Theorem 2 counts additions, scalar multiplications and other multiplications/divisions, and gives a constant-factor simultaneous derivative bound (at most four in the total-operation measure). This is already cited and audited in terminal-literature.md; it is NOT a newly discovered fast resultant theorem. Its generic independent-root resultant lower bounds are not transferred to these native inputs. The elementary square-zero lifting above, not an unsupported application of the field theorem to an arbitrary ring, supplies the composite-ring forward operation. The NEW identity (2) is proved directly in Section 2 and does not rely on AD complexity bounds.

## 5. Executed cost and the remaining algorithmic task

Apply (2) with the actually available polynomial-matrix gradient evaluator: build degree-Jb blocks, evaluate all L/b giant starts, process the clipped tail, and apply the supplied initial vector. Both calls cost soft(Jb+L/b+J); choosing dyadic b near sqrt(L/J) gives soft(J+sqrt(JL)), or soft k^(3/2). The scalar component could of course already have been retained in this evaluator, so the reduction does not improve that particular execution. It establishes that a future uniformly faster exact-gradient routine, with the stated shift closure, also supplies a faster scalar product through zeros. It must still acquire its own implicit block contractions or exploit actual native F structure.

The tempting alternative of taking the pole ratio of sum_i 1/(F(q^i)+epsilon) and sum_i q^i/(F(q^i)+epsilon) was also checked. At a unique local zero the residues are 1 and q^I, but their acquisition at epsilon=0 would require handling the original nonunit denominators. Short moments at epsilon=infinity or a formal analytic residue notation do not supply those residues. This is the old homotopy initialization gap and is not counted as a new result here. No additional negative certificate family is needed to state the actual target: a faster, zero-safe application of the acquired product or its gradient blocks remains unacquired.

## Exact inherited and primary pins

- ../semiprime-cofactor-recurrence-20261024/cofactor-contraction.md: e4100f7c507a1f3a894b9c9285425b942f086f0080e3f2ef51bd2b0aa7838ee0.
- ../semiprime-norm-sharing-20261024/implicit-evaluation.md (local minus-one proof): 5600980cbd17a37e09c79ed9503766cd081df9753bf8593443cc66bc0d4c0646.
- ../semiprime-zero-query-20261024/native-pairing.md (native labels/inequalities): 06548c974c61d9922a4ec6c2f41ba1c95d7dfcbb92442b3b2e5ceff984cd8016.
- ../semiprime-terminal-recurrence-20261024/terminal-literature.md supplies the prior AD audit; no frozen source is edited here.
- sources/baur-strassen-1983.pdf: SHA256 828e8c9eb30af0089c48b1a5bcac3990bc0e21d3b68d4e343490b0fdaa38ecae, matching the earlier audited cache.
