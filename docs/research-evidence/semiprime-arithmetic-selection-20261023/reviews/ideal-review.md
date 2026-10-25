# Independent ideal and real-cycle review

23 October 2026. Scratch only. **Pass after the two minimal convention
corrections recorded below.** No new recognition algorithm, class-group
bound, or all-input factoring improvement is claimed.

I checked ideal-short-cofactor.md and inspected the complete fixed replay
script. Root was already running that replay for the archive, so I did
not run it again. This review's replay conclusion is a code/convention
audit, not a claim of an additional independent execution. I also checked
the relevant local primary text: Lenstra sections 1-5 (including the
explicit strict/narrow convention), Gower-Wagstaff's proper equivalence,
reduction and ambiguity definitions, and Bradford-Wagstaff sections
2.2-2.5 and its positive-norm definition of principal ideals.

## Ideal integrality, primitivity, and signs

The order O_D=Z[theta], theta=(-b+sqrt(D))/2, is integral with
discriminant D. The identity alpha0=-(as+H theta) proves integrality
without an unjustified division by 2. For primitive g, I=(a,theta)
is invertible of norm a. Removing primitive content k is legal: k|a,B
and CN, gcd(k,N)=1, hence k|C; at the true witness k|sigma as well.
The nonsquare-discriminant screen excludes sigma=0. The new polynomial
remains primitive and its norm identities and size bounds persist.

The odd, unramified N-ideal n_R has norm N; 2 is invertible modulo N,
so its displayed sqrt(D) congruence correctly defines an index-N ideal
even when O_D has a half-integral basis. Containment of alpha0 in the
coprime-norm ideals I,n_R makes their quotient J_C integral. It is
invertible because it is a quotient of invertible ideals, and its norm
is |C|. The true alpha_h belongs to I and the stated oriented P-ideal;
P occurs exactly once in its norm since a,|sigma|<P. The same quotient
argument gives integral invertible J of norm |sigma|. The class relation
is correctly stated in the ordinary class group; its real narrow
version must retain the sign of aP sigma. No unproved unique
factorization into nonmaximal-order prime ideals is used.

## Two convention corrections applied to the report

1. Section 3 now explicitly says its equivalence and principality are
   proper SL2(Z) equivalence, hence narrow ideal classes for Delta>0.
2. Under Lenstra's oriented norm-form convention,
   (H,sqrt(delta)-B)=r_B^2 has norm form
   (H,-2B,DH)=G^{-1}, not G. The corresponding sentence was corrected.

The second correction changes no principal-class criterion. Indeed
r_B^4=(M,sqrt(delta)-B) has norm form (M,-2B,D), whose proper swap is
F=(D,2B,M). Thus [F]=[r_B]^4 in this convention, consistent with
G^2~F^{-1}. All ideal products are invertible because r is unramified
and split: delta=4aCN=4a^2 mod r is nonzero, and the selected B root
lifts simply to r^4. No maximal-order assumption is required.

The generator orientation in (7) remains **u+Bv=0 modulo r^4**.
An element u+v sqrt(delta) lies in r_B^4 exactly with that congruence.
Its positive norm r^4 makes its principal ideal equal to r_B^4 by
containment and equal index. In the real case positive norm permits
choosing a totally positive generator by changing its global sign;
negative norm alone would only prove ordinary principality. A generator
cannot have r|v, since that would also put it in the distinct conjugate
r-ideal. The stated primitive-v condition is therefore necessary and
consistent.

## Negative C and the fixed real-cycle certificate

For C<0 the centered even b' obeys 0<|b'|<H, and
c'>4a|C|N/H>1024H. Both G' and its inverse are distinct strictly
reduced positive-definite forms, proving non-ambiguity in arbitrary
quadratic orders. The direct norm proof agrees: v!=0 makes
u^2+4a|C|Nv^2>r^4; v=0 gives u=+/-r^2, which fails the oriented
r_B^4 condition. Ordinary versus narrow principality creates no escape
in the imaginary case.

The replay's rho operation is the stated proper SL2(Z) reduction.
Its integer predicate implements |sqrt(Delta)-2|A||<b<sqrt(Delta)
exactly, and every recorded cycle step rechecks discriminant and
primitivity. The first return traverses the entire reduced proper
class. Checking A=1 tests for the unique reduced principal form;
absence of it in F's complete cycle therefore proves narrow
nonprincipality. The ambiguity predicate matches the cited forms
A|b or A=C; the independent F-cycle certificate already suffices.
The script does not conflate ordinary equivalence with that proper
cycle. The fixed example refutes only automatic principality of each
true row, not existence of some other principal positive-C row.

## Final reviewed fingerprints

All paths are under /tmp/semiprime-arithmetic-selection-20261023.

* ideal-short-cofactor.md, after the two corrections:
  `b884eae5ddce1188a12ac963b60873d3387a369801fa0baba1dd3ea7eb5fd04d`
* replay_principal_square_premise.py, unchanged and not rerun here:
  `2dc008af1b7db31cde84afb6ec8a4df0f183ae3082ee2b8fe3cb395cb892b129`

No frozen or repository file was edited. Only the explicitly authorized
two convention sentences and this scratch review were written.
