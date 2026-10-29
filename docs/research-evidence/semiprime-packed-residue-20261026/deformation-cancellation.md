# Noncovariant clock differentiation: a bulk-retaining contiguous identity

26 October 2026. Scratch paper derivation and exact symbolic execution, no repository changes. The two differentiated shifts DO retain the required interior residue; their exact initialized execution still costs the old soft K^(5/4). No general impossibility or new fast supplier is claimed.

## 1. Full finite parameter identity before differentiating

Keep the ORIGINAL beta-coupled weighted bank and constant canonical weights w_j, either [j²]_n (M1) or L+[j²]_n (packed C). Introduce INDEPENDENT formal parameters T,r,s and define

 G_h(T;r,s)=prod_(i=0)^(h-1)(1+s-T*r^i).

Everything below is an identity over integer Laurent polynomials, specialized only after clearing denominators. No analytic logarithm, infinite q-product or derivative of an unidentified native lift is used. Define logarithmic rational derivatives

 A_h=T*(partial_T G_h)/G_h,
 B_h=r*(partial_r G_h)/G_h,
 D_h=(partial_s G_h)/G_h.

The full contiguous identity is

 (1+s-T)*G_h(rT;r,s)=(1+s-T*r^h)*G_h(T;r,s).           (1)

Thus both row and clock differentiation are lawful before native specialization. The chain rule for the left argument rT matters. Write e_i(T)=T*r^i/(1+s-T*r^i). Differentiating (1) gives

 A_h(rT)-A_h(T)=e_0(T)-e_h(T),                        (2)
 B_h(rT)+A_h(rT)-B_h(T)=-h*e_h(T).                  (3)

Also direct homogeneous differentiation of EACH finite factor gives

 A_h(T)+(1+s)*D_h(T)=h.                              (4)

These are rational identities with universal cleared versions; a collision denominator is never inverted numerically. Equation (3) contains the extra A term absent from a covariant row/clock shift. Omitting it would erase the entire potential gain.

## 2. Differentiate first, then take the singular residue

Now specialize r=rho, s=delta and the acquired T=T_j. Each row has at most one clock hit in each component. At a row hit at clock I,

 Res_delta D_h=1,   Res_delta A_h=-1,
 Res_delta B_h=-I.                                 (5)

At no hit all three residues vanish. In particular no clock cofactor amplitude remains in (5); this is the actual count/clock-position moment, not the Lambert c_I substitute. Weight by the canonical integer w_j and sum rows. Let C_h(T)=Res D_h, J_h(T)=-Res B_h. Equations (2)–(3) imply

 C_h(rho T)=J_h(T)-J_h(rho T)+h*1_(T*rho^h=1).       (6)

When the two endpoint leaves are certified units, C_h(rho T)=C_h(T), and the interior count is exactly the difference of the two clock-weighted residues. Thus TWO shifts with different Euler derivatives really can retain an interior coefficient. This is not a claim that all shift methods reduce to endpoint information.

A direct term check fixes the signs: if T*rho^I=1 and 1<=I<h, the shifted row has clock I-1. Then J_h(T)-J_h(rho T)=I-(I-1)=1. If the only new hit is the endpoint I=h, the difference is -(h-1) and the correction h restores one. At I=0 the original hit exits and (6) is zero. These three cases verify every possible finite-clock contribution, including endpoints. Weighted sums preserve the identity even when many rows hit.

The direct unknown readout is now the correlated difference of two CLOCK-EULER residues in (6), not the whole rational function B_h. This is a potentially useful alternative acquisition target. It is algebraically equal to the desired count plus the displayed cheap endpoint correction; that equality alone is not scalar acquisition credit.

## 3. Actual tangent-ring initialization and full cost

There is an honest finite algorithm for all terms, with no symbolic clock array. Run the existing shared division-free product engine in the fixed-rank tangent ring with r=rho*(1+epsilon), s=delta, epsilon²=delta²=0 (retain the mixed coefficient if needed). Starts T_j are held fixed as formal independent inputs. Binary powering of r automatically supplies the factors i in r^i=rho^i*(1+i*epsilon). The engine uses monic operations and certified base inverses; no inversion of an unknown mass is introduced by this deformation.

This acquires G_h(T_j), its regulator derivative gamma_j, and its clock derivative beta_j jointly in

 soft(J+sqrt(Jh))=soft K^(5/4).

Here gamma_j=h*G_h(T_j)-T_j*G_h'(T_j), while beta_j=(r partial_r G_h)(T_j) at fixed T. The derivative inputs and all starts are therefore actually initialized; no J*h list of i-weights is emitted.

At a globally zero row, gamma_j is a global unit by the one-hit-per-row clock guard. Directly beta_j/gamma_j=-I componentwise. Norm/coordinate classification factors or permits this inverse. At a unit row the residue is zero. All weighted clock moments and counts can thus be computed with constant extra jet rank AFTER that acquisition. Performing the same run on starts rho*T_j doubles the row count by only a constant factor. Original endpoint values are acquired directly in soft J. A globally saturated endpoint remains an ACTUAL labelled leaf and can use its existing two-coordinate decoder; an arbitrary additive cancellation in (3) cannot.

Equation (6) therefore has a complete finite implementation, but it has not shortened the expensive acquisition. Counts from ordinary zero/unit row flags are already cheaper in constant factors after the same G values are known. The clock-derivative route is useful as an exact bulk-retaining decomposition, not as an asserted better baseline.

## 4. Execute residue-compatible clock multisection

A concrete attempt to advance the new clock-weighted residues jointly is to split the clock into a residue a modulo b and a block index k. Write h=b*m+r0, 0<=r0<b. BEFORE taking derivatives,

 G_h(T;r,s)=prod_(a=0)^(b-1) G_(m+1_(a<r0))(T*r^a;r^b,s).    (7)

This is an exact finite multiplication law. For each sector, the clock Euler operator on the original r is

 r partial_r = a*(T' partial_T')+b*(r' partial_r'),
 T'=T*r^a, r'=r^b.                                   (8)

Equations (7)–(8) retain every carry, remainder sector and endpoint. On residues they recover the exact label I=a+b*k rather than just a residue class. No root of unity is adjoined and no finite characteristic factorial is inverted.

Two direct executions can now be charged. Emitting all sector starts costs J*b, even though each is binary-power acquired; separately processing all sectors does not make that free. Alternatively use common baby blocks of length b and h/b giant anchors per row, avoiding explicit whole-sector arrays. The standard shared monic engine has work

 soft(b+J*ceil(h/b)+J),

including the short last block, fixed-rank tangent coefficients, and MPE. The choice b around sqrt(Jh) gives the existing soft sqrt(Jh) bill. This counts all emitted coefficients and anchors; it does not yield soft K for J~K,h~K^(3/2). Replacing B_h by the correlated difference (6) does not cause the sector anchors in this executed algorithm to cancel before acquisition.

This is a scoped cost computation for the actual multisection/tangent algorithm, not a claim that a different joint scheme must emit those arrays. In particular the paid coefficient-Cauchy actions might support a future correlated scalar contraction that bypasses their emission; none is supplied here.

## 5. What the decomposition changes

Pure covariant shifts erase the interior count. Noncovariant clock differentiation changes that fact: (3)–(6) explicitly retain it as a difference of first clock moments, with only original finite endpoints added. This opens a specific acquisition option: compute that correlated clock-Euler difference directly, with constant integer amplitudes and correct empty-row zeros. It does not require a full resolvent or all individual clock indices.

The exact experiments above include the chain-rule term, the homogeneous identity, all endpoint cases and an initialized fixed-rank tangent execution. Their currently completed cost remains K^(5/4). Further cancellation must occur INSIDE the correlated acquisition of B_h(T)-B_h(rho T), not by dropping an unknown bulk or assuming its selected residue is regular. No broad lower bound follows from this attempt.
