# Decomposing the selected long-query residue

26 October 2026. This packet follows the user's request to decompose the
long query into forms admitting cancellations or shortcuts. It also matches
the previously unidentified scalar to the supplied
[six-domain report](../semiprime-six-domain-acquisition-20261026/README.md).

**Several cancellations are exact, but no cheaper whole-family acquisition
has been proved.** The completed query algorithms here still cost
`soft O(K^(5/4))`. The constructive change to the hybrid is a weaker output
requirement: one unnormalized canonical colour moment suffices. The
guaranteed all-semiprime sixth-rate goal and its full bit proof remain open.
These are paper proofs and symbolic checks, not Lean theorems.

## 1. Smaller sufficient target

Keep the ORIGINAL beta-coupled family, its one row per unit colour, and all
preparation/coverage contracts. Write

    K=2*3^e, e>=3, H=K^2, n=3^ceil(e/2), D0=3^floor(e/2),
    u_j=[j^2]_n as a CANONICAL INTEGER,
    a_ji(delta)=1+delta-T_j*rho^i, 0<=i<h=O(K^(3/2)).

The side report's packed coefficient is

    C=Res_delta sum_(j,i) (K/2+u_j)/a_ji(delta).

Its consumer passes independent review. There is also a simpler sufficient
output:

    M_r=Res_delta sum_(j,i) u_j^r/a_ji(delta), ANY ONE fixed r=1,2,3.

At the nonsplit prime in a correct bin, `M_r=d*u^r` with `1<=d<=D0` and
`u=[R^2]_n`. This is a positive integer below `D0*n^r<=3K^2/4`, hence
below both primes. Recover that small integer by the existing blocked
modular search, factor the small integer, and form a public divisor palette
of possible tags. ONE shared restricted Harvey–Hittmeir call handles the
entire palette in soft K. Neither the count nor division by it is needed.
For r=1, the small integer is even below K/2.

The complete argument and finite parameter choice are in
[hybrid integration](hybrid-integration.md), with
[two](moment-consumer-review.md)
[independent audits](independent-moment-review.md).
This reduces what acquisition must output; it does not perform acquisition.
Generic Lambert amplitudes and raw-torus aliases do not satisfy this
bounded-integer promise.

## 2. Decompositions that preserve the wanted signal

Use weight `w_j=u_j` for M1, or `w_j=K/2+u_j` for the packed C. Put
`S_w(delta)=sum_(j,i) w_j/a_ji(delta)`.

| Form | Exact cancellation | What remains to acquire |
| --- | --- | --- |
| Adjacent denominators | A geometric weight telescopes to paid endpoints; the constant-weight correction has residue one per hit | The selected residue of `sum w_j/(a_ji*a_j,i+1)` |
| Opposite regulators | `delta/2*(S_w(delta)-S_w(-delta))=sum w_j*delta^2/(delta^2-a_ji(0)^2)` | Its constant coefficient; all nonhits have zero constant coefficient |
| Clock-Euler difference | After endpoint gates, `J_h(T)-J_h(rho*T)` contributes `I-(I-1)=1` at an interior hit | The correlated difference of the two index-weighted residues |
| Two-source Ward/Schur form | Double poles or known regular contact terms cancel; the normalization is acquired and unit-gated | A selected scalar retaining `S_w` with coefficient one |
| Singleton replica/reset | At the mandatory zero gate, second variations and the common cofactor cancel | Two first variations, or the simpler existing row-value triples |

The adjacent identity is especially explicit. With `A=1+delta`,
`a_i=A-T*rho^i`, let `T0=sum_i 1/(a_i*a_(i+1))`. Then

    sum_i 1/a_i
      = A*T0-rho/(1-rho)*(1/a_0-1/a_h).

All endpoint terms are acquired in soft K over the whole bank. If an endpoint
is nonunit it is an actual labelled relation and the inherited decoder
applies. On continuation the endpoints are units, so the residue of T0 is
exactly the original hit count. Its two adjacent contributions add to one;
the corresponding geometrically weighted telescope instead cancels them.

The clock derivative gives a different signal-preserving decomposition.
Define, BEFORE specialization,

    G_h(T;r,s)=product_(i<h)(1+s-T*r^i),
    J_h(T)=-Res_delta [r*partial_r log G_h(T;r,delta)]_(r=rho),

where T is held fixed in the derivative. A hit at I contributes I. The
chain rule in the shifted product gives

    count_h(rho*T)=J_h(T)-J_h(rho*T)+h*1_(T*rho^h=1).

After both endpoint gates, the correction vanishes and the shifted count
equals the original count. A Wronskian cancels derivatives of the shared
bulk before numerical evaluation, but the signal-preserving version still
contains its selected logarithmic residue. This explicitly identifies the
term a future fast contraction must retain.

See [adjacent denominators](packed-finite-part.md),
[clock differentiation](deformation-cancellation.md),
[early Wronskian contraction](correlated-wronskian.md),
[Ward sources](packed-source.md),
[replicas and cavities](ward-cavity-contraction.md), and
[the singleton reset](replica-reset.md).

## 3. Another branch: scalar torus collisions

The separately prepared raw-torus family has a complete alias decoder.
On its endpoint-gated locus, `F(x)=(1+x)/(1-x)` satisfies

    F(x)+F(y)=2*(1-x*y)/((1-x)*(1-y)).

For norm-one characters, `F(x)/tau` is a base scalar. Thus the actual
multiplicative collision becomes a licensed additive scalar collision.
Inversion sends this scalar to its negative; pairing the positive and
negative physical clock halves the clock length by a constant factor.
Its squared clock is a Möbius transform of an order-two Chebyshev sequence.
This is fully initialized, but its joint evaluation still has the old cost.

The [binary Chebyshev experiment](chebyshev-decimation.md) safely discards
the negative algebraic square-root branch using odd order. Both physical
clock parity branches survive. A degree-J target is shared across them,
but their cosets reassemble into a finer clock with the same number of
positions; this executed recurrence gives no exponent improvement.

The explicit cone subdivision instead cancels the interior collision pole
itself. A short lattice enumerator does not automatically compute its
selected-resolvent transform. Details and guards are in
[cone reciprocity](cone-reciprocity.md). This branch does NOT inherit the
original bank's common tags or singleton partition. Cayley transformation
and its paid unit companion have prior credit in the
[22 October packet](../semiprime-twist-character-20261022/README.md).

## 4. What the tests settle

The follow-up contractions test cancellation before numerical anchor
emission, not just after separately acquiring long objects. Ordinary
Wronskians remove the signal along with the shared factor. The version
retaining it leaves a selected log-residue. Replica/reset identities remove
second jets but leave first variations. A certified regular cavity may be
deleted without its self-energy; the tested way of certifying a macroscopic
cavity already costs K^(5/4). None is a lower bound on all scalar algorithms.

The q-difference route also acquires its endpoint rational function and
O(K) initial coefficients. Every native row lies in the same whole q-orbit
at the good field; selecting its position within the finite clock remains
essential. Generic residue extraction before singular specialization loses
that information. See [the initialized q-difference audit](packed-qdifference.md).

The next acquisition target can therefore be M1 alone, any one of the
equivalent selected coefficients above, or one gated useful singleton
readout. A proposed shortcut must bound its actual inputs, coefficient
operations and localization over the WHOLE family. A constant-size formula
containing an unacquired scalar does not meet that requirement.

## 5. Evidence and preservation

The [review record](review.json) separates paper proof, symbolic identity
checks, and the unchanged acquisition bound. All 14 cleared polynomial
checks pass the [root replay](validation-cancellation.md); they check
coefficient algebra, not the unit guards, coverage or complexity. The [source pins](sources.json)
identify inherited contracts; the [manifest](manifest.json) freezes this
packet. The side report is preserved unchanged. The statement that its C
was unidentified in the previous frozen packet is superseded here, not
silently edited out of that history. No factoring-success campaign,
benchmark exponent, formal proof, commit or push is part of this packet.
