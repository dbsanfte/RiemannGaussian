# Channel acquisition investigation: no improvement to the query bound

2026-10-16. Three parallel Sol 6.1 investigations examined channel-system
desingularization, Padé/interleaved reconstruction, and compact-circuit
GCD/Graeffe extraction. No whole-family nearlinear acquisition algorithm
or new general acquisition obstruction was obtained. This is an
unsuccessful research-pass record, not a new scaling result.

The existing long-query bound remains soft O(J+sqrt(JL)), hence soft
O(m^(3/2)) for J~m and L~m^2. The required soft O(J+sqrt L) query, its
restriction-stable controller, full bit budget and Lean sixth-rate
composition remain unfinished. No Lean declaration or build is added.

## The precise interface that remains open

Use monic D(t)=prod_j(t-z_j), D_B(Y)=prod_j(Y-z_j^B), and the balanced
dyadic B. Write

    E_B(t)=D_B(t^B)/D(t),
    P_L(t;q) E_B(t)=sum_(r<B) t^r N_r(t^B).

At Y_j=z_j^B the exact inherited identity is

    N_r(Y_j)=P_L(z_j;q) [D_B'(Y_j)/D'(z_j)] z_j^(B-1-r).

Its displayed multipliers are units on the retained odd-order branch.
Consequently H_hit=gcd(D_B,N_0) in each hidden field. ONE channel and the
known D_B suffice; acquiring every channel polynomial is unnecessary.
This follows already from the frozen mixed-contraction report, section 2;
it is not a new reduction in this pass. Changing the constant-one mask to
the monic mask only rescales all channels by a known unit.

N_0 has degree at most floor((L+J(B-1))/B)=O(m), and one arbitrary scalar
evaluation has a paid soft O(J+B+L/B+sqrt L) circuit. Evaluating the scalar
at J interpolation points costs softly quadratic work by that method.
A soft-linear uniform extractor for gcd(D_B,N_0), from THIS structured
circuit and the explicit split D_B, would be a useful advance. Small
gcd degree does not supply its coefficients, seeds, or a constructor.
Over Z/N the algorithm must also justify nonunit pivots and saturated
branches; the two fieldwise gcds need not have the same degree. A
retained-family h=o(J) fact is not a worst-case guarantee for all inputs.

## What was checked

[Corrected Padé report](reports/channel-pade.md). The proper rational
channels have reduced denominator D_B/H_hit, of degree J-h. Their moment
recurrence therefore tracks the nonhit rows. This is the already proved
ordinary-row-moment obstruction transported through known unit weights
and the powered-node map. It is explicitly not counted as new arithmetic
progress. With independent numerator bounds <J-h, ordinary Padé
congruences at precision <=J-h impose no denominator constraints. This
elementary observation concerns that formulation; coupled numerators,
transformed syndromes and other structured reconstruction remain open.

The two primary papers audited here take polynomial approximants or
received/syndrome data as inputs. Their algorithms do not acquire those
data from our point circuit. The saved report, exact source copies and
two independent reviews record the input and complexity checks. Review
also corrected the zeroth-moment inversion statement: the complete
J-component Vandermonde vector requires B>=J. With B<J it is rectangular.
Even when B>=J, obtaining proper parts is an unpaid step. The precision
observation is not an information or operation lower bound.

The other investigations found no paid extractor. Graeffe/sign-GCD
identities preserve the unknown locator under injective dyadic powering;
the identity does not pay for its computation. Differentiating a scalar
point circuit returns derivatives at that point, rather than independent
coefficient weights. A proposed free-weight scalar circuit would need
its own construction. Known identities from these checks are not
repackaged as new results here.

## Next acquisition requirement

The useful next result must actually construct the scalar-channel gcd,
a collision-supported observable with all its seeds acquired, or another
sufficient factor query in soft O(m). It must include subset and common
interval restrictions and a justified all-input branch. Further changes
of representation or transfers of the same moment obstruction do not
meet that requirement. This pass changes neither the factoring exponent
nor the status of the overall goal.

All fourteen predecessor packets and their journal entries are preserved.
The manifest and source map record exact reviewed bytes and provenance.
