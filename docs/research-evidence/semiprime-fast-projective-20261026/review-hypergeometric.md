# Independent review of hypergeometric-contraction.md

26 October 2026. Read the complete report and the frozen
`semiprime-projective-readout-20261026/initial-chart.md` prefix theorem.
Paper-only; no tests, source edits or repository changes.

**Scoped PASS.** The coefficient identities and the finite polynomial
q-Gosper obstruction check. Make “degree after good-field/hit-root
specialization” explicit in the leading-coefficient paragraph; no
computational or general rational-certificate conclusion follows.

## Coefficients and finite multisection

For a_t=(-1)^t rho^(t(t-1)/2)[h choose t]_rho,
`a_(t+1)/a_t=(rho^h-rho^t)/(1-rho^(t+1))`, exactly as printed.
The two-factor parity ratio and B-factor stride ratio have the correct
powers, signs and endpoint shifts. Their denominators used for
advancing an INCLUDED index are short guarded factors. The terminating
zero numerator is retained; a recurrence ratio is not inverted through
that zero or advanced indefinitely outside its supplied range.

The rational parity numerators are obtained by P(z)Q(-z) and its even/
odd coefficient sections, with u=z^2. Full powered denominator
Q_B(z^B) is divisible by Q(z), including repeated roots and supplied
cancellations. Using the original full rev(F) representation avoids
any need to compute a minimal denominator over the composite ring.
The literal JB coefficient acquisition and O(h) scalar completion
are valid UPPER costs. No lower bound on a joint scalar algorithm is
asserted. Graeffe zero-predicate preservation uses the actual odd-order
subgroup; it is different from coefficient multisection and keeps h.

## Exact q-Gosper equation, including the constant case

Multiplying the desired antidifference by the unit recurrence
`1-rho*z` gives exactly

    x*(A-z)R(rho*z)-(1-rho*z)R(z)=1-rho*z.

For a constant R=r, its constant and linear equations are

    r*(x*A-1)=1,
    r*(rho-x)=-rho.

Eliminating r gives x*(1-rho*A)=0. Since x is a unit and
1-rho^(h+1) is a certified short unit, this is impossible. This
argument does not secretly invert x*A-1. The zero polynomial is
also impossible because the right side is nonzero.

If a quotient-valued certificate specializes at the good field and
then at x=theta=rho^(-I), its SPECIALIZED polynomial is nonzero.
Let d be THAT polynomial's degree and r_d its nonzero leading
coefficient IN THE FIELD. Comparing z^(d+1) for d>=1 gives
`rho^(d-I-1)=1`. A globally nonzero quotient leading coefficient
could vanish at the hit root, so its original global degree cannot
be substituted for d; one must first drop such vanished leading
coefficients. The report's specialization-first wording is sound,
but this explicit definition prevents a possible overreading.

For 1<=d<ord(q), 0<=I<h<ord(q), the exponent d-I-1 lies strictly
between -ord(q) and ord(q), so it must be zero: d=I+1. More
generally only the displayed congruence modulo ord(q) is asserted.
If the global certificate degree were <=5J, its specialized degree
would also be <=5J, so this still contradicts I>=5J on continuation.

The frozen chart proof screens precisely the original indices
0<=i<5J. It has an actual nonzero short-label norm/extractor branch
even on a wrong family. Thus UNIT CONTINUATION of that screen rules out a good hit before
index5J; the resonance argument uses the paid prefix correctly. Small exceptional parameter ranges retain the
source guard/fallback and are not asymptotic advice.

The endpoint sum is also exact for a polynomial certificate: a_(h+1)=0
by the terminating numerator, while 1-rho^(h+1) remains a unit.
Therefore T_(h+1)=0 and the finite telescoping result is -R(1).
No infinite limit, non-root-of-unity substitution or singular endpoint
inversion is used.

The q-suitable-field operation in the symbolic primary source is
appropriately identified as an additional algorithmic input. Computing
all d with F(rho^(1-d))=0 is the native membership problem here,
not a free degree routine. No claim against rational certificates,
matrix certificates, short projective outputs or joint norm algorithms
is supported or made.

No substantive correction is required beyond explicitly naming the
SPECIALIZED degree. Separately, my paired-contraction.md sibling
integrality explanation was tightened: sum equation(6), subtract the
middle sibling three times, and use sum k_s-3k_c=0. Its H/9
divisibility is unconditional and uses no existence of a true R lift.
