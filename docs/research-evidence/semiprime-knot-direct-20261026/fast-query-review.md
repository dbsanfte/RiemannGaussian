# Independent review of the fast-factorial/native-jet audit

26 October2026. Read `fast-query.md` and the primary Tal PDF https://eccc.weizmann.ac.il/report/2026/211/download, including Theorems1.1–1.3, Proposition4.3 and AppendixH. The algebra, cost accounting and negative applicability conclusion pass. No additional research, numerical tests or repository edits.

## Source hypotheses and two precision notes

Tal's Theorems1.1/1.2 use a supplied prime p and divisor of p−1; compatible reconstruction data is constructed within their bounds. Theorem1.3 explicitly takes the extension-field representation and compatible character for its fixed odd prime-power cyclotomic index. The report should distinguish those input lists rather than imply all three theorems require externally supplied character data. All require the known prime, so this clarification does not change the native applicability conclusion.

Proposition4.3 is the stated deterministic logarithmic improvement for p>=5, using AppendixH. It does not claim a uniform power-exponent improvement. Its prefix lemma also limits the number of requested indices; it is not a general arbitrary-many shifted-prefix oracle. The report does not invoke it as one.

AppendixH writes P_h(Z)=A_h+B_h^source Z with p dividing B_h^source. The report instead normalizes B_h=h! sum_(j<=h)1/j and writes A_h+pZ B_h. These agree modulo p² for h<p; B_h is only needed modulo p, whereas A_h is retained modulo p². This harmless notation change should be explicit. No division by a native collision follows from it.

## Native phase jet

The exact Hasse–Taylor formula is

    F(t(1+Z))=sum_(r=0)^J t^r F^[r](t) Z^r.

Thus the printed tail after truncation is correct without factorial denominators, including finite characteristic. Substituting Z=q−1 is legal in the full identity. Its unit status follows separately at both primes from the supplied local orders>1. Likewise q^h−1 is a unit for nonzero signed h in the guarded short range. Hence the source's p² nilpotence does not justify deleting any native tail merely from its power of Z.

The report correctly says the tail is not certified zero or unit, rather than asserting it is nonzero for every F. A zero of the full value can arise by cancellation with the truncated part. Over Z/N for squarefree N, scalar nilpotence means zero; an auxiliary truncated-polynomial ring can store jets, but substitution of its nilpotent parameter by the unit q−1 is not an algebra homomorphism. A new coverage-preserving map would be needed. This is a concrete failure of the attempted adaptation, not a general no-go for all characteristic-free factorial identities.

## Exact parity and full charged completion

The even/odd parity identity is correct for the stated convention P_s(F;t,q)=product_(i=0)^(s−1)F(tq^i). For the report's physical indices1..m, instantiate t=eta q. Both parity branches are real parts of that original interval, so no branch may be omitted without a separate witness proof.

The acquired block polynomial product_(r<B)F(q^rX) has degree JB, and building its actual coefficients costs soft(JB). Monic multipoint evaluation at the m/B acquired block starts costs soft(JB+m/B). The <B leftover original values can be evaluated jointly within soft(J+B), or by the retained geometric routine, both absorbed. Optimizing B near sqrt(m/J), with B>=1 and clipped endpoints, gives soft(J+sqrt(Jm)). Thus the claimed fallback is initialized and collision-safe, not a field-only division argument. Repeated starts and nonunit target values do not invalidate monic remainder evaluation.

The q-holonomic checkpoint appropriately retains growing recurrence order/degree and does not identify a small knot recurrence with an acquired modular scalar algorithm. I did not independently re-audit its already-archived Bostan–Yurkevich theorem in this source-focused review; the report supplies the explicit division-free block algorithm needed for the actual bound regardless.

## Predicate and outcome

A truncated jet, character sum, or auxiliary additive zero receives no original signed-gap decoder automatically. The full parity/block completion does retain every original factor and its labels. Tal's given-characteristic, divisor-conditioned or logarithmic algorithms are not asserted to solve the unknown-semiprime geometric product. The report consistently claims no full-query gain and no attained sixth-exponent algorithm. Apart from the two source/notation clarifications above, no correction is required.
