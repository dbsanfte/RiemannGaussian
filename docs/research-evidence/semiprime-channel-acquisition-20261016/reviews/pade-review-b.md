# Independent adversarial review: channel Padé audit v2

2026-10-16. PASS as an unsuccessful acquisition pass and a transferred route limitation. No acquisition advance, new arithmetic obstruction, general jet lower bound or operation lower bound is established. Read the full original and full corrected v2, independently checked the algebra, and inspected the saved primary theorem/model passages rather than relying on the report's summaries.

## Final reviewed pins

- pade/report-v2.md: 9688 bytes; SHA256 `b22dfebe61a0117c66ed43b79c87b8671306363795e1e1f07350032ec958c181`.
- pade/source-pins-v2.json: 1231 bytes; SHA256 `d4b52cdb8b8a97ac7d97c76548c734bf80e8c4d5cf129bf14f2a0654c06c09fa`.
- pade/manifest-v2.json: 1192 bytes; SHA256 `4908f0a8d85c99fe3744c3077652f9ae3c731a74436dec0e68744d3f8650e729`.

All SIX v2 manifest entries and all FOUR inherited source file pins match their recorded byte counts and hashes. Both saved primary PDF/text pairs were independently regenerated with pdftotext -layout and match byte-for-byte. The original report 8255/a92a9aa0... was not edited; v2 explicitly supersedes it. This review requested the B>=J qualification for the complete moment-vector claim, which v2 now states correctly.

## Exact algebra

Distinct powered nodes y_j=z_j^B and unit multipliers give M_r(y_j)=z_j^(-r)N_0(y_j). Therefore each channel has exactly the same zeros on the squarefree D as N_0, and its field-side reduced proper denominator is EXACTLY D/H. No cancellation at a nonhit can remain hidden: its partial-fraction residue is a product of the nonzero value and unit factors. The all-hit d=0 case is separated; the retained density premise implies d=J-o(J), not a small hit-supported denominator.

The leading d-by-d Hankel matrix really is V diag(lambda_j) V^T at distinct nonhit nodes, with every lambda_j nonzero. Hence its determinant cannot vanish, including in positive characteristic. A lower-order scalar recurrence would force singularity, while D/H gives an order-d recurrence. Thus the exact minimal order and common minimal order of any nonempty unmodified channel collection are d. The mechanism is the already frozen sparse-intersection moment theorem, with powered nodes and changed unit weights. V2 now credits that provenance and does not advertise this transfer as a new obstruction.

At Taylor precision nu<=d with numerator degrees independently bounded by <d, EVERY normalized candidate denominator of degree<=d admits numerators obtained by truncating lambda R_r modulo Y^nu. This is valid for arbitrarily many channels. It proves vacuity of precisely those independent-numerator congruences, not that all algorithms using the coefficients have no information. Cross-channel identities, coupled numerator constraints and specialized approximation problems remain outside it. The denominator degree may be unknown algorithmically; here it is a proof-side description of the proposed natural bounds.

The known point-vector SLP computes RAW N_r(X), not proper parts M_r/D or their expansions. Polynomial parts cannot be dropped for free. Generic arithmetic-circuit lifting to precision nu has the stated O(s M(nu)) ring work and output accounting; with s,nu,B all linear in J that implementation is softly quadratic. The logarithmic bit scaling is consistent with O(log N)-bit residues and fast polynomial arithmetic. This is an upper-bound account for a routine implementation, not a lower bound against specialized jets or compressed outputs. Fixed-unit circuit constants and D(0) units are required; composite-ring Padé pivots still need factor-aware handling.

## Important adversarial information nuance

With B>=J, the proper Taylor ZEROTH coefficients alone also determine all row values through a known Vandermonde transform:

 R_r(0)=-sum_j z_j^(-r) N_0(y_j)/(y_j D'(y_j)),  0<=r<J.

All weights multiplying N_0(y_j) are units. This is the same invertible transform as the report's infinity zeroth moments, with an extra unit y_j^(-1). Thus one coefficient PER PROPER CHANNEL can suffice if those data are acquired and the known cross-channel relations are used. The Padé vacuity theorem must not be read as an information lower bound even at precision1. V2 correctly permits this escape and identifies acquisition of proper parts as unpaid. Raw N_r(0) cannot be substituted for R_r(0). If B<J only B such moments are supplied and the matrix is rectangular; v2 now says so explicitly. The corrected report is consistent with this stronger adversarial observation.

## Targeted primary inspections

Rosenkilde--Storjohann 2016: independently inspected Problem1, compact solution specifications, introductory cost definitions and Theorem20 on printed page411/PDF page7. Input consists of explicit polynomial S_i, moduli g_i and degree bounds. The theorem's d is MAXIMUM modulus degree, with bound O(n^(omega-1) M(d) log d (log(d/n))²), using customary logarithm conventions, not a sum-degree parameter. The compact output does not acquire input series or prove that arbitrary bounds select H. At n and required precision both of order J it gives no nearlinear acquisition. The low-precision vacuity argument is an elementary approximation statement and does not rely on silently extending that paper's admissible degree-bound conventions.

Yu--Loeliger 2018: independently inspected the SPI polynomial-input formulation, Definition2 of the partial-inverse condition, received-word/syndrome constructions, Theorem2's equivalence and Proposition13's complexity. The theorem needs supplied received/syndrome data and a proved error-pattern condition. Its specified algorithm has O(L(n-k_min)(n-k_max)) field operations under that condition. A small common zero factor of our channels neither supplies such data nor makes the dense nonhit residues into sparse errors. A separately proved coupled coding-model reduction could evade the present ordinary-Padé formulation; v2 explicitly leaves it open.

These are targeted theorem/model inspections, not complete correctness audits of either primary paper, and not an exhaustive literature nonexistence claim. No new primary theorem is imported as a free coefficient oracle.

## Verdict

Final v2 is sound within its narrow contracts. Its qualified provenance and scopes now clearly describe an unsuccessful pass, not a new theorem packet or acquisition progress. No further correction requested. No reviewed report, source, primary payload or frozen bundle was mutated; no build or numerical example used.
