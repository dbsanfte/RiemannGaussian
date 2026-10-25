# Independent scalar-endpoint applicability and tensor identity review

2026-10-24. PASS for `literature-endpoint.md`, SHA256
`762a054cb539cc633f3d8295184a3feb9a8339348bd115396f2e4d340cbad85b`.
This review checks the decisive cost specialization and the proposed
tensor identity. It is not an exhaustive literature search or a proof
that a faster scalar algorithm is impossible.

The primary Bostan--Yurkevich text was independently opened and its
Theorem 5 checked: specializing recurrence order to one retains the
square root of coefficient degree times endpoint index. The composite-ring
blocking construction in the report is independently sufficient for this
application, so its validity does not depend on silently extending a field
theorem. Monic multipoint evaluation and multiplication never divide by
the endpoint or a collision value. The optimized charge is
soft(J*b+L/b+J), hence soft(J+sqrt(JL)).

The primary Bostan--Mori abstract and problem definition, the special
resultants paper's explicit degree-st output and Proposition 3, and
the 2026 modular-composition paper's generic-input Theorem 1.1 and
Theorem 1.3 were independently checked. Their supplied-input and degree
parameters support the distinctions made in the report. The finite-ring
composition reference was also opened: unknown factorization by itself
is not a valid exclusion argument. The report correctly retains the
explicit quotient/input size, genericity or randomization where required,
and distinguishes n^(1+o(1)) from a soft-linear theorem. After an initial
HTTP 502 from the web tool, the isogeny source was acquired in the local
primary-source cache, PDF SHA256
`d18c20ebca34b14e51055f7367ff5577435191c245dc98ae0c1443dfcb73490a`.
Its sections 3.1--3.2 were independently read: the single-target geometric
product algorithm works over Z/nZ and divides only by known unit powers.
Its scalar-target promise is accurately distinguished from an additive-cost
many-target theorem. The decisive endpoint bound also has the self-contained
proof above.

For the new tensor expression, A and B are monic and split at known
scalar powers, with unit pairwise differences under the prepared horizon.
Evaluation therefore identifies their tensor quotient with the product
of st scalar copies of R. Multiplication by F(XY) is diagonal there with
entries F(q^(a+s*b)), proving the displayed norm and iterated-resultant
identities. The same identities are integral polynomial identities and
remain true at singular endpoint values. No inverse of F is used.

The endpoint tail is shorter than s and is acquired by ordinary MPE in
soft(J+s). Thus the claimed small INPUT cost, including the tail, is
correct. It does not give the tensor norm: the quotient has rank st,
the inner resultant can have degree Js, and a quotient-ring operation
has a cost depending on t. The report explicitly charges all three.
Constructing the complete composed-product polynomial would simply
construct the original st-node geometric polynomial.

The suggested generator-elimination experiment is appropriately stated
as unproved. Small initial displacement rank does not establish closure
under elimination, scalar ring cost, or legal pivots over Z/N. A proposed
factor-or-norm primitive must also work for row and subinterval restrictions:
the unrestricted norm can be globally zero and carries insufficient
localization information alone. The report's success contract includes
these restrictions. No whole-query rate advance is established.
