# Independent mathematical review

2026-10-15. Reviewed qproducts/formal-log-obstruction.md and norms/report.md as present at review time. This is an algebraic/interface review, not independent verification of every bibliographic theorem, date or bit bound.

## Required correction made to my report

The original sentence about the degree of a monic carrier was too broad. Distinct residues modulo composite N do not imply an arbitrary monic vanishing polynomial has at least that many degrees: X^2-1 modulo 15 has four distinct roots. source-moving-carrier.md now limits the degree count to the literal product of distinct linear factors; it explicitly disclaims an arbitrary vanishing-polynomial lower bound.

## formal-log-obstruction.md

No mathematical error found in the core jet obstruction: because x is a unit in A, x^K A=A, so any fixed finite jet admits every quotient residue. Residues zero and one genuinely distinguish norms even when the constant coefficient of each input polynomial is fixed at one. The separate disclaimer about promised special q-products is essential and is present.

The scaling-endomorphism criterion is correct over the composite ring: H divides H(q^t X), and monicity plus equal degree forces the stated constant multiple. The moving modulus q^(tJ)H(q^(-t)Z) has the correct sign for P_t(q^t X). The geometric-series division caveats, characteristic denominator caveats and absence of a universal scalar lower bound are correctly scoped.

The asserted strict distinction between D^(1+o(1)) and soft O(D) is correct for the displayed D^(5/sqrt(log D)) factor. This review does not independently rederive that external theorem's precise bit bound.

Suggested strengthening: under the actual prime local order R>J and 0<t<R, constant-term comparison alone rules out H dividing H(q^t X), since it would force R dividing tJ. Thus this particular fixed-residue failure is actual-family, not merely generic. Root supplied this strengthening; it is added to source-moving-carrier.md.

## norms/report.md

The resultant sign is correct for S=prod_(j,i)(u q^i-Y_j), with F monic roots Y_j: Res(F,G_L)=prod_(j,i)(Y_j-u q^i), hence S=(-1)^(JL)Res(F,G_L). The doubling factor q^(h^2) and moving quotient sign are also correct.

The report correctly requires explicit input arrays for modular composition and does not treat the unknown degree-J remainder as already available. Its product-modulus degree J*2^t is explicitly an upper-bound accounting issue for the direct construction, with coincidences and richer representations excluded from the lower-bound claim. Unlike my original wording, it does not infer a root-count lower bound over a composite ring.

The unit/nonunit resultant discussion is safe as phrased: a proper gcd yields a factor, and unit pivots permit normal continuation. An implementation should additionally distinguish gcd=N (a globally zero pivot, requiring degree trimming or another step) from a proper gcd; the report does not claim every failed inversion yields a proper factor.

The augmented-ring cost is a valid cost of that particular evaluation scheme, not a lower bound on all augmented-ring algorithms. The final wording preserves that distinction.

No substantive mathematical correction to either reviewed file is requested. Their primary-source bibliographic claims remain the responsibility of the source-checking agents. I have not rerun source downloads or generic builds.
