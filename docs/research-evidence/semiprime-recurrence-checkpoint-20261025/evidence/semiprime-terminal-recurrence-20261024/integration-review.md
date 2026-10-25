# Independent terminal-recurrence integration review

24 October 2026. Reviewed the exact two draft appends and the three final reports plus the frozen root-gradient addendum. No draft or repository mutation.

| Integration draft | SHA-256 |
|---|---|
| /tmp/semiprime-terminal-recurrence-20261024/journal-append.md | f7654a0fea513eb0c3c17c8df6b4fe2ddd63d656ebcd7f0545193a2e7f8fb976 |
| /tmp/semiprime-terminal-recurrence-20261024/agents-append.md | c1a27733b11a973bced2c6c51e077d9344ca5a89fa3cc4fee5d4ef17484468f9 |

Final source pins checked:

| Report | SHA-256 |
|---|---|
| terminal-toda.md | 937018c6ee61730a90df1ee9f05bea37cd1bc0a9d2a4addbb3701ec670aa0e3c |
| terminal-character.md | 75cf6cbaa4a15bd5d334440a93fafad90a57b6d3286228e5d4e016a911c0e9ae |
| terminal-literature.md | 49c90f496dcfaf1f4cc2e69e746950c9e3b597257ca94d21056c76ad7547ed06 |
| terminal-root-gradient.md | 8915ff758ba60c6cf956fb49b65287a45d82623f2c5c92f003a4021b137fa4cf |

Verdict: **PASS. No required mathematical/content fixes.** This review checks integration and claim scope. Final repository-prefix/frozen-entry preservation is the separate root validator's responsibility; this read-only review does not assert that a subsequent append/validation run has already occurred.

## Original target, Toda updates and actual endpoint boundary

The moment family and full-support determinant normalization in the drafts agree with the report, including the (-1)^[n(n-1)/2] sign and Y^-n² factor. Its outer norm differs from the actual scalar target only by known units; those factors have short geometric power formulas. A compatible vector is cheap for ONE scalar Z, not for every outer node simultaneously.

The executed tau_3 condensation contains the correct squared adjacent-minor cross term. It is acquired without c3 inversion, even if that coefficient vanishes. The q-contiguous moment formula and the displayed Omega update also match the actual generating-series identity. These are genuine initialized recurrence operations. The normalized scalar recurrence still requires a norm of an additive mixed expression, rather than a product of already known factor norms.

At full support tau_(n+1)=0 and adjacent tau_n values differ by known powers. The Toda boundary therefore cancels the unknown amplitude; it does not compute that amplitude or its mask. The drafts describe this as a scoped failed closure, not a scalar-algorithm lower bound.

The scalar original-grid relation E1*F(1)=E0*F(q^(nt)) is used correctly. Unit endpoints acquire a multiplier c and the equality E1=c*E0 even for E0=0; they do not license E1/E0 or provide an absolute starting mask. Endpoint indices remain checked within <4H. This preserves the corrected zero/decoder scope of both source reports.

## Logarithmic pivot cleanup is supporting work, not endpoint acquisition

The draft's soft(n+t) logarithmic-prefix helper is supported by the actual trace/Newton determinant construction. Each full degree-k² polynomial is acquired at a proved sufficient formal precision; only certified integer units are divided. Reversal supplies monic endpoint polynomials. Aggregate zero nodes are checked individually and handled at ORIGINAL slices before removal.

The head/cofactor state and subsequent doubled block are truly acquired at logarithmic size, with corrected top-head coefficient count and <=4K next-block integer-denominator bound. The tail still has degree n-O(log n), and arbitrary larger blocks retain their acquired kt state/degree and mixed-mask costs. The drafts do not extrapolate the supporting helper to a whole-query bound or treat removed/holed outer grids as unchanged geometric ones.

The original scalar blocked completion and its restriction/saturation recovery remain the available whole-query algorithm, at soft(J+sqrt(JL)). These appends claim no improvement to that bound.

## Circuit differentiation and actual-h costs

The stated scalar circuit contract is essential and correctly retained: an actual size-C arithmetic identity in INDEPENDENT monic coefficients, fixed q/u/L, with its actual denominators unit. Reverse addition/multiplication/inverse rules are legal over Z/N and never divide by E or a hit value. Native-beta-only programs and Boolean/Jacobi oracles do not meet that differentiable contract automatically.

The first coefficient gradient D_k=sum_i x_i^k product_(v!=i)F(x_v) has exactly the described behavior: one local hit gives a nonzero geometric vector, while two or more hits kill the entire first gradient. Adaptive Hasse precision finds h=min(hP,hQ). Its first coefficient not globally zero has a proper gcd if the counts differ, or is a unit if they agree. Lifting and reverse propagation cost soft(C(h+1)) with the explicitly retained short-input/output and row-locator work; this is not a cost-C multiplicity shortcut. The report's total bound includes J and sqrt L, and the draft retains those operations.

The original report's Newton reconstruction is valid; the addendum supplies a simpler direct root statistic. The draft accurately treats that as recovery simplification, not a new circuit.

## Direct leading root gradient: sign, support and paid map

At equal positive local count h, let a_h be the certified unit leading Hasse coefficient. Holding z fixed,

    partial F(X)/partial Y_j=-product_(a!=j)(X-Y_a).

In the coefficient of z^(h-1), deleting a nonhit factor contributes nothing. Deleting a hit factor contributes a_h times this derivative. At its matching original row it equals -F'(Y_j); at every other original row it vanishes. Therefore the draft's exact local formula

    G_j=-a_h*F'(Y_j)*1_(row j hits)

has the correct sign and coefficient. It also covers h=J without a monic-leading-coefficient derivative. No factorial division is present.

The chain map uses the ORIGINAL unperturbed F_rev, not roots shifted by z. Extract the coefficient vector [z^(h-1)]D_k(z), apply the stated single truncated convolution/reversal and monic MPE, and all G_j are acquired in soft J beyond the paid reverse lift. Unit a_h and guarded F'(Y_j) make every hit statistic locally nonzero and every nonhit statistic zero. Different local row sets yield a proper gcd; equal sets identify a common original row by a unit G_j. The ordinary original-row locator handles possibly different local seed indices and invokes the bounded decoder only at an actual original leaf. The drafts faithfully state all of these distinctions.

## Strong uniform padding contract versus a pointwise valid trace

The padding route is correctly conditional on a STRONGER uniform endpoint circuit/program contract, including every denominator on every padded input. A valid formal trace at one native point does not provide that contract, and a native-only identity may cease to hold after padding. The appends explicitly preserve this limitation.

For an unrestricted monic-input circuit, zero roots multiply each seed evaluation by a known unit power, so fixed-degree padding preserves the original restricted zero mask. This padding is correctly excluded when unit constants or root separation are required.

For the separated-unit version, candidate dummy roots d_s=q^(u-s), 1<=s<=3J, have pairwise and seed differences guarded by L+3J<16H. Evaluating the ACTUAL full original F there costs soft J. A proper scalar gcd already factors; absent one, each value is unit or globally zero. There are at most J globally bad candidates, even if different original rows cause the zeros in the two fields, because that set is contained in a degree-J root set in either field. Thus J safe candidates can be selected. Unit F(d_s) certifies separation from EACH original root; candidate powers themselves are units.

For any row subset, padding with distinct selected dummies preserves monicity, unit constant, separation and its original hit mask. The numeric long dummy product need not be acquired: only its PROVED unit status is used for this mask algorithm. No dummy zero is assigned an original decoder. Actual padded coefficients cost soft J per level, and O(log J) uniform endpoint calls plus one original-row locator yield soft(C+J+sqrt L), suppressing only logarithmic factors. This is the old restriction strategy implemented under the explicitly stronger generic contract; it supplies no new endpoint circuit or all-input acquisition theorem.

## Overall claim scope and preservation

Both drafts lead with no guaranteed soft-m query advance, retain the existing soft m^(3/2) complete query, and leave the sixth-rate theorem and full executable/Lean bit proof open. The derivative/root/padding results are called supporting recovery results; the logarithmic cleanup is called a helper. No sample campaign, broad build, hidden-field oracle, unproved constant hit count, zero-mask division or generic algorithm lower bound is substituted for acquisition.

The exact draft bytes above are mathematically faithful to the final reports/addendum and pass integration review. No shared document or source report was changed by this audit.
