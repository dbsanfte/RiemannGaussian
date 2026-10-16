# Long-query extraction: paid inverses and actual rank obstructions

2026-10-16. **Partial structural progress; whole-family acquisition remains open.** Three user-authorized Sol 6.1 agents investigated the common-channel gcd, the mixed diagonal, and cancellations in the block kernel. This packet contains classical constructive proofs and actual-source obstructions. It does not prove a softly linear collision query or a sixth-rate factoring theorem.

The [preceding block packet](../semiprime-block-query-20261016/README.md) pays both actions of the coefficient matrix, both actions of the mixed matrix S, and every channel at one arbitrary scalar point in softly O(m). Its exact common-channel gcd selects the collision rows, but acquiring that gcd or diag S is still unpaid. The general query bound remains softly O(m^(3/2)).

## Constructive results

[Paid q-pencil](reports/paid-q-pencil.md). Let C_(n,s)=c_(Jn+s), F(t)=sum c_k t^k=P_L(t;q), M=CW, W_(s,j)=z_j^s, Z=diag(z_j), and Q_row=W^(-1)diag(q^s)W. The finite block recurrence gives

    M(I-q^L Z)-diag(q^(Jn)) M Q_row(I-Z)
      = u 1^T-v (z_j^J)_j^T.

All operators and the two endpoint generators are acquired in softly O(J+L/J+sqrt L), including shared selected coefficients. No 1-z_j, endpoint coefficient, or row value is inverted. Degree<J block polynomials really do close under interpolation at q-shifted nodes. This corrects any overly broad suggestion that finite-carrier q-shifts can never close. It supplies a generalized pencil, not an ordinary powered-node commutator for S.

[Coefficient-block inverse](reports/coefficient-block-inverse.md). On the retained actual prime-order source, the leading J-by-J block C is invertible, and its inverse and transpose inverse have softly linear actions after paid setup. Rational Newton interpolation supplies an explicit algorithm with justified unit denominators. The order premise is stronger than merely ord(q)>L: the proof uses units through L+J-1. The retained family supplies that premise. This is not an all-input or all-restriction promise. The determinant also has a cheaply acquired product formula. These results do not extract the diagonal of a product of fast transforms.

## Exact limits on the proposed cancellations

[Powered-node q-shift defect](reports/qshift-power-defect.md). For the column-value interpolation shift Q and Y=diag(z_j^B), with 1<=B<=J,

    rank(QY-q^B YQ)=min(B, #{j:H(qz_j)!=0}),
    H(t)=prod_j(t-z_j).

This is an exact field identity. For the literal quadratic-row offsets on the retained family, qz_i=z_j holds exactly when delta_i-delta_j=m^2 as integers. The low-digit fibers have size at most two, so at least ceil(J/2) rows remain nonzero. A balanced dyadic B<=J therefore makes this defect have rank Omega(m) in both hidden fields. The rank-one q-compatibility relation cannot be promoted to a polylog-rank powered-node correction by this route. This does not prove high rank for YS-SY itself, or high arithmetic cost for applying the defect.

[Mask separation](reports/mask-separation.md). The exact canonical weights that contract F's polyphases into N_0 have evaluation matrix

    w_s(z_j^B)=E_B(z_j) z_j^s/B.

It has actual unit Vandermonde minors. Therefore these weights require linearly many separable constant-vector/polynomial terms. The conclusion extends to canonical channel combinations preserving the unit rows. The actual channel polynomials themselves also have constant-linear span dimension Omega(m), even after removing their small common factor. **This is a coefficientwise separation-rank obstruction.** The fixed q-binomial input has syzygies; alternative weights using those syzygies, general structured contractions, and direct gcd/factor methods remain outside the theorem. No arithmetic-operation lower bound is claimed.

[Local content and blind probes](reports/local-channel-content.md). At every safe center -gamma^a, all channel jets generate the whole truncated-series ring at every precision, because the global collision locator is a unit there. At a powered target, their fieldwise common valuation is exactly the collision indicator, zero or one. This excludes substituting local content for global polynomial content, while allowing global Padé/reconstruction and individual nonunit-pivot leaks. Blind uniform polylogarithmically many target-value gcd probes miss the sparse informative rows with probability 1-o(1) on the inherited family; this is not a claim about adaptive algorithms.

## Literature, verification, and the remaining advance

The [structured determinant prerequisite audit](notes/structured-determinant-primary-note.md) checks an author-hosted ISSAC 2021 paper. The coefficient-block report also audits recurrence-width and determinant-evaluation sources. They support fast structured transforms or supplied-generator determinant routines; they do not currently supply the missing determinant deformation or mixed diagonal. Primary payloads, exact source hashes, and independent final-byte mathematical reviews are preserved in this packet.

The needed advance remains acquisition of one channel modulo the powered-node polynomial, the exact collision locator, the mixed diagonal, or another sufficient restriction-stable observable in softly O(m), followed by the full bit-complexity and Lean composition. A rank-two pencil, a fast inverse, or a small common-factor degree alone does not establish that result.

All eight prior evidence bundles and their exact journal entries are preserved. No new Lean declarations, factoring benchmark, or broad build is used to support these classical results. The manifest records file hashes, source resolutions, and the pre-entry journal baseline; the reviews identify the precise report bytes they checked.
