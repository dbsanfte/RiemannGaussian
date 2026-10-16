# Independent review: paid fast mixed matrix and conditional diagonal extraction

2026-10-16. Verdict: PASS. The report establishes the two fast matrix actions, not the compatible low-rank commutator or diagonal acquisition.

## Exact bytes

Reviewed `/tmp/semiprime-decimation-query-20261015/fast-mixed-matrix-interface.md`, SHA-256 `4959b0f33989570507b15eb82e8b93c2020449032ad1612b4d4e92b74f1d5767`.

The pinned prerequisite block-transform report remains SHA-256 `825aaaa7d10637eddcf38a7b8e8f2241a70984c4b94c506372e922b845b2fe70`, and the mixed-kernel classification remains SHA-256 `ad33d26baea13d0d6f0ea968c1f8373042f7911049255c48d45e8c2118cde73f`. Both were independently read, with the paid block primitive reviewed separately. The THREE saved primary-note/PDF/text entries in q_integral/mixed-diagonal-manifest.json independently match their byte lengths and hashes. Saved Bini--Meini--Poloni section 3.3 equation (3.9) explicitly recovers a diagonal from supplied generators and ONE supplied action; the report does not misread that as an unconditional fast diagonal theorem.

## Matrix identity and paid actions

Dimensions are A:J by T, C:T by B, W:B by J. The ragged term has u_i=y_i^T and v_j equal to the explicitly acquired final partial coefficient polynomial at z_j. Thus S_(i,j) is exactly the displayed complete-block bilinear evaluation plus that rank-one term, and putting i=j turns y_i^n z_i^s into z_i^(Bn+s). This proves diag S=(F(z_i)) with no missing coefficient, padding or scale.

W*x consists of the first B weighted power sums at the z_j. It is a paid transposed Vandermonde operation over R, without dividing by node differences, including repeated nodes. C acts at the already proved formal block-transform clock. A evaluates a degree<T polynomial at the y_i by monic remainder trees. Transposition reverses these operations: A^T gives weighted power sums, C^T is the paid formal transpose with parameter-only inverse constants, and W^T is ordinary polynomial multipoint evaluation. The rank-one correction needs one dot product and scaling in either direction. Therefore BOTH actions, including S*1, have the stated soft O(J+B+L/B+sqrt L) ring and stored-residue scale, with the usual log N modular bit factor.

All C row starts are complete: Bn+B-1<=L. The h coefficients in the final partial row also stay within [0,L], so the only q denominators needed are those through L. If h=0 the correction vanishes; if T=0 the complete-block action is empty and the ragged polynomial is the entire F. This also handles B=1 and small L. Metadata powers y_i^T and z_i^B, selected coefficients, evaluations of the final polynomial, and the coefficient operator setup fit the stated bound. These are genuine fast actions with explicit structure, rather than black-box assumptions or J separate one-point queries.

## Conditional commutator extraction

For i!=j, the exact ordinary commutator YS-SY=UV^T gives

    S_(i,j)=sum_a U_(i,a)V_(j,a)/(y_i-y_j).

The orientation and sign are correct. With b=S*1, subtracting these off-diagonal sums returns the exact diagonal; no diagonal entry of S or commutator is assumed supplied. All-ones input is a unit vector coordinatewise, so the general Trummer diagonal formula needs no inversion of an arbitrary action vector here.

The rational regular-part formula can be proved directly as a polynomial identity over R. Put Q_i=Q/(X-y_i). The i-th summand in P' at y_i contributes w_i Q_i'(y_i)=w_i Q''(y_i)/2. Each j!=i contributes w_j Q'(y_i)/(y_i-y_j). Dividing by the promised unit Q'(y_i) gives exactly the reported formula. No analytic residue argument or field-only elimination is required. Since N is odd, 2 is a known unit; unit pairwise differences make Q'(y_i)=product_(j!=i)(y_i-y_j) a unit. A common product tree constructs P from weights and Q factors softly linearly, without expanding J individual quotients. Differentiation, evaluations and one batch inversion have the stated soft O(J log N) bit cost per generator column. The source odd-subgroup promise makes the powered y_i differences units. Outside the promise, the stated proper-factor/saturation distinction is correct.

Thus polylogarithmic r PLUS paid compatible generators would indeed suffice for the whole diagonal and product/gcd query. Their existence, rank, and acquisition are conspicuously unproved. Merely paying the commutator action, or having a different rational-Newton q-shift pencil, does not supply these arrays. The latter changes targets and cannot be substituted for the fixed-node ordinary commutator.

## Scope

The row-subset/common-interval recovery claim is correctly conditional on the corresponding generator theorem; neither low rank nor restriction stability is inferred automatically from the full-row operator. Repeated nodes are allowed for the fast actions, while diagonal extraction correctly switches to the actual distinct-node promise. There is no improved total query clock, scalar norm lower bound, all-input guarantee, or new Lean theorem. The positive advance is precisely the paid bidirectional operator with the desired row list on its diagonal, leaving a well-specified generator/diagonal problem.

No original report or repository file was changed, and no build was run.
