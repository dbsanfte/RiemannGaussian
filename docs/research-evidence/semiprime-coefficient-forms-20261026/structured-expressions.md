# Structured expressions for the uniform torus first-jet pair

26 October 2026. Paper derivation and primary-source audit; no tests, numerical examples, repository changes or Lean. **No target-rate coefficient acquisition obtained.** An explicit zero-safe row-diagonal solve and an explicit cheap moment family are derived below. Their missing data and failed short-closure step are paid precisely. These are alternatives for the same weak observable, not independent query acquisition.

Read hybrid-handoff.md sections 1–4, the prior quotient-gradient/weak-readout.md, hybrid-audit/moment-locator.md and topology-prefix.md, and the earlier journal's Cauchy/selected-diagonal warnings (41032, 41194, 42602ff). Old Bezout, corank-one and endpoint interfaces remain prior credit.

## 1. Actual target and the rank-two array

Keep either of the two acquired monic root lists y_j, J<=K, clock x_i=q^i, 0<=i<h=2H+1, and labels w_j=[j]_n. On one list at the good nonsplit prime there is exactly one hit (j*,i*), with w_j*=R mod n. The requested values are

    V=sum_(j,i) product_((l,t)!=(j,i))(1-y_l/x_t),
    U=sum_(j,i) w_j product_((l,t)!=(j,i))(1-y_l/x_t).

They are the exact first coefficients in hybrid-handoff. At the good field V!=0 and U/V=w_j*. No statement about the other prime is needed. All native/provenance and own-source recovery obligations remain those of that report.

The leaf array A_(j,i)=1-y_j z_i, z_i=q^-i, has ordinary rank at most two. This is NOT the operator whose determinant is the entrywise product. For any two rows and columns its minor is

    det A[{j,l},{i,t}]=(y_j-y_l)*(z_t-z_i).

At the actual unique hit, choose its row and any other row; these row roots differ at the good field, since otherwise the other row would hit too. Any other clock column gives a nonzero displayed minor. Thus the ordinary array still has rank TWO at the collision (when J,h>=2), while the entrywise product vanishes. Ordinary rank/kernel compression of this array does not itself locate the zero entry. This is an actual-native test of that matrix choice, not a general lower bound.

## 2. Fold each clock row: exact determinant coefficients and a weaker solve

Define the geometric polynomial and its row data

    G(T)=product_(i<h)(1-T q^-i),
    R_j=G(y_j), D_j=hG(y_j)-y_j G'(y_j).

Indeed product_i(1-y_j q^-i+delta)=(1+delta)^h G(y_j/(1+delta)), whose derivative at zero is D_j. Let C_j=product_(l!=j)R_l. Then exactly

    V=sum_j D_j C_j, U=sum_j w_j D_j C_j.         (1)

With D=diag(R_j), the two rank-one pencils

    det(D+t*1*Dvec^T),
    det(D+t*1*(w*Dvec)^T)

have respective t coefficients V,U. The determinant lemma here is polynomial multilinearity, not an inverse of singular D. It holds over the actual composite algebra through every zero pattern.

For the WEAK ratio there is an even simpler legitimate replacement:

    V0=sum_j C_j, U0=sum_j w_j C_j.              (2)

At the good unique-hit field only C_j* survives, so V0!=0 and U0/V0=w_j*. These are not numerically the original U,V; the omitted D_j* is a common NONZERO local scale only on the promised field. Their validator and HH consumer therefore remain valid. This is the old projective/cofactor target in a row-value basis, not a new computed invariant.

A completely zero-safe regularized system realizes (2). Set M=D+11^T. Its determinant is s=product_j R_j+sum_j C_j. If s is a unit, the explicit solution of Mz=1 is z_j=C_j/s: multiplying any row gives (product R+sum C)/s=1. At the good field s=C_j*!=0 and z=e_j*, so w^Tz yields the tag. Norm(s) gives a proper factor or a unit on that field; no arbitrary Gaussian-elimination pivots are assumed. Prefix/suffix products acquire C_j,s,z in soft J once R_j is supplied.

### Actual acquisition bill

All R_j, and their D_j if (1) is wanted, are acquired with the OLD shared monic block evaluator, with a constant dual-number overhead for derivatives:

    soft O(J+sqrt(Jh))=soft O(K^(3/2)).          (3)

Repeated evaluation points and collision zeros are allowed. This pays actual block coefficients, ALL starts, tails and products. After that, (1), (2) and the explicit regularized solve cost only soft J. A black-box M action does not avoid the input bill: M*1-J*1 is exactly the full missing R_j vector. Merely specifying G by a short q-recurrence is not acquiring that diagonal.

## 3. Execute the tempting rank-two displacement generator

Let E=diag(y_j). The regularized matrix M above obeys

    E M-M E=y*1^T-1*y^T.                        (4)

This rank-two right side is fully acquired in soft J and is independent of R_j. The reason it does NOT supply a cheap generator representation of M is exact: the operator X->EX-XE annihilates EVERY diagonal matrix. Its nullspace contains the entire J-dimensional diagonal; equation (4) gives none of the missing R_j. Even before considering additional coincident roots, it is not an invertible displacement operator.

To test a conventional repair, replace the right operator by E+cI, with a certified scalar c chosen to separate spectra if possible. Then

    E M-M(E+cI)=y*1^T-1*y^T-c*11^T-c*diag(R_j).

The unknown diagonal returns explicitly. Generically it has rank J; no claim is made about every native input or every other operator. The same issue occurs with a Stein operator designed to cancel the diagonal: exactly cancelling it leaves a diagonal kernel, while breaking that kernel reintroduces diagonal data. This is a scoped input-contract check for this concrete regularized solve.

## 4. A genuinely acquired alternative: short moments of the LEAF diagonal

Consider instead the diagonal operator L=diag_(j,i)(1-y_j q^-i), dimension m=Jh. Its determinant is the full unmarked product. The desired coefficients are traces against its adjugate, with weights 1 and w_j. Unlike the rank-two rectangular array, L retains the correct singular eigenvector.

Its first O(J) trace moments are actually cheap. Put

    p_t=sum_j y_j^t,
    c_0=h, c_t=(1-q^(-h*t))/(1-q^-t), t>0.

Then

    tr(L^s)=sum_(t=0)^s (-1)^t binom(s,t) p_t c_t. (5)

Weighted trace moments replace p_t by sum_j w_j y_j^t. Acquire the root polynomial and its weighted logarithmic-derivative numerator by product trees, yielding all these power sums through s0=2J in soft J. For t<=2J<=2K, q^t-1 is an actual supplied unit. Factorials through 2J are also units, since both characteristics exceed 16H. Thus (5) is ONE factorial convolution for all s<=2J, with its weighted companion, total soft J. This is a fully acquired finite statistic, not a formal Krylov oracle.

What it does not establish is a degree-J recurrence for L. At the good field, for any ONE fixed row its h diagonal values 1-y_j q^-i are distinct by the short q-order guard. Therefore the minimal polynomial of the full diagonal L has degree AT LEAST h, including at the unique zero. In the present family h=Theta(K²), rather than O(J). The leaf-array rank two does not change this polynomial degree. The ORDINARY trace does not lose those eigenvalues through characteristic cancellation here: each eigenvalue appears at most once per row, hence has multiplicity between 1 and J, strictly less than the good characteristic. After combining equal eigenvalues, all ordinary-trace weights are therefore nonzero. Vandermonde independence shows that this trace sequence itself has minimal recurrence degree equal to the number of distinct eigenvalues, hence at least h. The weighted companion may cancel weights, but does not by itself provide a faithful zero-eigenvector selector. This is a proof about these specific full-diagonal and trace realizations, not every cleverly chosen compressed observable.

The trace recurrence bound refers to a homogeneous constant-coefficient recurrence valid from s=0. If an initial transient is allowed, the zero-eigenvalue contribution disappears after s=0; the eventual recurrence still has degree at least h-1, which remains much larger than J. Consequently the acquired O(J) moments in (5) do not initialize the required full minimal-polynomial/adjugate procedure. A new finite relation selecting the zero eigenspace, with paid coefficient/seed acquisition, is still required. The old Hankel/Bethe tests already warn that short moment determinants count subsets rather than supply the long product; (5) changes the moment alphabet but does not evade that warning by notation.

## 5. Primary algorithms checked against these exact inputs

* [Villard, Kaltofen's division-free determinant algorithm differentiated for matrix adjoint computation](https://arxiv.org/html/0810.5647), sections 2–6, gives an explicit Krylov-based adjoint calculation and a division-free ring version. Its starting data are a supplied matrix/action and enough sequence terms; section 2 states its nonsingular Hankel hypothesis, while the ring construction explicitly pays power-series work. It supplies neither the R_j input in section 2 above nor an O(J)-degree closure for L. Selected derivatives inherit an actual circuit's cost; no cheap determinant/adjoint circuit is acquired by this citation.
* [Bostan–Jeannerod–Mouilleron–Schost 2017](https://arxiv.org/html/1703.03734), introduction and sections 3/6, takes displacement data with an invertible operator and supplied generators. Its fast multiplication is deterministic over its specified field inputs; the inversion/solve algorithms use Las Vegas regularization. Equation (4) fails the invertible-operator requirement and omits its diagonal kernel data. Field preconditioning or final determinant invertibility is not a certificate for every composite-ring pivot. The concrete known-diagonal solve above avoids that issue but not its input acquisition.

These source contracts were checked from the primary full texts. They refine the assessment of these particular candidate inputs, not a general exclusion of structured linear algebra. The older Bostan–Jeannerod–Schost 2008 regularized-Bezout audit remains prior credit; merely changing to the 2017 reference would not be new acquisition.

## Result and precise next interface

The full first-jet pair has exact rank-one pencil expressions. Its projective replacement has an explicit zero-safe J-dimensional regularized solve. A short weighted Krylov moment vector is acquired in soft J. None currently computes a valid pair at soft K: the row-diagonal solve needs the unacquired R_j, while the full-leaf Krylov construction retains a minimal polynomial of degree at least h.

A genuinely useful new primitive would obtain (2), or the promised coarse-tag ratio, directly from the acquired y_j,q,w_j and geometric-clock recurrence WITHOUT supplying the whole row-factorial diagonal or a length-h Krylov initialization. This is a concrete selected cofactor/action interface, not a demand for the full determinant or full adjugate. No such primitive or complete-query speedup was established in this pass.
