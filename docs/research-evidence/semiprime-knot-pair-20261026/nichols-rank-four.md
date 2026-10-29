# Executed diagonal Nichols rank-four R, rotations, and trefoil scalar

26 October 2026. Scratch symbolic derivation; no numerical campaign, Lean work or repository edits. **Result:** the surviving diagonal Nichols module has a lawful, explicitly rigid four-state R over the native ring. A normalized symbolic trefoil evaluation is computed below. Its mixed correction is additive, not a known unit multiplier of the two Alexander values. This does not establish a faster prefix algorithm or an attained native counterexample.

## 1. Source and finite specialization

Use Garoufalidis–Kashaev, *Multivariable Knot Polynomials from Braided Hopf Algebras with Automorphisms*, Publ. RIMS 62 (2026),75–114, https://ems.press/content/serial-article-files/52259?nt=1 ; equations (7),(19),(21),(96),(110)–(116), Proposition 7.4 and Theorems 3.6–3.7. This is the **diagonal** Nichols construction, not the failed independently weighted KM Hecke construction.

Write z=q_12*q_21, choose q_12=−1, q_21=−z, and set the scaling parameters a,b with abz=1. In the alternating-word algebra x_1²=x_2²=0, define

    e0=1, e1=x1, e2=x2, e3=v=x1x2+b*x2x1.

The diagonal braiding between words is the scalar product of the generator crossings. All maps below are defined over Z[a^(±1),b^(±1)], with z=(ab)^(-1). Unlike the KM Hecke map, a diagonal scaling satisfies separate braided naturality, since every crossing is a scalar interchange.

The right coaction is the ordinary coproduct restricted to this span:

    Delta e1=e1⊗e0+e0⊗e1,
    Delta e2=e2⊗e0+e0⊗e2,
    Delta e3=e3⊗e0+e0⊗e3
       +(1−zb)e1⊗e2+(b−1)e2⊗e1.                    (1)

For any word u, the right action on a primitive generator is

    u▷x_j=u*x_j−t_j*chi(u,x_j)*x_j*u,
    t_1=a, t_2=b.

Consequently

    e0▷e1=(1−a)e1,  e0▷e2=(1−b)e2,
    e1▷e2=e3,       e2▷e1=za*e3=e3/b,
    e3▷e1=e3▷e2=0,
    e0▷e3=(2−a−b)e3.

The equal-generator actions and positive-degree actions on e3 are zero. The last formula follows by expressing e3=x1x2+b*x2x1 and using the associative action. These formulas prove closure of the coaction/action, not merely existence of an invariant vector. The basis is free because the coefficient of x1x2 in e3 is 1.

The generic source proposition assumes z not a root of unity. Here the explicit polynomial/Laurent identities extend to all specializations with a,b,z units: establish YB generically from the source module, then specialize its denominator-free braid identity over the universal Laurent ring. Alternatively the explicit stable action/coaction comes from the alternating-word braided Hopf algebra before imposing any further root-of-unity Nichols relations. No native root order is replaced by an auxiliary torsion assumption. The native specialization a=eta^(2i+1), b=eta^(−2i−3), z=q=eta² satisfies abz=1 exactly.

## 2. All sixteen R images

Abbreviate ij=e_i⊗e_j, and put A=1−a, B=1−b, E=A+B. Source (21) gives

    R00=00,
    R01=A*01+a*10,              R02=B*02+b*20,
    R03=E*03−A*B*12−b*A*B*21+a*b*30,

    R10=01,                    R11=−a*11,
    R12=03−b*21,               R13=A*13+a*b*31,

    R20=02,                    R21=(03−12)/b,
    R22=−b*22,                 R23=B*23+32,

    R30=03,                    R31=13/b,
    R32=b*23,                  R33=33.                 (2)

Thus the complete local input costs O(1) ring operations. No 1−a, 1−b, Alexander value or native root difference is inverted. Its multidegree blocks give

    det R=(ab)^4=z^(−4).                              (3)

For example the four-dimensional (1,1)-multidegree block, in order 03,12,21,30, is

    [[ E,    1, 1/b, 1],
     [−AB,   0,−1/b, 0],
     [−bAB, −b,   0, 0],
     [ ab,   0,   0, 0]],

with determinant ab. The remaining blocks have unit determinants as well. This distinguishes the lawful R from the prior formal KM table, which had a nonzero braid defect.

## 3. Explicit inverse and rotations; all pivots are units

The inverse images are

    R^(-1)00=00,               R^(-1)01=10,
    R^(-1)02=20,               R^(-1)03=30,
    R^(-1)10=(01−A*10)/a,      R^(-1)11=−11/a,
    R^(-1)12=30−b*21,          R^(-1)13=b*31,
    R^(-1)20=(02−B*20)/b,
    R^(-1)21=(30−12)/b,        R^(-1)22=−22/b,
    R^(-1)23=32/b,
    R^(-1)30=[03−AB*12−b*AB*21+(2AB−E)*30]/(ab),
    R^(-1)31=13/(ab)−A*31/a,
    R^(-1)32=23−B*32/b,        R^(-1)33=33.           (4)

Use the source's partial transpose T=tilde R: an R coefficient ij→kl contributes the same coefficient to T:(k,i)→(l,j), with the first input and second output interpreted as dual basis labels. Its complete table is

    T00=00+A*11+B*22+E*33,
    T01=10+32,                 T02=20+31/b,
    T03=30,
    T10=a*01−AB*23,            T11=−a*11+A*33,
    T12=−21/b,                 T13=31/b,
    T20=b*02−b*AB*13,          T21=−b*12,
    T22=−b*22+B*33,            T23=b*32,
    T30=ab*03,                 T31=ab*13,
    T32=23,                    T33=33.                (5)

Then det T=(ab)^4. The following sparse solves give its **entire inverse**, avoiding a hidden matrix inversion. For output coordinates y and input coordinates x with y=T x:

    x00=y00,
    x11=(A*y00−y11)/a, x22=(B*y00−y22)/b,
    x33=y33−E*y00−A*x11−B*x22;

    x01=y10, x10=y01/a,
    x23=(y32−y10)/b, x32=y23+AB*y01/a;

    x02=y20, x20=y02/b,
    x13=b*y31−y20, x31=(y13+AB*y02)/(ab);

    x30=y03/(ab), x03=y30,
    x21=−y12/b, x12=−b*y21.                            (6)

For the other rotated matrix U=tilde(R^(-1)), use (4) and the same explicit index permutation, so no extra data are needed. Its determinant is (ab)^(-4). To make its rotated inverse equally explicit, put C=(2AB−E)/(ab). For y=U x the full solve is

    x33=y33,
    x11=−a*y11−A*y33, x22=−b*y22−B*y33,
    x00=y00+A*x11/a+B*x22/b−C*y33;

    x23=y32, x32=b*y23,
    x10=y01−y23, x01=a*y10+AB*y32;

    x13=ab*y31, x31=y13/b,
    x20=y02−y13/b, x02=b*y20+b*AB*y31;

    x30=y03, x03=ab*y30,
    x21=−y12/b, x12=−b*y21.                            (7)

Equations (2),(4)–(7) acquire every crossing orientation required by source §2.2. All pivots are a,b or ab, hence certified units over the native composite ring. This is a full finite-ring rigidity check, rather than importing generic-field invertibility. Endpoint Alexander collisions do not affect it. Native order bounds are needed for the source generation argument and later zero claims, but not for any inverse in (4)–(7).

## 4. Explicit scalar normalization

Set the enhancement mu=diag(1,−1,−1,1). Multidegree preservation gives [R,mu⊗mu]=0. Directly from (2),(4),

    tr_2[R*(I⊗mu)]=I,
    tr_2[R^(-1)*(I⊗mu)]=I.                            (8)

For the first equation the four diagonal entries are

    1−A−B+E,  a+A,  b+B,  1,

all 1. For the inverse they are 1, (1−A)/a, (1−B)/b, and

    1+A/a+B/b+(2AB−E)/(ab)=1.

Thus both positive and negative curls have scalar 1 under this enhanced partial-trace convention. The unknot cut endomorphism is I. The ordinary closed trace vanishes because tr mu=0; one must use the cut/partial closure, not divide by that trace. This explicitly fixes the normalization needed below, rather than treating a YB solution alone as a scalar knot invariant.

## 5. Symbolic trefoil calculation, with every mixed term retained

Take the closure of the positive two-braid sigma_1³ and cut its first strand. In the normalization (8), its endomorphism is

    J_trefoil=tr_2[R³*(I⊗mu)].

Multidegree makes it diagonal. The four diagonal entries can be computed in the small blocks above. For entry 00,

    J00=1−(A³+2aA)−(B³+2bB)
           +E³−4EAB+2AB+2Eab
       =1−AB(a+b).

For entry 11 the terms are

    aA+a³−AB(a+b)+A³+2aA=1−AB(a+b),

and entry 22 is the exchanged expression. Entry 33 is

    1+abE−aA−bB=1−AB(a+b).

Hence the FULL cut endomorphism is proved scalar for this knot:

    J_trefoil(a,b)=[1−(a+b)(1−a)(1−b)] I_4.            (9)

No conjectural all-knot scalarity statement is needed. Mirror/reciprocal conventions do not change the ordinary reciprocal trefoil Alexander polynomial K_3(T)=T+T^(-1)−1. Comparing (9) with its two-value product gives the exact identity

    J_trefoil(a,b)=ab*[K_3(a)K_3(b)+1−ab] I_4.        (10)

At the native adjacent reciprocal resonance ab=q^(-1), the prefactor ab is a unit and the retained additive correction 1−q^(-1) is also a certified unit. Therefore the correction is not generally an innocuous multiplicative unit. If the diagonal product were zero, this scalar would instead be a unit; conversely its zero would impose K_3(a)K_3(b)=q^(-1)−1, not the desired product-zero equation.

**Essential diagnostic limitation.** For this particular trefoil polynomial, K_3(a)=0 implies a has order 6 in residue characteristic greater than 3: a²−a+1=0 and a³=−1. The native arguments have odd order, so this zero cannot occur on the prepared native branch. Thus (10) is actual symbolic knot evidence for a nontrivial coupled amplitude, not an attained native collision counterexample or a proof against every possible zero-preserving rule for other knots. Neither an explicit semiprime example nor an unsupported all-knot formula is claimed.

At q=1 on the same resonance, b=a^(-1), (10) reduces to K_3(a)², agreeing with the independently proved decoupled tensor construction. The native q is not 1, and its correction in (10) must not be discarded by that specialization.

## 6. Cost and the remaining native test

All R/rotation/enhancement data cost O(1) per specified native pair, using only acquired powers and unit inverses. The trefoil scalar (9) costs O(1); the original trefoil Alexander factors are also O(1). These are actual computations, not expanded 4^crossing state sums. They do not evaluate the arbitrary acquired sparse-Seifert knot's coupled invariant, which can contain knot information beyond K(T).

For a general native K, a useful next identity would acquire its normalized coupled scalar or correction from the O(L)-entry Seifert input, prove its zero/nonunit relation to K(a)K(b), and compose it through the geometric pairs without losing the correction. The current symbolic trefoil calculation supplies a concrete normalization and a concrete correction for the smallest nontrivial knot, and shows that simply declaring the resonant four-state scalar equal to a product is incorrect as a polynomial identity. It does not supply a soft O(L+sqrt m) prefix oracle. Existing acquisition and original-label recovery costs remain unchanged.

## Convention qualification for the trefoil comparison

The calculation in §5 fixes its local operator, enhancement and braid word R³. Its scalar is

    F_plus(a,b)=1−(a+b)(1−a)(1−b).

Kohli arXiv:2505.08296 Proposition 2.18 at n=1 instead prints, in its Ishii variables,

    F_plus(a^(-1),b^(-1)).

Therefore the calculation must not be cited as an established identification of the **same canonical trefoil/mirror and parameter convention** with that table. A simultaneous variable inversion, a braid/mirror change, or the older/newer representation convention can explain the comparison, but the complete diagram/braiding dictionary has not been proved here. Equation (9) is the scalar for the explicitly specified operator convention, not an independently verified canonical-label LG table entry. The reciprocal ordinary Alexander polynomial is unchanged by these inversions, so the qualitative conclusion “the mixed amplitude is nontrivial” remains, while the exact additive term must follow the chosen dictionary. Under simultaneous inversion, (10) becomes

    F_plus(a^(-1),b^(-1))
       =(ab)^(-1)[K_3(a)K_3(b)+1−(ab)^(-1)].

At abz=1 these two corrections are 1−z^(-1) and 1−z respectively; both are certified units on the native continuing branch, but they are distinct formulas. Neither may be silently substituted for the other's scalar. The figure-eight primary-table audit in `scalar-audit.md` is separately invariant under both relevant variable inversions and avoids this particular ambiguity.
