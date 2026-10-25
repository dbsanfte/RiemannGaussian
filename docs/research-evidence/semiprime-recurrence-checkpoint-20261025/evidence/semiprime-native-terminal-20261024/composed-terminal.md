# Terminal composed-product norms with a fixed inner composition

24 October 2026. Scratch only. This constructs a zero-safe soft-(J+G) single terminal evaluation from the actual short factors. It isolates a more specific batched-norm contract, with a FIXED inner modular composition and geometrically rescaled outer coefficient vectors. Independent single evaluations cost soft m(J+G)=soft k²; the old blocked query remains soft k^(3/2). No nearlinear norm-batch theorem is inferred from ordinary composition or transposition.

## Input, primary sources and duplicate credit

Use the authoritative monic R of corrected native-moments.md, SHA256 `6fabb876e618ba1a5fafbda304f95d43c1b8d785e56de6062254b0ae63f3b20d`. Its q-log uses inverse roots, not the reversed polynomial's positive-root moments. The acquired main length is L0=2H, H=k², m=k, G=2k, Q=q^m, with actual native F(X)=prod_j(X-y_j) and constant-one/monic normalizations tracked. Use the canonical one-representative-per-tag family of degree J0<=k; after optional reciprocal augmentation, J denotes the ACTUAL degree of F and satisfies J<=2J0<=2k. Reciprocal augmentation may double that original degree; the actual scalar then represents a known-unit MAIN square. The two original tail factors remain acquired separately. The safe repaired 3H+2 variant uses G=3k and its own tail two, with D=JG<=6H<P,Q.

The input ring B=(Z/N)[tau]/(tau²-Dquad) has exactly one unknown nonsplit side. Its rank is two, all y_j and q are acquired units, and the actual rough bases and q screen are the ones already paid. All metadata have O(log N) bits. No local field, local order, arbitrary dense matrix, or long R vector is supplied.

Two primary papers were inspected directly:

* Bostan–Flajolet–Salvy–Schost, [Fast Computation of Special Resultants](https://cs.uwaterloo.ca/~eschost/publications/BoFlSaSc05.pdf), Theorem 1(1) and Section 3.1: full monic composed products are computed in O(M(JG)) field operations when characteristic is zero or exceeds JG, by multiplying root-power-sum sequences and recovering coefficients. The theorem outputs the full polynomial, not its short remainder.
* Kedlaya–Umans, [Fast polynomial factorization and modular composition](https://drops.dagstuhl.de/storage/16dagstuhl-seminar-proceedings/dsp-vol08381/DagSemProc.08381.5/DagSemProc.08381.5.pdf), Theorems 7.1 and 7.7 cover explicit modular composition/power projection over monic finite-ring extensions, subject to unit-separated interpolation points, with arbitrarily small fixed power overhead. Section 5 preprocesses the queried polynomial's actual coefficients. These are not implicit composed-product norm interfaces.

Cached primary PDFs are in this directory's sources/: BoFlSaSc05.pdf SHA256 `19db312c68f997949db342a050df568a009a340dd5026e4584e2c4fa59fcc375`; KU-dagstuhl.pdf SHA256 `6cc1b371b8f3cd7746db3efaadab9e01a41768f099a7db98e20ee8d05c9ad1a5`.

Duplicate check: the journal near 29640 already credits KU's composite-ring scope and the explicit-array boundary. The tensor-norm packet already tested the full Sylvester elimination over an outer quotient. The scalar resultant below is classical and is not claimed as a new factoring shortcut. The point of this execution is to replace an unspecified “modular composed product” call by an initialized single-output algorithm and the exact remaining nonlinear batch interface.

## 1. Acquire and evaluate a composed product without its JG coefficients

Acquire the actual geometric orbit polynomial

    Gamma_G(Z)=prod_(g<G)(Z-Q^g)=sum_(d=0)^G gamma_d Z^d.

Its G roots and monic product tree cost soft G; gamma_0 is a known unit. Define

    R(T)=prod_(j,g)(T-Q^g y_j)=F tensor Gamma_G.

For an ACTUAL supplied unit t, acquire the degree-G polynomial

    H_t(X)=X^G Gamma_G(t/X)
          =sum_(d=0)^G gamma_d t^d X^(G-d).          (1)

This expression is polynomial: no symbolic division by X occurs in its construction. Its leading coefficient gamma_0 and constant coefficient t^G are units. The G+1 coefficient scalings cost soft G, including all powers of t. Since F is monic, the standard resultant identity is EXACTLY

    Res_X(F(X),H_t(X))
       =prod_j y_j^G Gamma_G(t/y_j)
       =R(t).                                       (2)

There is no omitted leading coefficient of F or hidden factor depending on t. Thus a scalar terminal evaluation does NOT require acquiring the degree-JG composed product.

### Composite-ring divisions in the actual resultant

A fast field-style polynomial resultant algorithm can be run over B with an explicit factor-or-unit-or-zero classifier at every pivot. For c=c0+c1*tau, compute gcd(N,Norm(c)). A unit norm supplies c^(-1)=bar(c)/Norm(c); a proper gcd factors. If the norm gcd is N, at the unknown nonsplit prime c is zero in a field, so both c0,c1 are divisible by that prime. The coefficient gcd gcd(N,c0,c1) consequently is proper or N. The former factors; the latter means c is ACTUALLY zero in B and the usual polynomial degree drop is lawful. No nonunit pivot is silently inverted or passed to an original collision decoder.

Therefore execute fast Euclidean/half-GCD resultant arithmetic, stopping with a proper factor if classification finds one, otherwise treating only actual global zeros as zeros and only certified units as invertible. The field computation's exact identities and degree bounds transfer on that path. This costs soft(J+G) B operations and the usual gcd/log-bit factors, and returns the correct scalar (2), including global zero. It never inverts R(t). A globally zero or nonunit RESULTANT is localized using the original labelled products; it is not itself asserted to specify one row. This also has a paid single-evaluation consumer: split whichever of the F-root subset or geometric-root subset is larger, evaluate the two child resultants, and choose a nonunit norm child (or obtain a proper factor). Rebuild/reuse their actual monic subset polynomials. Alternating larger-side splits reduces the sum of degrees geometrically; all oracle work and subset coefficients along the path cost soft(J+G). The final pair is one stored row and one original g, not an auxiliary pivot.

This is a genuinely initialized short-input single evaluation, including all constants, pivot tests and normalization. It is consistent with the old soft sqrt(JG) single-point covered query when J and G are comparable; it is not a new asymptotic gain.

## 2. Match the actual terminal nodes and original labels

Take t_i=q^(-i), 0<=i<m. All nodes are acquired in soft m and have unit differences by the actual q screen. At each original root,

    t_i-Q^g y_j=q^(-i) V_j^(-1)
                                 [V_j-q^(mg+i)].     (3)

Thus (2) has exactly the original main index mg+i, in [0,L0). For a reciprocal-augmented root a0/y_j with a0=q^(1-L0), use its stored root-type flag and map mg+i to L0-1-(mg+i). Both are MAIN indices. Neither is automatically assigned to either of the original tail indices L0,L0+1.

Consequently independent evaluation of (2) at all m nodes gives R mod the monic-normalized P_m by ordinary interpolation, or its scalar norm/resultant by multiplying values and the known leading/sign phases. Work is

    soft(J+G+m) startup + soft m(J+G)=soft k².         (4)

All intermediate scalar arrays actually contain only O(J+G+m) elements per evaluation; no rank-JG tensor element is formed. This is an executed complete zero-safe algorithm. A proper factor discovered at any pivot is valid; otherwise any nonunit final product is localized to (3) with its original root/index map before using the nonsplit/G_beta consumer. The original tails or their squares are multiplied as actually acquired data.

## 3. The remaining batch has ONE fixed inner composition

Because F(0) is a unit, acquire

    xi=X mod F, v=xi^(-1),
    v=-F(0)^(-1) [F(X)-F(0)]/X mod F.

This is a supplied degree-<J vector with no root-difference division. In the actual rank-J algebra E=B[X]/F, (2) equivalently becomes

    R(t)=u_X^G Norm_(E/B)(Gamma_G(t*v)),
    u_X=Norm_(E/B)(xi)=(-1)^J F(0).                (5)

Now all t share the SAME monic F and inner polynomial v. Their outer coefficient vectors are just gamma_d t_i^d. Formula (5) specifies the exact desired additional primitive:

  Input: acquired F (degree J), Gamma_G (degree G), the one actual vector v=xi^(-1), and the m supplied geometric scalars t_i=q^(-i), with the existing factor/zero classifier.

  Output: the m SCALARS Norm_E Gamma_G(t_i*v), or only their product with restriction/leaf support; not the m full J-coefficient vectors Gamma_G(t_i*v) mod F.

  Desired work: soft(J+G+m), or a proved improvement on the original soft sqrt(JGm) query, including preprocessing and all inverse/zero branches.

All input arrays total O(J+G+m). There is no hidden arbitrary J-by-m matrix. The ordinary modular-composition map for fixed v,F is linear in the G outer coefficients and can be preprocessed/transposed as such; its postcomposed norm in (5) is nonlinear. Transposing the fixed composition circuit supplies a linear projection, not the norms of these geometrically rescaled inputs. Calling a composition routine m times acquires m degree-J residue vectors; the explicit route pays for them, although (5) does NOT prove that any scalar-only algorithm must do so.

KU's ring scope is applicable to B itself. For degree-O(k) composition, the required O(k^(1+epsilon)) unit-separated scalars for any fixed sufficiently small epsilon can be supplied by initial integer residues below min(P,Q)>16k². But that valid hypothesis does not change its output interface to the nonlinear batched norm in (5). Even its power-projection transpose is an explicitly sized linear output sequence. No strict soft-k or scalar-norm batch theorem follows from its small-power overhead bound.

Trying the composition over a rank-m carrier for all t at once must also pay its coefficient bit width/rank; moreover a monogenic presentation for a tensor tower cannot be assumed without construction. Granting such a presentation still does not make a rank-m ring operation constant cost. No uninitialized extension encoding is used in (4) or (5).

## 4. Test the primary full composed-product algorithms and the endpoint

The BFSS full composed-product algorithm is actually executable here, with corrected inverse-root q-log if working at the constant end, or positive root sums and reversal if working at the monic top end. Its O(M(JG)) field construction extends for this particular route using formal products/logarithms and only integer divisions <=JG<P,Q and constant-unit series inversion. Acquire both input moment vectors through JG, multiply entrywise, recover all coefficients. This costs soft JG=soft k². It is a valid alternative completion, not a free way to present Gamma_G(t_i*v)'s norms in (5).

Likewise the KU evaluation data structure for the HIGH-degree R is initialized from R's actual coefficients. Preprocessing at degree JG cannot be booked as soft J+G merely because those coefficients come from two short factors. This is an exact mismatch with that theorem's supplied input, not a generic composed-product lower bound. A new implicit preprocessing algorithm from F and Gamma_G would be precisely a solution of the specialized batch above.

One can instead reduce the resultant problem modulo P_m and operate in B[T]/P_m. Its formal result is correct, but literal arithmetic retains rank m. In the earlier tensor/Sylvester execution, the resulting pivot coefficients or an E-valued H_t array were not free. The current single-point construction cleanly exposes that cost, while leaving open an algorithm acting only on the scalar norms. Replacing (5) by an ordinary determinant of all paired Vandermonde values would again change the desired zero mask and is not used.

The best retained full query therefore remains soft sqrt(JL0), plus the acquired tail, rather than (4)'s soft m(J+G) or the full composed-product construction's soft JG. The new exact contract is the nonlinear batch of NORMS of a fixed modular-composition map with a geometric diagonal rescaling of ONE supplied outer coefficient vector. Its objects and a complete safe per-output realization are initialized here; a shared soft-k implementation has not been established. No primary-source theorem was invoked on missing coefficient arrays, no original witness was assigned to an auxiliary norm sum, and no generic impossibility or factoring-rate improvement is claimed.
