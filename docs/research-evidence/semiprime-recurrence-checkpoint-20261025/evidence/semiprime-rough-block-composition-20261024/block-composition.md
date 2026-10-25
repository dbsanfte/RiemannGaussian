# Bounded angular width and an executed nonautonomous block composition

24 October 2026. Scratch only. This executes a polynomial-in-the-block-start composition on the actual native norm fibers, including a scalar determinant state and a rough-order Adams alternative. It gives a complete zero-safe terminal-value algorithm, but its optimized cost is the existing soft(J+sqrt(JL)), not a new exponent. The exact retained polynomial coefficient and the actual row-dependent seeds are displayed below; no general lower bound is inferred.

## Inputs, source credit, and retained recovery

Read the prior lawful moving quotient in `/tmp/semiprime-recurrence-closure-20261024/scalar-closure.md`, the initialized quartet and family expansion in its `shared-recurrence.md`, and the terminal Toda packet in `/tmp/semiprime-terminal-recurrence-20261024/`. They already distinguish scalar merging from acquiring all starts, moment/Toda amplitude from shift ratios, and a small row recurrence from its cumulative product. None is counted as new here. Constant Somos-4/5 cumulative mappings were already rejected in the intervening packet.

Current pinned inputs:

* `/tmp/semiprime-large-order-recurrence-20261024/rough-torus-working.md`, SHA256 `6333f318c8bc1c1e88a398aaeff94efb83b0d2e6ead3d64d455317b41036dcda`;
* its preceding joint graph note `recurrence-followup-working.md`, SHA256 `45c2f89d53d509bab46d43db3f2cc6d9f64e992c6748d4cc27a3df93268f41c1`;
* `/tmp/semiprime-quadratic-ideal-20261024/ideal-literature.md`, SHA256 `90f760d067f9de61a2950289c4f8aceba013cba521a2e4078053c2c2916ef77b`.

Over R=Z/N, B=R[tau]/(tau²-D) has rank two with its explicit conjugation and norm. All actual targets and their original labels are supplied:

    V_j=beta^E_j W^T_j,
    E_j=N+delta_j,
    T_j=ell_j+epsilon_j(N+a_j), epsilon_j=chi_D(j),
    z=(beta W)^H, H=k², L=2H+2, J<=k.

The W local orders are k-rough, odd and >16H, and H powering preserves them. The scalar beta guards and the actual CHANGED coupled-seed screen are retained. At the unknown nonsplit prime the beta and W local orders are coprime, but no such claim is made about split coordinates or the two different primes. All coordinates, factors and bit lengths are charged in the cited supplier.

Use the controlled public modulus and the factor-or-target-separation branch of the ideal report. Exact norm fibers have sizes r_d<=16 and their actual characteristic polynomials

    F_d(U)=product_(j in fiber d)(U-V_j)

are acquired, with sum_d r_d=J. There are Theta(k) norm labels in the full family; constant angular width is not a small number of fibers. Repeated actual targets may alternatively be retained by monic algorithms; the value algorithm below does not require target-difference inverses.

Proper norm gcds factor N. Saturated products are localized to an ORIGINAL row and index before using the nonsplit-field / scalar-beta decoder. The target of this report is the actual long product, not a new recovery oracle for an auxiliary polynomial coefficient.

## 1. Actual fixed-width quotient state, including the first nontrivial merge

For a fiber of size r, let C be the class of U in B[U]/F_d(U). Its multiplication matrix is the actual r-by-r companion matrix; r<=16 is constant and the coefficients of every such matrix have been acquired. A quotient operation for ONE fiber therefore costs only constant-many B operations. Across all fibers it costs soft J, not constant.

Keep the giant-block start as a formal scalar X, and define the ACTUAL reduced block

    R_b(C;X)=product_(a=0)^(b-1)(C-z^a X) mod F_d(C).       (1)

The initialization is R_0=1, R_1=C-X. The exact nonautonomous composition is

    R_(a+b)(C;X)=R_a(C;X)*R_b(C;z^a X) mod F_d(C).        (2)

All reductions are by the acquired monic F_d, and the quotient modulus is fixed here because only X changes. Thus (2) does NOT reuse the false scaling endomorphism U->zU modulo F_d; the companion variable C is unchanged. No inverse of a block value or pivot appears.

Execute the rank-two-fiber case, writing

    F_d(U)=U²-s_d U+c_d, C²=s_d C-c_d,
    R_b(C;X)=A_b(X)C+B_b(X).

For two arbitrary acquired states A C+B and A' C+B', multiplication gives exactly

    A_new=s_d A A'+A B'+B A',
    B_new=B B'-c_d A A'.                              (3)

In (2) the primed polynomials are actually evaluated at z^a X. Starting with A_1=1,B_1=-X, the first doubled state is

    A_2=s_d-(1+z)X,
    B_2=zX²-c_d.                                      (4)

This is an initialized two-coordinate, variable-start recurrence. Every coefficient for b=2 across all fibers costs soft J. It handles zeros without division; no generic diagonalization has been imported.

## 2. Take the terminal scalar before composition: the determinant still has an actual term

The fiber norm of A C+B is

    B²+s_d A B+c_d A².

Hence the first scalar fiber block is the fully acquired quartic

    H_(2,d)(X)=c_d²-(1+z)c_d s_d X
       +[z s_d²+(1+z²)c_d]X²
       -z(1+z)s_d X³+z² X^4.                         (5)

This is an actual elimination of the constant-width quotient, not merely naming its norm. For arbitrary r<=16 the corresponding determinant

    H_(b,d)(X)=det(R_b(C;X))
             =product_(j in d) product_(a<b)(V_j-z^a X)       (6)

is valid over the composite coefficient ring, including every zero specialization. Determinant multiplicativity gives the closed scalar relation

    H_(a+b,d)(X)=H_(a,d)(X)*H_(b,d)(z^a X).            (7)

Thus the scalar state has no unpaid additive determinant cross term in THIS normalization. Its start H_(1,d)(X)=(-1)^r F_d(X) is actually acquired. The remaining issue is executing (7) at all required starts without expanding its polynomial argument.

Here an exact coefficient can be followed, rather than just a maximal-degree count. In (1), the coefficient of X^b in the CONSTANT companion basis coordinate is

    (-1)^b z^[b(b-1)/2],                             (8)

a certified unit. It comes from choosing -z^a X in EVERY factor; every term involving a positive power of C has smaller X degree before monic reduction. Reduction changes companion powers but cannot increase that X degree. Therefore that coordinate polynomial has EXACT degree b. Similarly (6) has EXACT degree r*b, with unit leading coefficient

    (-1)^(r*b) z^[r*b(b-1)/2].                       (9)

For r=2, (9) is precisely the acquired z² X^4 in (5). Constant angular width does not make this particular polynomial-in-start state have bounded degree as b grows. This is a proof about the proposed state and its actual coefficient, not a lower bound for a different scalar-only algorithm.

All scalar block identities multiply at the terminal values. No saturated terminal is divided out. If H_(b,d)(x)=0 at a prime, it still has exactly the original product support of that fiber/block.

## 3. Both ways of carrying this state are fully initialized and priced

There are two honest implementations of (2)/(7).

**Evaluate before merging.** At X=1, all R_b(C;1) can be acquired collectively in soft(J+b): build the ONE degree-b polynomial product_(a<b)(U-z^a), then use a monic remainder tree against all acquired F_d. This supplies the actual constant-width states for ALL fibers at the first start, not separate black-box factorial calls.

But the next merge needs R_b(C;z^b), not its value at one. One can scale that same explicit degree-b input and run the remainder tree for each new start, paying soft(J+b) per giant block. Alternatively evaluate the single short polynomial at every actual shifted root z^(-bg)V_j by monic MPE, paying soft(b+J*L/b), the already known transposed completion. No operation here supplies the next scalar H_(b,d)(z^b) from only H_(b,d)(1).

**Retain the polynomial in X and perform binary coefficient composition.** All reduced companion-coordinate arrays in (1) have O(r*b) coefficients, and the total across fibers is O(J*b). Products using (2) and the explicit constant-width reduction pay those coefficient operations. Their highest coefficient (8) shows an actual degree being retained. A terminal-only alternative is to retain just all H_(b,d), whose total degree is J*b, again including actual coefficients.

This alternative does give a COMPLETE shared whole-family algorithm, with no unacquired varying scalar starts. Form the global actual polynomial

    H_b(X)=product_d H_(b,d)(X)
          =product_j product_(a<b)(V_j-z^a X).        (10)

Its start H_1(X)=(-1)^J F(X), F=product_j(X-V_j), is acquired in soft J. Binary coefficient composition

    H_(a+b)(X)=H_a(X)*H_b(z^a X)                     (11)

acquires every coefficient of H_b in soft(J*b) by fast polynomial multiplication; the balanced recursion has a geometrically dominated total coefficient budget. This proof does not assume the separate H_(b,d) were previously expanded. It also works for arbitrary b by its actual balanced split, with no coefficient oracle.

Now write L=rb+d, 0<=d<b. Acquire all r giant starts X_g=z^(bg), evaluate the SINGLE acquired H_b at them by monic MPE, and multiply the answers. The final shorter block is computed on its actual tail seeds. Since Norm_B(-1)=1, the scalar product of these block norms and tail norms equals exactly the requested Norm_B(product_(i<L)F(z^i)); the orientation signs in (10) disappear under the rank-two norm. At the B-valued level the full-block orientation sign is (-1)^(Jbr), retained if that value is requested.

All coefficients, giant nodes, evaluations and tail cost

    soft(J+J*b+L/b).                               (12)

The optimum is b about sqrt(L/J), clipped to [1,L], giving soft(J+sqrt(JL)). For J~k,L~k² it uses b~sqrt k, a polynomial with about k^(3/2) coefficients, and about k^(3/2) giant evaluations. Choosing b~k instead makes the short coordinate recurrence look attractive but requires J*b~k² explicit polynomial coefficients. Conversely the root-side cut optimizes b~sqrt(JL) and has the same old cost. Neither orientation yields soft(J+b+L/b) from the data actually acquired here.

Thus the proposed shared composition is an executed algorithm through the FINAL scalar, not just a startup lemma. It reproduces the covered exponent and isolates the scalar polynomial that this implementation expands. Omitting most of that polynomial would require a new initialized product-only contraction, not a consequence of (7) or (11).

## 4. Nonunits, restrictions, and final row/index recovery

Only known unit powers of z are used for scaling. All polynomial products and evaluation trees are monic on their divisor side. Repeated targets, repeated local spectral values and vanishing block values cause no arithmetic exception. There is no division by H_b(X_g), a companion-state determinant, s_d or a discriminant.

If an acquired block norm gcd is proper, it is a factor. If it saturates, retain its original g and hence the interval [bg,bg+b). Split the actual target-row list in half and recompute/evaluate its H_b at that SAME start, returning a proper factor or a saturated child. The sum of the recomputed degrees down one row path is O(J*b). Once a row is selected, descend the already acquired short seed factor tree at z^(-bg)V_j, paying soft b, to recover a proper factor or the ORIGINAL index bg+a. If different original row/index labels caused the two prime zeros, this descent yields a proper factor before an incorrect same-label inference. A saturated final leaf is precisely the ORIGINAL norm leaf Norm(V_j-z^(bg+a))=0 modulo N. It need not give whole-element equality on the split side. Invoke the predecessor's nonsplit-field/G_beta consumer: it returns a proper factor or a saturated ORIGINAL scalar beta leaf, whose bounded decoder is legal.

The root-side implementation instead keeps the direct (j,g) point labels from its MPE list and descends just the short seed tree. Both have the stated old total budget. Actual row subsets rebuild their degree-J' F; actual interval offsets use starts z^(u+bg), retaining u in final labels. The shorter tail has no overhang. The algorithm never replaces SAME-index support by a gcd of two independently multiplied coordinate tests.

## 5. Execute the rough small-power alternative

The additional roughness does allow a useful operation, but it does not shorten this composition. Put t=beta^(2H), v=W^H, n_j=beta^(2E_j), u_j=W^T_j as in the joint note. The actual whole-coordinate incidence is exactly

    n_j=t^i AND u_j=v^i at the SAME prime/row/index.  (13)

For any known POSITIVE integer m with O(log N) bits whose prime factors are <=k (in particular m<=k, or m=j² for a native tag), the power map on each local subgroup generated by W is bijective. Thus the angular condition in (13) is equivalent to

    u_j^m=(v^m)^i.                                (14)

No inverse exponent or hidden order is acquired to prove or execute this: just compute positive powers and use gcd(m,ord_p(W))=1 for the implication. The norm coordinate in (13) is retained, so this is an exact whole-incidence transformation on both local types; no claim about arbitrary unpaired split-component norm masks is needed.

For ONE common m of that stated width, acquire W^m once by binary powering and then all u_j^m=(W^m)^T_j in soft k; keep the same bounded norm fibers. A wider m would incur its actual exponent bit length and is not assigned this soft-k bound. Their angular fiber polynomials remain of degree r_d<=16; actual roots or constant-width companion powering acquire them in soft k. The seed angular base becomes v^m, and the coupled norm-family seed is changed accordingly if that formulation is used. RERUN its actual soft-k coupled-seed screen; the old split-side certificate is not imported. Coverage and the original same-leaf beta consumer survive, and rough W orders stay unchanged under m.

This is a fully paid alternative normalization. Its original index interval is still [0,L). Repeating (1)--(12) with the changed common base retains the actual highest coefficient (8) and fiber determinant degree r_d*b. Small-power invertibility did not identify b different consecutive seeds with one seed.

The native variable power m_j=j² offers a sharper symbolic repair, so execute it rather than dismiss it abstractly. With D_j=(N-a_j j²)/k and epsilon=chi_D(j), the exact INTEGER identity is

    j²*T_j = epsilon*N*(j-epsilon)²
               +k*[b_j*j²+D_j*(2j-epsilon)].        (15)

Expanding T_j=k b_j-2a_jj+epsilon(N+a_j) and substituting a_jj²=N-kD_j proves every sign and carry in (15). Because W is k-rough, angular powering by j² is now genuinely zero-support preserving in (13), rather than an unguarded claim that j is a unit modulo a hidden order. All transformed target exponents have O(log N) bits and their values are acquired in soft k.

But the transformed comparison is against (v^(j²))^i. The seed base is now ROW DEPENDENT. The known perfect-square N term in (15) has not changed this index coefficient, and the displayed carry is actual data that cannot be dropped. Expanding a separate degree-b short seed polynomial for every row costs soft(J*b); applying a shared binary composition would have to provide a new operation for these different bases, not the already acquired common-z block (11). Neither a native affine carry identity nor small-power injectivity supplies that operation here. This explicitly tests the roughness-based alternative without calling a different family of seeds a shared one.

## Scope and acquisition ledger

| Executed step | Paid cost | Delivered quantity / retained boundary |
|---|---:|---|
| Current rough W, native rows, norm fibers and actual coupled screen | soft k | covered constant-rank source and legal consumer |
| First quotient/scalar states (4)--(5), all fibers | soft J | actual nonautonomous initialization, no pivots |
| One evaluated block, all constant-width quotient states | soft(J+b) | real remainder vectors at ONE start |
| Polynomial-in-start quotient/scalar states | soft(J*b) | exact growing coefficient arrays; (8)--(9) retained |
| Global coefficient recurrence (11) plus all terminal nodes | soft(J+J*b+L/b) | actual full scalar product and safe localization |
| Root-side alternative | soft(J+b+J*L/b) | actual mixed points, old optimum |
| Common smooth-power angular reparametrization | soft k | exact joint incidence, same L and width |
| Native j² reparametrization (15) | soft k targets | row-dependent seed bases; their contraction not acquired |

All costs include constant-rank B arithmetic, integer exponent bits and the usual log N factors. No hidden field, unknown local order, unacquired initial matrix, auxiliary-pivot decoder or discarded zero tail is used. The new supplier makes the power transformation (14)--(15) legal and the bounded angular quotient genuinely available; it does not itself compress the time-block start variable. This attempt completes one shared nonautonomous composition at the existing soft(J+sqrt(JL)) cost and leaves a precise terminal-only contraction problem. No whole-query exponent reduction or generic algorithmic impossibility is claimed.
