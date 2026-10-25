# Whole-input AP multiplier geometry with a short quadratic seed

23 October 2026. Scratch construction only; no repository edits. This note supplies a uniform arithmetic family and a fixed-k trace extension, not a sixth-rate factorizer. The inherited rank-two quotient-Gauss construction is credited explicitly. The long multiplicative query remains unpaid.

## Result and inherited scope

Assume the paid all-semiprime setup at a public odd prime scale r supplies

    N=P Q<=r^6, r=Theta(N^(1/6)), P<Q,
    P,Q>16r^2,

and a unit base with odd, coprime local orders exceeding 16r^2, or returns a factor. Auxiliary-prime divisibility and the finite input branches are already paid by that setup.

There is a public family of soft-O(r) quadratic descriptors, on the elementary AP catalog modulo H=r^2, with the following properties:

* Every surviving semiprime has a covered row and multiplier 1<=c<r whose true integer seed satisfies |sigma|<6r, independently of balance.
* Every descriptor has either nonzero leading coefficient |a|<r/20, or is a controlled linear row. Its constant-in-Z coefficient is a nonzero integer multiple C N.
* A public integer-zero screen examines at most one multiplier per AP row, in fact only the s=c=1 row in each factor-size window.
* Legally acquired roots of the nonzero a coefficients restore common curvature. Consequently one specified power trace of this full, all-size family is acquired in soft-O(r) bit work, with the same usual log N factors as the preceding trace result. Linear rows use a second common polynomial.

The arithmetic construction is **inherited quotient Gauss plus the AP small-multiple cover and public factor-size bins**. It is not a new second-vector or higher-degree lattice theorem. The inherited positive result is in `docs/semiprime-sparse-residue-gauss-audit.json`, derivation Sections 2-4, and `scripts/probe_semiprime_sparse_residue_gauss.py::weighted_gauss`. That older supplied-residue algorithm assumes direct factor residues and separately forces a!=0; those assumptions cannot be silently asserted for the present small-multiple input. This note retains the exact general lift inequality, allows the a=0 outcome, and handles it directly.

The prior adaptive stationary/window route in `semiprime-query-continuation-20261022/reports/quotient-centering.md` pays only one short window before its row/window count expands and optimizes to N^(1/5). Here only dyadic factor-size windows are used: O(log N), with r AP rows in each. The extra multiplier c is retained in the query and trace, rather than expanded as r additional giant targets. That distinction explains both the new whole-input geometry and why it is not already an explicit-list sixth-rate factoring algorithm.

## 1. Public windows and AP coverage

Put

    H=r^2,  S={s_t=1+r t:0<=t<r}.

For every unit P modulo H there is a unique c in {1,...,r-1} with cP=1 modulo r. Then cP modulo H is a unique s in S. Thus (s,c)->s/c is a bijection onto the units modulo H, but the unknown P does not reveal its c publicly.

Choose public factor-size windows

    P0=16r^2*2^j, j>=0, P0<=floor(sqrt N),
    P in [P0,2P0],
    X=2P0/r=32r*2^j.

There are O(log N) such windows. Every surviving smaller factor P is in at least one of them. The integers X are exact, satisfy X>=32r, and have O(log N) bits.

For its true small multiple cP=s+Hh,

    h=(cP-s)/H is an integer >=0,
    h<cP/H<r*(2P0)/H=X.

The lower endpoint is valid even if c is small: cP is positive with canonical positive residue s, so h cannot be negative. No h>=X/2 premise is used. These are windows in P, not old dyadic bins in h.

## 2. Exact quotient Gauss and its general nearest lift

For each public (s,X), construct the quotient lattice

    Lambda={(u,a) in Z^2: u+kappa a=0 modulo N},
    kappa=s^2 H^(-1) modulo N,
    D=s^2+H^2 X^2,
    F(u,a)=u^2+X^2 D a^2.

It has determinant N and explicit basis (N,0),(-kappa,1). The inverse H^(-1) exists because the setup has already handled gcd(H,N). Exact rank-two Gauss reduction in the integer Gram matrix diag(1,X^2D) returns a shortest nonzero vector. It uses polynomial logarithmic bit work per descriptor, exactly as in the inherited implementation.

The inherited Hermite calculation gives

    F(u,a)<= (2/sqrt(3)) N X sqrt D <=2N X sqrt D.

Do not discard the a=0 outcome. The old HX<=2sqrt N restriction was used to exclude it in the old theorem; it is not needed to run this arithmetic or to bound the lifted vector here.

Use gcd(H,s)=1 to solve H d-s b=u. All solutions have the form (d+v s,b+vH). Choose v nearest to

    -(s d+H X^2 b)/D.

The exact completion-of-the-square bound, before the old H^3<=N simplification, is

    d^2+X^2 b^2+X^4 a^2
      <=X^2 F(u,a)/D+D/4
      <=(2N/H+H^2/2) X^2.                              (1)

Indeed sqrt D>=HX, and s<H, X>=1 give D/4<=H^2 X^2/2. The integer algorithm uses exact rational nearest-integer divisions; the displayed square roots are only for the bound.

Here N<=r^6=H^3, in the direction opposite to the old direct-residue theorem. Inequality (1) is still applicable and gives

    d^2+X^2 b^2+X^4 a^2 <=(5/2)H^2 X^2.                 (2)

Thus

    |a|<=sqrt(5/2)H/X <=sqrt(5/2)r/32 <r/20,
    |b|<2H,
    |d|<2HX.                                          (3)

No second successive minimum or choice of a second LLL vector is used in this construction.

## 3. Exact lifted polynomial and nontriviality

Define

    L=H b-2a s,
    C=(H^2 d-H b s+a s^2)/N=(H u+s^2 a)/N,
    G(Z)=a Z^2+L Z+C N.

The quotient-lattice congruence makes C an integer. Equivalently,

    G(Z)=a(Z-s)^2+H b(Z-s)+H^2 d.                       (4)

So G(s)=0 modulo H^2 and G'(s)=0 modulo H, as required. All quantities use their actual signed integer lifts.

Crucially C!=0. If H u+s^2 a=0, coprimality gcd(s,H)=1 forces H|a. But |a|<r<H, hence a=0 and then u=0, contradicting selection of a nonzero quotient vector.

This also settles the full trivial polynomial subspace. The primitive linear polynomial Hx+s has gcd(H,s)=1. By Gauss's lemma, every integer polynomial of degree<=2 in its rational multiple span is (Hx+s)q(x) for an integer polynomial q of degree<=1. Every such multiple has G(0)=0, hence C=0, and conversely C=0 means exact divisibility by Hx+s. Our C!=0 certificate excludes the entire saturated integer-trivial subspace, including nonconstant multiples; it does not merely exclude one known linear vector.

The a=0 outcome is controlled rather than exceptional. The quotient condition then says u is a nonzero multiple of N. Since (N,0) belongs to Lambda and the selected vector is shortest, u=+N or -N. Consequently

    C=+H or -H,
    b=-u/s modulo r,

so b is a unit modulo r and modulo H. In particular b!=0. A linear row is still a nontrivial informative relation, not a constant or an integer-trivial polynomial.

The inherited code's public function currently guards HX and checks a!=0; it cannot be invoked unchanged on these parameters. Its exact Gauss and nearest-lift arithmetic is the construction being reused. Removing those two obsolete restrictions for this application is not counted as completed repository integration or a new backend.

## 4. Forced short seed for every factor-size window

At the true row h=(cP-s)/H, H is a unit modulo P. The quotient congruence is exactly

    H^2 d-sH b+s^2 a=0 modulo N.

Reducing modulo P and substituting h=-s/H modulo P shows P|g(h), where g(x)=a x^2+b x+d. Therefore sigma=g(h)/P is an integer. Since 0<=h<X and P>=P0, (2) gives

    |sigma|<=sqrt(3)*sqrt((5/2)H^2 X^2)/P
            <=sqrt(15/2) H X/P
            <=sqrt(30) r <6r.                         (5)

The common interval I=[-6r,6r] is consequently valid for every window and every surviving semiprime. The small-multiplier value c does not enlarge it beyond O(r).

Dividing G(cP)=H^2 g(h) by P gives the exact source identity

    H^2 sigma=a c^2 P+L c+C Q.                         (6)

For any unit base rho, put

    E=a c^2+L c+C N,
    K=E-H^2 sigma.

Then at the true leaf

    K=(P-1)(C Q-a c^2),                                (7)

so rho^E=rho^(H^2 sigma) modulo P.

The true K is nonzero without a limiting argument. If a=0, C!=0 makes C Q nonzero. If a!=0 and C Q=a c^2, the prime Q>r would divide a c^2, impossible because 0<|a|<r and 1<=c<r. No estimate comparing the giant exponent with the global order is used.

## 5. Exact public zero-exponent cleanup

For any candidate c and sigma, write y=c-s. Equation (4) gives

    K=a y^2+H b y+H^2(d-sigma).                        (8)

If a!=0, then |a|<r makes a an r-adic unit. If v_r(y)<2, the first summand in (8) has strictly lower valuation than both others, so K cannot vanish. Hence K=0 forces H|y.

If a=0, b is a unit modulo H by Section 3. Equation (8) then implies H|b y, so again H|y. Canonical 1<=c<r and 1<=s<H force c=s as integers. For this AP catalog the only possibility is

    s=c=1, sigma=d.

Thus at most one leaf per factor-size window needs testing, including multiplier-mask and interval membership. This costs O(log N) such tests in the full family, or a harmless soft-O(r) scan of all descriptors. It never restores r^2 multiplier pairs. If duplicate descriptors are retained, their labeled multiplicities are retained in the zero count h0.

The cleaned power sums subtract h0 at every positive k, since rho^(k*0)=1. True coverage survives cleanup by (7).

## 6. Legally normalize the varying curvature coefficients

The leading coefficients vary by row, but all nonzero a satisfy |a|<r/20. They therefore admit the same paid small-factor purification/outside-power construction already used for C-roots in the preceding packet.

Let V be the public family of all window/row descriptors, |V|=O(r log N), and form

    E0=r * product_(v in V, a_v!=0)|a_v|,
    L0=ceil(log_2 N), K0=E0^L0,
    gamma=beta_in^K0.

The explicit bit lengths of E0 and K0 are soft-O(r). Every prime divisor of E0 is removed completely from the local orders of gamma. Run the inherited first-nonunit detector through B=16r^2. It either returns a factor or certifies both surviving orders >B. Their oddness and coprimality are preserved by powering.

If the detector instead reaches a common order, coprimality forces that order to be one, hence gamma=1 modulo N. Factor recovery on this collapse uses the inherited small-factor product-tree method, not the polylog-annihilator theorem on the soft-r-bit K0: the known leaves of K0 are r and the |a_v|, repeated L0 times, all <=r. Descent keeps a base nontrivial in both fields and a known annihilating node product. At a final leaf, both nontrivial coprime local orders divide an integer <=r, and the inherited detector yields a proper factor. The path's total exponent-bit work and final detector cost are soft-O(r).

On the NoHit branch define

    beta0=gamma^E0,
    rho_v=gamma^(E0/a_v) for a_v!=0,
    rho_v=beta0 for a_v=0.

Negative a use signed powers. Outside powers for the whole list are acquired in soft-O(r) work by the inherited product tree. For every nonzero a_v,

    rho_v^(a_v)=beta0.

All these bases have the same local orders as gamma, still odd and >B, and those orders are coprime to r. Thus powering by H^2=r^4 loses no local order. These are supplied, legally acquired bases; exponent division is not being inferred from a modular integer inverse.

For the new base beta0, replacing beta0 by rho_v in the exponent K preserves vanishing separately in each hidden field, because both have exactly the same local orders. Coverage also follows directly from Fermat's theorem for each unit rho_v. Ring-product equality with the pre-purification beta_in query is neither needed nor asserted.

## 7. One-k trace of the full all-size family

For each descriptor v=(window,s), let

    Z_(v,c,sigma)=rho_v^(a_v c^2+L_v c+C_vN-H^2 sigma).

Use any supplied subset of descriptors, any common multiplier set D subset {1,...,r-1}, and common interval I subset [-6r,6r]. Public zeros are deleted as above.

For a specified positive k, put

    A_(v,k)=sum_(sigma in I) rho_v^(-kH^2 sigma),
    x_(v,k)=rho_v^(k L_v),
    w_(v,k)=rho_v^(k C_vN) A_(v,k).

The row-dependent geometric sum A_(v,k) is computed by division-free doubling, including all signed endpoints. It is O(log r) work per descriptor, not O(r) work per descriptor.

For the quadratic rows a_v!=0, form ONE common polynomial

    P_k(T)=sum_(c in D) beta0^(k c^2) T^c.

Then their full-family trace is exactly

    S_k^quad=sum_(v:a_v!=0) w_(v,k) P_k(x_(v,k)).       (9)

This follows from rho_v^(a_v)=beta0. The changing leading coefficient has become a changing row base/point and weight; these do not require a different multiplier polynomial for each row.

For the linear rows a_v=0, form the SECOND common polynomial

    P^lin(T)=sum_(c in D) T^c,
    S_k^lin=sum_(v:a_v=0) w_(v,k) P^lin(x_(v,k)).       (10)

The complete clean trace is S_k^quad+S_k^lin-h0. Both polynomials have degree<r; their total number of points is soft-O(r). Monic multipoint evaluation works over Z/NZ with repeated points and zero divisors and does not invert target differences.

This also supports native residue-tag restrictions: every s is 1 modulo r, so j=s/c modulo r corresponds to c=j^(-1) modulo r, independently of row and window. Common multiplier masks therefore implement native-tag masks. Arbitrary descriptor restrictions simply omit points. Row-specific seed subintervals can also be included by changing the weights A_(v,k); no shared interval assumption is essential for this fixed-k identity.

## 8. Complete resource and recovery ledger

All public rows, bins, integer operations and signs are acquired without P or Q. There are r catalog rows and O(log N) windows. Each Gauss reduction and nearest lift has polynomial logarithmic bit cost. Its inputs and output coefficients have O(log N) bits: X<=2sqrt N/r<=2r^2, and (2)-(3) bound all g coefficients. The lifted C N and every E,K have size O(r^8), hence O(log N) bits since r=Theta(N^(1/6)). Their actual integer signs are retained.

Row generation, the zero screen, small-factor purification and outside powers therefore cost soft-O(r) bits in total. For one k with O(log N) bits, the two polynomial constructions, all point/weight powers and division-free geometric sums, and the two monic MPE calls cost soft-O(r), with a conservative explicit form soft-O(r(log N)^2) bit work and soft-O(r log N) workspace. The O(log N) window factor is included by soft notation, not omitted as a constant.

For clarity on the window factor, write J=O(r log N), b=ceil(log_2 N), and L=b+log(1+k). The direct point/weight powering charge is O(J L M_int(b)), up to modular-reduction factors; monic MPE adds soft-O((J+r)b), and the geometric sums add O(J log r) ring operations. Thus the window multiplicity is present before soft notation is applied.

A proper collision gcd already factors N. Any remaining global leaf supplies a nonzero O(log N)-bit annihilator K of its supplied rho_v. Its local orders are odd and >16r^2, so the inherited unconditional unbalanced short-annihilator extractor costs soft-O(N^(31/192)), within soft-O(r). This handles unrelated global hits; there is no need to assert that every global leaf has the true row's sigma.

If desired, the true row's sigma is unique in the cap because the local order of rho_v^(H^2) is >16r^2>12r. But the arbitrary global-leaf recovery is already paid independently.

For a formal product prefix through degree h<=r, compute h clean traces and exponentiate the usual logarithm. All denominators 1,...,h are units since P,Q>16r^2. The proved bound remains soft-O(rh), not soft-O(r) uniformly in h. The full product has Theta(r^3 log N) labeled factors before restrictions, and its value at z=1 remains unacquired. This count is not a lower bound; it records the exact family for the missing shared contraction.

## 9. Checks, novelty boundary and remaining work

An independent inline implementation reused only the inherited exact quotient-Gauss and nearest-plane formulas, allowing a=0 and dropping the old HX/a!=0 guards. It checked 1,046 descriptors for r=43,67,101, including 624 quadratic and 422 linear rows. The test semiprimes had both a small-factor window and a balanced window, with P,Q>16r^2 and N<=r^6. For each descriptor it verified the exact quotient congruence, nearest-lift bound, |a|<r/20, C!=0, and the public-zero classification. At the six actual covered windows it verified integrality, |sigma|<6r, (6), (7), K!=0 and the local Fermat equality. Three restricted root-normalized trace identities were also checked modulo 59447*59747. These are finite algebra checks, not an empirical coverage theorem or an implementation/runtime certificate.

The proved coverage and bounds are the algebraic arguments in Sections 1-5. The exact Gauss primitive, smooth projection, outside powers, and annihilator recovery are inherited. The fresh composition is the all-input AP small-multiple family with a uniform O(r) seed, its controlled linear outcomes, and common-curvature trace normalization across all factor-size windows.

The original coefficient-one AP rows required balanced Q for their O(r) seed. The present family allows a_v to vary and then legally normalizes it in the query. No higher-degree assertion, lucky lattice vector, supplied hidden window, or uncharged row/multiplier expansion is used. This restores whole-input geometry and one-trace acquisition; it does not acquire the multiplicative detector, restriction-safe product contraction, full sixth-rate factor algorithm, or a new executable/Lean backend theorem.


If a later method targets a CRT-valued local collision count instead of the full product, it should query one factor-size window at a time. In one window, each row/multiplier pair has at most one local sigma hit because every q_v local order exceeds 16r^2>12r. Its local count is therefore at most r(r-1)<P,Q; a nonzero local count cannot cancel in the field characteristic. Counts aggregated across all O(log N) windows are not automatically below the factors. Separate window queries preserve the soft-r budget. This is an explicitly sufficient future interface, not an acquired count; the current trace formulas do not compute its indicators.
