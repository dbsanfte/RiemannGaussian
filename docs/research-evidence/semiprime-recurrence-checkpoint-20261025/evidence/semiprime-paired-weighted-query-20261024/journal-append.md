
## A complete scalar catalogue controller and the paired-index test, 2026-10-24

The complete catalogue now has a simpler initialized execution entirely
over Z/N. It requires neither a quadratic extension nor algorithmic
factor-bin masks. This is a proved controller simplification; its full
cost remains soft k^(5/4), and the target soft-k acquisition/one-sixth
theorem and full Lean bit proof are still open.

### One fixed modulus, one scalar query

Take K0=ceil(N^(1/6)) and the least e>=1 with k=2*3^e>=K0. This
known factored k is at the required scale. Handle parity, squares and
the small finite branches, then run the ACTUAL scalar controller from
the unbalanced-annihilator setup, including its HH range checks,
common-order branches and q=beta^(k^2) screen. Its successful output
has BOTH beta local orders odd and >16H, and BOTH q orders >16H,
where H=k^2. Consequently both primes exceed 16H+1. A separate
integer small-factor prefix is redundant here: the scalar controller
has no such input premise. No torus, D0 or rough cleaning is needed.
The paid Burgess input inside the controller/extractor remains in use.

Acquire the complete catalogue of all signed pairs 0<|ab|<k and
the four axes (+/-k,0),(0,+/-k), with EVERY phase
0<=lambda<H satisfying lambda^2=4abN modH. Only 2-adic and 3-adic
root lifting is now needed. The preceding divisor/root count gives
soft k rows, including arbitrary ramification and contents. For every
row acquire E=a+bN+lambda and Y=beta^E. Use the already proved common
M=ceil(4ceil(sqrt(kN))/H)+2 and h=2M+1<16H.

For coverage only, choose a factor R, S=N/R, its unit tag and a virtual
dyadic size bin. The old Gauss witness has |ab|<k and
|a|R+|b|S<4sqrt(kN), so its pair/phase belongs to the catalogue and

    HI=aR+bS+lambda,  |I|<M,
    E-HI=(R-1)(bS-a).

Fermat gives Y=q^I modulo R. The algorithm computes NO such bin or
ellipse filter; these are proof tools to establish one stored witness.
Scalar weighted rows and this Fermat identity are prior work, credited
to the signed palette source. The new composition uses the complete
bounded catalogue and its uniform coefficient bound.

Delete an ENTIRE row when E/H is an integer i0 in [-M,M]. This is
also the credited public zero-row mechanism, with a newly automatic
nonzero-witness premise: |a|<=k and S>16H imply bS-a!=0 for every
catalogue pair, including axes. If the witness row were deleted, its
collision and E=Hi0 would force q^(I-i0)=1 modulo R. The screened
order exceeds the entire window, hence I=i0, contradicting the displayed
nonzero integer identity. At least one genuine witness survives.

Perform ONE scalar product query between T=q^M Y for all retained
rows and q^s for 0<=s<h. The actual block-polynomial/MPE execution
and residuals cost soft(J+sqrt(Jh)). A proper gcd factors. A saturated
aggregate is localized with the same restricted evaluator to an actual
leaf, giving beta^K=1 GLOBALLY for explicit K=E-H(s-M)!=0. Its bit
length is O(log N). The existing all-semiprime short-annihilator
extractor accepts this exact input in soft N^(31/192)<soft k, without
knowing the local orders or factoring K. Every extra catalogue row is
therefore safe, even though its linear form need not be small at R.

This replaces the quadratic consumer's every-row correct-bin bound
with an actually licensed global-annihilator consumer. No local equality
is passed as a global certificate. If zero-row deletion breaks a root
coset, this execution does NOT apply a full-coset tiling formula to it.
All setup, roots, powers, deletion, query, localization and one recovery
call remain paid at soft k^(5/4)=soft N^(5/24). The inherited complete
finite fallback remains; the result is not a new global factoring record.

### Paired rows retain an exact normalization cost

A separate attempt acquired a FULL Gauss basis (a1,b1),(a2,b2), with
Delta=epsilon*k, and its two integral indices. Cramer's rule gives

    R=R0+epsilon*k*(b2 I1-b1 I2),
    S=S0+epsilon*k*(-a2 I1+a1 I2).

The public R0,S0 are integers with residues j,N/j modulo k. The
conic RS-N has EXACT content H=k^2. After division it is primitive
and irreducible. In the honest norm-certified index rectangle,
X1*X2=Theta(N/k^3) and the scaled primitive height is Theta(N/H).
Using raw N or N/k as that height would give a false small-root gain.
Hard, ill-conditioned bases and axis cases are included in these bounds.

The tested monomials in L1=b2I1-b1I2 and L2=-a2I1+a1I2 have integer
coefficient-change determinant k^[D(D+1)(D+2)/6] through degree D.
Their transport is not a free unimodular change. This is a calculation
for that monomial family, not a full auxiliary-lattice determinant or
a lower bound on every affine-aware root method. No faster guaranteed
index selector was obtained. The checked Gao–Feng–Hu–Pan rank-three
paper still performs a BSGS search of the same index scale; its balanced
fifth-rate logarithmic improvement is not such a selector.

The current Umans–Wang and He–Sahai primary contracts were also
rechecked. The earlier group-gap consumer already removed prefactoring
when an appropriate actual cover is supplied. This catalogue supplies
one soft-k target list and a horizon of scale k^(3/2), not two acquired
soft-k lists or a universal divisor cover. A short description of the
long seed progression is not its cheap acquisition. The known single-AP
obstruction is neither a refutation nor a solution of this construction.

Exact sources, independent reviews and preservation validation:
/tmp/semiprime-paired-weighted-query-20261024/. Preserve all prior
prefixes, all 270 frozen entries, HEAD and concurrent work. No numerical
campaign, backend lemma batch, exponent gain, commit or push.
