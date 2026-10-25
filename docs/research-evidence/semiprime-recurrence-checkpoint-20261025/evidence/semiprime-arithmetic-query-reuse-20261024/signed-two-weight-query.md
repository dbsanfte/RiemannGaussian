# A faster fixed-sixth-scale signed-weight query, with direct nonsplit recovery

24 October 2026. Scratch theorem and initialized algorithm. At k=Theta(N^(1/6)) the complete cost below is soft k^(5/4)=soft N^(5/24), improving the earlier fixed-k native execution soft k^(3/2). This is NOT a new global record: optimizing the same tradeoff recovers the already known soft N^(1/5) bound. The target soft N^(1/6) theorem remains open.

The useful changes are the long-query execution of an old signed two-weight family and a direct integer-quadratic consumer at whichever prime is nonsplit. Factor-size bins are attempted SEPARATELY. No smaller-nonsplit orientation, QRH palette, unique hit, extra sqrt(N/k) factor prefix or nonzero-annihilator oracle is needed by this query/consumer.

## 1. Prior credit and actual unconditional setup

The signed family, a*j^2=b*N modk and its LLL/interval tradeoff are prior work: journal section “Signed two-weight construction” near42399 and /tmp/semiprime-unique-acquisition-20261024/palette-acquisition.md SHA256 `85009ef8ac37c32cc1eef60aed0796c2a150ab756bc30c7c22d7fb2dc6c8159f`. Its direct execution paid soft(J+h+k), with h~k^(3/2) at constant interval parameter. The finite q-product baby/giant evaluator is also old. Neither arithmetic family nor the known fifth-bound optimization is claimed as new.

Unconditional Jacobi-minus discovery is /tmp/semiprime-recurrence-closure-20261024/frobenius-pairing.md SHA256 `215f1fd452452ce0719ff4b88b81f74b69c8a88dc12d80c8bb63a81d11e2e363`, Section1: the accepted unconditional Burgess/Lau--Wu bound supplies ONE negative fundamental D0 with Jacobi(D0,N)=-1 and factored conductor c0=|D0|=O(N^(5/32)), in soft N^(5/32). Its explicit finite/asymptotic convention is retained: failed public discovery/size guards take the inherited complete fallback, and those exceptions are finite. No QRH orientation theorem is used.

For a known factored k use /tmp/semiprime-jet-recurrence-20261024/constant-blocks.md SHA256 `30e92d4286611be1e6a70e28ac2c612e673e44a919d9c281e5d86486964153f7`: K0=ceil(N^(1/6)), guard54c0<=K0, least e>=3 with k=2c0*3^e>=K0. Then K0<=k<3K0, k even, c0|k/2. This uses only its paid modulus supplier, not its constant-block row family.

FIRST acquire the positive-integer prefix through16(3K0)^2 (or16k^2 after k is known), cost soft k by block polynomials/monic MPE. An endpoint>=N uses the inherited finite-input fallback; otherwise every leaf is belowN and any nontrivial gcd is proper. On the hard branch

    N=P Q<=k^6, P<Q distinct odd, P,Q>16H, H=k^2.

Hence k>16, since N>256k^4. No prefix through sqrt(N/k) is required.

Run the actual scalar/torus controllers at THIS k,D0 and rebuild changed bases. Exact sources: rough-torus-working.md SHA256 `6333f318c8bc1c1e88a398aaeff94efb83b0d2e6ead3d64d455317b41036dcda` in /tmp/semiprime-large-order-recurrence-20261024, and rough-index-cancellation.md SHA256 `283cb2dd6b39f1c84aa62e488703bc2f68a89e3fda2d6620aa14a59dc5236da0` in /tmp/semiprime-rough-block-composition-20261024. They factor or supply beta in(Z/N)^*, norm-one W in B=(Z/N)[tau]/(tau^2-D0), with BOTH local orders odd, k-rough and >16H. Their costs are soft k and do not presume which prime is nonsplit. Cross-prime coprimality of beta, although available, is not used here. The independent symmetric-supplier-audit.md in this packet SHA256 `e31daf2b017109cd844bda3b5814cac84bd000ac223a7571efe13c615ff1ac62` checks this exact orientation-free setup.

Put pi=beta W, barpi=beta/W, q=pi^H and rerun the actual coupled q screen through16H. It returns a factor or certifies all1-q^s,1<=s<=16H, units in B. At the one unknown nonsplit prime R, the beta/W orders divide R-1,R+1, are odd and therefore coprime, and each exceeds16H. Consequently

    ord_R(pi)=ord_R(beta)*ord_R(W)>256H^2.          (1)

Roughness makes H powering injective. A nonunit in the coupled short screen cannot vanish at this field, so its norm gcd is proper. All setup is soft k. R can be EITHER P or Q.

## 2. Explicit weighted Gauss rows for every public bin

Attempt all bins B0<=R<2B0, where B0 runs through powers2 with1<=B0<=N. There are O(log N) bins, covering both possible nonsplit factors. The current bin is not advice about R.

For each unit tag1<=j<k acquire s=[N*j^(-2)]_k and the integer basis

    (k B0^2,0), (s B0^2,N).

It is the diagonal image (a,b)->(a B0^2,b N) of Lambda_j={(a,b):a*j^2=b*N modk}, with determinant k B0^2 N. Exact two-dimensional Gauss reduction supplies a nonzero shortest vector v=(a B0^2,b N); extract a,b by exact integer division. This costs polynomial(log N) per row.

A reduced first vector satisfies ||v||^2<=(2/sqrt3)*k B0^2 N: its reduced second vector is no shorter, with angle sine>=sqrt3/2. This is a proof bound, not a real approximation oracle in the algorithm. In the CORRECT bin, writing S=N/R,

    |a|R+|b|S <= (2|a|B0^2+|b|N)/B0
      <=sqrt5*||v||/B0
      <=sqrt(10/sqrt3)*sqrt(kN)<4sqrt(kN).         (2)

This holds for EVERY row of that bin, all signs and zero coefficients. The pair(a,b) is never(0,0). Basis/vector entries and a,b have O(log N) bits even in wrong bins B0<=N. The O(k) actual rows per bin cost soft k including the bin loop.

Acquire the integer D_j=(a*j^2-b*N)/k, t_j=[D_j*j^(-1)]_k, and center

    ell_j=-2a*j+k*t_j moduloH, -H/2<=ell_j<H/2.

Then f_j(X)=aX^2+ell_j X+bN satisfies f_j(j)=0 modH and f_j'(j)=0 modk, hence f_j(j+ku)=0 modH for EVERY integeru. No inverse of a,b,2 or a content gcd modulo an unknown prime is used. Acquire the actual unit

    V_j=pi^(ell_j)*barpi^(a+bN).                  (3)

Its signed exponents have O(log N) bits. No hidden prime, positive multiplier, Fermat centre or character sign of j is supplied.

## 3. Cover the nonsplit factor, including the larger possibility

At j=[R]_k, gcd(R,H)=1 and f_j(R)=R(aR+bS+ell_j) is divisible byH. Thus

    I=(aR+bS+ell_j)/H is an INTEGER.              (4)

Locally at R, pi^R=barpi and pi^(R^2)=pi. For EVERY row this gives

    V_j=pi^(ell_j)*barpi^(a+bN)
       =pi^(aR+bS+ell_j) modR.                   (5)

Frobenius is used only in this proof; R is not an exponent input. At the own tag(4) gives V_j=q^I. R may be the larger prime. Multiple hits/global aliases are allowed, and all tags use the same constructor(3).

Compute Dceil=ceil(sqrt(kN)) exactly and set

    M=ceil(4Dceil/H)+2, h=2M+1.

By(2), |I|<4sqrt(kN)/H+1/2<M. Acquire targets T_j=q^M V_j and search t=0,...,2M, retaining original signed i=t-M. This is a fully initialized cover. From N<=k^6,

    h<=8k^(3/2)+7+8/H<16H  (k>16).

All needed q differences are guarded. All targets and a,b,ell,bin/tag/index labels are acquired in soft k.

## 4. Execute the long query and its restriction-safe localization

For the current bin compute E_bin=prod_j prod_(0<=t<h)(T_j-q^t) in B. Equivalently evaluate P_h at T_j^-1, retaining its known unit prefactors if exact E_bin is wanted. Choose d=min(h,ceil sqrt(Jh)); build P_d(X)=prod_(u<d)(1-q^uX), and evaluate it by monic MPE at EVERY actual giant argument q^(dg)T_j^-1. There are at most J*h/d arguments. Build/evaluate the one residual polynomial of length h mod d at all final actual starts too. Coefficients, arguments, outputs and products are paid. No target difference or collision value is inverted.

The bin cost is

    soft(d+Jh/d+J)=soft(J+sqrt(Jh)).              (6)

A proper norm gcd factors; gcd1 rejects this bin. For a saturated product norm, binary row/index restrictions use this SAME exact evaluator on restricted lists and shifted intervals. Norm multiplicativity guarantees a nonunit parent has a nonunit child. A proper child gcd factors immediately; otherwise descend a saturated child to an actual original leaf, in logarithmically many subqueries. This pays localization at the same bound up to logarithms, without unit target separation, uniqueness, interpolation or nonzero derivatives.

Do NOT aggregate all bins and decode an arbitrary selected leaf. Run each bin's complete bounded query/localization/decoder SEPARATELY. Wrong bins may factor or return bounded failure, then continue. In the correct bin every saturated leaf has the guarantee below, so wrong-bin choices cannot conceal its success.

## 5. Direct integer-quadratic consumer, including a=0 or b=0

A saturated norm LEAF in the correct bin vanishes as a whole element at the nonsplit field R. Undoing q^M gives V_j=q^i. By(1),(5), ord_R(pi)>256H^2 divides K=aR+bS+ell_j-H*i. For EVERY searched row/index, not just the private witness,

    |K|<8sqrt(kN)+(7/2)H+4<3H^2<256H^2.           (7)

Indeed(2), |ell_j|<=H/2 and H*M<=4sqrt(kN)+4+3H give the first bound. After dividing byH^2, N<=k^6 bounds its terms by8/sqrt k+3.5/H+4/H^2<3 on k>16. Therefore K=0 as an INTEGER.

The nonzero integer polynomial

    Q_leaf(X)=aX^2+(ell_j-H*i)X+bN               (8)

has actual proper factor R as an integer root, with O(log N)-bit coefficients. Extract/validate roots deterministically:

- For a,b both nonzero: test exact discriminant and both rational quadratic roots; retain integral roots1<x<N dividing N.
- For a=0,b!=0: test the nonzero denominator and exact divisibility in R=bN/(H*i-ell_j).
- For b=0,a!=0: test exact divisibility in R=(H*i-ell_j)/a; discard the other quadratic root0.

A correct-bin saturated leaf necessarily passes one test. No positivity, primitiveness or modular inverse of a or b is assumed. The polynomial cannot be identically zero since(a,b)!=(0,0). There is NO need to delete zero-coefficient rows or apparent scalar-trivial leaves: the actual mixed quadratic row(3), field-side equality and bound(7) establish(8) directly. Wrong-bin roots are accepted only after verifying a proper divisor; otherwise that bin returns bounded failure. This is a proved consumer for the actual rows and norm leaves, not an arbitrary auxiliary norm oracle. No global beta annihilator or factor-sum amplitude is needed.

## 6. Guaranteed completion and honest cost claim

At least one public bin contains the nonsplit R. Its own tag gives a nonunit leaf. If the norm gcd is proper, factor immediately; if it is saturated, every saturated leaf selected in this bin factors by(8). Thus the algorithm succeeds regardless of which prime is nonsplit. ONE unconditional D0 suffices; the earlier QRH smaller-orientation palette is not called. All inherited finite setup/size guard exceptions keep their old complete fallback convention.

All O(log N) bin-row lists and scalar/torus preparation cost soft k. With J<=k and h=O(1+sqrt(N)/k^(3/2)), equations(6) and paid localization give total

    soft(k+N^(1/4)/k^(1/4)).                     (9)

At fixed k=Theta(N^(1/6)), this is soft k^(5/4)=soft N^(5/24), versus the former native execution soft k^(3/2). It does not attain soft k and is slower than the already known global fifth-rate factoring algorithm. Optimizing this same parameter formula at k~N^(1/5) recovers the KNOWN fifth exponent, not a record. The older derivative-centred eta family and its parameter optimization are credited separately; they are not silently imported as starts here.

The completed change is a faster long-query execution and an orientation-free integer-quadratic consumer for an old signed-weight idea, with only the existing soft-k prefix/setup. No numerical coverage campaign, backend theorem, shared/frozen source edit or completed sixth-rate Lean bit-cost proof is claimed.
