# Shared linear summaries and sparse-zero counting: native-query applicability

26October2026. Requested paper study while the factoring goal remains PAUSED. Source: OpenAI, *The Exponential Time Hypothesis Is False*, dated17October2026, revised25October2026, supplied67-page [PDF](https://raw.githubusercontent.com/openai/math/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf) and `pdftotext -layout` extraction (hash in [sources.json](sources.json)). This note audits §§3–5, not the paper's full correctness or the separate high-arity tensor-network possibility in AppendixD.1.

**Main findings.** The common-zero theorem is explicitly for sparse fixed-degree equations over F2 on a Boolean cube. Section3 has a broader exact sum-product identity, but requires supplied polynomial factors, bounded total incidence degree and actual bounded-value summary fibres. It does not turn a fast linear action into a free summed diagonal. Original-factor-bit verification can be a degree2 INTEGER equation with O(logN) variables, but that expression does not fit the F2/sparsity/scope hypotheses. A separate linear-wire high-arity network is a different interface and is not excluded by this observation.

## 1. Exact shared-summary algorithm

Section3, equation(3.1), printedp.21, targets Z=sum_(x Boolean)prod_f Phi_f(x|I_f). The factors are POLYNOMIALS with rational coefficients (or coefficients in a commutative Q-algebra), not arbitrary rational functions of the Boolean inputs. Equation(3.2) bounds the degree of the WHOLE product in independent incidence variables Y_(f,v), so degree lost by identifying repeated inputs is not a free reduction.

Definition3.1, pp.21–22, supplies replacement rows P_(f,v)(T), P(0)=the original coordinate, of degree<=R. At Q positive integer points there must be partitions into groups of size<=2n/r and integer measurement matrices C_(t,g), with total row count<=2tau n and each row's absolute coefficient sum<=D. The crucial property is kernel invariance of every factor input outside its assigned group, not merely a small matrix rank.

Lemma3.2, equations(3.4) and the measurement-fibre formula, pp.22–23, is an exact finite Fubini/distributivity algorithm. For each measurement tuple y enumerate representatives in each Boolean group, sum each group's factor product over its restricted fibre, multiply those group sums, then sum y. It examines at most 2(2D+1)^c sum_g 2^|S_g| Boolean vectors. This lemma is ring-generic once the evaluators/invariance are supplied. Each vector still requires its actual factor evaluations and ring operations.

The L1 bound matters: a rank1 row (1,2,...,2^(n-1)) identifies every Boolean assignment and gives no compression. Encoding a native clock index as one binary-weighted integer measurement has D of order h, so enumerating its values would reintroduce h. A fast coefficient-kernel action is neither this bounded measurement nor a proof of the required fibres.

## 2. The paper DOES pay a diagonal-substitution step

Section3.4, pp.24–25, is a useful exact identity, not an assumed diagonal oracle. For polynomial p_x(X) of degree<=q,

sum_x p_x(x)
 =sum_(E subset[n],|E|<=q) sum_(U subset E) (-1)^(|E|-|U|)
       sum_(x Boolean, x_i=1 for i in E) p_x(1_U).       (3.10)

Boolean multilinearization plus Mobius inversion proves it. The actual cost is C_q=sum_(s<=min(q,n))2^s binom(n,s). When q>=n this is3^n; it is not free. In the application a correction input carries one Taylor parameter z, so its degree in the auxiliary X variables is<=the Taylor order, equation(3.9). Fixing X=1_U restores the supplied group separation before each restricted sum.

Hermite data at Q points require J=floor(dR/Q)+1 coefficients per point; the computation runs in A[z]/z^J. Proposition3.4 gives the vector count 2Qr C_q(2D+1)^(2tau n)2^(2n/r), and charges factor evaluation, rank-J algebra arithmetic, rational interpolation and storage. Equation(3.16), p.26, has three exponential contributions R/Q log(2Q/R), tau log(2D+1), and1/r. Thus an actual low-Taylor-degree replacement of a matched contraction could be useful, but cheap actions alone do not meet this interface.

## 3. How the low-degree replacement rows are constructed

Section4 uses an explicit auxiliary array of size D=r^(2Q), with coordinates labelled by pairs of length-Q group sequences, pp.26–27. Commuting involutions Pi_s swap the two labels at coordinate s. Put W0=(1/2)sum_s(I-Pi_s), V0=prod_s Pi_s. On their common eigenbasis W0 has integer eigenvalue j and V0 eigenvalue(-1)^j. The truncated binomial polynomial

f_I(z)=(-1)^A sum_(j<R)(-2)^j binom(z-A,j)

agrees exactly with parity on the R-consecutive-integer interval I. Hence M0=V0 f_I(W0) fixes the span of eigenvectors in that interval; only the binomial-tail exceptional vectors become measurement rows (Lemma4.1). Low polynomial degree also bounds label mismatches in every nonzero M0 entry (Lemma4.2). Multiplying each such entry by prod_(s mismatch)(1-T/s) yields the restoring rows(4.9)–(4.10).

This simultaneous parity/mismatch construction is stronger than independently interpolating Q arbitrary matrices: it proves the low-degree replacement and its shared kernel, rather than declaring an existing fast action low rank. Its auxiliary arrays are explicitly constructed at polynomial-in-D cost. The chosen Q makes D polynomially small in n, not in our native h by fiat.

Lemma4.7 requires 2(b+w)D²<=M and 2Qr²<=n, plus an explicit binomial-tail bound. Here w is maximum scope and b maximum variable incidence. Lemma4.8 gives the successful asymptotic parameters only when BOTH b,w<=polylog(n). It uses r~sqrt(log n)/(loglog n)², Q~log n/loglog n, R=O(sqrt(log n)), with a fixed exponent in the scope/incidence bounds. Failed finite-size checks use exhaustive search. A single global factor of scope n does not meet that low-scope guarantee just because there is only one factor.

## 4. What sparse common zeros means

Theorem2.2, printedpp.20–21, and Section5, pp.35–39, require polynomials OVER F2, Boolean variables, m_test<=c n equations, each given by <=(log n)^c monomials of degree<=fixed k. The stronger AppendixD.2 version still explicitly assumes F2. These are not stated integer or odd-prime-field common-zero theorems.

The exact reason is the parity lift. The integer lift L_i counts active monomials; P_i(x)=0 overF2 iff L_i(x) is even. Lemma5.1 constructs

p_ell(Y)=sum_(j<ell)e_j(Y)[Y(Y-1)]^j,

with degree(e_j)<=1 and p_ell(y)=1_(y even) mod2^ell for ALL integers y. Take ell=n+1, so the exact solution count<2^ell is recovered from that residue.

The shared truncated variable V in Lemma5.2 is important: retain total V-order<ell ACROSS ALL equations, then apply the nonmultiplicative coefficient-sum functional S_ell only AFTER multiplication. Every omitted order s is divisible by2^s at integer arguments. This yields whole incidence degree<=k(m_test+2(ell-1))=O(n), rather than the naive quadratic degree. Interpolation occurs rationally at nonBoolean replacement points; divisibility is used only after recovering the original integer data at T=0.

This is a genuine useful model for protecting a selected linear readout while truncating an ideal. But 2-adic divisibility does NOT vanish in our odd-modulus algebra, where2 is a unit. Our fixed source jets already have genuine nilpotence; the paper does not supply an analogous low-rank truncation for the h-long native residue. For an odd field, Y(Y-1) is not universally divisible by its characteristic; the analogous product over all residues has degree p. No unknown large-prime or integer-zero version with the same fixed-degree bounds is proved here.

Section3's Q-algebra presentation also is not automatically an algorithm over Z/N: all rational denominators must be licensed. If every encountered denominator has only sufficiently small prime factors then our preparation can sometimes certify it, so characteristic mismatch is not a universal barrier. That check does not repair a failed polynomial-degree, scope or sparsity hypothesis.

## 5. Execute native factor-verification input accounting

Let L=ceil(log2N). Two candidate factors can be represented with O(L) original Boolean bits:

P=sum_u2^u p_u, Q=sum_v2^v q_v,
P Q-N=0.

This is one degree2 INTEGER polynomial, with Theta(L²) monomials and L-bit coefficients, plus range/nontriviality conditions. It is an honest original-variable verification description. It is NOT a sparse F2 equation: reducing mod2 retains only the low-bit condition. A large odd-prime modulus changes the theorem, and the usual finite-field zero indicator raises degree by p-1. Merely splitting the monomials into many separate zero equations does not preserve their sum's zero set.

Standard full-adder compilation does fit the sparse F2 format: sum bit s+a+b+c=0 and carry c_out+ab+ac+bc=0, with product bits z+pq=0. A schoolbook multiplier uses Theta(L²) auxiliary wires/variables and O(n) constant-sparse degree2 equations. Deterministic gate equations give a unique internal extension, so factor counts and bit-prefix self-reduction are sound. But substituting n=Theta(L²) in Section5's 2^{O(n(loglog n)²/sqrt(log n))} upper bound does NOT imply N^(1/6), let alone a subpolynomial factorer.

Keeping only O(L logL) carry bits without all local adder gates does not immediately meet the format either: column sums retain Theta(L) quadratic terms, or their Boolean high-carry-bit polynomials have growing degree/dense elementary-symmetric expansions. This diagnoses straightforward compilers, NOT a lower bound excluding a clever linear-size representation. In particular a high-arity tensor network in AppendixD.1 is a DIFFERENT interface and may avoid Tseitin gate-wire counting; it needs its own audit.

If one DID provide a parsimonious bounded-degree/polylog-sparse F2 encoding with n=O(L) variables, the stated Section5 theorem would imply deterministic N^{o(1)} factor search asymptotically: count, then fix factor bits using O(L) additional count calls. That is a conditional implication of the paper, not an encoding established by §§3–5. The original-variable degree2 integer formula alone is insufficient to claim it.

## 6. Direct native selected-query test

Our finite Cauchy expression is sum_i p(q^i)/(F(q^i)+delta), or a marked tangent norm. Encode i in n=ceil(log2h) bits. Its natural expression q^i=prod_b[1+(q^(2^b)-1)x_b] is polynomial, but the RECIPROCAL remains rational in those bits. Taking A=Q(delta) does not make a denominator depending on x into a coefficient. Substituting replacement rows therefore gives a rational H(T), not the bounded-degree polynomial required by(3.3).

Every Boolean function has a degree<=n multilinear extension, but constructing/evaluating that PARTICULAR extension at nonBoolean replacement inputs can require the h native values. Using the cheap natural rational expression at those nonBoolean points instead changes the extension and invalidates the degree claim. The paper's fixed-Boolean substitution trick does not remove its nonBoolean BASE replacement evaluations. This is a precise missing handoff, not a general information or complexity obstruction.

Using the protected polynomial norm avoids rational factors but then either explicitly supplies h leaf factors (startup/cost h) or retains a product of large total incidence degree. A fast rational-Newton coefficient action or Sylvester boundary action from our earlier packets is not the bounded-summary invariance of Definition3.1. The paper DOES give an explicit diagonal recovery algorithm when those properties hold; no such properties are presently proved for the native GP/root graph. One should investigate an actual low-degree polynomial extension and bounded-value summary design, rather than equating “fast action” with that diagonal algorithm.

## Disposition

The useful identities are exact shared-fibre separation, the paid low-degree diagonal-substitution/Mobius formula, simultaneous commuting-involution replacement rows, and a shared filtration protecting a nonmultiplicative final readout. Their computational hypotheses are explicit and material. §§3–5 alone do not supply the native selected residue or an O(logN)-variable sparse-F2 multiplication compiler. They also do not exclude the separately proposed macro-FFT tensor-network route, which uses AppendixD.1 rather than these sparse-polynomial hypotheses. No implementation, repository edit or goal resumption is included.

Follow-up distinction: the separately audited AppendixD.1 macro-FFT construction in [review-factor-network.md](/tmp/semiprime-eth-paper-20261026/review-factor-network.md) DOES give a conditional N^{o(1)} factoring implication under that theorem's high-arity succinct-entry contract. It bypasses, rather than satisfies, the sparse-F2 compiler interface discussed in §5 above. The §3–5 conclusions must not be read as excluding it.
