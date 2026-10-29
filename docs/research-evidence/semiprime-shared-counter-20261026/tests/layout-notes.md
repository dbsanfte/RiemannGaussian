# Constructive shared layout: implementation and audit

Author implementation, 26 October 2026. Source: *The Exponential Time Hypothesis Is False*, Section 4, pp. 26–34, especially Lemmas 4.1–4.7 and equations (4.7), (4.9), (4.10), (4.14), (4.15). Local source `/tmp/semiprime-eth-paper-20261026/paper.txt`, lines 1455–1925. This is a dense standard-library exact implementation of the construction, not a simulation claiming the asymptotic speed has been demonstrated.

## Files and interface

`../shared_layout.py` exports:

- `build_layout(n, scopes, r, Q, R, A0, *, tau=Fraction(1,2), labels=None, require_lemma=False)`;
- `construct_layout` with keyword-only parameters and `require_lemma=True` by default;
- `lemma_hypotheses`, `tail_probability`, and `deterministic_labels` for independent checks.

The returned object has `n,r,Q,R,D,scopes`, methods `groups(t)`, `factor_group(t,f)`, `measurement_rows(t,g)`, `form(f,v)`, and `validate(quantitative=True)`. Variables/factors/groups are zero-based; points are the actual integers `t=1,...,Q`. `form` maps a global variable index to a tuple of rational coefficients in ascending powers of T. Restricted measurement columns follow exactly the order returned by `groups(t)[g]`. Empty-scope factors use group zero and have no substitution rows.

Root owns `../shared_parameters.py`; parameter scheduling is deliberately not duplicated. The production wrapper should pass the exact tau and `require_lemma=True`. A failed guard requires its exact finite-size fallback. The algebra-only constructor mode permits R=Q for the paper's illustrative Remark 4.4 and other tiny controls. It still verifies exact restoration, degree, integer measurements and rational kernel separation, but **does not assert** the quantitative measurement/group bounds. It is not a bypass of the production guard.

All variables must occur in at least one scope. If they do not, the caller must explicitly add distinct constant-one unary factors, adjust occurrence statistics, and retain the original Boolean variable count. The module never silently adds independent variables or silently changes factor indexing.

## Executed construction

1. Enumerate whole words in `[r]^Q`. Choose all variable words `a_v`, then nonempty-factor words `d_f`, in deterministic index/lexicographic order by exact conditional expectation. No supplied random labels are needed. Optional supplied labels are an explicit diagnostic input, checked for shape and empty-factor convention; all quantitative checks still run in guarded mode.
2. The exact potential is `Phi/(M(b+w))+Xi/(Qn)`. For incidence-pair indicators, variable-word and factor-word equality probabilities multiply because their label families are independent. Same-index equality is 1; two fixed unequal words give 0; otherwise equality of distinct independent words has probability `r^-Q`. A coordinate equality for Xi instead has probability `1/r`. Thus code computes precisely the conditional expectation without enumerating K^4 combinations. Candidate minimization cannot increase it; the entire exact history is retained.
3. Enumerate the product orthogonal exchange eigenbasis, with local vectors `e_aa`, `e_ad+e_da`, `e_ad-e_da`. Form `M0` from its spectral projectors with eigenvalue `(-1)^j f_I(j)`. Retain in `C^B` all basis vectors with j outside I. The matrix is explicitly materialized, including exact cancellation of entries forbidden by Lemma 4.2.
4. Construct every auxiliary coefficient as `delta_uy + M0[u,y]*(phi_uy(T)-1)`, where `phi=product_(s mismatch)(1-T/s)`. This is equation (4.10) without numerical cancellation at a special T. Assert support degree <=R-1.
5. Assign the kth incidence with label u to `(copy=k,u)`. Fill that occupied position with its original Boolean variable and leave unused positions zero. Several positions may contain the SAME variable, and their coefficients are added on projection. This is not an enlarged counting space.
6. Apply equation (4.14) to obtain the actual forms, and equation (4.15) to obtain common integral measurements and their group restrictions. Keep all measurement rows, including zeros. Assert common denominator `(R-1)!Q!` for all actual coefficients and `(R-1)!` for M0.
7. Validate exact P_fv(0)=delta_v, degree, partition, integer measurement row l1 norm <=D, and all outside-assigned-group kernel implications. The latter is verified independently as rational row-space containment by Gaussian rank, not assumed from the construction. Guarded mode additionally verifies maximum label multiplicity hD<=2M, group size <=2n/r, and total restricted measurement-row count <=2tau*n.

## Actual uniform complexity and bit heights

Write F=#factors, K=r^Q, D=K^2. The scope list and any empty factors are supplied explicitly; complexity includes F and incidence M. This is a polynomial reference construction, not an optimized implementation.

The exact conditional label routine tries `(n+F_nonempty)*K` candidates. A candidate score uses `M^2+Qn^2` indicator terms, with O(Q) tuple-equality cost when comparing whole words. A common denominator for all potential values divides a product of `D`, `r`, `M(b+w)`, and `Qn`. Its bit length is O(log D+log M+log n+log Q+log(b+w)+log r). Numerators add at most polynomially many bounded terms and have the same polynomial bit bound. Fraction reduction therefore introduces no exponential-height arithmetic. The final potential <=2 and nonnegativity imply precisely the square-root bounds in Lemma 4.5, and the two guarded balance inequalities give h<=2M/D and group size<=2n/r.

The spectral routine enumerates D basis vectors, stores D coordinates for each, and updates D^2 matrix entries per vector: O(D^3 poly(Q)) rational operations and polynomial storage. At integer j, generalized binomial values `binom(j-A0,k)` are integers, including j<A0. Hence each f_I(j) is an integer of bit length O(Q log Q); each basis norm is a power of two at most 2^Q. Every partial spectral sum has denominator dividing 2^Q and polynomial numerator height. No uncontrolled lcm of unrelated rational denominators occurs. Final M0 also satisfies the stronger factorial denominator assertion by cancellation.

Each phi denominator divides Q!, its coefficient sum is at most product(1+1/s)<=2^Q. Multiplying spectral coefficients and adding polynomials has a common intermediate denominator dividing `2^Q Q!` and bit height O(Q log Q+log D). Projection adds at most D terms and never increases coefficient l1 mass. The final theoretical common denominator is checked explicitly. Measurement entries are integers bounded in absolute value by D, not necessarily just 0,+/-1 after duplicate-variable projection.

Embedding, dense storage of actual rows, group restrictions and exact validation all take polynomial time/space in `(n,M,F,D,Q,r,b,w)`. Rational Gaussian elimination in validation retains polynomial bit heights by the usual determinant/minor bounds for rational matrices with these entry heights. This extra validation is intentionally retained; it does not change the polynomial-construction guarantee. There is no oracle kernel test or field-extension step.

Under guarded scheduled parameters D is polynomial in n, and this fixed polynomial overhead is consistent with the paper's overall subexponential bound. Tiny diagnostic cases below deliberately do NOT satisfy the asymptotic balance/tail assumptions. Their runtime is not evidence that the enormous threshold is practical.

## Tests and scope

Run `python3 tests/test_shared_layout.py --output /tmp/layout-checks.json` (default output is `../layout-checks.json`). All 11 tests pass:

- deterministic replay and monotone exact potential;
- independent exhaustive conditional averages for every fixing prefix of a tiny label instance;
- orthogonal eigenbasis and exchange eigenvalues;
- independent swap-polynomial M0 identity when f=1-2W;
- exact signs and coefficients of paper Remark 4.4;
- rational kernel/restoration validation plus independent direct Boolean-fibre agreement;
- distinct occupied copies for repeated original variables and empty factors;
- Q=3,R=2 and R=1 algebra controls;
- supplied-label checks and malformed scope rejection;
- binomial tail against exact eigenbasis multiplicity enumeration, and strict guard rejection;
- root schedule finite fallback.

No native semiprime coverage experiment, successful factor search, or asymptotic contraction timing was used. No new proof flaw was found in Section 4's construction. These tests and the author audit are not a Lean kernel verification of the generic counter or the factoring corollary.
