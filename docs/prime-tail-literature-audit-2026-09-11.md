# Prime structure and the signed zeta tail

The next useful arithmetic input must distinguish ordinary primes from a positive oscillating comparison density. Positivity, retention of conjugate phases, and a fixed polynomial that isolates the selected frequency do not suffice: a locally verified Lean comparison theorem exhibits the same negative unit limit for every such polynomial. The literature offers several ways to use additional arithmetic information, but none of the estimates reviewed here supplies the independent bound required by the current RH argument.

The first feasibility audit of **joint factorization and additive correlations** has now ruled out a blanket upgrade from complete signed moments to source-scale norm estimates on every raw interval. A locally verified actual-prime example retains a growing narrow-window contribution even after exact pole annihilation and selected-mode normalization. The Type I/II framework of Ford and Maynard remains useful for specifying what additional estimates would be necessary, but its centered arithmetic error must be identified before those hypotheses can be tested. Additive congruences, shifted correlations, and simultaneous prime-factor information remain candidates; no reviewed estimate yet supplies the required signed bound.

## 1. The exact target

Let a hypothetical nontrivial zero be

\[
\rho=\beta+i\gamma,\qquad \tfrac12<\beta<1,
\qquad u=\tfrac32-\beta\in(\tfrac12,1).
\]

Let \(F\in\mathbb C[X]\) be the repository's fixed pole-jet polynomial, normalized by \(F(1/u)=1\). Write

\[
K_{F,N}(s,x)=x^{-s}\sum_k F_k\frac{(\log x)^{N+k}}{(N+k)!}.
\]

The surviving ordinary-prime response is

\[
P_N=u^{N+1}
\sum_{\substack{p\text{ prime}\\p>D_N,\ p\notin S_N}}
\log p\,K_{F,N}(\tfrac32+i\gamma,p).
\]

Here \(S_N\) is the actual quadratic small-prime sieve and the positive divisor cutoff satisfies

\[
D_N\leq\lfloor u^{-N/4}\rfloor^2.
\]

The series is genuinely convergent. In the current locally verified chain, the complete logarithmic divisor matrix and small-prime insertion have independent decay. Consequently the large-prime composite source \(L_N\) satisfies \(L_N+P_N\to0\). Combining this identity with the previously established source limit gives

\[
P_N\longrightarrow-m_\rho,\qquad m_\rho\geq1.
\]

The relevant declarations are `tendsto_normalized_moebius_logResponse`, `tendsto_large_add_primeCorrection`, and `tendsto_normalizedPrimeLogResponse` in [the family-decay module](../RiemannGaussian/ZetaSquarefreeEulerFamilyDecay.lean) and [the prime-tail module](../RiemannGaussian/ZetaSquarefreeEulerPrimeTailSource.lean). This is a consequence of assuming a zero; it is not an independent estimate against that zero.

A fixed margin

\[
\exists\varepsilon>0\quad\forall N_0\quad\exists N\geq N_0:
\operatorname{Re}P_N\geq-1+\varepsilon
\]

would contradict the limit. Full norm decay is stronger than necessary. A pointwise inequality \(\operatorname{Re}P_N>-1\) without a fixed margin is insufficient. The target therefore remains a signed inequality, with all complex polynomial coefficients retained.

## 2. The Lean comparison test

For \(0<a<1/2\) and \(|y|>1\), define on positive logarithmic time

\[
f_{a,y}(t)=e^t\left|1-e^{(-a+iy)t}\right|^2.
\]

Lean proves both \(0\leq f_{a,y}(t)\leq4e^t\) and the exact four-channel expansion

\[
f_{a,y}(t)=e^t-e^{(1-a+iy)t}-e^{(1-a-iy)t}+e^{(1-2a)t}.
\]

Its Laplace transform, for \(\operatorname{Re}s>1\), is

\[
T_{a,y}(s)=\frac1{s-1}
-\frac1{s-(1-a+iy)}
-\frac1{s-(1-a-iy)}
+\frac1{s-(1-2a)}.
\]

All factorial moments are absolutely integrable and equal the signed Taylor moments of this transform. Set \(v=1/2+a\), \(s_0=3/2+iy\). For **every fixed complex polynomial** \(F\) with \(F(1/v)=1\), the checked terminal theorem gives

\[
v^{N+1}\sum_k F_k
\int_0^\infty f_{a,y}(t)
\frac{t^{N+k}}{(N+k)!}e^{-s_0t}\,dt
\longrightarrow-1.
\]

The selected denominator is exactly \(v\); the other three denominators have modulus greater than \(v\). Thus the selected negative channel survives while all other normalized geometric channels vanish. The theorem covers the repository's actual pole-jet polynomial after substituting \(a=1-\beta\), \(y=\gamma\).

Evidence: [PositiveDensityPrimeTailAudit.lean](../../research-audits/prime-tail-positive-density-evidence-2026-09-11/PositiveDensityPrimeTailAudit.lean), especially `moment_eq_integral`, `normalized_filtered_density_tendsto_neg_one`, and `comparison_limit_for_repository_filter`. [Validation output](../../research-audits/prime-tail-positive-density-evidence-2026-09-11/lean-validation.log) records the checks.

This is a failure test for an inference from positivity and conjugate pairing alone. It is not an example of ordinary primes, does not satisfy the full zeta functional equation, and is not a counterexample to RH. Its terminal integral is over the complete positive axis; the script does not assert a theorem for the original moving prime cutoff. It also does not classify arbitrary polynomials whose degree and coefficients vary with \(N\).

These limitations matter. The result rejects the proposed general positivity inference, while leaving available stronger hypotheses that use the actual integer lattice, prime positions, or the full functional equation. It must not be listed as a new zero exclusion or as a proof that every approach retaining phases fails.

## 3. The scale an imported estimate must reach

The damping of an individual arithmetic term is \(e^{-3t/2}\), but the number of integers near \(e^t\) contributes \(e^t\,dt\). The full-density absolute envelope therefore has damping \(e^{-t/2}\). Its moment saddle is \(t\approx2N\), and its normalized exponential size is \((2u)^N\), which grows for every \(\beta<1\).

This rules out a common rate mismatch. An estimate for a partial sum of size \(x/\log^A x\), with fixed \(A\), does not give source-scale decay after the factorial transform. Neither does a generic error \(x\exp(-o(\log x))\). These can be excellent prime-distribution estimates while remaining too large for this particular normalization.

An existing Lean rate audit makes the fixed-logarithm distinction exact. For \(d,u>0\) and an integer \(A\geq0\), it evaluates

\[
J_{A,d}(N)=u^{N+A+1}
\int_0^\infty\frac{t^N}{(N+A)!}e^{-dt}\,dt
=u^A\left(\frac ud\right)^{N+1}\frac{N!}{(N+A)!}.
\]

If \(d<u\), this allowance diverges despite any fixed factorial-ratio saving. If \(d=u\), it tends to zero for \(A>0\), while \(A=0\) gives exactly one. See [PrimeBilinearRateAudit.lean](../../research-audits/prime-bilinear-rate-evidence-2026-09-11/PrimeBilinearRateAudit.lean).

For a proposed partial-sum bound with exponent \(\vartheta\), the associated exponential damping is \(d=3/2-\vartheta\). The relevant threshold is therefore \(\vartheta<\beta\), or a saving at \(\vartheta=\beta\). This is a test of absolute majorants; it does not preclude a better signed argument. A strict constant deficit directly at the known source scale remains sufficient.

The practical requirement is to write down the final normalized allowance, including the costs of coefficient norms, moduli, interval partitions, exceptional sets, and every Cauchy–Schwarz step. A phrase such as “power saving” is incomplete until its variable and reference scale are specified.

## 4. Information already present in the repository

| Structure | Existing implementation | What is still missing |
|---|---|---|
| Exact squarefree Euler factors and prescribed prime divisibility | `ZetaSquarefreeEulerResponse`, `Marks`, `Quadratic` | A bound for the prime correction after the complete matrix decays |
| Complex lcm and Selberg quadratic forms | `ZetaSquarefreeEulerQuadratic`, `FamilyDecay` | Positivity cannot be assigned to a complex transpose form without proof |
| Prime insertion and derivative cancellation | `ZetaSquarefreeEulerPrimeInsertion` | The remaining logarithmic-derivative source |
| Balanced factors, semiprimes, rough support | `ZetaRoughSquarefreeFactorGeometry`, `FactorSource` | A signed estimate for the surviving sectors |
| Additive near-pair correlations | `ZetaArithmeticLocalEnergy`, `ZetaRoughSquarefreeLocalCorrelation` | The far-pair form still carries the source square |
| Abel transformation into the Chebyshev error | `ZetaPrimeBandAbel`, `ZetaPrimeBandChebyshev` | Cancellation inside the exact complex error integral |
| Signed quotient prefixes and Möbius cancellation | `ChebyshevMoebiusQuotientCoupling` | A rate or signed comparison at the current source scale |
| Heat, Hilbert, Weil, phase and finite/continuous interfaces | Suzuki, Gaussian and Montgomery–Vaughan modules | An independent arithmetic inequality at the remaining interface |

The [local-correlation note](zeta-rough-squarefree-local-correlation.md) already warns that pairs far apart additively can still be close in logarithmic phase. The [Chebyshev note](zeta-prime-band-chebyshev.md) retains the imaginary channel of the differentiated kernel. Repeating these transformations or eliminating another negligible endpoint does not provide a new estimate of the remaining tail.

Likewise, a Heath–Brown coefficient identity was already tested in the [hyperbola assessment](eta-hyperbola-endgame-assessment.md). Reintroducing it is useful only if a new estimate exploits the resulting coefficients. A new decomposition alone is not additional cancellation.

## 5. General sieves and simultaneous factor information

Ford and Maynard study prime sums for nonnegative sequences satisfying Type I and Type II estimates, using all of the supplied information together. Their Theorem 2.1 constructs sequences with no prime mass despite some nontrivial Type II information; their asymptotic criterion depends on the ranges of both types of estimates. This gives a precise framework for asking what an entire class of arithmetic estimates can imply, rather than selecting isolated sieve weights.[^1]

The hypothesis audit is essential. Their Type I estimate controls interval-restricted sums along multiples, aggregated over divisors. Their Type II estimate allows arbitrary bounded, or specified divisor-bounded, coefficients in both factor variables. The current marked Euler moment bounds do not automatically supply either statement: they concern specific complex filtered sums, without all of these interval and coefficient quantifiers.

**Local interval test, now verified.** The [actual-prime Lean audit](../../research-audits/prime-phase-window-evidence-2026-09-11/README.md) constructs, for every \(u>1/2\) and \(|\gamma|>1\), the fixed polynomial

\[
P(z)=\frac{1-(1/2+i\gamma)z}{1-(1/2+i\gamma)/u}.
\]

It has exactly zero pole-mode response and unit selected response. Nevertheless, on the narrow interval \(e^{2N}<a\le e^{2N+h}\), where \(h=1/(|\gamma|+1)\), the normalized norm of its actual prime sum tends to infinity. The theorem `exists_normalized_filter_with_large_prime_windows` proves this using the existing prime number theorem, Stirling's formula, and both trigonometric channels. The proof's lower scale is a positive constant times \((2u)^N/N\). It does not take an asymptotic density heuristic as a hypothesis.

The tested window is beyond both moving arithmetic cutoffs. `filteredWindowMoment_eq_prime_tail_window` identifies it with the restriction of the original tail coefficient, for every fixed polynomial. The explicit linear witness is not claimed to be the full zero-isolating polynomial, nor does this prove divergence for every filter. It suffices to refute a uniform source-scale norm bound on all raw intervals under the two mode constraints alone.

This does not refute the literature's centered Type I/II hypotheses. Pole annihilation in a complete moment is not the same operation as subtracting the smooth prime density separately on each interval. The remaining test must use the exact centered error and account for the reconstruction of the complete signed tail. The repository's Abel–Chebyshev identity already exposes that error; this audit does not supply its missing estimate.

**Centered counting continuation.** The subsequent [complete squarefree counting slice](zeta-squarefree-centered-counting.md) proves an actual centered interval bound, uniform over all bounded complex divisor-weight families: its error is at most `C_sigma D exp(4 sqrt(R)) (B^sigma + A^sigma)` for `1/2 < sigma <= 1`. The exact density and all shared-prime intersections are retained, and the divisor cost is linear in `D`. This discharges a counting interface for the complete squarefree matrix. It does not yet prove the factor-variable Type II hypotheses or the independent signed ordinary-prime-tail estimate.

**Application assessment.** Use the framework first as a test of sufficiency. Record the actual factor ranges and the precise class of allowed coefficients in the surviving matrix. Retain the vector of prime-factor sizes and the subset products available for splitting; a scalar divisor count or a norm of the whole matrix can obscure this information. No Type I/II parameter triple is certified here for the current signed sequence.

Friedlander–Iwaniec's asymptotic sieve makes the missing parity information particularly explicit. Its extra bilinear assumption contains the signed factor \(\mu(mn)\), together with a truncated Möbius divisor sum. The theorem obtains prime asymptotics only after this estimate and the other sieve hypotheses have been verified. Section 10 allows a roughness restriction, which is close in form to the present carrier.[^2]

**Application assessment.** This is a useful specification of the missing estimate, not a theorem that discharges it. Replacing the signed sequence by its absolute value to fit a nonnegative sieve hypothesis would lose the quantity needed for the contradiction. Applying a sieve separately to positive and negative parts can also reintroduce errors at full density.

## 6. Additive structure and higher correlations

Maynard's progression estimates use factored moduli, amplification, and exponential-sum input from automorphic spectral theory or algebraic geometry. They access additive residue information that an Euler product alone does not encode. The precise Theorem 1.1 estimates deviations of \(\pi(x;q,a)\) from \(\pi(x)/\varphi(q)\), averaged over specified moduli.[^3]

**Application assessment.** This distinction exposes a concrete obstruction: the comparison uses the unknown total prime count. Equidistribution among residue classes can coexist with an error in the common mean. If the prime-tail response is expanded in additive characters, its zero-frequency component must remain explicit; bounding only the other characters does not bound the original scalar sum.

The useful candidate is therefore not simply “add a modulus.” It is a mixed identity in which congruence information is coupled to the original factorization, and its principal contribution cancels by a proved identity. All reconstruction coefficients and the cost of averaging over moduli must remain in the final source-scale estimate.

Green and Sawhney provide a substantial example of additional structure producing Type II control. Their work on primes represented by \(p^2+nq^2\) combines multiplication in a quadratic number field with additive Gowers-uniformity and concatenation estimates. The resulting real-coordinate expressions contain genuinely coupled linear forms; the argument is not a generic bound for every bilinear prime sum.[^4]

**Application assessment.** The transferable idea is to derive and then control several compatible additive correlations. It is not the occurrence of the word “Gaussian”: Gaussian heat and Gaussian integer factorization are different structures. A viable adaptation must exhibit the actual coupled forms arising from this repository's carrier. The paper's logarithmic savings, without another reduction of scale, do not by themselves meet the present normalization.

Two elementary algebraic tests should precede such an adaptation. First,

\[
e^{-i\gamma\log(mn)}
=e^{-i\gamma\log m}e^{-i\gamma\log n}
\]

for positive \(m,n\). Thus this phase alone is a row and column modulation of a bilinear matrix. A bound uniform over arbitrary complex coefficients cannot gain from it alone: the coefficients can absorb the two unit phases. This observation does not remove arithmetic restrictions on the actual coefficients, and it does not say that the full factorial kernel is a product.

Second, for a finite residue vector \(v_r\), centered dispersion is unchanged by adding the same constant to every \(v_r\), whereas \(\sum_r v_r\) changes. These are analytical tests of a proposed transport, not new library theorems. They identify the exact place where a proof must use more than phase modulation or nonprincipal equidistribution.

## 7. Multiplicative colours and pretentious obstructions

Matomäki, Merikoski and Teräväinen develop sieves for multiplicatively structured sets without using \(L\)-functions in their applications. Their finite-group theorem explicitly requires mass in appropriate index-two cosets, in addition to distribution and upper-bound hypotheses. Their Remark 1.5 explains that this assumption prevents a parity counterexample.[^5]

**Application assessment.** Index-two coset mass is a concrete type of colour information beyond a scalar density bound. It merits testing alongside the existing phase carrier, with a genuine multiplicative map into a finite group. Rounding the continuous phase \(\gamma\log n\) to a finite colour would generally destroy multiplicativity; that cannot be used as an exact bridge. Moreover a positive proportion of primes in a colour class is not yet the required signed factorial-moment estimate.

Granville, Harper and Soundararajan's form of Halász's theorem organizes multiplicative cancellation around pretentious modes. Their Corollary 1.2 includes an error of order \(x(\log\log x)^\kappa/\log x\); the paper explicitly discusses the resulting limitation of this general bound.[^6]

**Application assessment.** This offers an inverse question: if a signed Möbius expression remains large, what multiplicative character or logarithmic phase must it resemble? But the bare function \(n^{-i\gamma}\) is already such a structured mode. A useful theorem must isolate a residual arithmetic coefficient that cannot imitate it. An \(x/\log x\)-scale estimate for that coefficient would still need the rate test in Section 3.

Matomäki–Radziwiłł prove cancellation of Möbius in almost all short intervals with lengths tending to infinity.[^7] Matomäki–Radziwiłł–Tao additionally connect a large average of local Fourier sums to approximation by twisted characters; their Theorem 1.4 specifies the averaging and frequency ranges.[^8]

**Application assessment.** These theorems are useful if the carrier can be represented as a controlled average of the relevant local sums. One must estimate the weighted contribution of the exceptional intervals. Neither “almost all” nor an unquantified small relative error can be substituted for a bound at a fixed selected ordinate. Inverse theorems at a fixed positive relative threshold also require a new quantitative audit if the detected relative signal is exponentially small in \(N\).

Green–Tao's Möbius–nilsequence theorem gives cancellation against a large structured class, with logarithmic savings and explicit dependence on nilsequence complexity.[^9] It is a valuable alternative after a structured residual has been identified. The present moving divisor masks are not automatically nilsequences of uniformly controlled complexity, and the full-density logarithmic barrier remains.

## 8. Harmonic analysis, fractals and spectral geometry

Guth and Maynard's large-value theorem controls the number of separated ordinates at which a Dirichlet polynomial is large. Their work yields the zero-density estimate \(N(\sigma,T)\ll T^{30(1-\sigma)/13+o(1)}\) and stronger short-interval results.[^10]

**Application assessment.** This is a credible route to a separate, quantitative zero-density formalization. It is not a ready-made contradiction for one hypothetical zero: a bound allowing a small exceptional set can allow that zero. To use it here, one must first prove that the selected source forces enough separated large values of the same Dirichlet polynomial in the theorem's length-height range. Varying the moment order changes the polynomial and does not supply that implication automatically.

Dyatlov–Zahl's fractal uncertainty approach obtains spectral gaps from multiscale regularity and additive-energy information.[^11] It is relevant as a mechanism for preventing simultaneous concentration, not because prime sets are sparse in a loose sense.

**Application assessment.** No required multiscale regularity theorem has been established for the relevant prime support in this chain. A sieve density of logarithmic size is not a fixed power-law dimension gap. The logarithmic coordinate also changes spacing substantially. A fractal approach should proceed only after identifying the exact two supports, the operator between them, and uniform constants at all needed scales.

Connes–Consani connect Weil positivity with compressed scaling operators and prolate spheroidal functions in the archimedean case.[^12] Connes–Consani–Moscovici extend aspects of this operator framework to finitely many places, retaining local arithmetic data.[^13]

**Application assessment.** This is the most relevant longer-range alternative to a direct tail estimate because it connects to the existing heat, Fourier, matrix and Weil interfaces. The important additional structure is the relation between an integer-lattice summation operator and Fourier duality, together with local prime data. Archimedean positivity alone does not imply positivity of the complete prime contribution.

Connes's 2026 work states a real-zero theorem for Fourier transforms of suitable even ground states of convolution-form operators. Its Section 6.6 explicitly leaves two steps: establish the requisite ground-state properties of the Weil operator and control its approximation by the proposed prolate construction.[^14]

**Application assessment.** The finite real-zero result cannot be substituted for those steps. A bounded prototype would compare the actual compressed Weil form with the proposed operator and retain the entire correction, including its sign. It should proceed to a new framework only if a one-prime or finite-place estimate reveals an independently controllable correction. Finite approximants on the line, numerical agreement, and an unproved convergence assertion do not establish RH.

## 9. Generalized primes as a diagnostic

Broucke constructs Beurling systems with prescribed zero contours and nearly matching prime-counting oscillations, under the explicit hypotheses of Theorem 1.6. These systems retain multiplicative Euler-product structure and substantial regularity of generalized integer counts while lacking the full additive structure of ordinary integers.[^15]

**Application assessment.** This supports using generalized-prime examples to test which hypotheses a proposed argument actually needs. It does not prove that any one missing property is sufficient for RH. The local squared-density example is a smaller, directly verified diagnostic; it is not claimed to instantiate every hypothesis of Broucke's constructions.

Gonek's finite-Euler-product approximation results provide a related warning: the strong approximation in the right half of the strip is conditional on RH in the forward direction, and strong converse conclusions constrain zeros.[^16] The current high-order marked-moment decay is not a substitute for a locally uniform nonvanishing approximation at the selected zero.

## 10. Recommended next experiments

These are research priorities, not claims that the necessary estimates are already available.

| Priority | Bounded experiment | Evidence required to continue | Reason to stop or redirect |
|---|---|---|---|
| 1 | After the verified raw-interval obstruction, identify a centered Type I/II interface with all interval and coefficient quantifiers | An exact reconstruction of the signed carrier with an allowance at source scale, and independently available estimates for the centered sequence | Complete moment decay is used as though it bounded every raw interval, or a new full-density cancellation premise has no source of improvement |
| 2 | Retain both prime-factor sizes and additive residue/shift data in one surviving block | A mixed correlation in which the principal contribution cancels by a checked identity | Only row/column phase modulation or nonprincipal characters have changed |
| 3 | Test multiplicative finite-group colours and index-two coset information | An exact multiplicative colouring and an independent coset inequality that enters the signed target | A rounded phase breaks the identity, or only a full-density positive proportion is obtained |
| 4 | Compare the actual finite-place Weil form with a prolate or Fourier-compression model | A proved signed correction estimate, initially in a bounded finite-place case | The unknown correction is simply the original prime tail under a different name |
| Separate objective | Adapt modern large-value estimates to actual zeta zero counts | Complete length-height and zero-detection bridges | The intended conclusion is an individual zero exclusion but the theorem only controls frequency |

The first experiment should begin upstream of the final ordinary-prime collapse, where the complete matrix and its signed prime-deletion identity remain available. A pure prime indicator has no nontrivial factorization into smaller integers. The earlier divisor formulation may make some arithmetic correlations accessible, but any use of them must reconstruct the exact prime correction with controlled cost.

There are three acceptable outcomes for an overnight slice: an independent signed improvement for an actual surviving part; a complete reduction to a specific literature estimate with its hypotheses discharged; or a verified obstruction that eliminates an entire proposed mechanism. A new identity with the same unbounded remainder is useful only as preparation and should be labelled accordingly.

The decisive success test remains the cofinal fixed-margin inequality in Section 1. No reviewed theorem currently closes it. The comparison test and this assessment do not improve the existing zero-free region, and RH remains unproved.

## Sources

The cited versions were inspected on 11 September 2026. Preprint dates identify the cited works, not a claim that they are the latest or strongest results in every subfield.

[^1]: Kevin Ford and James Maynard, [*On the theory of prime-producing sieves*](https://arxiv.org/html/2407.14368v1), arXiv:2407.14368, first posted 19 July 2024. Introduction (I), (II); Theorems 2.1–2.2; Section 4.4. Used for the all-estimates framework and hypothesis audit.

[^2]: John Friedlander and Henryk Iwaniec, [*Asymptotic sieve for primes*](https://arxiv.org/pdf/math/9811186), 1998. Hypothesis (B), Theorem 1, and Section 10. Used for parity-sensitive bilinear information and rough-variable restrictions.

[^3]: James Maynard, [*Primes in arithmetic progressions to large moduli I: Fixed residue classes*](https://arxiv.org/pdf/2006.06572), arXiv:2006.06572, 11 June 2020. Theorem 1.1 and introductory proof discussion. Used for additive progression information and its total-count comparison term.

[^4]: Ben Green and Mehtaab Sawhney, [*Primes of the form p² + nq²*](https://arxiv.org/html/2410.04189v1), arXiv:2410.04189, 5 October 2024. Introduction, Propositions 4.2–4.3, Sections 6–7. Used for coupled algebraic forms and Gowers concatenation.

[^5]: Kaisa Matomäki, Jori Merikoski and Joni Teräväinen, [*Primes in arithmetic progressions and short intervals without L-functions*](https://arxiv.org/html/2401.17570v1), arXiv:2401.17570, 31 January 2024. Theorem 1.4, assumption (A4), Remark 1.5. Used for finite-group colours and the explicit parity obstruction.

[^6]: Andrew Granville, Adam J. Harper and K. Soundararajan, [*A new proof of Halász's theorem, and its consequences*](https://wrap.warwick.ac.uk/id/eprint/103414/), *Compositio Mathematica* 155 (2019), 126–163. Accepted manuscript dated 18 June 2018; Theorem 1.1, Corollary 1.2, Section 1.2. Used for pretentious modes and the scale of the general mean-value bound.

[^7]: Kaisa Matomäki and Maksym Radziwiłł, [*Multiplicative functions in short intervals*](https://annals.math.princeton.edu/2016/183-3/p06), *Annals of Mathematics* 183 (2016), 1015–1056. Used for almost-all short-interval cancellation and its scope.

[^8]: Kaisa Matomäki, Maksym Radziwiłł and Terence Tao, [*Fourier uniformity of bounded multiplicative functions in short intervals on average*](https://arxiv.org/pdf/1812.01224), arXiv:1812.01224, 4 December 2018. Theorem 1.4 and Corollary 1.5. Used for the averaged inverse theorem and its twisted-character alternatives.

[^9]: Ben Green and Terence Tao, [*The Möbius function is strongly orthogonal to nilsequences*](https://arxiv.org/pdf/0807.1736), arXiv:0807.1736, 2008; published in *Annals of Mathematics* in 2012. Theorem 1.1. Used for logarithmic savings and complexity dependence.

[^10]: Larry Guth and James Maynard, [*New large value estimates for Dirichlet polynomials*](https://arxiv.org/html/2405.20552v1), arXiv:2405.20552, 31 May 2024. Theorems 1.1–1.2 and Corollaries 1.3–1.4. Used for exceptional-value frequency, zero-density and length-height restrictions.

[^11]: Semyon Dyatlov and Joshua Zahl, [*Spectral gaps, additive energy, and a fractal uncertainty principle*](https://arxiv.org/pdf/1504.06589), arXiv:1504.06589, 2015; published in *GAFA* in 2016. Introduction and Section 6. Used for multiscale regularity and additive-energy requirements.

[^12]: Alain Connes and Caterina Consani, [*Weil positivity and Trace formula, the archimedean place*](https://arxiv.org/pdf/2006.13771), arXiv:2006.13771, 24 June 2020. Used for compressed scaling, the archimedean scope, and prolate correction operators.

[^13]: Alain Connes, Caterina Consani and Henri Moscovici, [*Zeta zeros and prolate wave operators*](https://arxiv.org/abs/2310.18423), arXiv:2310.18423, 27 October 2023. Used as a lead for finite-place operator structure; no theorem from it is imported into Lean here.

[^14]: Alain Connes, [*The Riemann Hypothesis: Past, Present and a Letter Through Time*](https://arxiv.org/html/2602.04022v1), arXiv:2602.04022, 3 February 2026. Theorem 6.1 and Sections 6.4–6.6. Used for the ground-state real-zero result and the explicitly remaining approximation steps.

[^15]: Frederik Broucke, [*On the connection between zero-free regions and the error term in the prime number theorem*](https://arxiv.org/html/2507.13780v1), arXiv:2507.13780, 18 July 2025. Section 1.1 and Theorem 1.6. Used for generalized-prime countermodels and the distinction between multiplicative and additive structure.

[^16]: S. M. Gonek, [*Finite Euler products and the Riemann Hypothesis*](https://arxiv.org/abs/0704.3448), arXiv:0704.3448, 26 April 2007. Used for the conditional nature of strong right-strip Euler-product approximation and its converse implications.
