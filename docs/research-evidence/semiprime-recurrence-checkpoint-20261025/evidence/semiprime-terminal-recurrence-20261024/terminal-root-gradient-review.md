# Independent leading-root-gradient and uniform-padding review

2026-10-24. **PASS. No required fixes.** Read-only audit; no source/repository edits, numerical examples or backend work.

Reviewed source: `/tmp/semiprime-terminal-recurrence-20261024/terminal-root-gradient.md`

Exact SHA256: `8915ff758ba60c6cf956fb49b65287a45d82623f2c5c92f003a4021b137fa4cf`

The original terminal-literature.md remains unchanged at SHA256 49c90f496dcfaf1f4cc2e69e746950c9e3b597257ca94d21056c76ad7547ed06 and has a separate independent PASS. This audit checks the added simplification and stronger uniform-circuit route directly.

## Leading root derivative, sign and multiplicity

The derivative is with respect to the roots of the UNPERTURBED F, holding z fixed. It is correctly not implemented by replacing every root Y_j with Y_j+z. At a local hit node, dF/dY_j equals -F'(Y_j) if that node is Y_j, and zero at every different original root. In the product rule for E(F+z), omitting a hit factor leaves valuation h-1 with coefficient a_h, while omitting a nonhit leaves valuation h.

Hence the exact coefficient is

    [z^(h-1)] partial_(Y_j)E(F+z)
       =-a_h*F'(Y_j)*1_(j is a local hit).

The minus sign and factor a_h are correct. Target separation makes each F'(Y_j) a global unit, and a_h was certified unit when local counts coincide. Thus a different hit-row set produces an individual proper gcd, while absent such a gcd the sets coincide and every common-hit coefficient is unit. A common row exists because h>=1. No h inverse, Newton reconstruction, fixed-leading-coefficient derivative or hit-value inverse is needed, including at h=J.

The convolution/reversal transformation applied to B_k gives precisely these leading root derivatives. The original coefficient-to-root Jacobian is independent of z; coefficient extraction therefore commutes with that linear transformation. Its ordinary monic MPE costs soft J and does not divide by F' algorithmically. The adaptive primal/reverse jet cost remains soft(C(h+1)+J+sqrt L); the simplification removes postprocessing, not the h multiplier.

Only an ORIGINAL selected row is sent to its one-row locator, which handles different local seed indices. Auxiliary gradient coefficients are not fed to a leaf decoder. The original generic independent-coefficient/unit-denominator circuit contract is explicitly retained; no AD of a Jacobi oracle or native-only formula is asserted.

## Stronger uniform fixed-degree circuit contract

A pointwise differentiable trace does not automatically cover padded queries. The addendum correctly requires a uniformly valid degree-J circuit on the entire actual padded query class, including all denominator certificates and branch validity. This stronger hypothesis is not claimed for a newly acquired circuit.

With an unrestricted monic-input contract, multiplying F_S by X^(J-|S|) preserves the original mask on unit seeds. The warning is necessary and correct: zero padding violates unit constant/root-separation hypotheses and cannot be used if the circuit requires them.

## Safe dummy acquisition and every saturation branch

The dummy list d_s=q^(u-s), 1<=s<=3J is acquired by signed powers/recurrence in soft J. Its pairwise gaps and all dummy-seed gaps are nonzero and bounded by L+3J<16H. Thus the original short q-order certificate proves their unit separation, including negative exponent starts.

MPE of the ACTUAL original degree-J F at those 3J nodes and INDIVIDUAL scalar gcds cost soft J. A proper gcd factors. If none occurs, each F(d_s) is unit or globally zero. There are at most J globally zero dummy nodes by the degree bound in either field. This conclusion does not require a zero dummy to be one globally equal original root: the report explicitly allows different root labels across P,Q. Therefore at least 2J good dummies remain and J can be selected publicly.

For a good dummy, the acquired unit product F(d_s)=product_j(d_s-Y_j) certifies every factor a unit. Combined with dummy-dummy separation and nonzero dummy powers, this proves unit constants and pairwise unit-separated roots for every padded F_S. Dummy factors at every seed are units too, so the endpoint mask is unchanged. Their long total product need not be numerically acquired merely to prove and use this mask equivalence; no division by an unacquired factor occurs.

The addendum correctly does not infer other possible circuit denominators from these root conditions. Those remain part of the explicitly stronger uniform contract.

## Bisection cost and actual recovery

Each padded polynomial is acquired by actual monic product/multiplication trees in soft J. There are O(log J) row bisection calls, each with the uniform circuit cost C. A known-nonunit parent always has a nonunit original child; padding preserves its mask. Proper gcds may terminate, otherwise saturated children continue. A Boolean-only oracle can choose a zero child and defer actual proper/global recovery to the existing one-row locator.

The total bound soft(C+J+sqrt L) follows, without the h multiplier. It is the established restriction/bisection recovery method under a stronger query contract, not an endpoint-circuit construction or an unconditional improvement to current acquisition. All original row/interval labels and the bounded original-beta leaf decoder remain attached. No dummy or padded auxiliary zero is assigned an original-row identity without the supplied unit guards.

## Verdict

Both positive conditional algorithms are correct: direct all-h leading-root-gradient row selection with actual-h jet cost, and old-cost restriction recovery from genuinely uniform fixed-degree circuits using acquired safe padding. Their different circuit hypotheses are clearly stated. Neither supplies a new fast endpoint or whole-input factorization exponent. PASS for the exact reviewed bytes.
