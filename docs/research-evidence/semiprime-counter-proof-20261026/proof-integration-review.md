# Independent proof / executed-core integration review

Verdict: **PASS for the stated algebraic component interfaces; not yet an end-to-end Lean counter/factorer or a machine-time theorem.** No substantive equation/sign/off-by-one error found in the six reviewed modules. Read exact current declaration bodies and the frozen Python `shared_counter.py`, `shared_parameters.py`, `factor_solver.py`; no finite controls used as proof.

## 1. Boolean diagonal + concrete filtration: exact match

`SemiprimeBooleanDiagonal.lean:157–200` proves the actual identity, not an assumed Möbius oracle: sign `(-1)^(|E|-|U|)`, `U subset E`, original Boolean assignments `x` forced **one** on E, and menu `|E|<=J-1`. The subtraction exponent is safe because U is a subset. Its support argument uses total degree, so powers of individual variables do not invalidate the Boolean support cutoff.

`SemiprimeCounterFiltration.lean:90–155` supplies the needed filtration from the actual recursive nonlinear multilinear evaluator. To instantiate at Python node t, use `base_x(f,v)=sum_i a_fv,i(t)*x_i`, and row d equal the coefficient of z^(d+1) of `a_fv,i(t+z)-a_fv,i(t)`. Set D=R. The base depends on x but is a scalar in the independent correction indeterminates; this is explicitly allowed by `base : Finset V -> ... -> Q`. Each positive-z correction has independent-variable degree one. Thus the j-th coefficient has total degree <=j even after products of local nonlinear extensions. Python computes exactly these base/correction data (`shared_counter.py:289–326`). A truncation of length J retains coefficients 0,...,J-1; no factorial derivative convention is involved.

**Open execution refinement:** no theorem yet identifies Python's jet operations/assignment streaming with the Lean polynomial evaluator or constructs this concrete instantiation from the layout object. Also still needed is the global polynomial `H(T)` degree bound <=dR and restoration `H(0)=literal tensor count`; the current filtration theorem is a local-Taylor diagonal frontend, not by itself that global theorem.

## 2. Shared summary: representatives and forced bits are correct

`SemiprimeSharedSummary.lean:25–102` proves arbitrary finite-group fibre factorization and the full sum over summaries. Representatives must reproduce their measurement fibre but **need not satisfy forced bits**. This matches Python `separated_fibre_sum`: first fibre scan ignores E, whereas actual summation applies E; after a group subtotal the mutable coordinates are reset to that group's representative. Empty fibres contribute zero; empty groups are legal. Python scans all measurement coordinates over `[-sum_abs_row,+sum_abs_row]`; every attainable Boolean measurement lies there, and validation checks each sum_abs_row<=D. Its potentially unattainable tuples are safely skipped.

The invariance hypothesis is pointwise, not a supplied contraction value. Python validates row-span containment of the foreign-group coefficient vectors. Given equal measurements this implies equal foreign linear forms, and the fixed-U correction is independent of x, so nonlinear local evaluation and group products preserve invariance. This is a sound mathematical instantiation.

**Open Lean application:** row-span validation => `hinvariant`, finite measurement ranges, construction/existence of representatives, and the actual layout construction satisfying those conditions are not connected in a compiled combined theorem here. `hrep`/`hinvariant` are explicit hypotheses, not executable functions or cost-free algorithm claims.

## 3. Hermite: the explicit coefficient formula now matches code

`SemiprimeHermiteRecovery.lean:80–82` matches code exactly: q=floor(dR/Q), J=q+1, hence dR<QJ, not merely <=. Nodes `1,...,Q` are distinct rationals (`samplePoints`). The actual cardinal factor is `L_t(T)=prod_(s!=t)((T-s)/(t-s))^J`. Python's local series product has coefficients `binom(J,k)/(t-s)^k`, precisely the truncated Taylor expansion of L_t(t+z); its scalar `at_zero=prod(-s/(t-s))^J` is L_t(0). Its quotient and evaluation sum at `(-t)^j` agree with `explicit_hermite_at_zero` (`:229–241`). No sign reversal or missing multiplicity/factorial occurs.

The new geometric inverse is constructed, with constant term one and congruence modulo X^J; reconstruction is not merely an assumed matching-packet uniqueness statement. All divided scalar differences are nonzero rationals.

**Open implementation/bit-cost refinement:** `inverseJet` is a mathematical finite geometric polynomial; Python `Jets.inverse` is a truncated coefficient recurrence. Their agreement follows from inverse uniqueness modulo X^J but is not yet an execution-refinement theorem in the module. Similarly, full polynomial cardinal/Taylor operations and truncated Python products require their quotient-ring compatibility bridge. This does not invalidate the formula, but means `explicit_hermite_at_zero` is not itself a Python runtime bound or complete code verification.

## 4. Count recovery: exactly the right restricted-query promise

`SemiprimeCountRecovery.lean:50–157` keeps a single original finite witness space and queries only prefix restrictions. It explicitly assumes equality of every conditional count to the actual accepted-count function; no counter is conjured. One empty-prefix test plus one zero-child test per requested bit matches `recover_from_counter` (`factor_solver.py:35–66`), which restricts the original P-bit edges. Reversing the list of accumulated prefix pairs does not change conjunction. A positive accepted witness remains after every selection, and returned bits belong to one witness. Duplicate requested indices do not invalidate the generic theorem; actual input-bit indices are distinct.

The Python runtime check `0<=zero<=total` is a diagnostic implied by true counts, not an additional counting oracle. A true zero-child count gives the complementary child the positive parent count. Divisor extraction still relies on compiler/network correctness, not only on this generic selector. `select_queries` counts query calls, not their bit cost.

## 5. Schedule and analytic rate: exact integers, honest remaining tail

`SemiprimeCounterRate.lean:154–178,222–257,311–439` matches `shared_parameters.py`: lambda=clog_2 n=ceil_log2(n), nu=clog_2 lambda, r=floor(sqrt(lambda))/nu^2, Q=floor(lambda/(128nu)), R=4ceil(sqrt(lambda)), D=r^(2Q), tau=1/(r*lambda), and the displayed centered integer interval. The proved nonnegative numerator makes Lean natural subtraction match Python signed subtraction in the accepted regime. Containment is A0+R<=Q+1, equivalent to the inclusive last node A0+R-1<=Q. The auxiliary budget is correctly D^128<2n, not necessarily <=n; the real bound accounts for its factor two.

The growing-arity load inequality is for actual occurrence two and incidence 2n. It is not a claim for arbitrary supplied occurrence/arity. All non-tail guards are established eventually; the actual binomial spectral-tail condition in Python is still a separate open Lean obligation, as the final theorem states. No theorem here eliminates or computes the finite fallback threshold.

The analytic rho uses **natural logarithms**, while the numerical schedule uses ceiling binary logarithms. Natural/binary changes are asymptotic constant changes, not definitional equalities. The `eventually_*subpower` and sixth-rate theorems bound an analytic expression only; they do not prove the executed counter's running time equals that expression, do not identify n with the original integer bit length L, and do not formalize the linear-wire compiler bound n<=C L. The arity overhead exp(B*x^(3/4)) is included in the envelope. A source-rate claim must keep those implementation and parameter-substitution bridges explicit.

## 6. Closed and open obligations

Closed in reviewed component statements: Boolean Möbius identity and support cutoff; filtration from nonlinear actual port expressions; fibre factorization using measurement-only representatives; explicit rational Hermite inverse/reconstruction/scalar evaluation; prefix-selection correctness conditional on genuine counts; numerical non-tail schedule guards; analytic envelope decay.

Open for a fully formal acquired factorer: layout construction and integer row-height/space accounting; exact forms/restoration/global H degree/jet semantics and their composition with fibre and Hermite theorems; binomial-tail guard; Boolean macro-network encoding/parameter and wire-size bridge; execution resource theorem (including streamed O(w*2^w) local work and polynomial rational heights); finite-guard fallback and final integer-size rate substitution. Boolean 0/1 entries give the intended rational-height contract; arbitrary per-entry small rational denominators alone do not, as the Python docs correctly warn. None of the reviewed theorem conclusions silently closes these obligations.
