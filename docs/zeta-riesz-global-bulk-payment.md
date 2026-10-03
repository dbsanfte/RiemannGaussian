# The completed all-count bulk now has a signed geometric payment

`ZetaRieszGlobalBulkPayment.completedCore_real_bound` proves an independent
bound on the real part of the complete squarefree response over the physical
window `1.95N < log n <= 2.03N`. It keeps the actual moving integer-floor
length, full factorial kernel and fixed character. It joins every prime
count, including the restored ordinary primes and semiprimes. Its assumptions
are `1/2 <= u <= 10001/20000`, `54 <= |y|`, and `64 <= N`; there is no zero,
exposure, RH, prime-density or Type-II hypothesis.

Write `Ccount = ZetaRieszLongCutoffError.countingConstant`. The proved bound is

```text
|Re(completedCore u y N)|
 <= 7 ownerSamplingBudget(u,y,N)
    + 2u Ccount (4+|y|) N(N+1) exp(-N/200).
```

Both terms tend to zero for fixed height. This pays a global completed
arithmetic bulk, rather than improving a positive `(2u)^N` allowance by an
inverse polynomial. It does not assert complex-norm decay.

The proof applies the existing squarefree sharp-prefix counting estimate
without composite/prime deletion. The actual cutoff obeys `D^4 <= X^3` on
every dyadic row of the full window. All signed divisor profiles are joined
into the single scalar `densityRiesz L`, whose absolute value is at most 7.
The counting error retains the `exp(-N/128)` saving, giving `exp(-N/200)`
after source normalization. The signed scalar multiplies one complete
integer-lattice phase sum. `full_lattice_phase_bound` pays that sum by an
exact factorial phase primitive with only the two exterior endpoints and
the original integer-sampling error. No prime approximation is used.

## The payment is spent in the current native ledger

`ZetaRieszGlobalCentralPayment` proves the restored prime coefficient has
the same divisor-log majorant. It reuses the existing uniform edge theorem
to contract the completed window to `1.971N < log n <= 2.029N`, paying its
own two radial strips. This is a separate use of the bound from the already
paid strips of the original balanced native population.

Let `Gcentral` denote this completed central sum, `Mcentral` the exact
allocation-free `centralRest`, and `H` the SAME original signed native head.
The head keeps its original wider window. The checked finite identity is

```text
Gcentral = Mcentral + P1 + P2 + Rejected,
Mcentral - H = Gcentral - B,
B = P1 + P2 + Rejected + H.
```

`P1` contains all ordinary primes in the central window; `P2` contains all
squarefree two-prime labels. `Rejected` contains every squarefree count >=3
label in that window that fails membership of the EXACT native central
population. In particular it retains count, physical, deletion, owner and
nondominant failures, with their original unallocated coefficient and phase.
There is no anonymous dropped boundary, completed cofactor, factorial-order
exception, or independently chosen phase. Every label is charged once.

`joinedBoundary` is `B`. Its components are not independently bounded.
The sign of `P2` is its original completed coefficient; the subtracted
semiprime boundary in the earlier matched-head theorem is `-P2` on matching
labels. Thus that earlier cancellation remains available with its actual
sign, but is not silently applied to unmatched pairs.

`eventually_native_boundary_bound` spends the completed-bulk bound and the
existing balanced allocation, radial and allocated high-owner payments:

```text
|Re(sourceScaledNativeCore) + Re(B)| <= nativeBoundaryBudget,
nativeBoundaryBudget -> 0.
```

The budget is the sum of the completed central bulk payment, the original
balanced radial payment, the balanced allocation difference, and the old
allocated high-owner payment. The last payment does NOT pay the raw
high-owner labels inside `Rejected`. All multiplicities and zero hypotheses
remain outside these independent arithmetic theorems.

The resulting one-sided inequality is

```text
Re(sourceScaledNativeCore) >= -Re(B) - nativeBoundaryBudget.
```

The remaining independent floor target is therefore an upper bound
`Re(B) <= 399/5000 + o(1)` on this ENTIRE joined signed boundary. None of
`P1`, `P2`, raw high owners or the other rejected labels is declared small.
The whole floor, ceiling `42/25`, restricted contradiction and RH remain
open. This is a genuine bulk payment and exact mask-transfer ledger; it is
not a zero exclusion or an automatic completion proof of the floor.

## Optional numerical regression

`scripts/probe_riesz_global_bulk_phase.py` evaluates the exact full factorial
primitive of the continuous integer-density phase main at orders
256, 640, 1536, 4096, 8192, 32768 and 65536, at heights 54, 65 and 100. It uses
the exact rational-floor moving length. It uses ideal real radial endpoints;
the Lean proof separately pays the actual integer rounding.

The diagnostic allowance `7*|normalized phase integral|/L` is about
`4.39e-4` at order 8192 and `7.01e-5` at order 65536, taking the maximum of
the three tested heights. These are continuous-main diagnostics, not
values of the literal carrier or an evaluated total theorem budget. The
finite counting/radial constants are not set to one or assumed small.
Three independent 70-digit incomplete-Gamma checks match the factorial
endpoint recurrence to relative error below `2e-9`. The probe is optional
and stays outside builds and CI.

Validation uses strict leaf checks, targeted module builds, and frozen
compiled-root imports with both explicit leaves. All 14 namespace linters
and every compiled declaration's transitive standard-axiom audit are
required. The ordinary root is not rebuilt or edited by this slice; no
README, explorer, public endpoint, commit or push is changed.
