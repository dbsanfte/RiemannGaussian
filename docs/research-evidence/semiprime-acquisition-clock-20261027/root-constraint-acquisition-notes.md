# Actual original integer-constraint acquisition

Five NEW modules: PaidConstraintCache, PaidConstraintRows,
PaidPackingSnapshot, PaidConstraintAcquisition, PaidOriginalConstraints.
Earlier modules and sealed packets were not edited.

The original integer rows used by the source-based factor-count detour now
have an actual report-bearing acquisition program. This is not a new native
long-query shortcut and does not improve the native soft-K^1.25 bound.

## Runtime data flow and exact equality

1. The actual original conditional-expectation word search executes once. Its
   output is the cached reverse-prefix word list used by the paid label reader.
   OriginalConstraints supplies that concrete producer internally: neither a
   label function answer nor a label-work budget is a runtime input.
2. PackingSnapshot performs the actual label/bucket/minimum/address scans once
   and retains both the common block count and addresses. Its address output is
   exactly the sealed MaterializedPacking output; retaining the block count
   adds one charged metadata cell.
3. ConstraintCache acquires the actual parity/universal integer numerator
   table once and the denominator 2^(R-1) once. Each later constraint entry uses
   executed finite list/key scans and the complete paid universal-word equality
   comparison. It does not call the old uninstrumented numerator at runtime.
4. Complete-block rows use cached Nat block IDs and universal types. Leftover
   rows use actual packing-address and label reads. The owner pullback scans
   the original finite incidence list, charges all owner tests, and sums the
   returned integer contributions. copy_value/source_value prove exact equality
   with the old padded row family, including covered leftovers and zero rows.
5. The row-name program constructs every (block,type) name followed by every
   original incidence name, in exactly the original padded enumeration order.
   The Q-by-r-by-p-by-n integer family is fully materialized by nested finite
   callbacks. Its work includes explicit finite-coordinate list construction,
   packing, numerator setup, names, all entries and all returned lower reports.
6. OriginalConstraints.read executes four actual finite-list scans. For every
   valid original head column, read_acquire proves exact equality with the
   previous SourceConstraintAcquisition.matrix. The acquisition stores the
   untruncated source row: outside-head zero/truncation is not silently imposed
   by a type cast or assumed in this theorem. A future design builder can read
   only the actual head columns, or explicitly perform that truncation.

The read budget is 2*(Q+r+p+n)+8 list-cell/control units. The complete family
has p=blocks*D+M original padded row names, where M is incidence count and D
universal alphabet size. blocks_le proves blocks<=M even for empty alphabets.

## Closed resource envelope and its scope

All complete-family work has an explicit budget in original dimensions. The
only superficially exponential universal entry term is the existing paid
subset/difference expansion. At r>=2, its bound

    entryBudget(Q,R) <= D*entryPolynomial(Q,R),  D=r^(2Q)

is proved from the actual complete universal alphabet. The new native theorem
substitutes this and blocks<=M to obtain a literal fixed polynomial. The
original searched-label producer is also instantiated with its already proved
explicit polynomial; no terminal-score, label, packing-size or row budget
premise remains in OriginalConstraints.acquire_work_native.

This is an integer/rational scalar, selected register, finite-list and control
ledger. It does NOT turn each rational operation, Nat floor, encoded equality,
metadata call, list address, allocation or counter increment into one bit step.
The original network owner/factor functions and input finite enumerations have
their stated interfaces; source enumerations are charged separately by the
new enum acquisition modules. Public macro graph generation is a further
separate setup obligation.

This family is not yet substituted into the runtime RawDesign/build path of
the public counter. The new physical row selector needs encoded integer input
words, a derived physical width/template and actual cached grouping/column
metadata; its output then needs to become the runtime selected design. The
current public count/controller continues to use the older raw/build supplier,
whose work omission is explicitly documented. OriginalConstraints reconstructs
its own searched labels/packing; any future join with coefficient acquisition
must either share them concretely or charge both executions. No free shared
cache is presumed.

## Verification and controls

All five modules passed strict autoImplicit=false/warningAsError=true checking,
ordinary-root fifteen-linter audits, and all-generated transitive standard-axiom
audits: 188 declarations, 106 theorem constants. Final combined isolated builds
and full compiler-import source/object pins are performed by the packet verifier.

PaidConstraintSmoke.lean checks the actual executed closure, with one incidence
and an additional unused original variable. For R=0 and R=4 it returns
(1,1,2269,true) and (1,1,3223,true): every acquired entry agrees with the legacy
matrix in this small control, including zero columns. Empty incidences/variables
and Q=0 produce (0,0,88). These are finite interpreter/edge controls, not rate,
coverage or semiprime-success evidence. General semantic equality is proved.
