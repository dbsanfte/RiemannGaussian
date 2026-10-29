# Exact head-fibre shortcut for the canonical source menu

Let r>0, L=r^Q, and let the actual alphabet be the canonical complete, duplicate-free list of all functions Fin Q→Fin r, in its original order. This is the menu identified by SourceWordBankSemantics.ids_decode and SourceWordBankIndexed.ids_indexed, not an arbitrary sampled/subgroup menu. Let p=head(q,a,b), so q:Fin Q and necessarily Q>0. Let remaining be Nodup; the original active list is remaining filtered by membership in [a,b]. Write m for its length, and e(k) for the original environment read before these local overrides.

The exact ORIGINAL padded count is:

| Condition | Raw active-completion count | Padded count (multiply by L^(4−m)) |
|---|---:|---:|
| a=b | L^m (m=0 or 1) | L^4 |
| a≠b, neither key active | indicator(e(a)(q)=e(b)(q)) | indicator·L^4 |
| a≠b, exactly one key active | r^(Q−1) | r^(4Q−1) |
| a≠b, both keys active | r^(2Q−1) | r^(4Q−1) |

In the neither-active line m=0. “Active” means literal membership in remaining; no inference about an unknown factor or semantic colour is involved. Fixed values include the exact reverse-prefix/default and newest-override lookup semantics. Overrides introduced by counting replace those previous values only on active keys. With Nodup remaining, every active key receives exactly one independent alphabet choice. Repeated support keys do not create two independent variables. For a=b the same final environment read occurs on both sides for every assignment, hence tautology, even if the old value was overridden.

## Counting proof

For fixed c:Fin r, restricting a word to the coordinates other than q is a bijection

    {w : Fin Q→Fin r | w(q)=c} ≃ ({j:Fin Q | j≠q}→Fin r).

The inverse fills q with c. The complement has cardinal Q−1, hence the fibre has r^(Q−1) words. For two independent words, keep the first word and all non-q coordinates of the second. Fill the second q-coordinate with the first q-coordinate. This bijection gives r^Q·r^(Q−1)=r^(2Q−1) satisfying ordered pairs. It does not divide by r in a composite ring.

For one active key, the inactive endpoint supplies an actual c:Fin r, and the first fibre bijection applies regardless of that c. For two active distinct keys, the second bijection applies regardless of active-list order. The remaining two table lines follow directly from no choices or literal self-equality. Multiplying the raw counts by the original padding gives the displayed result; exponents use Q>0 and m≤2. The canonical alphabet completeness/nodup theorem transfers these finite-type cardinalities to its literal ordered scans: order changes neither a finite sum nor multiplicity. No altered objective, normalization, or new averaging hypothesis is used.

Repeated source terms remain separate list occurrences. Their counts add with exactly the original multiplicities; no deduplication of terms is licensed by this shortcut. Q=0 has no q:Fin Q and therefore no head instruction. For r=1, L=1 and r^(4Q−1)=1, so all existing head instructions are tautologies as expected. r=0 is outside the positive-alphabet preparation and is not silently covered.

## Actual acquisition algorithm and cost

For each original head descriptor, compare the two acquired key words and test active membership using the actual remaining/support metadata. If keys coincide return the acquired L^4. If distinct and at least one is active return an acquired r^(4Q−1). Only if neither is active read the two fixed/default environment IDs, resolve their physical bank rows, read q, and compare actual colour words. Return L^4 or zero from that Boolean. The existing physical environment/predicate reader already supplies those scans and their original-bank bounds. Thus there are at most TWO fixed-coordinate reads, and no terminal truth or count advice. A supplied generic environment can be used only with its existing valid-ID invariant; the original indexed caller supplies it.

The integer constants can be acquired once and reused across all head descriptors: compute r^(Q−1) by Q−1 actual physical integer multiplications and multiply by three copies of L, or use repeated squaring for r^(4Q−1). L itself is already actually acquired by the bank initializer. There is no exact-division oracle and no unknown order. Counts have O(Q log(r+1)) bits; conservative schoolbook multiplication and physical copies give polynomial cost in Q and the acquired integer word widths, in addition to the actual key/environment/address scans. The acquired constants must be cached and their acquisition reports charged. Returning L^4 still requires copying its output bits. This replaces up to L² head leaves (and the old padding construction) with polynomial integer arithmetic; it does not yet replace incidence counting or the complete source/public runtime.

## Formal scope (completed original-count connector)

The NEW canonical modules are `RiemannGaussian.SemiprimeSourceHeadFibres` and `RiemannGaussian.SemiprimeSourceHeadCountFormula`. The first proves explicit fibre/collision equivalences and cardinalities. The second proves canonical-list sum conversion, fibre-indicator sums, actual recursive singleton/pair/self counts, complete classification of the paid active list, and finally:

    SourceHeadCountFormula.head_padded_original
      (r Q : Nat) (q : Fin Q) (a b : Nat)
      (remaining : List Nat) (env : Environment r Q)
      (hn : remaining.Nodup)

Its conclusion is exactly ORIGINAL SourceScoreCountsPadding.paddedLocal on `(SemiprimeFiniteEnumerations.words r Q).values`, equal to the proposed if-case formula. No desired count, uniformity, environment relation, fixed/default restriction or NeZero premise is assumed. Arbitrary typed original environments are included. The canonical menu's complete/nodup certificate is used to transfer actual list sums to Fintype cardinality. Original recursive calls and override updates are explicitly rewritten; there is no abstract assumed assignment-count equivalence.

The initial scratch head-fibre-shortcut.lean remains the finite-cardinality proof; head-original-count.lean is the scratch development of the full connector. Neither is a claimed optimized runtime. The physical optimized callback and aggregate controller replacement remain separate integration tasks, now supported by the exact original all-prefix theorem.
