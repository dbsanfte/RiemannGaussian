# Enumeration-inclusive source and integer-family acquisition

Four NEW files, frozen after strict autoImplicit=false/warningAsError=true builds, ordinary-root fifteen-linter and every-generated-declaration standard-axiom audit:165declarations/110theoremconstants. All four isolated strict objects byte-identical. Replay/pins: EnumerationAudit.lean, enumeration-audit.log, strict_recheck_enumerations.py, strict-recheck.json, enumeration-final-pins.json. No old sealed source, vendor or packet was edited.

## Actual finite constructor

`PaidFiniteEnumerationLists` executes recursive Fin-list generation, mapped Cartesian products, tagged sums and dependent flattening; all callback work, new cells and append traversal are retained. It does not call a supplied list/size/cardinality oracle. `words r Q` uses the SAME head-major order as the old recursive pi construction, but each candidate's EVERY coordinate is read into a concrete immutable array before exposing the resulting Word function. The function subsequently reads that array. Coordinate-list construction, per-coordinate reads, list/array cells, and the head/tail Cartesian construction all enter the report. This avoids pretending that an unbuilt length-Q coordinate chain is a single already materialized word.

`PaidFiniteEnumerations.indexed n F r Q arity` builds the complete Enumerations record. Its only data inputs are the original dimensions/arities; [NeZero r] is proof data. It acquires:

* ascending variable and factor Fin lists;
* factor-major dependent port incidences, calling the original arity metadata once per factor;
* the full A=r^Q word table and full D=r^(2Q) universal pair/slot table;
* ALL M² collision and Q*n² head score descriptors;
* the n+F variable/factor source index list;
* the wordTail by a paid COMPLETE coordinate zero-test for every word.

The universal constructor reuses its acquired word list internally for head/slot products. The top indexed constructor separately acquires the word list used by wordTail; this deliberate second acquisition is explicitly charged, not claimed shared for free. All retained coordinate arrays/list data are real runtime outputs. Old enumeration records appear only in erased nodup/completeness proofs and in equality theorems.

`indexed_value` proves equality to the ENTIRE previous FiniteEnumerations.indexed record, not merely the same unordered set or lengths. Thus every incidence, word, universal type, score and index has the same ordering; deterministic conditional-expectation tie choices downstream remain the same. Actual word functions are extensionally equal despite their new cached representation.

## Explicit fixed polynomial

Let M=sum_e arity(e), A=r^Q. The attached run's bound is the literal `polynomial n F M Q A A`, for Q>=1 (actual source guard has Q>=2). Define

    W(c,Q,A)=1+Q*[3(c+1)^2+c(4A+3)+1+3(Q+1)^2+c*A(5Q+5)+1+4],
    U(c,Q,A)=W(c,Q,A)+(7A+1)+(3A+1)+[A(4A+3)+1]+(4A^2+1)+4,
    I(F,M)=3(F+1)^2+F*[3(M+1)^2+4M+5]+2,
    T(M,n,Q)=[M(4M+3)+1]+[n(4n+3)+1]+[Q(4n^2+3)+1]
             +4(M^2+Q*n^2)+7,
    P(n,F,M,Q,c,A)=3(n+1)^2+3(F+1)^2+I(F,M)+W(c,Q,A)+U(c,Q,A)
                  +3(Q+1)^2+T(M,n,Q)+4(n+F)+4+A(3Q+4)+13.

Theorem `indexed_work_polynomial` proves actual work<=P(n,F,M,Q,A,A), using r<=r^Q for Q>=1. This is a fixed polynomial; no exponent depends on a network dimension. D=A² is exactly the acquired universal list size. `indexed_work` also supplies an unconditional finite report bound for Q=0; construction and ordering theorems themselves do not require Q>0. Exact menu lengths are M,D,M²+Q*n²,n+F; none is an attained-signature cardinality supplied as an answer.

## Source and integer constraints are actually joined

`PaidEnumeratedSource.acquire arity coordinate eps R` FIRST runs this new indexed constructor, THEN feeds its actual record to the sealed MaterializedOriginalSource.acquire. Both work reports plus the wrapper cell are retained. `acquire_value` proves the exact old source arrays; `acquire_coefficient` uses the existing immutable SourceArrayAcquisition.read accessor and covers every k<=R of the original builtLayout. Its acquire_work budget has no finite-list, chosen-label, coefficient or terminal-score advice; it substitutes actual lengths and bounds wordTail<=A.

`PaidEnumeratedConstraints.acquire` analogously calls the new constructor then the actual PaidOriginalConstraints.acquire. Its value theorem preserves the ENTIRE stored family and row ordering. `read_acquire` matches the original padded matrix on named head columns. `acquire_work_native`, under the actual native r>=2 guard, retains both generation reports and uses the parent's already proved original-constraint polynomial; no unknown block count or supplied label-work bound survives.

These convenience wrappers each generate their own finite record. A joint setup controller can instead run indexed ONCE, pass its value to source and constraint producers, and add indexed.work once. Such sharing is an optimization/next integration step, not silently asserted by these standalone wrappers.

## Clock model and frontier

This is an attached scalar/list/cell/coordinate-access trace. Each original arity invocation is a metadata access event; construction of the original public network/arity descriptor and its primitive bit execution is a separate implementation layer. Coordinate copy functions perform actual finite array reads/writes, but proof of physical bit-pointer/tape simulation of those accesses is not supplied here. Rational arithmetic and integer bit heights in the downstream source/constraint producers remain their existing explicit interfaces.

This closes the initial-source-enumeration omission for the NEW source/constraint wrappers. It does NOT retroactively change any sealed CachedSourceCounter/Public/Scheduled definition. A final full setup controller must literally call these acquired data paths and the physical selector, retain their setup reports and aggregate count/prefix/decoder work. Existing old raw/build design paths and the full original-input bit clock must not be declared free by citing this result.

## Executable control

One actual enumeration run, n=F=r=Q=2 and arities [1,2], returns incidences [(0,0),(1,0),(1,1)], D=16, tail words 01/10/11,17scoreterms,4indices and work838. It executes the actual coordinate-array construction and finite menus. This is a computability/order control, not a factor example or scaling benchmark. Kernel proofs above cover all finite parameters.
