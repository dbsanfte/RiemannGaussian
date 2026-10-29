# Actual physical native-group clock

NEW SemiprimeNativeGroupBitsBudget is final frozen and canonical strict/root15/all-generated standard3 PASS (18 declarations/15 theorems). It proves cost bounds for the ACTUAL NativeGroupBits program, separately from skein's run_correct semantic proof.

productList_bounded and productList_clock handle every real same-order tail-first factor callback, suffix multiplication and nil/one buffer. Each callback is called once and its report retained. multiplyBudget includes the actual JetBits convolution/dot and coefficient-access costs; it is not an abstract unit polynomial multiplication.

run_clock bounds the actual group report by

```
groupBudget n F R J b s w A E
```

with s=sum arity, original local arity<=w, original source word arrays width<=groupWidth(b,R,F,s) and size<=A, integer node-word width bounded by the same derived W, and actual entry callbacks clock<=E and magnitude length<=W. These are ORIGINAL input-word/callback bounds, not intermediate Fits. The only exponential traversal is 2^w inside the local evaluator. Total incidence s affects groupWidth polynomially, not a spurious 2^s local truth table.

The budget retains ALL corrected-port/local reports, all F active or inactive factor reports, every suffix convolution and the actual groupControl allowance. run_bounded and the existing run_size bound the ACTUAL output words. decodeWork_bound then bounds the declared scalar-boundary normalization/copy allowance from those actual output lengths. toScalarRun_clock proves complete scalarGroupBudget for report.clock+decodeWork, without equating old/new group work or discarding the physical clock.

Source-word acquisition remains separate and must be added by the actual setup/counter caller. Generic source/grouping getter implementations and finite-memory/address/tape refinement retain their documented scopes. In particular decodeWork is a declared boundary ledger; this module does not turn rational boundary decoding or all surrounding scalar folds into an executed primitive tape program. Physical arithmetic before that boundary is the actual JetBits/RationalBits path.
