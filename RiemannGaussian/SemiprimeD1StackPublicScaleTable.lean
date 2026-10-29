/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticTable
import RiemannGaussian.SemiprimeD1StackPublicScaleFinite
/-! # One fixed 332-role whole-table compiler for the actual public integer scale checker
Only original binary N, original descriptor marker fields and a physically
acquired scope-ID bank are initialized. The static checker is fixed before N;
All selector, guard and scale-equation branches execute that SAME code.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicScaleTable
namespace P
export SemiprimeD1StackPublicScale (Stack Label program initial)
/-- Actual original binary input role. -/
def inputRole : Stack := SemiprimeD1StackPublicScaleBounds.inputRole
/-- Actual checker verdict role. -/
def output : Stack := SemiprimeD1StackPublicScale.auxRole .output
/-- Physical raw assignment role. -/
def assignment : Stack := .inr (.inr .raw)
/-- Actual physical j marker role. -/
def stride : Stack := .inr (.inl (.inl (.inl (.inl .stride))))
/-- Actual physical k marker role. -/
def frequency : Stack := .inr (.inl (.inl (.inl (.inl .frequency))))
/-- Actual physical singleton forward/inverse selector. -/
def selector : Stack := .inr (.inr .selector)
end P
namespace G
export SemiprimeD1StackStaticTable (Static)
end G
/-- Literal complete160-role scale-checker inventory, including every shadow. -/
def roles : List P.Stack :=
  [Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.input))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.width))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.nonzero))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.threshold))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.radius))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.square))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.exponent))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.squareWork))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.thresholdWork))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.temporary))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.radix))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackDigitBlock.Stack.input))))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackDigitBlock.Stack.width))))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackDigitBlock.Stack.counter))))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackDigitBlock.Stack.scratch))))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackDigitBlock.Stack.temporary))))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackDigitBlock.Stack.dummyLeft))))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackDigitBlock.Stack.dummyRight))))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackDigitBlock.Stack.output))))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inr 0))))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inr 1))))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inr 2))))),
        Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inr PUnit.unit)))), Sum.inl (Sum.inl (Sum.inr (Sum.inl true))),
        Sum.inl (Sum.inl (Sum.inr (Sum.inl false))), Sum.inl (Sum.inl (Sum.inr (Sum.inr 0))),
        Sum.inl (Sum.inl (Sum.inr (Sum.inr 1))), Sum.inl (Sum.inl (Sum.inr (Sum.inr 2))),
        Sum.inl (Sum.inr SemiprimeD1StackRootSources.Aux.base),
        Sum.inl (Sum.inr SemiprimeD1StackRootSources.Aux.markers),
        Sum.inl (Sum.inr SemiprimeD1StackRootSources.Aux.count),
        Sum.inl (Sum.inr SemiprimeD1StackRootSources.Aux.scratch),
        Sum.inl (Sum.inr SemiprimeD1StackRootSources.Aux.root),
        Sum.inl (Sum.inr SemiprimeD1StackRootSources.Aux.normal),
        Sum.inl (Sum.inr SemiprimeD1StackRootSources.Aux.forwardRoot),
        Sum.inl (Sum.inr SemiprimeD1StackRootSources.Aux.forwardNormal),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.base)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.stride)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.frequency)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.count)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.remaining)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.multiplier)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.productScratch)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.intermediate)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.exponent)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.powerCounter)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.powerScratch)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.cache)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.reader)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.index)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.parser)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.skipped)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.word)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.valid)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.readerCopy)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.frameScratch)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.copyScratch)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackExprDot.Stack.output)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr SemiprimeD1StackExpr.Stack.code)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr SemiprimeD1StackExpr.Stack.modulus)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr SemiprimeD1StackExpr.Stack.saved)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr SemiprimeD1StackExpr.Stack.result)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr SemiprimeD1StackExpr.Stack.left)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr SemiprimeD1StackExpr.Stack.right)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr SemiprimeD1StackExpr.Stack.flag)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr SemiprimeD1StackExpr.Stack.scratch)))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.literal (Sum.inl 0)))))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.literal (Sum.inl 1)))))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.literal (Sum.inl 2)))))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.literal (Sum.inl 3)))))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.literal (Sum.inl 4)))))),
        Sum.inr
          (Sum.inl (Sum.inl (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.literal (Sum.inr (Sum.inl PUnit.unit))))))),
        Sum.inr
          (Sum.inl (Sum.inl (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.literal (Sum.inr (Sum.inr PUnit.unit))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.addition (Sum.inl SemiprimeD1StackAdder.Stack.left)))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.addition (Sum.inl SemiprimeD1StackAdder.Stack.right)))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.addition (Sum.inl SemiprimeD1StackAdder.Stack.scratch)))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.addition (Sum.inl SemiprimeD1StackAdder.Stack.output)))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.addition
                    (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.left)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.addition
                    (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.right)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.addition
                    (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.scratch)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.addition
                    (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.output)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.addition
                    (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.input)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.addition
                    (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.divisor)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.addition
                    (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.digits)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.addition
                    (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.remainder)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.addition
                    (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.quotient)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.addition
                    (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.copyScratch)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.addition
                    (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.template)))))))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.addition (Sum.inr (Sum.inr true))))))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.addition (Sum.inr (Sum.inr false))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.subtraction (Sum.inl SemiprimeD1StackAdder.Stack.left)))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr (SemiprimeD1StackExpr.Stack.subtraction (Sum.inl SemiprimeD1StackAdder.Stack.right)))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr (SemiprimeD1StackExpr.Stack.subtraction (Sum.inl SemiprimeD1StackAdder.Stack.scratch)))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr (SemiprimeD1StackExpr.Stack.subtraction (Sum.inl SemiprimeD1StackAdder.Stack.output)))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.subtraction (Sum.inr (Sum.inl SemiprimeD1StackAdder.Stack.left))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.subtraction (Sum.inr (Sum.inl SemiprimeD1StackAdder.Stack.right))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.subtraction (Sum.inr (Sum.inl SemiprimeD1StackAdder.Stack.scratch))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.subtraction (Sum.inr (Sum.inl SemiprimeD1StackAdder.Stack.output))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.subtraction
                    (Sum.inr (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.left))))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.subtraction
                    (Sum.inr (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.right))))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.subtraction
                    (Sum.inr (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.scratch))))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.subtraction
                    (Sum.inr (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.output))))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.subtraction
                    (Sum.inr (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.input))))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.subtraction
                    (Sum.inr (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.divisor))))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.subtraction
                    (Sum.inr (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.digits))))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.subtraction
                    (Sum.inr (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.remainder))))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.subtraction
                    (Sum.inr (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.quotient))))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.subtraction
                    (Sum.inr (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.copyScratch))))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.subtraction
                    (Sum.inr (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.template))))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.subtraction (Sum.inr (Sum.inr (Sum.inr true)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.subtraction (Sum.inr (Sum.inr (Sum.inr false)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.multiplication (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.left))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.multiplication (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.right))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.multiplication
                    (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.scratch))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.multiplication
                    (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.output))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.multiplication (Sum.inl (Sum.inr (Sum.inl 0)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.multiplication (Sum.inl (Sum.inr (Sum.inl 1)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.multiplication (Sum.inl (Sum.inr (Sum.inl 2)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.multiplication (Sum.inl (Sum.inr (Sum.inr true)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.multiplication (Sum.inl (Sum.inr (Sum.inr false)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.multiplication
                    (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.left)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.multiplication
                    (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.right)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.multiplication
                    (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.scratch)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.multiplication
                    (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.output)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.multiplication
                    (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.input)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.multiplication
                    (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.divisor)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.multiplication
                    (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.digits)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.multiplication
                    (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.remainder)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.multiplication
                    (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.quotient)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.multiplication
                    (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.copyScratch)))))))),
        Sum.inr
          (Sum.inl
            (Sum.inl
              (Sum.inl
                (Sum.inr
                  (SemiprimeD1StackExpr.Stack.multiplication
                    (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.template)))))))),
        Sum.inr
          (Sum.inl (Sum.inl (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.multiplication (Sum.inr (Sum.inr true))))))),
        Sum.inr
          (Sum.inl (Sum.inl (Sum.inl (Sum.inr (SemiprimeD1StackExpr.Stack.multiplication (Sum.inr (Sum.inr false))))))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inr SemiprimeD1StackVectorCanonical.Stack.cache))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inr SemiprimeD1StackVectorCanonical.Stack.modulus))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inr SemiprimeD1StackVectorCanonical.Stack.reader))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inr SemiprimeD1StackVectorCanonical.Stack.word))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inr SemiprimeD1StackVectorCanonical.Stack.scratch))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inr SemiprimeD1StackVectorCanonical.Stack.valid))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inr SemiprimeD1StackVectorCanonical.Stack.difference))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inr SemiprimeD1StackVectorCanonical.Stack.copiedModulus))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inr SemiprimeD1StackVectorCanonical.Stack.lessFlag))),
        Sum.inr (Sum.inl (Sum.inl (Sum.inr SemiprimeD1StackVectorCanonical.Stack.output))),
        Sum.inr (Sum.inl (Sum.inr (Sum.inl 0))), Sum.inr (Sum.inl (Sum.inr (Sum.inl 1))),
        Sum.inr (Sum.inl (Sum.inr (Sum.inl 2))), Sum.inr (Sum.inl (Sum.inr (Sum.inl 3))),
        Sum.inr (Sum.inl (Sum.inr (Sum.inl 4))), Sum.inr (Sum.inl (Sum.inr (Sum.inr 0))),
        Sum.inr (Sum.inl (Sum.inr (Sum.inr 1))), Sum.inr (Sum.inl (Sum.inr (Sum.inr 2))),
        Sum.inr (Sum.inl (Sum.inr (Sum.inr 3))), Sum.inr (Sum.inl (Sum.inr (Sum.inr 4))),
        Sum.inr (Sum.inr SemiprimeD1StackPublicScale.Aux.raw),
        Sum.inr (Sum.inr SemiprimeD1StackPublicScale.Aux.selector),
        Sum.inr (Sum.inr SemiprimeD1StackPublicScale.Aux.padding),
        Sum.inr (Sum.inr SemiprimeD1StackPublicScale.Aux.scratch),
        Sum.inr (Sum.inr SemiprimeD1StackPublicScale.Aux.count), Sum.inr (Sum.inr SemiprimeD1StackPublicScale.Aux.word),
        Sum.inr (Sum.inr SemiprimeD1StackPublicScale.Aux.output)]
/-- All160 roles are visited exactly once, as a compile-time fact only. -/
theorem roles_nodup : roles.Nodup := by decide
/-- The literal inventory has its fixed160 positions before all inputs. -/
theorem roles_length : roles.length=160 := by decide
/-- Dormant input/header/comparator/private shadows are included too. -/
theorem roles_complete (k : P.Stack) : k∈roles := by
  have h:roles.toFinset=(Finset.univ : Finset P.Stack):=by decide
  have hk:k∈roles.toFinset:=by rw [h];exact Finset.mem_univ k
  exact List.mem_toFinset.mp hk
/-- One constant static checker instance for ALL original inputs/descriptors.
There is no N, arity, raw assignment, predicate or budget in this value. -/
def static : G.Static P.Stack P.Label :=
  ⟨P.program,.start,P.assignment,P.output,roles,roles_complete,roles_nodup⟩
/-- The fixed finite Boolean-bank type, independent of N and descriptor values. -/
abbrev Stack := SemiprimeD1StackStaticTable.Stack P.Stack
/-- The fixed finite label type, independent of N and actual scope arity. -/
abbrev Label := SemiprimeD1StackStaticTable.Label P.Label roles.length
/-- Literal whole table program; the SAME constant checker instance for all N. -/
def program : Label→SemiprimeD1StackCalls.Instruction Stack Label :=
  SemiprimeD1StackStaticTable.program static
/-- The read-only template contains ONLY actual checker initialization words:
original binary N, physical j/k marker fields and singleton selector; raw empty. -/
def inputTemplate (bits stride frequency : List Bool) (inverse : Bool) : P.Stack→List Bool :=(P.initial bits [] stride frequency inverse).data
/-- The scope is an actual binary-ID vector; its arity is acquired by the real
record scanner rather than initialized as a cardinality/width/count answer. -/
def initial (bits stride frequency : List Bool) (inverse : Bool) (bank : List Bool) : SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackStaticTable.initial static (inputTemplate bits stride frequency inverse) bank
/-- One genuine finite machine fixed before ALL original N and descriptor values. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackStaticTable.machine static
/-- The raw-assignment slot in the input template is physically EMPTY. -/
theorem template_raw (bits stride frequency : List Bool) (inverse : Bool) : inputTemplate bits stride frequency inverse P.assignment=[] := rfl
/-- Supplying the actual physically reversed prefix reproduces exactly the
frozen original checker's input; no metadata/caches/verdict are added. -/
theorem template_raw_update (bits raw stride frequency : List Bool) (inverse : Bool) :
    Function.update (inputTemplate bits stride frequency inverse) P.assignment raw=(P.initial bits raw stride frequency inverse).data := by
  funext k
  cases k with
  | inl k=>rfl
  | inr k=>cases k with
    | inl k=>rfl
    | inr k=>cases k <;> rfl
/-- Complete332-role inventory: checker160, read-only template160, counter7 and DFS5. -/
theorem stack_card : Fintype.card Stack=332 := by
  rw [SemiprimeD1StackStaticTable.stack_card,SemiprimeD1StackPublicScale.stack_card]
/-- Runtime state consists solely of finite Boolean and return-label flags. -/
theorem control_finite : Finite machine.σ :=SemiprimeD1StackStaticTable.control_finite static
end RiemannGaussian.SemiprimeD1StackPublicScaleTable
