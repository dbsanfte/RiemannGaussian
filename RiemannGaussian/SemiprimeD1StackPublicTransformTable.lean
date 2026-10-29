/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticTable
import RiemannGaussian.SemiprimeD1StackPublicTransformOriginalResources
/-! # One fixed 420-role whole-table compiler for the actual public integer transform checker
Only original binary N, original descriptor marker fields and a physically
acquired scope-ID bank are initialized. The static checker is fixed before N;
All stage, selector, guard and transform-equation branches execute that SAME code.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2040000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformTable
namespace P
export SemiprimeD1StackPublicTransform (Stack Label program initial)
/-- Actual original binary input role. -/
def inputRole : Stack := SemiprimeD1StackPublicTransformResources.inputRole
/-- Actual checker verdict role. -/
def output : Stack := .aux .output
/-- Actual physical raw-assignment role. -/
def assignment : Stack := .aux .raw
/-- Actual first/second descriptor flag role. -/
def second : Stack := .aux .second
/-- Actual forward/inverse descriptor flag role. -/
def inverse : Stack := .aux .inverse
end P
namespace G
export SemiprimeD1StackStaticTable (Static)
end G
/-- Literal complete204-role transform-checker inventory, including every shadow. -/
def roles : List P.Stack :=
  [SemiprimeD1StackPublicTransform.Stack.roots (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.input))),
        SemiprimeD1StackPublicTransform.Stack.roots (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.width))),
        SemiprimeD1StackPublicTransform.Stack.roots
          (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.nonzero))),
        SemiprimeD1StackPublicTransform.Stack.roots
          (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.threshold))),
        SemiprimeD1StackPublicTransform.Stack.roots
          (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.radius))),
        SemiprimeD1StackPublicTransform.Stack.roots
          (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.square))),
        SemiprimeD1StackPublicTransform.Stack.roots
          (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.exponent))),
        SemiprimeD1StackPublicTransform.Stack.roots
          (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.squareWork))),
        SemiprimeD1StackPublicTransform.Stack.roots
          (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.thresholdWork))),
        SemiprimeD1StackPublicTransform.Stack.roots
          (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.temporary))),
        SemiprimeD1StackPublicTransform.Stack.roots (Sum.inl (Sum.inl (Sum.inl SemiprimeD1StackTransform.Stack.radix))),
        SemiprimeD1StackPublicTransform.Stack.roots
          (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackDigitBlock.Stack.input))))),
        SemiprimeD1StackPublicTransform.Stack.roots
          (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackDigitBlock.Stack.width))))),
        SemiprimeD1StackPublicTransform.Stack.roots
          (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackDigitBlock.Stack.counter))))),
        SemiprimeD1StackPublicTransform.Stack.roots
          (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackDigitBlock.Stack.scratch))))),
        SemiprimeD1StackPublicTransform.Stack.roots
          (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackDigitBlock.Stack.temporary))))),
        SemiprimeD1StackPublicTransform.Stack.roots
          (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackDigitBlock.Stack.dummyLeft))))),
        SemiprimeD1StackPublicTransform.Stack.roots
          (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackDigitBlock.Stack.dummyRight))))),
        SemiprimeD1StackPublicTransform.Stack.roots
          (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackDigitBlock.Stack.output))))),
        SemiprimeD1StackPublicTransform.Stack.roots (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inr 0))))),
        SemiprimeD1StackPublicTransform.Stack.roots (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inr 1))))),
        SemiprimeD1StackPublicTransform.Stack.roots (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inr 2))))),
        SemiprimeD1StackPublicTransform.Stack.roots (Sum.inl (Sum.inl (Sum.inr (Sum.inr PUnit.unit)))),
        SemiprimeD1StackPublicTransform.Stack.roots (Sum.inl (Sum.inr (Sum.inl true))),
        SemiprimeD1StackPublicTransform.Stack.roots (Sum.inl (Sum.inr (Sum.inl false))),
        SemiprimeD1StackPublicTransform.Stack.roots (Sum.inl (Sum.inr (Sum.inr 0))),
        SemiprimeD1StackPublicTransform.Stack.roots (Sum.inl (Sum.inr (Sum.inr 1))),
        SemiprimeD1StackPublicTransform.Stack.roots (Sum.inl (Sum.inr (Sum.inr 2))),
        SemiprimeD1StackPublicTransform.Stack.roots (Sum.inr SemiprimeD1StackRootSources.Aux.base),
        SemiprimeD1StackPublicTransform.Stack.roots (Sum.inr SemiprimeD1StackRootSources.Aux.markers),
        SemiprimeD1StackPublicTransform.Stack.roots (Sum.inr SemiprimeD1StackRootSources.Aux.count),
        SemiprimeD1StackPublicTransform.Stack.roots (Sum.inr SemiprimeD1StackRootSources.Aux.scratch),
        SemiprimeD1StackPublicTransform.Stack.roots (Sum.inr SemiprimeD1StackRootSources.Aux.root),
        SemiprimeD1StackPublicTransform.Stack.roots (Sum.inr SemiprimeD1StackRootSources.Aux.normal),
        SemiprimeD1StackPublicTransform.Stack.roots (Sum.inr SemiprimeD1StackRootSources.Aux.forwardRoot),
        SemiprimeD1StackPublicTransform.Stack.roots (Sum.inr SemiprimeD1StackRootSources.Aux.forwardNormal),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.base),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.stride),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.frequency),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.count),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.remaining),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.multiplier),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.productScratch),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.intermediate),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.exponent),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.powerCounter),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.powerScratch),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.cache),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.reader),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.index),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.parser),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.skipped),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.word),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.valid),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.readerCopy),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.frameScratch),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.copyScratch),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inl SemiprimeD1StackExprDot.Stack.output),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inr SemiprimeD1StackExpr.Stack.code),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inr SemiprimeD1StackExpr.Stack.modulus),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inr SemiprimeD1StackExpr.Stack.saved),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inr SemiprimeD1StackExpr.Stack.result),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inr SemiprimeD1StackExpr.Stack.left),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inr SemiprimeD1StackExpr.Stack.right),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inr SemiprimeD1StackExpr.Stack.flag),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inr SemiprimeD1StackExpr.Stack.scratch),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inr (SemiprimeD1StackExpr.Stack.literal (Sum.inl 0))),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inr (SemiprimeD1StackExpr.Stack.literal (Sum.inl 1))),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inr (SemiprimeD1StackExpr.Stack.literal (Sum.inl 2))),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inr (SemiprimeD1StackExpr.Stack.literal (Sum.inl 3))),
        SemiprimeD1StackPublicTransform.Stack.dot (Sum.inr (SemiprimeD1StackExpr.Stack.literal (Sum.inl 4))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.literal (Sum.inr (Sum.inl PUnit.unit)))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.literal (Sum.inr (Sum.inr PUnit.unit)))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.addition (Sum.inl SemiprimeD1StackAdder.Stack.left))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.addition (Sum.inl SemiprimeD1StackAdder.Stack.right))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.addition (Sum.inl SemiprimeD1StackAdder.Stack.scratch))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.addition (Sum.inl SemiprimeD1StackAdder.Stack.output))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.addition (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.left))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.addition (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.right))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.addition (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.scratch))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.addition (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.output))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.addition (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.input))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.addition (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.divisor))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.addition (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.digits))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.addition (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.remainder))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.addition (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.quotient))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.addition
              (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.copyScratch))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.addition (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.template))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.addition (Sum.inr (Sum.inr true)))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.addition (Sum.inr (Sum.inr false)))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.subtraction (Sum.inl SemiprimeD1StackAdder.Stack.left))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.subtraction (Sum.inl SemiprimeD1StackAdder.Stack.right))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.subtraction (Sum.inl SemiprimeD1StackAdder.Stack.scratch))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.subtraction (Sum.inl SemiprimeD1StackAdder.Stack.output))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.subtraction (Sum.inr (Sum.inl SemiprimeD1StackAdder.Stack.left)))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.subtraction (Sum.inr (Sum.inl SemiprimeD1StackAdder.Stack.right)))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.subtraction (Sum.inr (Sum.inl SemiprimeD1StackAdder.Stack.scratch)))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.subtraction (Sum.inr (Sum.inl SemiprimeD1StackAdder.Stack.output)))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.subtraction
              (Sum.inr (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.left)))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.subtraction
              (Sum.inr (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.right)))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.subtraction
              (Sum.inr (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.scratch)))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.subtraction
              (Sum.inr (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.output)))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.subtraction
              (Sum.inr (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.input)))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.subtraction
              (Sum.inr (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.divisor)))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.subtraction
              (Sum.inr (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.digits)))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.subtraction
              (Sum.inr (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.remainder)))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.subtraction
              (Sum.inr (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.quotient)))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.subtraction
              (Sum.inr (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.copyScratch)))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.subtraction
              (Sum.inr (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.template)))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.subtraction (Sum.inr (Sum.inr (Sum.inr true))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.subtraction (Sum.inr (Sum.inr (Sum.inr false))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.multiplication (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.left)))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.multiplication (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.right)))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.multiplication (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.scratch)))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.multiplication (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.output)))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.multiplication (Sum.inl (Sum.inr (Sum.inl 0))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.multiplication (Sum.inl (Sum.inr (Sum.inl 1))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.multiplication (Sum.inl (Sum.inr (Sum.inl 2))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.multiplication (Sum.inl (Sum.inr (Sum.inr true))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.multiplication (Sum.inl (Sum.inr (Sum.inr false))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.multiplication (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.left))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.multiplication
              (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.right))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.multiplication
              (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.scratch))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.multiplication
              (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.output))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.multiplication
              (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.input))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.multiplication
              (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.divisor))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.multiplication
              (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.digits))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.multiplication
              (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.remainder))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.multiplication
              (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.quotient))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.multiplication
              (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.copyScratch))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr
            (SemiprimeD1StackExpr.Stack.multiplication
              (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.template))))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.multiplication (Sum.inr (Sum.inr true)))),
        SemiprimeD1StackPublicTransform.Stack.dot
          (Sum.inr (SemiprimeD1StackExpr.Stack.multiplication (Sum.inr (Sum.inr false)))),
        SemiprimeD1StackPublicTransform.Stack.multiply (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.left)),
        SemiprimeD1StackPublicTransform.Stack.multiply (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.right)),
        SemiprimeD1StackPublicTransform.Stack.multiply (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.scratch)),
        SemiprimeD1StackPublicTransform.Stack.multiply (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.output)),
        SemiprimeD1StackPublicTransform.Stack.multiply (Sum.inl (Sum.inr (Sum.inl 0))),
        SemiprimeD1StackPublicTransform.Stack.multiply (Sum.inl (Sum.inr (Sum.inl 1))),
        SemiprimeD1StackPublicTransform.Stack.multiply (Sum.inl (Sum.inr (Sum.inl 2))),
        SemiprimeD1StackPublicTransform.Stack.multiply (Sum.inl (Sum.inr (Sum.inr true))),
        SemiprimeD1StackPublicTransform.Stack.multiply (Sum.inl (Sum.inr (Sum.inr false))),
        SemiprimeD1StackPublicTransform.Stack.multiply (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.left))),
        SemiprimeD1StackPublicTransform.Stack.multiply (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.right))),
        SemiprimeD1StackPublicTransform.Stack.multiply
          (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.scratch))),
        SemiprimeD1StackPublicTransform.Stack.multiply (Sum.inr (Sum.inl (Sum.inl SemiprimeD1StackAdder.Stack.output))),
        SemiprimeD1StackPublicTransform.Stack.multiply (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.input))),
        SemiprimeD1StackPublicTransform.Stack.multiply
          (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.divisor))),
        SemiprimeD1StackPublicTransform.Stack.multiply (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.digits))),
        SemiprimeD1StackPublicTransform.Stack.multiply
          (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.remainder))),
        SemiprimeD1StackPublicTransform.Stack.multiply
          (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.quotient))),
        SemiprimeD1StackPublicTransform.Stack.multiply
          (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.copyScratch))),
        SemiprimeD1StackPublicTransform.Stack.multiply
          (Sum.inr (Sum.inl (Sum.inr SemiprimeD1StackDivider.Aux.template))),
        SemiprimeD1StackPublicTransform.Stack.multiply (Sum.inr (Sum.inr true)),
        SemiprimeD1StackPublicTransform.Stack.multiply (Sum.inr (Sum.inr false)),
        SemiprimeD1StackPublicTransform.Stack.inputVector (Sum.inl 0),
        SemiprimeD1StackPublicTransform.Stack.inputVector (Sum.inl 1),
        SemiprimeD1StackPublicTransform.Stack.inputVector (Sum.inl 2),
        SemiprimeD1StackPublicTransform.Stack.inputVector (Sum.inl 3),
        SemiprimeD1StackPublicTransform.Stack.inputVector (Sum.inl 4),
        SemiprimeD1StackPublicTransform.Stack.inputVector (Sum.inr 0),
        SemiprimeD1StackPublicTransform.Stack.inputVector (Sum.inr 1),
        SemiprimeD1StackPublicTransform.Stack.inputVector (Sum.inr 2),
        SemiprimeD1StackPublicTransform.Stack.inputVector (Sum.inr 3),
        SemiprimeD1StackPublicTransform.Stack.inputVector (Sum.inr 4),
        SemiprimeD1StackPublicTransform.Stack.outputVector (Sum.inl 0),
        SemiprimeD1StackPublicTransform.Stack.outputVector (Sum.inl 1),
        SemiprimeD1StackPublicTransform.Stack.outputVector (Sum.inl 2),
        SemiprimeD1StackPublicTransform.Stack.outputVector (Sum.inl 3),
        SemiprimeD1StackPublicTransform.Stack.outputVector (Sum.inl 4),
        SemiprimeD1StackPublicTransform.Stack.outputVector (Sum.inr 0),
        SemiprimeD1StackPublicTransform.Stack.outputVector (Sum.inr 1),
        SemiprimeD1StackPublicTransform.Stack.outputVector (Sum.inr 2),
        SemiprimeD1StackPublicTransform.Stack.outputVector (Sum.inr 3),
        SemiprimeD1StackPublicTransform.Stack.outputVector (Sum.inr 4),
        SemiprimeD1StackPublicTransform.Stack.guard SemiprimeD1StackVectorCanonical.Stack.cache,
        SemiprimeD1StackPublicTransform.Stack.guard SemiprimeD1StackVectorCanonical.Stack.modulus,
        SemiprimeD1StackPublicTransform.Stack.guard SemiprimeD1StackVectorCanonical.Stack.reader,
        SemiprimeD1StackPublicTransform.Stack.guard SemiprimeD1StackVectorCanonical.Stack.word,
        SemiprimeD1StackPublicTransform.Stack.guard SemiprimeD1StackVectorCanonical.Stack.scratch,
        SemiprimeD1StackPublicTransform.Stack.guard SemiprimeD1StackVectorCanonical.Stack.valid,
        SemiprimeD1StackPublicTransform.Stack.guard SemiprimeD1StackVectorCanonical.Stack.difference,
        SemiprimeD1StackPublicTransform.Stack.guard SemiprimeD1StackVectorCanonical.Stack.copiedModulus,
        SemiprimeD1StackPublicTransform.Stack.guard SemiprimeD1StackVectorCanonical.Stack.lessFlag,
        SemiprimeD1StackPublicTransform.Stack.guard SemiprimeD1StackVectorCanonical.Stack.output,
        SemiprimeD1StackPublicTransform.Stack.read SemiprimeD1StackJetRead.Stack.cache,
        SemiprimeD1StackPublicTransform.Stack.read SemiprimeD1StackJetRead.Stack.reader,
        SemiprimeD1StackPublicTransform.Stack.read SemiprimeD1StackJetRead.Stack.index,
        SemiprimeD1StackPublicTransform.Stack.read SemiprimeD1StackJetRead.Stack.parser,
        SemiprimeD1StackPublicTransform.Stack.read SemiprimeD1StackJetRead.Stack.skipped,
        SemiprimeD1StackPublicTransform.Stack.read SemiprimeD1StackJetRead.Stack.output,
        SemiprimeD1StackPublicTransform.Stack.read SemiprimeD1StackJetRead.Stack.valid,
        SemiprimeD1StackPublicTransform.Stack.read SemiprimeD1StackJetRead.Stack.copy,
        SemiprimeD1StackPublicTransform.Stack.equal SemiprimeD1StackAdder.Stack.left,
        SemiprimeD1StackPublicTransform.Stack.equal SemiprimeD1StackAdder.Stack.right,
        SemiprimeD1StackPublicTransform.Stack.equal SemiprimeD1StackAdder.Stack.scratch,
        SemiprimeD1StackPublicTransform.Stack.equal SemiprimeD1StackAdder.Stack.output,
        SemiprimeD1StackPublicTransform.Stack.aux SemiprimeD1StackPublicTransform.Aux.raw,
        SemiprimeD1StackPublicTransform.Stack.aux SemiprimeD1StackPublicTransform.Aux.second,
        SemiprimeD1StackPublicTransform.Stack.aux SemiprimeD1StackPublicTransform.Aux.inverse,
        SemiprimeD1StackPublicTransform.Stack.aux SemiprimeD1StackPublicTransform.Aux.normalizer,
        SemiprimeD1StackPublicTransform.Stack.aux SemiprimeD1StackPublicTransform.Aux.remaining,
        SemiprimeD1StackPublicTransform.Stack.aux SemiprimeD1StackPublicTransform.Aux.scratch,
        SemiprimeD1StackPublicTransform.Stack.aux SemiprimeD1StackPublicTransform.Aux.output]
/-- All204 roles are visited exactly once, as a compile-time fact only. -/
theorem roles_nodup : roles.Nodup := by decide
/-- The literal inventory has its fixed204 positions before all inputs. -/
theorem roles_length : roles.length=204 := by decide
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
original binary N, two singleton descriptor flags; raw empty. -/
def inputTemplate (bits : List Bool) (second inverse : Bool) : P.Stack→List Bool :=(P.initial bits [] second inverse).data
/-- The scope is an actual binary-ID vector; its arity is acquired by the real
record scanner rather than initialized as a cardinality/width/count answer. -/
def initial (bits : List Bool) (second inverse : Bool) (bank : List Bool) : SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackStaticTable.initial static (inputTemplate bits second inverse) bank
/-- One genuine finite machine fixed before ALL original N and descriptor values. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackStaticTable.machine static
/-- The raw-assignment slot in the input template is physically EMPTY. -/
theorem template_raw (bits : List Bool) (second inverse : Bool) : inputTemplate bits second inverse P.assignment=[] := rfl
/-- Supplying the actual physically reversed prefix reproduces exactly the
frozen original checker's input; no metadata/caches/verdict are added. -/
theorem template_raw_update (bits raw : List Bool) (second inverse : Bool) :
    Function.update (inputTemplate bits second inverse) P.assignment raw=(P.initial bits raw second inverse).data := by
  funext k
  cases k with
  | roots k=>rfl
  | aux k=>cases k <;> rfl
  | dot k=>rfl
  | multiply k=>rfl
  | inputVector k=>rfl
  | outputVector k=>rfl
  | guard k=>rfl
  | read k=>rfl
  | equal k=>rfl
/-- Complete420-role inventory: checker204, read-only template204, counter7 and DFS5. -/
theorem stack_card : Fintype.card Stack=420 := by
  rw [SemiprimeD1StackStaticTable.stack_card,SemiprimeD1StackPublicTransform.stack_card]
/-- Runtime state consists solely of finite Boolean and return-label flags. -/
theorem control_finite : Finite machine.σ :=SemiprimeD1StackStaticTable.control_finite static
end RiemannGaussian.SemiprimeD1StackPublicTransformTable
