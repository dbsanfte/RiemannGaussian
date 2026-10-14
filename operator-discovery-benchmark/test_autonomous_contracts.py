"""Public language contracts, separate from answer-free candidate discovery."""
import unittest
from fractions import Fraction as Q

from autonomous_grammar import (Gaussian, decode, digest, encode, evaluate, infer,
                                polynomial_certificate)


class FiniteLanguageContracts(unittest.TestCase):
    def setUp(self):
        self.x = [Gaussian(Q(2, 3), Q(-1)), Gaussian(Q(-3), Q(2, 5)), Gaussian(Q(4), Q(1, 7))]
        self.y = [Q(-5, 3), Q(2), Q(7, 4)]
        self.identity = ["kernel", ["indicator", ["eq", ["v", "n"], ["v", "i"]]]]
        self.prefix = ["kernel", ["indicator", ["le", ["v", "i"], ["v", "n"]]]]

    def run_program(self, p, **kwargs):
        return [encode(x) for x in evaluate(p, [self.x, self.y], **kwargs)[0]]

    def test_exact_complex_matrix_composition_and_inverse(self):
        p = ["apply", ["mcompose", ["minverse", self.prefix], self.prefix], ["input", 0]]
        self.assertEqual(self.run_program(p), [encode(x) for x in self.x])

    def test_nonlinear_complex_product_and_conjugate_norm_are_distinct(self):
        product = self.run_program(["point", ["input", 0], ["input", 0]])
        norms = self.run_program(["norm2", ["input", 0]])
        self.assertNotEqual(product, norms)
        self.assertEqual(norms[0], encode(Q(4, 9) + 1))

    def test_bounded_sum_empty_and_clamped_domains(self):
        empty = ["tab", ["bsum", "j", ["int", -1], ["embed", ["v", "j"]]]]
        clamped = ["tab", ["bsum", "j", ["int", 100], ["embed", ["v", "j"]]]]
        self.assertEqual(self.run_program(empty), [encode(0)] * 3)
        self.assertEqual(self.run_program(clamped), [encode(6)] * 3)

    def test_free_index_macro_preserves_binding(self):
        body = ["iq", ["v", "n"], ["v", "i"]]; key = digest(body)
        macros = {key: {"body": body, "type": "index", "free_indices": ["n", "i"]}}
        compressed = ["apply", ["kernel", ["embed", ["macro", key]]], ["input", 0]]
        original = ["apply", ["kernel", ["embed", body]], ["input", 0]]
        self.assertEqual(self.run_program(compressed, macros=macros), self.run_program(original))

    def test_domain_failures_remain_explicit(self):
        cases = [(["apply", ["minverse", ["kernel", ["q", 0, 1]]], ["input", 0]], {}),
                 (["apply", self.identity, ["input", 0]], {"operations": 1}),
                 (["apply", ["minverse", self.identity], ["input", 0]], {"inverse_max": 2}),
                 (["tab", ["embed", ["iq", ["v", "n"], ["int", 0]]]], {})]
        for p, kwargs in cases:
            with self.subTest(program=p), self.assertRaises(ValueError): self.run_program(p, **kwargs)

    def test_invalid_types_scopes_and_rational_inputs(self):
        for p in (["input", True], ["input", 2], ["tab", ["embed", ["v", "i"]]],
                  ["apply", ["input", 0], ["input", 1]], ["q", 1, 0],
                  ["tab", ["bsum", "j", ["v", "n"], ["bsum", "j", ["v", "n"], ["q", 1, 1]]]]):
            with self.subTest(program=p), self.assertRaises(ValueError): infer(p)
        with self.assertRaises(ValueError): decode([1, True, 0, 1])

    def test_certificate_support_is_separate_from_numerical_validity(self):
        p = ["add", ["point", ["input", 0], ["input", 1]],
             ["scale", ["q", -1, 1], ["point", ["input", 1], ["input", 0]]]]
        c = polynomial_certificate(p)
        self.assertEqual(c["normal_form"], [])
        self.assertFalse(c["analytic_claim"])
        unsupported = polynomial_certificate(["apply", self.prefix, ["input", 0]])
        self.assertEqual(unsupported["status"], "unsupported")
        self.assertEqual(len(self.run_program(["apply", self.prefix, ["input", 0]])), 3)


if __name__ == "__main__": unittest.main()
