#!/usr/bin/env python3
"""Focused compiler/verifier controls; no contraction or factoring campaign."""
import argparse
import json
from pathlib import Path
import unittest
from factor_network import compile, bits, unpack, dft


def pack(values,widths):
    return tuple(bit for value,width in zip(values,widths) for bit in bits(value,width))


class CompilerControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.net=compile(15)
        cls.witness=cls.net.witness(3,5)

    def test_exact_port_wiring_and_bipartition(self):
        net=self.net
        self.assertTrue(self.witness['valid'])
        self.assertEqual(sum(len(v.ports) for v in net.vertices),2*len(net.edges))
        seen=set()
        for edge_id,edge in enumerate(net.edges):
            self.assertEqual(len(edge.ends),2)
            sides=[]
            for vid,pos in edge.ends:
                self.assertNotIn((vid,pos),seen);seen.add((vid,pos))
                self.assertEqual(net.vertices[vid].ports[pos],edge_id)
                sides.append(net.vertices[vid].side)
            self.assertEqual(sorted(sides),[0,1])
        self.assertEqual(len(seen),sum(len(v.ports) for v in net.vertices))
        self.assertEqual(len(net.input_bits['P']),net.parameters['L'])

    def test_canonical_invalid_ring_encoding_rejected(self):
        net=self.net
        vertex=next(v for v in net.vertices if v.kind=='dft')
        local=tuple(self.witness['assignment'][e] for e in vertex.ports)
        values=unpack(local,vertex.widths)
        ins=values[:vertex.inputs];ins[0]=vertex.params['modulus']
        # Even choose outputs consistent with reduction modR: invalid input
        # must still be rejected because representation is noncanonical.
        outs=dft(ins,vertex.params['root'],vertex.params['modulus'],vertex.params['normalizer'])
        self.assertEqual(vertex.entry(pack(ins+outs,vertex.widths)),0)
        self.assertEqual(vertex.entry(local),1)

    def test_carry_is_integer_not_ring_congruence(self):
        vertex=next(v for v in self.net.vertices if v.kind=='carry' and v.params['digit']==0)
        M=vertex.params['modulus']
        self.assertEqual(vertex.entry(pack([0,0,0],vertex.widths)),1)
        self.assertEqual(((M-1)+1)%M,0)
        self.assertEqual(vertex.entry(pack([M-1,1,0],vertex.widths)),0)

    def test_supplied_witnesses_trivial_and_invalid_inputs(self):
        for P,Q,expected in ((3,5,True),(5,3,True),(3,7,False),
                             (1,15,False),(0,15,False),(19,5,False),(-3,-5,False)):
            with self.subTest(P=P,Q=Q):
                self.assertEqual(self.net.witness(P,Q)['valid'],expected)

    def test_square_and_unequal_fft_axis_controls(self):
        square=compile(49)
        self.assertTrue(square.witness(7,7)['valid'])
        other=compile(21)
        self.assertTrue(other.witness(3,7)['valid'])
        self.assertNotEqual(self.net.parameters['r'],self.net.parameters['t'])
        self.assertEqual(other.parameters['r'],other.parameters['t'])

    def test_prefix_restriction_without_new_edges(self):
        edge=self.net.input_bits['P'][0]
        keep=self.net.restrict({edge:1})
        reject=self.net.restrict({edge:0})
        self.assertEqual(len(keep.edges),len(self.net.edges))
        self.assertEqual(len(reject.vertices),len(self.net.vertices))
        self.assertTrue(keep.witness(3,5)['valid'])
        self.assertFalse(reject.witness(3,5)['valid'])

    def test_subdivision_equality_detects_bad_half(self):
        assignment=list(self.witness['assignment']);assignment[0]^=1
        equality=self.net.edges[0].ends[1][0]
        result=self.net.validate(assignment)
        self.assertFalse(result['valid'])
        self.assertIn(equality,result['failed_vertices'])

    def test_inverse_transform_coefficients_are_integer_convolution(self):
        net=compile(21);w=net.witness(3,7);par=net.parameters
        Pdigits=[(3>>(par['b']*i))&((1<<par['b'])-1) for i in range(par['d'])]
        Qdigits=[(7>>(par['b']*i))&((1<<par['b'])-1) for i in range(par['d'])]
        coefficients=[0]*par['nfft']
        for i,a in enumerate(Pdigits):
            for j,b in enumerate(Qdigits):coefficients[i+j]+=a*b
        actual=[]
        for vertex in net.vertices:
            if vertex.kind=='carry':
                local=tuple(w['assignment'][e] for e in vertex.ports)
                actual.append(unpack(local,vertex.widths)[0])
        self.assertEqual(actual,coefficients)

    def test_principal_root_roundtrip_over_composite_auxiliary_ring(self):
        n=32;M=(1<<n)+1
        self.assertEqual(M,641*6700417)
        values=[i*i+7*i for i in range(n)]
        transformed=dft(values,4,M)
        recovered=dft(transformed,pow(4,-1,M),M,pow(n,-1,M))
        self.assertEqual(recovered,values)

    def test_public_count_and_degree_bounds(self):
        for N in (15,21,49):
            stats=compile(N).statistics()
            for key in ('edges_le_100_nfft_squared','edges_le_6400_L',
                        'degree_fourth_power_bound','D1_degree_bound'):
                self.assertTrue(stats[key],(N,key))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('factor-network-validation.json'))
    args=parser.parse_args()
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(CompilerControls)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    output=dict(status='PASS' if result.wasSuccessful() else 'FAIL',
                tests=result.testsRun,failures=len(result.failures),errors=len(result.errors),
                scope='compiler/verifier structural controls; no contraction or factoring search')
    args.output.write_text(json.dumps(output,indent=2)+'\n')
    raise SystemExit(not result.wasSuccessful())
