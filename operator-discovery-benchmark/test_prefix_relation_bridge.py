import copy
from fractions import Fraction as Q
import unittest

import prefix_relation_bridge as B


def row():
    return dict(schema='arithmetic-floor-prefix-row-v1',N=3,channel=0,
        prefix_kind='weighted_channel',lhs=[dict(kernel_argument=d,prefix_floor=3//d,
            coefficient={'op':'positive_power_sum','terms':[{'coefficient':str(d),'factors':[]}]}) for d in (1,2,3)],
        rhs={'weight':['2','-1'],'coefficient':{'op':'positive_power_sum','terms':[]}})


class PrefixBridge(unittest.TestCase):
    def test_coordinate_substitution_preserves_signed_form(self):
        matrix=[['1','1'],['1','-1']]
        inverse=B.inverse(matrix)
        relation=row();converted=B.convert_row(relation,inverse)
        self.assertTrue(B.verify_conversion(relation,inverse,converted))
        # Independent arbitrary full-prefix values: original weighted channel
        # and generated states must evaluate to the same complete linear row.
        W=[[0,Q(2),Q(-1),Q(3)],[0,Q(7),Q(4),Q(-2)]]
        V=[[sum(Q(matrix[i][j])*W[j][n] for j in range(2)) for n in range(4)] for i in range(2)]
        left=sum(t['kernel_argument']*W[0][t['prefix_floor']] for t in relation['lhs'])
        right=sum(Q(t['scalar'])*t['kernel_argument']*V[t['variable']['state']][t['variable']['argument']]
                  for t in converted['lhs'])
        self.assertEqual(left,right)

    def test_inverse_and_complete_floor_mutations_rejected(self):
        with self.assertRaises(ValueError):B.inverse([['1','1'],['2','2']])
        with self.assertRaises(ValueError):B.verify_inverse([['1','1'],['1','-1']],[['1','0'],['0','1']])
        inv=B.inverse([['1','1'],['1','-1']]);r=row();correct=B.convert_row(r,inv)
        for alteration in ('drop','prime','sign','unit'):
            bad=copy.deepcopy(correct)
            if alteration=='drop':bad['lhs'].pop()
            elif alteration=='prime':bad['lhs'][0]['variable']['kind']='explicit_prime_profile'
            elif alteration=='sign':bad['lhs'][0]['scalar']='-1/2'
            else:bad['lhs'][0]['variable']['argument']=0
            with self.assertRaises(ValueError):B.verify_conversion(r,inv,bad)

    def test_prime_profile_has_its_own_coefficient_semantics(self):
        c=B.prime_profile_contract(1)
        self.assertEqual(c['value_below_one'],'0')
        self.assertEqual(c['V_kind'],'full_generated_state_prefix')
        self.assertFalse(c['equals_complete_rough_prefix_without_domain_proof'])
        with self.assertRaises(ValueError):B.prime_profile_contract(True)


if __name__=='__main__':unittest.main()
