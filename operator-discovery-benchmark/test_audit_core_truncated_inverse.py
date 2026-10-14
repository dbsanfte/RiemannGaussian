import unittest
from audit_core_truncated_inverse import keyed_components


class ComponentKeyTests(unittest.TestCase):
    def test_distinct_enumeration_orders_match_by_actual_monomial(self):
        a=[dict(mode='U',a=0,b=0,values=['1']),dict(mode='U',a=1,b=0,values=['2']),dict(mode='U',a=0,b=2,values=['3'])]
        keys={('U',0,0),('U',1,0),('U',0,2)}
        self.assertEqual(keyed_components(a,keys),keyed_components(list(reversed(a)),keys))

    def test_missing_duplicate_and_wrong_mode_cannot_be_hidden_by_reordering(self):
        a=[dict(mode='U',a=0,b=0),dict(mode='U',a=1,b=0)]
        keys={('U',0,0),('U',1,0)}
        for bad in (a[:1],a+[a[0]],[a[0],dict(mode='V',a=1,b=0)]):
            with self.assertRaises(ValueError):keyed_components(bad,keys)


if __name__=='__main__':unittest.main()
