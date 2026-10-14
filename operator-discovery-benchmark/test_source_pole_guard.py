import unittest

import source_pole_guard as P


def atom(kind,shift):return dict(kind=kind,shift=shift)


def source():
    # Synthetic shifted source, with a hidden affine calibration to derive.
    return dict(lattice=5,channels=[
        dict(atoms=[atom('power',2),atom('mu',0)],weight=['3','0']),
        dict(atoms=[atom('power',2)],weight=['0','-2'])])


class NormalizationDiscovery(unittest.TestCase):
    def test_parameter_binding_is_derived_from_different_source(self):
        result=P.inspect(source());pole=result['positive_poles'][0]
        self.assertEqual(pole['point'],'3/5')
        self.assertEqual(pole['cancellation']['laurent_solution'],
                         [dict(coefficient='3/2',powers=[['3/5',-1]])])
        self.assertEqual(result['initial_abscissa'],'1')

    def test_local_equal_factor_cancels_before_pole_analysis(self):
        s=source();s['channels'][0]['atoms'].append(atom('mu',2))
        result=P.inspect(s)
        self.assertEqual(result['positive_poles'][0]['channel_orders'],[0,1])
        self.assertEqual(result['positive_poles'][0]['cancellation']['laurent_solution'],[])

    def test_higher_order_pole_is_explicitly_unsupported(self):
        s=source();s['channels'][0]['atoms'].append(atom('power',2))
        result=P.inspect(s)['positive_poles'][0]
        self.assertEqual(result['status'],'higher_order_unsupported')
        self.assertNotIn('residue',result)

    def test_arbitrary_fraction_and_nonpositive_gate(self):
        s=source();s['lattice']=257
        self.assertEqual(P.inspect(s)['positive_poles'][0]['point'],'255/257')
        s=source();s['channels'][0]['atoms'].append(atom('mu',-5))
        result=P.inspect(s)
        self.assertEqual(result['initial_abscissa'],'2')
        self.assertEqual(result['positive_poles'][0]['status'],'nonpositive_regular_argument_unsupported')

    def test_no_parameter_cannot_silently_cancel_a_pole(self):
        s=source();s['channels']=s['channels'][:1]
        pole=P.inspect(s)['positive_poles'][0]
        self.assertTrue(pole['residue']['constant'])
        self.assertEqual(pole['residue']['R'],[])
        self.assertIsNone(pole['cancellation']['laurent_solution'])


if __name__=='__main__':unittest.main()
