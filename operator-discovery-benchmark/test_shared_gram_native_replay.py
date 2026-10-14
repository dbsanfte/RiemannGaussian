"""Tiny deterministic saved-support checks; no floating solver calls."""
import unittest
from unittest.mock import patch
import run_shared_gram_native_replay as R


class NativeReplay(unittest.TestCase):
 def test_saved_support_exact_separator(self):
  instance=dict(target='mu',horizon=1,lhs=[dict(m=[1,1],c='-1')],square_groups=[],relation_groups=[])
  blocks=[{'g':[[[dict(m=[1],c='1')],[]]]}]
  # y(x^2)+ and the matching diagonal slack, in fixed native variable order.
  with patch('cancellation_native_gram_dual.support_proposal',side_effect=AssertionError('no floating search')):
   result=R.replay([instance],blocks,{'g':2},[1,5])
  self.assertTrue(result['certified'],result)
  self.assertTrue(result['independent_check']['verified'])
  self.assertEqual(result['saved_support'],[1,5])
  self.assertEqual(result['constant_coordinates'],['0'])
  self.assertEqual(result['gram_duals']['g']['matrix'],[['1','0'],['0','0']])
 def test_failed_same_support_retained(self):
  instance=dict(target='mu',horizon=1,lhs=[dict(m=[1,1],c='-1')],square_groups=[],relation_groups=[])
  result=R.replay([instance],[{'g':[[[dict(m=[1],c='1')],[]]]}],{'g':2},[])
  self.assertFalse(result['certified'])
  self.assertEqual(result['status'],'uncertified')


if __name__=='__main__':unittest.main()
