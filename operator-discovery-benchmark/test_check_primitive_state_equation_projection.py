import ast
import copy
from fractions import Fraction as F
import inspect
import time
import unittest
import primitive_state_equation_projection as producer
import primitive_state_exact_row_basis as basis_producer
import check_primitive_state_equation_projection as checker


class IndependentProjectionTests(unittest.TestCase):
    def fixture(self,**limits):
        columns=[{'a':F(1),'b':F(2)},{'a':F(-1),'b':F(-2)},{'a':F(3),'b':F(6)},{'a':F(-11),'b':F(-22)}]
        lhs={'a':F(5),'b':F(10)};domain=['a','b'];keep=[0,2];recipes={1:{0:F(-1)},3:{0:F(1),2:F(-4)}}
        rows,rhs,receipt=producer.project_equations(columns,lhs,domain,keep,recipes,deadline=time.monotonic()+10,**limits)
        return columns,lhs,domain,keep,recipes,rows,rhs,receipt

    def test_complete_projection_counts_and_full_solver_identity(self):
        args=self.fixture();out=checker.verify_projection(*args)
        self.assertTrue(out['projection_authorized']);self.assertTrue(out['augmented_projection_injective'])
        self.assertEqual(out['optimization_variables'],4);self.assertEqual(out['rank_computation_coordinates'],2)
        self.assertEqual(out['solver_variable_mapping'],'identity');self.assertEqual(out['counts'],args[-1]['counts'])
        self.assertFalse(out['infeasibility_proved'])

    def test_full15_recipe_declaration_independent(self):
        keep,recipes=checker.full15_recipes((366,613),1597,dict(full_child=15,full_parent=15,storage_K=15),1957)
        self.assertEqual(len(keep),1224);self.assertEqual(len(recipes),733)
        self.assertEqual(recipes[367],{366:F(-1)});self.assertEqual(recipes[1837],{1597:F(1),1717:F(-4)})
        self.assertTrue(all(i in keep for i in range(1592,1837)))
        with self.assertRaises(ValueError):checker.full15_recipes((1,1),2,dict(full_child=15,full_parent=15,storage_K=15),362)

    def test_complete_source_and_each_recipe_identity(self):
        for mode in ('recipe','source','domain','partition','cycle','float-zero-recipe'):
            args=copy.deepcopy(self.fixture())
            if mode=='recipe':args[4][1][0]=F(-2)
            elif mode=='source':args[0][3]['a']+=1
            elif mode=='domain':args[2].append('extra')
            elif mode=='partition':args[3].append(1)
            elif mode=='cycle':args[4][1]={1:F(1)}
            else:args[4][1][2]=0.0
            with self.subTest(mode=mode),self.assertRaises(ValueError):checker.verify_projection(*args)

    def test_every_projection_hash_mapping_and_dimension(self):
        original=self.fixture()
        edits=dict(monomial_domain_hash='wrong',target_hash='wrong',full_columns_hash='wrong',full_source_hash='wrong',
            projection_hash='wrong',projected_rows_hash='wrong',solver_variable_mapping='projected',solver_cone_mapping='projected',
            solver_objective_mapping='projected',target_mapping='projected',projection_use='optimization',original_columns=3,
            projected_columns=1,rows=3,retained_indices=[2,0],recipes=[])
        for key,value in edits.items():
            args=copy.deepcopy(original);args[-1][key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):checker.verify_projection(*args)
        args=copy.deepcopy(original);args[-1]['recipes'][0][0]=True
        with self.assertRaises(ValueError):checker.verify_projection(*args)
        for key in original[-1]['counts']:
            args=copy.deepcopy(original);args[-1]['counts'][key]+=1
            with self.subTest(count=key),self.assertRaises(ValueError):checker.verify_projection(*args)

    def test_projected_rows_targets_extra_and_float_coefficients(self):
        for mode in ('missing','extra','rhs','float','bool-key','zero'):
            args=copy.deepcopy(self.fixture())
            if mode=='missing':args[5][0].pop(0)
            elif mode=='extra':args[5][0][2]=F(1)
            elif mode=='rhs':args[6][0]+=1
            elif mode=='float':args[5][0][0]=1.0
            elif mode=='bool-key':args[5][0]={False:F(1),1:F(3)}
            else:args[5][0][0]=F(0)
            with self.subTest(mode=mode),self.assertRaises(ValueError):checker.verify_projection(*args)

    def test_zero_columns_and_nontrivial_label_order(self):
        columns=[{'a':F(1)},{'a':F(0)}];lhs={'b':F(1)};domain=['b','a'];keep=[0];recipes={1:{0:F(0)}}
        rows,rhs,r=producer.project_equations(columns,lhs,domain,keep,recipes,deadline=time.monotonic()+10)
        self.assertTrue(checker.verify_projection(columns,lhs,domain,keep,recipes,rows,rhs,r)['unchanged_rhs'])

    def test_unknown_never_authorizes_preprocessing_or_transfer(self):
        for limits in [dict(max_operations=1),dict(max_source_cells=1),dict(max_live_cells=1),dict(max_coefficient_bits=1),dict(max_receipt_bytes=256)]:
            args=self.fixture(**limits);out=checker.verify_projection(*args)
            self.assertFalse(out['projection_authorized']);self.assertFalse(out['row_basis_transfer_authorized'])
            args=list(args);args[5]=[];args[6]=[]
            with self.assertRaises(ValueError):checker.verify_projection(*args)

    def test_independent_limits_and_flags(self):
        args=self.fixture()
        for limits in [dict(max_audit_operations=1),dict(max_audit_cells=1),dict(max_coefficient_bits=1),dict(max_receipt_bytes=256)]:
            with self.assertRaises((ValueError,OverflowError)):checker.verify_projection(*args,**limits)
        with self.assertRaises(TimeoutError):checker.verify_projection(*args,deadline=time.monotonic()-1)
        args=self.fixture();args[-1]['global_bound_proved']=True
        with self.assertRaises(ValueError):checker.verify_projection(*args)
        args=self.fixture();args[-1]['limits']['max_operations']=450000001
        with self.assertRaises(ValueError):checker.verify_projection(*args)

    def test_basis_transfer_selects_full_equations_not_projected_variables(self):
        args=self.fixture();columns,lhs,domain,keep,recipes,rows,rhs,projection=args
        selected,targets,basis=basis_producer.reduce_rows(rows,rhs,len(keep),deadline=time.monotonic()+10)
        indices=basis['retained_indices'];full=[{j:p[domain[i]] for j,p in enumerate(columns)} for i in indices]
        out=checker.verify_projection_basis(*args,selected,targets,basis,selected_full_rows=full,selected_full_rhs=targets)
        self.assertEqual(out['original_equation_indices'],[0]);self.assertEqual(out['optimization_variables'],4)
        self.assertTrue(out['reduction_authorized']);self.assertFalse(out['exact_admission'])
        with self.assertRaises(ValueError):checker.verify_projection_basis(*args,selected,targets,basis,selected_full_rows=selected,selected_full_rhs=targets)
        full[0][0]=1.0
        with self.assertRaises(ValueError):checker.verify_projection_basis(*args,selected,targets,basis,selected_full_rows=full,selected_full_rhs=targets)

    def test_augmented_inconsistency_transfers_and_unknown_basis_does_not(self):
        args=self.fixture();args[1]['b']=F(11)
        args=list(args);args[5],args[6],args[7]=producer.project_equations(*args[:5],deadline=time.monotonic()+10)
        selected,targets,basis=basis_producer.reduce_rows(args[5],args[6],len(args[3]),deadline=time.monotonic()+10)
        out=checker.verify_projection_basis(*args,selected,targets,basis)
        self.assertEqual(len(out['original_equation_indices']),2);self.assertTrue(out['basis']['inconsistent_augmented_pivots'])
        selected,targets,basis=basis_producer.reduce_rows(args[5],args[6],len(args[3]),deadline=time.monotonic()+10,max_operations=1)
        out=checker.verify_projection_basis(*args,selected,targets,basis)
        self.assertFalse(out['reduction_authorized']);self.assertIn('independent_audit_work_reserve',out)
        with self.assertRaises(ValueError):checker.verify_projection_basis(*args,selected,targets,basis,selected_full_rows=[],selected_full_rhs=[])

    def test_checker_imports_no_producers_or_numerical_solvers(self):
        modules=[]
        for node in ast.walk(ast.parse(inspect.getsource(checker))):
            if isinstance(node,ast.Import):modules.extend(n.name for n in node.names)
            elif isinstance(node,ast.ImportFrom):modules.append(node.module)
        self.assertFalse(any(name in modules for name in ['primitive_state_equation_projection','primitive_state_exact_row_basis','numpy','scipy','cvxpy','clarabel']))

if __name__=='__main__':unittest.main()
