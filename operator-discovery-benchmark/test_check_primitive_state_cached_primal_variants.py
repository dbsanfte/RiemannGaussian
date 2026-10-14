import copy
from fractions import Fraction as F
import hashlib
import time
import unittest
import check_primitive_state_cached_primal_variants as I
import test_check_primitive_state_basis_primal as fixtures


class CacheTests(unittest.TestCase):
    def fixture(self):
        source,trace=fixtures.NativeAuditTests().fixture();columns,lhs,domain,shape,offset,specs,selected=source
        mapping={m:(i,) for i,m in enumerate(domain)};columns=[{mapping[m]:q for m,q in p.items()} for p in columns];lhs={mapping[m]:q for m,q in lhs.items()};domain=list(mapping.values())
        source=(columns,lhs,domain,shape,offset,specs,selected);rebuilt=I.CORE.reconstruct(*source);assembly=rebuilt['receipt'];assembly['limits']=dict(max_operations=50000000,max_cells=4000000,max_coefficient_bits=4096)
        original=dict(columns=[[[domain.index(m),str(q)] for m,q in sorted(p.items())] for p in columns],rhs=[str(lhs.get(m,F(0))) for m in domain],monomials=[list(m) for m in domain],shape=shape,offset=offset,specs=[[k,v] for k,v in specs.items()],selected_original_indices=selected)
        expected=rebuilt['canonical_system'];ptr=[0];indices=[];values=[]
        for j in range(len(columns)):
            for i,row in enumerate(expected['rows']):
                for col,q in row:
                    if col==j:indices.append(i);values.append(q)
            ptr.append(len(indices))
        canonical=dict(format='csc-floathex-v1',shape=[len(expected['rows']),len(columns)],indptr=ptr,indices=indices,values=values,rhs=expected['rhs'],objective=expected['objective'],P='zero',cones=expected['cones'])
        cache=dict(schema='primitive-state-cached-primal-v1',original=original,canonical=canonical,assembly=assembly,parent_bindings={'completed-parent':'sha'},source_hashes={'producer.py':'sha'},**I.FLAGS)
        self.rehash(cache);trace.update(assembly=assembly,variant='qdldl_default',cache_binding={k:cache[k] for k in ('original_source_hash','canonical_cache_hash','assembly_hash')})
        trace['solver']['options']['direct_solve_method']='qdldl';trace['solver']['options_hash']=I.digest(trace['solver']['options']);trace['source_hashes']=cache['source_hashes']
        trace['cache_binding']['cache_file_hash']=hashlib.sha256(I.encoded(cache)).hexdigest()
        return cache,trace

    def rehash(self,cache):
        for key,value in [('original_source_hash',cache['original']),('canonical_cache_hash',cache['canonical']),('assembly_hash',cache['assembly'])]:cache[key]=I.digest(value)

    def test_cache_full_original_and_native_csc_independently_rebuilt(self):
        cache,trace=self.fixture();check=I.verify_cache(cache,expected_parent_assembly=cache['assembly'],expected_parent_bindings=cache['parent_bindings'])
        self.assertTrue(check['verified']);self.assertEqual((check['full_original_rows'],check['full_original_variables'],check['selected_rows']),(3,5,2))
        result=I.verify_variant_trace(trace,cache,'qdldl_default');self.assertEqual(result['trace_check']['diagnostics']['equality_max_abs'],3.);self.assertFalse(result['certified'])
        self.assertGreater(result['independent_audit_work_reserve'],result['audit_operations']+check['cache_bytes'])

    def test_rehashed_csc_alterations_do_not_hide_actual_matrix_change(self):
        for mode in ('coefficient','objective','rhs','P','cones','pointer','rowindex'):
            cache,_=self.fixture()
            if mode=='coefficient':cache['canonical']['values'][0]=(2.).hex()
            elif mode=='objective':cache['canonical']['objective'][0]=(0.).hex()
            elif mode=='rhs':cache['canonical']['rhs'][0]=(0.).hex()
            elif mode=='P':cache['canonical']['P']='nonzero'
            elif mode=='cones':cache['canonical']['cones'][1][1]=1
            elif mode=='pointer':cache['canonical']['indptr'][1]=-1
            else:cache['canonical']['indices'][0]=True
            self.rehash(cache)
            with self.subTest(mode=mode),self.assertRaises(ValueError):I.verify_cache(cache)

    def test_no_implicit_missing_original_coordinates(self):
        for mode in ('rhs','column','duplicate','rational','domain'):
            cache,_=self.fixture()
            if mode=='rhs':cache['original']['rhs'].pop()
            elif mode=='column':cache['original']['columns'].pop()
            elif mode=='duplicate':cache['original']['columns'][0].append(cache['original']['columns'][0][0])
            elif mode=='rational':cache['original']['rhs'][0]='6/1'
            else:cache['original']['monomials'][0]=[True]
            self.rehash(cache)
            with self.subTest(mode=mode),self.assertRaises(ValueError):I.verify_cache(cache)

    def test_parent_and_source_binding(self):
        cache,_=self.fixture()
        for kwargs in [dict(expected_parent_bindings={'other':'sha'}),dict(expected_source_hashes={'other.py':'sha'}),dict(expected_parent_assembly={})]:
            with self.assertRaises(ValueError):I.verify_cache(cache,**kwargs)

    def test_variant_raw_coordinates_and_option_binding(self):
        cache,trace=self.fixture()
        for mode in ('variant','cache','clipped','options'):
            changed=copy.deepcopy(trace);kwargs={}
            if mode=='variant':changed['variant']='faer_static_1e-6'
            elif mode=='cache':changed['cache_binding']['canonical_cache_hash']='changed'
            elif mode=='clipped':changed['original_vector']=list(changed['original_vector']);changed['original_vector'][1]=0.
            else:kwargs['expected_options']={'changed':True}
            with self.subTest(mode=mode),self.assertRaises(ValueError):I.verify_variant_trace(changed,cache,'qdldl_default',**kwargs)

    def test_resources_and_deadlines(self):
        cache,trace=self.fixture()
        for kwargs in [dict(max_cache_bytes=1),dict(max_operations=1),dict(max_cells=1)]:
            with self.assertRaises((ValueError,OverflowError)):I.verify_cache(cache,**kwargs)
        with self.assertRaises(TimeoutError):I.verify_cache(cache,deadline=time.monotonic()-1)
        with self.assertRaises(OverflowError):I.verify_variant_trace(trace,cache,'qdldl_default',max_operations=1)

    def test_component_hash_and_nonfinite_cache_rejected(self):
        cache,_=self.fixture();cache['canonical_cache_hash']='changed'
        with self.assertRaises(ValueError):I.verify_cache(cache)
        cache,_=self.fixture();cache['canonical']['values'][0]='inf';self.rehash(cache)
        with self.assertRaises(ValueError):I.verify_cache(cache)


if __name__=='__main__':unittest.main()
