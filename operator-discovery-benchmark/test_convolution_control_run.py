import unittest
import check_convolution_control_run as c


class IndependentRunArithmetic(unittest.TestCase):
    def test_factorized_actual_coefficients(self):
        a=c.factor_sequences(40)
        self.assertEqual(a['mu'][1:9],[1,-1,-1,0,-1,1,-1,0])
        self.assertEqual(a['c'][1:9],[1,-2,-2,2,-2,4,-2,-2])
        self.assertEqual(a['tau'][1:9],[1,2,2,3,2,4,2,4])
        self.assertEqual(c.convolution(a['c'],a['h']),[0,1]+[0]*39)
        self.assertEqual(c.convolution(a['c'],a['tau']),[0]+[int(c.isqrt(n)**2==n) for n in range(1,41)])

    def test_quotient_grouped_diagonal_matches_direct_every_boundary(self):
        a=c.factor_sequences(63);C=c.prefix(a['c'])
        for kind in ('h','tau'):
            g=a[kind];H,R=c.weighted_square_prefixes(g);total=0
            for T in range(64):
                if T:total+=sum(g[d]**2*C[T//d]**2 for d in range(1,T+1))
                self.assertEqual(c.grouped_diagonal_prefix(C,T,H,R),total)

    def test_full_profile_complete_dense_gram(self):
        p=c.IndependentProfiles(63)
        for X in (1,2,4,8,16):
            r=p.profile(X)
            for kind in ('h','tau'):
                for label,Y in [('parent',X),('child',2*X)]:
                    full=diag=0
                    for n in range(Y,2*Y):
                        terms=[p.atoms[kind][d]*p.C[n//d] for d in range(1,n+1)]
                        full+=sum(terms)**2;diag+=sum(v*v for v in terms)
                    b=r['grams'][kind][label]
                    self.assertEqual((b['full'],b['diagonal'],b['cross']),(full,diag,full-diag))
            self.assertEqual(r['grams']['h']['defect']['full'],-2*X)
            self.assertEqual(r['energy']['c']['defect']+r['grams']['h']['defect']['other_diagonal']+r['grams']['h']['defect']['cross'],-2*X)

    def test_features_own_child_root_cutoff_and_exact_fit(self):
        p=c.IndependentProfiles(63);table=c.independent_feature_table(p,[1,2,4,8,16])
        feature=next(f for f in c.feature_dictionary() if f['kind']=='root' and f['divisor']==2 and f['weight']=='-1/2')
        rows={r['X']:r for r in table['value']['rows']}
        self.assertEqual(rows[8]['feature_metadata'][feature['feature_id']]['divisor_at_scale'],2)
        self.assertEqual(rows[16]['feature_metadata'][feature['feature_id']]['divisor_at_scale'],4)
        terms=[{'feature_id':feature['feature_id'],'weight':'1/4'}]
        constants,observations=c.exact_refit(terms,table,[1,2,4,8],[2,3,6,12])
        program={'terms':terms,'constants':constants}
        score=c.exact_score(program,table,[1,2,4,8],[2,3,6,12])
        self.assertEqual(score['finite_failures'],0)
        self.assertEqual(score['missing_cases'],0)
        self.assertEqual(c.exact_score(program,table,[8],[17])['missing_cases'],1)
        bad=[{'feature_id':feature['feature_id'],'weight':'-1'}]
        with self.assertRaises(ValueError):c.innovation(bad,table,8)

    def test_missing_feature_does_not_break_zero_weight_semantics(self):
        p=c.IndependentProfiles(15);table=c.independent_feature_table(p,[1,2,4],work_budget=1)
        fid=c.feature_dictionary()[0]['feature_id']
        self.assertIsNone(table['value']['rows'][0]['features'][fid])
        self.assertIsNotNone(c.innovation([{'feature_id':fid,'weight':'0'}],table,1)[0])
        self.assertIsNone(c.innovation([{'feature_id':fid,'weight':'1'}],table,1)[0])

    def test_archive_requires_all_proposals_and_exact_constants(self):
        p=c.IndependentProfiles(15);table=c.independent_feature_table(p,[1,2,4])
        proposals=[];candidates=[]
        origins=[{'kind':'baseline'}]+[{'kind':'singleton','feature_id':f['feature_id'],'weight':w} for f in c.feature_dictionary() for w in ('1/4','1','4')]
        for origin in origins:
            terms=[] if origin['kind']=='baseline' else [{'feature_id':origin['feature_id'],'weight':origin['weight']}]
            constants,observations=c.exact_refit(terms,table,[1,2],[2,3])
            program={'terms':terms,'constants':constants};pid=c.digest(program)
            proposals.append({'origin':origin,'program_id':pid,'exact_program':program,'fit_observations':observations,'solver':None,'discarded':False,'alias_of':None})
            candidates.append({'program_id':pid,'program':program,'origins':[origin],'training_score':c.exact_score(program,table,[1,2],[2,3])})
        archive={'schema':1,'dictionary_sha256':c.digest(c.feature_dictionary()),'selection_used_scales':[1,2],'levels':[2,3],'global_bound_proved':False,'proposal_archive':proposals,'candidates':candidates}
        self.assertEqual(c.verify_candidate_archive(archive,table,[1,2],[2,3],use_lp=False)['candidate_count'],163)
        proposals.pop()
        with self.assertRaises(ValueError):c.verify_candidate_archive(archive,table,[1,2],[2,3],use_lp=False)

    def test_wrong_child_cutoff_and_unknown_q_promotion_rejected(self):
        p=c.IndependentProfiles(31);scales=[2,4,8]
        def sub(kind):
            return {'rows':[c.producer_profile_row(p.profile(X),X,kind) for X in scales],
                    'coefficients':p.atoms['c'],'control':p.atoms[kind],'prefix':p.C,
                    'full_divisor_diagonal':True,'global_bound_proved':False}
        value=sub('h')
        value.update(source_lookahead=31,sequence='convolution',control_kind='actual_h',shift=0,dilate=1,inverse_identity_verified=True,coefficient_bit_complexity_certified=False)
        value['actual_h_profile']=sub('h');value['tau_profile']=sub('tau')
        value['tau_minus_h_diagonal']=[{'X':X,'at_X':p.profile(X)['grams']['tau']['parent']['diagonal']-p.profile(X)['grams']['h']['parent']['diagonal'],
            'at_2X':p.profile(X)['grams']['tau']['child']['diagonal']-p.profile(X)['grams']['h']['child']['diagonal']} for X in scales]
        record={'status':'available','reason':None,'lookahead':31,'value':value,'cost':1}
        self.assertTrue(c.verify_actual_profile(record,p,scales))
        value['rows'][0]['S_2X']=value['rows'][0]['S_X']
        with self.assertRaises(ValueError):c.verify_actual_profile(record,p,scales)
        with self.assertRaises(ValueError):c.reject_promotions({'queue':[{'global_bound_proved':True}]})
        table=c.independent_feature_table(p,[2,4,8,16])
        program={'terms':[],'constants':{'2':'100'}}
        obs=c.exact_score(program,table,[2],[13])['observations'][0]
        self.assertIsNone(obs['finite_pass']);self.assertEqual(obs['reason'],'unknown_level_constant')

    def test_zero_and_nonzero_wrong_proposal_weights_rejected(self):
        table=c.independent_feature_table(c.IndependentProfiles(15),[1,2,4])
        with self.assertRaises(ValueError):c.innovation([{'feature_id':'not-in-dictionary','weight':'1'}],table,1)
        with self.assertRaises(ValueError):c.rational(0.5)

    def test_missing_work_fails_closed(self):
        p=c.IndependentProfiles(63,max_grouped_terms=1)
        with self.assertRaises(RuntimeError):p.profile(16)
        with self.assertRaises(ValueError):c.IndependentProfiles(8).profile(4)
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(FileNotFoundError):c.audit_run(directory)


if __name__=='__main__':unittest.main()
