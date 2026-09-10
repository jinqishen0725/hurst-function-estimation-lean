from pathlib import Path
import json,re,hashlib
mods=Path('.scratch/batch28_modules.txt').read_text().split()
p=Path('Hurst.lean');text=p.read_text()
for m in mods:
 if f'import Hurst.{m}\n' not in text:text+=f'import Hurst.{m}\n'
p.write_text(text)
remaining='Conditional implications connected under explicit delayed supporting premises. INT-CLT, INT-VAR, INT-LONG, INT-SCALE, INT-MOM-RISK remain where listed. INT-MOM-RISK is an internal actual-model bound, not EXT-MOM; its derivation from EXT-MOM is still unformalized. Unconditional paper coverage remains 2/27.'
p=Path('verification/lean_formalization_progress.json');j=json.loads(p.read_text());ns=[]
for m in mods:
 f=Path('Hurst')/(m+'.lean');names=['Hurst.'+n for n in re.findall(r'^theorem\s+(\w+)',f.read_text(),re.M)];ns+=names
 j['modules']=[x for x in j['modules'] if x['path']!=str(f)]
 wp=['19'] if any(v in m for v in ['Moment','Minimax','FiniteRisk']) else ['11','13','14','15','21']
 j['modules'].append(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),declarations=names,written_proofs=wp,remaining=remaining))
assert len(ns)==70,len(ns)
j.update(date='2026-09-09',latest_batch=28,latest_batch_new_mathematical_declarations=70,mainline_complete=False,conditional_supporting_lemma_mainline_complete=True,external_literature_only_mainline_complete=False,phase='Conditional downstream mainline complete under the explicit external and internal supporting-premise boundary; discharging internal inputs and the EXT-MOM bridge remains.')
j['batches']=[x for x in j['batches'] if x['batch']!=28]+[dict(batch=28,new_mathematical_declarations=70,declarations=ns,description=remaining)]
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
count=sum(len(re.findall(r'^theorem\s+',f.read_text(),re.M)) for f in Path('Hurst').glob('*.lean'))-3
assert count==1152,count
p=Path('verification/conditional_results.json');c=json.loads(p.read_text())
c.update(date='2026-09-09',conditional_mainline_complete=True,completion_boundary='Explicit external AND internal delayed supporting lemmas, in the parameter and bandwidth regimes of the listed Lean endpoints.',external_literature_only_mainline_complete=False,unconditional_mainline_complete=False,note=remaining)
c['not_yet_closed_conditionally']=[]
c['not_yet_discharged']=['INT-CLT: finite Hermite polynomial triangular-array limits, including joined pilot indices','INT-VAR: actual variance limits and weighted fourth-correlation/mean/second-moment smallness in memory branches','INT-LONG: actual quadratic-statistic to second-chaos limit','INT-SCALE: q2 optimal-bandwidth and memory-branch scale L1 smallness','INT-MOM-RISK: actual uniform calibrated raw moments; EXT-MOM to this bound is not formalized']
c['results']=[x for x in c['results'] if x['status']=='input_discharged']
def add(name,ids,inputs,scope,proofs):
 c['results'].append(dict(declaration='Hurst.'+name,status='conditional',original_results=ids,inputs=inputs,scope=scope,written_proofs=proofs))
for q in [1,2]:
 scope=('q1,p=r+1>=1,0<a<=H<=b<3/4' if q==1 else 'q2,p=r+1>=2,0<a<=H<=b<u<1')+', H is C^p, fixed interior t, literal optimal bandwidth, any common nonzero scale'
 add(f'hurstHolder_q{q}_conditional_all_scale_short_mainline',['3.3','3.4','3.5','4.3'],['INT-CLT','INT-VAR']+(['INT-SCALE'] if q==2 else []),scope,['11','13','21'])
 add(f'hurstHolder_q{q}_conditional_raw_optimal_CLT',['3.3','3.5'],['INT-CLT','INT-VAR'],scope+'; raw calibrated log statistic, limit mean -2R',['11','13'])
 add(f'hurstHolder_q{q}_conditional_all_scale_pilot_CLT',['4.1'],['INT-CLT: joined two-scale polynomial statistic','INT-VAR: joined correlation-square row bound, normalized weight energy and variance limit'],('q1,p>=1' if q==1 else 'q2,p>=2')+', actual grid, arbitrary bandwidth/normalization satisfying explicit inputs, any nonzero scale',['15'])
 add(f'q{q}_conditional_allfinite_minimax_mainline',['3.1','3.2','3.4','4.3'],[f'INT-MOM-RISK: Q{q}RawMomentBound (used only when s>2)'],('q1,p>=1,0<a<1/2<b<3/4' if q==1 else 'q2,p>=2,0<a<1/2<b<1')+', M>0, fixed finite s>=1, whole (0,1), same fixed-range class, known and unknown nonzero scale',['18','19','20'])
for branch in ['critical','long']:
 add(f'hurstHolder_q1_conditional_all_scale_{branch}_mainline',['3.3','3.4','4.3'],[('INT-CLT: actual quadratic Gaussian limit' if branch=='critical' else 'INT-LONG: actual quadratic limit Q'),'INT-VAR: weighted fourth-correlation double sum, normalized raw mean and second-moment smallness','INT-SCALE: two-bandwidth scale L1 smallness'],'q1,p>=1,0<a<=H<=b<1, interior t, '+('H(t)=3/4' if branch=='critical' else 'H(t)>3/4')+', positive bandwidths tending to zero with n*bandwidth tending to infinity; additional stated weighted moment/smallness inputs; any nonzero scale',['13','14','21'])
add('hurstHolder_q1_conditional_all_scale_memory_mainline',['3.3','3.4','4.3'],['INT-LONG or INT-CLT: actual quadratic limit Z','INT-VAR: weighted fourth-correlation energy and normalized raw moments','INT-SCALE'],'q1,p>=1,0<a<=H<=b<1, interior t, explicit two-bandwidth hypotheses; general finite bias beta; estimator limit -Z-beta; any nonzero scale',['13','14','21'])
add('hurstHolder_q1_conditional_all_scale_pilot_memory_limit',['4.1'],['INT-LONG or INT-CLT: joined quadratic limit','INT-VAR: joined weighted fourth-correlation energy smallness'],'actual q1 two-scale joined pilot, explicit normalization and weighted conditions, any nonzero scale',['14','15'])
add('hurstHolder_q2_unknown_scale_expected_bias_of_scale_L1',['3.4','4.3'],['INT-SCALE: E|actual q2 scale estimator|/(log n * delta^p) tends to zero'],'q2,p=r+1>=2,C^p,interior t,literal optimal bandwidth,0<a<=H<=b<u<1,any unknown nonzero scale',['21'])
p.write_text(json.dumps(c,indent=2,ensure_ascii=False)+'\n')
p=Path('scripts/repair_updates.json');u=json.loads(p.read_text())
for key in ['3.1','3.2','3.3','3.4','3.5','4.1','4.3']:
 e=u[key]
 evidence=[x['declaration'].removeprefix('Hurst.') for x in c['results'] if key in x.get('original_results',[])]
 e['evidence_add']=list(dict.fromkeys(e.get('evidence_add',[])+evidence))
 note=' 第二十八阶段已接通所列一维范围的显式支撑前提 Lean 链，见 conditional_mainline_summary.md。有限多项式 CLT、实际方差/长记忆/尺度小量和实际高阶矩输入仍按条件登记保留；不是全部原定理无条件完成。'
 if note not in e.get('repair_status',''):e['repair_status']=e.get('repair_status','')+note
 if key!='3.1': e['remaining']='消除 conditional_results.json 为本结果列出的内部/外部支撑前提，及原范围超出固定一维核/参数/带宽版本的部分。s>2 目前依赖实际 QRawMomentBound，其从 EXT-MOM 的桥接尚未形式化。'
p.write_text(json.dumps(u,indent=2,ensure_ascii=False)+'\n')
print('Registered',len(mods),'modules;',len(ns),'new declarations;',count,'mathematical declarations total.')
