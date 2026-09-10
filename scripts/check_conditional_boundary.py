"""Validate declared conditional endpoints and record their exact Lean statements.
This checks traceability, not the truth of the mathematical hypotheses.
"""
from pathlib import Path
import json,re,hashlib
ROOT=Path(__file__).resolve().parents[1]
registry=json.loads((ROOT/'verification/conditional_results.json').read_text())
coverage=json.loads((ROOT/'verification/coverage.json').read_text())
assert registry['external_literature_only_mainline_complete'] is False
assert registry['unconditional_mainline_complete'] is False
assert coverage['complete_original_results']==2
inputs={'INT-CLT','INT-VAR','INT-LONG','INT-SCALE','INT-MOM-RISK'}
records=[]
for entry in registry['results']:
 name=entry['declaration'];assert name in coverage['declarations'],name
 source=coverage['declarations'][name];path=ROOT/source;text=path.read_text()
 match=re.search(r'^theorem\s+'+re.escape(name.removeprefix('Hurst.'))+r'\b',text,re.M)
 assert match,name
 end=text.find(':= by',match.start());assert end>=0,name
 statement=text[match.start():end].rstrip()
 if entry['status']=='conditional':
  assert entry['inputs'] and entry['scope'],name
  assert any(i in ' '.join(entry['inputs']) for i in inputs),name
 records.append(dict(declaration=name,status=entry['status'],source=source,line=text[:match.start()].count('\n')+1,sha256=hashlib.sha256(path.read_bytes()).hexdigest(),lean_statement=statement,declared_inputs=entry['inputs']))
progress=json.loads((ROOT/'verification/lean_formalization_progress.json').read_text())
for module in progress['modules']:
 path=ROOT/module['path']
 assert hashlib.sha256(path.read_bytes()).hexdigest()==module['sha256'],module['path']
for q in [1,2]:
 row=next(r for r in records if r['declaration']==f'Hurst.q{q}_conditional_allfinite_minimax_mainline')
 assert f'Q{q}RawMomentBound' in row['lean_statement']
 assert 'INT-MOM-RISK' in ' '.join(row['declared_inputs'])
result=dict(date='2026-09-09',conditional_endpoints=sum(r['status']=='conditional' for r in records),discharged_endpoints=sum(r['status']=='input_discharged' for r in records),all_registered_source_hashes_match=True,external_literature_only_mainline_complete=False,warning='Exact source statements are retained. The check verifies traceability and hashes, not hypothesis truth or mathematical sufficiency for a broader paper statement.',endpoints=records)
(ROOT/'verification/conditional_boundary_audit.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
print(f"Conditional boundary: {result['conditional_endpoints']} endpoints, {result['discharged_endpoints']} discharged predecessor, all registered source hashes match.")
