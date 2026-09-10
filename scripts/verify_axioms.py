from pathlib import Path
import json,re
ROOT=Path(__file__).resolve().parents[1]
coverage=json.loads((ROOT/'verification/coverage.json').read_text())
text=(ROOT/'verification/axioms.log').read_text()
assert 'error:' not in text,text
assert 'sorryAx' not in text
allowed={'propext','Classical.choice','Quot.sound'}
for name in coverage['declarations']:
    assert "'"+name+"'" in text,name
for block in re.findall(r'depends on axioms:\s*\[([^]]*)\]',text,re.S):
    names={x.strip() for x in block.split(',') if x.strip()}
    assert names<=allowed,names-allowed
assert 'Build completed successfully' in (ROOT/'verification/build.log').read_text()
result=dict(declarations_checked=coverage['proved_declarations'],
 allowed_foundation_axioms=sorted(allowed),sorryAx=False,custom_axioms=False,build_passed=True,
 complete_original_results=coverage['complete_original_results'])
(ROOT/'verification/audit_result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
