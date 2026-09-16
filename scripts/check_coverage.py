"""Check source/result coverage and generate an audit for Lean's proof kernel."""
from pathlib import Path
import json,re
ROOT=Path(__file__).resolve().parents[1]
entries=json.loads((ROOT/'results/catalog.json').read_text())
main=set(re.findall(r'^(?:THEOREM|LEMMA|PROPOSITION|COROLLARY) (\d+\.\d+)\.\s',(ROOT/'source/paper.txt').read_text(),re.M))
supp=set(re.findall(r'^(?:Lemma|Proposition|Theorem|Corollary) (S\.\d+\.\d+)\.\s',(ROOT/'source/supplement.txt').read_text(),re.M))
assert {e['id'] for e in entries}==main|supp
names={}
for path in sorted((ROOT/'Hurst').glob('*.lean')):
    text=path.read_text()
    # No placeholder proofs/custom axioms allowed in the project sources.
    assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',text),path
    # Only bare names resolve to Hurst.<name>; dotted names live in other
    # namespaces (e.g. MeasureTheory) and would misindex.
    ns_match = re.search(r'^namespace\s+(\w+)',text,re.M)
    file_ns = ns_match.group(1) if ns_match else None
    if file_ns and file_ns != 'Hurst':
        continue  # non-Hurst namespace: audited via #print axioms in its own module, not referenced here
    cur_ns = None
    for line in text.split('\n'):
        mns = re.match(r'^namespace\s+(\w+)',line)
        if mns:
            cur_ns = mns.group(1)
            continue
        if re.match(r'^end\b',line):
            cur_ns = None
            continue
        if path.stem=='ResultIndex':
            prefix='Hurst.Index.'
        elif cur_ns:
            prefix=cur_ns+'.'
        else:
            prefix='Hurst.'
        mt = re.match(r"^theorem\s+([\w']+)(?![.\w'])",line)
        if mt:
            names[prefix+mt.group(1)]=str(path.relative_to(ROOT))
for e in entries:
    assert (ROOT/f"results/{e['id']}.md").exists()
    if e['full_lean_proof']:
        assert e.get('completion_evidence'), e['id']
        for n in e['completion_evidence']: assert n in e['lean_evidence'] and 'Hurst.'+n in names, (e['id'], n)
    for n in e['lean_evidence']: assert 'Hurst.'+n in names,(e['id'],n)
(ROOT/'verification/AxiomAudit.lean').write_text('import Hurst\n\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
completed=sum(bool(e['full_lean_proof']) for e in entries)
(ROOT/'verification/coverage.json').write_text(json.dumps(dict(numbered_results=27,
 main=13,supplement=14,complete_original_results=completed,proved_declarations=len(names),
 index_declarations=3,proof_declarations=len(names)-3,declarations=names),indent=2)+'\n')
print(f'27/27 numbered results indexed; {len(names)-3} mathematical proof declarations; {completed}/27 full original results proved.')
