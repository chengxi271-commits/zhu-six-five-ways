from pathlib import Path
import argparse,subprocess,re,json,shutil
p=argparse.ArgumentParser();p.add_argument('--lean',default=shutil.which('lean'));a=p.parse_args()
if not a.lean:p.error('Lean 4.34.1 is required; use --lean PATH')
root=Path(__file__).resolve().parents[1]
s=(root/'lean/Main.lean').read_text(encoding='utf-8')
assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',s)
names=re.findall(r'^theorem\s+(\w+)',s,re.M)
(root/'lean/Audit.lean').write_text(s+'\n'+'\n'.join('#print axioms QuinqueViae.'+n for n in names),encoding='utf-8')
version=subprocess.check_output([a.lean,'--version'],encoding='utf-8').strip();assert '4.34.1' in version
r=subprocess.run([a.lean,'-j','2',str(root/'lean/Audit.lean')],capture_output=True,text=True,encoding='utf-8',timeout=60)
(root/'evidence/lean-validation.log').write_text(r.stdout+r.stderr,encoding='utf-8')
assert r.returncode==0,r.stdout;assert 'sorryAx' not in r.stdout
deps={}
for n,d in re.findall(r"'QuinqueViae\.(\w+)' (does not depend on any axioms|depends on axioms: \[[^\]]*\])",r.stdout):deps[n]=[] if d.startswith('does not') else d.split('[',1)[1][:-1].split(', ')
assert len(deps)==len(names)
rows=[]
for n in [0,1,2,3,4,5,6,7,10,12,28]:
 ds=[d for d in range(1,n) if n%d==0];rows.append({'n':n,'proper_parts':ds,'sum':sum(ds)})
record={'version':version,'exit_code':r.returncode,'theorems':len(names),'axioms':deps,'table_rows':rows,'custom_axioms':False,'sorry':False,'threads':2}
(root/'evidence/verification.json').write_text(json.dumps(record,ensure_ascii=False,indent=2),encoding='utf-8')
print(json.dumps(record,ensure_ascii=False,indent=2))
