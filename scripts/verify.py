"""Build, audit standard axioms, and kernel-replay the library and its tests.

A full verification starts without project build artifacts. Dependencies may use
Mathlib's official binary cache. Build-only mode supports selected module groups.
"""
from pathlib import Path
import argparse, concurrent.futures, csv, json, os, re, subprocess, time
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--build-only',action='store_true')
p.add_argument('--targets',nargs='*')
p.add_argument('--workers',type=int,default=2)
a=p.parse_args()
root=Path(__file__).resolve().parents[1]
os.chdir(root)
threads=max(1,min(8,int(os.environ.get('LEAN_NUM_THREADS','4'))))
workers=max(1,min(2,a.workers))
os.environ['LEAN_NUM_THREADS']=str(threads)
out=root/'verification-output';out.mkdir(exist_ok=True)
modules={r['module']:r['file'] for r in csv.DictReader((root/'MODULES.tsv').open(),delimiter='\t')}
for f in sorted([*(root/'Tests').rglob('*.lean'), *(root/'Challenge').rglob('*.lean'), root/'Challenge.lean',root/'Solution.lean']):
 modules[str(f.relative_to(root)).removesuffix('.lean').replace('/','.')]=str(f.relative_to(root))
deps={n:{d for d in re.findall(r'^import (\S+)',(root/f).read_text(),re.M) if d in modules} for n,f in modules.items()}
for n,f in modules.items():
 for d in re.findall(r'^import (\S+)',(root/f).read_text(),re.M):
  assert not d.startswith(('RMTFoundations','Tests','Challenge','Solution')) or d in modules,('unlisted dependency',n,d)
selected=set()
def visit(n):
 assert n in modules,('unknown target',n)
 if n in selected:return
 selected.add(n)
 for d in deps[n]:visit(d)
for n in a.targets or sorted(modules):visit(n)
if not a.build_only:
 assert selected==set(modules),'full verification requires every module'
 assert not (root/'.lake/build').exists(),'full verification requires a cold project build'
subprocess.run(['python3','scripts/check_source.py'],check=True)
pending=set(selected);finished=set();running={};records=[]
buildlogs=out/'build';buildlogs.mkdir(exist_ok=True)
def build(n):
 begin=time.monotonic()
 with (buildlogs/(n+'.log')).open('w') as f:
  r=subprocess.run(['lake','build',n],stdout=f,stderr=subprocess.STDOUT,env=dict(os.environ,LEAN_NUM_THREADS=str(threads)))
 return dict(module=n,exit_code=r.returncode,seconds=time.monotonic()-begin)
with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
 while pending or running:
  ready=sorted(n for n in pending if deps[n]<=finished)
  limit=workers if finished else 1
  for n in ready[:max(0,limit-len(running))]:
   pending.remove(n);running[pool.submit(build,n)]=n
   print('BUILD_START '+n,flush=True)
  assert running,('dependency cycle',sorted(pending))
  done,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
  for future in done:
   n=running.pop(future);record=future.result();records.append(record)
   assert record['exit_code']==0,('build failed',n,record['exit_code'])
   finished.add(n);print('BUILD_PASS '+n,flush=True)
(out/'BUILD.json').write_text(json.dumps(records,indent=2)+'\n')
if a.build_only:
 print('SCRATCH_PASS',len(finished),flush=True);raise SystemExit(0)
for f in sorted((root/'examples').rglob('*.lean')):
 with (out/(f.stem+'.log')).open('w') as log:
  subprocess.run(['lake','env','lean',f'-j{threads}',str(f.relative_to(root))],stdout=log,stderr=subprocess.STDOUT,check=True)
 print('EXAMPLE_PASS '+f.stem,flush=True)
with (out/'axiom-output.log').open('wb') as log:
 for f in sorted(buildlogs.glob('*.log')):log.write(f.read_bytes())
subprocess.run(['python3','scripts/check_axioms.py',str(out/'axiom-output.log')],check=True)
umbrellas={'RMTFoundations','Challenge','Solution'}
for n in sorted(umbrellas):
 assert all(not l.strip() or l.startswith('import ') for l in (root/modules[n]).read_text().splitlines()),('umbrella contains declarations',n)
replay=sorted(set(modules)-umbrellas)
checker=out/'checker';checker.mkdir(exist_ok=True)
def check(n):
 begin=time.monotonic()
 with (checker/(n+'.log')).open('w') as log:
  r=subprocess.run(['lake','env','leanchecker','-v',n],stdout=log,stderr=subprocess.STDOUT,env=dict(os.environ,LEAN_NUM_THREADS='1'))
 selected_names=[l[len('replaying '):] for l in (checker/(n+'.log')).read_text().splitlines() if l.startswith('replaying ')]
 assert selected_names==[n],('kernel selector scope',n,selected_names)
 print(('CHECKER_PASS ' if r.returncode==0 else 'CHECKER_FAIL ')+n,flush=True)
 return dict(module=n,exit_code=r.returncode,seconds=time.monotonic()-begin,lean_num_threads=1)
replay_workers=min(4,max(1,int(os.environ.get('SLURM_CPUS_PER_TASK',str(threads)))))
with concurrent.futures.ThreadPoolExecutor(max_workers=replay_workers) as pool:results=list(pool.map(check,replay))
(out/'REPLAY.json').write_text(json.dumps(results,indent=2)+'\n')
assert {r['module'] for r in results}==set(replay)
assert all(r['exit_code']==0 for r in results),'kernel replay failure'
print('FULL_GATE_PASS',len(modules),'modules;',len(replay),'kernel selectors',flush=True)
print('EXIT=0',flush=True)
