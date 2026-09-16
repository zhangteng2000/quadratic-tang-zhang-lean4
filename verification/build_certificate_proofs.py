"""Generate and kernel-check certificate chunks with bounded process concurrency.

Every chunk uses `decide +kernel`; native_decide and external verification
results do not enter the proof. Existing successful Lake targets are reused.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
import subprocess
import time
import os
import json
import hashlib
import argparse

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--workers',type=int,default=2)
parser.add_argument('--generate-only',action='store_true')
parser.add_argument('--dry-run',action='store_true')
args=parser.parse_args()
assert args.workers>0

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'QuadraticTangZhang' / 'Certificate'
LOG = ROOT / 'verification' / 'certificate-kernel'
LOG.mkdir(exist_ok=True)
raw=(ROOT/'verification'/'certificate.json').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='8384d62a377b4fcac4080d0e05979d7a6fcf90437b7e4911927a5403d4052709'
doc = json.loads(raw)
tags={'direct':0,'center-monotone':1,'center-cubic':2,'boundary':3}
light_chunks=set(range(18,37))
tagged_chunks=light_chunks-{33,34}
changed=[]
def save(target,data):
    if not target.exists() or target.read_text(encoding='utf-8')!=data:
        changed.append(str(target.relative_to(ROOT)))
        if not args.dry_run:
            target.parent.mkdir(exist_ok=True)
            target.write_text(data,encoding='utf-8')

kdata=['import QuadraticTangZhang.CertificateKernel.Compute','namespace QuadraticTangZhangKernel','']
for i,(ml,mh,al,ah,h,tag,sub) in enumerate(doc['records']):
    kdata.append(f'def record_{i:04d} : CertificateRecord := decodeRecord {ml} {mh} {al} {ah} {h} {tags[tag]} {sub}')
kdata+=['end QuadraticTangZhangKernel','']
save(ROOT/'QuadraticTangZhang/CertificateKernel/Data.lean','\n'.join(kdata))
groups=[]
for i,row in enumerate(doc['records']):
    if not groups or groups[-1][0] != tuple(row[:2]): groups.append((tuple(row[:2]),[]))
    groups[-1][1].append(i)
assert len(groups)==430
chunks=[]
for c in range(43):
    name=f'Checked{c:02d}'
    chunks.append(name)
    imports=['import QuadraticTangZhang.Certificate.Data']
    if c in light_chunks:
        imports += ['import QuadraticTangZhang.CertificateKernel.Bridge',
                    f'import QuadraticTangZhang.CertificateKernel.{name}']
        kimports=['import QuadraticTangZhang.CertificateKernel.Data']
        if c in tagged_chunks:
            kimports.append('import QuadraticTangZhang.CertificateKernel.Tagged')
        klines=kimports+['set_option maxRecDepth 100000',
                'set_option maxHeartbeats 0','set_option Elab.async false','namespace QuadraticTangZhangKernel','']
        indices=[i for _,group in groups[c*10:(c+1)*10] for i in group]
        for i in indices:
            kproof='  exact tagged_checked _ (by decide +kernel)' if c in tagged_chunks else '  decide +kernel'
            klines += [f'theorem record_{i:04d}_checked : verifyStandardRecord record_{i:04d}=true := by',
                       kproof,'']
        klines += [f'#print axioms record_{indices[-1]:04d}_checked','end QuadraticTangZhangKernel','']
        save(ROOT/f'QuadraticTangZhang/CertificateKernel/{name}.lean','\n'.join(klines))
    lines=imports+['set_option maxRecDepth 100000',
           'set_option maxHeartbeats 0','set_option Elab.async false',
           'namespace QuadraticTangZhang.CertificateData','']
    for j in range(c*10,(c+1)*10):
        for i in groups[j][1]:
            proof='  decide +kernel'
            if c in light_chunks:
                ml,mh,al,ah,h,tag,sub=doc['records'][i]
                proof=f'  exact kernel_checked_record {ml} {mh} {al} {ah} {h} {tags[tag]} {sub} QuadraticTangZhangKernel.record_{i:04d}_checked'
            lines.extend([f'theorem record_{i:04d}_checked : verifyStandardRecord record_{i:04d}=true := by',
                          proof,''])
        names=', '.join(f'record_{i:04d}_checked' for i in groups[j][1])
        lines.extend([f'theorem block_{j:03d}_checked : block_{j:03d}.records.all verifyStandardRecord=true := by',
                      f'  simp only [block_{j:03d}, List.all_cons, List.all_nil, {names}, Bool.and_self]',
                      f'#print axioms block_{j:03d}_checked',''])
    lines+=['end QuadraticTangZhang.CertificateData','']
    target=OUT/(name+'.lean')
    data='\n'.join(lines)
    save(target,data)

print(json.dumps({'changed_sources':changed,'dry_run':args.dry_run}),flush=True)
if args.dry_run or args.generate_only:
    raise SystemExit(0)

start=time.monotonic()
env=dict(os.environ,LEAN_NUM_THREADS='2')
def build(name):
    t=time.monotonic()
    with (LOG/(name+'.log')).open('w',encoding='utf-8') as log:
        run=subprocess.run(['lake','build','QuadraticTangZhang.Certificate.'+name],
            cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT,
            creationflags=getattr(subprocess,'CREATE_NO_WINDOW',0))
    result={'module':name,'returncode':run.returncode,'seconds':round(time.monotonic()-t,2)}
    print(json.dumps(result),flush=True)
    return result
results=[]
with ThreadPoolExecutor(max_workers=args.workers) as pool:
    for fut in as_completed([pool.submit(build,n) for n in chunks]):
        result=fut.result()
        results.append(result)
        (LOG/'progress.json').write_text(json.dumps({'completed':len(results),'total':43,'results':results},indent=2))
report={'success':all(r['returncode']==0 for r in results),'chunks':43,'blocks':430,'records':6593,
        'seconds':round(time.monotonic()-start,2),'method':'Lean decide +kernel','results':results}
(LOG/'summary.json').write_text(json.dumps(report,indent=2))
print(json.dumps({k:v for k,v in report.items() if k!='results'}),flush=True)
raise SystemExit(0 if report['success'] else 1)
