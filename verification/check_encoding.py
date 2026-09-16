"""Check that both Lean data files encode every original JSON integer exactly.

This is a source-to-input audit, independent of the mathematical Lean proofs.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT=Path(__file__).resolve().parents[1]
raw=(ROOT/'verification/certificate.json').read_bytes()
expected_sha='8384d62a377b4fcac4080d0e05979d7a6fcf90437b7e4911927a5403d4052709'
assert hashlib.sha256(raw).hexdigest()==expected_sha, 'Original certificate SHA-256 mismatch'
doc=json.loads(raw)
assert (doc['precision_bits'],doc['m_start'],doc['m_stop_exclusive'])==(100,5,1000000)
assert len(doc['records'])==6593
tags={'direct':0,'center-monotone':1,'center-cubic':2,'boundary':3}
expected=[tuple(map(int,(ml,mh,al,ah,h,tags[tag],sub)))
          for ml,mh,al,ah,h,tag,sub in doc['records']]
pattern=re.compile(r'^def record_(\d{4}) : CertificateRecord := decodeRecord '+
    r'(\d+) (\d+) (\d+) (\d+) (\d+) (\d+) (\d+)$',re.M)
checked=[]
for relative in ['QuadraticTangZhang/Certificate/Data.lean','QuadraticTangZhang/CertificateKernel/Data.lean']:
    data=(ROOT/relative).read_text(encoding='utf-8')
    rows=[tuple(map(int,m)) for m in pattern.findall(data)]
    assert len(rows)==6593, (relative,'record count',len(rows))
    assert [r[0] for r in rows]==list(range(6593)), (relative,'record numbering')
    assert [r[1:] for r in rows]==expected, (relative,'integer encoding mismatch')
    checked.append({'path':relative,'records':len(rows),
                    'sha256':hashlib.sha256((ROOT/relative).read_bytes()).hexdigest()})
groups=[]
for i,row in enumerate(expected):
    if not groups or groups[-1][:2]!=row[:2]: groups.append((row[0],row[1],[]))
    groups[-1][2].append(i)
assert len(groups)==430
original=(ROOT/'QuadraticTangZhang/Certificate/Data.lean').read_text(encoding='utf-8')
block_pattern=re.compile(r'^def block_(\d{3}) : DegreeBlock := ⟨(\d+),(\d+),\[([^\]]*)\]⟩$',re.M)
encoded_blocks=block_pattern.findall(original)
assert len(encoded_blocks)==430
for j,(index,lo,hi,body) in enumerate(encoded_blocks):
    refs=list(map(int,re.findall(r'record_(\d{4})',body)))
    assert (int(index),int(lo),int(hi),refs)==(j,*groups[j]), ('block',j)
block_list=re.search(r'def blocks : List DegreeBlock := \[(.*?)\n\]',original,re.S)
assert block_list is not None
assert list(map(int,re.findall(r'block_(\d{3})',block_list.group(1))))==list(range(430))
report={'success':True,'certificate_sha256':expected_sha,'records':6593,'files':checked,
        'blocks':430,'block_references_match':True,
        'method':'Exact Python integers; no floating-point conversion'}
(ROOT/'verification/encoding.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report))
