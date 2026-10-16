#!/usr/bin/env python3
"""Untrusted fixed Named Stack syntax-node scan and bound-composition arithmetic.

This diagnoses the uniform maximum-body strategy; it is not an execution or
source-clock proof. Every syntax bound and compiler premise needs Lean checks.
"""
from pathlib import Path
import re,json,hashlib
ROOT=Path(__file__).resolve().parents[2]
records=[]
missing=[]
ids=[0,1,2,4,5,6]+list(range(64,890))
for ident in ids:
 p=ROOT/f'submission/InitECandidate/Proofs/BackendStages/Named{ident}.lean'
 if not p.exists():
  missing.append(ident)
  continue
 source=p.read_text(); facts={}
 for d in re.finditer(r'^def (NamedBody\d+_\d+) : StackLang.HolProg 64 :=\n(.*?)(?=^def |^theorem |^end )',source,re.M|re.S):
  name,body=d[1],d[2].strip()
  head=re.match(r'(?:Flapjack.Compiler.Backend.StackLang.Prog|)\.([a-zA-Z]+)\b',body)
  assert head,(ident,name,body[:70])
  refs=re.findall(r'NamedBody\d+_\d+',body)
  assert all(r in facts for r in refs),(ident,name,refs)
  assert not re.search(r'(?:Flapjack.Compiler.Backend.StackLang.Prog|)\.(?:seq|ite|loop|call)\b',body[head.end():]),(ident,name,'inline composite')
  kind=head[1]
  expected={'seq':2,'ite':2,'loop':1}
  if kind in expected: assert len(refs)==expected[kind],(ident,name)
  elif kind=='call': assert len(refs)<=2,(ident,name)
  else: assert not refs,(ident,name)
  facts[name]=1+sum(facts[r] for r in refs)
 root=re.search(r'^def Named\d+ : Nat × StackLang.HolProg 64 := \(\d+, (NamedBody\d+_\d+)\)$',source,re.M)
 if not root:
  records.append({'procedure':ident,'unparsed':True,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
  continue
 assert root[1] in facts
 records.append({'procedure':ident,'nodes':facts[root[1]],'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
parsed=[r for r in records if 'nodes' in r]
maximum=max(r['nodes'] for r in parsed)
# With source clock c: Crep 256c, Word-to-Stack 35x, RawCall 2x;
# Alloc adds 0; RemoveDirect adds at most 1. WholeCall adds 4*((L+1)*s+2L)
# to the Lab initial clock s-1. Lab->RV multiplies by 402.
coefficient=402*(4*maximum+5)*2*35*256
result={'description':__doc__,'records':records,'missing_individual_files':missing,'maximum_parsed_nodes':maximum,
        'uniform_linear_coefficient':coefficient,'yukon_max_finite':9007199254740984,
        'max_source_clock_ignoring_additive_cost':9007199254740984//coefficient,
        'assumptions':['Crep ceiling 126 pending kernel checks','Word ceiling 17 aggregate pending',
                       'Stack/Lab initial relations and full composition not yet proved']}
(ROOT/'work/agent-notes/flatten-nodes-scan.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('description','records','assumptions')}))
print('largest',sorted(parsed,key=lambda r:r['nodes'],reverse=True)[:5])
print('unparsed',[r['procedure'] for r in records if 'nodes' not in r])
print('missing_individual_files',missing)
