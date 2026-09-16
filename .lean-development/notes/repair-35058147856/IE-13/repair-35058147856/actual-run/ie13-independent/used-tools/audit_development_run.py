from pathlib import Path
import hashlib,json,subprocess,tempfile,os,sys
run=Path(sys.argv[1]);a=run/'artifacts/lean-development-statements';r=json.loads((a/'receipt.json').read_text());meta=json.loads((run/'run.json').read_text());commit=r['repository_commit'];repo='/Users/georgestepaniants/Research/OpenProblemsInNLA'
sha=lambda b:hashlib.sha256(b).hexdigest()
assert meta['head_sha']==commit and str(meta['id'])==r['run_id'] and meta['status']=='completed'
assert r['uid']==1001 and r['platform'].startswith('Linux-') and not r['mathematical_verification'] and not r['comparator_run']
for n,h in r['source_sha256'].items():
 b=subprocess.check_output(['git','-c','gc.auto=0','-C',repo,'show',commit+':.lean-development/'+n]);assert sha(b)==h,n
for c in r['commands']:
 assert sha((a/c['log']).read_bytes())==c['sha256'],c['log']
 assert c['source_sha256_after']==r['source_sha256'],c['log']
manifest=json.loads(subprocess.check_output(['git','-c','gc.auto=0','-C',repo,'show',commit+':.lean-development/lake-manifest.json']))
for p in manifest['packages']:assert r['dependency_commits'][p['name']]==p['rev']
cs={c['log']:c for c in r['commands']};statement_acceptances={}
for c in r['commands']:
 if c['log'].endswith('-challenge.log'):
  pid=c['log'][:-len('-challenge.log')];log=(a/c['log']).read_text()
  statement_acceptances[pid]={'exit_code':c['exit_code'],'deliberate_holes':log.count('declaration uses `sorry`'),'error_lines':[l for l in log.splitlines() if 'error' in l]}
out={'reviewer':'/root','run':int(r['run_id']),'actual_checkout':commit,'actual_GitHub_conclusion':meta['conclusion'],'artifact_sha256':sha((run/'lean-development-statements.zip').read_bytes()),'bound_git_inputs':len(r['source_sha256']),'all_source_hashes_unchanged_during_commands':True,'commands':[{'argv':c['argv'],'exit_code':c['exit_code'],'log':c['log'],'sha256':c['sha256']} for c in r['commands']],'dependencies':r['dependency_commits'],'statement_elaboration':statement_acceptances,'mathematical_verification':False,'comparator_run':False,'limits':'Statement holes are intentional specifications. Individual accepted proof helpers are not a complete problem verification. Inspect full compiler diagnostics before repairing or counting anything.'}
p=run/'ROOT-AUDIT.json';data=(json.dumps(out,indent=2)+'\n').encode()
if p.exists():assert p.read_bytes()==data
else:
 with tempfile.NamedTemporaryFile(dir=run,delete=False) as f:f.write(data);f.flush();os.fsync(f.fileno());t=f.name
 os.replace(t,p)
print(json.dumps({'run':r['run_id'],'inputs':len(r['source_sha256']),'statements':statement_acceptances,'audit_sha256':sha(data)},indent=2))
