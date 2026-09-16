from pathlib import Path,PurePosixPath
from concurrent.futures import ThreadPoolExecutor
import hashlib,json,subprocess,sys,zipfile,tempfile,os
runid=int(sys.argv[1]);commit=sys.argv[2];out=Path(sys.argv[3]);out.mkdir(parents=True,exist_ok=True)
gh='/tmp/nla-submission-tools/gh_2.100.0_macOS_arm64/bin/gh'
repo=sys.argv[4] if len(sys.argv)>4 else 'sgstepaniants/OpenProblemsInNLA'
def api(p):return subprocess.check_output([gh,'api','--allow-escape-sequences',f'repos/{repo}/{p}'])
def save(p,b):
 p=out/p;p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():assert p.read_bytes()==b,p;return
 with tempfile.NamedTemporaryFile(dir=p.parent,delete=False) as f:f.write(b);f.flush();os.fsync(f.fileno());tmp=f.name
 os.replace(tmp,p)
paths={'run.json':f'actions/runs/{runid}','jobs.json':f'actions/runs/{runid}/jobs?per_page=100','artifacts.json':f'actions/runs/{runid}/artifacts?per_page=100'}
with ThreadPoolExecutor(max_workers=3) as pool:raw=dict(zip(paths,pool.map(api,paths.values())))
for p,b in raw.items():save(p,b)
r=json.loads(raw['run.json']);assert r['id']==runid and r['head_sha']==commit and r['status']=='completed'
jobs=json.loads(raw['jobs.json'])['jobs'];arts=json.loads(raw['artifacts.json'])['artifacts']
records=[]
for a in arts:
 assert a['workflow_run']['head_sha']==commit and not a['expired']
 b=api(f"actions/artifacts/{a['id']}/zip");h=hashlib.sha256(b).hexdigest();assert a['digest']=='sha256:'+h
 save(a['name']+'.zip',b)
 with zipfile.ZipFile(out/(a['name']+'.zip')) as z:
  for item in z.infolist():
   p=PurePosixPath(item.filename);assert not p.is_absolute() and '..' not in p.parts and ((item.external_attr>>16)&0o170000)!=0o120000
   if not item.is_dir():save(Path('artifacts')/a['name']/p,z.read(item))
 records.append({'id':a['id'],'name':a['name'],'sha256':h})
for j in jobs:
 if j['conclusion']!='skipped':save(f"job-{j['id']}.log",api(f"actions/jobs/{j['id']}/logs"))
receipt={'run':runid,'commit':commit,'conclusion':r['conclusion'],'archives':records,'jobs':[{k:j[k] for k in ['id','name','conclusion']} for j in jobs],'scope':'GitHub metadata/raw log/artifact identity only; proof acceptance needs actual log inspection.'}
save('FETCH-IDENTITY.json',(json.dumps(receipt,indent=2)+'\n').encode());print(json.dumps(receipt,indent=2))
