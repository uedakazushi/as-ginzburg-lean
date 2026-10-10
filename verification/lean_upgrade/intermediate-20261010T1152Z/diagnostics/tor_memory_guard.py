from pathlib import Path
import argparse,datetime,hashlib,json,os,signal,subprocess,time
p=argparse.ArgumentParser();p.add_argument('--pid',type=int,required=True);p.add_argument('--source',required=True);p.add_argument('--label',required=True);p.add_argument('--limit-kib',type=int,default=8*1024*1024);a=p.parse_args()
source=Path(a.source);sha=hashlib.sha256(source.read_bytes()).hexdigest();out=Path('work/lean-upgrade')/(a.label+'.json');log=out.with_suffix('.log');assert not out.exists() and not log.exists()
start=datetime.datetime.now(datetime.timezone.utc).isoformat();peak=0;status='process ended';samples=0
with log.open('w') as stream:
 while True:
  result=subprocess.run(['ps','-p',str(a.pid),'-o','rss=,etime=,args='],capture_output=True,text=True)
  if result.returncode or not result.stdout.strip():break
  rss,elapsed,args=result.stdout.strip().split(maxsplit=2);rss=int(rss)
  if not rss:break
  assert a.source in args and '-DautoImplicit=false' in args and ' -o ' not in args,args
  stamp=datetime.datetime.now(datetime.timezone.utc).isoformat();peak=max(peak,rss);samples+=1;stream.write(json.dumps({'timestamp_utc':stamp,'rss_kib':rss,'elapsed':elapsed})+'\n');stream.flush()
  if rss>=a.limit_kib:
   assert hashlib.sha256(source.read_bytes()).hexdigest()==sha
   os.kill(a.pid,signal.SIGTERM);status='targeted SIGTERM at memory limit';break
  time.sleep(1)
x={'started_at_utc':start,'finished_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pid':a.pid,'source':a.source,'source_sha256':sha,'source_unchanged':hashlib.sha256(source.read_bytes()).hexdigest()==sha,'limit_kib':a.limit_kib,'peak_observed_kib':peak,'sample_count':samples,'status':status,'samples_log':str(log)};out.write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x))
