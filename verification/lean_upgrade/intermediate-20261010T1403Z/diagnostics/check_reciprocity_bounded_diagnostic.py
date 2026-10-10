from pathlib import Path
import datetime, hashlib, json, os, signal, subprocess, sys, time

source=Path(sys.argv[1]); label=sys.argv[2]; outdir=Path('work/lean-upgrade')
log=outdir/(label+'.log'); record=outdir/(label+'.json'); snapshot=outdir/(label+'.lean.source')
guard=outdir/(label+'-guard.json')
assert not any(p.exists() for p in [log,record,snapshot,guard]),label
snapshot.write_bytes(source.read_bytes()); sha=hashlib.sha256(snapshot.read_bytes()).hexdigest()
env=os.environ.copy()
env['AS_GINZBURG_LEAN_ROOT']=str(Path.cwd()/'work/lean-upgrade/lean-4.34.1-linux')
env['AS_GINZBURG_PROC_SELF_FIX']='1'
cmd=['bash','scripts/with_lean.sh','lake','env','lean','-DautoImplicit=false',str(source)]
started=datetime.datetime.now(datetime.timezone.utc).isoformat(); tick=time.monotonic()
peak=0; triggered=None

with log.open('w') as stream:
    p=subprocess.Popen(cmd,env=env,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
    while p.poll() is None:
        processes=[]
        for proc in Path('/proc').iterdir():
            if not proc.name.isdecimal():
                continue
            try:
                args=[a.decode() for a in (proc/'cmdline').read_bytes().split(b'\0') if a]
                if not args or Path(args[0]).name!='lean':
                    continue
                if str(source) not in args and str(source.resolve()) not in args:
                    continue
                pid=int(proc.name)
                rss=int((proc/'statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE')
                processes.append((pid,rss)); peak=max(peak,rss)
            except (OSError,IndexError):
                pass
        elapsed=time.monotonic()-tick
        if triggered is None and (any(rss>6*1024**3 for _,rss in processes) or elapsed>150):
            triggered={'observed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'elapsed_seconds':elapsed,'processes':processes,'peak_rss_bytes':peak,
              'signal':'SIGTERM','reason':'bounded work-only diagnostic 6GiB RSS or 150 seconds',
              'diagnostic_only':True}
            guard.write_text(json.dumps(triggered,indent=2)+'\n')
            if processes:
                for pid,_ in processes:
                    try: os.kill(pid,signal.SIGTERM)
                    except ProcessLookupError: pass
            else:
                os.killpg(p.pid,signal.SIGTERM)
        if triggered is not None and elapsed-triggered['elapsed_seconds']>10 and p.poll() is None:
            os.killpg(p.pid,signal.SIGKILL)
        time.sleep(.5)
    exit_code=p.wait()
result={'command':cmd,'source':str(source),'source_sha256':sha,
  'source_unchanged':hashlib.sha256(source.read_bytes()).hexdigest()==sha,'source_snapshot':str(snapshot),
  'started_at_utc':started,'finished_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
  'elapsed_seconds':time.monotonic()-tick,'exit_code':exit_code,'log':str(log),
  'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'wrote_olean':False,
  'diagnostic_only':True,'proof_limits_unchanged':True,'peak_rss_bytes':peak,
  'guard':str(guard) if triggered else None}
record.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result));sys.exit(exit_code)
