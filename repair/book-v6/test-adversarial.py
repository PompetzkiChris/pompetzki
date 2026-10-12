"""Execute the ambiguous-verdict and inherited-pipe regressions on Windows."""
import argparse, hashlib, json, shutil, subprocess, time
from pathlib import Path

parser=argparse.ArgumentParser()
parser.add_argument('--bundle',type=Path,required=True)
parser.add_argument('--racket',default=r'C:\Program Files\Racket\racket.exe')
args=parser.parse_args()
here=Path(__file__).resolve().parent
out=here/'tests'/('adversarial-'+time.strftime('%Y%m%d-%H%M%S'))
out.mkdir(parents=True,exist_ok=False)
source=out/'owned-judge.c'
source.write_text(r'''
#include <windows.h>
#include <stdio.h>
#include <string.h>
int main(int argc,char**argv) {
 if(argc>1 && strcmp(argv[1],"--owned-pipe-child")==0){Sleep(6500);return 0;}
 char own[MAX_PATH],modepath[MAX_PATH],mode[40]={0};
 GetModuleFileNameA(NULL,own,MAX_PATH);
 strcpy(modepath,own);char *p=strrchr(modepath,'\\');if(!p)return 2;
 strcpy(p+1,"mode.txt");FILE*f=fopen(modepath,"r");if(f){fgets(mode,sizeof mode,f);fclose(f);}
 if(strncmp(mode,"orphan",6)==0){
  char cmd[2*MAX_PATH];snprintf(cmd,sizeof cmd,"\"%s\" --owned-pipe-child",own);
  STARTUPINFOA s={sizeof s};PROCESS_INFORMATION pi={0};
  s.dwFlags=STARTF_USESTDHANDLES;s.hStdInput=GetStdHandle(STD_INPUT_HANDLE);
  s.hStdOutput=GetStdHandle(STD_OUTPUT_HANDLE);s.hStdError=GetStdHandle(STD_ERROR_HANDLE);
  if(!CreateProcessA(NULL,cmd,NULL,NULL,TRUE,CREATE_NO_WINDOW,NULL,NULL,&s,&pi))return 2;
  CloseHandle(pi.hThread);CloseHandle(pi.hProcess);Sleep(20000);return 0;
 }
 puts("ACCEPT");puts("REJECT");puts("0 1 2 1");return 0;
}
''',encoding='ascii')
exe=out/'owned-judge.exe'
build=subprocess.run(['gcc',str(source),'-o',str(exe)],capture_output=True)
(out/'compile.stdout.txt').write_bytes(build.stdout);(out/'compile.stderr.txt').write_bytes(build.stderr)
assert build.returncode==0,build.stderr
results=[]
version='v5' if (args.bundle/'judge/judge-v5.pmp').is_file() else 'v4'
for mode in ['ambiguous','orphan']:
 bundle=out/('bundle-'+mode);(bundle/'judge').mkdir(parents=True)
 for name in ['judge-'+version+'.pmp','judge-'+version+'.rkt','registry-auth-v4.rkt']:
  shutil.copy2(args.bundle/'judge'/name,bundle/'judge'/name)
 shutil.copy2(args.bundle/'pompetzki.exe',bundle/'pompetzki.exe')
 shutil.copy2(exe,bundle/('judge/judge-'+version+'-windows.exe'));shutil.copy2(exe,bundle/'judge-rkt.exe')
 (bundle/'mode.txt').write_text(mode);(bundle/'judge/mode.txt').write_text(mode)
 posting=out/('posting-'+mode)
 cmd=[args.racket,str(here/'verified-book-post.rkt'),'--bundle',str(bundle),'--timeout','1',str(posting),'2026-10-12 UTC',str(here/'registry-tests/prefix-0-truth.jdg')]
 start=time.monotonic_ns();p=subprocess.run(cmd,capture_output=True,timeout=25);elapsed=(time.monotonic_ns()-start)//1000000
 (out/(mode+'.stdout.txt')).write_bytes(p.stdout);(out/(mode+'.stderr.txt')).write_bytes(p.stderr)
 meta=json.loads((posting/'run-metadata.json').read_text())
 assert p.returncode==3 and b'SUSPENSE 1' in p.stdout,(mode,p.returncode,p.stdout,p.stderr)
 assert all(r[j]['verdict']=='UNKNOWN' for r in meta['runs'] for j in ['pmp','racket'])
 assert not any(l.startswith('F') for l in (posting/'BOOK-1.0.ledger').read_text().splitlines())
 if mode=='orphan':assert elapsed<16000,elapsed
 results.append({'case':mode,'exit':p.returncode,'elapsed_ms':elapsed,'command':cmd,'passed':True})
(out/'results.json').write_text(json.dumps({'cases':len(results),'passed':len(results),'results':results},indent=2))
(out/'SHA256SUMS.txt').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(out).as_posix()+'\n' for p in sorted(out.rglob('*')) if p.is_file()))
print(json.dumps({'output':str(out),'cases':len(results),'passed':len(results)}))
