"""Retain the exact v6 eight-instruction RECORDCOUNT controller."""
from pathlib import Path
import argparse,hashlib,json,re,shutil
root=Path(__file__).resolve().parent
parser=argparse.ArgumentParser();parser.add_argument('--project',type=Path,required=True);args=parser.parse_args()
source=args.project/'judge'/'judge-v6.pmp';raw=source.read_bytes()
pin='87562735cf20dfd18eb5f26348878b2ac6306bc78714d6953565df9c833d0dc7'
assert hashlib.sha256(raw).hexdigest()==pin
retained=root/'source';retained.mkdir(exist_ok=False);(retained/'judge-v6.pmp').write_bytes(raw)
lines=raw.splitlines(keepends=True)
start=next(i for i,line in enumerate(lines) if line.strip()==b'label RECORDCOUNT')
end=start+8;fragment=b''.join(lines[start:end])
(retained/'recordcount-fragment.pmp').write_bytes(fragment)
quote=lambda s:'"'+s.replace('"','""')+'"'
operand=lambda s:'(OL '+s+')' if re.fullmatch(r'-?\d+',s) else '(OV '+quote(s)+')'
rows=[];terms=[]
for number,line in enumerate(lines[start:end],start+1):
    text=line.decode('ascii').strip();tokens=text.split();op=tokens[0]
    if op=='label':assert len(tokens)==2;term='SLabel '+quote(tokens[1])
    elif op=='return':assert len(tokens)==1;term='SReturn'
    elif op=='goto':assert len(tokens)==2;term='SGoto '+quote(tokens[1])
    elif op=='set':assert tokens[2]=='sub' and len(tokens)==5;term='SSub '+quote(tokens[1])+' '+operand(tokens[3])+' '+operand(tokens[4])
    elif op=='when':assert tokens[1]=='negative' and tokens[3]=='goto' and len(tokens)==5;term='SWhen CNeg '+operand(tokens[2])+' '+quote(tokens[4])
    elif op=='text':
        match=re.fullmatch(r'text (\w+) "([^"\n]*)"',text);assert match
        term='STextLit '+quote(match[1])+' (bytes_of_str '+quote(match[2])+')'
    else:raise AssertionError(text)
    rows.append({'pc':len(terms),'source_line':number,'source_text':text,'PmpCore_constructor':term});terms.append(term)
assert len(terms)==8
proof=root/'Proof';proof.mkdir()
code='''From Stdlib Require Import List String ZArith Init.Byte.
From mathcomp Require Import all_ssreflect.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore.
Local Open Scope string_scope.
Local Open Scope Z_scope.
'''
code+='Definition pinned_judge_sha256 : string := '+quote(pin)+'.\n'
code+='Definition retained_recordcount_bytes : seq byte := [:: '+'; '.join('x%02x'%b for b in fragment)+'].\n'
code+='Definition Precord : seq stmt := [::\n  '+';\n  '.join(terms)+'].\n'
code+='Definition record_stops : seq string := [:: "FAIL"].\n'
code+='Definition pc_RECORDCOUNT : nat := 0%N.\nDefinition pc_RECORDCOUNTBAD : nat := 5%N.\n'
code+='Lemma find_RECORDCOUNT : find_label Precord "RECORDCOUNT" = Some pc_RECORDCOUNT.\nProof. vm_compute; reflexivity. Qed.\n'
code+='Lemma find_RECORDCOUNTBAD : find_label Precord "RECORDCOUNTBAD" = Some pc_RECORDCOUNTBAD.\nProof. vm_compute; reflexivity. Qed.\n'
code+=f'Lemma retained_recordcount_length : size retained_recordcount_bytes = {len(fragment)}%N.\nProof. vm_compute; reflexivity. Qed.\n'
(proof/'RecordCountSource.v').write_text(code,encoding='utf-8')
record={'source':'source/judge-v6.pmp','source_sha256':pin,'first_line':start+1,'last_line':end,
        'fragment_bytes':len(fragment),'fragment_sha256':hashlib.sha256(fragment).hexdigest(),'instructions':rows,
        'boundary':'Trusted mechanical text-to-AST translation; kernel checks semantics of Precord, not the translation or native compiler.'}
(retained/'source-extraction.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({key:value for key,value in record.items() if key!='instructions'}))
