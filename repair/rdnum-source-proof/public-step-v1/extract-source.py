"""Retain and translate the pinned reader fragment into existing PmpCore syntax."""
from pathlib import Path
import hashlib,json,re

root=Path(__file__).resolve().parent
source=root/'source'/'judge-v5.pmp';raw=source.read_bytes()
pin='4d936cb8103c6aa97fb6ec290f88b3ee636c69f94f0cdb089a4621d9ba251d1b'
assert hashlib.sha256(raw).hexdigest()==pin
lines=raw.splitlines(keepends=True)
start=next(i for i,line in enumerate(lines) if line.strip()==b'label SKIPWS')
end=next(i for i,line in enumerate(lines) if line.strip()==b'label RDTAG')
fragment=b''.join(lines[start:end])
(root/'source'/'reader-fragment.pmp').write_bytes(fragment)
quote=lambda s:'"'+s.replace('"','""')+'"'
def operand(text):
    return '(OL '+text+')' if re.fullmatch(r'-?\d+',text) else '(OV '+quote(text)+')'
rows=[];ast=[]
for index,line in enumerate(lines[start:end],start+1):
    text=line.decode('ascii').strip()
    if not text or text.startswith(';'):continue
    tokens=text.split();op=tokens[0]
    if op=='label':term='SLabel '+quote(tokens[1])
    elif op=='goto':term='SGoto '+quote(tokens[1])
    elif op=='gosub':term='SGosub '+quote(tokens[1])
    elif op=='return':assert len(tokens)==1;term='SReturn'
    elif op=='when':
        assert tokens[3]=='goto' and len(tokens)==5
        condition={'negative':'CNeg','zero':'CZero','nonzero':'CNonzero'}[tokens[1]]
        term='SWhen '+condition+' '+operand(tokens[2])+' '+quote(tokens[4])
    elif op=='set':
        ctor={'const':'SConst','sub':'SSub','add':'SAdd','mul':'SMul','peek':'SPeek'}[tokens[2]]
        term=ctor+' '+quote(tokens[1])+' '+operand(tokens[3])
        if tokens[2]=='peek':assert tokens[4]=='1';term+=' 1%N'
        elif tokens[2]!='const':term+=' '+operand(tokens[4])
    elif op=='text':
        m=re.fullmatch(r'text (\w+) "([^"]*)"',text);assert m
        term='STextLit '+quote(m[1])+' (bytes_of_str '+quote(m[2])+')'
    else:raise ValueError(text)
    rows.append({'source_line':index,'pc':len(ast),'source':text,'PmpCore_constructor':term})
    ast.append(term)
header='''From Stdlib Require Import List String ZArith Lia.
From Stdlib Require Import Init.Byte.
From mathcomp Require Import all_ssreflect.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore ExecStep ExecMono.
Local Open Scope string_scope.
Local Open Scope Z_scope.
'''
body=header+'\nDefinition pinned_judge_sha256 : string := '+quote(pin)+'.\n'
body+='Definition retained_reader_bytes : seq byte := [:: '+('; '.join('x'+format(b,'02x') for b in fragment))+'].\n'
body+='Definition Preader : seq stmt := [::\n  '+';\n  '.join(ast)+'].\n'
body+='Definition reader_stops : seq string := [:: "FAIL"].\n'
for label in ['SKIPWS','ENDTOK','RDNUM','RDNUM1','RDNUM2','RDNUM3','RDNUMLEAD','RDNUMBOUND','RDNUM4','RDNUMADVANCE','RDNUM9','RDNUMBAD']:
    body+='Definition pc_'+label+' : nat := Eval vm_compute in odflt 0%N (find_label Preader '+quote(label)+').\n'
    body+='Lemma find_'+label+' : find_label Preader '+quote(label)+' = Some pc_'+label+'.\nProof. vm_compute; reflexivity. Qed.\n'
body+='Lemma retained_reader_length : size retained_reader_bytes = '+str(len(fragment))+'%N.\nProof. vm_compute; reflexivity. Qed.\n'
(root/'Proof'/'RDNUMSource.v').write_text(body)
receipt={'source_path':'source/judge-v5.pmp','source_sha256':pin,'first_line':start+1,'last_line':end,
         'fragment_sha256':hashlib.sha256(fragment).hexdigest(),'fragment_bytes':len(fragment),'instructions':len(ast),'rows':rows,
         'boundary':'This Python text-to-AST extraction is a retained mechanical translation, not a proved source parser or native/compiler correspondence. The operational theorems execute Preader in the unchanged existing C2Link.PmpCore semantics.'}
(root/'source'/'source-extraction.json').write_text(json.dumps(receipt,indent=2))
print(json.dumps({key:receipt[key] for key in ['source_sha256','first_line','last_line','fragment_bytes','instructions']}))
