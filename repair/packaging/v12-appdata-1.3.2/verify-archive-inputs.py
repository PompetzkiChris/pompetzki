"""Check archive paths, CRCs and every explicit public source selection."""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,re,zipfile

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--build',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
if args.output.exists():raise SystemExit('Output already exists: '+str(args.output))
digest=lambda data:hashlib.sha256(data).hexdigest()
assets=[]
for name in ['Abschluss-1.3.2-source.zip','Abschluss-1.3.2-windows-x64.zip']:
    path=args.build/name
    with zipfile.ZipFile(path) as archive:
        assert archive.testzip() is None,'ZIP CRC failure'
        names=archive.namelist();folded=set()
        for name_in_zip in names:
            relative=PurePosixPath(name_in_zip)
            assert not relative.is_absolute() and '..' not in relative.parts and '\\' not in name_in_zip
            assert name_in_zip.casefold() not in folded,'Windows path collision'
            folded.add(name_in_zip.casefold())
        assets.append({'name':name,'bytes':path.stat().st_size,'entries':len(names),'sha256':digest(path.read_bytes()),'paths_and_crc_passed':True})

checked=[]
with zipfile.ZipFile(args.build/'Abschluss-1.3.2-source.zip') as archive:
    prefix='Abschluss-1.3.2-source/'
    def data(path):return archive.read(prefix+path)
    def manifest(path):return json.loads(data(path))
    def check_rows(label,path,rows,path_key,base=''):
        for row in rows:
            target=base+row[path_key]
            assert digest(data(target))==row['sha256'],label+': '+target
        checked.append({'manifest':label,'path':path,'entries':len(rows),'sha256':digest(data(path)),'passed':True})
    main=manifest('PUBLIC-SOURCE-WHITELIST.json')
    assert len(main['files'])==86
    check_rows('judge-runtime86','PUBLIC-SOURCE-WHITELIST.json',main['files'],'package_relative_path')
    paths=[
        ('book-v7','repair/book-v7/PUBLIC-SOURCE-MANIFEST.json','repair/book-v7/'),
        ('packaging','repair/packaging/v12-appdata-1.3.2/PUBLIC-SOURCE-MANIFEST.json','repair/packaging/v12-appdata-1.3.2/'),
        ('math-workbench-v2','repair/math-workbench-v2/PUBLIC-SOURCE-MANIFEST.json','repair/math-workbench-v2/'),
        ('matrix-oracle','repair/packaging/v12-appdata-1.3.2/MATRIX-SOURCE-MANIFEST.json','repair/bot-matrix-validation/'),
        ('gallina-gate-proof','repair/grok-proof-integrated/public/PUBLIC-WHITELIST.json','repair/grok-proof-integrated/public/'),
        ('resource-v6','judge/validation-v6-resource/PUBLIC-SOURCE-MANIFEST.json','judge/validation-v6-resource/'),
        ('cockpit','repair/packaging/v12-appdata-1.3.2/COCKPIT-SOURCE-MANIFEST.json','cockpit/'),
    ]
    for label,path,base in paths:check_rows(label,path,manifest(path)['files'],'path',base)
    path='judge/validation-v5/SOURCE-INPUTS.json'
    check_rows('validation-v5',path,manifest(path)['files'],'package_relative_path')
    path='repair/packaging/v12-appdata-1.3.2/SUPPORT-SOURCE-MANIFEST.json'
    for section,rows in manifest(path).items():
        if isinstance(rows,list):check_rows('support-'+section,path,rows,'package_relative_path')
    runtime_hash=digest(data('runtime/source/pompetzki.asm'))
    builder=data('runtime/build-interpreter.py').decode()
    pin=re.search(r'EXPECTED_SOURCE_SHA256\s*=\s*["\']([0-9a-f]{64})',builder).group(1)
    assert pin==runtime_hash
    native_source_hash=digest(data('judge/judge-v6.pmp'))
    native_builder=data('judge/native-v6/portable/build-native.py').decode()
    native_pin=re.search(r'^SOURCE_SHA256\s*=\s*["\']([0-9a-f]{64})',native_builder,re.M).group(1)
    assert native_pin==native_source_hash
    context_paths=[n for n in archive.namelist() if re.search(r'(?i)(?:^|/)(?:brainstorm[^/]*|private[^/]*|transcripts?|app-api|client-data)(?:/|$)',n) or n.endswith('.jsonl') or n.endswith('/lib/cdp.pmp')]
    assert not context_paths,context_paths
report={'passed':True,'version':'1.3.2','assets':assets,'explicit_manifests':checked,
        'runtime_source_sha256':runtime_hash,'runtime_builder_pin_matches':True,
        'judge_v6_sha256':native_source_hash,'native_builder_pin_matches':True,
        'excluded_context_path_hits':context_paths,
        'scope':'Explicit selections, bytes, builder pins, paths and CRCs; executable correspondence remains a separate obligation.'}
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(json.dumps(report,indent=2))
print(json.dumps({'passed':True,'manifest_sections':len(checked),'assets':len(assets),'output':str(args.output)}))
