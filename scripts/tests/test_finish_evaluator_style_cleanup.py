"""Test Git completion logic with local servers and a mock verifier; no Lean runs."""

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

SOURCE = Path(__file__).resolve().parents[2]
BASE = 'd2100df1b583368c56c00c3a4babf0bb72b0cfb2'
CLEANUP = '7506b26a5bb92c036fc13bdae7262f26b21368e0'
REAL_GIT = shutil.which('git')
REAL_BASH = shutil.which('bash')
PASS = 'PASS native build, module inventory, strict style gate, theorem/type and axiom audits, dependency audit, both kernel replays, and nine paired draft checks'

def run(args, cwd=None, env=None, check=True, input_text=None):
    p = subprocess.run(list(map(str, args)), cwd=cwd, env=env, text=True,
                       input=input_text, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if check and p.returncode:
        raise AssertionError(f'{args}: exit {p.returncode}\n{p.stdout}')
    return p

def git(root, *args, env=None):
    return run([REAL_GIT, '-C', root, *args], env=env).stdout.strip()

def main():
    temporary_root=SOURCE/'.codex-work/tmp'
    temporary_root.mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory(dir=temporary_root, prefix='finish-tests-') as temporary:
        root = Path(temporary)
        prep = root/'prep'
        run([REAL_GIT,'clone','--quiet','--no-hardlinks',SOURCE,prep])
        git(prep,'switch','--detach',CLEANUP)
        git(prep,'config','user.name','Workflow test')
        git(prep,'config','user.email','fixture@example.invalid')
        shutil.copy2(SOURCE/'scripts/finish-evaluator-style-cleanup.sh',prep/'scripts/finish-evaluator-style-cleanup.sh')
        git(prep,'add','scripts/finish-evaluator-style-cleanup.sh')
        git(prep,'commit','--quiet','-m','Workflow fixture')
        candidate=git(prep,'rev-parse','HEAD')
        shim=root/'bin';shim.mkdir()
        (shim/'git').write_text('#!/usr/bin/env python3\nimport os,sys\na=sys.argv[1:]\n'
            'if any(x in a for x in ("fetch","push","ls-remote")):\n'
            ' a=["-c","url.file://"+os.environ["MOCK_ORIGIN"]+".insteadOf=git@github.com:flengyel/FailureOfComposition.git",*a]\n'
            f'os.execv({REAL_GIT!r},[{REAL_GIT!r},*a])\n')
        (shim/'git').chmod(0o755)
        (shim/'bash').write_text('#!/usr/bin/env python3\nimport os,sys\na=sys.argv[1:]\n'
            'if a and a[0].endswith("scripts/verify-failure-composition.sh"):\n'
            ' a=[os.environ["MOCK_VERIFIER"],*a[1:]]\n'
            f'os.execv({REAL_BASH!r},[{REAL_BASH!r},*a])\n')
        (shim/'bash').chmod(0o755)
        fake=root/'mock-verify.sh'
        fake.write_text('''#!/usr/bin/env bash
set -euo pipefail
if [[ ${1:-} == --check-environment ]]; then
  if [[ ${MOCK_ENV_FAILURE:-0} == 1 ]]; then echo 'fixture environment failure'; exit 9; fi
  echo 'PASS fixture environment check'; exit 0
fi
echo run >> "$MOCK_COUNTER"
if [[ ${MOCK_FAILURE:-0} == 1 ]]; then echo 'fixture verification failure'; exit 7; fi
python3 - <<'PY'
from pathlib import Path
import json,subprocess,sys,os
project=Path.cwd()/'Lean'
sys.path.insert(0,str(project/'FailureOfComposition'))
import check_style
check_style.bounded_lake_command=lambda *args: ['fixture-no-lean']
check_style.subprocess.run=lambda *args,**kwargs: subprocess.CompletedProcess(args,0,'','')
check_style.check_style(project,project/'fixture-packages.json')
report=project.parent/'.codex-work/logs/port-verification'
(report/'native-build.json').write_text(json.dumps({'status':'passed','returncode':0,
  'mathematical_module_counts':{'FailureOfComposition':72,'CategoricalRiceShapiro':31,'total':103},
  'lean_toolchain':'leanprover/lean4:v4.35.0-rc2',
  'foundation_revision':'e72cfe981aa65166f37fa4e2584f4806bc48d72f',
  'mathlib_revision':'065356127b1dc0016f66b7283ce0ce2c4055aa55'}))
if os.environ.get('MOCK_BAD_STYLE')=='1':
  p=report/'style-lint.json';data=json.loads(p.read_text());data['warning_or_error_count']=1;p.write_text(json.dumps(data))
PY
echo 'ALL_TEST_OUTPUT_IS_SYNTHETIC_NO_LEAN_RAN'
echo ''' + repr(PASS) + '\n')
        cases=['single_branch_success','verifier_failure','bad_style_report','reuse_complete_run',
               'reuse_invalid_tail','environment_failure','dirty_checkout']
        for case in cases:
            origin=root/(case+'-origin.git')
            run([REAL_GIT,'clone','--quiet','--bare','--no-hardlinks',prep,origin])
            git(origin,'update-ref','refs/heads/main',BASE)
            git(origin,'update-ref','refs/heads/codex/evaluator-style-cleanup',candidate)
            git(origin,'symbolic-ref','HEAD','refs/heads/main')
            work=root/(case+'-work')
            run([REAL_GIT,'clone','--quiet','--single-branch','--branch','main',origin,work])
            git(work,'remote','set-url','origin','git@github.com:flengyel/FailureOfComposition.git')
            git(work,'config','user.name','Workflow test')
            git(work,'config','user.email','fixture@example.invalid')
            env=os.environ.copy();env.update(PATH=str(shim)+os.pathsep+env['PATH'],
                MOCK_ORIGIN=str(origin),MOCK_VERIFIER=str(fake),MOCK_COUNTER=str(root/(case+'.count')),
                GIT_CONFIG_GLOBAL='/dev/null',GIT_CONFIG_NOSYSTEM='1')
            env.pop('MOCK_FAILURE',None);env.pop('MOCK_BAD_STYLE',None);env.pop('MOCK_ENV_FAILURE',None)
            if case=='verifier_failure':env['MOCK_FAILURE']='1'
            if case=='bad_style_report':env['MOCK_BAD_STYLE']='1'
            if case=='environment_failure':env['MOCK_ENV_FAILURE']='1'
            sentinel=work/'Lean/.lake/build/cache-sentinel';sentinel.parent.mkdir(parents=True)
            sentinel.write_text('do not alter existing cache')
            if case in {'reuse_complete_run','reuse_invalid_tail'}:
                run([str(shim/'git'),'fetch','origin','refs/heads/codex/evaluator-style-cleanup'],cwd=work,env=env)
                git(work,'switch','--detach',CLEANUP)
                log=work/'.codex-work/logs/evaluator-style-cleanup.log';log.parent.mkdir(parents=True)
                result=run([REAL_BASH,fake],cwd=work,env=env);log.write_text(result.stdout)
                if case=='reuse_invalid_tail':log.write_text(log.read_text()+'fixture trailing failure\n')
            if case=='dirty_checkout':(work/'README.md').write_text('uncommitted user change\n')
            # Match the documented git-show-to-Bash bootstrap, including stdin.
            result=run([REAL_BASH],cwd=work,env=env,check=False,
                       input_text=(SOURCE/'scripts/finish-evaluator-style-cleanup.sh').read_text())
            (root/(case+'.output')).write_text(result.stdout)
            require_success=case in {'single_branch_success','reuse_complete_run','reuse_invalid_tail'}
            if require_success:
                assert result.returncode==0,(case,result.returncode,result.stdout)
                head=git(work,'rev-parse','HEAD')
                assert head==git(origin,'rev-parse','main')
                assert git(work,'symbolic-ref','--short','HEAD')=='main'
                assert not git(work,'status','--porcelain')
                assert '+refs/heads/*:refs/remotes/origin/*' in git(work,'config','--get-all','remote.origin.fetch')
                assert git(work,'rev-parse','origin/codex/evaluator-style-cleanup')==candidate
            else:
                assert result.returncode!=0,(case,result.stdout)
                assert git(work,'rev-parse','main')==BASE
                assert git(origin,'rev-parse','main')==BASE
                if case=='dirty_checkout':assert (work/'README.md').read_text()=='uncommitted user change\n'
            counter=Path(env['MOCK_COUNTER'])
            count=len(counter.read_text().splitlines()) if counter.exists() else 0
            expected=0 if case in {'dirty_checkout','environment_failure'} else 2 if case=='reuse_invalid_tail' else 1
            assert count==expected,(case,count,result.stdout)
            assert sentinel.read_text()=='do not alter existing cache'
            print('PASS',case,'exit',result.returncode,'verifier executions',count,flush=True)

if __name__=='__main__':main()
