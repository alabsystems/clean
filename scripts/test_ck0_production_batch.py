#!/usr/bin/env python3
# Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
"""Real committed-Git inventory and injected binary-protocol refusal controls.

No Rust/native authority or proof is executed. Malformed replies are isolated
parser fixtures; real Git outputs provide the positive object/path witnesses.
"""
import hashlib
import io
import json
import os
import shlex
from pathlib import Path
import subprocess
import sys
import tempfile
import types
import unittest
from unittest.mock import patch

SCRIPT=Path(__file__).with_name('check_ck0_lineage.py')


def subject(path=SCRIPT):
    module=types.ModuleType('production_batch_test_subject');module.__file__=str(path)
    exec(compile(path.read_bytes(),str(path),'exec',dont_inherit=True),module.__dict__)
    return module


def oid(data):
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data,
                        usedforsecurity=False).hexdigest()


def frame(data):
    return oid(data).encode()+b' blob '+str(len(data)).encode()+b'\n'+data+b'\n'


class BatchProtocol(unittest.TestCase):
    def setUp(self):self.s=subject()

    def test_empty_and_binary_blobs(self):
        for data in [b'',b'\x00\n\r\xff'*(1024*1024),b'no final newline']:
            with self.subTest(bytes=len(data)):
                self.assertEqual(self.s._batch_blob_hashes(io.BytesIO(frame(data)),[oid(data)]),
                                 {oid(data):hashlib.sha256(data).hexdigest()})

    def test_bad_header_and_size_refuse(self):
        data=b'abc';key=oid(data).encode()
        headers=[b'',key+b' missing\n',key+b' blob',b'0'*40+b' blob 3\n',
                 key+b' tree 3\n',key+b' blob -3\n',key+b' blob +3\n',
                 key+b' blob 03\n',key+b' blob x\n',key+b' blob '+b'9'*21+b'\n',
                 key+b' blob 9223372036854775808\n',key+b' blob 3 extra\n',
                 key+b' blob 3\r\n']
        for header in headers:
            with self.subTest(header=header),self.assertRaises(ValueError):
                self.s._batch_blob_hashes(io.BytesIO(header+data+b'\n'),[oid(data)])

    def test_missing_short_body_and_terminator_refuse(self):
        data=b'abc';valid=frame(data)
        for reply in [b'',valid[:-3],valid[:-1],valid[:-1]+b'\r',valid+b'\n',valid+valid]:
            with self.subTest(reply=reply),self.assertRaises(ValueError):
                self.s._batch_blob_hashes(io.BytesIO(reply),[oid(data)])

    def test_same_size_substitution_refuses(self):
        data=b'abc';reply=frame(data).replace(b'\nabc\n',b'\nxyz\n')
        with self.assertRaisesRegex(ValueError,'Git blob identity'):
            self.s._batch_blob_hashes(io.BytesIO(reply),[oid(data)])

    def test_omitted_object_identity_mutant_accepts_the_planted_substitution(self):
        original=SCRIPT.read_text()
        needle="need(object_hash.hexdigest() == oid, 'production Git blob identity: ' + oid)"
        self.assertEqual(original.count(needle),1)
        mutant=types.ModuleType('omitted_object_identity_control');mutant.__file__=str(SCRIPT)
        exec(compile(original.replace(needle,"need(True, 'deleted identity control')"),
                     str(SCRIPT),'exec',dont_inherit=True),mutant.__dict__)
        data=b'abc';reply=frame(data).replace(b'\nabc\n',b'\nxyz\n')
        self.assertEqual(mutant._batch_blob_hashes(io.BytesIO(reply),[oid(data)]),
                         {oid(data):hashlib.sha256(b'xyz').hexdigest()})

    def test_ordered_census_and_request_validation(self):
        a,b=b'one',b'two'
        expected={oid(a):hashlib.sha256(a).hexdigest(),oid(b):hashlib.sha256(b).hexdigest()}
        self.assertEqual(self.s._batch_blob_hashes(io.BytesIO(frame(a)+frame(b)),list(expected)),expected)
        for reply in [frame(b)+frame(a),frame(a),frame(a)+frame(a)]:
            with self.subTest(reply=reply),self.assertRaises(ValueError):
                self.s._batch_blob_hashes(io.BytesIO(reply),list(expected))
        for requests in [[oid(a),oid(a)],['x'],['a'*64],[oid(a)+'\n']]:
            with self.subTest(requests=requests),self.assertRaises(ValueError):
                self.s._batch_blob_hashes(io.BytesIO(frame(a)),requests)

    def test_tree_shape_refuses_before_batch(self):
        key=oid(b'abc').encode()
        good=b'100644 blob '+key+b'\tsrc/a\0'
        cases=[b'',good[:-1],good+good,b'100644 blob '+key+b'\t\0',
               b'120000 blob '+key+b'\tsrc/link\0',
               b'160000 commit '+key+b'\tsrc/submodule\0',
               b'040000 tree '+key+b'\tsrc/subtree\0',
               b'100644 blob invalid\tsrc/a\0',b'malformed\0',
               b'100644 blob '+key+b'\tsrc/\xff\0']
        for raw in cases:
            with self.subTest(raw=raw),patch.object(self.s,'_production_git',return_value=raw),\
                 patch.object(self.s.subprocess,'run') as run,self.assertRaises(ValueError):
                self.s.git_files(Path('/unused'),'a'*40,['src'])
            run.assert_not_called()

    def test_nonzero_child_with_valid_response_refuses_and_spool_closes(self):
        data=b'abc';key=oid(data)
        raw=b'100644 blob '+key.encode()+b'\tsrc/a\0'
        held=[];actual_run=subprocess.run
        with tempfile.TemporaryDirectory(prefix='q6-nonzero-git-') as directory:
            directory=Path(directory);script=directory/'probe.py';binary=directory/'git'
            script.write_text('import sys\nsys.stdout.buffer.write('+repr(frame(data))+')\nraise SystemExit(17)\n')
            binary.write_text('#!/bin/sh\nexec '+shlex.quote(sys.executable)+' '+shlex.quote(str(script))+' "$@"\n')
            binary.chmod(0o700)
            def observe(argv,**kwargs):
                held.append(kwargs['stdout']);return actual_run(argv,**kwargs)
            with patch.object(self.s,'_production_git',return_value=raw),\
                 patch.object(self.s.subprocess,'run',side_effect=observe),\
                 patch.dict(os.environ,{'PATH':str(directory)+os.pathsep+os.environ.get('PATH','')}),\
                 self.assertRaises(subprocess.CalledProcessError) as error:
                self.s.git_files(Path('/unused'),'a'*40,['src'])
            self.assertEqual(error.exception.returncode,17)
        self.assertTrue(held[0].closed)

    def test_launch_error_refuses(self):
        data=b'abc';raw=b'100644 blob '+oid(data).encode()+b'\tsrc/a\0'
        with patch.object(self.s,'_production_git',return_value=raw),\
             patch.object(self.s.subprocess,'run',side_effect=OSError('injected missing Git')),\
             self.assertRaises(OSError):self.s.git_files(Path('/unused'),'a'*40,['src'])

    def test_invalid_response_spool_closes(self):
        data=b'abc';raw=b'100644 blob '+oid(data).encode()+b'\tsrc/a\0';held=[]
        def invalid(argv,**kwargs):
            held.append(kwargs['stdout']);kwargs['stdout'].write(b'injected malformed frame\n')
            return subprocess.CompletedProcess(argv,0)
        with patch.object(self.s,'_production_git',return_value=raw),\
             patch.object(self.s.subprocess,'run',side_effect=invalid),self.assertRaises(ValueError):
            self.s.git_files(Path('/unused'),'a'*40,['src'])
        self.assertTrue(held[0].closed)

    def test_real_git_failure_is_not_partial_inventory(self):
        with tempfile.TemporaryDirectory(prefix='q6-missing-git-') as directory:
            with self.assertRaises(subprocess.CalledProcessError):
                self.s.git_files(Path(directory),'a'*40,['src'])

    def test_production_environment_changes_only_git_io_controls(self):
        env={'PATH':'unchanged','GIT_NO_REPLACE_OBJECTS':'0','GIT_NO_LAZY_FETCH':'0',
             'GIT_TERMINAL_PROMPT':'1','CARGO_MAKEFLAGS':'untouched-advertisement',
             'TRUST_CPU_HANDOFF':'untouched-routing'}
        with patch.dict(os.environ,env,clear=True):actual=self.s._production_env()
        self.assertEqual(actual,{**env,'GIT_NO_REPLACE_OBJECTS':'1',
                                 'GIT_NO_LAZY_FETCH':'1','GIT_TERMINAL_PROMPT':'0'})

    def test_repository_local_context_is_removed_without_resource_changes(self):
        local=subprocess.check_output(['git','rev-parse','--local-env-vars']).decode().splitlines()
        selectors={name:'foreign Git context' for name in local}
        selectors.update(GIT_NAMESPACE='foreign namespace',GIT_CONFIG_KEY_0='core.worktree',
                         GIT_CONFIG_VALUE_0='/foreign',GIT_CONFIG_COUNT='1')
        untouched={'PATH':'unchanged','CARGO_MAKEFLAGS':'untouched advertisement',
                   'ATERM_SDK_LEASE_V3':'untouched descriptor',
                   'ATERM_WORKLOAD_CPU_FDS_V1':'untouched transport',
                   'TRUST_CPU_IMPLICIT_FD':'untouched descriptor',
                   'GIT_CONFIG_NOSYSTEM':'1'}
        with patch.dict(os.environ,{**selectors,**untouched},clear=True):
            actual=self.s._production_env()
        self.assertEqual(actual,{**untouched,'GIT_NO_REPLACE_OBJECTS':'1',
                                 'GIT_NO_LAZY_FETCH':'1','GIT_TERMINAL_PROMPT':'0'})

    def test_authentication_cannot_be_shadowed_by_introspection(self):
        command=[sys.executable,'-B',str(SCRIPT),'--authenticate-production','--pinned-inputs']
        child=subprocess.run(command,capture_output=True,text=True)
        self.assertEqual(child.returncode,2,child.stdout+child.stderr)
        self.assertIn('not allowed with argument',child.stderr)
        self.assertEqual(child.stdout,'')

    def test_capture_cannot_shadow_authentication(self):
        child=subprocess.run([sys.executable,'-B',str(SCRIPT),'--capture-production',
                              '--authenticate-production'],capture_output=True,text=True)
        self.assertEqual(child.returncode,2,child.stdout+child.stderr)
        self.assertIn('not allowed with argument',child.stderr)

    def test_standalone_pinned_inputs_stays_a_query(self):
        child=subprocess.run([sys.executable,'-B',str(SCRIPT),'--pinned-inputs'],
                             capture_output=True,text=True)
        self.assertEqual(child.returncode,0,child.stderr)
        self.assertIn('scripts/test_ck0_production_batch.py',child.stdout.splitlines())


class RealCommittedInventory(unittest.TestCase):
    def setUp(self):
        self.s=subject();self.temp=tempfile.TemporaryDirectory(prefix='q6-git-batch-')
        self.addCleanup(self.temp.cleanup);self.root=Path(self.temp.name)
        self.git('init','-q');self.git('config','user.name','Batch fixture')
        self.git('config','user.email','batch@example.invalid')
        self.files={'src/plain':b'shared','src/duplicate':b'shared','src/empty':b'',
                    'src/ executable ':b'#!/bin/sh\nexit 0\n','src/tab\tname':b'tab',
                    'src/line\nname':b'line','src/quote"slash\\name':b'quote',
                    'src/λ':b'\x00\n\xff'}
        for path,data in self.files.items():
            f=self.root/path;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(data)
        (self.root/'src/ executable ').chmod(0o755)
        self.git('add','--','src');self.git('commit','-qm','committed fixture')
        self.revision=self.git('rev-parse','HEAD').decode().strip()

    def git(self,*args):
        return subprocess.check_output(['git','-C',str(self.root),*args],stderr=subprocess.PIPE)

    def expected(self):return {p:hashlib.sha256(data).hexdigest() for p,data in self.files.items()}

    def test_literal_paths_regular_modes_and_shared_content(self):
        self.assertEqual(self.s.git_files(self.root,self.revision,['src','.cargo']),self.expected())

    def test_exact_two_git_processes_and_unique_oid_requests(self):
        actual_run=subprocess.run;calls=[]
        def observe(argv,**kwargs):
            calls.append((argv,kwargs.get('input')));return actual_run(argv,**kwargs)
        with patch.object(self.s.subprocess,'run',side_effect=observe):
            self.assertEqual(self.s.git_files(self.root,self.revision,['src']),self.expected())
        self.assertEqual(len(calls),2)
        self.assertIn('--batch',calls[1][0])
        requests=calls[1][1].decode().splitlines()
        self.assertEqual(len(requests),len(set(oid(data) for data in self.files.values())))
        self.assertLess(len(requests),len(self.files))

    def test_worktree_edits_do_not_enter_committed_inventory(self):
        (self.root/'src/plain').write_bytes(b'changed')
        (self.root/'src/untracked').write_bytes(b'untracked')
        self.assertEqual(self.s.git_files(self.root,self.revision,['src']),self.expected())

    def test_no_persistent_cache_across_revisions(self):
        self.s.git_files(self.root,self.revision,['src'])
        self.files['src/plain']=b'new committed bytes';(self.root/'src/plain').write_bytes(self.files['src/plain'])
        self.git('add','--','src/plain');self.git('commit','-qm','second')
        self.assertEqual(self.s.git_files(self.root,'HEAD',['src']),self.expected())

    def test_selected_symlink_refuses(self):
        (self.root/'src/link').symlink_to('plain');self.git('add','--','src/link')
        self.git('commit','-qm','symlink')
        with self.assertRaisesRegex(ValueError,'non-regular'):
            self.s.git_files(self.root,'HEAD',['src'])

    def test_empty_prefix_refuses(self):
        with self.assertRaisesRegex(ValueError,'empty'):
            self.s.git_files(self.root,'HEAD',['absent'])

    def test_replacement_blob_and_commit_are_ignored(self):
        original_oid=self.git('rev-parse','HEAD:src/plain').decode().strip()
        (self.root/'replacement').write_bytes(b'forged replacement')
        replacement=self.git('hash-object','-w','replacement').decode().strip()
        self.git('replace',original_oid,replacement)
        self.assertEqual(self.s.git_files(self.root,self.revision,['src']),self.expected())
        self.files['src/plain']=b'new commit';(self.root/'src/plain').write_bytes(self.files['src/plain'])
        self.git('add','--','src/plain');self.git('commit','-qm','new tree')
        newer=self.git('rev-parse','HEAD').decode().strip()
        self.git('replace',self.revision,newer)
        historical={**self.expected(),'src/plain':hashlib.sha256(b'shared').hexdigest()}
        self.assertEqual(self.s.git_files(self.root,self.revision,['src']),historical)
        self.assertEqual(self.s._production_git(self.root,'show',self.revision+':src/plain'),b'shared')


class ProductionCommitIdentity(unittest.TestCase):
    """Real private Git repositories; source metadata only, no Cargo/Rust."""
    def setUp(self):
        self.s=subject();self.temp=tempfile.TemporaryDirectory(prefix='q6-production-commits-')
        self.addCleanup(self.temp.cleanup);self.root=Path(self.temp.name)
        self.clean=self.root/'clean';self.ty=self.root/'ty';self.trust=self.root/'trust'
        for repo in [self.clean,self.ty,self.trust]:
            repo.mkdir();self.git(repo,'init','-q','-b','main')
            self.git(repo,'config','user.name','Commit fixture')
            self.git(repo,'config','user.email','commit@example.invalid')
        self.write(self.clean,{'crates/clean-ck0/Cargo.toml':'[package]\nname="fixture"\n',
                              'crates/clean-ck0/src/lib.rs':'// uncompiled source fixture\n'})
        self.write(self.ty,{'crates/tla-check/Cargo.toml':'''[dependencies.clean-ck0]
workspace=true
optional=true
[features]
clean-cic=["dep:clean-kernel","dep:clean-ck0"]
''','crates/tla-check/src/lib.rs':'// uncompiled fixture\n',
            'crates/tla-check/src/ck0_bridge.rs':'// uncompiled fixture bridge\n'})
        manifest='''[dependencies.tla-check]
path="../../first-party/ty/crates/tla-check"
default-features=false
features=["im","bumpalo","clean-cic"]
[patch."https://github.com/alabsystems/clean.git".clean-ck0]
path="../../first-party/clean/crates/clean-ck0"
'''
        for name,suffix in [('num-bigint','bigint'),('num-integer','integer'),('num-traits','traits')]:
            manifest+=f'[patch.crates-io.{name}]\npath="../../first-party/ty/crates/tla-bignum/{suffix}"\n'
        lock='''[[package]]
name="clean-ck0"
version="0.0.0"
[[package]]
name="tla-check"
version="0.0.0"
dependencies=["clean-ck0"]
'''
        self.write(self.trust,{'crates/trust-spec-temporal/Cargo.toml':manifest,
                              'crates/trust-spec-temporal/Cargo.lock':lock,
                              'crates/trust-spec-temporal/src/lib.rs':'// uncompiled fixture\n'})
        self.links={name:self.git(repo,'rev-parse','HEAD').decode().strip()
                    for name,repo in [('clean',self.clean),('ty',self.ty)]}
        for name,key in self.links.items():self.set_link(name,key)
        self.git(self.trust,'commit','-qm','production gitlinks')
        self.commit=self.git(self.trust,'rev-parse','HEAD').decode().strip()

    def git(self,repo,*args):
        return subprocess.check_output(['git','-C',str(repo),*args],stderr=subprocess.PIPE)

    def write(self,repo,files):
        for path,text in files.items():
            p=repo/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
        self.git(repo,'add','-A');self.git(repo,'commit','-qm','fixture')

    def set_link(self,name,key):
        self.git(self.trust,'update-index','--add','--cacheinfo',f'160000,{key},first-party/{name}')

    def record(self,ref=None):return self.s.production_record(self.trust,self.ty,self.clean,ref or self.commit)

    def test_named_repository_wins_over_ambient_git_dir(self):
        foreign=self.git(self.clean,'rev-parse','HEAD').decode().strip()
        self.assertNotEqual(foreign,self.commit)
        with patch.dict(os.environ,{'GIT_DIR':str(self.clean/'.git')}):
            actual=self.s._production_commit(self.trust,'HEAD')
        self.assertEqual(actual,self.commit)

    def test_full_record_and_authentication_ignore_foreign_repository_context(self):
        expected=self.record()
        cases=[{'GIT_DIR':str(self.clean/'.git')},
               {'GIT_COMMON_DIR':str(self.clean/'.git')},
               {'GIT_OBJECT_DIRECTORY':str(self.clean/'.git/objects')},
               {'GIT_DIR':str(self.ty/'.git'),'GIT_WORK_TREE':str(self.clean),
                'GIT_INDEX_FILE':str(self.ty/'.git/index'),
                'GIT_CONFIG_COUNT':'1','GIT_CONFIG_KEY_0':'core.worktree',
                'GIT_CONFIG_VALUE_0':str(self.clean)}]
        for context in cases:
            with self.subTest(context=sorted(context)),patch.dict(os.environ,context):
                self.assertEqual(self.record('HEAD'),expected)
                self.s.authenticate_production(expected,self.trust,self.ty,self.clean)

    def test_worktree_repository_context_is_still_supported(self):
        worktree=self.root/'trust worktree'
        self.git(self.trust,'worktree','add','--detach',str(worktree),self.commit)
        with patch.dict(os.environ,{'GIT_DIR':str(self.clean/'.git')}):
            self.assertEqual(self.s._production_commit(worktree,'HEAD'),self.commit)
            self.assertEqual(self.s.production_record(worktree,self.ty,self.clean,'HEAD'),self.record())

    def test_commit_and_tag_reference_positives_are_identical(self):
        self.git(self.trust,'tag','lightweight');self.git(self.trust,'tag','-a','annotated','-m','fixture tag')
        expected=self.record();self.s.checked_production(expected)
        for ref in ['HEAD',self.commit,'lightweight','annotated','refs/heads/main','refs/tags/annotated']:
            with self.subTest(ref=ref):
                actual=self.record(ref);self.assertEqual(actual,expected)
                self.assertEqual(actual['trust_revision'],self.commit)
        self.s.authenticate_production(expected,self.trust,self.ty,self.clean)

    def test_same_content_root_tree_refuses(self):
        tree=self.git(self.trust,'rev-parse','HEAD^{tree}').decode().strip()
        with self.assertRaises(subprocess.CalledProcessError):self.record(tree)

    def test_blob_and_tree_tag_refs_refuse(self):
        blob=self.git(self.trust,'rev-parse','HEAD:crates/trust-spec-temporal/Cargo.toml').decode().strip()
        tree=self.git(self.trust,'rev-parse','HEAD^{tree}').decode().strip()
        self.git(self.trust,'tag','-a','tree-tag',tree,'-m','tree tag')
        for ref in [blob,'tree-tag']:
            with self.subTest(ref=ref),self.assertRaises(subprocess.CalledProcessError):self.record(ref)

    def test_missing_option_control_and_empty_refs_refuse(self):
        for ref in ['missing','0'*40,'--help','--verify','--end-of-options','HEAD\n','HEAD\0bad','']:
            with self.subTest(ref=ref),self.assertRaises((ValueError,subprocess.CalledProcessError)):
                self.s._production_commit(self.trust,ref)

    def test_ambiguous_ref_refuses_even_when_local_warning_disabled(self):
        self.git(self.trust,'branch','ambiguous');self.git(self.trust,'tag','ambiguous')
        self.git(self.trust,'config','core.warnAmbiguousRefs','false')
        with self.assertRaisesRegex(ValueError,'Git diagnostics'):self.record('ambiguous')

    def test_tree_blob_and_annotated_tag_gitlinks_refuse_unpeeled(self):
        for name,repo in [('clean',self.clean),('ty',self.ty)]:
            self.git(repo,'tag','-a','gitlink-tag','-m','tag is not a commit')
            blob_path='crates/clean-ck0/src/lib.rs' if name=='clean' else 'crates/tla-check/src/lib.rs'
            keys=[self.git(repo,'rev-parse',expr).decode().strip()
                  for expr in ['HEAD^{tree}','HEAD:'+blob_path,'gitlink-tag']]
            for key in keys:
                with self.subTest(repo=name,key=key):
                    self.set_link(name,key);self.git(self.trust,'commit','-qm','noncommit gitlink')
                    with self.assertRaisesRegex(ValueError,'not an exact commit'):self.record('HEAD')
                    self.set_link(name,self.links[name]);self.git(self.trust,'commit','-qm','restore gitlink')

    def test_gitlink_commit_absent_from_named_repository_refuses(self):
        for name,repo in [('clean',self.clean),('ty',self.ty)]:
            with self.subTest(repo=name):
                self.set_link(name,self.commit);self.git(self.trust,'commit','-qm','foreign commit')
                with self.assertRaises(subprocess.CalledProcessError) as error:self.record('HEAD')
                self.assertEqual(error.exception.cmd[2],str(repo))
                self.set_link(name,self.links[name]);self.git(self.trust,'commit','-qm','restore gitlink')

    def test_malformed_commit_probe_output_refuses(self):
        for raw in [self.commit.encode(),(self.commit+'\n\n').encode(),
                    (' '+self.commit+'\n').encode(),(self.commit.upper()+'\n').encode(),
                    b'a'*64+b'\n',(self.commit+'\n'+self.commit+'\n').encode()]:
            with self.subTest(raw=raw),patch.object(self.s,'_production_git',return_value=raw),\
                 self.assertRaisesRegex(ValueError,'Trust commit identity'):
                self.s._production_commit(self.trust,'HEAD')

    def test_malformed_gitlink_rows_refuse(self):
        real=self.s._production_git;key=self.links['clean'].encode();path=b'first-party/clean'
        valid=b'160000 commit '+key+b'\t'+path+b'\0'
        cases=[b'',valid[:-1],valid+valid,b'160000 commit '+key+b'\twrong/path\0',
               b'040000 tree '+key+b'\t'+path+b'\0',
               b'160000 commit '+b'a'*64+b'\t'+path+b'\0']
        for raw in cases:
            def read(repo,*args,**kwargs):
                return raw if args[0]=='ls-tree' and '-z' in args else real(repo,*args,**kwargs)
            with self.subTest(raw=raw),patch.object(self.s,'_production_git',side_effect=read),\
                 self.assertRaisesRegex(ValueError,'malformed production gitlink'):self.record()

    def test_gitlink_type_probe_requires_exact_commit_line(self):
        real=self.s._production_git
        for raw in [b'commit',b'commit\n\n',b'commit\r\n',b'tag\n']:
            def read(repo,*args,**kwargs):
                return raw if args[:2]==('cat-file','-t') else real(repo,*args,**kwargs)
            with self.subTest(raw=raw),patch.object(self.s,'_production_git',side_effect=read),\
                 self.assertRaisesRegex(ValueError,'not an exact commit'):self.record()

    def test_actual_nonzero_and_warning_commit_probes_refuse(self):
        # Git-shaped process is an inert transport fixture, never a source answer.
        script=self.root/'probe.py';binary=self.root/'git'
        binary.write_text('#!/bin/sh\nexec '+shlex.quote(sys.executable)+' '+shlex.quote(str(script))+' "$@"\n');binary.chmod(0o700)
        for status,stderr,error in [(17,'',subprocess.CalledProcessError),(0,'fixture diagnostic',ValueError)]:
            script.write_text('import sys\nsys.stdout.write('+repr(self.commit+'\n')+')\nsys.stderr.write('+repr(stderr)+')\nraise SystemExit('+str(status)+')\n')
            with self.subTest(status=status),patch.dict(os.environ,{'PATH':str(self.root)+os.pathsep+os.environ.get('PATH','')}),\
                 self.assertRaises(error):self.s._production_commit(self.trust,'HEAD')


if __name__=='__main__':unittest.main()
