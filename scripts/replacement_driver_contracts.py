# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Offline, revision-guarded contracts for the two pinned Lean test drivers.

This is not a Lean evaluator. Directive selection follows the driver's string
operations, including markers inside strings/comments and byte-based columns.
Response-dependent requests remain symbolic and require execution.
"""
import hashlib
from pathlib import PurePosixPath
import re

RUNNER = 'src/Lean/Server/Test/Runner.lean'
DOC = 'tests/docparse/run_test.lean'
SERVER = 'tests/server_interactive/run_test.lean'
IPC = 'src/Lean/Data/Lsp/Ipc.lean'
PINS = {
    IPC: '3e16086d5ea9dd3bc1f7479e4241c09c5ef78204',
    DOC: '4a16e659a519ecea6b928b944156302f4a310b59',
    SERVER: 'a8927a2bfa07651dd5ae91ae96101cf47c23125e',
    RUNNER: 'a9f5df3c760826bac21e5719bac746d9ad661c0b',
}


def blob(text):
    raw = text.encode()
    return hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()


def require(path, sources):
    if path not in sources:
        raise ValueError('driver source not archived: ' + path)
    if path in PINS and blob(sources[path]) != PINS[path]:
        raise ValueError('unreviewed driver grammar: ' + path)
    return sources[path]


def evidence(path, sources, targets, start=0, end=None):
    text = require(path, sources)
    if end is None:
        end = len(text)
    return dict(path=path, **targets[path], sha256=hashlib.sha256(text.encode()).hexdigest(),
                byte_range=[len(text[:start].encode()), len(text[:end].encode())],
                lines=[text.count('\n', 0, start) + 1, text.count('\n', 0, end) + 1],
                source=text[start:end])


def definitions(text):
    matches = list(re.finditer(r'^(?:partial )?def ([A-Za-z_][\w.]*)\b', text, re.M))
    return {m[1]: (m.start(), matches[i + 1].start() if i + 1 < len(matches) else len(text))
            for i, m in enumerate(matches)}


def import_records(text):
    # Header statements only; keep their literal spelling. No transitive closure claim.
    # Mask nested block comments, strings, and line comments before recognizing lines.
    out = list(text); i = 0; depth = 0; string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth += 1; n = 2
            elif text.startswith('-/', i): depth -= 1; n = 2
            else: n = 1
        elif string:
            if text[i] == '\\': n = min(2, len(text) - i)
            else:
                if text[i] == '"': string = False
                n = 1
        elif text.startswith('/-', i): depth = 1; n = 2
        elif text.startswith('--', i):
            end = text.find('\n', i); n = (len(text) if end < 0 else end) - i
        elif text[i] == '"': string = True; n = 1
        else: i += 1; continue
        for j in range(i, i + n):
            if out[j] != '\n': out[j] = ' '
        i += n
    masked = ''.join(out)
    return [dict(line=masked.count('\n', 0, m.start()) + 1, declaration=m[0].strip())
            for m in re.finditer(r'^[ \t]*(?:(?:public|private|meta)\s+)*import\s+[^\n]+', masked, re.M)]


def server_directives(text, handlers):
    sessions = []
    offset = 0
    for session_no, segment in enumerate(text.split('-- RESET')):
        last_actual = 0; synced = True; version = 2; steps = []
        for line_no, line in enumerate(segment.split('\n')):
            parts = line.split('--')
            if len(parts) != 2 or not parts[1] or parts[1][0] not in ('^', 'v', '⬑'):
                last_actual = line_no
                continue
            ws, directive = parts
            marker = directive[0]
            method, colon, params = directive[1:].partition(':')
            # Lean trimAscii, not Python's broader Unicode whitespace trim.
            method = method.strip(' \t\r\n\v\f')
            params = params.strip(' \t\r\n\v\f') if colon else '{}'
            target = line_no + 1 if marker == 'v' else last_actual
            step = dict(ordinal=len(steps), session_line=line_no, source_byte_offset=offset + len(segment[:sum(len(x) + 1 for x in segment.split('\n')[:line_no])].encode()),
                        raw_line=line, marker=marker, method=method, params=params,
                        position=dict(line=target, character=len(ws.encode()) + (0 if marker == '⬑' else 2)),
                        handler=handlers.get(method, 'processGenericRequest'), plan_condition='all prior directives complete successfully', version_before=version,
                        synced_before=synced)
            if method in ('delete', 'insert', 'change'):
                step['execution_precondition'] = 'synced; Lean Syntax.decodeStrLit; change splits on literal space into exactly two arguments'
                step['statically_unsynced_edit'] = not synced
                version += 1; synced = False
            elif method in ('sync', 'collectDiagnostics', 'waitFor'):
                synced = True
            steps.append(step)
        sessions.append(dict(index=session_no, source_byte_offset=offset,
            open=dict(method='textDocument/didOpen', version=1, text=segment),
            initial_state=dict(synced=True, versionNo=2, rpcSessionId=None, lineNo=0, lastActualLineNo=0),
            directives=steps, finalization=['collectDiagnostics(requestNo, uri, versionNo - 1)', 'advanceRequestNo', 'textDocument/didClose']))
        offset += len(segment.encode()) + len('-- RESET')
    return sessions


def driver_contract(path, driver, sources, targets):
    text = require(path, sources)
    driver_text = require(driver, sources)
    contract = dict(schema='clean-source-driver-contract-v1', input=evidence(path, sources, targets),
        driver=evidence(driver, sources, targets),
        invocation=dict(cwd=str(PurePosixPath(path).parent), argv=['lean', '-Dlinter.all=false', '--run', 'run_test.lean', PurePosixPath(path).name]),
        environment=dict(ASAN_OPTIONS='detect_leaks=0', stage='configured upstream stage', TEST_CTEST='1 under CTest',
            configured_variables=['LEAN_TEST_VARS', 'STAGE', 'SRC_DIR', 'TEST_DIR', 'BUILD_DIR', 'SCRIPT_DIR', 'PATH=stage bin before inherited PATH', 'LEANC_OPTS', 'CXX'],
            platform_condition='CMake WIN32 rewrites drive-letter paths for bash; see pinned catalog'),
        catalog_environment=evidence('tests/CMakeLists.txt', sources, targets),
        imports=dict(state='direct-header-statements; transitive closure requires module resolution',
                     input=import_records(text) if path.endswith('.lean') else [], driver=import_records(driver_text)),
        measured=False)
    if driver == DOC:
        configs = driver_text.split('def testConfigs', 1)[1].split('\ndef main', 1)[0]
        entries = list(re.finditer(r'^  \("([^"]+)",', configs, re.M))
        table = {}
        for i, m in enumerate(entries):
            expression = configs[m.end():entries[i+1].start() if i+1 < len(entries) else configs.rfind(']')].strip()
            table[m[1]] = expression.removesuffix(',').rstrip().removesuffix(')').rstrip()
        kind = PurePosixPath(path).name.split('_', 1)[0]
        contract.update(kind='docparse', selector=dict(rule='filename.takeWhile(character != underscore)', key=kind,
            parser_expression=table.get(kind)),
            subcases=[dict(id='parse-input', input=path, parser_expression=table.get(kind),
                context=dict(filename='<input>', environment='mkEmptyEnvironment', options={}, token_table='getTokenTable env', parser_state='mkParserState input'),
                observation=['run selected ParserFn once over complete input', 'ppStack final syntax stack; format width 50, nest 2',
                    'success: final stack and all-input-consumed or remaining suffix',
                    'one error: byte position, file-map position, message, stack and suffix',
                    'multiple errors: sort by position then error text; emit count/errors/stack'])],
            argument_failures={'arity':1, 'absolute_path':2, 'missing_file':3, 'not_one_component':4, 'unknown_selector':5},
            dynamic_expansion_required=False,
            execution_requirements=['execute selected Lean.DocString.Parser ParserFn to obtain syntax/errors/output; compare pinned output policy',
                                    'resolve transitive Lean.DocString.Parser imports'])
        if kind not in table:
            contract['subcases'] = []
            contract['expected_driver_exit'] = 5
        else:
            contract['expected_driver_exit'] = 0
    elif driver == SERVER:
        runner = require(RUNNER, sources); defs = definitions(runner)
        ipc = require(IPC, sources)
        dispatch = runner[slice(*defs['processDirective'])]
        handlers = {}
        for m in re.finditer(r'^  \| ((?:"[^"]+"\s*(?:\|\s*)?)+) => (\w+)', dispatch, re.M):
            for name in re.findall(r'"([^"]+)"', m[1]): handlers[name] = m[2]
        sessions = server_directives(text, handlers)
        used = sorted({s['handler'] for session in sessions for s in session['directives']})
        # Include full helper definitions, retaining symbolic response loops and option branches.
        dynamic = []
        for session in sessions:
            for step in session['directives']:
                method, params = step['method'], step['params']
                reason = None
                if method in ('completion', 'codeAction', 'widgets'):
                    reason = {'completion':'resolve each returned item with data',
                              'codeAction':'resolve each returned action with data',
                              'widgets':'request source for each returned widget'}[method]
                elif method == 'goals' and params in ('withPopups', 'withGoToLoc'):
                    reason = 'iterate returned goals/hypotheses/tagged subtrees for ' + params
                elif method == 'interactiveDiagnostics' and (params == 'expandTraces' or params.startswith('highlightMatches:')):
                    reason = 'expand returned lazy trace children recursively' if params == 'expandTraces' else 'highlight each returned diagnostic'
                elif method in ('incomingCallHierarchy', 'outgoingCallHierarchy', 'moduleHierarchyImports', 'moduleHierarchyImportedBy'):
                    reason = 'recursively expand response-dependent hierarchy with visited-item cycle detection; pinned Ipc source defines traversal'
                if reason:
                    dynamic.append(dict(session=session['index'], directive=step['ordinal'], method=method, reason=reason))
        helper_names = sorted(set(used) | {'processDirective', 'processLine', 'main', 'reset', 'request',
            'rpcRequest', 'requestWithLoggedResponse', 'rpcRequestWithLoggedResponse', 'logResponse',
            'logRpcResponse', 'printOutputLn', 'patchUri', 'patchUris', 'waitForMessage', 'expandTraces'})
        contract.update(kind='interactive-server', runner=evidence(RUNNER, sources, targets), ipc=evidence(IPC, sources, targets),
            imports=dict(contract['imports'], runner=import_records(runner), ipc=import_records(ipc)),
            directive_grammar=dict(session_separator='-- RESET', line_separator='newline', line_selection='exactly two components after splitting on --; second starts immediately with ^, v, or ⬑', method='remove marker; trimAscii before first colon', params='trimAscii after first colon, otherwise {}', target='v: next line; ^/⬑: last non-directive line; ⬑ column is marker start; other columns after --; UTF-8 byte offsets'),
            sessions=sessions, directive_count=sum(len(x['directives']) for x in sessions),
            handler_contracts={name:evidence(RUNNER, sources, targets, *defs[name]) for name in helper_names},
            server_invocation=dict(command='lean', args=['--server', '-DstderrAsMessages=false', '-Dexperimental.module=true'],
                alternative=dict(condition='first driver argument == -p (not selected by this shell runner)', command='lake', args=['serve','--','-DstderrAsMessages=false','-Dexperimental.module=true'])),
            initialization=dict(request_id=0, method='initialize', hasWidgets=True, insertReplaceSupport=True,
                incrementalDiagnosticSupport=True, silentDiagnosticSupport=True, rpcWireFormat='v1', followed_by='initialized'),
            state_rules=['requestNo starts at 1; request increments it; reset preserves it across sessions',
                'RPC connect is lazy per session; request/response IDs and session IDs are runtime values',
                'waitForILeans does not set synced; sync/collectDiagnostics/waitFor do',
                'edits do not adjust later source directive positions; columns count UTF-8 bytes',
                'shutdown(requestNo), waitForExit after all sessions'],
            dynamic_expansion_required=bool(dynamic), dynamic_expansion=dynamic,
            execution_requirements=['run IPC server to resolve responses, diagnostics, RPC references and session IDs',
                'expand response-dependent completion/codeAction resolutions, widget sources, trace children, goal popups/go-to and hierarchy recursion when selected',
                'resolve generic JSON parameter parse/type failures and edit string decoding in Lean',
                'resolve transitive input/driver/runner imports and configured stage paths'],
            output_normalization=['patch file URIs using realPath and deepest /src/Init/, /src/Lean/, /src/Std/, /tests/misc_dir/ match',
                'Ipc diagnostic accumulation: incremental append, nonincremental replacement, then range/message sort',
                'interactive diagnostic sort and RPC-reference normalization as retained in runner source',
                'shell normalize_mvar_suffixes and normalize_reference_urls'])
    else:
        raise ValueError('unknown driver: ' + driver)
    return contract
