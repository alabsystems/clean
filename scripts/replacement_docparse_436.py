# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Source contracts for the exact reviewed Lean 4.36 docparse driver.

The caller checks the complete Git blob before reaching this extractor. The
extractor records parser calls, validation and directory batches; it executes
none of those operations and grants no output or compatibility verdict.
"""
from pathlib import PurePosixPath
import re


def mask_noncode(text):
    """Keep offsets while blanking nested comments and escaped strings."""
    out = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1; n = 2
            elif text.startswith('-/', i):
                depth -= 1; n = 2
            else:
                n = 1
        elif string:
            if text[i] == '\\':
                n = min(2, len(text) - i)
            else:
                if text[i] == '"':
                    string = False
                n = 1
        elif text.startswith('/-', i):
            depth = 1; n = 2
        elif text.startswith('--', i):
            end = text.find('\n', i); n = (len(text) if end < 0 else end) - i
        elif text[i] == '"':
            string = True; n = 1
        else:
            i += 1
            continue
        for j in range(i, i + n):
            if out[j] != '\n':
                out[j] = ' '
        i += n
    if depth or string:
        raise ValueError('unfinished docparse comment or string')
    return ''.join(out)


def test_configs(text):
    masked = mask_noncode(text)
    marker = 'def testConfigs : List (String × ParserFn × Bool) := ['
    if masked.count(marker) != 1:
        raise ValueError('changed docparse configuration declaration')
    start = masked.index(marker) + len(marker)
    depth, stop = 1, None
    for i in range(start, len(masked)):
        if masked[i] == '[':
            depth += 1
        elif masked[i] == ']':
            depth -= 1
            if depth == 0:
                stop = i
                break
    if stop is None:
        raise ValueError('unclosed docparse configuration array')
    body = text[start:stop]
    matches = list(re.finditer(r'^  \("([^"\n]+)",', body, re.M))
    if not matches or body[:matches[0].start()].strip():
        raise ValueError('unclassified docparse configuration prefix')
    configs = {}
    for index, match in enumerate(matches):
        segment = body[match.end():matches[index+1].start() if index+1 < len(matches) else len(body)]
        suffix = re.search(r',\s*(true|false)\),\s*$', segment)
        if not suffix or match[1] in configs:
            raise ValueError('unclassified or duplicate docparse configuration')
        expression = segment[:suffix.start()].strip()
        if not expression:
            raise ValueError('empty docparse parser expression')
        configs[match[1]] = dict(parser_expression=expression, validate_source_info=suffix[1] == 'true')
    return configs


def directory_dispatch(text):
    main = text.split('\ndef main : List String → IO UInt32\n', 1)
    if len(main) != 2:
        raise ValueError('changed docparse main declaration')
    pairs = re.findall(r'    if kind == "([^"\n]+)" then\n      return \(← (\w+)\)', main[1])
    dispatch = dict(pairs)
    expected = {'coverage': 'coverage', 'format': 'formatRoundTrip', 'nodeinfo': 'nodeInfo', 'blankPara': 'blankParagraphs'}
    if len(pairs) != len(expected) or dispatch != expected:
        raise ValueError('unreviewed docparse directory dispatch')
    return dispatch


def docparse_contract(contract, path, driver_text, sources, targets):
    configs = test_configs(driver_text)
    dispatch = directory_dispatch(driver_text)
    key = PurePosixPath(path).name.split('_', 1)[0]
    contract.update(kind='docparse', selector=dict(rule='filename.takeWhile(character != underscore)', key=key),
        argument_failures={'arity': 1, 'absolute_path': 2, 'missing_file': 3, 'not_one_component': 4, 'unknown_selector': 5},
        driver_revision_contract='v4.36.0 docparse; triple configuration and four directory checks',
        output_transport='IO.println (adds a final newline); failures inside test output do not alter main exit0',
        execution_requirements=['execute authentic parser/view/source-info/formatter functions to obtain output; compare pinned output policy',
            'resolve transitive Lean.DocString.Parser/View/Formatter imports'],
        dynamic_expansion_required=False)
    if key in dispatch:
        directory = str(PurePosixPath(path).parent)
        inputs = sorted(p for p in targets if str(PurePosixPath(p).parent) == directory and p.endswith('.txt'))
        if not inputs or any(p not in sources for p in inputs):
            raise ValueError('missing docparse directory batch inputs')
        checks = {
            'coverage': ['read directory .txt in filesystem order; select filename prefix in testConfigs',
                'run selected parser in empty environment; keep syntax from error-free parses',
                'collect syntax node kinds; require all Parser.documentKinds covered and all seen kinds builtin',
                'print missing/nonbuiltin kinds; return1 if either check fails, else0'],
            'format': ['sort .txt filenames lexically; parseDocument; skip errors and empty block arrays',
                'compare summarizeBlock arrays before and after versoDocumentToString and reparsing',
                'record formatted parse failures or different decoded document; print counts and failures; return1 iff failures'],
            'nodeinfo': ['sort .txt filenames lexically; parseDocument; skip parse errors',
                'find first syntax node with its own non-none source info in each block',
                'print checked count and failures; return1 iff any node has its own source info'],
            'blankPara': ['sort .txt filenames lexically; parseDocument; skip parse errors',
                'find paragraph whose InlineView source text contributes only whitespace; escaped text remains content',
                'print checked count and failures; return1 iff any empty-content paragraph'],
        }
        contract.update(kind='docparse-directory-check', directory_inputs=inputs,
            selector=dict(contract['selector'], entry_point=dispatch[key]),
            input_scope='all immediate .txt files of exact frozen directory, not just dispatch filename',
            subcases=[dict(id='directory-batch', candidate_inputs=inputs, operations=checks[key],
                selection='runtime parser success and syntax predicates, as retained in complete driver source')],
            dynamic_expansion_required=True,
            dynamic_expansion=[dict(reason='runtime parsing filters directory inputs; aggregate counts/failure vectors and coverage require actual execution')],
            expected_driver_exit='0 if batch checks pass;1 if any fail',
            output_transport='batch prints its own lines; main returns batch exit without ordinary test printing')
        contract['execution_requirements'] += ['materialize exact frozen .txt working directory with no extra files',
            'execute symbolic parser-dependent batch filters and global aggregation; no fixture-count pass inference']
        return contract
    config = configs.get(key)
    contract['selector']['parser_expression'] = config and config['parser_expression']
    if config is None:
        contract.update(subcases=[], expected_driver_exit=5)
        return contract
    validation = dict(enabled=config['validate_source_info'], region='[0, parser final position] of mkInputContext-normalized input',
        stack_preparation='setStartLeading 0 (mkNullNode parser stack)',
        checks=['node source info none', 'original leaf info and exact text/ranges', 'ordered non-overlapping leaves',
            'whitespace exactly fills token gaps', 'leading whitespace only on first leaf', 'Syntax.reprint reproduces checked region'],
        outcomes=['Round-trip OK', 'no tokens: skipped because doc comment records whitespace',
            'partial/error parse: failure to reproduce is reported as recovery', 'successful parse: explicit Round-trip FAILED',
            'validation disabled: parser classifies or discards syntax'])
    contract.update(expected_driver_exit=0, source_info_validation=validation,
        subcases=[dict(id='parse-input', input=path, parser_expression=config['parser_expression'],
            context=dict(filename='<input>', environment='mkEmptyEnvironment', options={}, token_table='getTokenTable env', parser_state='mkParserState input'),
            observation=['normalize line endings using mkInputContext and print Input repr',
                'run selected ParserFn over complete input; ppStack final stack width50/nest2',
                'print all-input-consumed or remaining suffix; flag syntax reaching beyond consumed input',
                'run configured source-info validation over consumed region, including partial recovery output',
                'success: decoded views; one error: range/carets/consumed byte prefix; multiple errors: position/text sorted diagnostics'])])
    return contract
