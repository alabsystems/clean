"""Observed Q6 input endpoints; no continuous or hermetic-read claim."""
import hashlib
import json
import os
from pathlib import Path
import stat
import tempfile

RUN_SCHEMA = 'clean.ck0-input-qualification/v2'
SNAPSHOT_SCHEMA = 'clean.ck0-input-snapshot/v1'
PHASES = ('before', 'after-default', 'after-export', 'after-binary')


def need(ok, reason):
    if not ok:
        raise ValueError(reason)


def encoded(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def file_identity(path, data=None):
    path = Path(path).resolve(strict=True)
    need(path.is_file(), f'not a regular input: {path}')
    data = path.read_bytes() if data is None else data
    return {'path': str(path), 'sha256': sha(data), 'bytes': len(data)}


def tree_inventory(root, exclude_git=False):
    """Include legitimate target/ directories; refuse untraversed directory links."""
    root = Path(root).resolve(strict=True)
    need(root.is_dir(), f'not an input directory: {root}')
    files, links = {}, {}
    def traversal_error(error):
        raise error

    for directory, names, filenames in os.walk(root, followlinks=False, onerror=traversal_error):
        names.sort()
        filenames.sort()
        if exclude_git:
            names[:] = [name for name in names if name != '.git']
            filenames = [name for name in filenames if name != '.git']
        for name in names:
            need(not (Path(directory) / name).is_symlink(),
                 f'unsupported input directory symlink: {Path(directory) / name}')
        for name in filenames:
            path = Path(directory) / name
            relative = path.relative_to(root).as_posix()
            need(stat.S_ISREG(path.stat().st_mode), f'non-regular input: {path}')
            if path.is_symlink():
                links[relative] = {'target': os.readlink(path),
                                   'resolved': str(path.resolve(strict=True))}
            files[relative] = sha(path.read_bytes())
    need(files, f'empty input directory: {root}')
    return {'root': str(root), 'files': files, 'links': links}


def config_candidates(root, cargo_home):
    root = Path(root).resolve()
    homes = [root, *root.parents]
    paths = {base / '.cargo' / name for base in homes for name in ('config', 'config.toml')}
    paths.update(Path(cargo_home) / name for name in ('config', 'config.toml'))
    return tuple(sorted(str(path.absolute()) for path in paths))


def reachable_metadata(document):
    """Conservative all-platform graph, including Cargo's dev/build edges."""
    packages = {package['id']: package for package in document['packages']}
    need(len(packages) == len(document['packages']), 'duplicate metadata package')
    roots = [package for package in packages.values() if package['name'] == 'clean-ck0']
    need(len(roots) == 1, 'metadata checker package census')
    root = roots[0]['id']
    nodes = {node['id']: node for node in document['resolve']['nodes']}
    need(len(nodes) == len(document['resolve']['nodes']), 'duplicate metadata node')
    visited, todo = set(), [root]
    while todo:
        key = todo.pop()
        if key in visited:
            continue
        need(key in packages and key in nodes, 'unresolved metadata package: ' + key)
        visited.add(key)
        todo.extend(nodes[key]['dependencies'])
    return {'root': root, 'targets': roots[0]['targets'],
            'packages': {key: {field: packages[key][field]
                              for field in ('manifest_path', 'source', 'version')}
                         for key in sorted(visited)},
            'nodes': {key: {'dependencies': sorted(nodes[key]['dependencies']),
                            'features': sorted(nodes[key]['features'])}
                      for key in sorted(visited)}}


def resolution_specs(resolution):
    need(set(resolution) == {'default', 'export'}, 'metadata context census')
    roots = {context['root'] for context in resolution.values()}
    need(len(roots) == 1, 'metadata checker package identity changed')
    root = next(iter(roots))
    specs = {}
    for context in resolution.values():
        need(set(context) == {'root', 'targets', 'packages', 'nodes'} and
             isinstance(context['targets'], list) and bool(context['targets']), 'metadata context shape')
        packages, nodes = context['packages'], context['nodes']
        need(isinstance(packages, dict) and isinstance(nodes, dict) and
             set(packages) == set(nodes) and root in packages, 'metadata graph census')
        reached, todo = set(), [root]
        while todo:
            key = todo.pop()
            if key in reached:
                continue
            need(key in packages, 'metadata edge outside package census')
            reached.add(key)
            node = nodes[key]
            need(set(node) == {'dependencies', 'features'} and all(
                isinstance(node[field], list) and node[field] == sorted(set(node[field])) and
                all(isinstance(value, str) for value in node[field])
                for field in ('dependencies', 'features')), 'metadata node shape')
            todo.extend(node['dependencies'])
        need(reached == set(packages), 'metadata unreachable package')
        for key, package in packages.items():
            need(isinstance(key, str) and bool(key) and set(package) == {'manifest_path', 'source', 'version'} and
                 isinstance(package['manifest_path'], str) and Path(package['manifest_path']).is_absolute() and
                 isinstance(package['version'], str) and bool(package['version']) and
                 (package['source'] is None or isinstance(package['source'], str) and bool(package['source'])),
                 'metadata package shape')
            if key != root:
                spec = {field: package[field] for field in ('manifest_path', 'source')}
                need(key not in specs or specs[key] == spec, 'metadata package identity differs by context')
                specs[key] = spec
    return root, specs


def capture_state(root, source_files, driver, compiler, version, sysroot,
                  resolution, cargo_home, producer_files, config_validator=None):
    root = Path(root).resolve()
    resolution = json.loads(encoded(resolution))
    _checker, specs = resolution_specs(resolution)
    dependencies, dependency_trees = {}, {}
    for key, spec in sorted(specs.items()):
        tree = tree_inventory(Path(spec['manifest_path']).parent, exclude_git=True)
        need(tree['root'] == str(Path(spec['manifest_path']).parent),
             'noncanonical dependency root')
        dependencies[key] = {**spec, 'files': tree['files']}
        dependency_trees[key] = {'root': tree['root'], 'links': tree['links']}
    configs = {}
    for name in config_candidates(root, cargo_home):
        path = Path(name)
        try:
            path.lstat()
        except FileNotFoundError:
            configs[name] = None
            continue
        need(stat.S_ISREG(path.stat().st_mode), f'non-regular configuration input: {path}')
        data = path.read_bytes()
        if config_validator is not None:
            config_validator(data)
        configs[name] = file_identity(path, data)
    sysroot = Path(sysroot).resolve(strict=True)
    library = tree_inventory(sysroot / 'lib')
    return {'source_root': str(root), 'cargo_home': str(Path(cargo_home).resolve()),
            'source_files': dict(source_files), 'compiler': file_identity(compiler),
            'driver': file_identity(driver), 'version': version, 'sysroot': str(sysroot),
            'sysroot_files': {'lib/' + name: value for name, value in library['files'].items()},
            'sysroot_links': {'lib/' + name: value for name, value in library['links'].items()},
            'config_candidates': configs, 'resolution': resolution,
            'dependency_sources': dependencies, 'dependency_trees': dependency_trees,
            'producer_files': {name: sha((root / name).read_bytes()) for name in producer_files}}


def same_state(before, after):
    need(isinstance(before, dict) and isinstance(after, dict) and set(before) == set(after),
         'input snapshot field census changed')
    changed = [key for key in before if before[key] != after[key]]
    need(not changed, 'input snapshot changed: ' + ', '.join(changed))


def write_snapshot(output, phase, state, observed_at):
    need(phase in PHASES, 'snapshot phase')
    name = 'inputs-' + phase + '.json'
    data = encoded({'schema': SNAPSHOT_SCHEMA, 'phase': phase,
                    'observed_at': observed_at, 'state': state})
    (Path(output) / name).write_bytes(data)
    return {'file': name, 'sha256': sha(data)}


def read_bound_file(base, name, expected_sha):
    base = Path(base).resolve(strict=True)
    relative = Path(name)
    need(isinstance(name, str) and bool(name) and name == relative.as_posix() and
         not relative.is_absolute() and '..' not in relative.parts, 'snapshot archive path')
    path = base / relative
    need(all(not part.is_symlink() for part in (path, *path.parents) if part != base and base in part.parents),
         'snapshot archive symlink')
    need(path.resolve(strict=True).is_relative_to(base) and path.is_file(), 'snapshot archive escape')
    data = path.read_bytes()
    need(sha(data) == expected_sha, 'input snapshot digest: ' + name)
    return data


def selftest():
    """Mutate owned real files; never an installed compiler or shared cache."""
    from unittest import mock
    count = 0
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary).resolve()
        crate = root / 'crates/clean-ck0'
        dependency = root / 'dependency'
        for path in (crate / 'Cargo.toml', crate / 'src/lib.rs', dependency / 'Cargo.toml',
                     dependency / 'src/target/legitimate.rs', root / 'sdk/lib/stdlib',
                     root / 'compiler', root / 'driver', root / 'producer.py',
                     root / '.cargo/config.toml'):
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b'owned synthetic input')
        context = {'root': 'ck0', 'targets': [{'name': 'clean_ck0', 'kind': ['lib']}],
                   'packages': {key: {'manifest_path': str(path / 'Cargo.toml'), 'source': None, 'version': '1'}
                                for key, path in [('ck0', crate), ('dep', dependency)]},
                   'nodes': {'ck0': {'dependencies': ['dep'], 'features': []},
                             'dep': {'dependencies': [], 'features': []}}}

        def capture():
            return capture_state(root, {'crates/clean-ck0/src/lib.rs': sha((crate / 'src/lib.rs').read_bytes())},
                root / 'driver', root / 'compiler', 'synthetic; not executed', root / 'sdk',
                {'default': context, 'export': context}, root / '.cargo', ('producer.py',))

        before = capture()
        same_state(before, capture())
        need(before['config_candidates'][str(root / '.cargo/config')] is None,
             'genuinely missing config must remain absent')
        need('src/target/legitimate.rs' in before['dependency_sources']['dep']['files'],
             'legitimate target source omitted')

        def refuses(change, restore, reason='input snapshot changed'):
            nonlocal count
            change()
            try:
                try:
                    same_state(before, capture())
                except (ValueError, OSError) as error:
                    need(reason in str(error), 'wrong input stability refusal: ' + str(error))
                    count += 1
                else:
                    raise ValueError('input stability mutant accepted')
            finally:
                restore()
            same_state(before, capture())

        for path in (crate / 'src/lib.rs', dependency / 'src/target/legitimate.rs',
                     root / 'compiler', root / 'driver', root / 'sdk/lib/stdlib',
                     root / 'producer.py', root / '.cargo/config.toml'):
            original = path.read_bytes()
            refuses(lambda: path.write_bytes(b'changed'), lambda: path.write_bytes(original))
        for path in (dependency / 'added.rs', root / 'sdk/lib/added', root / '.cargo/config'):
            refuses(lambda: path.write_bytes(b'added'), path.unlink)
        for path in (dependency / 'src/target/legitimate.rs', root / 'sdk/lib/stdlib',
                     root / '.cargo/config.toml'):
            original = path.read_bytes()
            # Keep the sysroot nonempty while exercising deletion.
            (root / 'sdk/lib/retained').write_bytes(b'retained')
            before = capture()
            refuses(path.unlink, lambda: path.write_bytes(original))
        link = dependency / 'directory-link'
        refuses(lambda: link.symlink_to(crate, target_is_directory=True), link.unlink,
                'unsupported input directory symlink')
        link = dependency / 'file-link'
        link.symlink_to(crate / 'src/lib.rs')
        before = capture()
        refuses(lambda: (link.unlink(), link.symlink_to(root / 'compiler')),
                lambda: (link.unlink(), link.symlink_to(crate / 'src/lib.rs')))
        old = context['packages']['dep']['source']
        refuses(lambda: context['packages']['dep'].__setitem__('source', 'changed-source'),
                lambda: context['packages']['dep'].__setitem__('source', old))
        scandir = os.scandir

        def unreadable_directory(path):
            if Path(path) == dependency / 'src/target':
                raise PermissionError('fixture nested traversal denied')
            return scandir(path)

        with mock.patch.object(os, 'scandir', unreadable_directory):
            try:
                capture()
            except PermissionError as error:
                need('fixture nested traversal denied' in str(error), 'wrong traversal refusal')
                count += 1
            else:
                raise ValueError('incomplete traversal accepted as snapshot')
        same_state(before, capture())
        lstat = Path.lstat
        config = root / '.cargo/config.toml'

        def unreadable_config(path, *args, **kwargs):
            if path == config:
                raise PermissionError('fixture config lstat EACCES')
            return lstat(path, *args, **kwargs)

        with mock.patch.object(Path, 'lstat', unreadable_config):
            try:
                capture()
            except PermissionError as error:
                need('fixture config lstat EACCES' in str(error), 'wrong config refusal')
                count += 1
            else:
                raise ValueError('unreadable config accepted as absent')
        same_state(before, capture())
        original = config.read_bytes()

        def config_directory():
            config.unlink()
            config.mkdir()

        def restore_config():
            config.rmdir()
            config.write_bytes(original)

        refuses(config_directory, restore_config, 'non-regular configuration input')
        # Retarget the metadata package root, rather than a file inside it.
        manifest_parent = Path(next(iter(before['dependency_sources'].values()))['manifest_path']).parent
        saved = manifest_parent.with_name(manifest_parent.name + '-physical')
        def link_root():
            manifest_parent.rename(saved)
            manifest_parent.symlink_to(saved, target_is_directory=True)
        def restore_root():
            manifest_parent.unlink()
            saved.rename(manifest_parent)
        refuses(link_root, restore_root, 'noncanonical dependency root')

    return count
