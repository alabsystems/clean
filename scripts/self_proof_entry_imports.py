# Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
"""Trace local checker source imports with the package's pinned Lean parser."""
from collections import deque
import hashlib
import io
import os
from pathlib import Path
import subprocess
import tarfile
import tempfile

if __package__:
    from . import self_proof_elab_probe as e4
else:
    import self_proof_elab_probe as e4

PACKAGE = "kcheck_labelled"
ENTRY = "KCheckLabelledMain.lean"
SOUNDNESS = "KCheck/CompleteSound.lean"


def entry_imports(root, revision, entry=ENTRY):
    archive = subprocess.check_output(
        ["git", "--no-replace-objects", "archive", revision, *("theories/" + p for p in e4.PACKAGES)], cwd=root)
    with tempfile.TemporaryDirectory(prefix="w1-imports-") as tmp:
        work = Path(tmp).resolve()
        snapshot = work / "snapshot"
        with tarfile.open(fileobj=io.BytesIO(archive)) as files:
            for member in files:
                if member.isfile():
                    path = snapshot / member.name
                    if not path.resolve().is_relative_to(snapshot):
                        raise ValueError("source path escaped its Git archive")
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes(files.extractfile(member).read())
        theories = snapshot / "theories"
        closure = e4.package_closures(theories)[PACKAGE]
        inventory = {(package, module + ".lean") for package, module, _ in e4.inventory(snapshot)}
        owners = {path.relative_to(theories / package).as_posix(): package
                  for package in closure for path in (theories / package).rglob("*.lean")}
        e4.stage_sources(snapshot, work)
        stage = work / PACKAGE
        _, lib = e4.pinned_lean_library({p: (theories / p / "lean-toolchain").read_text().strip() for p in closure})
        sdk = lib.parents[1]
        std = (sdk / "src/lean").resolve()
        lean = sdk / "bin/lean"
        env = os.environ | {"LEAN_SRC_PATH": os.pathsep.join(map(str, (stage, std))), "LEAN_SYSROOT": str(sdk)}
        if entry not in owners or owners[entry] != PACKAGE:
            raise ValueError(f"missing adopted checker source at {revision}: {entry}")
        pending = deque([entry])
        seen = {entry}
        graph = {}
        while pending:
            name = pending.popleft()
            command = subprocess.run([lean, "--src-deps", name], cwd=stage, env=env, capture_output=True,
                                     text=True, timeout=30)
            if command.returncode or command.stderr.strip():
                raise ValueError(f"could not read the pinned imports of {name}: {command.stderr.strip()}")
            local, external = [], []
            for line in command.stdout.splitlines():
                path = (stage / line).resolve()
                if path.is_relative_to(stage):
                    child = path.relative_to(stage).as_posix()
                    if child not in owners:
                        raise ValueError(f"local import has no owning package: {name} imports {child}")
                    local.append(child)
                    if child not in seen:
                        pending.append(child)
                        seen.add(child)
                elif path.is_relative_to(std) and path.is_file():
                    external.append(path.relative_to(std).as_posix())
                else:
                    raise ValueError(f"unresolved pinned import of {name}: {line}")
            graph[name] = {"package": owners[name], "in_census": (owners[name], name) in inventory,
                           "sha256": hashlib.sha256((stage / name).read_bytes()).hexdigest(),
                           "local": local, "sdk": external}
        return {"entry": entry, "lean_githash": subprocess.check_output([lean, "--githash"], text=True).strip(),
                "staged_sources": sum(1 for _ in stage.rglob("*.lean")), "modules": graph}
