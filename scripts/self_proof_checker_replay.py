"""Run one candidate checker on the retained W4 inputs and compare complete process results."""
from dataclasses import dataclass
import gzip
import hashlib
import json
import os
from pathlib import Path
import runpy
import subprocess
import tempfile


# The independent PR-42 transport receipt covers the genuine run. The producer
# qualification also pins the changed declaration, changed advice and both refusals.
PRELUDE_QUALIFICATION = {
    "source": "reports/self-proof-native-paired-beta/qualification.json",
    "revision": "a9fa4ca863c69e542526e47d33deb963c0ab34a8",
    "sha256": "782be731f6d4a1e919da3e96a03888eaa0f8804956b93cb0ccec0e5ba869ef6c",
}


@dataclass(frozen=True)
class Case:
    name: str
    source: bytes
    advice: bytes
    stdout: bytes
    stderr: bytes = b""
    status: int = 0


def digest(data):
    return hashlib.sha256(data).hexdigest()


def stream_digest(stream):
    h = hashlib.sha256()
    for chunk in iter(lambda: stream.read(65536), b""):
        h.update(chunk)
    return h.hexdigest()


def file_digest(path):
    with path.open("rb") as src:
        return stream_digest(src)


def first_difference(stream, expected):
    stream.seek(0)
    for line, want in enumerate([*expected.splitlines(keepends=True), b""], 1):
        got = stream.readline(len(want) + 321)
        if got != want:
            return {"line": line, "expected": want[:320].decode(errors="replace"),
                    "observed": got[:320].decode(errors="replace")}
    raise ValueError("different process output has no differing line")


def read(path):
    return json.loads(path.read_bytes())


def qualified_bytes(path, expected_digest):
    content = path.read_bytes()
    if digest(content) != expected_digest:
        raise ValueError(f"{path.name} differs from its Prelude qualification")
    return content


def prelude_cases(root):
    path = root / PRELUDE_QUALIFICATION["source"]
    receipt = json.loads(qualified_bytes(path, PRELUDE_QUALIFICATION["sha256"]))
    base = path.parent
    archive = runpy.run_path(str(base / "verify.py"))
    exports = archive["inputs"]()
    profile = receipt["profile"]
    fixture = profile["fixtures"]["prelude"]
    # The corrupt-advice control runs on the unchanged declaration export.
    source = exports["prelude"]
    if digest(source) != profile["controls"]["native-nat-corrupt"]["export_sha256"]:
        raise ValueError("original Prelude export differs from its qualification")
    wire = qualified_bytes(base / "prelude-prepared.bin", fixture["prepared_sha256"])

    def transcript(name):
        filename = name + ".txt.gz"
        return gzip.decompress(qualified_bytes(base / filename, receipt["artifact_sha256"][filename]))

    cases = [Case("Prelude/original", source, wire, transcript("prelude"))]
    prepared = {"prelude": wire, "neutral": (base / "neutral-prepared.bin").read_bytes()}
    controls = archive["controls"](exports, prepared)
    for name in ("native-nat-corrupt", "native-nat-wrong-body"):
        _, _, source, advice, _ = controls[name]
        control = profile["controls"][name]
        if digest(source) != control["export_sha256"] or digest(advice) != control["advice_sha256"]:
            raise ValueError(f"{name} inputs differ from the qualified Prelude control")
        cases.append(Case("Prelude/" + name, source, advice, transcript(name)))
    return cases


def retained_cases(root):
    reports = root / "reports"
    directions = read(root / "data/self_proof_fleet_timeline.json")["events"]
    bound = {}
    for unit in ("PR-49", "PR-52", "PR-53"):
        row, = [r for r in directions if r["unit"] == unit and r["kind"] == "measurement"]
        receipt = root / row["source"]
        if file_digest(receipt) != row["source_sha256"]:
            raise ValueError(f"{unit} receipt differs from the qualified timeline")
        bound[unit] = {"source": row["source"], "revision": row["source_revision"], "sha256": row["source_sha256"]}

    base = reports / "self-proof-native-init-slice"
    qualified = read(base / "qualification.json")
    init = runpy.run_path(str(base / "verify.py"))
    if init["check"](None, None, False, False) != qualified:
        raise ValueError("PR-49 archive differs from its qualification")
    source = gzip.decompress((base / "roots.ndjson.gz").read_bytes())
    advice = (base / "advice.bin").read_bytes()
    transcript = (base / "checker.txt").read_bytes()
    cases = [Case("Init/named-slice", source, advice, transcript)]
    subjects, _ = init["check_roots"](source, advice, transcript)
    for label, _, _, blob, wire in init["wrong_inputs"](source, advice, subjects):
        cases.append(Case("Init/" + label, blob, wire, gzip.decompress((base / (label + ".txt.gz")).read_bytes())))

    base = reports / "self-proof-native-level-shapes"
    levels = runpy.run_path(str(base / "verify.py"))
    if levels["verify"]()["observations_sha256"] != bound["PR-52"]["sha256"]:
        raise ValueError("PR-52 archive differs from its qualification")
    for name, row in read(base / "observations.json").items():
        blob = (base / "inputs" / (name + ".ndjson")).read_bytes()
        for label, wire in [("native", bytes.fromhex(row["native_advice_hex"])), ("specified", levels["SPECIFIED"])]:
            cases.append(Case(f"levels/{name}/{label}", blob, wire, row[label + "_transcript"].encode()))

    base = reports / "self-proof-native-structure-eta"
    eta = runpy.run_path(str(base / "verify.py"))
    if eta["verify"](None, None, False)["observations_sha256"] != bound["PR-53"]["sha256"]:
        raise ValueError("PR-53 archive differs from its qualification")
    for name, row in read(base / "observations.json").items():
        blob = gzip.decompress((base / (name + ".ndjson.gz")).read_bytes())
        cases.append(Case(f"eta/{name}/native", blob, bytes.fromhex(row["native_wire"]), row["native_transcript"].encode()))
        for label, control in row["controls"].items():
            stderr = control["stderr"].replace("<advice>", "advice.bin").encode()
            cases.append(Case("eta/" + label, blob, bytes.fromhex(control["wire"]),
                              control["transcript"].encode(), stderr, 2 if label == "prod_eta_proj" else 0))
    cases.extend(prelude_cases(root))
    bound["PR-42"] = PRELUDE_QUALIFICATION.copy()
    return bound, cases


def compare(image, case):
    row = {"case": case.name, "input_sha256": digest(case.source), "advice_sha256": digest(case.advice),
           "expected_exit": case.status, "expected_stdout_sha256": digest(case.stdout),
           "expected_stderr_sha256": digest(case.stderr)}
    with tempfile.TemporaryDirectory(prefix="clean-checker-comparison-") as tmp:
        work = Path(tmp)
        (work / "input.ndjson").write_bytes(case.source)
        (work / "advice.bin").write_bytes(case.advice)
        with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr:
            try:
                proc = subprocess.run([image, "input.ndjson", "advice.bin"], cwd=work,
                                      stdout=stdout, stderr=stderr, timeout=60)
                row["exit"] = proc.returncode
            except subprocess.TimeoutExpired:
                row.update(exit=None, error="timed out after 60 seconds")
            for label, stream, expected in (("stdout", stdout, case.stdout), ("stderr", stderr, case.stderr)):
                stream.seek(0)
                row[label + "_sha256"] = stream_digest(stream)
                if row[label + "_sha256"] != row["expected_" + label + "_sha256"]:
                    row[label + "_first_difference"] = first_difference(stream, expected)
    row["matched"] = (row["exit"] == row["expected_exit"] and row["stdout_sha256"] == row["expected_stdout_sha256"]
                      and row["stderr_sha256"] == row["expected_stderr_sha256"])
    return row


def replay(root, image):
    image = image.resolve(strict=True)
    if not image.is_file() or not os.access(image, os.X_OK):
        raise ValueError(f"candidate checker is not executable: {image}")
    sha = file_digest(image)
    archives, cases = retained_cases(root)
    results = []
    for case in cases:
        result = compare(image, case)
        results.append(result)
        if result.get("error"):
            break
    if file_digest(image) != sha:
        raise ValueError("the candidate executable changed during replay")
    matched = sum(row["matched"] for row in results)
    return {"schema": "clean.checker-replay/1", "checker_sha256": sha, "archives": archives,
            "qualified_cases": len(cases), "attempted": len(results), "matched": matched,
            "all_matched": matched == len(cases), "compiler_provenance": "unmeasured",
            "production_decisions_credited": 0, "cases": results}
