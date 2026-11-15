#!/usr/bin/env python3
"""Unit tests for the WS6.12 trust-ir semantics probe's pure half.

The live half (`clean check` over the package) is recorded in
reports/trust-ir-semantics-probe/; these tests pin the parts that decide what
the census COUNTS, so a regression there cannot silently turn the axiom census
or the import order vacuous. They need no `clean` binary and no Lean.
"""

import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest import mock


SCRIPT = Path(__file__).resolve().parent / "trust_ir_semantics_probe.py"
SPEC = importlib.util.spec_from_file_location("trust_ir_semantics_probe", SCRIPT)
PROBE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PROBE)


BRIDGE = """\
/-- `ay_check` is opaque; a docstring may say sorry without being one. -/
opaque ay_check : Nat -> Bool

-- a comment mentioning axiom fake_axiom and sorry is prose
axiom ay_sound_unsat : forall n, ay_check n = true -> n = 0

theorem ay_sound_contrapositive (n : Nat) (h : n ≠ 0) :
    ay_check n ≠ true := by
  intro hc
  exact h (ay_sound_unsat n hc)

def msg : String := "sorry is only a string here"
"""


def write_pkg(root: Path, files: dict) -> Path:
    for rel, text in files.items():
        p = root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
    return root


class SourceCensus(unittest.TestCase):
    def pkg(self, bridge_text: str) -> Path:
        tmp = tempfile.mkdtemp()
        self.addCleanup(lambda: __import__("shutil").rmtree(tmp, ignore_errors=True))
        return write_pkg(Path(tmp), {
            "TrustIr/Basic.lean": "def one : Nat := 1\n",
            "TrustIr/Proofs/AYBridge.lean": "import TrustIr.Basic\n" + bridge_text,
            "lakefile.lean": "-- axiom in_lakefile : False\n",
        })

    def test_positive_sole_first_party_axiom_matches(self):
        census = PROBE.source_axiom_census(self.pkg(BRIDGE))
        self.assertEqual([a["name"] for a in census["first_party_axioms"]], ["ay_sound_unsat"])
        self.assertEqual(census["placeholders"], [])
        self.assertTrue(census["matches"])

    def test_mutation_control_injected_sorry_is_flagged(self):
        pkg = self.pkg(BRIDGE)
        self.assertEqual(PROBE.inject_sorry(pkg), PROBE.MUTATION_TARGET_FILE)
        census = PROBE.source_axiom_census(pkg)
        self.assertFalse(census["matches"])
        self.assertEqual([(p["token"], p["file"]) for p in census["placeholders"]],
                         [("sorry", PROBE.MUTATION_TARGET_FILE)])

    def test_negative_extra_first_party_axiom_is_flagged(self):
        census = PROBE.source_axiom_census(self.pkg(BRIDGE + "axiom smuggled : False\n"))
        self.assertFalse(census["matches"])
        self.assertIn("smuggled", [a["name"] for a in census["first_party_axioms"]])

    def test_negative_admit_is_a_placeholder(self):
        census = PROBE.source_axiom_census(self.pkg(BRIDGE + "theorem b : 1 = 1 := by admit\n"))
        self.assertFalse(census["matches"])
        self.assertEqual([p["token"] for p in census["placeholders"]], ["admit"])

    def test_native_decide_is_disclosed_not_first_party(self):
        # Lean-core `Lean.ofReduceBool`, outside trust-ir's first-party census,
        # exactly as its AxiomAudit treats it -- but never silently dropped.
        census = PROBE.source_axiom_census(self.pkg(
            BRIDGE + "theorem a : 1 = 1 := by native_decide\n"))
        self.assertTrue(census["matches"])
        self.assertEqual(census["evaluator_sites"], 1)
        self.assertEqual(census["evaluator_sites_by_file"], {"TrustIr/Proofs/AYBridge.lean": 1})

    def test_negative_missing_sole_axiom_does_not_match(self):
        census = PROBE.source_axiom_census(self.pkg(BRIDGE.replace(
            "axiom ay_sound_unsat", "theorem ay_sound_unsat")))
        self.assertFalse(census["matches"])

    def test_attributed_private_axiom_is_counted(self):
        census = PROBE.source_axiom_census(self.pkg(BRIDGE + "@[simp] private axiom hidden : True\n"))
        self.assertIn("hidden", [a["name"] for a in census["first_party_axioms"]])

    def test_identifier_containing_sorry_is_not_a_placeholder(self):
        census = PROBE.source_axiom_census(self.pkg(BRIDGE + "def sorry_count : Nat := 0\n"))
        self.assertTrue(census["matches"])


class Stripping(unittest.TestCase):
    def test_nested_block_comment_and_line_numbers_survive(self):
        src = "/- outer /- inner sorry -/ still -/\nsorry\n"
        out = PROBE.strip_comments_and_strings(src)
        self.assertEqual(out.count("\n"), 2)
        self.assertNotIn("inner", out)
        self.assertEqual(out.splitlines()[1], "sorry")

    def test_char_literal_quote_does_not_open_a_string(self):
        out = PROBE.strip_comments_and_strings("def q : Char := '\"'\ntheorem t := sorry\n")
        self.assertIn("sorry", out)

    def test_primed_identifier_is_not_a_char_literal(self):
        out = PROBE.strip_comments_and_strings("have h'x' := sorry\n")
        self.assertIn("h'x'", out)


class TagNormalization(unittest.TestCase):
    MODS = {"TrustIr.Basic", "TrustIr"}

    def test_absolute_import_tag_is_reduced_to_its_module_name(self):
        tag = "[Users.me.scratch.pkg.TrustIr.Basic] TrustIr.FieldDef: boom"
        self.assertEqual(PROBE.normalize_tags(tag, self.MODS),
                         "[TrustIr.Basic] TrustIr.FieldDef: boom")

    def test_a_bare_module_tag_is_unchanged(self):
        self.assertEqual(PROBE.normalize_tags("[TrustIr.Basic] boom", self.MODS),
                         "[TrustIr.Basic] boom")

    def test_machine_paths_are_masked_in_both_spellings(self):
        base = Path("$HOME/repo/repros")
        text = "[Users.me.repo.repros.Pkg.A] and $HOME/repo/repros/Pkg/A.lean"
        self.assertEqual(PROBE.mask_paths(text, base),
                         "[<repros>.Pkg.A] and <repros>/Pkg/A.lean")

    def test_a_tag_that_is_not_a_module_of_this_package_is_left_alone(self):
        self.assertEqual(PROBE.normalize_tags("[anonymous] boom", self.MODS), "[anonymous] boom")
        self.assertEqual(PROBE.normalize_tags("[Other.Pkg.A] boom", self.MODS), "[Other.Pkg.A] boom")


class ImportOrder(unittest.TestCase):
    def test_imports_header_only_and_comment_blind(self):
        src = "-- import Fake.Module\nimport TrustIr.Basic\n/- import X -/\nimport TrustIr.Inst\n\ndef x := 1\nimport Late\n"
        self.assertEqual(PROBE.imports_of(src), ["TrustIr.Basic", "TrustIr.Inst"])

    def test_dependencies_precede_users_deterministically(self):
        graph = {
            "TrustIr": ["TrustIr.B", "TrustIr.A"],
            "TrustIr.A": ["TrustIr.Basic", "Init.Data"],
            "TrustIr.B": ["TrustIr.Basic"],
            "TrustIr.Basic": [],
        }
        self.assertEqual(PROBE.import_order(graph),
                         ["TrustIr.Basic", "TrustIr.A", "TrustIr.B", "TrustIr"])

    def test_cycle_is_refused_not_broken(self):
        with self.assertRaises(PROBE.ProbeError):
            PROBE.import_order({"A": ["B"], "B": ["A"]})

    def test_package_files_skip_lakefile(self):
        with tempfile.TemporaryDirectory() as tmp:
            write_pkg(Path(tmp), {"lakefile.lean": "", "TrustIr/Basic.lean": "", "TrustIr.lean": ""})
            self.assertEqual(PROBE.package_files(Path(tmp)),
                             {"TrustIr": "TrustIr.lean", "TrustIr.Basic": "TrustIr/Basic.lean"})


class TableProvenance(unittest.TestCase):
    CENSUS = {
        "clean": "clean 0.9.0", "clean_source": None, "mem_cap_gb": 8.0, "files": [],
        "summary": {"files": 0, "elaborated": 0, "blocked": 0, "failed": 0, "memory_cap": 0,
                    "timeout": 0, "decls_ok": 0, "decls": 0, "seconds": 0.0, "peak_rss_gb": 0.0},
        "axiom_census": {"source": {"first_party_axioms": [], "placeholders": [],
                                    "evaluator_sites": 0, "matches": False},
                         "clean_sorry_axioms_total": 0},
        "authority_transfer_ready": False,
    }

    def test_an_unrecorded_source_commit_is_said_out_loud(self):
        # `clean --version` is a package version, not an identity: a table
        # without the built-from commit must say so rather than imply one.
        self.assertIn("built from a commit that was NOT RECORDED", PROBE.render_table(self.CENSUS))

    def test_a_recorded_source_commit_is_rendered(self):
        census = dict(self.CENSUS, clean_source="deadbeef")
        self.assertIn("`clean 0.9.0` built from `deadbeef`", PROBE.render_table(census))

    def test_the_verdict_is_never_rendered_ready_by_an_empty_run(self):
        self.assertIn("`authority_transfer_ready`: false", PROBE.render_table(self.CENSUS))


FAKE_CLEAN = """\
#!/usr/bin/env python3
# A stand-in `clean check --json`: a file PASSES unless it contains the
# word FAIL, in which case its report carries an error naming the line's text.
# A line containing SORRY models the G13 shape — parser recovery minting a
# synthetic sorry — from a checker that STILL reports `pass` and exits 0:
# only `trust_summary.sorry_axioms` and `trust_failures` say anything.
import json, sys
path = sys.argv[-1]
text = open(path, encoding="utf-8").read()
errs = [ln.strip() for ln in text.splitlines() if "FAIL" in ln]
# A line containing AUTOBOUND models G50: `Foo` auto-binds unless the run
# carries `-DautoImplicit=false`, under which it is an unknown identifier.
if "-DautoImplicit=false" in sys.argv:
    errs += [ln.strip() + ": Unknown identifier: Foo"
             for ln in text.splitlines() if "AUTOBOUND" in ln]
sorries = [ln.strip() + ": declaration uses synthetic sorry"
           for ln in text.splitlines() if "SORRY" in ln]
print(json.dumps({"schema_version": "Clean-check-report-v2", "command": "clean check",
                  "status": "fail" if errs else "pass", "errors": errs,
                  "decl_count": 1, "success_count": 0 if errs else 1,
                  "failed_count": len(errs), "diverged_count": 0,
                  "trust_summary": {"sorry_axioms": len(sorries), "kernel_check_failures": 0},
                  "trust_failures": sorries, "kernel_failures": [], "diverged": [],
                  "parser_recovery": []}))
sys.exit(1 if errs else 0)
"""


class ReprosRows(unittest.TestCase):
    """The row logic of `repros`, driven by a fake checker: OPEN rows must still
    fail as filed, closed_by rows must pass with a refused twin, and every
    flip is a run failure."""

    def setUp(self):
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(lambda: __import__("shutil").rmtree(tmp, ignore_errors=True))
        self.clean = tmp / "clean"
        self.clean.write_text(FAKE_CLEAN, encoding="utf-8")
        self.clean.chmod(0o755)
        self.base = tmp / "repros"
        self.base.mkdir()

    def run_manifest(self, gaps: list, files: dict) -> dict:
        write_pkg(self.base, files)
        manifest = self.base / "manifest.json"
        manifest.write_text(__import__("json").dumps({"gaps": gaps}), encoding="utf-8")
        return PROBE.run_repros(self.clean, manifest, timeout=30)

    def test_repro_corpus_must_be_a_nonempty_list_before_checker_birth(self):
        for gaps in ([], None, {}, "G1", False, 0):
            with self.subTest(gaps=gaps):
                marker = self.mark_checker_birth()
                marker.unlink(missing_ok=True)
                with self.assertRaisesRegex(PROBE.ProbeError, "non-empty list"):
                    self.run_manifest(gaps, {})
                self.assertFalse(marker.exists())

    def test_late_invalid_row_refuses_before_any_checker_birth(self):
        invalid = [
            {"id": "G2", "entry": "b.lean", "expect": ""},
            {"id": "G2", "entry": "b.lean", "expect": "["},
            {"id": "G2", "entry": "b.lean", "expect": "boom", "clean_args": "-Dfoo=true"},
            {"id": "G2", "entry": 0, "expect": "boom"},
            {"id": "G2", "entry": "b.lean", "expect": "boom", "cwd": 0},
            {"id": "G2", "entry": "b.lean", "closed_by": True,
             "twin": "b-twin.lean", "twin_expect": "boom"},
            {"id": "G2", "entry": "b.lean", "closed_by": "closed", "twin": None,
             "twin_expect": "boom"},
            {"id": "G2", "entry": "b\x00.lean", "expect": "boom"},
            {"id": "G2", "entry": "b.lean", "expect": "boom", "cwd": "bad\x00path"},
            {"id": "G2", "entry": "b.lean", "expect": "boom", "clean_args": ["bad\x00arg"]},
            None,
        ]
        for late in invalid:
            with self.subTest(late=late):
                marker = self.mark_checker_birth()
                marker.unlink(missing_ok=True)
                with self.assertRaises(PROBE.ProbeError):
                    self.run_manifest(
                        [{"id": "G1", "entry": "a.lean", "expect": "boom"}, late],
                        {"a.lean": "FAIL: boom\n", "b.lean": "FAIL: boom\n",
                         "b-twin.lean": "FAIL: boom\n"},
                    )
                self.assertFalse(marker.exists())

    def test_clean_args_requires_a_json_list_without_falsey_coercion(self):
        for args in ("-DautoImplicit=false", {}, False, 0, None, [1]):
            with self.subTest(args=args):
                marker = self.mark_checker_birth()
                marker.unlink(missing_ok=True)
                with self.assertRaisesRegex(PROBE.ProbeError, "list of strings"):
                    self.run_manifest(
                        [{"id": "G1", "entry": "a.lean", "expect": "boom", "clean_args": args}],
                        {"a.lean": "FAIL: boom\n"},
                    )
                self.assertFalse(marker.exists())

    def test_duplicate_ids_cannot_count_the_same_filed_row_twice(self):
        marker = self.mark_checker_birth()
        with self.assertRaisesRegex(PROBE.ProbeError, "duplicate repro id"):
            self.run_manifest(
                [{"id": "G1", "entry": "a.lean", "expect": "boom"},
                 {"id": "G1", "entry": "b.lean", "expect": "boom"}],
                {"a.lean": "FAIL: boom\n", "b.lean": "FAIL: boom\n"},
            )
        self.assertFalse(marker.exists())

    def test_open_row_still_fails_as_filed(self):
        r = self.run_manifest([{"id": "G1", "entry": "a.lean", "expect": "FAIL: boom"}],
                              {"a.lean": "x FAIL: boom\n"})
        self.assertEqual([x["outcome"] for x in r["repros"]], ["still-fails"])
        self.assertTrue(r["pass"])
        self.assertEqual((r["open"], r["closed_upstream"]), (1, 0))

    def test_non_object_checker_json_is_unjudged_not_semantic_drift(self):
        import json
        for value in (None, [], True, False, 0, "pass"):
            with self.subTest(value=value):
                self.clean.write_text(
                    "#!/usr/bin/env python3\nprint(" + repr(json.dumps(value)) + ")\n",
                    encoding="utf-8",
                )
                result = self.run_manifest(
                    [{"id": "G1", "entry": "a.lean", "expect": "boom"}],
                    {"a.lean": "def ok := 1\n"},
                )
                self.assertEqual(result["repros"][0]["outcome"], "no-report")
                self.assertEqual(result["repros"][0]["exit"], 0)
                self.assertFalse(result["pass"])

    def test_non_object_negative_twin_report_cannot_keep_a_closed_row_green(self):
        self.clean.write_text(FAKE_CLEAN.replace(
            'text = open(path, encoding="utf-8").read()\n',
            'text = open(path, encoding="utf-8").read()\n'
            'if "NONOBJECT" in text:\n    print("null")\n    sys.exit(0)\n',
            1,
        ), encoding="utf-8")
        result = self.run_manifest(
            [self.CLOSED], {"c.lean": "def ok := 1\n", "c-twin.lean": "NONOBJECT\n"},
        )
        row = result["repros"][0]
        self.assertEqual(row["outcome"], "no-report")
        self.assertEqual(row["twin"]["exit"], 0)
        self.assertFalse(result["pass"])

    def install_invalid_utf8_checker(self, stream):
        self.clean.write_text(FAKE_CLEAN.replace(
            'text = open(path, encoding="utf-8").read()\n',
            'text = open(path, encoding="utf-8").read()\n'
            'if "INVALID_UTF8" in text:\n'
            '    print(json.dumps({"status": "fail", "errors": ["FAIL: boom"]}))\n'
            f'    sys.{stream}.buffer.write(bytes([255]))\n'
            '    sys.exit(7)\n',
            1,
        ), encoding="utf-8")

    def test_invalid_utf8_checker_output_is_unjudged_and_preserves_exit(self):
        for stream in ("stdout", "stderr"):
            with self.subTest(stream=stream):
                self.install_invalid_utf8_checker(stream)
                result = self.run_manifest(
                    [{"id": "G1", "entry": "a.lean", "expect": "boom"}],
                    {"a.lean": "INVALID_UTF8\n"},
                )
                self.assertEqual(result["repros"][0]["outcome"], "no-report")
                self.assertEqual(result["repros"][0]["exit"], 7)
                self.assertFalse(result["pass"])

    def test_invalid_utf8_negative_twin_cannot_keep_a_closed_row_green(self):
        for stream in ("stdout", "stderr"):
            with self.subTest(stream=stream):
                self.install_invalid_utf8_checker(stream)
                result = self.run_manifest(
                    [self.CLOSED],
                    {"c.lean": "def ok := 1\n", "c-twin.lean": "INVALID_UTF8\n"},
                )
                self.assertEqual(result["repros"][0]["outcome"], "no-report")
                self.assertEqual(result["repros"][0]["twin"]["exit"], 7)
                self.assertFalse(result["pass"])

    def test_diagnostic_mapping_cannot_satisfy_a_filed_refusal(self):
        self.clean.write_text(FAKE_CLEAN.replace(
            '"errors": errs,', '"errors": {"FAIL: boom": None},', 1,
        ), encoding="utf-8")
        result = self.run_manifest(
            [{"id": "G1", "entry": "a.lean", "expect": "boom"}],
            {"a.lean": "FAIL: boom\n"},
        )
        self.assertEqual(result["repros"][0]["outcome"], "no-report")
        self.assertFalse(result["pass"])

    def test_incomplete_pass_cannot_keep_a_closed_row_green_with_a_valid_twin(self):
        self.clean.write_text(FAKE_CLEAN.replace(
            'text = open(path, encoding="utf-8").read()\n',
            'text = open(path, encoding="utf-8").read()\n'
            'if "MINIMAL_PASS" in text:\n'
            '    print(json.dumps({"status": "pass"}))\n    sys.exit(0)\n',
            1,
        ), encoding="utf-8")
        result = self.run_manifest(
            [self.CLOSED],
            {"c.lean": "MINIMAL_PASS\n", "c-twin.lean": "g03_twin: FAIL: mismatch\n"},
        )
        self.assertEqual(result["repros"][0]["outcome"], "no-report")
        self.assertFalse(result["pass"])

    def mark_checker_birth(self) -> Path:
        marker = self.base.parent / "checker-born"
        self.clean.write_text(FAKE_CLEAN.replace(
            "import json, sys\n",
            f"import json, sys\nfrom pathlib import Path\nPath({str(marker)!r}).touch()\n",
            1,
        ), encoding="utf-8")
        return marker

    def test_later_missing_toolchain_refuses_before_any_checker_birth(self):
        marker = self.mark_checker_birth()
        gaps = [
            {"id": "G1", "entry": "a.lean", "expect": "boom"},
            {"id": "G2", "entry": "b.lean", "expect": "boom",
             "lean_toolchain": "leanprover/lean4:v4.8.0"},
        ]
        with mock.patch.object(PROBE, "lean_toolchain_lib",
                               side_effect=PROBE.ProbeError("pinned library absent")):
            with self.assertRaisesRegex(PROBE.ProbeError, "pinned library absent"):
                self.run_manifest(gaps, {"a.lean": "FAIL: boom\n", "b.lean": "FAIL: boom\n"})
        self.assertFalse(marker.exists(), "the earlier row must not start a checker")

    def test_available_toolchain_keeps_actual_checker_rows(self):
        marker = self.mark_checker_birth()
        lib = self.base.parent / "lib" / "lean"
        lib.mkdir(parents=True)
        gaps = [
            {"id": "G1", "entry": "a.lean", "expect": "boom"},
            {"id": "G2", "entry": "b.lean", "expect": "boom",
             "lean_toolchain": "leanprover/lean4:v4.8.0"},
        ]
        with mock.patch.object(PROBE, "lean_toolchain_lib", return_value=lib):
            result = self.run_manifest(gaps, {"a.lean": "FAIL: boom\n", "b.lean": "FAIL: boom\n"})
        self.assertTrue(marker.exists())
        self.assertEqual([row["outcome"] for row in result["repros"]],
                         ["still-fails", "still-fails"])
        self.assertTrue(result["pass"])

    def test_open_row_that_now_passes_is_closed_and_fails_the_run(self):
        r = self.run_manifest([{"id": "G1", "entry": "a.lean", "expect": "boom"}],
                              {"a.lean": "def ok := 1\n"})
        self.assertEqual(r["repros"][0]["outcome"], "closed")
        self.assertFalse(r["pass"])

    def test_open_row_failing_for_another_reason_is_changed(self):
        r = self.run_manifest([{"id": "G1", "entry": "a.lean", "expect": "boom"}],
                              {"a.lean": "x FAIL: other\n"})
        self.assertEqual(r["repros"][0]["outcome"], "changed")
        self.assertFalse(r["pass"])

    CLOSED = {"id": "G3", "entry": "c.lean", "expect": "isEmpty", "closed_by": "abc123",
              "twin": "c-twin.lean", "twin_expect": "^g03_twin: .*mismatch"}

    def test_closed_row_passes_with_a_refused_twin(self):
        r = self.run_manifest([self.CLOSED], {"c.lean": "def ok := 1\n",
                                              "c-twin.lean": "g03_twin: FAIL: mismatch\n"})
        self.assertEqual(r["repros"][0]["outcome"], "still-passes")
        self.assertEqual(r["repros"][0]["closed_by"], "abc123")
        self.assertTrue(r["pass"])
        self.assertEqual((r["open"], r["closed_upstream"]), (0, 1))

    def test_closed_row_that_fails_again_is_regressed(self):
        r = self.run_manifest([self.CLOSED], {"c.lean": "x FAIL: isEmpty\n",
                                              "c-twin.lean": "g03_twin: FAIL: mismatch\n"})
        self.assertEqual(r["repros"][0]["outcome"], "regressed")
        self.assertFalse(r["pass"])

    def test_closed_row_whose_twin_is_accepted_fails_the_run(self):
        # a checker that accepts everything would "close" every gap
        r = self.run_manifest([self.CLOSED], {"c.lean": "def ok := 1\n",
                                              "c-twin.lean": "def also_ok := 1\n"})
        self.assertEqual(r["repros"][0]["outcome"], "twin-accepted")
        self.assertFalse(r["pass"])

    def test_closed_row_whose_twin_fails_for_the_wrong_reason_fails_the_run(self):
        r = self.run_manifest([self.CLOSED], {"c.lean": "def ok := 1\n",
                                              "c-twin.lean": "other: FAIL: unrelated\n"})
        self.assertEqual(r["repros"][0]["outcome"], "twin-changed")
        self.assertFalse(r["pass"])

    # --- adversarial (review): a `pass` verdict that carries a sorry -------

    def test_closed_row_that_passes_only_by_a_synthetic_sorry_is_regressed(self):
        # A checker that recovers from a parse gap by minting a sorry, reports
        # `pass` and exits 0 (only its axiom census says otherwise) must not
        # keep a PASS row green: the row's entry is a refusal for the ratchet.
        r = self.run_manifest([self.CLOSED], {"c.lean": "def ok := SORRY\n",
                                              "c-twin.lean": "g03_twin: FAIL: mismatch\n"})
        self.assertEqual(r["repros"][0]["outcome"], "regressed")
        self.assertIn("synthetic sorry", r["repros"][0]["first"])
        self.assertFalse(r["pass"])

    def test_closed_row_whose_twin_is_refused_only_by_a_sorry_is_twin_changed(self):
        # The twin must be refused FOR ITS FILED REASON; a sorry-laundered
        # "refusal" is the wrong reason, so it is `twin-changed`, never green.
        r = self.run_manifest([self.CLOSED], {"c.lean": "def ok := 1\n",
                                              "c-twin.lean": "g03_twin := SORRY\n"})
        self.assertEqual(r["repros"][0]["outcome"], "twin-changed")
        self.assertFalse(r["pass"])

    def test_open_row_filed_on_a_synthetic_sorry_still_fails_with_a_pass_verdict(self):
        # G13's shape: the filed signature IS the synthetic sorry, and the
        # checker's `pass`/exit 0 must not read as the gap having closed.
        r = self.run_manifest([{"id": "G13", "entry": "s.lean", "expect": "synthetic sorry"}],
                              {"s.lean": "theorem t := SORRY\n"})
        self.assertEqual(r["repros"][0]["outcome"], "still-fails")
        self.assertTrue(r["pass"])

    # --- adversarial (review): a row without a filed signature is refused ---
    # (an empty `expect` matches every refusal, so `changed` could never fire)

    def test_an_open_row_with_an_empty_signature_is_refused(self):
        with self.assertRaises(PROBE.ProbeError):
            self.run_manifest([{"id": "G1", "entry": "a.lean", "expect": ""}],
                              {"a.lean": "x FAIL: boom\n"})

    def test_an_open_row_without_a_signature_is_refused(self):
        with self.assertRaises(PROBE.ProbeError):
            self.run_manifest([{"id": "G1", "entry": "a.lean"}], {"a.lean": "x FAIL: boom\n"})

    def test_a_closed_row_with_an_empty_twin_signature_is_refused(self):
        with self.assertRaises(PROBE.ProbeError):
            self.run_manifest([dict(self.CLOSED, twin_expect="")],
                              {"c.lean": "def ok := 1\n", "c-twin.lean": "g03_twin: FAIL: mismatch\n"})

    def test_a_closed_row_without_a_twin_is_refused(self):
        row = {k: v for k, v in self.CLOSED.items() if k != "twin"}
        with self.assertRaises(PROBE.ProbeError):
            self.run_manifest([row], {"c.lean": "def ok := 1\n"})

    # --- G50: a row checked under its own `clean_args` -------------------

    G50 = {"id": "G50", "entry": "ok.lean", "expect": "unused", "closed_by": "this change",
           "twin": "twin.lean", "twin_expect": "Unknown identifier: Foo",
           "clean_args": ["-DautoImplicit=false"]}

    def test_row_clean_args_reach_entry_and_twin(self):
        r = self.run_manifest([self.G50], {"ok.lean": "def ok := 1\n",
                                           "twin.lean": "theorem t AUTOBOUND\n"})
        self.assertEqual(r["repros"][0]["outcome"], "still-passes")
        self.assertEqual(r["repros"][0]["clean_args"], ["-DautoImplicit=false"])
        self.assertTrue(r["pass"])

    def test_row_without_its_clean_args_accepts_the_twin(self):
        # Non-vacuity: the same twin WITHOUT the override is accepted, so the
        # refusal above is the override's doing.
        row = {k: v for k, v in self.G50.items() if k != "clean_args"}
        r = self.run_manifest([row], {"ok.lean": "def ok := 1\n",
                                      "twin.lean": "theorem t AUTOBOUND\n"})
        self.assertEqual(r["repros"][0]["outcome"], "twin-accepted")
        self.assertFalse(r["pass"])

    def test_row_clean_args_must_be_strings(self):
        with self.assertRaises(PROBE.ProbeError):
            self.run_manifest([dict(self.G50, clean_args=[1])],
                              {"ok.lean": "def ok := 1\n", "twin.lean": "x\n"})

    def test_the_committed_manifest_files_a_twin_for_every_closed_row(self):
        manifest = SCRIPT.parent.parent / "reports" / "trust-ir-semantics-probe" / "repros" / "manifest.json"
        spec = __import__("json").loads(manifest.read_text(encoding="utf-8"))
        self.assertIs(PROBE.validate_repro_manifest(spec), spec["gaps"])
        for gap in spec["gaps"]:
            entry = manifest.parent / gap.get("cwd", ".") / gap["entry"]
            self.assertTrue(entry.is_file(), f"{gap['id']}: missing {entry}")
            if gap.get("closed_by"):
                self.assertIn("twin", gap, gap["id"])
                self.assertIn("twin_expect", gap, gap["id"])
                self.assertTrue((manifest.parent / gap.get("cwd", ".") / gap["twin"]).is_file(), gap["id"])
            else:
                self.assertIn("expect", gap, gap["id"])


class ReportRow(unittest.TestCase):
    """`report_row` / `report_passed`: what a census row is allowed to call
    `elaborated`. Every refusal-bearing field must be silent — a `pass`
    verdict alone is never enough (adversarial review of WS6.12)."""

    PASS = {"schema_version": "Clean-check-report-v2", "command": "clean check",
            "status": "pass", "decl_count": 3, "success_count": 3, "failed_count": 0,
            "diverged_count": 0, "trust_summary": {"sorry_axioms": 0, "kernel_check_failures": 0},
            "errors": [], "trust_failures": [], "kernel_failures": [], "diverged": [],
            "parser_recovery": []}

    def test_malformed_verdict_data_is_unjudged_by_both_classifiers(self):
        malformed = [
            {"status": "pass"},
            {k: v for k, v in self.PASS.items() if k != "trust_summary"},
            dict(self.PASS, trust_summary=[]),
            dict(self.PASS, failed_count=False),
            dict(self.PASS, diverged_count=0.0),
            dict(self.PASS, decl_count=-1),
            dict(self.PASS, trust_summary={"sorry_axioms": False, "kernel_check_failures": 0}),
            dict(self.PASS, schema_version="Clean-check-report-v1"),
            dict(self.PASS, command="clean project"),
            dict(self.PASS, errors=""),
            dict(self.PASS, kernel_failures={}),
            dict(self.PASS, parser_recovery=[None]),
        ]
        for report in malformed:
            with self.subTest(report=report):
                self.assertFalse(PROBE.report_passed(report, 0))
                self.assertEqual(PROBE.report_row(report, 0)["status"], "no-report")

    def test_pass_with_unchecked_own_declarations_is_not_elaborated(self):
        report = dict(self.PASS, success_count=2)
        self.assertFalse(PROBE.report_passed(report, 0))
        self.assertEqual(PROBE.report_row(report, 0)["status"], "failed")

    def test_unqualified_pass_is_elaborated(self):
        self.assertEqual(PROBE.report_row(self.PASS, 0)["status"], "elaborated")
        self.assertTrue(PROBE.report_passed(self.PASS, 0))

    def test_pass_verdict_with_an_inherited_error_is_blocked_not_elaborated(self):
        # a checker that said `pass` (exit 0) while an import failed
        rep = dict(self.PASS, errors=["[Pkg.A] bad: Type mismatch"], failed_count=1)
        row = PROBE.report_row(rep, 0)
        self.assertEqual(row["status"], "blocked")
        self.assertEqual(row["inherited_error_count"], 1)
        self.assertIsNone(row["first_own_failure"])

    def test_inherited_failed_count_does_not_unblock_a_blocked_row(self):
        # measured shape: Constant.lean at c3720ea36 — 1/1 own, failed_count 4
        # (the four failed declarations of Basic.lean), exit 1
        rep = dict(self.PASS, status="fail", decl_count=1, success_count=1, failed_count=4,
                   errors=["[TrustIr.Basic] TrustIr.FieldDef: Unsupported feature"] * 4)
        self.assertEqual(PROBE.report_row(rep, 1)["status"], "blocked")

    def test_pass_verdict_with_a_sorry_is_failed(self):
        rep = dict(self.PASS, trust_summary={"sorry_axioms": 1, "kernel_check_failures": 0},
                   trust_failures=["t: declaration uses synthetic sorry"])
        self.assertEqual(PROBE.report_row(rep, 0)["status"], "failed")
        self.assertFalse(PROBE.report_passed(rep, 0))

    def test_pass_verdict_with_a_kernel_failure_is_failed(self):
        rep = dict(self.PASS, kernel_failures=["t: Kernel check failed"])
        self.assertEqual(PROBE.report_row(rep, 0)["status"], "failed")

    def test_pass_verdict_with_a_nonzero_exit_is_not_elaborated(self):
        self.assertFalse(PROBE.report_passed(self.PASS, 1))

    def test_an_own_trust_failure_is_never_blocked(self):
        rep = dict(self.PASS, trust_failures=["t: declaration uses explicit sorry"],
                   trust_summary={"sorry_axioms": 1, "kernel_check_failures": 0})
        self.assertEqual(PROBE.report_row(rep, 1)["status"], "failed")

    # --- adversarial (review): an own failure tagged with the file's own module

    def test_an_error_tagged_with_the_files_own_module_is_own_not_inherited(self):
        # G09's shape: the failing command (`#guard_msgs in #print axioms`) is
        # not counted as a declaration, so success_count == decl_count still
        # holds; if the tag made the row read as inherited the file would
        # classify `blocked` although its OWN body failed.
        rep = dict(self.PASS, status="fail",
                   errors=["[TrustIr.Proofs.AxiomAudit] Kernel check failed for [anonymous]"])
        row = PROBE.report_row(rep, 1, module="TrustIr.Proofs.AxiomAudit")
        self.assertEqual(row["status"], "failed")
        self.assertEqual(row["inherited_error_count"], 0)
        self.assertEqual(row["first_own_failure"],
                         "[TrustIr.Proofs.AxiomAudit] Kernel check failed for [anonymous]")

    def test_an_error_tagged_with_another_module_is_still_inherited(self):
        rep = dict(self.PASS, status="fail",
                   errors=["[TrustIr.Basic] TrustIr.FieldDef: Unsupported feature"])
        row = PROBE.report_row(rep, 1, module="TrustIr.Proofs.AxiomAudit")
        self.assertEqual(row["status"], "blocked")
        self.assertEqual(row["inherited_error_count"], 1)

    def test_a_prefix_of_the_own_module_name_is_not_the_own_module(self):
        # `[TrustIr.Basic]` must not be read as own by `TrustIr.Basics`
        rep = dict(self.PASS, status="fail", errors=["[TrustIr.Basic] x: bad"])
        self.assertEqual(PROBE.report_row(rep, 1, module="TrustIr.Basics")["inherited_error_count"], 1)


class CensusCompleteness(unittest.TestCase):
    """`authority_transfer_ready` is decided over EVERY file of the package
    (adversarial review of WS6.12): a `--only` run over the files that happen
    to elaborate must never claim readiness."""

    def setUp(self):
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(lambda: __import__("shutil").rmtree(tmp, ignore_errors=True))
        self.clean = tmp / "clean"
        self.clean.write_text(FAKE_CLEAN, encoding="utf-8")
        self.clean.chmod(0o755)
        self.pkg = write_pkg(tmp / "pkg", {
            "TrustIr/Basic.lean": "def one : Nat := 1\n",
            "TrustIr/Bad.lean": "import TrustIr.Basic\nx FAIL: boom\n",
            "TrustIr/Proofs/AYBridge.lean": "import TrustIr.Basic\n" + BRIDGE,
        })

    def census(self, only=None):
        return PROBE.run_census(self.clean, self.pkg, timeout=30, extra=[], only=only,
                                mem_cap_gb=0)

    def test_missing_report_counters_cannot_grant_authority_transfer(self):
        self.clean.write_text(
            "#!/usr/bin/env python3\nprint(" + repr('{"status": "pass"}') + ")\n",
            encoding="utf-8",
        )
        result = self.census()
        self.assertFalse(result["authority_transfer_ready"])
        self.assertEqual(result["summary"]["no_report"], 3)
        self.assertEqual(result["summary"]["elaborated"], 0)

    def test_a_full_run_over_a_package_that_does_not_check_is_not_ready(self):
        c = self.census()
        self.assertTrue(c["summary"]["complete"])
        self.assertEqual((c["summary"]["files"], c["summary"]["package_files"]), (3, 3))
        self.assertEqual(c["summary"]["failed"], 1)
        self.assertFalse(c["authority_transfer_ready"])

    def test_a_partial_run_over_only_the_elaborating_files_is_not_ready(self):
        c = self.census(only=["TrustIr/Basic.lean", "TrustIr/Proofs/AYBridge.lean"])
        self.assertEqual(c["summary"]["elaborated"], c["summary"]["files"])
        self.assertFalse(c["summary"]["complete"])
        self.assertFalse(c["authority_transfer_ready"])
        self.assertIn("PARTIAL run", PROBE.render_table(c))

    def test_a_full_run_that_checks_everything_is_ready(self):
        # the positive twin of the two above: readiness is reachable, so the
        # negatives are not vacuous
        (self.pkg / "TrustIr/Bad.lean").write_text("import TrustIr.Basic\ndef two := 2\n", encoding="utf-8")
        c = self.census()
        self.assertTrue(c["summary"]["complete"])
        self.assertEqual(c["summary"]["elaborated"], 3)
        self.assertTrue(c["authority_transfer_ready"])
        self.assertNotIn("PARTIAL run", PROBE.render_table(c))


class FirstFailure(unittest.TestCase):
    def test_errors_win_over_stderr(self):
        report = {"errors": ["A: boom"], "kernel_failures": ["K"]}
        self.assertEqual(PROBE.first_failure(report, "stderr"), "A: boom")

    def test_no_report_falls_back_to_stderr_tail(self):
        self.assertEqual(PROBE.first_failure(None, "x\n\nError: check failed\n"), "Error: check failed")


class LakefileLeanOptions(unittest.TestCase):
    """G50: the census runs under the options `lake build` compiles with."""

    def lakefile(self, text: str) -> Path:
        tmp = tempfile.mkdtemp()
        self.addCleanup(lambda: __import__("shutil").rmtree(tmp, ignore_errors=True))
        return write_pkg(Path(tmp), {"lakefile.lean": text})

    TRUST_IR = (
        "import Lake\nopen Lake DSL\n\n-- leanOptions := #[⟨`bogus, true⟩] in prose\n"
        "package trust_irSemantics where\n  leanOptions := #[\n    ⟨`autoImplicit, false⟩\n  ]\n\n"
        "@[default_target]\nlean_lib TrustIr where\n  srcDir := \".\"\n"
    )

    def test_trust_ir_lakefile_yields_auto_implicit_false(self):
        options = PROBE.lakefile_lean_options(self.lakefile(self.TRUST_IR))
        self.assertEqual(options, ["autoImplicit=false"])
        self.assertEqual(PROBE.clean_define_args(options), ["-DautoImplicit=false"])

    def test_value_kinds_render_like_lake(self):
        pkg = self.lakefile('package p where\n  leanOptions := #[⟨`maxHeartbeats, 400000⟩, '
                            '⟨`pp.format, "x y"⟩]\n')
        self.assertEqual(PROBE.lakefile_lean_options(pkg),
                         ["maxHeartbeats=400000", 'pp.format="x y"'])

    def test_no_lean_options_is_empty(self):
        self.assertEqual(PROBE.lakefile_lean_options(self.lakefile("package p\n")), [])
        self.assertEqual(PROBE.lakefile_lean_options(self.lakefile("package p where\n  leanOptions := #[]\n")), [])

    def test_more_and_weak_lean_args_defines_in_lake_order(self):
        # Lake: weakLeanArgs ++ (leanOptions ++ moreLeanArgs); -D is last-wins.
        pkg = self.lakefile('package p where\n  moreLeanArgs := #["-DautoImplicit=false", "-D", '
                            '"maxRecDepth=9"]\n  leanOptions := #[⟨`autoImplicit, true⟩]\n'
                            '  weakLeanArgs := #["-DrelaxedAutoImplicit=false"]\n')
        self.assertEqual(PROBE.lakefile_lean_options(pkg),
                         ["relaxedAutoImplicit=false", "autoImplicit=true",
                          "autoImplicit=false", "maxRecDepth=9"])

    def test_unreadable_or_lib_level_options_fail_closed(self):
        for text in ("package p where\n  leanOptions := mathlibLeanOptions\n",
                     "package p where\n  leanOptions := #[⟨`a, someDef⟩]\n",
                     "package p where\n  leanOptions := #[⟨`a, true⟩]\n    ++ #[⟨`b, true⟩]\n",
                     'package p where\n  moreLeanArgs := #["--tstack=100"]\n',
                     'package p where\n  weakLeanArgs := #["-D"]\n',
                     # An attribute on the library's own line still makes it
                     # the owner, never the package above it.
                     "package p where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n\n"
                     "@[default_target] lean_lib Loose where\n"
                     "  leanOptions := #[⟨`autoImplicit, true⟩]\n",
                     'package p\n\n@[default_target] lean_exe e where\n  moreLeanArgs := #["-DautoImplicit=false"]\n',
                     "package p\n\nlean_lib L where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n"):
            with self.assertRaises(PROBE.ProbeError, msg=text):
                PROBE.lakefile_lean_options(self.lakefile(text))


if __name__ == "__main__":
    unittest.main()
