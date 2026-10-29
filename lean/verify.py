"""Fresh source build, exact dependency pins, and complete declaration audit.

Project/vendor oleans are never copied. Pinned external dependency caches are
reused after revision and tracked-source checks. --preflight does not compile.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PINS = {"Foundation": "81810b9f22c49fbb32bd89c1e9737059d83a37e6",
        "mathlib": "0df444a360eaa60ab8c11dca51a86af692955474"}
TERMINAL_FILES = ["Audit.lean", "Part2Audit.lean", "FregeanECA/V2/Certificate.lean",
                  "FregeanECA/V4/Certificate.lean", "FregeanECA/V4/PrintedTheory.lean", "FregeanECA/V4/Choice.lean", "FregeanECA/V4/FregeArithmetic.lean", "FregeanECA/V4/HumeBridge.lean",
                  "FregeanECA/V4/BiInterpretability.lean",
                  "FregeanECA/V4/TruthValues.lean",
                  "FregeanECA/V3/Certificate.lean", "FregeanECA/V3/Cleaner.lean",
                  "FregeanECA/V3/ModelReconstruction.lean", "FregeanECA/V3/Specifications.lean",
                  "FregeanECA/V3/Nontriviality.lean", "FregeanECA/V3/PaperResults.lean",
                  "FregeanECA/V3/SuccessorVerification.lean",
                  "FregeanECA/Certificates/FunctionExtensionality.lean",
                  "FregeanECA/Certificates/ThreeWay.lean",
                  "FregeanECA/Research/Z2Reverse/ProgressCertificate.lean"]
REQUIRED_ENDPOINTS = [
    "FregeanECA.V4.Certificate.checked",
    "FregeanECA.V4.Certificate.printed_theory",
    "FregeanECA.V4.Printed.axioms_iff_cleaner",
    "FregeanECA.V4.Printed.core_to_cleaner",
    "FregeanECA.V4.Printed.provability_iff",
    "FregeanECA.V4.Printed.consistency_iff",
    "FregeanECA.V4.Printed.lawV_provable",
    "FregeanECA.V4.Printed.parametric_comprehension",
    "FregeanECA.V4.Printed.parametric_comprehension_provable",
    "FregeanECA.V4.Printed.countermodel",
    "FregeanECA.V4.Printed.A6_not_provable",
    "FregeanECA.V4.Certificate.inverse",
    "FregeanECA.V4.Certificate.unique_preimage_provable",
    "FregeanECA.V4.Certificate.basic_law_V_and_extensionality_provable",
    "FregeanECA.V4.Certificate.nontriviality_independent",
    "FregeanECA.V4.Certificate.core_combinators_unique",
    "FregeanECA.V4.Certificate.shared_algebra_provability",
    "FregeanECA.V4.Certificate.three_way",
    "FregeanECA.V4.Certificate.equiconsistency",
    "FregeanECA.V4.Certificate.consistent",
    "FregeanECA.V4.Certificate.models_and_consistency",
    "FregeanECA.V4.Certificate.bi_interpretable",
    "FregeanECA.V4.BiInterpretability.bi_interpretability",
    "FregeanECA.V4.BiInterpretability.double_translation_provability",
    "FregeanECA.V4.BiInterpretability.translation_lemma",
    "FregeanECA.V4.Certificate.exact_equations",
    "FregeanECA.V4.Certificate.conservativity",
    "FregeanECA.V4.Certificate.hume_on_number_domain",
    "FregeanECA.V4.Certificate.arithmetic_through_hume",
    "FregeanECA.V4.Certificate.whole_domain_hume",
    "FregeanECA.V4.HumeBridge.internal_hume_cleaner",
    "FregeanECA.V4.HumeBridge.internal_hume_algebra",
    "FregeanECA.V4.HumeBridge.via_hume_Z2_to_cleaner",
    "FregeanECA.V4.HumeBridge.via_hume_Z2_to_algebra",
    "FregeanECA.V4.HumeBridge.whole_domain_hume_model",
    "FregeanECA.V4.Certificate.concepts",
    "FregeanECA.V4.Certificate.collapse",
    "FregeanECA.V4.Certificate.no_horizontal",
    "FregeanECA.V4.Certificate.no_choice_function",
    "FregeanECA.V4.Certificate.frege_arithmetic",
    "FregeanECA.V4.FregeArithmetic.ff_interprets_fa",
    "FregeanECA.V4.FregeArithmetic.fa_interprets_ff",
    "FregeanECA.V4.FregeArithmetic.fa_interprets_algebra",
    "FregeanECA.V4.FregeArithmetic.fa_model_of_ff_model",
    "FregeanECA.V4.FregeArithmetic.ff_model_of_fa_model",
    "FregeanECA.V4.FregeArithmetic.printed_model_of_fa_model",
    "FregeanECA.V4.Choice.no_choice_provable",
    "FregeanECA.V4.Choice.choice_fails",
    "FregeanECA.V4.TruthValues.collapse_provable",
    "FregeanECA.V4.TruthValues.concepts_provable",
    "FregeanECA.V4.TruthValues.strokes_provable",
    "FregeanECA.Part2.FregeArithmeticProofTransfer.interpretation_preserves_falsum",
    "FregeanECA.Part2.HumeInternal.internal_hume_provable",
    "FregeanECA.Part2.HumeInternal.internal_hume_provable_fregean",
    "FregeanECA.Part2.Hume.part_two_has_hume_expansion",
    "FregeanECA.V3.Certificate.checked",
    "FregeanECA.V3.Certificate.program_equations_both",
    "FregeanECA.V3.Certificate.pure_conservativity_three_way",
    "FregeanECA.V3.Certificate.models_and_consistency",
    "FregeanECA.V3.Nontriviality.countermodel",
    "FregeanECA.V3.Nontriviality.A5_not_provable",
    "FregeanECA.V3.PaperResults.inverse",
    "FregeanECA.V3.PaperResults.unique_preimage_provable",
    "FregeanECA.V3.PaperResults.basic_law_V_and_extensionality_provable",
    "FregeanECA.V3.PaperResults.specification",
    "FregeanECA.V3.SuccessorVerification.verifies",
    "FregeanECA.V3.SuccessorVerification.available_domain",
    "FregeanECA.V3.SuccessorVerification.code_identity_provable",
    "FregeanECA.V3.SuccessorVerification.specification_provable",
    "FregeanECA.V3.PaperResults.concrete_models",
    "FregeanECA.V3.PaperResults.concrete_encoded_models",
    "FregeanECA.V3.Certificate.three_way",
    "FregeanECA.V3.Certificate.equiconsistency",
    "FregeanECA.V3.Certificate.consistent",
    "FregeanECA.V3.Certificate.shared_algebra_provability",
    "FregeanECA.V3.Certificate.program_equations",
    "FregeanECA.V3.Certificate.pure_conservativity",
    "FregeanECA.V3.Cleaner.provability_iff_fullFE",
    "FregeanECA.V3.Cleaner.zero_instance_proves_coverage",
    "FregeanECA.V3.Cleaner.core_combinators_unique",
    "FregeanECA.V3.Cleaner.inverse_from_zero_and_A3",
    "FregeanECA.V3.ModelReconstruction.reconstruction",
    "FregeanECA.V3.Specifications.graph_specification",
    "FregeanECA.V3.RelationalComprehension.closure_provability",
    "FregeanECA.V2.pcAlgebra_iff_positiveComprehension",
    "FregeanECA.V2.fcAlgebra_iff_fullComprehension",
    "FregeanECA.V2.pc_algebra_comprehension_provability",
    "FregeanECA.V2.fc_algebra_comprehension_provability",
    "FregeanECA.V2.combined_positive_original_provability",
    "FregeanECA.V2.combined_full_original_provability",
    "FregeanECA.V2.Certificate.checked",
    "FregeanECA.V2.Certificate.standalone",
    "FregeanECA.V2.Certificate.combined",
    "FregeanECA.V2.Certificate.program_equations",
    "FregeanECA.V2.Certificate.computational_conservativity",
    "FregeanECA.V2.Certificate.three_way",
    "FregeanECA.Certificates.ThreeWay.checked",
    "FregeanECA.Part2.MutualInterpretability.three_way",
    "FregeanECA.Part2.MutualInterpretability.equiconsistency",
    "FregeanECA.Part2.MutualInterpretability.FE_to_Z2",
    "FregeanECA.Research.Z2Reverse.ReverseProofTransfer.v2_proof_transfer",
    "FregeanECA.Certificates.FunctionExtensionality.checked",
    "FregeanECA.V2.Certificate.internal_hume",
    "FregeanECA.V2.Certificate.humes_principle",
    "FregeanECA.V2.Certificate.a2_presentation",
    "FregeanECA.V2.Certificate.arithmetic_transfer",
    "FregeanECA.Research.HigherOrderAudit.rows_give_abstraction",
    "FregeanECA.Research.HigherOrderAudit.row_existence_gives_abstraction",
    "FregeanECA.Research.HigherOrderAudit.diagonal_instance_is_inconsistent",
]


def digest(path: Path) -> str:
    # Line endings are normalised so that the hash is the same whether the file
    # was checked out with LF or CRLF (git autocrlf, GitHub archives).
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def code_only(source: str) -> str:
    """Remove nested Lean comments and strings; preserve line boundaries."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(source):
        pair, char = source[i:i + 2], source[i]
        if depth:
            if pair == "/-":
                depth, i = depth + 1, i + 2
            elif pair == "-/":
                depth, i = depth - 1, i + 2
            else:
                out.append("\n" if char == "\n" else " ")
                i += 1
        elif quoted:
            if char == "\\":
                out.append("  ")
                i += 2
            else:
                quoted = char != '"'
                out.append("\n" if char == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth, i = 1, i + 2
            out.append("  ")
        elif pair == "--":
            end = source.find("\n", i)
            if end == -1:
                break
            out.append(" " * (end - i))
            i = end
        elif char == '"':
            quoted, i = True, i + 1
            out.append(" ")
        else:
            out.append(char)
            i += 1
    return "".join(out)


def source_files(root: Path) -> list[Path]:
    return sorted(p for p in root.rglob("*") if p.is_file()
                  and ".lake" not in p.parts and "__pycache__" not in p.parts
                  and (p.suffix in {".lean", ".toml", ".json", ".py"}
                       or p.name == "lean-toolchain"))


def environment() -> dict[str, str]:
    env = os.environ.copy()
    # Process-local ownership exception for the shared cache; never global Git
    # configuration. Exact pins and tracked source cleanliness are checked.
    i = int(env.get("GIT_CONFIG_COUNT", "0"))
    env.update(GIT_CONFIG_COUNT=str(i + 1))
    env[f"GIT_CONFIG_KEY_{i}"] = "safe.directory"
    env[f"GIT_CONFIG_VALUE_{i}"] = "*"
    return env


def run(cmd: list[str], cwd: Path, env: dict[str, str]):
    return subprocess.run(cmd, cwd=cwd, env=env, text=True, encoding="utf-8",
                          errors="replace", stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


def dependency_check(root: Path, env: dict) -> tuple[list[dict], list[str]]:
    manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
    records, failures = [], []
    pins = {p["name"]: p.get("rev") for p in manifest["packages"]}
    for name, rev in PINS.items():
        if pins.get(name) != rev:
            failures.append(f"{name}: expected manifest revision {rev}")
    for package in manifest["packages"]:
        if package["type"] != "git":
            continue
        directory_name = package["name"].removeprefix("«").removesuffix("»")
        path = (root / ".lake/packages" / directory_name).resolve()
        record = {"name": package["name"], "url": package["url"],
                  "pinned_revision": package["rev"], "cache_path": str(path)}
        if not path.is_dir():
            failures.append(f"{package['name']}: missing checkout")
        else:
            head = run(["git", "rev-parse", "HEAD"], path, env)
            dirty = run(["git", "status", "--porcelain", "--untracked-files=no"], path, env)
            record.update(actual_revision=head.stdout.strip(), tracked_changes=dirty.stdout.splitlines())
            if head.returncode or head.stdout.strip() != package["rev"]:
                failures.append(f"{package['name']}: revision mismatch")
            if dirty.returncode or dirty.stdout.strip():
                failures.append(f"{package['name']}: changed tracked sources or failed status")
        records.append(record)
    return records, failures


def junction(link: Path, target: Path, env: dict) -> None:
    if os.name != "nt":
        link.symlink_to(target, target_is_directory=True)
        return
    env = env | {"FREGE_CHECK_LINK": str(link), "FREGE_CHECK_TARGET": str(target)}
    result = run(["powershell", "-NoProfile", "-NonInteractive", "-Command",
                  "New-Item -ItemType Junction -Path $env:FREGE_CHECK_LINK "
                  "-Target $env:FREGE_CHECK_TARGET | Out-Null"], link.parent, env)
    if result.returncode:
        raise RuntimeError(result.stdout)


def audit_source(modules: list[str]) -> str:
    return "\n".join(f"import {name}" for name in modules) + """
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let environment ← getEnv
  let names := environment.constants.toList.filterMap fun (name, info) =>
    let own := name.toString.startsWith "FregeanECA." ||
      name.toString.startsWith "_private.FregeanECA." ||
      name.toString.startsWith "Frege." ||
      name.toString.startsWith "_private.Frege."
    if own then
      match info with
      | .thmInfo _ | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ => some name
      | _ => none
    else none
  let ordered := names.toArray.qsort Name.lt
  for name in ordered do
    let dependencies ← collectAxioms name
    logInfo m!"PROJECT_AXIOMS {name}: {dependencies.toList}"
  logInfo m!"PROJECT_AUDIT_COUNT {ordered.size}"
"""


def main() -> int:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    parser = argparse.ArgumentParser()
    parser.add_argument("--lake", type=Path)
    parser.add_argument("--preflight", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    local = root.parent.parent / "frege-duc-pe/lean/.tools/lean-4.33.1-windows/bin/lake.exe"
    found = args.lake or shutil.which("lake") or (local if local.is_file() else None)
    if found is None:
        parser.error("Install lean-toolchain or supply --lake.")
    lake, env = str(Path(found).resolve()), environment()
    output = root.parent / "verification"
    output.mkdir(exist_ok=True)
    files = source_files(root)
    sources = {p.relative_to(root).as_posix(): digest(p) for p in files}
    forbidden = [p.relative_to(root).as_posix() for p in files if p.suffix == ".lean"
                 and re.search(r"\b(sorry|admit|axiom)\b", code_only(p.read_text(encoding="utf-8")))]
    provenance = json.loads((root / "vendor/PROVENANCE.json").read_text(encoding="utf-8"))
    changed = [name for name, expected in provenance["files"].items()
               if not (root / "vendor" / name.replace("\\", "/")).is_file()
               or digest(root / "vendor" / name.replace("\\", "/")) != expected]
    dependencies, failures = dependency_check(root, env)
    modules = sorted(p.relative_to(root).with_suffix("").as_posix().replace("/", ".")
                     for p in files if p.suffix == ".lean"
                     and "vendor" not in p.relative_to(root).parts)
    vendor_modules = sorted(p.relative_to(root / "vendor").with_suffix("").as_posix().replace("/", ".")
                            for p in files if p.suffix == ".lean"
                            and "vendor" in p.relative_to(root).parts)
    report = {"timestamp_utc": datetime.now(timezone.utc).isoformat(), "success": False,
              "mode": "preflight" if args.preflight else "fresh-source-build", "commands": [],
              "source_sha256": sources, "source_modules": modules,
              "vendor_source_modules": vendor_modules, "admission_scan": forbidden,
              "changed_vendor_sources": changed, "external_dependencies": dependencies,
              "dependency_failures": failures, "toolchain": (root / "lean-toolchain").read_text().strip(),
              "fresh_scope": "Every project/vendor source; no project/vendor oleans copied. Pinned external dependency caches reused.",
              "scope": "Every project and vendor definition and theorem is audited transitively. V4 is the active certificate for the printed theory FF (A1-A6) and NECA + RC; it restates every V3 endpoint and adds the applicative-fragment, truth-value and Hume's Principle results. Inherited V2 certificates are retained as dependencies and regression checks. Paper-to-theorem correspondence is recorded in ../COVERAGE.md. Research/HigherOrderAudit is checked separately and is not a premise of the V4 certificate."}
    okay = not forbidden and not changed and not failures
    if args.preflight:
        report["success"] = okay
        destination = output / "verification-preflight.json"
    else:
        destination = output / "verification.json"
        if okay:
            stage = Path(tempfile.mkdtemp(prefix="fregean-eca-check-")) / "lean"
            shutil.copytree(root, stage, ignore=shutil.ignore_patterns(".lake", "__pycache__"))
            (stage / ".lake").mkdir()
            junction(stage / ".lake/packages", (root / ".lake/packages").resolve(), env)
            audit = stage / "AllDeclarationsAudit.lean"
            importable = modules + vendor_modules
            audit.write_text(audit_source(importable), encoding="utf-8")
            report.update(fresh_directory=str(stage), generated_audit_sha256=digest(audit))
            # Root audit files are standalone Lean entry files, not Lake library
            # targets. Compile them explicitly into the fresh cache before the
            # generated declaration audit imports them.
            library_modules = [name for name in modules
                               if name == "FregeanECA" or name.startswith("FregeanECA.")]
            entry_modules = [name for name in modules if name not in library_modules]
            entry_logs = {"Audit": "terminal-axioms.log", "Part2Audit": "part2-axioms.log"}
            commands = [([lake, "build", *library_modules, *vendor_modules], "fresh-build.log"),
                        ([lake, "env", "lean", "--trust=0", "FregeanECA/V4/Certificate.lean"], "v4-certificate.log"),
                        ([lake, "env", "lean", "--trust=0", "FregeanECA/V3/Certificate.lean"], "v3-certificate.log"),
                        ([lake, "env", "lean", "--trust=0", "FregeanECA/V2/Certificate.lean"], "v2-certificate.log"),
                        ([lake, "env", "lean", "--trust=0", "FregeanECA/Certificates/FunctionExtensionality.lean"], "fe-certificate.log"),
                        ([lake, "env", "lean", "--trust=0", "FregeanECA/Certificates/ThreeWay.lean"], "three-way-certificate.log"),
                        *[([lake, "env", "lean", "--trust=0", "-o",
                            str(stage / ".lake/build/lib/lean" / (name.replace(".", "/") + ".olean")),
                            name.replace(".", "/") + ".lean"],
                           entry_logs.get(name, name.replace(".", "-") + "-audit.log"))
                          for name in entry_modules],
                        ([lake, "env", "lean", "--trust=0", "FregeanECA/Research/HigherOrderAudit.lean"], "research-axioms.log"),
                        ([lake, "env", "lean", "--trust=0", "AllDeclarationsAudit.lean"], "axioms.log")]
            for command, log in commands:
                print(f"Starting {log}; live output: {output / log}", flush=True)
                started = time.monotonic()
                with (output / log).open("w", encoding="utf-8") as stream:
                    result = subprocess.run(command, cwd=stage, env=env,
                                            stdout=stream, stderr=subprocess.STDOUT)
                elapsed = time.monotonic() - started
                report["commands"].append({"command": command, "returncode": result.returncode,
                                           "cwd": str(stage), "log": log,
                                           "elapsed_seconds": round(elapsed, 3)})
                print(f"{log}: exit {result.returncode} ({elapsed:.1f}s)", flush=True)
                if result.returncode:
                    print((output / log).read_text(encoding="utf-8", errors="replace")[-18000:], flush=True)
                    okay = False
                    break
            text = (output / "axioms.log").read_text(encoding="utf-8") if okay else ""
            entries = re.findall(r"PROJECT_AXIOMS ([^:\n]+):\s*\[([^]]*)\]", text)
            closure = {name: [x.strip() for x in values.split(",") if x.strip()] for name, values in entries}
            used = {a for values in closure.values() for a in values}
            unexpected = sorted(used - ALLOWED)
            count = re.search(r"PROJECT_AUDIT_COUNT (\d+)", text)
            count_ok = bool(count and int(count[1]) == len(closure) and closure)
            required = sorted(set(REQUIRED_ENDPOINTS).union(*(re.findall(
                r"#print axioms\s+(\S+)", code_only((root / name).read_text(encoding="utf-8")))
                for name in TERMINAL_FILES)))
            missing = [name for name in required if name not in closure]
            after = {p.relative_to(root).as_posix(): digest(p) for p in source_files(root)}
            drift = sorted(name for name in sources.keys() | after.keys()
                           if sources.get(name) != after.get(name))
            report.update(audited_axiom_dependencies=sorted(used), unexpected_axioms=unexpected,
                          declaration_axioms=closure, audited_declaration_count=len(closure),
                          audit_count_matches=count_ok, required_terminal_declarations=required,
                          missing_audits=missing, source_changes_during_verification=drift)
            okay = okay and not unexpected and not missing and count_ok and not drift
            report["success"] = okay
    destination.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"{'Preflight' if args.preflight else 'Verification'}: {'PASS' if okay else 'FAIL'}")
    for failure in failures:
        print(failure)
    return 0 if okay else 1


if __name__ == "__main__":
    raise SystemExit(main())
