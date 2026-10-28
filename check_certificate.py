#!/usr/bin/env python3
"""Check the certificate of the Functional Frege Lean development.

Run from the root of the artefact (double-click `check-certificate.cmd` on
Windows, or `python3 check_certificate.py` anywhere). Needs Python 3.9+.

Offline check (default; a few seconds; no Lean needed):
  1. reads verification/verification.json, the machine-readable record of the
     fresh-source verification reported in the manuscript;
  2. recomputes the SHA-256 hash of every Lean source file in lean/ and
     compares it with the hash recorded at verification time, so the sources
     in this folder are exactly the ones that were verified;
  3. confirms that every required endpoint was audited and depends on nothing
     beyond Lean's three standard axioms (propext, Classical.choice,
     Quot.sound), and prints the certificate: each printed result of the
     paper with its Lean theorem(s) and their axioms.

Kernel check (`--run`; double-click `check-certificate-with-lean.cmd`):
  builds the development and re-elaborates FregeanECA/V4/Certificate.lean
  with the Lean kernel in --trust=0 mode, printing V4 CERTIFICATE PASS or the
  rejection message. Needs the Lean toolchain; with `--install` (or when the
  script asks and you answer y) it installs elan, which installs the pinned
  Lean 4.33.1, and fetches the prebuilt Mathlib library (several gigabytes).
"""
from __future__ import annotations

import hashlib
import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
import urllib.request
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
LEAN = ROOT / "lean"
RECORD = ROOT / "verification" / "verification.json"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
CERT = "FregeanECA.V4.Certificate."
ELAN_BIN = Path.home() / ".elan" / "bin"

# Printed results of the manuscript and the certificate theorems that state them.
RESULTS = [
    ("Definition 2.1 (def:tf): the printed axioms have the models and theorems of the encoding",
     [CERT + "printed_theory"]),
    ("Proposition 2.2 (prop:inverse): delta is bijective; application is evaluation after its inverse",
     [CERT + "inverse", CERT + "unique_preimage_provable"]),
    ("Proposition 2.3 (prop:blv): abstract identity, function identity, pointwise agreement; extensionality",
     [CERT + "basic_law_V_and_extensionality_provable"]),
    ("Proposition 2.4 (prop:nontriviality): A5 is independent of A1-A4",
     [CERT + "nontriviality_independent"]),
    ("Theorem 3.4 (thm:correspondence): K and S unique; same consequences in the shared language",
     [CERT + "core_combinators_unique", CERT + "shared_algebra_provability"]),
    ("Proposition 3.5 (prop:reconstruction): recovery of the structures",
     ["FregeanECA.V3.ModelReconstruction.reconstruction"]),
    ("Theorem 3.6 (thm:bi-interpretability): FF and NECA + RC are bi-interpretable",
     [CERT + "bi_interpretable"]),
    ("Theorems 4.2, 4.3, Corollary 4.4 (thm:arithmetic, thm:reverse, thm:three-way): "
     "six proof-transfer arrows; equiconsistency",
     [CERT + "three_way", CERT + "equiconsistency"]),
    ("Theorem 4.5 (thm:consistency): a model of both theories; consistency",
     [CERT + "models_and_consistency"]),
    ("Theorem 5.1 (thm:equations): provable equations are exactly beta-eta conversions",
     [CERT + "exact_equations"]),
    ("Theorem 5.2 (thm:conservativity): same pure applicative sentences in NECA, NECA + RC, FF",
     [CERT + "conservativity"]),
    ("Proposition 6.1 (prop:concepts): truth values and connectives as objects; quantification as identity",
     [CERT + "concepts"]),
    ("Theorem 6.2 (thm:collapse): every bivalent object is constant; no horizontal, strokes, tests",
     [CERT + "collapse", CERT + "no_horizontal"]),
    ("Proposition 6.3 (prop:choice): no object is a choice function; FF + AC_f is inconsistent",
     [CERT + "no_choice_function"]),
    ("Theorem 7.1 (thm:hume): Hume's Principle on the number domain",
     [CERT + "hume_on_number_domain"]),
    ("Corollary 7.2 (cor:frege-theorem): Z2 through Hume's Principle",
     [CERT + "arithmetic_through_hume"]),
    ("Proposition 7.3 (prop:hume-expansion): a model of whole-domain Hume's Principle",
     [CERT + "whole_domain_hume"]),
    ("All of the above as one statement",
     [CERT + "checked"]),
]


def sha256(path: Path) -> str:
    # Line endings are normalised, as in verify.py, so the hash is the same
    # whether the file was checked out with LF or CRLF.
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def offline() -> bool:
    if not RECORD.exists():
        print(f"FAIL: {RECORD} not found; run this file from the artefact root.")
        return False
    record = json.loads(RECORD.read_text(encoding="utf-8"))
    print("Functional Frege: certificate check (offline)")
    print("=" * 72)
    print(f"Verified run:    {record.get('timestamp_utc', '?')} UTC")
    print(f"Toolchain:       {record.get('toolchain', '?')}")
    print(f"Recorded result: {'PASS' if record.get('success') else 'FAIL'}")
    print(f"Modules audited: {len(record.get('source_modules', []))} project, "
          f"{len(record.get('vendor_source_modules', []))} vendored; "
          f"{record.get('audited_declaration_count', '?')} declarations; "
          f"{len(record.get('required_terminal_declarations', []))} required endpoints")
    ok = bool(record.get("success"))

    # 1. The Lean sources in this folder are the ones that were verified.
    hashes: dict[str, str] = record.get("source_sha256", {})
    mismatched, missing = [], []
    for rel, digest in hashes.items():
        p = LEAN / rel
        if not p.exists():
            missing.append(rel)
        elif sha256(p) != digest:
            mismatched.append(rel)
    print()
    print(f"Source hashes:   {len(hashes)} files recorded; "
          f"{len(hashes) - len(mismatched) - len(missing)} match, "
          f"{len(mismatched)} differ, {len(missing)} missing")
    for rel in mismatched[:10]:
        print(f"   differs:  lean/{rel}")
    for rel in missing[:10]:
        print(f"   missing:  lean/{rel}")
    if mismatched or missing:
        ok = False

    # 2. Every required endpoint was audited and uses only the standard axioms.
    axioms: dict[str, list[str]] = record.get("declaration_axioms", {})
    required = record.get("required_terminal_declarations", [])
    bad = []
    for name in required:
        if name not in axioms:
            bad.append((name, "not audited"))
        elif set(axioms[name]) - ALLOWED:
            bad.append((name, ", ".join(sorted(set(axioms[name]) - ALLOWED))))
    print(f"Endpoints:       {len(required)} required; "
          f"{len(required) - len(bad)} audited with standard axioms only")
    for name, why in bad[:10]:
        print(f"   PROBLEM: {name}: {why}")
    if bad:
        ok = False

    # 3. The certificate, result by result.
    print()
    print("Certificate: printed result -> Lean theorem [axioms]")
    print("-" * 72)
    for label, names in RESULTS:
        print(label)
        for name in names:
            ax = axioms.get(name)
            if ax is None:
                status = "NOT AUDITED"
                ok = False
            elif set(ax) - ALLOWED:
                status = "EXTRA AXIOMS: " + ", ".join(sorted(ax))
                ok = False
            else:
                status = "ok [" + ", ".join(sorted(ax)) + "]" if ax else "ok [no axioms]"
            print(f"   {name}")
            print(f"      {status}")
    print("-" * 72)
    print("CERTIFICATE " + ("PASS" if ok else "FAIL") + " (offline check of the recorded verification)")
    return ok


def find_lake() -> str | None:
    exe = "lake.exe" if os.name == "nt" else "lake"
    for cand in [os.environ.get("LAKE"), shutil.which("lake"), str(ELAN_BIN / exe)]:
        if cand and Path(cand).exists():
            return cand
    return None


def install_elan() -> bool:
    """Install elan (the Lean version manager) for the current user."""
    print("Installing elan (the Lean version manager) ...")
    try:
        if os.name == "nt":
            url = "https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-pc-windows-msvc.zip"
            with tempfile.TemporaryDirectory() as tmp:
                data = urllib.request.urlopen(url, timeout=120).read()
                zipfile.ZipFile(io.BytesIO(data)).extractall(tmp)
                init = next(Path(tmp).rglob("elan-init.exe"))
                subprocess.run([str(init), "-y", "--default-toolchain", "none"], check=True)
        else:
            script = urllib.request.urlopen("https://elan.lean-lang.org/elan-init.sh", timeout=120).read()
            subprocess.run(["sh", "-s", "--", "-y", "--default-toolchain", "none"], input=script, check=True)
    except Exception as e:  # noqa: BLE001
        print(f"elan installation failed: {e}")
        print("Install it by hand from https://github.com/leanprover/elan and run this file again with --run.")
        return False
    os.environ["PATH"] = str(ELAN_BIN) + os.pathsep + os.environ.get("PATH", "")
    return find_lake() is not None


def live(install: bool) -> bool:
    print()
    print("Kernel check with Lean")
    print("=" * 72)
    lake = find_lake()
    if lake is None:
        print("Lean's build tool `lake` was not found on this computer.")
        if not install and sys.stdin and sys.stdin.isatty():
            try:
                install = input("Install Lean now (elan + Lean 4.33.1 + prebuilt Mathlib, several GB)? [y/N] ").strip().lower() == "y"
            except EOFError:
                install = False
        if not install or not install_elan():
            print("Skipping the kernel check. To run it later: install elan from")
            print("  https://github.com/leanprover/elan")
            print("and run this file again with --run.")
            return False
        lake = find_lake()
    print(f"Using {lake}")
    print("Step 1/3: fetching the prebuilt Mathlib library (one large download; skipped if present) ...")
    subprocess.run([lake, "exe", "cache", "get"], cwd=LEAN)
    print("Step 2/3: building the development (the first build takes some minutes) ...")
    build = subprocess.run([lake, "build", "FregeanECA.V4.Certificate"], cwd=LEAN)
    if build.returncode != 0:
        print("BUILD FAILED; see the messages above.")
        return False
    print("Step 3/3: re-elaborating the certificate with the kernel (--trust=0) ...")
    run = subprocess.run([lake, "env", "lean", "--trust=0", "FregeanECA/V4/Certificate.lean"],
                         cwd=LEAN, capture_output=True, text=True, encoding="utf-8", errors="replace")
    out = run.stdout + run.stderr
    for line in out.splitlines():
        if "CERTIFICATE" in line or "depends on axioms" in line or "error" in line.lower():
            print("   " + line[:220])
    passed = run.returncode == 0 and "V4 CERTIFICATE PASS" in out
    print("KERNEL CHECK " + ("PASS" if passed else "FAIL"))
    return passed


def main() -> int:
    ok = offline()
    if "--run" in sys.argv:
        ok = live("--install" in sys.argv) and ok
    if sys.stdin and sys.stdin.isatty() and ("--no-pause" not in sys.argv):
        try:
            input("\nPress Enter to close.")
        except EOFError:
            pass
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
