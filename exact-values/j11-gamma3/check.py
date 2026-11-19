"""Check the archived endpoint proof, or rebuild it with the Lean kernel."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

from prepare_steel import prepare_sources


ROOT = Path(__file__).resolve().parent
SHARED = ROOT.parents[1] / "laver_table_lower_bounds" / "lean"
MANIFEST = ROOT / "verification" / "sources.json"
FINAL = "Gamma11.RankI3.j11_gamma3_exact"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def check_axioms(output):
    for name in (FINAL, "Gamma11.RankI3.finite_table_reading_of_I3"):
        found = re.search(re.escape(f"'{name}' depends on axioms:") + r"\s*\[([^\]]*)\]", output)
        if not found or {v.strip() for v in found[1].split(",")} != ALLOWED:
            raise ValueError(f"Missing or unexpected axiom report for {name}")


def check_replays(transcript, modules):
    if "sorryAx" in transcript or re.findall(r"^replaying ([\w.]+)$", transcript, re.M) != list(modules):
        raise ValueError("Kernel replay inventory differs from the module list")
    check_axioms(transcript)


def check_archive(manifest):
    expected = manifest["modules"]
    if set(expected) != {file.stem for file in (ROOT / "lean").glob("*.lean")}:
        raise ValueError("Module inventory differs from the verification record")
    logs = []
    for folder, files in [(ROOT / "lean", {n + ".lean": h for n, h in expected.items()}),
                          (ROOT / "verification", manifest["logs"])]:
        for filename, digest in files.items():
            data = (folder / filename).read_bytes().replace(b"\r\n", b"\n")
            if hashlib.sha256(data).hexdigest() != digest:
                raise ValueError(f"Source or log differs from the archive: {filename}")
            if filename.endswith(".log"):
                logs.append(data.decode("utf-8"))
    check_replays("\n".join(logs), expected)
    fresh_log = manifest["atlas_rebuild"]
    data = (ROOT / "verification" / fresh_log["log"]).read_bytes().replace(b"\r\n", b"\n")
    if hashlib.sha256(data).hexdigest() != fresh_log["sha256_lf"]:
        raise ValueError("The Atlas source rebuild log differs from its recorded hash")
    check_replays(data.decode("utf-8"), [*manifest["steel_modules"], *expected])


def rebuild(args, manifest):
    suffix = ".exe" if os.name == "nt" else ""
    lean = args.lean_bin.resolve() / ("lean" + suffix)
    checker = args.lean_bin.resolve() / ("leanchecker" + suffix)
    version = subprocess.check_output([lean, "--version"], text=True)
    if not re.search(r"\bversion " + re.escape(manifest["lean_version"]) + r"\b", version):
        raise ValueError(f"Expected Lean {manifest['lean_version']}, found {version.strip()}")
    mathlib = args.mathlib.resolve()
    packages = (args.packages or mathlib / ".lake/packages").resolve()
    libraries = [SHARED / ".build/lean", mathlib / ".lake/build/lib/lean"]
    if not (libraries[0] / "LaverLowerBounds/StandardLine.olean").is_file():
        raise ValueError("Build the shared finite-table project first (laver_table_lower_bounds/lean/build.py).")
    if not (libraries[1] / "Mathlib/SetTheory/ZFC/VonNeumann.olean").is_file():
        raise ValueError("A Mathlib build including Mathlib.SetTheory.ZFC.VonNeumann is required.")
    libraries.extend(sorted(packages.glob("*/.lake/build/lib/lean")))
    build = args.build_dir.resolve()
    steel = build / "steel-src"
    objects = build / "lib"
    objects.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["LEAN_NAT_MAX_SIZE"] = "201326592"
    log_path = build / ("rebuild.log" if args.part == "all" else f"{args.part}.log")
    components = []
    if args.part in ("all", "steel"):
        prepare_sources(args.upstream.resolve(), mathlib, steel, manifest)
        components.append((steel, list(manifest["steel_modules"])))
    if args.part in ("all", "core"):
        components.append((ROOT / "lean", [n for n in manifest["modules"] if not n.startswith("RankSteel")]))
    if args.part in ("all", "endpoint"):
        components.append((ROOT / "lean", [n for n in manifest["modules"] if n.startswith("RankSteel")]))

    def run(command, log):
        result = subprocess.run(command, env=env, cwd=build, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, encoding="utf-8", errors="replace",
                                timeout=600)
        log.write(result.stdout)
        log.flush()
        if result.returncode or "sorryAx" in result.stdout:
            raise RuntimeError(f"{command[-1]} failed\n{result.stdout}")
        return result.stdout

    with log_path.open("w", encoding="utf-8") as log:
        for src, modules in components:
            for name in modules:
                imports = libraries if src == steel or name.startswith("Rank") else libraries[:1]
                env["LEAN_PATH"] = os.pathsep.join(map(str, [objects, *imports]))
                relative = Path(*name.split("."))
                output = (objects / relative).with_suffix(".olean")
                output.parent.mkdir(parents=True, exist_ok=True)
                print(f"Checking {name}", flush=True)
                options = ["-M", "1800", "-j", "1", "-R", str(src)]
                if src != steel:
                    options += ["-DwarningAsError=true"]
                report = run([lean, *options, "-o", str(output), str((src / relative).with_suffix(".lean"))], log)
                run([checker, "-v", name], log)
                if name == "RankSteelEndpoint":
                    check_axioms(report)
    print(f"PASS: rebuilt and replayed {sum(len(names) for _, names in components)} modules. Log: {log_path}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rebuild", action="store_true", help="compile and replay all endpoint and Steel modules")
    parser.add_argument("--part", choices=("all", "steel", "core", "endpoint"), default="all",
                        help="steel and core are independent; endpoint imports both")
    parser.add_argument("--lean-bin", type=Path, help="directory containing lean and leanchecker")
    parser.add_argument("--mathlib", type=Path, help="prebuilt Mathlib source checkout")
    parser.add_argument("--upstream", type=Path, help="FrenzyMath/LaverTable Git checkout")
    parser.add_argument("--packages", type=Path, help="Mathlib dependency checkout directory (default .lake/packages)")
    parser.add_argument("--build-dir", type=Path, default=ROOT / ".build")
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    check_archive(manifest)
    print(f"PASS: {len(manifest['modules'])} endpoint sources and their original receipts, plus the "
          f"{len(manifest['steel_modules']) + len(manifest['modules'])}-module Atlas replay and final axioms.",
          flush=True)
    if args.rebuild:
        if not args.lean_bin or not args.mathlib or (args.part in ("all", "steel") and not args.upstream):
            parser.error("--rebuild needs --lean-bin and --mathlib; the Steel build also needs --upstream")
        rebuild(args, manifest)


if __name__ == "__main__":
    main()
