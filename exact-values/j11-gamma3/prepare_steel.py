"""Reconstruct the sources used in the recorded Steel port from pinned inputs."""
import hashlib
from pathlib import Path
import re
import subprocess

IMPORT = re.compile(r"^import ([\w.]+)", re.MULTILINE)
MATH_IMPORT = re.compile(r"^((?:(?:private|public|meta) )*import (?:all )?)(Mathlib\.[\w.]+)", re.MULTILINE)


def port_steel_module(name, upstream, revision):
    path = Path(*name.split(".")).with_suffix(".lean")
    source = subprocess.check_output(
        ["git", "-C", str(upstream), "show", f"{revision}:{path.as_posix()}"]
    ).decode("utf-8").replace("\r\n", "\n")
    if name == "Comparator.Statement":
        # Steel uses only the set language and its models. The rest defines PA provability.
        source = source.split("/-- **Laver's function", 1)[0] + "\nend LaverTables\n"
        source = source.replace("import Foundation.FirstOrder.Arithmetic.Schemata\n", "")
        source = source.replace("import Mathlib.SetTheory.Cardinal.Finite\n", "")
        # Lean 4.33's implicit transparency checks must see the rank subtype.
        source = source.replace("def VSet (lam :", "abbrev VSet (lam :")
    if name == "LaverTables.Foundations.SetLanguage":
        # Keep the bounded variables in VSet for the two explicit subtype witnesses.
        source = source.replace("  simp [Fin.snoc]", "  simp [-Subtype.forall, Fin.snoc]")
    if name == "LaverTables.Foundations.Elementarity":
        source = source.replace("simpa [Matrix.comp_vecCons', relMap_memRel] using h", "exact h")
    if name == "LaverTables.Algebra.SigmaCong":
        source = source.replace("Fin.castLE (by norm_num) i", "Fin.castLE (by decide : 3 ≤ 6) i")
    if name == "LaverTables.Algebra.DeltaZeroApp":
        source = source.replace("↔ a.val ∈ b.val\n    simp\n", "↔ a.val ∈ b.val\n    rfl\n")
    # The published theorem fixes ZFSet at level 0. Recheck its proof
    # after replacing this one universe by a parameter at every use.
    source = source.replace(".{0}", ".{vsteel}").replace(".{1}", ".{vsteel+1}")
    source = re.sub(r"\bType 1\b", "Type (vsteel+1)", source)
    last = list(IMPORT.finditer(source))[-1].end()
    return source[:last] + "\n\nuniverse vsteel" + source[last:]


def prepare_sources(upstream, mathlib, destination, manifest):
    expected = manifest["steel_modules"]

    def rewrite_import(match):
        local = match[2].replace("Mathlib.", "SteelDeps.", 1)
        return match[1] + local if local in expected else match[0]

    for name, digest in expected.items():
        path = Path(*name.split(".")).with_suffix(".lean")
        if name.startswith("SteelDeps."):
            source = (mathlib / "Mathlib" / path.relative_to("SteelDeps")).read_text(encoding="utf-8")
        else:
            source = port_steel_module(name, upstream, manifest["steel_revision"])
        source = MATH_IMPORT.sub(rewrite_import, source)
        if hashlib.sha256(source.encode("utf-8")).hexdigest() != digest:
            raise ValueError(f"Reconstructed source differs from the verified {name}")
        output = destination / path
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(source, encoding="utf-8", newline="\n")
