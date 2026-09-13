#!/usr/bin/env python3
"""Generate/check NR03 sources; never invoke Lean, Lake, Git or network."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile

BASE = "91a1588f3141580cd1a0b95b6d22a7b32681fa97"
COVERAGE_SHA256 = "31c175f842514d021a827386b3628f09a82fd7bb1e25f279749d2cb38866fdac"
INTERFACES_SHA256 = "f3d40b245b3f1e7b22bc82a1597d18239ef1e07e27e7fee3c3e00102215872e1"
CHANGED_EXISTING = {
    "development/NR03/NLA/NR03/FamilyIdentities.lean",
    "development/NR03/NLA/NR03/Certificate.lean",
    "development/NR03/ci_compile.py",
    "development/NR03/SOURCE_INPUTS.json",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def encoded(value: object) -> bytes:
    return (json.dumps(value, indent=2) + "\n").encode()


def write_or_check(path: Path, data: bytes, check: bool) -> None:
    if check:
        if not path.is_file() or path.read_bytes() != data:
            raise RuntimeError(f"Generated source mismatch: {path}")
        return
    if path.is_file() and path.read_bytes() == data:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, pending = tempfile.mkstemp(prefix="." + path.name + ".", dir=path.parent)
    with os.fdopen(fd, "wb") as stream:
        stream.write(data)
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(pending, path)


def generated_block(block: dict) -> str:
    family, title = block["family"], block["title"]
    body = f"""/-
Generated NR-03 literal-row certificates; see row-certificates/INTERFACES.md.
Each row uses its own closed kernel decision. The predecessor import makes
heavy row reductions sequential during ordinary Lake dependency builds.
No earlier probe source is imported. This source awaits full verification.
-/
import {block['predecessor']}
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

namespace NLA.NR03.RowCertificate.{title}

"""
    for row in block["rows"]:
        n = row["value"]
        body += f"""theorem row{n} : ∀ b : Mask7,
    {family}Sum ({n} : Mask7) b = {family}Closed ({n} : Mask7) b := by
  decide +kernel

#print axioms {row['declaration']}

"""
    return body + f"end NLA.NR03.RowCertificate.{title}\n"


def generated_families(template: str, coverage: dict) -> str:
    last = coverage["blocks"][-1]["module"]
    assert template.count("import NLA.NR03.Core\n") == 1
    result = template.replace("import NLA.NR03.Core\n",
                              f"import NLA.NR03.Core\nimport {last}\n", 1)
    for family in coverage["families"]:
        name, title = family["family"], family["title"]
        old = (f"theorem {name}_identity : {family['full_type']} := by\n"
               "  decide +kernel\n")
        assert result.count(old) == 1
        new = (f"theorem {name}_identity : {family['full_type']} := by\n"
               "  intro a\n  fin_cases a\n")
        new += "".join(f"  · exact RowCertificate.{title}.row{n}\n" for n in range(128))
        new += f"\n#print axioms NLA.NR03.{name}_identity\n"
        result = result.replace(old, new, 1)
    return result


def generated_driver(template: str, coverage: dict) -> str:
    start = template.index("# Two independent grouped-row probes.")
    end = template.index("\n\n\ndef sha", start)
    modules = [(n, f"NLA/NR03/{n}.lean") for n in
               ["Definitions", "Encoding", "FamilyDefs", "Index", "Core"]]
    modules += [(b["module"].removeprefix("NLA.NR03."), b["path"])
                for b in coverage["blocks"]]
    modules += [(n, f"NLA/NR03/{n}.lean") for n in
                ["FamilyIdentities", "Certificate", "Rank"]]
    modules += [("Solution", "Solution.lean")]
    block = ("# Full original development proof graph. Heavy literal-row modules\n"
             "# are ordered in one explicit import chain, also enforcing sequential\n"
             "# heavy reductions in ordinary Lake dependency builds.\nMODULES = [\n")
    block += "".join(f'    ("{name}", Path("{path}")),\n' for name, path in modules)
    block += "]"
    result = template[:start] + block + template[end:]
    old = """            "purpose": "NR-03 grouped closed-row family probes only",
            "full_family_obligations_checked": False,
            "restricted_probe_rows": {"first": 120, "last": 127, "count": 8},
            "rows_per_closed_lemma": 1,
            "closed_row_lemmas_per_grouped_module": 8,
            "restricted_probe_columns": 128,"""
    new = """            "purpose": "NR-03 complete original proof graph development compilation",
            "full_family_obligations_in_scope": True,
            "literal_rows_per_family": 128,
            "columns_per_family": 128,
            "closed_row_lemmas_per_module": 8,
            "sequential_row_module_count": 48,"""
    assert result.count(old) == 1
    return result.replace(old, new, 1)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root", required=True, type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    project = args.project_root.resolve()
    support = project / "row-certificates"
    repo = project.parents[1]
    coverage_bytes = (support / "COVERAGE.json").read_bytes()
    interfaces = (support / "INTERFACES.md").read_bytes()
    assert sha(coverage_bytes) == COVERAGE_SHA256
    assert sha(interfaces) == INTERFACES_SHA256
    coverage = json.loads(coverage_bytes)
    baseline = json.loads((support / "BASE-HASHES.json").read_text())
    assert coverage["base_commit"] == baseline["base_commit"] == BASE
    for rel, digest in baseline["files"].items():
        if rel not in CHANGED_EXISTING:
            assert sha((repo / rel).read_bytes()) == digest, rel
    for family in coverage["families"]:
        rows = [r["value"] for b in coverage["blocks"]
                if b["family"] == family["family"] for r in b["rows"]]
        assert rows == list(range(128))
    assert len(coverage["blocks"]) == 48
    assert len({r["declaration"] for b in coverage["blocks"] for r in b["rows"]}) == 384
    predecessor = "NLA.NR03.FamilyDefs"
    for block in coverage["blocks"]:
        assert block["predecessor"] == predecessor
        assert len(block["rows"]) == 8
        assert block["path"] == block["module"].replace(".", "/") + ".lean"
        predecessor = block["module"]
    outputs = {block["path"]: generated_block(block).encode()
               for block in coverage["blocks"]}
    templates = support / "templates"
    for name in ["FamilyIdentities.lean", "Certificate.lean", "ci_compile.py"]:
        rel = "development/NR03/" + ("NLA/NR03/" if name.endswith(".lean") else "") + name
        assert sha((templates / name).read_bytes()) == baseline["files"][rel]
    outputs["NLA/NR03/FamilyIdentities.lean"] = generated_families(
        (templates / "FamilyIdentities.lean").read_text(), coverage).encode()
    certificate = (templates / "Certificate.lean").read_text()
    assert certificate.count("exact Nat.pow_pos hp _") == 1
    outputs["NLA/NR03/Certificate.lean"] = certificate.replace(
        "exact Nat.pow_pos hp _", "exact Nat.pow_pos hp", 1).encode()
    outputs["ci_compile.py"] = generated_driver(
        (templates / "ci_compile.py").read_text(), coverage).encode()
    for rel, data in outputs.items():
        write_or_check(project / rel, data, args.check)
    input_names = ["BASE-HASHES.json", "COVERAGE.json", "INTERFACES.md", "generate.py",
                   "templates/FamilyIdentities.lean", "templates/Certificate.lean",
                   "templates/ci_compile.py"]
    source_manifest = {
        "purpose": "Deterministic source generation only; full graph uncompiled",
        "base_commit": BASE,
        "coverage_sha256": COVERAGE_SHA256,
        "interfaces_sha256": INTERFACES_SHA256,
        "row_modules": 48,
        "row_lemmas": 384,
        "sequential_import_chain": coverage["sequential_heavy_dependency_chain"],
        "inputs": {"row-certificates/" + n: sha((support / n).read_bytes()) for n in input_names},
        "outputs": {rel: sha(data) for rel, data in outputs.items()},
        "excluded_to_avoid_self_hash_cycle": ["row-certificates/SOURCE-MANIFEST.json", "SOURCE_INPUTS.json"],
    }
    write_or_check(support / "SOURCE-MANIFEST.json", encoded(source_manifest), args.check)
    source_files = sorted(p for p in project.rglob("*") if p.is_file()
                          and p != project / "SOURCE_INPUTS.json"
                          and ".lake" not in p.relative_to(project).parts
                          and "__pycache__" not in p.relative_to(project).parts)
    workflow = repo / ".github/workflows/lean-nr03-development.yml"
    source_files.append(workflow)
    inventory = {str(p.relative_to(repo)): sha(p.read_bytes()) for p in source_files}
    source_inputs = {
        "purpose": "Complete NR03 family row-certificate development graph; not canonical verification",
        "repository": "sgstepaniants/OpenProblemsInNLA",
        "base_commit": BASE,
        "base_run": 34778330872,
        "generation_manifest": "development/NR03/row-certificates/SOURCE-MANIFEST.json",
        "files": inventory,
    }
    write_or_check(project / "SOURCE_INPUTS.json", encoded(source_inputs), args.check)
    print(json.dumps({"mode": "check" if args.check else "generate",
                      "row_modules": 48, "row_lemmas": 384,
                      "source_input_files": len(inventory),
                      "source_manifest_sha256": sha(encoded(source_manifest)),
                      "local_Lean_Lake_executed": False}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
