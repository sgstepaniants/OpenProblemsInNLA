#!/usr/bin/env python3
"""Static byte/statement checks only; this script does not execute Lean."""
import difflib
import hashlib
import json
import pathlib
import re

P = pathlib.Path(__file__).resolve().parent
sha = lambda b: hashlib.sha256(b).hexdigest()
before = json.loads((P / "BEFORE-BINDINGS.json").read_text())
paths = [r["author_path"] for r in before["all27_active_plus_frozen_challenge_exact_source_matches"]
         if r["author_path"] != "Challenge.lean"]
assert len(paths) == 27
for rel, expected in json.loads((P / "BEFORE-MANIFEST.json").read_text()).items():
    assert sha((P / rel).read_bytes()) == expected, ("before packet changed", rel)

def header(text, name):
    m = re.search(r"(?m)^theorem\s+" + re.escape(name) + r"\b([\s\S]*?)\s*:=", text)
    assert m, name
    return " ".join(m.group(0).removesuffix(":=").split())

def all_headers(text):
    pattern = r"(?m)^(?:@\[[^\n]*\]\s+)?(?:private\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+\S+[\s\S]*?\s*:="
    return [" ".join(m.group(0).split()) for m in re.finditer(pattern, text)]

def strip_comments(text):
    out = []
    depth = 0
    i = 0
    while i < len(text):
        if text[i:i + 2] == "/-":
            depth += 1
            i += 2
        elif depth and text[i:i + 2] == "-/":
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text[i:i + 2] == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            i += 1
    assert depth == 0
    return "".join(out)

changed = []
source_hashes = {}
headers_count = 0
diff = []
modified_declarations = {}
allowed_modified_declarations = {
    "NLA/IE13/LateColumn.lean": ["oldRows_subset_frontRows", "front_not_old_label", "late_column_zero_at"],
    "NLA/IE13/WitnessEntries.lean": ["early_original_upper_support"],
    "NLA/IE13/WitnessForward.lean": ["forward_window", "forward_lower_action", "targetFactorColumn_original"],
}

def declaration_segments(text):
    matches = list(re.finditer(r"(?m)^(?:(?:private|noncomputable)\s+)?(?:theorem|lemma|def|abbrev)\s+(\S+)", text))
    if not matches:
        return text, []
    return text[:matches[0].start()], [(m.group(1), text[m.start():matches[j + 1].start() if j + 1 < len(matches) else len(text)])
                                    for j, m in enumerate(matches)]

for path in paths:
    old = (P / "before" / path).read_text()
    new = (P / "after" / path).read_text()
    source_hashes[path] = sha((P / "after" / path).read_bytes())
    assert all_headers(old) == all_headers(new), ("declaration changed", path)
    headers_count += len(all_headers(new))
    assert re.findall(r"(?m)^import\s+.*$", old) == re.findall(r"(?m)^import\s+.*$", new)
    code = strip_comments(new)
    assert not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b|debug\.skipKernelTC", code), path
    assert not re.search(r"(?m)^import\s+.*Challenge", code), path
    old_prefix, old_segments = declaration_segments(old)
    new_prefix, new_segments = declaration_segments(new)
    assert old_prefix == new_prefix, ("preamble changed", path)
    assert [n for n, _ in old_segments] == [n for n, _ in new_segments], path
    modified = [n for (n, a), (_, b) in zip(old_segments, new_segments) if a != b]
    assert modified == allowed_modified_declarations.get(path, []), (path, modified)
    if modified:
        modified_declarations[path] = modified
    if old != new:
        changed.append(path)
        diff += list(difflib.unified_diff(old.splitlines(keepends=True), new.splitlines(keepends=True),
                         fromfile="before/" + path, tofile="after/" + path))
assert changed == ["NLA/IE13/LateColumn.lean", "NLA/IE13/WitnessEntries.lean",
                   "NLA/IE13/WitnessForward.lean"]
for name, row in before["all28_public_headers"].items():
    assert header((P / "after" / row["source"]).read_text(), name) == row["normalized_header"], name
for path, expected in before["frozen_files_sha256"].items():
    assert sha((P / "after" / path).read_bytes()) == expected, ("frozen file changed", path)
assert len(before["all28_public_headers"]) == 28
assert len(before["frozen_files_sha256"]) == 10

receipt_path = P / "actual-run/artifacts/lean-development-statements/receipt.json"
receipt = json.loads(receipt_path.read_text())
for row in before["all27_active_plus_frozen_challenge_exact_source_matches"]:
    blob = P / "actual-git" / row["receipt_key"]
    assert sha(blob.read_bytes()) == receipt["source_sha256"][row["receipt_key"]] == row["sha256"]
assert receipt["repository_commit"] == before["actual_commit"]
for command in receipt["commands"]:
    assert sha((receipt_path.parent / command["log"]).read_bytes()) == command["sha256"]
checks = {
    "kind": "author static proof-body repair audit; not Lean execution",
    "actual_failed_run": 35058147856,
    "actual_failed_commit": before["actual_commit"],
    "root_audit_sha256": before["root_audit_sha256"],
    "all27_before_exact_git_and_receipt_bound": True,
    "all27_after_sha256": source_hashes,
    "changed_sources": changed,
    "all_declaration_headers_unchanged": True,
    "declaration_headers_compared": headers_count,
    "only_seven_existing_proof_bodies_modified": modified_declarations,
    "all28_public_headers_unchanged": True,
    "all10_frozen_files_unchanged": True,
    "imports_unchanged_and_no_challenge_import": True,
    "active_source_no_admissions_custom_axioms_native_or_unsafe": True,
    "all_actual_command_log_hashes_match_receipt": True,
    "independent_runtime_manifest_sha256": before["independent_runtime_manifest_sha256"],
    "actual_repaired_compilation": False,
    "local_Lean_or_Lake": False,
    "strict_checker_run_for_repair": False,
    "Comparator_run_for_repair": False,
    "whole_problem_verified": False,
    "limitations": "Text header and source audit complements, but does not replace, future kernel compilation and independent Comparator acceptance. The authenticated run is a development failure on the before sources."
}
(P / "repair.patch").write_text("".join(diff))
(P / "CHECKS.json").write_text(json.dumps(checks, indent=2) + "\n")
print(json.dumps({"status": "static checks pass", "sources": len(paths), "changed": len(changed),
                  "headers": headers_count, "frozen": 10, "public_contracts": 28,
                  "CHECKS_sha256": sha((P / "CHECKS.json").read_bytes())}, indent=2))
