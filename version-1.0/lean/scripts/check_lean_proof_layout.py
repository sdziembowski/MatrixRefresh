#!/usr/bin/env python3
"""Check the three public Lean modules and the proof import boundary.

Each root module contains one admitted main statement. Construction certificates
are named definitions admitted in public and proved under Proofs/; every such
definition must be a comparator target.
Proofs/ReferenceClaims.lean imports the public modules as the challenge.
All other source files are admission-free.
Main theorem proofs belong under Proofs/. Every local import must resolve, and
public files must not import the proof tree, even indirectly.
Run from version-1.0/lean: python3 scripts/check_lean_proof_layout.py
"""

from collections import deque
import json
import os
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[2]
PUBLIC_FILES = {
    "Compiler.lean", "Refreshing.lean", "EfficientSimulation.lean",
}
PROOF_FOLDERS = {"Compiler", "Refreshing", "EfficientSimulaiton"}
PROOF_ENTRYPOINTS = {"ReferenceClaims.lean", "ProvedClaims.lean"}
REFERENCE_FILE = "Proofs/ReferenceClaims.lean"
PUBLIC_REFERENCES = {
    "Refreshing.lean": "Refreshing.main_theorem",
    "Compiler.lean": "Compiler.main_theorem",
    "EfficientSimulation.lean": "EfficientSimulation.main_theorem",
}
COMMAND = re.compile(
    r"^(?:@\[[^\n]*?\]\s*)?"
    r"(?:(?:noncomputable|private|protected)\s+)*"
    r"(?:abbrev|def|structure|inductive|theorem|lemma|instance|example|axiom|"
    r"namespace|section|end|variable|open|set_option|universe|attribute|include|omit)\b",
    re.MULTILINE,
)
IMPORT = re.compile(
    r"^[ \t]*(?:(?:public|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?"
    r"([\w.']+)", re.MULTILINE,
)


def code_only(source):
    """Mask nested comments and strings, preserving offsets and line numbers."""
    result = list(source)
    i = 0
    while i < len(source):
        start = i
        if source.startswith("/-", i):
            depth = 1
            i += 2
            while depth and i < len(source):
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("Unclosed block comment")
        elif source.startswith("--", i):
            stop = source.find("\n", i)
            i = len(source) if stop < 0 else stop
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            i += 1
            continue
        result[start:i] = ["\n" if c == "\n" else " " for c in source[start:i]]
    return "".join(result)


def commands_with_namespaces(code):
    """Yield top-level commands with their active namespace and source span."""
    commands = list(COMMAND.finditer(code))
    scopes = []
    for index, command in enumerate(commands):
        stop = commands[index + 1].start() if index + 1 < len(commands) else len(code)
        declaration = code[command.start():stop]
        head = re.match(
            r"(?:@\[[^\n]*?\]\s*)*"
            r"(?:(?:noncomputable|private|protected)\s+)*"
            r"(abbrev|def|structure|inductive|theorem|lemma|instance|example|axiom|"
            r"namespace|section|end|variable|open|set_option|universe|attribute|include|omit)\b"
            r"(?:\s+([\w']+(?:\.[\w']+)*))?",
            declaration,
        )
        if head is None:
            continue
        kind, local_name = head.groups()
        if kind == "namespace":
            scopes.append((kind, local_name or ""))
            continue
        if kind == "section":
            scopes.append((kind, local_name or ""))
            continue
        if kind == "end":
            if scopes:
                scopes.pop()
            continue
        namespace = ".".join(name for scope_kind, name in scopes
                             if scope_kind == "namespace" and name)
        name = f"{namespace}.{local_name}" if namespace and local_name else local_name
        yield kind, name, command.start(), stop, declaration


def violations(relative, source, certificate_targets, seen_certificates):
    """Enforce public admissions and prohibit admissions in all proof files."""
    code = code_only(source)
    masked = list(code)
    path = relative.as_posix()
    expected = PUBLIC_REFERENCES.get(path)
    main_count = 0
    errors = []
    for kind, name, start, stop, declaration in commands_with_namespaces(code):
        if path == REFERENCE_FILE and kind in {
            "theorem", "lemma", "example", "def", "abbrev", "instance",
            "inductive", "structure", "axiom",
        }:
            errors.append((start, "the reference aggregator must only import public modules"))
        if expected is None:
            continue
        if kind in {"theorem", "lemma", "example"}:
            if kind == "theorem" and name == expected:
                main_count += 1
                body = declaration.rsplit(":=", 1)
                if len(body) != 2 or body[1].split() not in (["sorry"], ["by", "sorry"]):
                    errors.append((start, f"{expected} must be admitted with `by sorry`"))
                else:
                    masked[start:stop] = ["\n" if c == "\n" else " " for c in declaration]
            else:
                errors.append((start, f"public theorem/lemma {name or '(unnamed)'} belongs under Proofs/"))
        # Both forms are definitions for the comparator; `abbrev` can keep
        # reducibility hints stable across admitted and proved certificates.
        if kind in {"def", "abbrev"} and name in certificate_targets:
            seen_certificates.setdefault(name, []).append(path)
            body = declaration.rsplit(":=", 1)
            if len(body) != 2 or body[1].split() not in (["sorry"], ["by", "sorry"]):
                errors.append((start, f"audited certificate {name} must be admitted with `by sorry`"))
            else:
                masked[start:stop] = ["\n" if c == "\n" else " " for c in declaration]
    if expected is not None and main_count != 1:
        errors.append((0, f"expected exactly one main theorem named {expected}"))
    remaining = "".join(masked)
    for match in re.finditer(r"\b(?:sorry|admit|axiom)\b", remaining):
        errors.append((match.start(), f"unexpected {match.group()!r}"))
    return [f"{relative}:{source.count(chr(10), 0, offset) + 1}: {message}"
            for offset, message in errors]


def source_modules(lean_root):
    """Discover local modules without traversing dependency/build caches."""
    modules = {}
    for folder, directories, files in os.walk(lean_root):
        directories[:] = sorted(d for d in directories if not d.startswith("."))
        for filename in sorted(files):
            if filename.endswith(".lean"):
                path = Path(folder) / filename
                relative = path.relative_to(lean_root).with_suffix("")
                modules[".".join(relative.parts)] = path
    return modules


def layout_violations(lean_root, modules):
    """Keep the three public files and the three proof topics in their intended locations."""
    errors = []
    relatives = {path.relative_to(lean_root) for path in modules.values()}
    root_files = {path.name for path in relatives if len(path.parts) == 1}
    for missing in sorted(PUBLIC_FILES - root_files):
        errors.append(f"{missing}: missing top-level public file")
    for unexpected in sorted(root_files - PUBLIC_FILES):
        errors.append(f"{unexpected}: unexpected top-level Lean file")
    for path in sorted(relatives):
        if len(path.parts) > 1 and path.parts[0] != "Proofs":
            errors.append(f"{path.as_posix()}: nested Lean sources belong under Proofs/")
    proof_files = {path.parts[1] for path in relatives
                   if len(path.parts) == 2 and path.parts[0] == "Proofs"}
    for missing in sorted(PROOF_ENTRYPOINTS - proof_files):
        errors.append(f"Proofs/{missing}: missing audit entrypoint")
    for unexpected in sorted(proof_files - PROOF_ENTRYPOINTS):
        errors.append(f"Proofs/{unexpected}: proof implementations belong in a topic subfolder")
    proof_folders = {path.parts[1] for path in relatives
                     if len(path.parts) > 2 and path.parts[0] == "Proofs"}
    for missing in sorted(PROOF_FOLDERS - proof_folders):
        errors.append(f"Proofs/{missing}/: missing proof topic")
    for unexpected in sorted(proof_folders - PROOF_FOLDERS):
        errors.append(f"Proofs/{unexpected}/: unexpected proof topic")
    return errors


def external_roots(lean_root):
    """Recognize toolchain modules and roots of installed Lake packages."""
    roots = {"Init", "Lean", "Std", "Lake"}
    packages = lean_root / ".lake" / "packages"
    if packages.is_dir():
        for package in packages.iterdir():
            if not package.is_dir():
                continue
            for path in package.iterdir():
                if path.is_file() and path.suffix == ".lean":
                    roots.add(path.stem)
                elif path.is_dir() and not path.name.startswith("."):
                    # A package may have no aggregate <Root>.lean module.
                    if next(path.rglob("*.lean"), None) is not None:
                        roots.add(path.name)
    return roots


def imports_in(source):
    """Read import names after masking comments and string literals."""
    return [match.group(1) for match in IMPORT.finditer(code_only(source))]


def import_violations(modules, imports, external):
    """Reject unresolved project imports, including misspelled module roots."""
    local_roots = {name.split(".", 1)[0] for name in modules}
    errors = []
    for module, dependencies in sorted(imports.items()):
        for dependency in dependencies:
            root = dependency.split(".", 1)[0]
            if dependency in modules:
                continue
            if root in local_roots or root not in external:
                path = module.replace(".", "/") + ".lean"
                errors.append(f"{path}: unresolved local import {dependency}")
    return errors


def boundary_violations(imports):
    """Find a shortest public-to-proof dependency chain for each public module."""
    errors = []
    for start in sorted(imports):
        if start + ".lean" not in PUBLIC_FILES:
            continue
        queue = deque([(start,)])
        seen = {start}
        while queue:
            chain = queue.popleft()
            current = chain[-1]
            if current.split(".", 1)[0] == "Proofs":
                path = start.replace(".", "/") + ".lean"
                errors.append(f"{path}: public model imports the proof tree: "
                              + " → ".join(chain))
                break
            for dependency in imports.get(current, []):
                if dependency not in seen:
                    seen.add(dependency)
                    queue.append((*chain, dependency))
    return errors


def audit_environment_violations(imports):
    """Keep reference and proof audit environments separate."""
    errors = []
    reference_imports = imports.get("Proofs.ReferenceClaims", [])
    expected = {"Refreshing", "Compiler", "EfficientSimulation"}
    if len(reference_imports) != 3 or set(reference_imports) != expected:
        errors.append("Proofs/ReferenceClaims.lean: import exactly the three public modules")

    queue = deque([("Proofs.ProvedClaims",)])
    seen = {"Proofs.ProvedClaims"}
    while queue:
        chain = queue.popleft()
        current = chain[-1]
        if current in expected:
            errors.append("Proofs/ProvedClaims.lean: proof environment imports an admitted public module: "
                          + " → ".join(chain))
            break
        for dependency in imports.get(current, []):
            if dependency not in seen:
                seen.add(dependency)
                queue.append((*chain, dependency))
    return errors


def public_import_violations(imports):
    """Enforce the requested Refreshing → Compiler → EfficientSimulation order."""
    earlier = {
        "Refreshing": set(),
        "Compiler": {"Refreshing"},
        "EfficientSimulation": {"Refreshing", "Compiler"},
    }
    errors = []
    for module, allowed_local in earlier.items():
        for dependency in imports.get(module, []):
            if dependency == "Mathlib" or dependency.startswith("Mathlib."):
                continue
            if dependency in allowed_local:
                continue
            errors.append(f"{module}.lean: disallowed import {dependency}; "
                          "public modules may import Mathlib and earlier public modules only")
    return errors


def main():
    errors = []
    lean_root = ROOT / "lean"
    comparator = json.loads((lean_root / "comparator.json").read_text(encoding="utf-8"))
    certificate_list = comparator.get("definition_names", [])
    certificate_targets = set(certificate_list)
    if len(certificate_targets) != len(certificate_list):
        errors.append("comparator.json: duplicate definition_names target")
    if set(comparator["theorem_names"]) != set(PUBLIC_REFERENCES.values()):
        errors.append("comparator.json: theorem_names must be the three public main theorems")
    seen_certificates = {}
    modules = source_modules(lean_root)
    errors.extend(layout_violations(lean_root, modules))
    imports = {}
    for module, path in sorted(modules.items()):
        relative = path.relative_to(lean_root)
        source = path.read_text(encoding="utf-8")
        errors.extend(violations(relative, source, certificate_targets, seen_certificates))
        imports[module] = imports_in(source)
    for name in sorted(certificate_targets):
        locations = seen_certificates.get(name, [])
        if len(locations) != 1:
            errors.append(f"comparator.json: certificate {name} must occur exactly once in a public file"
                          f" (found {len(locations)})")
    errors.extend(import_violations(modules, imports, external_roots(lean_root)))
    errors.extend(public_import_violations(imports))
    errors.extend(boundary_violations(imports))
    errors.extend(audit_environment_violations(imports))
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Lean proof layout: {len(modules)} files checked; three public files at "
          "the root, one admitted main theorem in each, "
          f"{len(certificate_targets)} comparator-audited construction certificates, "
          "and ordered public imports independent of Proofs/.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
