#!/usr/bin/env python3
"""Check the registered Lean sources offline, with an optional kernel replay.

Uses only Python's standard library, Lean 4.19.0, and an already compiled
mathlib installation. No dependency download or network command is run.
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from typing import Any


CACHE_SCHEMA = 2
LIBRARIES = ("LocalLaw", "SpectralConsequences")
LEAN_VERSION = "4.19.0"
KERNEL_COMPLETION = (
    "PASSED: every safe declaration from all 1371 project modules replayed "
    "through the Lean kernel at trust level zero."
)


def digest_file(path: Path) -> str:
    """SHA-256 of the complete file contents."""
    hasher = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def digest_json(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def lean_code_without_comments_or_strings(source: str) -> str:
    """Blank nested comments and strings, preserving offsets and line numbers."""
    result = list(source)
    index = depth = 0
    line_comment = string = False
    while index < len(source):
        char = source[index]
        pair = source[index:index + 2]
        if line_comment:
            if char == "\n":
                line_comment = False
            else:
                result[index] = " "
        elif depth:
            if pair == "/-":
                result[index:index + 2] = [" ", " "]
                depth += 1
                index += 1
            elif pair == "-/":
                result[index:index + 2] = [" ", " "]
                depth -= 1
                index += 1
            elif char != "\n":
                result[index] = " "
        elif string:
            if char != "\n":
                result[index] = " "
            if char == "\\" and index + 1 < len(source):
                index += 1
                if source[index] != "\n":
                    result[index] = " "
            elif char == '"':
                string = False
        elif pair in ("--", "/-"):
            result[index:index + 2] = [" ", " "]
            line_comment = pair == "--"
            depth = int(pair == "/-")
            index += 1
        elif char == '"':
            result[index] = " "
            string = True
        index += 1
    return "".join(result)


def imports(path: Path) -> list[str]:
    code = lean_code_without_comments_or_strings(path.read_text(encoding="utf-8"))
    result: list[str] = []
    for line in code.splitlines():
        match = re.match(r"^\s*import\s+(.+)$", line)
        if match:
            result.extend(match[1].split())
    return result


def reject_project_placeholders(path: Path) -> None:
    code = lean_code_without_comments_or_strings(path.read_text(encoding="utf-8"))
    forbidden = re.search(r"(?<![\w'])(?:sorry|sorryAx|admit|axiom)(?![\w'])", code)
    if forbidden:
        line = code.count("\n", 0, forbidden.start()) + 1
        raise RuntimeError(f"Forbidden proof placeholder or axiom at {path}:{line}: "
                           f"{forbidden[0]}")


def is_project_module(module: str) -> bool:
    return any(module == name or module.startswith(name + ".") for name in LIBRARIES)


def module_source(source_root: Path, module: str) -> Path:
    if not re.fullmatch(r"(?:LocalLaw|SpectralConsequences)(?:\.[A-Za-z0-9_]+)+", module):
        raise RuntimeError(f"Invalid project module name: {module}")
    source = source_root / (module.replace(".", "/") + ".lean")
    if not source.is_file():
        raise RuntimeError(f"Missing source module: {source}")
    return source


def stable_modules(source_root: Path) -> tuple[list[str], dict[str, list[str]]]:
    """Validate both complete registries and return their joint dependency order.

    Every .lean file in the two library directories must occur in a Main
    registry, apart from the two Main/Audit pairs, which are mandatory roots.
    Cross-library imports participate in the same topological ordering.
    """
    source_root = source_root.resolve()
    registry: list[str] = []
    roots: list[str] = []
    discovered: set[str] = set()
    for library in LIBRARIES:
        directory = source_root / library
        if not directory.is_dir():
            raise RuntimeError(f"Missing library source directory: {directory}")
        registry.extend(imports(module_source(source_root, library + ".Main")))
        roots.extend((library + ".Main", library + ".Audit"))
        for source in directory.rglob("*.lean"):
            discovered.add(".".join(source.relative_to(source_root).with_suffix("").parts))
    declared = {name for name in registry if is_project_module(name)} | set(roots)
    unlisted = sorted(discovered - declared)
    missing = sorted(declared - discovered)
    if unlisted:
        raise RuntimeError("Unregistered Lean source modules: " + ", ".join(unlisted))
    if missing:
        raise RuntimeError("Registered modules have no source file: " + ", ".join(missing))

    ordered: list[str] = []
    dependency_map: dict[str, list[str]] = {}
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(module: str) -> None:
        if module in visiting:
            raise RuntimeError(f"Project import cycle at {module}")
        if module in visited:
            return
        if module not in declared:
            raise RuntimeError(f"Project import {module} is absent from the Main registries")
        visiting.add(module)
        dependencies = [name for name in imports(module_source(source_root, module))
                        if is_project_module(name)]
        dependency_map[module] = dependencies
        for dependency in dependencies:
            visit(dependency)
        visiting.remove(module)
        visited.add(module)
        ordered.append(module)

    for module in [*registry, *roots]:
        if is_project_module(module):
            visit(module)
    if visited != discovered:
        raise RuntimeError("Source inventory and checked registry do not agree")
    return ordered, dependency_map


def compiled_paths(mathlib: Path, build_root: Path) -> list[Path]:
    """Project output first, then only compiled mathlib/dependency directories.

    Ambient LEAN_PATH is deliberately not inherited: another checkout must
    not silently supply a project module or an untracked external dependency.
    """
    candidates = [build_root, mathlib / ".lake/build/lib/lean"]
    for parent in (mathlib.parent, mathlib / ".lake/packages"):
        if parent.is_dir():
            candidates.extend(child / ".lake/build/lib/lean"
                              for child in sorted(parent.iterdir())
                              if (child / ".lake/build/lib/lean").is_dir())
    result: list[Path] = []
    for candidate in candidates:
        resolved = candidate.expanduser().resolve()
        if resolved not in result:
            result.append(resolved)
    return result


def installation_fingerprint(lean: Path, paths: list[Path], version: str) -> str:
    """Fingerprint the compiler and every external compiled artifact.

    paths[0] is this project's own output and is excluded. Its artifacts have
    independent content hashes in the project cache. External .olean files
    and Lean's runtime .olean files are hashed, not merely identified by age.
    """
    libraries = list(paths[1:])
    runtime = lean.parent.parent / "lib/lean"
    if not runtime.is_dir():
        raise RuntimeError(f"Lean runtime libraries unavailable: {runtime}")
    if runtime not in libraries:
        libraries.append(runtime)
    inventory: list[tuple[str, int, int, str]] = []
    for library in libraries:
        if not library.is_dir():
            raise RuntimeError(f"Compiled module directory unavailable: {library}")
        inventory.append((str(library), 0, 0, ""))
        for artifact in sorted(library.rglob("*.olean")):
            info = artifact.stat()
            inventory.append((str(artifact), info.st_size, info.st_mtime_ns,
                              digest_file(artifact)))
    return digest_json({
        "schema": CACHE_SCHEMA,
        "lean": str(lean),
        "lean_sha256": digest_file(lean),
        "version": version,
        "libraries": inventory,
    })


def resolve_lean(source_root: Path) -> Path:
    requested = os.environ.get("LEAN_BIN") or shutil.which("lean")
    if not requested:
        raise RuntimeError("Lean unavailable. Install Lean 4.19.0 or set LEAN_BIN.")
    located = shutil.which(requested) if os.sep not in requested else requested
    if not located:
        raise RuntimeError(f"Lean executable unavailable: {requested}")
    launcher = Path(located).expanduser().absolute()
    if not launcher.is_file() or not os.access(launcher, os.X_OK):
        raise RuntimeError(f"Lean executable unavailable: {launcher}")
    # elan's lean proxy may be a hard link, not a symlink. `elan run` without
    # --install resolves an already installed pinned toolchain without fetching.
    elan = launcher.with_name("elan")
    if elan.is_file() and os.path.samefile(launcher, elan):
        pin = source_root / "lean-toolchain"
        toolchain = pin.read_text(encoding="utf-8").strip() if pin.is_file() else "leanprover/lean4:v4.19.0"
        command = [str(elan), "run", toolchain, "lean", "--print-prefix"]
    else:
        command = [str(launcher), "--print-prefix"]
    prefix = subprocess.check_output(command, cwd=source_root, text=True,
                                     stderr=subprocess.STDOUT).strip()
    actual = (Path(prefix) / "bin/lean").expanduser().resolve()
    if not actual.is_file() or not os.access(actual, os.X_OK):
        raise RuntimeError(f"Lean --print-prefix did not identify an installed compiler: {prefix}")
    return actual


def save_cache(path: Path, cache: dict[str, Any]) -> None:
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(cache, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def suspicious_output(output: str) -> bool:
    return bool(re.search(r"\bpanic\b|\berror:", output, flags=re.IGNORECASE))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rebuild", action="store_true", help="compile every registered module")
    parser.add_argument("--kernel", action="store_true", help="also replay all project proofs at trust level zero")
    parser.add_argument("--verbose-cache", action="store_true", help="list every checked cache hit")
    parser.add_argument("--audit-only", action="store_true", help="check source inventory and placeholders without Lean")
    args = parser.parse_args()
    if args.audit_only and (args.kernel or args.rebuild):
        parser.error("--audit-only cannot be combined with --kernel or --rebuild")

    source_root = Path(__file__).resolve().parent.parent
    ordered, dependencies = stable_modules(source_root)
    sources = {module: module_source(source_root, module) for module in ordered}
    for source in sources.values():
        reject_project_placeholders(source)
    source_hashes = {module: digest_file(path) for module, path in sources.items()}

    def verify_sources() -> None:
        if stable_modules(source_root) != (ordered, dependencies):
            raise RuntimeError("Source registry or inventory changed during this check; rerun")
        for module, source in sources.items():
            if digest_file(source) != source_hashes[module]:
                raise RuntimeError(f"Source changed during this check: {source}; rerun")

    if args.audit_only:
        verify_sources()
        counts = ", ".join(f"{library}: {sum(name.startswith(library + '.') for name in ordered)}"
                           for library in LIBRARIES)
        print(f"Audit passed: {len(ordered)} registered modules ({counts}); no proof placeholders or project axioms.")
        return 0

    lean = resolve_lean(source_root)
    version = subprocess.check_output([str(lean), "--version"], cwd=source_root,
                                      text=True, stderr=subprocess.STDOUT).strip()
    if not re.search(r"\bversion " + re.escape(LEAN_VERSION) + r"(?=[,\s)])", version):
        raise RuntimeError(f"Expected Lean {LEAN_VERSION}; found {version}")
    print(version, flush=True)
    mathlib = Path(os.environ.get("MATHLIB_ROOT", str(source_root / ".lake/packages/mathlib"))).expanduser().resolve()
    if not (mathlib / ".lake/build/lib/lean/Mathlib.olean").is_file():
        raise RuntimeError(f"Compiled mathlib unavailable: {mathlib}. Set MATHLIB_ROOT; this checker does not download it.")
    build_root = Path(os.environ.get("BUILD_DIR", str(source_root / ".lake/build/lib/lean"))).expanduser().resolve()
    paths = compiled_paths(mathlib, build_root)
    installation = installation_fingerprint(lean, paths, version)
    module_hashes: dict[str, str] = {}
    for module in ordered:
        module_hashes[module] = digest_json({
            "source": source_hashes[module], "installation": installation,
            "dependencies": [(name, module_hashes[name]) for name in dependencies[module]],
            "source_root": str(source_root),
        })
    environment = os.environ.copy()
    environment["LEAN_PATH"] = os.pathsep.join(str(path) for path in paths)
    build_root.mkdir(parents=True, exist_ok=True)
    cache_path = build_root / "project-checks.json"
    replay_source = source_root / "scripts/KernelReplay.lean"
    replay_hash = digest_file(replay_source) if args.kernel else None
    if args.kernel:
        reject_project_placeholders(replay_source)

    with (build_root / ".project-build.lock").open("a+") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        try:
            cache = json.loads(cache_path.read_text(encoding="utf-8"))
        except (FileNotFoundError, json.JSONDecodeError):
            cache = {}
        if not isinstance(cache, dict) or cache.get("schema") != CACHE_SCHEMA:
            cache = {"schema": CACHE_SCHEMA, "modules": {}}
        if not isinstance(cache.get("modules"), dict):
            cache["modules"] = {}
        entries = cache["modules"]
        checked = cached = 0
        for module in ordered:
            if digest_file(sources[module]) != source_hashes[module]:
                raise RuntimeError(f"Source changed during this build: {sources[module]}")
            output = build_root / (module.replace(".", "/") + ".olean")
            previous = entries.get(module, {})
            if (not args.rebuild and isinstance(previous, dict) and output.is_file()
                    and previous.get("input_sha256") == module_hashes[module]
                    and previous.get("output_sha256") == digest_file(output)):
                cached += 1
                if args.verbose_cache:
                    print(f"{module}: cached checked artifact.", flush=True)
                continue
            output.parent.mkdir(parents=True, exist_ok=True)
            temporary = output.with_suffix(".olean.tmp")
            temporary.unlink(missing_ok=True)
            print(f"{module}: checking.", flush=True)
            result = subprocess.run([str(lean), f"--root={source_root}", "-o", str(temporary), str(sources[module])],
                                    cwd=source_root, env=environment, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            print(result.stdout, end="", flush=True)
            if result.returncode or suspicious_output(result.stdout) or not temporary.is_file():
                temporary.unlink(missing_ok=True)
                entries.pop(module, None)
                save_cache(cache_path, cache)
                raise RuntimeError(f"Lean did not check {module} cleanly (exit {result.returncode})")
            if digest_file(sources[module]) != source_hashes[module]:
                temporary.unlink(missing_ok=True)
                entries.pop(module, None)
                save_cache(cache_path, cache)
                raise RuntimeError(f"Source changed while Lean checked it: {sources[module]}")
            temporary.replace(output)
            entries[module] = {"input_sha256": module_hashes[module], "output_sha256": digest_file(output)}
            save_cache(cache_path, cache)
            checked += 1
            print(f"{module}: checked.", flush=True)

        def verify_artifacts() -> None:
            for module in ordered:
                output = build_root / (module.replace(".", "/") + ".olean")
                if not output.is_file() or digest_file(output) != entries[module]["output_sha256"]:
                    raise RuntimeError(f"Checked artifact changed during this check: {output}")

        verify_sources()
        verify_artifacts()
        if installation_fingerprint(lean, paths, version) != installation:
            raise RuntimeError("External Lean dependencies changed during the build; rerun")
        print(f"Passed: {checked} compiled, {cached} cached; {len(ordered)} modules.", flush=True)
        if args.kernel:
            print("Kernel audit (--trust=0): replaying both complete registries.", flush=True)
            result = subprocess.run([str(lean), "--trust=0", "--stdin"],
                                    input=replay_source.read_text(encoding="utf-8"), text=True,
                                    cwd=source_root, env=environment,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            print(result.stdout, end="", flush=True)
            if result.returncode or suspicious_output(result.stdout) or KERNEL_COMPLETION not in result.stdout:
                raise RuntimeError(f"Kernel replay did not complete cleanly (exit {result.returncode}); an exit status alone is insufficient")
            verify_sources()
            verify_artifacts()
            if installation_fingerprint(lean, paths, version) != installation:
                raise RuntimeError("External Lean dependencies changed during the kernel audit; rerun")
            if digest_file(replay_source) != replay_hash:
                raise RuntimeError("Kernel replay driver changed during the audit; rerun")
            print("Passed: Lean kernel audit with --trust=0.", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (RuntimeError, OSError, subprocess.CalledProcessError) as error:
        print(f"Check failed: {error}", file=sys.stderr)
        raise SystemExit(1)
