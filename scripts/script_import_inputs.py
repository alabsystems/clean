"""Derive the transitive sibling Python inputs of a script without importing them."""

import ast
from pathlib import Path


def first_party_imports(script: Path) -> list[str]:
    """Return repo-relative sibling .py imports, including function-local imports.

    This is the flat scripts/ module walk also used by the Crystal readers;
    packages and dynamic import expressions are outside this helper's contract.
    """
    here = script.resolve().parent
    seen: set[Path] = set()
    todo = [script.resolve()]
    while todo:
        tree = ast.parse(todo.pop().read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            names = [alias.name for alias in node.names] if isinstance(node, ast.Import) else (
                [node.module] if isinstance(node, ast.ImportFrom) and node.module and not node.level
                else [])
            for name in names:
                candidate = here / (name.split(".")[0] + ".py")
                if (candidate.is_file() and candidate.resolve() != script.resolve()
                        and candidate not in seen):
                    seen.add(candidate)
                    todo.append(candidate)
    return sorted(path.relative_to(here.parent).as_posix() for path in seen)
