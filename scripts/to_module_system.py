#!/usr/bin/env python3
"""
Convert Pi1 Lean files to use the module system:
1. Add `module` after the copyright header (or at the top)
2. Replace `import` with `public import`
3. Add `@[expose] public section` after imports and any module doc comment
"""

import re
import sys
from pathlib import Path


def transform(content: str) -> str:
    lines = content.split('\n')
    # Strip trailing empty string that results from a trailing newline
    if lines and lines[-1] == '':
        lines = lines[:-1]

    i = 0
    result = []

    # 1. Consume copyright block (/- ... -/) if the file starts with one
    first = lines[i].strip() if i < len(lines) else ''
    if first.startswith('/-') and not first.startswith('/-!'):
        while i < len(lines):
            result.append(lines[i])
            has_end = '-/' in lines[i]
            i += 1
            if has_end:
                break

    # Insert `module` (with a blank line after it)
    result.append('module')
    result.append('')

    # Skip any blank lines in the source that followed the copyright (or file start)
    while i < len(lines) and not lines[i].strip():
        i += 1

    # 2. Consume import lines, converting them to `public import`
    imports: list[str] = []
    while i < len(lines) and re.match(r'^import\s', lines[i]):
        imports.append('public ' + lines[i])
        i += 1

    result.extend(imports)

    # Skip blank lines after imports
    while i < len(lines) and not lines[i].strip():
        i += 1

    # Blank line before the doc comment / expose section
    result.append('')

    # 3. Consume a module-level doc comment (/-! ... -/) if present
    if i < len(lines) and lines[i].strip().startswith('/-!'):
        while i < len(lines):
            result.append(lines[i])
            has_end = '-/' in lines[i]
            i += 1
            if has_end:
                break
        result.append('')

    # Skip blank lines so we don't double up
    while i < len(lines) and not lines[i].strip():
        i += 1

    # 4. Insert @[expose] public section
    result.append('@[expose] public section')

    # 5. Append the rest of the file unchanged (blank separator only if there is more content)
    remaining = lines[i:]
    if remaining:
        result.append('')
        result.extend(remaining)

    return '\n'.join(result) + '\n'


def process_file(path: Path, dry_run: bool = False) -> None:
    original = path.read_text(encoding='utf-8')
    transformed = transform(original)
    if transformed == original:
        return
    if dry_run:
        print(f'[dry-run] would modify {path}')
    else:
        path.write_text(transformed, encoding='utf-8')
        print(f'modified {path}')


def main() -> None:
    dry_run = '--dry-run' in sys.argv

    root = Path(__file__).parent.parent
    targets = sorted(root.glob('Pi1/**/*.lean')) + [root / 'Pi1.lean']

    for path in targets:
        process_file(path, dry_run=dry_run)


if __name__ == '__main__':
    main()
