#!/usr/bin/env python3
"""Extract Lean 4 definitions, stripping proofs and imports.

Outputs the "API surface" of .lean files: type signatures, structure/inductive
definitions, computational defs, and context (variable/namespace/open), while
dropping proof bodies and imports.
"""

import sys
import os
import re
import argparse


def collect_lean_files(args):
    """Return list of .lean file paths from CLI args (or recursive cwd scan)."""
    if not args:
        args = ["."]
    files = []
    for arg in args:
        if os.path.isfile(arg):
            files.append(arg)
        elif os.path.isdir(arg):
            for root, dirs, fnames in os.walk(arg):
                # Skip .lake build directory
                dirs[:] = [d for d in dirs if d != ".lake"]
                for f in sorted(fnames):
                    if f.endswith(".lean"):
                        files.append(os.path.join(root, f))
    return files


def parse_blocks(lines):
    """Parse lines into blocks.

    A block = a top-level line (column 0, non-blank) plus all indented
    continuation lines until the next blank or column-0 line.

    Block comments (/-...-/) are tracked: lines inside block comments are
    always attached to the current block regardless of indentation.
    """
    blocks = []
    i = 0
    n = len(lines)
    comment_depth = 0

    while i < n:
        line = lines[i]
        # Skip blank lines between blocks
        if not line.strip() and comment_depth == 0:
            blocks.append([line])
            i += 1
            continue

        # Start a new block
        block = [line]
        # Update comment depth for first line
        comment_depth = _update_comment_depth(line, comment_depth)
        i += 1

        # Continue block with indented lines or lines inside block comments
        while i < n:
            next_line = lines[i]
            if comment_depth > 0:
                # Inside block comment: always continue
                block.append(next_line)
                comment_depth = _update_comment_depth(next_line, comment_depth)
                i += 1
                continue
            # Outside block comment: continue if indented and non-blank
            if next_line.strip() and (next_line[0] == " " or next_line[0] == "\t"):
                block.append(next_line)
                comment_depth = _update_comment_depth(next_line, comment_depth)
                i += 1
            else:
                break

        blocks.append(block)

    return blocks


def _update_comment_depth(line, depth):
    """Track /- ... -/ nesting depth changes across a single line."""
    i = 0
    n = len(line)
    while i < n - 1:
        if line[i] == "/" and line[i + 1] == "-":
            depth += 1
            i += 2
        elif line[i] == "-" and line[i + 1] == "/":
            depth = max(0, depth - 1)
            i += 2
        else:
            i += 1
    return depth


# Keywords that cause the entire block to be skipped
SKIP_KEYWORDS = {"import", "#check", "#eval", "#print"}

# Keywords for context lines — keep entire block
CONTEXT_KEYWORDS = {
    "variable", "namespace", "section", "end", "open", "universe",
    "set_option", "attribute", "deriving", "scoped", "infix", "infixl",
    "infixr", "notation", "prefix", "postfix", "macro", "macro_rules",
    "syntax", "declare_syntax_cat", "elab", "elab_rules",
}

# Keywords whose proof body should be stripped
PROOF_KEYWORDS = {"theorem", "lemma", "example"}

# Keywords for type definitions — keep entire block
TYPE_KEYWORDS = {"structure", "inductive", "class"}

# Keywords for defs — keep unless body is `:= by`
DEF_KEYWORDS = {"def", "abbrev", "instance"}

# Modifiers to strip when looking for the leading keyword
MODIFIERS = {
    "noncomputable", "private", "protected", "partial", "unsafe",
    "nonrec", "@[",
}


def find_keyword(block_text):
    """Find the leading keyword of a block, skipping attributes and modifiers."""
    text = block_text.lstrip()

    # Strip doc comments at the start
    while text.startswith("/--") or text.startswith("/-!"):
        # Find the closing -/
        close = text.find("-/")
        if close == -1:
            return None
        text = text[close + 2:].lstrip()

    # Strip attributes @[...]
    while text.startswith("@["):
        depth = 0
        i = 0
        while i < len(text):
            if text[i] == "[":
                depth += 1
            elif text[i] == "]":
                depth -= 1
                if depth == 0:
                    text = text[i + 1:].lstrip()
                    break
            i += 1
        else:
            break

    # Strip modifiers
    changed = True
    while changed:
        changed = False
        for mod in ("noncomputable", "private", "protected", "partial",
                     "unsafe", "nonrec"):
            if text.startswith(mod) and (len(text) == len(mod) or not text[len(mod)].isalnum()):
                text = text[len(mod):].lstrip()
                changed = True

    # Now extract the first word
    m = re.match(r"(\w+|#\w+)", text)
    if m:
        return m.group(1)
    return None


def find_toplevel_assign(text):
    """Find ':=' at bracket depth 0 in text.

    Returns the index of ':' in ':=', or -1 if not found.
    """
    depth = 0
    i = 0
    n = len(text)
    # Track whether we're inside a string literal
    in_string = False
    while i < n:
        c = text[i]
        if c == '"' and (i == 0 or text[i-1] != '\\'):
            in_string = not in_string
            i += 1
            continue
        if in_string:
            i += 1
            continue
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth = max(0, depth - 1)
        elif c == ":" and i + 1 < n and text[i + 1] == "=" and depth == 0:
            # Make sure it's not inside a comment
            return i
        elif c == "-" and i + 1 < n and text[i + 1] == "-":
            # Line comment — skip to end of line
            nl = text.find("\n", i)
            if nl == -1:
                return -1
            i = nl + 1
            continue
        elif c == "/" and i + 1 < n and text[i + 1] == "-":
            # Block comment — skip (respecting nesting)
            comment_depth = 1
            i += 2
            while i < n - 1 and comment_depth > 0:
                if text[i] == "/" and text[i + 1] == "-":
                    comment_depth += 1
                    i += 2
                elif text[i] == "-" and text[i + 1] == "/":
                    comment_depth -= 1
                    i += 2
                else:
                    i += 1
            continue
        i += 1
    return -1


def strip_proof(block_lines):
    """Strip proof body from theorem/lemma block. Keep up to before ':='."""
    text = "\n".join(block_lines)
    pos = find_toplevel_assign(text)
    if pos == -1:
        # No ':=' found — look for 'where' on its own line
        for i, line in enumerate(block_lines):
            if line.strip() == "where":
                return block_lines[:i]
        # No stripping possible, keep as-is
        return block_lines
    # Keep everything before ':='
    before = text[:pos].rstrip()
    return before.split("\n")


def strip_tactic_body(block_lines):
    """For def/abbrev/instance: strip body only if it's ':= by' (tactic proof)."""
    text = "\n".join(block_lines)
    pos = find_toplevel_assign(text)
    if pos == -1:
        return block_lines
    # Check what follows ':='
    after = text[pos + 2:].lstrip()
    if re.match(r"by\b", after):
        # Tactic proof — strip from ':= by'
        before = text[:pos].rstrip()
        return before.split("\n")
    # Computational body — keep entire block
    return block_lines


def classify_and_process(block_lines, *, include_comments=False):
    """Classify a block and return processed lines, or None to skip."""
    first_line = block_lines[0]

    # Blank lines — keep
    if not first_line.strip():
        return block_lines

    # Comment blocks (standalone -- or /- at column 0)
    stripped = first_line.lstrip()
    if stripped.startswith("--") or stripped.startswith("/-"):
        if not include_comments:
            return None
        return block_lines

    keyword = find_keyword("\n".join(block_lines))
    if keyword is None:
        # Unknown — keep (safe default)
        return block_lines

    if keyword in SKIP_KEYWORDS:
        return None

    if keyword in CONTEXT_KEYWORDS:
        return block_lines

    if keyword in PROOF_KEYWORDS:
        return strip_proof(block_lines)

    if keyword in TYPE_KEYWORDS:
        return block_lines

    if keyword in DEF_KEYWORDS:
        return strip_tactic_body(block_lines)

    # Unknown keyword — keep (safe default)
    return block_lines


def process_file(filepath, *, include_comments=False):
    """Process a single .lean file and return output lines."""
    with open(filepath, "r", encoding="utf-8") as f:
        content = f.read()

    lines = content.split("\n")
    # Remove trailing empty line from split
    if lines and lines[-1] == "":
        lines.pop()

    blocks = parse_blocks(lines)
    output_lines = []

    for block in blocks:
        result = classify_and_process(block, include_comments=include_comments)
        if result is not None:
            output_lines.extend(result)

    return output_lines


def collapse_blank_lines(lines):
    """Collapse runs of 3+ blank lines to 2."""
    result = []
    blank_count = 0
    for line in lines:
        if not line.strip():
            blank_count += 1
            if blank_count <= 2:
                result.append(line.rstrip())
        else:
            blank_count = 0
            result.append(line.rstrip())
    # Strip trailing blank lines
    while result and not result[-1].strip():
        result.pop()
    return result


def main():
    parser = argparse.ArgumentParser(
        description="Extract Lean 4 definitions, stripping proofs and imports.")
    parser.add_argument("paths", nargs="*", default=[],
                        help="Files or directories to process (default: current dir)")
    parser.add_argument("--comments", action="store_true",
                        help="Include comments (--, /-, /--,  /-!)")
    args = parser.parse_args()

    files = collect_lean_files(args.paths)
    if not files:
        print("No .lean files found.", file=sys.stderr)
        sys.exit(1)

    first = True
    for filepath in files:
        # Normalize path for display
        display_path = os.path.relpath(filepath)
        if display_path.startswith("./"):
            display_path = display_path[2:]

        output = process_file(filepath, include_comments=args.comments)
        output = collapse_blank_lines(output)

        if not output:
            continue

        if not first:
            print()
        first = False

        print(f"-- ===== {display_path} =====")
        for line in output:
            print(line)


if __name__ == "__main__":
    main()
