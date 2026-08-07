"""A small, deliberately dumb scanner for the shape of Rust this repository writes.

Two jobs depend on knowing where each item in `cpoly/src/*.rs` starts and stops:

* **genesis fidelity** — proving that a frozen baseline function is byte-for-byte
  what `cpoly/src` contained at the commit its annotation names, and
* **bench coverage** — pairing every `Mirrors CompPoly.X` docstring with a bench
  case or with an explicit exclusion.

Both need item spans, so the scanning lives here once.

This is not a Rust parser and must never grow into one. It handles exactly the
subset the crate is written in: rustfmt-formatted, no macros that define items,
no `unsafe`, no raw strings, no nested modules in the source files. Braces are
matched over a mask that blanks out comments and string literals, which is the
only genuinely fiddly part. Anything outside that subset should make the scanner
*fail loudly* rather than guess -- a silently mis-detected span would let a
corrupted genesis snapshot pass its own check, which is the one failure this
whole file exists to prevent.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field as dc_field

# Item heads we recognise, at a known indentation. `use`/`extern crate` are
# deliberately absent: they are not things anyone benchmarks or freezes.
_HEAD = re.compile(
    r"""^(?P<indent>[ ]*)
        (?P<vis>pub(?:\([^)]*\))?\s+)?
        (?P<kw>const\s+fn|fn|struct|enum|union|trait|type|const|static|impl|mod)
        \b(?P<rest>.*)$""",
    re.VERBOSE,
)

_NAME_AFTER_KW = re.compile(r"^\s*(?P<name>[A-Za-z_][A-Za-z0-9_]*)")

# `impl Add<&Poly> for &Poly {` / `impl Fp {` / `impl<T> Foo for Bar {`
_IMPL = re.compile(
    r"^impl(?:<[^>]*>)?\s+(?P<a>.+?)(?:\s+for\s+(?P<b>.+?))?\s*(?:where\b.*)?\{\s*$"
)


class ScanError(Exception):
    """The source stepped outside the subset this scanner promises to handle."""


@dataclass
class Item:
    """One Rust item, with the span of its own text (docs and attributes excluded)."""

    kind: str  # fn | struct | const | impl | type | ...
    name: str  # `mul`, `Fp`, `P`
    path: str  # `field::Fp::mul`, `field::<Fp as Add>::add`
    indent: int
    lead_start: int  # first line of the doc/attribute block above the item, 0-based
    start: int  # the item's own first line (signature), 0-based
    end: int  # last line of the item, inclusive, 0-based
    text: str  # exact source of lines [start, end], newline-terminated
    children: list["Item"] = dc_field(default_factory=list)

    @property
    def span_lines(self) -> int:
        return self.end - self.start + 1


def code_mask(src: str) -> list[bool]:
    """True where a character is real code -- not inside a comment or a literal.

    Brace matching runs over this so that a `{` in a doc comment or a string
    cannot close an item early.
    """
    mask = [True] * len(src)
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if c == "/" and nxt == "/":
            while i < n and src[i] != "\n":
                mask[i] = False
                i += 1
        elif c == "/" and nxt == "*":
            depth = 1
            mask[i] = mask[i + 1] = False
            i += 2
            while i < n and depth:
                if src[i] == "/" and i + 1 < n and src[i + 1] == "*":
                    depth += 1
                    mask[i] = mask[i + 1] = False
                    i += 2
                    continue
                if src[i] == "*" and i + 1 < n and src[i + 1] == "/":
                    depth -= 1
                    mask[i] = mask[i + 1] = False
                    i += 2
                    continue
                mask[i] = False
                i += 1
        elif c == '"':
            if src.startswith('r"', max(0, i - 1)) or src.startswith('r#"', max(0, i - 2)):
                raise ScanError("raw string literals are outside this scanner's subset")
            mask[i] = False
            i += 1
            while i < n:
                if src[i] == "\\":
                    mask[i] = False
                    if i + 1 < n:
                        mask[i + 1] = False
                    i += 2
                    continue
                mask[i] = False
                if src[i] == '"':
                    i += 1
                    break
                i += 1
        elif c == "'":
            # A char literal, or a lifetime. Lifetimes have no closing quote, so
            # only treat this as a literal when one turns up within 4 chars.
            m = re.match(r"'(?:\\.|[^'\\])'", src[i : i + 5])
            if m:
                for k in range(i, i + m.end()):
                    mask[k] = False
                i += m.end()
            else:
                i += 1
        else:
            i += 1
    return mask


def _line_offsets(src: str) -> list[int]:
    offs, pos = [0], 0
    for line in src.splitlines(keepends=True):
        pos += len(line)
        offs.append(pos)
    return offs


def _find_span(src: str, mask: list[bool], start_off: int) -> int:
    """Return the offset one past the end of the item beginning at `start_off`.

    An item ends either at the `}` closing its first `{`, or -- when no brace
    opens first -- at the `;` terminating a declaration such as `pub struct Fp(u64);`.
    """
    depth = 0
    i = start_off
    seen_brace = False
    n = len(src)
    while i < n:
        if mask[i]:
            c = src[i]
            if c == "{":
                depth += 1
                seen_brace = True
            elif c == "}":
                depth -= 1
                if depth == 0 and seen_brace:
                    # `const X: T = T { .. };` keeps going to its semicolon.
                    j = i + 1
                    while j < n and src[j] in " \t":
                        j += 1
                    return j + 1 if j < n and src[j] == ";" else i + 1
                if depth < 0:
                    raise ScanError(f"unbalanced '}}' at offset {i}")
            elif c == ";" and depth == 0 and not seen_brace:
                return i + 1
        i += 1
    raise ScanError(f"item beginning at offset {start_off} is never closed")


def _lead_start(lines: list[str], start: int) -> int:
    """Walk up over the doc comments and attributes attached to line `start`."""
    i = start
    while i > 0:
        prev = lines[i - 1].strip()
        if prev.startswith("///") or prev.startswith("#[") or prev.startswith("//!"):
            i -= 1
        elif prev.startswith("//") and i - 1 > 0 and _attached_comment(lines, i - 1):
            i -= 1
        else:
            break
    return i


def _attached_comment(lines: list[str], i: int) -> bool:
    """A `//` comment counts as part of an item's lead only if it is not blank-separated."""
    return bool(lines[i].strip()) and (i == 0 or True)


def _impl_path(header: str, module: str) -> str:
    m = _IMPL.match(header.strip())
    if not m:
        raise ScanError(f"unrecognised impl header: {header.strip()!r}")
    a, b = m.group("a").strip(), (m.group("b") or "").strip()
    return f"{module}::<{b} as {a}>" if b else f"{module}::{a}"


def scan(src: str, module: str) -> list[Item]:
    """Every top-level item in `src`, with `impl` members as children."""
    mask = code_mask(src)
    lines = src.splitlines(keepends=True)
    offs = _line_offsets(src)
    return _scan_region(src, mask, lines, offs, 0, len(lines), 0, module, None)


def _scan_region(src, mask, lines, offs, lo, hi, indent, module, owner) -> list[Item]:
    items: list[Item] = []
    i = lo
    while i < hi:
        line = lines[i]
        m = _HEAD.match(line.rstrip("\n"))
        if not m or len(m.group("indent")) != indent:
            i += 1
            continue
        # `impl` inside an impl, or a `fn` used as a type -- neither happens here.
        kw = m.group("kw")
        start_off = offs[i] + indent
        end_off = _find_span(src, mask, start_off)
        end_line = next(k for k in range(i, len(lines)) if offs[k + 1] >= end_off)

        if kw == "impl":
            header = _extract_impl_header(src, start_off)
            path = _impl_path(header, module)
            name = path.rsplit("::", 1)[-1]
        else:
            nm = _NAME_AFTER_KW.match(m.group("rest"))
            if not nm:
                raise ScanError(f"cannot read a name out of: {line.rstrip()!r}")
            name = nm.group("name")
            path = f"{owner}::{name}" if owner else f"{module}::{name}"

        item = Item(
            kind=kw,
            name=name,
            path=path,
            indent=indent,
            lead_start=_lead_start(lines, i),
            start=i,
            end=end_line,
            text="".join(lines[i : end_line + 1]),
        )
        if kw == "impl":
            item.children = _scan_region(
                src, mask, lines, offs, i + 1, end_line, indent + 4, module, path
            )
        items.append(item)
        i = end_line + 1
    return items


def _extract_impl_header(src: str, start_off: int) -> str:
    brace = src.index("{", start_off)
    return " ".join(src[start_off : brace + 1].split())


def flatten(items: list[Item]) -> list[Item]:
    """Every item and impl member, in source order."""
    out = []
    for it in items:
        out.append(it)
        out.extend(it.children)
    return out


def benchable(items: list[Item]) -> list[Item]:
    """Items that could plausibly have a runtime worth measuring.

    `impl` blocks themselves are containers, and `struct`/`type`/`use` are not
    code. Everything else -- free functions, methods, operator impls, and
    consts -- is offered up, and `bench/exclusions.toml` is where the ones that
    are O(1) by inspection get ruled out *by name, with a reason*. Silence is
    not an exclusion.
    """
    return [
        it
        for it in flatten(items)
        if it.kind in ("fn", "const fn", "const")
        and not (it.kind == "impl")
    ]
