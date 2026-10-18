#!/usr/bin/env bash
# Check that the link crate uses the definitions of the developments it links.
#
# The link crate includes the source files with `#[path = ...]` (see
# src/lib.rs). It does not copy them. This script fails if:
#
# 1. src/lib.rs does not include exactly the files in EXPECTED, an include
#    has a form that this script cannot read, an included file does not
#    exist, or its home crate does not declare it as a module (then the link
#    would use a file that its home does not verify). A declaration under a
#    `#[cfg ...]` attribute does not count;
# 2. an own file of the link crate defines an item with the name of an item
#    of an included file, at any indentation and with any visibility (a
#    shadow copy can drift from its source);
# 3. a verbatim copy differs from its source. A verbatim copy is a block
#    between the lines `// COPY OF <path from proofs/link>: <item>` and
#    `// END COPY`. The block must be identical to the item in that file.
set -euo pipefail
cd "$(dirname "$0")"

# The files that the link is about, relative to src/.
EXPECTED=(
    ../../../crates/weft-verified/src/places.rs
    ../../../crates/weft-verified/src/dataflow.rs
    ../../../crates/weft-verified/src/lifecycle.rs
    ../../borrowing/src/model.rs
    ../../borrowing/src/soundness.rs
    ../../borrowing/src/cfg.rs
    ../../borrowing/src/layout.rs
    ../../borrowing/src/layout_proof.rs
    ../../borrowing/src/layout_examples.rs
    ../../effects/src/model.rs
)

fail=0
included=()

# 1. The includes.
raw="$(grep -cE '^[[:space:]]*#!?\[[[:space:]]*path' src/lib.rs || true)"
mapfile -t rels < <(sed -nE 's/^[[:space:]]*#\[[[:space:]]*path[[:space:]]*=[[:space:]]*"([^"]+)"[[:space:]]*\][[:space:]]*$/\1/p' src/lib.rs)
if [ "${#rels[@]}" -ne "$raw" ]; then
    echo "FAIL: src/lib.rs has $raw path attributes, but only ${#rels[@]} have the form #[path = \"...\"] on a line of their own"
    fail=1
fi
if [ "$(printf '%s\n' "${rels[@]}" | sort)" != "$(printf '%s\n' "${EXPECTED[@]}" | sort)" ]; then
    echo "FAIL: the includes of src/lib.rs are not the expected files:"
    diff <(printf '%s\n' "${EXPECTED[@]}" | sort) <(printf '%s\n' "${rels[@]}" | sort) | sed 's/^/    /' || true
    fail=1
fi
for rel in "${rels[@]}"; do
    file="src/$rel"
    if [ ! -f "$file" ]; then
        echo "FAIL: included file $file does not exist"
        fail=1
        continue
    fi
    home="$(dirname "$file")/lib.rs"
    stem="$(basename "$file" .rs)"
    # The declaration must be at column 0, and the attribute lines and doc
    # comments directly above it must not hold `cfg`.
    if [ ! -f "$home" ] || ! awk -v stem="$stem" '
        /^[[:space:]]*(#\[|\/\/\/)/ { attrs = attrs $0 "\n"; next }
        $0 ~ ("^pub mod " stem ";") { if (attrs !~ /cfg/) ok = 1; attrs = ""; next }
        { attrs = "" }
        END { exit ok ? 0 : 1 }
    ' "$home"; then
        echo "FAIL: $home does not declare 'pub mod ${stem};' without a cfg attribute"
        fail=1
    fi
    included+=("$file")
done

if [ "${#included[@]}" -eq 0 ]; then
    echo "FAIL: src/lib.rs includes no source file"
    exit 1
fi

# The item pattern: any indentation, any visibility, the Verus modes.
ITEM='^[[:space:]]*(pub(\([^)]*\))?[[:space:]]+)?((open|closed|uninterp)[[:space:]]+)?(broadcast[[:space:]]+)?((spec|proof|exec)(\([a-z]+\))?[[:space:]]+)?(const[[:space:]]+)?(fn|struct|enum|type|trait|const|static|union)[[:space:]]+'

# The names of the items of some files.
item_names() {
    { grep -hoE "${ITEM}[A-Za-z_][A-Za-z0-9_]*" "$@" || true; } | awk '{ print $NF }' | sort -u
}

# 2. No shadow copies. An item in a marked copy block is not a shadow copy:
# check 3 compares it with its source.
mapfile -t own < <(find src -name '*.rs' | sort)
marked="$(sed -nE 's/^\/\/ COPY OF [^:]+: ([A-Za-z_][A-Za-z0-9_]*)$/\1/p' "${own[@]}" | sort -u)"
dups="$(comm -12 <(item_names "${included[@]}") <(item_names "${own[@]}") | comm -23 - <(echo "$marked"))"
if [ -n "$dups" ]; then
    echo "FAIL: the link crate defines items that an included file defines:"
    echo "$dups" | sed 's/^/    /'
    fail=1
fi

# The text of item NAME in FILE: its doc comments and attributes, then the
# item up to a closing brace in column 0 (or a line that ends with `;`).
extract_item() {
    awk -v name="$2" -v item="$ITEM" '
        BEGIN { pat = item name "([^A-Za-z0-9_]|$)" }
        found { print; if ($0 == "}") exit; next }
        /^(\/\/\/|#\[)/ { buf = buf $0 "\n"; next }
        $0 ~ pat { found = 1; printf "%s", buf; print; if ($0 ~ /;[[:space:]]*$/) exit; next }
        { buf = "" }
    ' "$1"
}

# 3. Verbatim copies.
copies=0
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
for f in "${own[@]}"; do
    awk -v dir="$tmp" '
        /^\/\/ COPY OF / { n++; out = dir "/block" n; hdr = substr($0, 12); print hdr > (dir "/head" n); next }
        /^\/\/ END COPY/ { out = ""; next }
        out != "" { print > out }
    ' "$f"
    for head in "$tmp"/head*; do
        [ -e "$head" ] || continue
        n="${head##*/head}"
        spec="$(cat "$head")"
        src="${spec%%: *}"
        item="${spec#*: }"
        copies=$((copies + 1))
        if [ ! -f "$src" ]; then
            echo "FAIL: $f: copy of $item names a missing file $src"
            fail=1
        elif ! diff -u <(extract_item "$src" "$item") "$tmp/block$n" > "$tmp/diff"; then
            echo "FAIL: $f: the copy of $item differs from $src:"
            sed 's/^/    /' "$tmp/diff"
            fail=1
        fi
        rm -f "$head" "$tmp/block$n"
    done
done

if [ "$fail" -ne 0 ]; then
    exit 1
fi
echo "check-copies: ${#included[@]} included source files, no shadow copies, $copies verbatim copies identical"
