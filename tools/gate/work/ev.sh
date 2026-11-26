#!/usr/bin/env bash
# ev.sh: one verdict row (TSV) for each program.
# Usage: WEFT=<weft binary> bash ev.sh FILE...
# Columns: path, basename, old codes, ir codes (with "(FB:<note>)" for a
# fallback), oracle of the AST engine, oracle of the IR engine, "ok", verdict,
# locations.
# The oracle runs `run --unchecked --oracle` with the first three
# configurations of the gate (seed, workers): (1,1), (2,4), (3,2). The first
# fault wins. Each run has a time limit of 10 s.
set -u
WEFT=${WEFT:?set WEFT to the weft binary}
TL=${EV_TIMEOUT:-10}
BENIGN='out of bounds|integer overflow|unsigned underflow|integer underflow|does not fit in|cannot listen on|division by zero|duration underflow|split point is out of bounds'

# codes OUTPUT: "0", or the codes in order of first use, as "2xW0301,W0405".
codes() {
  local c
  c=$(grep -o '^error\[W[0-9]*\]' <<<"$1" | sed 's/^error\[\(.*\)\]/\1/')
  local other
  other=$(grep -c '^error: ' <<<"$1")
  if [ -z "$c" ] && [ "$other" = 0 ]; then echo 0; return; fi
  {
    [ -n "$c" ] && awk '{n[$0]++; if (!($0 in o)) {o[$0]=++k; s[k]=$0}} END {for (i=1;i<=k;i++) {x=s[i]; printf "%s%s%s", (i>1?",":""), (n[x]>1? n[x] "x" : ""), x}}' <<<"$c"
    [ "$other" != 0 ] && { [ -n "$c" ] && printf ','; printf 'ERR'; }
  }
  echo
}

# lines OUTPUT: the lines of the diagnostics (the "-->" line after each error[...]).
lines() {
  awk '/^error\[/ {want=1; next} want && /-->/ {n=split($2,a,":"); printf "%s%s", (k++?",":""), a[n-1]; want=0}' <<<"$1"
}

# oracle ENGINE FILE: prints "verdict<TAB>fault line".
oracle() {
  local eng=$1 f=$2 out rc first="" cfg seed wk err msg line
  for cfg in "1 1" "2 4" "3 2"; do
    read -r seed wk <<<"$cfg"
    out=$(timeout "$TL" "$WEFT" run --unchecked --oracle --engine="$eng" --seed "$seed" --workers "$wk" "$f" 2>&1)
    rc=$?
    if grep -q '^error: no main' <<<"$out"; then
      printf 'not-runnable\t-\n'; return
    fi
    line=$(awk '/^error: runtime error:/ {want=1; next} want && /-->/ {n=split($2,a,":"); print a[n-1]; exit}' <<<"$out")
    err=$(grep -m1 '^error: runtime error: ' <<<"$out" | sed 's/^error: runtime error: //')
    msg=""
    for m in '<moved>' '<freed>' '<dangling>'; do
      if grep -qF -- "$m" <<<"$out"; then msg="the output holds \`$m\`"; break; fi
    done
    if [ -n "$err" ] && ! grep -Eq "$BENIGN" <<<"$err"; then
      msg="${msg:+$msg; }$err"
    fi
    if [ "$rc" = 124 ]; then
      [ -z "$first" ] && first="timeout"
      [ -z "$msg" ] && continue
    elif [ "$rc" -ge 100 ] && [ -z "$msg" ]; then
      msg="the run stopped with no verdict (exit $rc)"
    fi
    if [ -n "$msg" ]; then
      printf 'ORACLE: %s\t%s\n' "$(printf '%s' "$msg" | tr '\t\n' '  ' | sed 's/ *$//')" "${line:--}"
      return
    fi
    [ -z "$first" ] && first="clean($rc)"
  done
  printf '%s\t-\n' "$first"
}

for f in "$@"; do
  old_out=$(timeout 60 "$WEFT" check --facts=old "$f" 2>&1)
  ir_out=$(timeout 60 "$WEFT" check --facts=ir "$f" 2>&1)
  old=$(codes "$old_out")
  ir=$(codes "$ir_out")
  fb=$(grep -m1 -o 'the old pipeline checks the program: .*' <<<"$ir_out" | sed 's/^the old pipeline checks the program: //')
  irc=$ir
  [ -n "$fb" ] && irc="$ir(FB:$fb)"
  IFS=$'\t' read -r ast ast_line < <(oracle ast "$f")
  IFS=$'\t' read -r irv ir_line < <(oracle ir "$f")
  fault=0
  case "$ast" in ORACLE:*) fault=1 ;; esac
  case "$irv" in ORACLE:*) fault=1 ;; esac
  fline=$ir_line
  [ "$fline" = - ] && fline=$ast_line
  if [ $fault = 1 ]; then
    if [ -z "$fb" ] && [ "$ir" != 0 ] && [ "$old" != 0 ]; then v=both-reject
    elif [ -z "$fb" ] && [ "$ir" != 0 ]; then v=oldmiss
    elif [ -n "$fb" ] && [ "$ir" != 0 ]; then v=held
    elif [ -z "$fb" ]; then v=HOLE
    else v=fb-miss
    fi
  else
    if [ -z "$fb" ] && [ "$ir" != 0 ]; then v=FP-IR
    elif [ -n "$fb" ] && [ "$ir" != 0 ]; then v=fb-reject
    else v=nofault
    fi
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\tok\t%s\told@[%s] IR@[%s] fault@%s\n' \
    "$f" "$(basename "$f")" "$old" "$irc" "$ast" "$irv" "$v" \
    "$(lines "$old_out")" "$(lines "$ir_out")" "$fline"
done
