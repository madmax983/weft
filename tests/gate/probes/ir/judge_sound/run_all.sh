#!/bin/sh
# Runs each hand-written fact trace through spec/weft.dl (the b073ea7 binary):
# `weft lint` evaluates the spec, the facts of an empty program, and the facts
# and lint rules of the trace file. Each lint names the derived error it shows.
# Then it checks and runs each judge probe (b073ea7, R3a 616f99c, oracle).
cd "$(dirname "$0")"
W=../probes/weft
R=../work/machine/weft-r3a
for t in o32_mir o32_machine o32_minimal m3_mir m3_machine m3_minimal \
         j1_mir j1_machine j1_minimal j4_mir j4_machine f32_mir f32_machine; do
    cat common.dl "$t.dl" > "run_$t.dl"
    echo "== trace $t"
    $W lint --rules "run_$t.dl" empty.wf 2>&1 | grep "lint \`\|lint warning"
done
for p in j1_post_resume_keep j2_post_resume_closure j3_resuming_clause_value \
         j4_multi_outer_ref j5_kept_borrow j5b_kept_write j5c_kept_borrow_task \
         j5d_maker_borrow j6_resume_temp_keep; do
    a=$($W check "$p.wf" 2>&1 | tail -1 | sed 's/.*: //')
    b=$($R check "$p.wf" 2>&1 | tail -1 | sed 's/.*: //')
    o=$($W run --unchecked --oracle "$p.wf" 2>&1 | grep -o "oracle: [^(]*" | head -1)
    echo "== probe $p | b073ea7: $a | 616f99c: $b | oracle: ${o:-clean}"
done
