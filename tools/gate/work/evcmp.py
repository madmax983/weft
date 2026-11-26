#!/usr/bin/env python3
"""evcmp.py MAIN.tsv[,MAIN2.tsv] STAGE.tsv: the rows of ev.sh whose verdict or codes change.

It prints the verdict counts of both runs, one line for each changed row, the
count of each transition, and a line for each new HOLE and each new FP-IR
(a row that was nofault on main).
"""
import collections
import sys


def load(paths):
    d = {}
    for p in paths.split(','):
        with open(p) as f:
            for line in f:
                c = line.rstrip('\n').split('\t')
                if len(c) >= 9:
                    d[c[0]] = c
    return d


a = load(sys.argv[1])
b = load(sys.argv[2])
cnt_a = collections.Counter(r[7] for k, r in a.items() if k in b)
cnt_b = collections.Counter(r[7] for k, r in b.items() if k in a)
print('main verdicts: ', dict(sorted(cnt_a.items())))
print('stage verdicts:', dict(sorted(cnt_b.items())))
trans = collections.Counter()
for k in sorted(b):
    if k not in a:
        print('NEW-ROW', k, b[k][7])
        continue
    ra, rb = a[k], b[k]
    if ra[7] != rb[7] or ra[2] != rb[2] or ra[3] != rb[3]:
        trans[(ra[7], rb[7])] += 1
        print('\t'.join([k, ra[7] + '->' + rb[7], 'old ' + ra[2] + '->' + rb[2],
                         'ir ' + ra[3][:70] + ' -> ' + rb[3][:70]]))
print('transitions:', dict(trans))
for k in sorted(b):
    if k in a and b[k][7] == 'HOLE' and a[k][7] != 'HOLE':
        print('NEW HOLE', k)
    if k in a and b[k][7] == 'FP-IR' and a[k][7] == 'nofault':
        print('NEW FP-IR', k)
