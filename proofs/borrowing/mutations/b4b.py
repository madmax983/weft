# DESC: B4: `task_soundness` without `separated(ss1, p1, ss0, p0)`.
import sys; sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0]); from _lib import sub
d = sys.argv[1]
sub(d, "src/tasks.rs",
    "        separated(ss0, p0, ss1, p1),\n        separated(ss1, p1, ss0, p0),\n        is_itrace(p0, p1, sched, trace),\n    ensures",
    "        separated(ss0, p0, ss1, p1),\n        is_itrace(p0, p1, sched, trace),\n    ensures")
