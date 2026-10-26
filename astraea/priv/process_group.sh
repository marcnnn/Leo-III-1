#!/bin/sh
# Runs "$@" in its own process group and SIGKILLs the whole group when the
# wrapper receives SIGTERM/SIGINT/SIGHUP. MuonTrap only signals its direct child unless
# it runs under a cgroup, so without this wrapper grandchildren of a prover
# (portfolio workers, JVMs started by launcher scripts) would survive a kill.

child=""
trap '[ -n "$child" ] && kill -KILL -- "-$child" 2>/dev/null; exit 143' TERM INT HUP

# Job control gives the background job its own process group (pgid = its pid).
set -m
"$@" &
child=$!

wait "$child"
status=$?

# Reap stragglers the prover left behind in its group after exiting normally.
kill -KILL -- "-$child" 2>/dev/null
exit "$status"
