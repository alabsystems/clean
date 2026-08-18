#!/usr/bin/env python3
"""Run a command as a true daemon (double-fork + setsid), reparented to PID 1.

macOS ships no `setsid(1)`, and agent harnesses reap whole process groups on a
timer (~3600s observed). A plain `nohup cmd &` stays in the launching shell's
session and dies with it. This helper double-forks, calls `os.setsid()` between
the forks, and `execvp`s the command, so the work reparents to PID 1 and
survives the launching shell.

Usage:
    daemonize.py --log PATH [--pidfile PATH] [--cwd DIR] -- CMD [ARGS...]

Prints the daemon PID on stdout and exits 0 as soon as the child is launched.
Exit status of the daemon itself is NOT available to the caller by design --
callers must observe completion through the log / a sentinel file.
"""

from __future__ import annotations

import argparse
import os
import sys


def main() -> int:
    parser = argparse.ArgumentParser(add_help=True)
    parser.add_argument("--log", required=True, help="file to receive stdout+stderr")
    parser.add_argument("--pidfile", default=None, help="file to receive the daemon pid")
    parser.add_argument("--cwd", default=None, help="working directory for the daemon")
    parser.add_argument("cmd", nargs=argparse.REMAINDER, help="-- CMD [ARGS...]")
    args = parser.parse_args()

    cmd = args.cmd
    if cmd and cmd[0] == "--":
        cmd = cmd[1:]
    if not cmd:
        print("daemonize.py: no command given", file=sys.stderr)
        return 2

    # Pipe so the intermediate process can report the grandchild pid back.
    read_fd, write_fd = os.pipe()

    first = os.fork()
    if first > 0:
        # Original process: wait for the intermediate to exit, read the pid.
        os.close(write_fd)
        os.waitpid(first, 0)
        with os.fdopen(read_fd, "r") as handle:
            pid_text = handle.read().strip()
        if not pid_text:
            print("daemonize.py: child never reported a pid", file=sys.stderr)
            return 1
        if args.pidfile:
            with open(args.pidfile, "w", encoding="utf-8") as handle:
                handle.write(pid_text + "\n")
        print(pid_text)
        return 0

    # Intermediate process.
    os.close(read_fd)
    os.setsid()
    second = os.fork()
    if second > 0:
        with os.fdopen(write_fd, "w") as handle:
            handle.write(str(second))
        os._exit(0)

    # Daemon.
    os.close(write_fd)
    if args.cwd:
        os.chdir(args.cwd)
    os.umask(0o022)

    log_fd = os.open(args.log, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o644)
    devnull_fd = os.open(os.devnull, os.O_RDONLY)
    os.dup2(devnull_fd, 0)
    os.dup2(log_fd, 1)
    os.dup2(log_fd, 2)
    if devnull_fd > 2:
        os.close(devnull_fd)
    if log_fd > 2:
        os.close(log_fd)

    try:
        os.execvp(cmd[0], cmd)
    except OSError as exc:  # pragma: no cover - exec failure path
        sys.stderr.write(f"daemonize.py: exec failed: {exc}\n")
        os._exit(127)
    return 0  # unreachable


if __name__ == "__main__":
    sys.exit(main())
