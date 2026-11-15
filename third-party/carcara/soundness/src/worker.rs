// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Crash isolation. Carcara can abort the whole process on hostile input (GMP overflow on a
//! huge shift, stack exhaustion), which `catch_unwind` cannot contain. Every check therefore runs
//! in a worker process; a dead worker is recorded as a crash for the in-flight instance and
//! replaced.

use crate::oracle::{check_instance, Cex, Instance, OracleConfig, Outcome};
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

/// An instance that runs longer than this is treated as a hang: the worker is killed.
const HANG_SECONDS: u64 = 60;

fn now_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

fn esc(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('\n', "\\n")
        .replace('\t', "\\t")
}

fn unesc(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut it = s.chars();
    while let Some(c) = it.next() {
        if c == '\\' {
            match it.next() {
                Some('n') => out.push('\n'),
                Some('t') => out.push('\t'),
                Some(other) => out.push(other),
                None => {}
            }
        } else {
            out.push(c);
        }
    }
    out
}

/// Worker main loop: read instances from stdin, answer on stdout.
pub fn serve(cfg: &OracleConfig) {
    std::panic::set_hook(Box::new(|_| {}));
    let stdin = std::io::stdin();
    let mut lines = stdin.lock().lines();
    let stdout = std::io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    loop {
        let (Some(Ok(defs)), Some(Ok(proof))) = (lines.next(), lines.next()) else {
            return;
        };
        let inst = Instance {
            defs: unesc(&defs),
            proof: unesc(&proof),
        };
        let o = check_instance(&inst, cfg);
        if let Some(p) = &o.parse_error {
            let _ = writeln!(out, "PARSE\t{}", esc(p));
        }
        if let Some(p) = &o.panic {
            let _ = writeln!(out, "PANIC\t{}", esc(p));
        }
        if let Some((s, r, m)) = &o.first_error {
            let _ = writeln!(out, "ERR\t{}\t{}\t{}", esc(s), esc(r), esc(m));
        }
        for (s, r) in &o.accepted {
            let _ = writeln!(out, "ACC\t{}\t{}", esc(s), esc(r));
        }
        for s in &o.exercised {
            let _ = writeln!(out, "EXE\t{}", esc(s));
        }
        for c in &o.cexs {
            let _ = writeln!(
                out,
                "CEX\t{}\t{}\t{}\t{}",
                esc(&c.step),
                esc(&c.rule),
                u8::from(c.global),
                esc(&c.model)
            );
        }
        let _ = writeln!(out, "END");
        let _ = out.flush();
    }
}

pub struct Worker {
    child: Child,
    stdin: BufWriter<ChildStdin>,
    stdout: BufReader<ChildStdout>,
    busy_since: Arc<AtomicU64>,
    alive: Arc<AtomicBool>,
}

pub enum Reply {
    Done(Outcome),
    Crashed(String),
}

impl Worker {
    pub fn spawn(cfg: &OracleConfig, exe: Option<&std::path::Path>) -> std::io::Result<Worker> {
        let exe = match exe {
            Some(exe) => exe.to_path_buf(),
            None => std::env::current_exe()?,
        };
        let mut child = Command::new(exe)
            .arg("--worker")
            .arg("--models")
            .arg(cfg.random_models.to_string())
            .arg("--fuel")
            .arg(cfg.fuel.to_string())
            .arg("--seed")
            .arg(cfg.seed.to_string())
            .arg("--dialect")
            .arg(cfg.dialect.name())
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()?;
        let stdin = BufWriter::new(child.stdin.take().unwrap());
        let stdout = BufReader::new(child.stdout.take().unwrap());
        let busy_since = Arc::new(AtomicU64::new(0));
        let alive = Arc::new(AtomicBool::new(true));
        let pid = child.id();
        let (busy, live) = (busy_since.clone(), alive.clone());
        std::thread::spawn(move || {
            while live.load(Ordering::Relaxed) {
                std::thread::sleep(Duration::from_millis(500));
                let since = busy.load(Ordering::Relaxed);
                if since != 0 && now_secs().saturating_sub(since) > HANG_SECONDS {
                    let _ = Command::new("kill").arg("-9").arg(pid.to_string()).status();
                    return;
                }
            }
        });
        Ok(Worker {
            child,
            stdin,
            stdout,
            busy_since,
            alive,
        })
    }

    pub fn check(&mut self, inst: &Instance) -> Reply {
        self.busy_since.store(now_secs(), Ordering::Relaxed);
        let reply = self.check_inner(inst);
        self.busy_since.store(0, Ordering::Relaxed);
        reply
    }

    fn check_inner(&mut self, inst: &Instance) -> Reply {
        if writeln!(self.stdin, "{}\n{}", esc(&inst.defs), esc(&inst.proof)).is_err()
            || self.stdin.flush().is_err()
        {
            return self.crashed();
        }
        let mut o = Outcome::default();
        loop {
            let mut line = String::new();
            match self.stdout.read_line(&mut line) {
                Ok(0) | Err(_) => return self.crashed(),
                Ok(_) => {}
            }
            let line = line.trim_end_matches('\n');
            let f: Vec<&str> = line.split('\t').collect();
            match f[0] {
                "END" => return Reply::Done(o),
                "PARSE" => o.parse_error = Some(unesc(f.get(1).unwrap_or(&""))),
                "PANIC" => o.panic = Some(unesc(f.get(1).unwrap_or(&""))),
                "ERR" if f.len() >= 4 => {
                    o.first_error = Some((unesc(f[1]), unesc(f[2]), unesc(f[3])));
                }
                "ACC" if f.len() >= 3 => o.accepted.push((unesc(f[1]), unesc(f[2]))),
                "EXE" if f.len() >= 2 => {
                    o.exercised.insert(unesc(f[1]));
                }
                "CEX" if f.len() >= 5 => o.cexs.push(Cex {
                    step: unesc(f[1]),
                    rule: unesc(f[2]),
                    global: f[3] == "1",
                    model: unesc(f[4]),
                }),
                _ => {}
            }
        }
    }

    fn crashed(&mut self) -> Reply {
        let status = self
            .child
            .wait()
            .map(|s| format!("{}", s))
            .unwrap_or_else(|e| e.to_string());
        Reply::Crashed(status)
    }
}

impl Drop for Worker {
    fn drop(&mut self) {
        self.alive.store(false, Ordering::Relaxed);
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}
