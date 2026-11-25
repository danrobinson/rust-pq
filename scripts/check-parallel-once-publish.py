#!/usr/bin/env python3
"""Check the unique-writer, normally returning OnceLock publication event sequence."""
import os
from pathlib import Path
import re
import runpy
import subprocess

HERE = Path(__file__).resolve().parent


def compact(code):
    return re.sub(r"//[^\n]*|\s+", "", code)


def ordered(source, *fragments):
    for fragment in fragments:
        key = compact(fragment)
        if key not in source:
            raise ValueError(f"pinned OnceLock normal publication changed near {fragment}")
        source = source.split(key, 1)[1]


def pinned_sources():
    toolchain = HERE.parent / ".tools/aeneas/charon/charon"
    env = dict(os.environ, PATH=f"{Path.home()}/.cargo/bin:" + os.environ["PATH"])
    root = subprocess.check_output(["rustc", "--print", "sysroot"], cwd=toolchain, env=env, text=True).strip()
    lib = Path(root, "lib/rustlib/src/rust/library/std/src")
    lock = compact((lib / "sync/once_lock.rs").read_text())
    for chain in [
        ("pub fn set(&self, value: T)", "match self.try_insert(value) { Ok(_) => Ok(())"),
        ("pub fn try_insert(&self, value: T)", "let mut value = Some(value); let res = self.get_or_init(|| value.take().unwrap()); match value { None => Ok(res)"),
        ("pub fn get_or_init<F>", "match self.get_or_try_init(|| Ok::<T, !>(f()))"),
        ("pub fn get_or_try_init<F, E>", "if let Some(value) = self.get() {return Ok(value);} self.initialize(f)?; Ok(unsafe {self.get_unchecked()})"),
        ("fn initialize<F, E>", "let slot = &self.value; self.once.call_once_force(|p| {match f() { Ok(value) => { unsafe {(&mut *slot.get()).write(value)}; }"),
        ("pub fn get(&self)", "if self.initialized() {Some(unsafe {self.get_unchecked()})} else {None}"),
        ("fn initialized(&self)", "self.once.is_completed()"),
    ]:
        ordered(lock, *chain)
    ordered(compact((lib / "sync/once.rs").read_text()), "pub fn call_once_force<F>",
            "if self.inner.is_completed() {return;} let mut f = Some(f); self.inner.call(true, &mut |p| f.take().unwrap()(p));")
    base = lib / "sys/sync/once"
    for backend, atom, exchange, callbacks, read in [
        ("futex", "state_and_queued", "Release", ["set_state_to: Cell::new(COMPLETE)", "f(&f_state); waiter_queue.set_state_on_drop_to = f_state.inner.set_state_to.get(); return;"], "self.state_and_queued.load(Acquire) == COMPLETE"),
        ("queue", "state_and_queue", "AcqRel", ["set_state_on_drop_to: Cell::new(ptr::without_provenance_mut(COMPLETE))", "init(&init_state); waiter_queue.set_state_on_drop_to = init_state.inner.set_state_on_drop_to.get(); return;"], "self.state_and_queue.load(Acquire).addr() == COMPLETE"),
    ]:
        source = compact((base / (backend + ".rs")).read_text())
        ordered(source, "pub fn call(&self", f"self.{atom}.compare_exchange_weak(", "Acquire, Acquire,", "continue;", *callbacks)
        ordered(source, "fn drop(&mut self)", f"self.{atom}.swap(self.set_state_on_drop_to,{exchange})")
        ordered(source, "pub fn is_completed(&self)", read)
    ordered(compact((base/"mod.rs").read_text()), 'target_os="linux"', 'mod futex;', 'target_family="unix"', 'mod queue;')


def check(binary, libdir, folder):
    pinned_sources()
    herd = runpy.run_path(str(HERE / "check-pool-litmus.py"))["run"]
    base = (HERE / "parallel-proof/pool/once-publication.litmus").read_text()
    path = folder / "once-publication.litmus"
    for order in ("release", "acq_rel"):
        source = base.replace("state, 0, memory_order_release", "state, 0, memory_order_" + order)
        herd(binary, libdir, path, source, "Never")
        herd(binary, libdir, path, source.replace("1:value=0", "1:value=1"), "Sometimes")
        for before in (f"state, 0, memory_order_{order}", "atomic_load_explicit(state, memory_order_acquire"):
            herd(binary, libdir, path, source.replace(before, re.sub(r"memory_order_\w+", "memory_order_relaxed", before)), "Sometimes")
    print("OnceLock: stale completed reads excluded for both backends; successful and weakened-order controls witnessed.", flush=True)
