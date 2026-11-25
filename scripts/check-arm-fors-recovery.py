#!/usr/bin/env python3
"""Re-extract both AArch64 FORS recovery paths and check the verified loop bodies."""
import re
import runpy
import tempfile
import subprocess
from pathlib import Path

facade = runpy.run_path(str(Path(__file__).with_name("check-platform-facade.py")))
root = facade["ROOT"]
program = root / "lean-hw/Armplatform/WideForsProgram.lean"
cuts = (
    "crate::sha256::arm_wide", "crate::sha512::paired", "crate::sha512::compress",
    "crate::hash::thash_pair", "crate::fors::arm::base_2b_stack",
)


def projected(text, loop):
    decls = re.findall(rf"(@\[rust_loop(?:_body)?\]\ndef fors\.arm\.pk_from_sig_loop{loop}(?:\.body)?\b.*?)(?=\n\n)", text, re.S)
    if len(decls) != 2:
        raise ValueError("expected both loop declarations")
    return "\n\n".join(decls)


def outer_replay(scratch):
    source=(root/"rust/src/fors/arm.rs").read_text()
    (start,)=re.finditer(r"pub\(super\) fn pk_from_sig<",source)
    body=source[start.start():source.index("\n}",start.end())+2]
    # Every change lifts the type of a value. The absolute-index arithmetic and
    # scalar-tail parity are proved on the unmodified Aeneas translation.
    for old,new,count in (
        ("[u8","[Byte",3), ("[0u8;","[Byte::Literal(0);",5),
        ("[0u32; K_MAX]","[EMPTY; K_MAX]",1),
        ("((i as u32) << a) + raw[i]","absolute(i,a,raw[i])",1),
        ("idx[i] >> 1","idx[i].parent()",1), ("idx[i] & 1 == 0","!geo().odd",1),
        ("buf[size] = 0x80;","buf[size] = Byte::Literal(128);",2),
        (").to_be_bytes()",").to_be_bytes().map(Byte::Literal)",2)
    ):
        if body.count(old)!=count:
            raise ValueError(f"expected {count} occurrences of {old} in FORS recovery, got {body.count(old)}")
        body=body.replace(old,new)
    template=(root/"scripts/arm-fors/outer.rs").read_text()
    probe=scratch/"outer.rs"
    probe.write_text(template.replace("// PRODUCTION",body))
    subprocess.run(["rustc","--edition=2021",probe,"-o",scratch/"outer"],check=True)
    trace=subprocess.check_output([scratch/"outer"],text=True)
    expected=subprocess.check_output(["lake","env","lean","--run",root/"scripts/arm-fors/trace.lean"],cwd=root/"lean-hw",text=True)
    if len(trace.splitlines())!=48 or trace!=expected:
        raise ValueError("native compression/recovery call stream differs from the proved Lean plan")



def native_multi(scratch):
    helpers=runpy.run_path(str(root/"scripts/check-arm-keygen.py"))
    src=(root/"rust/src/sha256/arm_wide.rs").read_text()
    body=helpers["function"](src,"compress_multi_1_active").replace("msg: &[u8]","msg: &[usize]")
    body=body.replace("out.as_mut_ptr()","&mut out").replace("super::K","K")
    template=(root/"scripts/arm-keygen/multi.rs").read_text()
    if template.count("(0..640)")!=1:
        raise ValueError("unknown input to symbolic register tracer")
    for size in (256,576):
        probe=scratch/f"multi{size}.rs"
        probe.write_text(template.replace("(0..640)",f"(0..{size})").replace("// PRODUCTION",body))
        binary=scratch/f"multi{size}"
        subprocess.run(["rustc","--edition=2021",probe,"-o",binary],check=True)
        offsets=subprocess.check_output([binary],text=True).splitlines()
        expected=[",".join(str(i+d) for d in (0,16,32,48)) for i in range(0,size,64)]
        if offsets!=expected:
            raise ValueError(f"incorrect seeded SHA-256 feed-forward or offsets for {size} bytes")


def dispatch(target, scratch):
    extracted=facade["extract"]("rust",target,"Dispatch",scratch,["crate::fors::fors_pk_from_sig"],
        ["crate::fors::arm","crate::sha256::arm_wide","crate::sha512::parents","crate::hash","crate::util"],
        ["crate::hash::Seed"])

    def decls(text):
        return {m[1]:m[0] for m in re.finditer(
            r"def (fors\.fors_pk_from_sig(?:_loop\d+)*(?:\.body)?)(?:\s).*?(?=\n\n)",text,re.S)}

    native=decls((extracted/"Funs.lean").read_text())
    known=decls((root/"lean/Slhdsa/Funs.lean").read_text())
    arm=(root/"lean-hw/Armplatform/ForsProgram.lean").read_text()
    known.update(decls(arm.replace(" (target : Target)","")
        .replace("PlatformFors.pathParents target","sha512.parents.path_parents").replace("loop2.body target","loop2.body")))

    def canonical(s):
        # Charon emitted a second copy of the four portable loops for the
        # rejected-width branch. Check every declaration on both sides.
        return re.sub(r"fors\.fors_pk_from_sig_loop([4-7])",lambda m:m[0][:-1]+str(int(m[1])-4),s)
    entry=native.pop("fors.fors_pk_from_sig")
    for name,body in native.items():
        if canonical(body).split()!=known[canonical(name)].split():
            raise ValueError(f"{target}: fallback loop changed: {name}")
    if len(native)!=28:
        raise ValueError(f"{target}: unexpected fallback dependency count {len(native)}")
    entry=canonical(entry).replace("def fors.fors_pk_from_sig","noncomputable def actual (available : Result Bool) (paired multi : Bool)")
    entry=entry.replace("sha256.arm_wide.available","available").replace("fors.arm.pk_from_sig p","slhdsa.WideFors.native paired multi p")
    entry=entry.replace("fors.fors_pk_from_sig_loop2 sig","ArmForsReplay.slhdsa.fors.fors_pk_from_sig_loop2 sig")
    lean_source=("\nimport Armplatform.WideForsDispatch\nopen Aeneas Aeneas.Std Result slhdsa\nnamespace Replay\n"+
        entry+"\nexample (available : Result Bool) (pair multi : Bool) {N : Usize} (p : params.Params) (sig md : Slice U8) (seed : hash.Seed N) (a : address.Adrs) : actual available pair multi p sig md seed a = slhdsa.WideFors.dispatch available pair multi p sig md seed a := by rfl\nend Replay")
    facade["run"](["lake","env","lean","--stdin"],root/"lean-hw",text=True,input=lean_source)


def check():
    facade["run"](["lake","build","Armplatform.WideForsDispatch"],root/"lean-hw")
    with tempfile.TemporaryDirectory() as temporary:
        outer_replay(Path(temporary))
        native_multi(Path(temporary))
        for target in facade["TARGETS"][:2]:
            scratch = Path(temporary) / target
            scratch.mkdir()
            package = facade["extract"]("rust", target, "Armfors", scratch,
                                        ["crate::fors::arm::pk_from_sig"], cuts)
            dispatch(target,scratch)
            actual = (package / "Funs.lean").read_text()
            for loop in (0, 2, 4, 5, "3_loop0"):
                if projected(actual, loop) != projected(program.read_text(), loop):
                    raise ValueError(f"{target}: recovery loop {loop} changed")
    for module,names in (("WideFors",["absolute_indices","pack_roots_sha256","pack_roots_sha512","compress_fallback"]),
                         ("WideForsTail",["scalar_tail"]),("WideForsHashes",["leaf_eq","parent512_eq"]),
                         ("WideForsCompress",["compression256_spec","final_eq"]),
                         ("WideForsRecovery",["hardware_recover_fips"]),("WideForsSchedule",["source_plan_fips"]),
                         ("WideForsDispatch",["dispatch_fips"])):
        facade["audit_theorems"]("Armplatform."+module,["slhdsa.WideFors."+name for name in names])


if __name__ == "__main__":
    check()
