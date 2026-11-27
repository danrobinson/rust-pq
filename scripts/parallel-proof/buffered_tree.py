# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Check optimized physical XMSS subtree stack copies with arbitrary primitive bytes."""
import os
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import tempfile
from build import SRC, compile_probe, function
from buffered_lift import lift_rows
import subtree

bv = subtree.bv

def build(directory, batch=None):
    source = Path(__file__).with_name("buffered-tree.rs").read_text()
    source = source.replace("ADDRESS_PATH",str(SRC/"address.rs"))
    if batch is None:
        batch = (SRC/"shake/batch.rs").read_text()
    source = source.replace("// PRODUCTION",function(batch,"xmss_subtree"))
    source = source.replace("pub(super) fn xmss_subtree","fn xmss_subtree")
    for n in (16,24,32):
        for h in range(3,10):
            source += f'''
#[no_mangle] pub extern "C" fn tree{n}_{h}(out: &mut [u8;{n}], sk: &[u8;{n}], seed: &[u8;{n}],
    idx: u32, layer: u32, tree: u64, rest: &[u32;4]) {{
    *out = xmss_subtree(sk,seed,idx,{h},Adrs {{layer,tree,typ:rest[0],keypair:rest[1],word2:rest[2],word3:rest[3]}});
}}
'''
    return compile_probe(directory,source)


def calls(n, height, sk, seed, idx, layer, tree, tail, *, fors=False):
    prefix = bv.Concat(layer,bv.BVV(0,32),tree)
    base = bv.Concat(prefix,*(tail.get_bytes(i,4).reversed for i in range(0,16,4)))
    nodes = {}
    def digest(h,i):
        if (h,i) not in nodes:
            nodes[h,i] = bv.BVS(f"node{h}_{i}",n*8)
        return nodes[h,i]
    def parents(h, first, count):
        indices = range(first,first+count)
        addr = bv.Concat(*(bv.Concat(prefix,bv.BVV(3 if fors else 2,32),
                             tail.get_bytes(4,4).reversed if fors else bv.BVV(0,32),bv.BVV(h,32),
                             (idx << (height-h)) + i) for i in indices))
        left = bv.Concat(*(digest(h-1,2*i) for i in indices))
        right = bv.Concat(*(digest(h-1,2*i+1) for i in indices))
        values = [digest(h,i) for i in indices]
        if count == 1:
            return "parent",(seed,addr,left,right),values[0]
        values.extend(bv.BVS("unused",n*8) for _ in range(8-count))
        return "pairs",(seed,addr,left,right,bv.BVV(count,64)),bv.Concat(*values)
    groups = 1 << (height-3)
    for b in range(groups):
        first = (idx << height)+8*b
        if fors:
            ids = bv.Concat(*((first+i).reversed for i in range(8)))
            kind,args = "fors_leaves",(sk,seed,base,ids,bv.BVV(8,64))
        else:
            kind,args = "leaves",(sk,seed,first,base)
        yield kind,args,bv.Concat(*(digest(0,8*b+l) for l in range(8)))
        level = 1
        while (b+1) % (1 << level) == 0:
            yield parents(level,8*((b+1)//(1 << level)-1),8)
            level += 1
    for h in range(height-2,height+1):
        yield parents(h,0,1 << (height-h))
    yield "return",(),digest(height,0)


def check(image,n,h):
    p = subtree.project_for(image)
    idx = bv.ZeroExt(h,bv.BVS("index",32-h))
    layer,tree,tail = bv.BVS("layer",32),bv.BVS("tree",64),bv.BVS("rest",128)
    sk,seed = bv.BVS("sk",8*n),bv.BVS("seed",8*n)
    out,stop = 0x710000,0x750000
    st = p.factory.call_state(p.loader.find_symbol(f"tree{n}_{h}").rebased_addr,
        out,0x720000,0x730000,idx,layer,tree,0x740000,ret_addr=stop,
        prototype="void f(void*,void*,void*,unsigned,unsigned,unsigned long long,void*)",
        add_options={subtree.angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
                     subtree.angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS})
    for ptr,data in [(0x720000,sk),(0x730000,seed),(0x740000,tail)]:
        st.memory.store(ptr,data)
    subtree.execute(p,st,out,stop,calls(n,h,sk,seed,idx,layer,tree,tail),8,f"buffered tree n={n} h={h}")


def main():
    os.environ["PATH"] = os.pathsep.join([str(Path.home()/".cargo/bin"),os.environ["PATH"]])
    with tempfile.TemporaryDirectory() as d:
        original = (SRC/"shake/batch.rs").read_text()
        for label, source in (("production", original), ("row snapshots", lift_rows(original))):
            print(f"Checking optimized {label} subtree", flush=True)
            image = build(Path(d), source)
            for n in (16,24,32):
                for h in range(3,10):
                    check(image,n,h)
        target = "left[k] = buf[h][2 * k];"
        if original.count(target) != 2:
            raise ValueError("review streaming and final buffered pair inputs")
        bad = build(Path(d), original.replace(target,"left[k] = buf[h][2 * k + 1];",1))
        try:
            check(bad,16,4)
        except ValueError as error:
            if "mismatch at call" not in str(error):
                raise
        else:
            raise ValueError("accepted a swapped streaming sibling")
        print("Rejected a wrong child in the buffered stack's first full parent group.", flush=True)


if __name__ == "__main__":
    main()
