"""Lower the straight-line monomorphic Charon bodies to a functional SHAKE transcript.

References designate cells and projections designate fields. Iterator closures are
evaluated symbolically on an arbitrary accumulator and element before emitting a fold.
"""

from dataclasses import dataclass


@dataclass
class Cell:
    value: object


@dataclass
class Ref:
    cell: Cell


@dataclass
class Record:
    type_id: int
    fields: list


def path(item):
    return ".".join(part["Ident"][0] for part in item["item_meta"]["name"] if "Ident" in part)


def unwrap(value):
    return value.cell.value if isinstance(value, Ref) else value


class Lower:
    def __init__(self, crate):
        if crate["has_errors"]:
            raise ValueError("Charon reported errors")
        self.ir = crate["translated"]
        self.fns = self.ir["fun_decls"]
        self.types = self.ir["type_decls"]
        self.type_nodes = {}
        self.collect_types(self.ir)
        self.closures = {}
        for f in self.fns:
            if f and path(f).endswith(".call_mut") and isinstance(f["body"], dict):
                receiver = self.ty(f["signature"]["inputs"][0])["Ref"][1]
                index = self.ty(receiver)["Adt"]["id"]
                if index in self.closures:
                    raise ValueError("ambiguous closure type")
                self.closures[index] = f

    def collect_types(self, node):
        if isinstance(node, list):
            for item in node:
                self.collect_types(item)
        if isinstance(node, dict):
            if set(node) == {"Value"} and isinstance(node["Value"], list):
                key, val = node["Value"]
                if isinstance(val, dict) and set(val) in ({"Adt"}, {"Ref"}, {"Scalar"}):
                    if key in self.type_nodes and self.type_nodes[key] != val:
                        raise ValueError("ambiguous type node")
                    self.type_nodes[key] = val
            for item in node.values():
                self.collect_types(item)

    def ty(self, node):
        if "Value" in node:
            return node["Value"][1]
        return self.type_nodes[node["Deduplicated"]]

    def item(self, node):
        return self.types[self.ty(node)["Adt"]["id"]]

    def type_args(self, item):
        return item["item_meta"]["name"][-1]["Instantiated"]["skip_binder"]["types"]

    def nat(self, node):
        ty = self.item(node)
        name = path(ty)
        if name == "typenum.uint.UTerm":
            return 0
        if name == "typenum.uint.UInt":
            high, bit = self.type_args(ty)
            b = path(self.item(bit))
            return 2*self.nat(high) + {"typenum.bit.B0": 0, "typenum.bit.B1": 1}[b]
        raise ValueError(f"unexpected typenum {name}")

    def output_size(self, f):
        ty = self.item(f["signature"]["output"])
        if path(ty) != "hybrid_array.Array":
            raise ValueError("expected an output array")
        elem, size = self.type_args(ty)
        if self.ty(elem) != {"Scalar": {"Integer": {"Unsigned": "U8"}}}:
            raise ValueError("expected a byte array")
        return self.nat(size)

    def run(self, f, args):
        body = f["body"]["Structured"]
        if len(args) != body["locals"]["arg_count"]:
            raise ValueError("argument count differs from MIR")
        locals_ = [Cell(None)] + [Cell(x) for x in args]
        locals_.extend(Cell(None) for _ in range(len(body["locals"]["locals"])-len(locals_)))

        def place(p):
            p = p["kind"]
            if "Local" in p:
                return locals_[p["Local"]]
            base, projection = p["Projection"]
            v = place(base).value
            if projection == "Deref" and isinstance(v, Ref):
                return v.cell
            if isinstance(projection, dict) and "Field" in projection and isinstance(v, Record):
                variant, field = projection["Field"]
                if variant is not None:
                    raise ValueError("unexpected enum projection")
                return v.fields[field]
            raise ValueError(f"unsupported projection {projection} on {v}")

        def operand(op):
            mode, p = next(iter(op.items()))
            if mode not in ("Move", "Copy"):
                raise ValueError(f"unsupported operand {mode}")
            return place(p).value

        def rhs(op):
            if "Use" in op:
                return operand(op["Use"][0])
            if "Ref" in op:
                return Ref(place(op["Ref"]["place"]))
            if "Aggregate" in op:
                agg, fields = op["Aggregate"]
                return Record(agg["Adt"][0]["id"], [Cell(operand(x)) for x in fields])
            raise ValueError(f"unsupported rvalue {op}")

        for statement in body["body"]["statements"]:
            op = statement["kind"]
            if op == "Return":
                return locals_[0].value
            tag, rhs_op = next(iter(op.items()))
            if tag == "Assign":
                target, value = rhs_op
                place(target).value = rhs(value)
            elif tag == "Call":
                call = rhs_op["call"]
                idx = call["func"]["Regular"]["kind"]["Fun"]
                place(rhs_op["dest"]).value = self.call(self.fns[idx], [operand(a) for a in call["args"]])
            elif tag == "Drop":
                # Crypto state destruction cannot change the returned logical bytes.
                if path(self.fns[rhs_op["fn_ptr"]["kind"]["Fun"]]) != "sha3.Shake256":
                    raise ValueError("unknown destructor")
            elif tag == "Borrowck":
                if set(rhs_op) != {"FakeRead"}:
                    raise ValueError(f"unsupported borrow operation {rhs_op}")
            elif tag not in ("StorageLive","StorageDead"):
                raise ValueError(f"unsupported control flow {tag}")
        raise ValueError("MIR lacks return")

    def call(self, f, args):
        name = path(f)
        if isinstance(f["body"], dict):
            return self.run(f, args)
        if name == "sha3.default":
            return "x.empty"
        if name == "sha3.clone":
            return unwrap(args[0])
        if name == "digest.Update.chain":
            s, b = args
            return f"(x.update {s} {unwrap(b)})"
        if name == "sha3.update":
            state, b = args
            state.cell.value = f"(x.update {state.cell.value} {unwrap(b)})"
            return None
        if name in ("hybrid_array.as_slice", "hybrid_array.as_ref", "hybrid_array.deref_mut",
                    "zerocopy.IntoBytes.as_bytes"):
            arg, = args
            if not isinstance(arg, Ref):
                raise ValueError("expected borrowed view")
            return arg
        if name == "core.convert.as_ref":
            # <&[u8] as AsRef<[u8]>>::as_ref
            arg, = args
            result = unwrap(arg)
            return result if isinstance(result, Ref) else arg
        if name == "hybrid_array.default":
            return ("output", self.output_size(f))
        if name == "digest.ExtendableOutput.finalize_xof_into":
            state, output = args
            tag, size = output.cell.value
            if tag != "output":
                raise ValueError("unexpected XOF destination")
            output.cell.value = ("final", state, size)
            return None
        if name in ("core.slice.iter","hybrid_array.iter"):
            return ("iterator", unwrap(args[0]))
        if name == "core.iter.traits.iterator.Iterator.copied":
            tag, seq = args[0]
            if tag != "iterator":
                raise ValueError("copied expects a shared iterator")
            return ("copied", seq)
        if name == "core.iter.traits.iterator.Iterator.flatten":
            tag, seq = args[0]
            if tag != "copied":
                raise ValueError("flatten expects borrowed groups")
            return ("flattened", f"{seq}.flatten")
        if name in ("core.slice.iter.for_each", "core.iter.traits.iterator.Iterator.for_each"):
            (tag, seq), closure = args
            if tag not in ("iterator","flattened") or len(closure.fields) != 1:
                raise ValueError("unsupported iterator closure")
            acc = closure.fields[0].value.cell
            original = acc.value
            acc.value = "st"
            item = Ref(Cell("piece"))
            if tag == "flattened":
                item = Ref(Cell(item))
            self.run(self.closures[closure.type_id], [Ref(Cell(closure)), Record(-1, [Cell(item)])])
            expr = acc.value
            acc.value = f"({seq}.foldl (fun st piece => {expr}) {original})"
            return None
        raise ValueError(f"unmodeled external call: {name}")


METHODS = {
    "new_from_pk_seed": ("pk_seed",),
    "prf_sk": ("cached","adrs","sk_seed"),
    "f": ("cached","adrs","m"),
    "h": ("cached","adrs","m1","m2"),
    "t": ("cached","adrs","m"),
    "prf_msg": ("sk_prf","opt_rand","msg"),
    "h_msg": ("rand","pk_seed","pk_root","msg"),
}


def extracted(model, f):
    op = path(f).split(".")[-1]
    body = f["body"]["Structured"]
    param_names = [entry["name"] for entry in body["locals"]["locals"][1:1+body["locals"]["arg_count"]]]
    actual = [{"self":"cached"}.get(k,k) for k in param_names]
    if set(actual) != set(METHODS[op]) or len(actual)!=len(set(actual)):
        raise ValueError(f"unknown {op} input layout: {actual}")
    vals = []
    for k in actual:
        value = k
        if k == "cached":
            value = Record(-1,[Cell(None),Cell(None),Cell(k)])
        elif k in ("pk_seed","sk_prf","sk_seed"):
            value = Record(-1,[Cell(k)])
        vals.append(Ref(Cell(value)))
    result = model.run(f, vals)
    if op == "new_from_pk_seed":
        if len(result.fields) != 3 or any(field.value.fields for field in result.fields[:2]):
            raise ValueError("unknown cached state layout")
        return result.fields[2].value, None
    tag, state, n = result
    if tag != "final" or model.output_size(f) != n:
        raise ValueError("unexpected hash output")
    return state, n
