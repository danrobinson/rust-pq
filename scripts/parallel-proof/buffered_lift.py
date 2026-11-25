"""Make the two read-only row snapshots used by the Aeneas subtree extraction."""

from build import function


def lift_rows(batch, name="xmss_subtree"):
    original = function(batch, name)
    lifted = original
    for bound in ("8", "count"):
        start = f"            for k in 0..{bound} {{"
        body = f"""{start}
                addrs[k] = tree_adrs.with_word2(lvl).with_word3(base + k as u32);
                left[k] = buf[h][2 * k];
                right[k] = buf[h][2 * k + 1];
            }}"""
        if lifted.count(body) != 1:
            raise ValueError(f"review the subtree's {bound}-lane gather before lifting its row")
        snapshot = "            let row = buf[h];\n" + body.replace("= buf[h][", "= row[")
        lifted = lifted.replace(body, snapshot)
    return batch.replace(original, lifted, 1)
