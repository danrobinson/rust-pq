import Integration.SlhDsaBridgeMsg
open Reduction SLHDSA
variable (c : Caps)
#synth Fintype (BList Byte c.ml)
#synth DecidableEq (BList Byte c.ml)
#synth Fintype (Bytes Link.vp.params.m)
#synth DecidableEq (Bytes Link.vp.params.n × Bytes Link.vp.params.n × BList Byte c.ml)
#synth Fintype (Bytes Link.vp.params.n × Bytes Link.vp.params.n × BList Byte c.ml)
#synth DecidableEq (Bytes Link.vp.params.n × (Bytes Link.vp.params.n × Bytes Link.vp.params.n × BList Byte c.ml))
#synth Fintype (Bytes Link.vp.params.n × (Bytes Link.vp.params.n × Bytes Link.vp.params.n × BList Byte c.ml) → Bytes Link.vp.params.m)
set_option synthInstance.maxHeartbeats 400000 in
#synth Fintype (Bytes Link.vp.params.n × (Bytes Link.vp.params.n × Bytes Link.vp.params.n × BList Byte c.ml) → Bytes Link.vp.params.m)
