module
public import S8table.Funs
public import Streamround.Funs
@[expose] public section
namespace S8driverRust
abbrev sha256.stream.round := StreamRoundRust.sha256.stream.round
abbrev sha256.stream.schedule := S8tableRust.sha256.stream.schedule
end S8driverRust
