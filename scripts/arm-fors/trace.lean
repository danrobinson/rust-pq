import Armplatform.WideForsSchedule
open Spec slhdsa.WideFors

private def encode : Op → String
  | .leaves => "0 0 0"
  | .all16 h k => s!"1 {h} {k}"
  | .pair h k => s!"2 {h} {k}"
  | .scalar h t => s!"3 {h} {t}"
  | .final256 n => s!"4 {n} 0"
  | .try512 n => s!"5 {n} 0"
  | .block512 off => s!"6 {off} 128"
  | .truncate512 n => s!"7 {n} 0"

def main : IO Unit := do
  for pairs in [false,true] do
    for multi in [false,true] do
      for _parity in [false,true] do
        for p in [sha2_128s,sha2_128f,sha2_192s,sha2_192f,sha2_256s,sha2_256f] do
          IO.println (String.intercalate "," ((plan p pairs multi).map encode))
