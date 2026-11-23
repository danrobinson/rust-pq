# Lean may wrap the axiom list after a long declaration name.
/depends on axioms: \[/ {
  record = $0
  while (record !~ /]$/ && getline > 0) record = record $0
  print record
  next
}
{ print }
