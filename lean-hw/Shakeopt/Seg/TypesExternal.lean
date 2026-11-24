module
public import Aeneas
public import Slhdsa.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error

abbrev shake256.Sponge := slhdsa.shake256.Sponge
