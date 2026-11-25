import Parallel.PhaseTwoObserved

open Aeneas Aeneas.Std Result
namespace slhdsa.WidthThree.ParallelTickets

inductive Host where | linuxArm

noncomputable abbrev signTicket (_ : Host) (_p : params.Params) {N : Usize} :=
  @ParallelSignTicket.ticket N

abbrev sign_ticket (_ : Host) {N : Usize} (p : params.Params) (hp : PN p N) :=
  @ParallelSignTicket.ticket_spec N p hp

def rootHost (_ : Host) := ParallelRootWalk.Host.linuxArm

open Lean Elab Command in
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `ThreeLane
    [(`slhdsa.WidthEight.Platform,``Host),(`slhdsa.WidthEight.Ticket.ticket,``signTicket),
     (`slhdsa.WidthEight.Ticket.ticket_spec,``sign_ticket),(`slhdsa.WidthEight.Ticket.rootHost,``rootHost)]
    #[`slhdsa.WidthEight.Ticket.joined_from_forest]
    [`Parallel.PhaseTwoRoots,`Parallel.PhaseTwoJoin,`Parallel.PhaseTwoWrites]

end slhdsa.WidthThree.ParallelTickets
