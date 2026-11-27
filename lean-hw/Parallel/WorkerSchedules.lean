import Parallel.PhaseTwoObserved
namespace slhdsa.WidthEight.Ticket

/-- Distinct physical publications may have distinct completion orders even if
their table lengths happen to coincide. -/
structure Schedules where
  forest : ∀ n, Schedule n
  chunks : ∀ n, Schedule n
  leaves : ∀ n, Schedule n
  wots : ∀ n, Schedule n

end slhdsa.WidthEight.Ticket
