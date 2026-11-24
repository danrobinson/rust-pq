import Mathlib.Tactic
namespace PeerShake.Memory
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem checked0 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) :
    (((0 + 135) ≥ 0) ∧ ((0 + 135) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked1 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) :
    (((0 + 135) ≥ 0) ∧ ((0 + 135) < 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked2 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) :
    (136 > (state (0 + 135))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked3 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) :
    (((136 - (state (0 + 135))) ≥ 0) ∧ ((136 - (state (0 + 135))) < 9223372036854775808)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked4 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) :
    ((n < 9223372036854775808) = ((136 - (state (0 + 135))) < 9223372036854775808)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked5 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (n < (136 - (state (0 + 135))))) :
    (((0 + (state (0 + 135))) ≥ 0) ∧ ((0 + (state (0 + 135))) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked6 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (n < (136 - (state (0 + 135))))) :
    (True ∧ ((0 + (state (0 + 135))) ≥ 0) ∧ (n ≥ 0) ∧ ((0 + n) ≤ n) ∧ (((0 + (state (0 + 135))) + n) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked7 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (n < (136 - (state (0 + 135))))) :
    (n < 256) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked8 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (n < (136 - (state (0 + 135))))) :
    (((0 + 135) ≥ 0) ∧ ((0 + 135) < 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked9 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (n < (136 - (state (0 + 135))))) :
    (((n + pos) - ((n + pos) % 136)) = 0) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked10 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (n < (136 - (state (0 + 135))))) :
    (((if ((0 + 135) = 135) then (((state (0 + 135)) + (n % 256)) % 256) else (if (((0 + (state (0 + 135))) ≤ 135) ∧ (((0 + (state (0 + 135))) + n) > 135)) then (message (135 - (0 + (state (0 + 135))))) else (state 135))) = ((n + pos) % 136)) ∧ (((byte_index ≥ 0) ∧ (byte_index < ((n + pos) % 136))) → ((if (byte_index = (0 + 135)) then (((state (0 + 135)) + (n % 256)) % 256) else (if (((0 + (state (0 + 135))) ≤ byte_index) ∧ (byte_index < ((0 + (state (0 + 135))) + n))) then (message ((0 + byte_index) - (0 + (state (0 + 135))))) else (state byte_index))) = (if ((0 + byte_index) < pos) then (state (0 + byte_index)) else (message ((0 + byte_index) - pos)))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked11 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) :
    (136 > 0) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked12 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) :
    ((((n / 136) * 136) ≥ 0) ∧ (((n / 136) * 136) < 9223372036854775808)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked13 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) :
    (((n - ((n / 136) * 136)) ≥ 0) ∧ ((n - ((n / 136) * 136)) < 9223372036854775808)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked14 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) :
    (((0 + ((n / 136) * 136)) ≥ 0) ∧ ((0 + ((n / 136) * 136)) ≤ n)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked15 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) :
    ((n < 9223372036854775808) = (136 < 9223372036854775808)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked16 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (136 > n)) :
    (((0 + 135) ≥ 0) ∧ ((0 + 135) < 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked17 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (136 > n)) :
    (((0 + ((n / 136) * 136)) ≥ 0) ∧ True ∧ ((n - ((n / 136) * 136)) ≥ 0) ∧ (((0 + ((n / 136) * 136)) + (n - ((n / 136) * 136))) ≤ n) ∧ ((0 + (n - ((n / 136) * 136))) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked18 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (136 > n)) :
    (((n + pos) - ((n + pos) % 136)) = 0) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked19 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (136 > n)) :
    (((if (True ∧ ((0 + (n - ((n / 136) * 136))) > 135)) then (message (((0 + ((n / 136) * 136)) + 135) - 0)) else (if ((0 + 135) = 135) then ((n - ((n / 136) * 136)) % 256) else (state 135))) = ((n + pos) % 136)) ∧ (((byte_index ≥ 0) ∧ (byte_index < ((n + pos) % 136))) → ((if ((byte_index ≥ 0) ∧ (byte_index < (0 + (n - ((n / 136) * 136))))) then (message (((0 + ((n / 136) * 136)) + byte_index) - 0)) else (if (byte_index = (0 + 135)) then ((n - ((n / 136) * 136)) % 256) else (state byte_index))) = (if ((0 + byte_index) < pos) then (state (0 + byte_index)) else (message ((0 + byte_index) - pos)))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked20 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (¬(136 > n))) :
    ((n / 136) < 67818912035696881) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked21 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (¬(136 > n))) :
    (((n / 136) > 0) ∧ True ∧ ((0 + (136 * (n / 136))) ≤ n)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked22 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (¬(136 > n))) :
    (((0 + 135) ≥ 0) ∧ ((0 + 135) < 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked23 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (¬(136 > n))) :
    (((0 + ((n / 136) * 136)) ≥ 0) ∧ True ∧ ((n - ((n / 136) * 136)) ≥ 0) ∧ (((0 + ((n / 136) * 136)) + (n - ((n / 136) * 136))) ≤ n) ∧ ((0 + (n - ((n / 136) * 136))) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked24 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (¬(136 > n))) :
    (((byte_index ≥ 0) ∧ (byte_index < ((n / 136) * 136))) → ((message (0 + byte_index)) = (if ((0 + byte_index) < pos) then (state (0 + byte_index)) else (message ((0 + byte_index) - pos))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked25 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (¬(136 > n))) :
    ((0 + ((n / 136) * 136)) = ((n + pos) - ((n + pos) % 136))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked26 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (¬(136 > n))) :
    (((if (True ∧ ((0 + (n - ((n / 136) * 136))) > 135)) then (message (((0 + ((n / 136) * 136)) + 135) - 0)) else (if ((0 + 135) = 135) then ((n - ((n / 136) * 136)) % 256) else (state 135))) = ((n + pos) % 136)) ∧ (((byte_index ≥ 0) ∧ (byte_index < ((n + pos) % 136))) → ((if ((byte_index ≥ 0) ∧ (byte_index < (0 + (n - ((n / 136) * 136))))) then (message (((0 + ((n / 136) * 136)) + byte_index) - 0)) else (if (byte_index = (0 + 135)) then ((n - ((n / 136) * 136)) % 256) else (state byte_index))) = (if (((0 + ((n / 136) * 136)) + byte_index) < pos) then (state ((0 + ((n / 136) * 136)) + byte_index)) else (message (((0 + ((n / 136) * 136)) + byte_index) - pos)))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked27 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    (((0 + (136 - (state (0 + 135)))) ≥ 0) ∧ ((0 + (136 - (state (0 + 135)))) ≤ n)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked28 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    (((n - (136 - (state (0 + 135)))) ≥ 0) ∧ ((n - (136 - (state (0 + 135)))) < 9223372036854775808)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked29 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    (((0 + (state (0 + 135))) ≥ 0) ∧ ((0 + (state (0 + 135))) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked30 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    (True ∧ ((0 + (state (0 + 135))) ≥ 0) ∧ ((136 - (state (0 + 135))) ≥ 0) ∧ ((0 + (136 - (state (0 + 135)))) ≤ n) ∧ (((0 + (state (0 + 135))) + (136 - (state (0 + 135)))) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked31 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    ((1 > 0) ∧ True ∧ ((0 + (136 * 1)) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked32 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    (((0 + 135) ≥ 0) ∧ ((0 + 135) < 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked33 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    (136 > 0) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked34 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    (((((n - (136 - (state (0 + 135)))) / 136) * 136) ≥ 0) ∧ ((((n - (136 - (state (0 + 135)))) / 136) * 136) < 9223372036854775808)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked35 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    ((((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136)) ≥ 0) ∧ (((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136)) < 9223372036854775808)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked36 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) ≥ 0) ∧ (((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) ≤ n)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked37 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    (((n - (136 - (state (0 + 135)))) < 9223372036854775808) = (136 < 9223372036854775808)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked38 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (136 > (n - (136 - (state (0 + 135)))))) :
    (((0 + 135) ≥ 0) ∧ ((0 + 135) < 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked39 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (136 > (n - (136 - (state (0 + 135)))))) :
    ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) ≥ 0) ∧ True ∧ (((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136)) ≥ 0) ∧ ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + ((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136))) ≤ n) ∧ ((0 + ((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136))) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked40 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (136 > (n - (136 - (state (0 + 135)))))) :
    (((byte_index ≥ 0) ∧ (byte_index < (1 * 136))) → ((if (((0 + (state (0 + 135))) ≤ (0 + byte_index)) ∧ ((0 + byte_index) < ((0 + (state (0 + 135))) + (136 - (state (0 + 135)))))) then (message ((0 + (0 + byte_index)) - (0 + (state (0 + 135))))) else (state (0 + byte_index))) = (if ((0 + byte_index) < pos) then (state (0 + byte_index)) else (message ((0 + byte_index) - pos))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked41 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (136 > (n - (136 - (state (0 + 135)))))) :
    ((0 + (1 * 136)) = ((n + pos) - ((n + pos) % 136))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked42 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (136 > (n - (136 - (state (0 + 135)))))) :
    (((if (True ∧ ((0 + ((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136))) > 135)) then (message ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + 135) - 0)) else (if ((0 + 135) = 135) then (((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136)) % 256) else (if ((0 + 135) = 135) then 0 else (if (((0 + (state (0 + 135))) ≤ 135) ∧ (((0 + (state (0 + 135))) + (136 - (state (0 + 135)))) > 135)) then (message (135 - (0 + (state (0 + 135))))) else (state 135))))) = ((n + pos) % 136)) ∧ (((byte_index ≥ 0) ∧ (byte_index < ((n + pos) % 136))) → ((if ((byte_index ≥ 0) ∧ (byte_index < (0 + ((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136))))) then (message ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + byte_index) - 0)) else (if (byte_index = (0 + 135)) then (((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136)) % 256) else (if (byte_index = (0 + 135)) then 0 else (if (((0 + (state (0 + 135))) ≤ byte_index) ∧ (byte_index < ((0 + (state (0 + 135))) + (136 - (state (0 + 135)))))) then (message ((0 + byte_index) - (0 + (state (0 + 135))))) else (state byte_index))))) = (if (((0 + (1 * 136)) + byte_index) < pos) then (state ((0 + (1 * 136)) + byte_index)) else (message (((0 + (1 * 136)) + byte_index) - pos)))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked43 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (¬(136 > (n - (136 - (state (0 + 135))))))) :
    (((n - (136 - (state (0 + 135)))) / 136) < 67818912035696881) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked44 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (¬(136 > (n - (136 - (state (0 + 135))))))) :
    ((((n - (136 - (state (0 + 135)))) / 136) > 0) ∧ ((0 + (136 - (state (0 + 135)))) ≥ 0) ∧ (((0 + (136 - (state (0 + 135)))) + (136 * ((n - (136 - (state (0 + 135)))) / 136))) ≤ n)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked45 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (¬(136 > (n - (136 - (state (0 + 135))))))) :
    (((0 + 135) ≥ 0) ∧ ((0 + 135) < 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked46 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (¬(136 > (n - (136 - (state (0 + 135))))))) :
    ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) ≥ 0) ∧ True ∧ (((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136)) ≥ 0) ∧ ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + ((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136))) ≤ n) ∧ ((0 + ((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136))) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked47 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (¬(136 > (n - (136 - (state (0 + 135))))))) :
    (((byte_index ≥ 0) ∧ (byte_index < (1 * 136))) → ((if (((0 + (state (0 + 135))) ≤ (0 + byte_index)) ∧ ((0 + byte_index) < ((0 + (state (0 + 135))) + (136 - (state (0 + 135)))))) then (message ((0 + (0 + byte_index)) - (0 + (state (0 + 135))))) else (state (0 + byte_index))) = (if ((0 + byte_index) < pos) then (state (0 + byte_index)) else (message ((0 + byte_index) - pos))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked48 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (¬(136 > (n - (136 - (state (0 + 135))))))) :
    (((byte_index ≥ 0) ∧ (byte_index < (((n - (136 - (state (0 + 135)))) / 136) * 136))) → ((message ((0 + (136 - (state (0 + 135)))) + byte_index)) = (if (((0 + (1 * 136)) + byte_index) < pos) then (state ((0 + (1 * 136)) + byte_index)) else (message (((0 + (1 * 136)) + byte_index) - pos))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked49 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (¬(136 > (n - (136 - (state (0 + 135))))))) :
    (((0 + (1 * 136)) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) = ((n + pos) - ((n + pos) % 136))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked50 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (¬(136 > (n - (136 - (state (0 + 135))))))) :
    (((if (True ∧ ((0 + ((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136))) > 135)) then (message ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + 135) - 0)) else (if ((0 + 135) = 135) then (((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136)) % 256) else (if ((0 + 135) = 135) then 0 else (if (((0 + (state (0 + 135))) ≤ 135) ∧ (((0 + (state (0 + 135))) + (136 - (state (0 + 135)))) > 135)) then (message (135 - (0 + (state (0 + 135))))) else (state 135))))) = ((n + pos) % 136)) ∧ (((byte_index ≥ 0) ∧ (byte_index < ((n + pos) % 136))) → ((if ((byte_index ≥ 0) ∧ (byte_index < (0 + ((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136))))) then (message ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + byte_index) - 0)) else (if (byte_index = (0 + 135)) then (((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136)) % 256) else (if (byte_index = (0 + 135)) then 0 else (if (((0 + (state (0 + 135))) ≤ byte_index) ∧ (byte_index < ((0 + (state (0 + 135))) + (136 - (state (0 + 135)))))) then (message ((0 + byte_index) - (0 + (state (0 + 135))))) else (state byte_index))))) = (if ((((0 + (1 * 136)) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + byte_index) < pos) then (state (((0 + (1 * 136)) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + byte_index)) else (message ((((0 + (1 * 136)) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + byte_index) - pos)))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked51 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (output_len ≥ 0)) (h1 : (output_len ≤ 9223372036854775807)) :
    ((output_len = (((output_len / 136) * 136) + (output_len % 136))) ∧ ((output_len % 136) ≥ 0) ∧ ((output_len % 136) < 136) ∧ ((output_len < 136) = ((output_len / 136) = 0))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked52 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (output_len ≥ 0)) (h1 : (output_len ≤ 9223372036854775807)) (h2 : (completed_blocks ≥ 0)) (h3 : (completed_blocks < (output_len / 136))) :
    (((completed_blocks * 136) ≥ 0) ∧ (((completed_blocks + 1) * 136) ≤ output_len) ∧ ((((completed_blocks + 1) * 136) = (output_len - (output_len % 136))) = ((completed_blocks + 1) = (output_len / 136))) ∧ (((output_len / 136) - completed_blocks) > ((output_len / 136) - (completed_blocks + 1)))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked53 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (output_len ≥ 0)) (h1 : (output_len ≤ 9223372036854775807)) (h2 : (completed_blocks ≥ 0)) (h3 : (completed_blocks < (output_len / 136))) :
    (((index ≥ 0) ∧ (index < 136)) → (((((completed_blocks * 136) + index) / 136) = completed_blocks) ∧ ((((completed_blocks * 136) + index) % 136) = index))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked54 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (output_len ≥ 0)) (h1 : (output_len ≤ 9223372036854775807)) :
    (((index ≥ 0) ∧ (index < (output_len % 136))) → (((((output_len / 136) * 136) + index) < output_len) ∧ (((((output_len / 136) * 136) + index) / 136) = (output_len / 136)) ∧ (((((output_len / 136) * 136) + index) % 136) = index))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked55 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (blocks ≥ 0)) (h1 : (blocks ≤ 67818912035696880)) (h2 : (iteration ≥ 0)) (h3 : (iteration < blocks)) :
    ((((iteration + 1) * 136) ≤ (blocks * 136)) ∧ ((blocks * 136) ≤ 9223372036854775807) ∧ ((((iteration + 1) * 136) = (blocks * 136)) = ((iteration + 1) = blocks)) ∧ ((blocks - (iteration + 1)) < (blocks - iteration))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked56 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (136 > n)) :
    (((0 + ((n / 136) * 136)) ≥ 0) ∧ True ∧ ((n % 136) ≥ 0) ∧ (((0 + ((n / 136) * 136)) + (n % 136)) ≤ n) ∧ ((0 + (n % 136)) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked57 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (136 > n)) :
    (((if (True ∧ ((0 + (n % 136)) > 135)) then (message (((0 + ((n / 136) * 136)) + 135) - 0)) else (if ((0 + 135) = 135) then ((n % 136) % 256) else (state 135))) = ((n + pos) % 136)) ∧ (((byte_index ≥ 0) ∧ (byte_index < ((n + pos) % 136))) → ((if ((byte_index ≥ 0) ∧ (byte_index < (0 + (n % 136)))) then (message (((0 + ((n / 136) * 136)) + byte_index) - 0)) else (if (byte_index = (0 + 135)) then ((n % 136) % 256) else (state byte_index))) = (if ((0 + byte_index) < pos) then (state (0 + byte_index)) else (message ((0 + byte_index) - pos)))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked58 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (¬(136 > n))) :
    (((0 + ((n / 136) * 136)) ≥ 0) ∧ True ∧ ((n % 136) ≥ 0) ∧ (((0 + ((n / 136) * 136)) + (n % 136)) ≤ n) ∧ ((0 + (n % 136)) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked59 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (¬(136 > n))) :
    (((if (True ∧ ((0 + (n % 136)) > 135)) then (message (((0 + ((n / 136) * 136)) + 135) - 0)) else (if ((0 + 135) = 135) then ((n % 136) % 256) else (state 135))) = ((n + pos) % 136)) ∧ (((byte_index ≥ 0) ∧ (byte_index < ((n + pos) % 136))) → ((if ((byte_index ≥ 0) ∧ (byte_index < (0 + (n % 136)))) then (message (((0 + ((n / 136) * 136)) + byte_index) - 0)) else (if (byte_index = (0 + 135)) then ((n % 136) % 256) else (state byte_index))) = (if (((0 + ((n / 136) * 136)) + byte_index) < pos) then (state ((0 + ((n / 136) * 136)) + byte_index)) else (message (((0 + ((n / 136) * 136)) + byte_index) - pos)))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked60 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (136 > (n - (136 - (state (0 + 135)))))) :
    ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) ≥ 0) ∧ True ∧ (((n - (136 - (state (0 + 135)))) % 136) ≥ 0) ∧ ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + ((n - (136 - (state (0 + 135)))) % 136)) ≤ n) ∧ ((0 + ((n - (136 - (state (0 + 135)))) % 136)) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked61 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (136 > (n - (136 - (state (0 + 135)))))) :
    (((if (True ∧ ((0 + ((n - (136 - (state (0 + 135)))) % 136)) > 135)) then (message ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + 135) - 0)) else (if ((0 + 135) = 135) then (((n - (136 - (state (0 + 135)))) % 136) % 256) else (if ((0 + 135) = 135) then 0 else (if (((0 + (state (0 + 135))) ≤ 135) ∧ (((0 + (state (0 + 135))) + (136 - (state (0 + 135)))) > 135)) then (message (135 - (0 + (state (0 + 135))))) else (state 135))))) = ((n + pos) % 136)) ∧ (((byte_index ≥ 0) ∧ (byte_index < ((n + pos) % 136))) → ((if ((byte_index ≥ 0) ∧ (byte_index < (0 + ((n - (136 - (state (0 + 135)))) % 136)))) then (message ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + byte_index) - 0)) else (if (byte_index = (0 + 135)) then (((n - (136 - (state (0 + 135)))) % 136) % 256) else (if (byte_index = (0 + 135)) then 0 else (if (((0 + (state (0 + 135))) ≤ byte_index) ∧ (byte_index < ((0 + (state (0 + 135))) + (136 - (state (0 + 135)))))) then (message ((0 + byte_index) - (0 + (state (0 + 135))))) else (state byte_index))))) = (if (((0 + (1 * 136)) + byte_index) < pos) then (state ((0 + (1 * 136)) + byte_index)) else (message (((0 + (1 * 136)) + byte_index) - pos)))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked62 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (¬(136 > (n - (136 - (state (0 + 135))))))) :
    ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) ≥ 0) ∧ True ∧ (((n - (136 - (state (0 + 135)))) % 136) ≥ 0) ∧ ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + ((n - (136 - (state (0 + 135)))) % 136)) ≤ n) ∧ ((0 + ((n - (136 - (state (0 + 135)))) % 136)) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked63 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 9223372036854775807)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (¬(136 > (n - (136 - (state (0 + 135))))))) :
    (((if (True ∧ ((0 + ((n - (136 - (state (0 + 135)))) % 136)) > 135)) then (message ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + 135) - 0)) else (if ((0 + 135) = 135) then (((n - (136 - (state (0 + 135)))) % 136) % 256) else (if ((0 + 135) = 135) then 0 else (if (((0 + (state (0 + 135))) ≤ 135) ∧ (((0 + (state (0 + 135))) + (136 - (state (0 + 135)))) > 135)) then (message (135 - (0 + (state (0 + 135))))) else (state 135))))) = ((n + pos) % 136)) ∧ (((byte_index ≥ 0) ∧ (byte_index < ((n + pos) % 136))) → ((if ((byte_index ≥ 0) ∧ (byte_index < (0 + ((n - (136 - (state (0 + 135)))) % 136)))) then (message ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + byte_index) - 0)) else (if (byte_index = (0 + 135)) then (((n - (136 - (state (0 + 135)))) % 136) % 256) else (if (byte_index = (0 + 135)) then 0 else (if (((0 + (state (0 + 135))) ≤ byte_index) ∧ (byte_index < ((0 + (state (0 + 135))) + (136 - (state (0 + 135)))))) then (message ((0 + byte_index) - (0 + (state (0 + 135))))) else (state byte_index))))) = (if ((((0 + (1 * 136)) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + byte_index) < pos) then (state (((0 + (1 * 136)) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + byte_index)) else (message ((((0 + (1 * 136)) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + byte_index) - pos)))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked64 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) :
    (((0 + 135) ≥ 0) ∧ ((0 + 135) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked65 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) :
    (((0 + 135) ≥ 0) ∧ ((0 + 135) < 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked66 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) :
    (136 > (state (0 + 135))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked67 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) :
    (((136 - (state (0 + 135))) ≥ 0) ∧ ((136 - (state (0 + 135))) < 2147483648)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked68 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) :
    ((n < 2147483648) = ((136 - (state (0 + 135))) < 2147483648)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked69 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (n < (136 - (state (0 + 135))))) :
    (((0 + (state (0 + 135))) ≥ 0) ∧ ((0 + (state (0 + 135))) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked70 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (n < (136 - (state (0 + 135))))) :
    (True ∧ ((0 + (state (0 + 135))) ≥ 0) ∧ (n ≥ 0) ∧ ((0 + n) ≤ n) ∧ (((0 + (state (0 + 135))) + n) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked71 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (n < (136 - (state (0 + 135))))) :
    (n < 256) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked72 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (n < (136 - (state (0 + 135))))) :
    (((0 + 135) ≥ 0) ∧ ((0 + 135) < 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked73 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (n < (136 - (state (0 + 135))))) :
    (((n + pos) - ((n + pos) % 136)) = 0) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked74 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (n < (136 - (state (0 + 135))))) :
    (((if ((0 + 135) = 135) then (((state (0 + 135)) + (n % 256)) % 256) else (if (((0 + (state (0 + 135))) ≤ 135) ∧ (((0 + (state (0 + 135))) + n) > 135)) then (message (135 - (0 + (state (0 + 135))))) else (state 135))) = ((n + pos) % 136)) ∧ (((byte_index ≥ 0) ∧ (byte_index < ((n + pos) % 136))) → ((if (byte_index = (0 + 135)) then (((state (0 + 135)) + (n % 256)) % 256) else (if (((0 + (state (0 + 135))) ≤ byte_index) ∧ (byte_index < ((0 + (state (0 + 135))) + n))) then (message ((0 + byte_index) - (0 + (state (0 + 135))))) else (state byte_index))) = (if ((0 + byte_index) < pos) then (state (0 + byte_index)) else (message ((0 + byte_index) - pos)))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked75 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) :
    (136 > 0) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked76 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) :
    ((((n / 136) * 136) ≥ 0) ∧ (((n / 136) * 136) < 2147483648)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked77 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) :
    (((0 + ((n / 136) * 136)) ≥ 0) ∧ ((0 + ((n / 136) * 136)) ≤ n)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked78 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) :
    ((n < 2147483648) = (136 < 2147483648)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked79 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (136 > n)) :
    (((0 + 135) ≥ 0) ∧ ((0 + 135) < 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked80 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (136 > n)) :
    (((0 + ((n / 136) * 136)) ≥ 0) ∧ True ∧ ((n % 136) ≥ 0) ∧ (((0 + ((n / 136) * 136)) + (n % 136)) ≤ n) ∧ ((0 + (n % 136)) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked81 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (136 > n)) :
    (((n + pos) - ((n + pos) % 136)) = 0) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked82 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (136 > n)) :
    (((if (True ∧ ((0 + (n % 136)) > 135)) then (message (((0 + ((n / 136) * 136)) + 135) - 0)) else (if ((0 + 135) = 135) then ((n % 136) % 256) else (state 135))) = ((n + pos) % 136)) ∧ (((byte_index ≥ 0) ∧ (byte_index < ((n + pos) % 136))) → ((if ((byte_index ≥ 0) ∧ (byte_index < (0 + (n % 136)))) then (message (((0 + ((n / 136) * 136)) + byte_index) - 0)) else (if (byte_index = (0 + 135)) then ((n % 136) % 256) else (state byte_index))) = (if ((0 + byte_index) < pos) then (state (0 + byte_index)) else (message ((0 + byte_index) - pos)))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked83 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (¬(136 > n))) :
    ((n / 136) < 15790321) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked84 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (¬(136 > n))) :
    (((n / 136) > 0) ∧ True ∧ ((0 + (136 * (n / 136))) ≤ n)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked85 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (¬(136 > n))) :
    (((0 + 135) ≥ 0) ∧ ((0 + 135) < 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked86 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (¬(136 > n))) :
    (((0 + ((n / 136) * 136)) ≥ 0) ∧ True ∧ ((n % 136) ≥ 0) ∧ (((0 + ((n / 136) * 136)) + (n % 136)) ≤ n) ∧ ((0 + (n % 136)) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked87 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (¬(136 > n))) :
    (((byte_index ≥ 0) ∧ (byte_index < ((n / 136) * 136))) → ((message (0 + byte_index)) = (if ((0 + byte_index) < pos) then (state (0 + byte_index)) else (message ((0 + byte_index) - pos))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked88 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (¬(136 > n))) :
    ((0 + ((n / 136) * 136)) = ((n + pos) - ((n + pos) % 136))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked89 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (¬(136 > n))) :
    (((if (True ∧ ((0 + (n % 136)) > 135)) then (message (((0 + ((n / 136) * 136)) + 135) - 0)) else (if ((0 + 135) = 135) then ((n % 136) % 256) else (state 135))) = ((n + pos) % 136)) ∧ (((byte_index ≥ 0) ∧ (byte_index < ((n + pos) % 136))) → ((if ((byte_index ≥ 0) ∧ (byte_index < (0 + (n % 136)))) then (message (((0 + ((n / 136) * 136)) + byte_index) - 0)) else (if (byte_index = (0 + 135)) then ((n % 136) % 256) else (state byte_index))) = (if (((0 + ((n / 136) * 136)) + byte_index) < pos) then (state ((0 + ((n / 136) * 136)) + byte_index)) else (message (((0 + ((n / 136) * 136)) + byte_index) - pos)))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked90 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    (((0 + (136 - (state (0 + 135)))) ≥ 0) ∧ ((0 + (136 - (state (0 + 135)))) ≤ n)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked91 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    (((n - (136 - (state (0 + 135)))) ≥ 0) ∧ ((n - (136 - (state (0 + 135)))) < 2147483648)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked92 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    (((0 + (state (0 + 135))) ≥ 0) ∧ ((0 + (state (0 + 135))) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked93 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    (True ∧ ((0 + (state (0 + 135))) ≥ 0) ∧ ((136 - (state (0 + 135))) ≥ 0) ∧ ((0 + (136 - (state (0 + 135)))) ≤ n) ∧ (((0 + (state (0 + 135))) + (136 - (state (0 + 135)))) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked94 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    ((1 > 0) ∧ True ∧ ((0 + (136 * 1)) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked95 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    (((0 + 135) ≥ 0) ∧ ((0 + 135) < 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked96 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    (136 > 0) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked97 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    (((((n - (136 - (state (0 + 135)))) / 136) * 136) ≥ 0) ∧ ((((n - (136 - (state (0 + 135)))) / 136) * 136) < 2147483648)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked98 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) ≥ 0) ∧ (((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) ≤ n)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked99 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    (((n - (136 - (state (0 + 135)))) < 2147483648) = (136 < 2147483648)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked100 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (136 > (n - (136 - (state (0 + 135)))))) :
    (((0 + 135) ≥ 0) ∧ ((0 + 135) < 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked101 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (136 > (n - (136 - (state (0 + 135)))))) :
    ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) ≥ 0) ∧ True ∧ (((n - (136 - (state (0 + 135)))) % 136) ≥ 0) ∧ ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + ((n - (136 - (state (0 + 135)))) % 136)) ≤ n) ∧ ((0 + ((n - (136 - (state (0 + 135)))) % 136)) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked102 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (136 > (n - (136 - (state (0 + 135)))))) :
    (((byte_index ≥ 0) ∧ (byte_index < (1 * 136))) → ((if (((0 + (state (0 + 135))) ≤ (0 + byte_index)) ∧ ((0 + byte_index) < ((0 + (state (0 + 135))) + (136 - (state (0 + 135)))))) then (message ((0 + (0 + byte_index)) - (0 + (state (0 + 135))))) else (state (0 + byte_index))) = (if ((0 + byte_index) < pos) then (state (0 + byte_index)) else (message ((0 + byte_index) - pos))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked103 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (136 > (n - (136 - (state (0 + 135)))))) :
    ((0 + (1 * 136)) = ((n + pos) - ((n + pos) % 136))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked104 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (136 > (n - (136 - (state (0 + 135)))))) :
    (((if (True ∧ ((0 + ((n - (136 - (state (0 + 135)))) % 136)) > 135)) then (message ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + 135) - 0)) else (if ((0 + 135) = 135) then (((n - (136 - (state (0 + 135)))) % 136) % 256) else (if ((0 + 135) = 135) then 0 else (if (((0 + (state (0 + 135))) ≤ 135) ∧ (((0 + (state (0 + 135))) + (136 - (state (0 + 135)))) > 135)) then (message (135 - (0 + (state (0 + 135))))) else (state 135))))) = ((n + pos) % 136)) ∧ (((byte_index ≥ 0) ∧ (byte_index < ((n + pos) % 136))) → ((if ((byte_index ≥ 0) ∧ (byte_index < (0 + ((n - (136 - (state (0 + 135)))) % 136)))) then (message ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + byte_index) - 0)) else (if (byte_index = (0 + 135)) then (((n - (136 - (state (0 + 135)))) % 136) % 256) else (if (byte_index = (0 + 135)) then 0 else (if (((0 + (state (0 + 135))) ≤ byte_index) ∧ (byte_index < ((0 + (state (0 + 135))) + (136 - (state (0 + 135)))))) then (message ((0 + byte_index) - (0 + (state (0 + 135))))) else (state byte_index))))) = (if (((0 + (1 * 136)) + byte_index) < pos) then (state ((0 + (1 * 136)) + byte_index)) else (message (((0 + (1 * 136)) + byte_index) - pos)))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked105 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (¬(136 > (n - (136 - (state (0 + 135))))))) :
    (((n - (136 - (state (0 + 135)))) / 136) < 15790321) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked106 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (¬(136 > (n - (136 - (state (0 + 135))))))) :
    ((((n - (136 - (state (0 + 135)))) / 136) > 0) ∧ ((0 + (136 - (state (0 + 135)))) ≥ 0) ∧ (((0 + (136 - (state (0 + 135)))) + (136 * ((n - (136 - (state (0 + 135)))) / 136))) ≤ n)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked107 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (¬(136 > (n - (136 - (state (0 + 135))))))) :
    (((0 + 135) ≥ 0) ∧ ((0 + 135) < 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked108 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (¬(136 > (n - (136 - (state (0 + 135))))))) :
    ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) ≥ 0) ∧ True ∧ (((n - (136 - (state (0 + 135)))) % 136) ≥ 0) ∧ ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + ((n - (136 - (state (0 + 135)))) % 136)) ≤ n) ∧ ((0 + ((n - (136 - (state (0 + 135)))) % 136)) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked109 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (¬(136 > (n - (136 - (state (0 + 135))))))) :
    (((byte_index ≥ 0) ∧ (byte_index < (1 * 136))) → ((if (((0 + (state (0 + 135))) ≤ (0 + byte_index)) ∧ ((0 + byte_index) < ((0 + (state (0 + 135))) + (136 - (state (0 + 135)))))) then (message ((0 + (0 + byte_index)) - (0 + (state (0 + 135))))) else (state (0 + byte_index))) = (if ((0 + byte_index) < pos) then (state (0 + byte_index)) else (message ((0 + byte_index) - pos))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked110 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (¬(136 > (n - (136 - (state (0 + 135))))))) :
    (((byte_index ≥ 0) ∧ (byte_index < (((n - (136 - (state (0 + 135)))) / 136) * 136))) → ((message ((0 + (136 - (state (0 + 135)))) + byte_index)) = (if (((0 + (1 * 136)) + byte_index) < pos) then (state ((0 + (1 * 136)) + byte_index)) else (message (((0 + (1 * 136)) + byte_index) - pos))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked111 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (¬(136 > (n - (136 - (state (0 + 135))))))) :
    (((0 + (1 * 136)) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) = ((n + pos) - ((n + pos) % 136))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked112 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (¬(136 > (n - (136 - (state (0 + 135))))))) :
    (((if (True ∧ ((0 + ((n - (136 - (state (0 + 135)))) % 136)) > 135)) then (message ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + 135) - 0)) else (if ((0 + 135) = 135) then (((n - (136 - (state (0 + 135)))) % 136) % 256) else (if ((0 + 135) = 135) then 0 else (if (((0 + (state (0 + 135))) ≤ 135) ∧ (((0 + (state (0 + 135))) + (136 - (state (0 + 135)))) > 135)) then (message (135 - (0 + (state (0 + 135))))) else (state 135))))) = ((n + pos) % 136)) ∧ (((byte_index ≥ 0) ∧ (byte_index < ((n + pos) % 136))) → ((if ((byte_index ≥ 0) ∧ (byte_index < (0 + ((n - (136 - (state (0 + 135)))) % 136)))) then (message ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + byte_index) - 0)) else (if (byte_index = (0 + 135)) then (((n - (136 - (state (0 + 135)))) % 136) % 256) else (if (byte_index = (0 + 135)) then 0 else (if (((0 + (state (0 + 135))) ≤ byte_index) ∧ (byte_index < ((0 + (state (0 + 135))) + (136 - (state (0 + 135)))))) then (message ((0 + byte_index) - (0 + (state (0 + 135))))) else (state byte_index))))) = (if ((((0 + (1 * 136)) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + byte_index) < pos) then (state (((0 + (1 * 136)) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + byte_index)) else (message ((((0 + (1 * 136)) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + byte_index) - pos)))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked113 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (output_len ≥ 0)) (h1 : (output_len ≤ 2147483647)) :
    ((output_len = (((output_len / 136) * 136) + (output_len % 136))) ∧ ((output_len % 136) ≥ 0) ∧ ((output_len % 136) < 136) ∧ ((output_len < 136) = ((output_len / 136) = 0))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked114 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (output_len ≥ 0)) (h1 : (output_len ≤ 2147483647)) (h2 : (completed_blocks ≥ 0)) (h3 : (completed_blocks < (output_len / 136))) :
    (((completed_blocks * 136) ≥ 0) ∧ (((completed_blocks + 1) * 136) ≤ output_len) ∧ ((((completed_blocks + 1) * 136) = (output_len - (output_len % 136))) = ((completed_blocks + 1) = (output_len / 136))) ∧ (((output_len / 136) - completed_blocks) > ((output_len / 136) - (completed_blocks + 1)))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked115 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (output_len ≥ 0)) (h1 : (output_len ≤ 2147483647)) (h2 : (completed_blocks ≥ 0)) (h3 : (completed_blocks < (output_len / 136))) :
    (((index ≥ 0) ∧ (index < 136)) → (((((completed_blocks * 136) + index) / 136) = completed_blocks) ∧ ((((completed_blocks * 136) + index) % 136) = index))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked116 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (output_len ≥ 0)) (h1 : (output_len ≤ 2147483647)) :
    (((index ≥ 0) ∧ (index < (output_len % 136))) → (((((output_len / 136) * 136) + index) < output_len) ∧ (((((output_len / 136) * 136) + index) / 136) = (output_len / 136)) ∧ (((((output_len / 136) * 136) + index) % 136) = index))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked117 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (blocks ≥ 0)) (h1 : (blocks ≤ 15790320)) (h2 : (iteration ≥ 0)) (h3 : (iteration < blocks)) :
    ((((iteration + 1) * 136) ≤ (blocks * 136)) ∧ ((blocks * 136) ≤ 2147483647) ∧ ((((iteration + 1) * 136) = (blocks * 136)) = ((iteration + 1) = blocks)) ∧ ((blocks - (iteration + 1)) < (blocks - iteration))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked118 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) :
    (((n - ((n / 136) * 136)) ≥ 0) ∧ ((n - ((n / 136) * 136)) < 2147483648)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked119 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (136 > n)) :
    (((0 + ((n / 136) * 136)) ≥ 0) ∧ True ∧ ((n - ((n / 136) * 136)) ≥ 0) ∧ (((0 + ((n / 136) * 136)) + (n - ((n / 136) * 136))) ≤ n) ∧ ((0 + (n - ((n / 136) * 136))) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked120 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (136 > n)) :
    (((if (True ∧ ((0 + (n - ((n / 136) * 136))) > 135)) then (message (((0 + ((n / 136) * 136)) + 135) - 0)) else (if ((0 + 135) = 135) then ((n - ((n / 136) * 136)) % 256) else (state 135))) = ((n + pos) % 136)) ∧ (((byte_index ≥ 0) ∧ (byte_index < ((n + pos) % 136))) → ((if ((byte_index ≥ 0) ∧ (byte_index < (0 + (n - ((n / 136) * 136))))) then (message (((0 + ((n / 136) * 136)) + byte_index) - 0)) else (if (byte_index = (0 + 135)) then ((n - ((n / 136) * 136)) % 256) else (state byte_index))) = (if ((0 + byte_index) < pos) then (state (0 + byte_index)) else (message ((0 + byte_index) - pos)))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked121 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (¬(136 > n))) :
    (((0 + ((n / 136) * 136)) ≥ 0) ∧ True ∧ ((n - ((n / 136) * 136)) ≥ 0) ∧ (((0 + ((n / 136) * 136)) + (n - ((n / 136) * 136))) ≤ n) ∧ ((0 + (n - ((n / 136) * 136))) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked122 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (0 = (state (0 + 135)))) (h7 : (¬(136 > n))) :
    (((if (True ∧ ((0 + (n - ((n / 136) * 136))) > 135)) then (message (((0 + ((n / 136) * 136)) + 135) - 0)) else (if ((0 + 135) = 135) then ((n - ((n / 136) * 136)) % 256) else (state 135))) = ((n + pos) % 136)) ∧ (((byte_index ≥ 0) ∧ (byte_index < ((n + pos) % 136))) → ((if ((byte_index ≥ 0) ∧ (byte_index < (0 + (n - ((n / 136) * 136))))) then (message (((0 + ((n / 136) * 136)) + byte_index) - 0)) else (if (byte_index = (0 + 135)) then ((n - ((n / 136) * 136)) % 256) else (state byte_index))) = (if (((0 + ((n / 136) * 136)) + byte_index) < pos) then (state ((0 + ((n / 136) * 136)) + byte_index)) else (message (((0 + ((n / 136) * 136)) + byte_index) - pos)))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked123 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) :
    ((((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136)) ≥ 0) ∧ (((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136)) < 2147483648)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked124 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (136 > (n - (136 - (state (0 + 135)))))) :
    ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) ≥ 0) ∧ True ∧ (((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136)) ≥ 0) ∧ ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + ((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136))) ≤ n) ∧ ((0 + ((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136))) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked125 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (136 > (n - (136 - (state (0 + 135)))))) :
    (((if (True ∧ ((0 + ((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136))) > 135)) then (message ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + 135) - 0)) else (if ((0 + 135) = 135) then (((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136)) % 256) else (if ((0 + 135) = 135) then 0 else (if (((0 + (state (0 + 135))) ≤ 135) ∧ (((0 + (state (0 + 135))) + (136 - (state (0 + 135)))) > 135)) then (message (135 - (0 + (state (0 + 135))))) else (state 135))))) = ((n + pos) % 136)) ∧ (((byte_index ≥ 0) ∧ (byte_index < ((n + pos) % 136))) → ((if ((byte_index ≥ 0) ∧ (byte_index < (0 + ((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136))))) then (message ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + byte_index) - 0)) else (if (byte_index = (0 + 135)) then (((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136)) % 256) else (if (byte_index = (0 + 135)) then 0 else (if (((0 + (state (0 + 135))) ≤ byte_index) ∧ (byte_index < ((0 + (state (0 + 135))) + (136 - (state (0 + 135)))))) then (message ((0 + byte_index) - (0 + (state (0 + 135))))) else (state byte_index))))) = (if (((0 + (1 * 136)) + byte_index) < pos) then (state ((0 + (1 * 136)) + byte_index)) else (message (((0 + (1 * 136)) + byte_index) - pos)))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked126 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (¬(136 > (n - (136 - (state (0 + 135))))))) :
    ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) ≥ 0) ∧ True ∧ (((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136)) ≥ 0) ∧ ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + ((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136))) ≤ n) ∧ ((0 + ((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136))) ≤ 136)) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

theorem checked127 (n pos byte_index output_len completed_blocks index blocks iteration : Int) (state message : Int → Int)
    (h0 : (n ≥ 0)) (h1 : (n ≤ 2147483647)) (h2 : (pos ≥ 0)) (h3 : (pos < 136)) (h4 : ((state 135) = pos)) (h5 : (¬(n < (136 - (state (0 + 135)))))) (h6 : (¬(0 = (state (0 + 135))))) (h7 : (¬(136 > (n - (136 - (state (0 + 135))))))) :
    (((if (True ∧ ((0 + ((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136))) > 135)) then (message ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + 135) - 0)) else (if ((0 + 135) = 135) then (((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136)) % 256) else (if ((0 + 135) = 135) then 0 else (if (((0 + (state (0 + 135))) ≤ 135) ∧ (((0 + (state (0 + 135))) + (136 - (state (0 + 135)))) > 135)) then (message (135 - (0 + (state (0 + 135))))) else (state 135))))) = ((n + pos) % 136)) ∧ (((byte_index ≥ 0) ∧ (byte_index < ((n + pos) % 136))) → ((if ((byte_index ≥ 0) ∧ (byte_index < (0 + ((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136))))) then (message ((((0 + (136 - (state (0 + 135)))) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + byte_index) - 0)) else (if (byte_index = (0 + 135)) then (((n - (136 - (state (0 + 135)))) - (((n - (136 - (state (0 + 135)))) / 136) * 136)) % 256) else (if (byte_index = (0 + 135)) then 0 else (if (((0 + (state (0 + 135))) ≤ byte_index) ∧ (byte_index < ((0 + (state (0 + 135))) + (136 - (state (0 + 135)))))) then (message ((0 + byte_index) - (0 + (state (0 + 135))))) else (state byte_index))))) = (if ((((0 + (1 * 136)) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + byte_index) < pos) then (state (((0 + (1 * 136)) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + byte_index)) else (message ((((0 + (1 * 136)) + (((n - (136 - (state (0 + 135)))) / 136) * 136)) + byte_index) - pos)))))) := by
  classical
  first
  | omega
  | grind
  | (repeat' split <;> first | omega | grind)

end PeerShake.Memory
