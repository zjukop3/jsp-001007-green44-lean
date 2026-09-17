import Jsp001007Lean.PrimeData

open Jsp001007

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

example : StrictMono primes := by
  rw [Fin.strictMono_iff_lt_succ]
  decide
