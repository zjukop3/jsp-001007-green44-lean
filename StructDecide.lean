import Jsp001007Lean.PrimeData

open Function
open Jsp001007

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

example : StrictMono primes := by
  decide
