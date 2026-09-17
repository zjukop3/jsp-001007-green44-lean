import Jsp001007Lean.PrimeData

open Jsp001007

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

example (i : Fin 1000) : Nat.Prime (primes i) := by
  fin_cases i <;> norm_num [primes]
