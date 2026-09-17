import Jsp001007Lean.PrimeData

open Function
open Jsp001007

set_option maxRecDepth 1000000

example : StrictMono primes := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i <;> norm_num [primes]
