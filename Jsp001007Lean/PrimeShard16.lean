import Jsp001007Lean.PrimeData

namespace Jsp001007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem primes_prime_block16 (j : Fin 50) :
    Nat.Prime (primes ⟨800 + j.1, by omega⟩) := by
  fin_cases j <;> norm_num [primes]

end Jsp001007
