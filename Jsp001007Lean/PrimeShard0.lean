import Jsp001007Lean.PrimeData

namespace Jsp001007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem primes_prime_block0 (j : Fin 50) :
    Nat.Prime (primes ⟨0 + j.1, by omega⟩) := by
  fin_cases j <;> norm_num [primes]

end Jsp001007
