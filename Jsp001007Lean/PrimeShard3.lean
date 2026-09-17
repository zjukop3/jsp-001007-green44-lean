import Jsp001007Lean.PrimeData

namespace Jsp001007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem primes_prime_block3 (j : Fin 50) :
    Nat.Prime (primes ⟨150 + j.1, by omega⟩) := by
  fin_cases j <;> norm_num [primes, primeBlocks]

theorem primes_lt_block3 (j : Fin 50) :
    primes ⟨150 + j.1, by omega⟩ <
      primes ⟨150 + j.1 + 1, by omega⟩ := by
  fin_cases j <;> norm_num [primes, primeBlocks]

end Jsp001007
