import Jsp001007Lean.PrimeData

namespace Jsp001007

theorem primes_prime_block17 (j : Fin 50) :
    Nat.Prime (primes ⟨850 + j.1, by omega⟩) := by
  fin_cases j <;> norm_num [primes]

end Jsp001007
