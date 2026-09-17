import Jsp001007Lean.PrimeData

namespace Jsp001007

theorem primes_prime_block19 (j : Fin 50) :
    Nat.Prime (primes ⟨950 + j.1, by omega⟩) := by
  fin_cases j <;> norm_num [primes]

end Jsp001007
