import Jsp001007Lean.PrimeData
import Jsp001007Lean.PrimeShard0
import Jsp001007Lean.PrimeShard1
import Jsp001007Lean.PrimeShard2
import Jsp001007Lean.PrimeShard3
import Jsp001007Lean.PrimeShard4
import Jsp001007Lean.PrimeShard5
import Jsp001007Lean.PrimeShard6
import Jsp001007Lean.PrimeShard7
import Jsp001007Lean.PrimeShard8
import Jsp001007Lean.PrimeShard9
import Jsp001007Lean.PrimeShard10
import Jsp001007Lean.PrimeShard11
import Jsp001007Lean.PrimeShard12
import Jsp001007Lean.PrimeShard13
import Jsp001007Lean.PrimeShard14
import Jsp001007Lean.PrimeShard15
import Jsp001007Lean.PrimeShard16
import Jsp001007Lean.PrimeShard17
import Jsp001007Lean.PrimeShard18
import Jsp001007Lean.PrimeShard19

namespace Jsp001007

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def N0 : ℕ := 100_000
def T0 : ℕ := 10_001

def primeBlock (i : Fin 1000) : Fin 20 :=
  ⟨i.1 / 50, by
    have hi := i.isLt
    omega⟩

def primeOffset (i : Fin 1000) : Fin 50 :=
  ⟨i.1 % 50, by
    exact Nat.mod_lt _ (by norm_num)⟩

lemma prime_index_decomp (i : Fin 1000) :
    50 * (primeBlock i).1 + (primeOffset i).1 = i.1 := by
  dsimp [primeBlock, primeOffset]
  omega

theorem primes_prime (i : Fin 1000) : Nat.Prime (primes i) := by
  let b := primeBlock i
  let j := primeOffset i
  have hidx : (⟨50 * b.1 + j.1, by
      have hb := b.isLt
      have hj := j.isLt
      omega⟩ : Fin 1000) = i := by
    apply Fin.ext
    simpa [b, j] using prime_index_decomp i
  rw [← hidx]
  fin_cases b
  · simpa using primes_prime_block0 j
  · simpa using primes_prime_block1 j
  · simpa using primes_prime_block2 j
  · simpa using primes_prime_block3 j
  · simpa using primes_prime_block4 j
  · simpa using primes_prime_block5 j
  · simpa using primes_prime_block6 j
  · simpa using primes_prime_block7 j
  · simpa using primes_prime_block8 j
  · simpa using primes_prime_block9 j
  · simpa using primes_prime_block10 j
  · simpa using primes_prime_block11 j
  · simpa using primes_prime_block12 j
  · simpa using primes_prime_block13 j
  · simpa using primes_prime_block14 j
  · simpa using primes_prime_block15 j
  · simpa using primes_prime_block16 j
  · simpa using primes_prime_block17 j
  · simpa using primes_prime_block18 j
  · simpa using primes_prime_block19 j

end Jsp001007
