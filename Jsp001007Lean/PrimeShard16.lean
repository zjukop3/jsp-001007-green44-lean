import Jsp001007Lean.PrimeData
namespace Jsp001007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0 in
theorem primeChunk16_all_prime : ∀ p : ↥primeChunk16, Nat.Prime p.1 := by decide
end Jsp001007
