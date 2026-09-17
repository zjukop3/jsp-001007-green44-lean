import Jsp001007Lean.PrimeData
namespace Jsp001007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0 in
theorem primeChunk8_all_prime : ∀ p : ↥primeChunk8, Nat.Prime p.1 := by decide
end Jsp001007
