import Jsp001007Lean.PrimeData
namespace Jsp001007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0 in
theorem primeChunk10_all_prime : ∀ p : ↥primeChunk10, Nat.Prime p.1 := by decide
end Jsp001007
