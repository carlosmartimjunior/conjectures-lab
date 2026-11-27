import Erdos287.GapAtLeastTwo
import Erdos287.ConditionalReduction

namespace Erdos287

/-!
# Main Entry Point & Axiom Audit for Erdős Problem #287

Exports the complete suite of verified Lean 4 theorems for Erdős #287:
1. `erdos_287_iff_no_candidate_set` — equivalence with path-independent complements on `[a, b]`;
2. `erdos_287_sharp_2_3_6` — sharpness witness `1/2 + 1/3 + 1/6 = 1` (`max_gap = 3`);
3. `erdos_287_gap_at_least_two` — unconditional lower bound `max_gap ≥ 2` (Kürschák, 1918);
4. `erdos_287_upto_20000` — unconditional proof of `max_gap ≥ 3` for all `max(S) ≤ 20,000`;
5. `erdos_287_of_linear_prime_collision_hyp` — formal reduction to `LinearPrimeCollisionHyp 20000`.
-/

#print axioms erdos_287_iff_no_candidate_set
#print axioms erdos_287_sharp_2_3_6
#print axioms erdos_287_gap_at_least_two
#print axioms erdos_287_upto_20000
#print axioms erdos_287_of_linear_prime_collision_hyp

end Erdos287
