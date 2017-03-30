import theories.analysis.real_limit
import standard

namespace ak_compat

open classical nat real analysis
/- These are definition from an old version of lean2.
   We reintroduce them here to fix a regression.
 -/
noncomputable definition converges_to_seq (X : ℕ → ℝ) (y : ℝ) : Prop :=
  ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ ⦃N : ℕ⦄, ∀ ⦃n : ℕ⦄, n ≥ N → abs (X n - y) < ε
noncomputable definition converges_seq (X : ℕ → ℝ): Prop :=
  ∃ y : ℝ , converges_to_seq X y

noncomputable definition limit_seq (X : ℕ → ℝ) (H : ak_compat.converges_seq X) : ℝ := some H
proposition converges_to_limit_seq (X : ℕ → ℝ) (H : ak_compat.converges_seq X) :
  converges_to_seq X (limit_seq X H) := epsilon_spec H
proposition converges_to_seq_unique {X : ℕ → ℝ} {y₁ y₂ : ℝ} (H₁ : converges_to_seq X y₁) (H₂ : converges_to_seq X y₂) : y₁ = y₂ := 
eq_of_forall_dist_le
  (take ε, suppose ε > 0,
    have e2pos : ε / 2 > 0, from  div_pos_of_pos_of_pos `ε > 0` two_pos,
    obtain N₁ (HN₁ : ∀ {n}, n ≥ N₁ → dist (X n) y₁ < ε / 2), from H₁ e2pos,
    obtain N₂ (HN₂ : ∀ {n}, n ≥ N₂ → dist (X n) y₂ < ε / 2), from H₂ e2pos,
    let N := max N₁ N₂ in
    have dN₁ : dist (X N) y₁ < ε / 2, from HN₁ !le_max_left,
    have dN₂ : dist (X N) y₂ < ε / 2, from HN₂ !le_max_right,
    have dist y₁ y₂ < ε, from calc
      dist y₁ y₂ ≤ dist y₁ (X N) + dist (X N) y₂ : dist_triangle
             ... = dist (X N) y₁ + dist (X N) y₂ : dist_comm
             ... < ε / 2 + ε / 2                 : add_lt_add dN₁ dN₂
             ... = ε                             : add_halves,
    show dist y₁ y₂ ≤ ε, from le_of_lt this)

end ak_compat
