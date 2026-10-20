module

public import SKConstants.Parameters
public import SKConstants.Asymptotics

public section

open Filter
open scoped Topology

namespace SKConstants

@[expose] noncomputable def optimizedEpsilon (c : ℝ) : ℝ :=
  min (1 / ((2000 : ℕ) : ℝ)) ((1 / ((4 : ℕ) : ℝ) - c) / ((20 : ℕ) : ℝ))

@[expose] noncomputable def optimizedParameters (c : ℝ) : Parameters :=
  family (optimizedEpsilon c)

@[expose] noncomputable def numericalFiniteChainBound
    (c q d C : ℝ) (n : ℕ) : ℝ :=
  C * (n : ℝ) * Real.exp ((n : ℝ) ^ (1 - q) - (n : ℝ) ^ (1 - c) / 2)
    + 2 * (n : ℝ) ^ (-d)

theorem optimizedEpsilon_margins (c : ℝ) (_hc : 0 < c) (hquarter : c < 1 / 4) :
    0 < optimizedEpsilon c ∧ optimizedEpsilon c < 1 / 1000 ∧
      10 * optimizedEpsilon c < 1 / 4 - c := by
  have hgap : 0 < (1 / 4 - c) / 20 := by linarith
  have hpos : 0 < optimizedEpsilon c :=
    lt_min (by norm_num) hgap
  have hleft : optimizedEpsilon c ≤ 1 / 2000 := min_le_left _ _
  have hright : optimizedEpsilon c ≤ (1 / 4 - c) / 20 := min_le_right _ _
  exact ⟨hpos, by linarith, by linarith⟩

theorem optimizedParameters_feasible (c : ℝ) (hc : 0 < c) (hquarter : c < 1 / 4) :
    Feasible c (optimizedParameters c) := by
  obtain ⟨hpos, hsmall, hgap⟩ := optimizedEpsilon_margins c hc hquarter
  exact family_feasible hc hpos hsmall hgap

theorem optimizedParameters_rate_margins (c : ℝ) (hc : 0 < c)
    (hquarter : c < 1 / 4) :
    c < (optimizedParameters c).q ∧ (optimizedParameters c).q < 1 ∧
      0 < (optimizedParameters c).d := by
  have h := optimizedParameters_feasible c hc hquarter
  have hcq : c < (optimizedParameters c).q := by
    unfold Feasible at h
    tauto
  have hqhalf : (optimizedParameters c).q < 1 / 2 := by
    unfold Feasible at h
    tauto
  have hd : 0 < (optimizedParameters c).d := by
    unfold Feasible at h
    tauto
  exact ⟨hcq, by linarith, hd⟩

theorem optimized_numerical_bound_decay (c C : ℝ) (hc : 0 < c)
    (hquarter : c < 1 / 4) :
    Tendsto (numericalFiniteChainBound c (optimizedParameters c).q
      (optimizedParameters c).d C) atTop (𝓝 0) := by
  obtain ⟨hcq, hq, hd⟩ := optimizedParameters_rate_margins c hc hquarter
  exact flow_bound_decay_nat c (optimizedParameters c).q
    (optimizedParameters c).d C hcq hq hd

theorem exists_feasible_natural_rate (c : ℝ) (hc : 0 < c)
    (hquarter : c < 1 / 4) :
    ∃ p : Parameters, Feasible c p ∧ c < p.q ∧ p.q < 1 ∧ 0 < p.d ∧
      ∀ C : ℝ, Tendsto (numericalFiniteChainBound c p.q p.d C) atTop (𝓝 0) := by
  obtain ⟨hcq, hq, hd⟩ := optimizedParameters_rate_margins c hc hquarter
  exact ⟨optimizedParameters c, optimizedParameters_feasible c hc hquarter,
    hcq, hq, hd, fun C => optimized_numerical_bound_decay c C hc hquarter⟩

theorem optimized_convergence_of_finite_chain_bound (c C : ℝ) (hc : 0 < c)
    (hquarter : c < 1 / 4) (err : ℕ → ℝ)
    (hzero : ∀ᶠ n in atTop, 0 ≤ err n)
    (hbound : ∀ᶠ n in atTop, err n ≤
      numericalFiniteChainBound c (optimizedParameters c).q
        (optimizedParameters c).d C n) :
    Tendsto err atTop (𝓝 0) :=
  squeeze_zero' hzero hbound (optimized_numerical_bound_decay c C hc hquarter)

theorem convergence_of_feasible_finite_chain_estimate (c : ℝ) (hc : 0 < c)
    (hquarter : c < 1 / 4) (err : ℕ → ℝ)
    (hzero : ∀ᶠ n in atTop, 0 ≤ err n)
    (hfinite : ∀ p : Parameters, Feasible c p → ∃ C : ℝ,
      ∀ᶠ n in atTop, err n ≤ numericalFiniteChainBound c p.q p.d C n) :
    Tendsto err atTop (𝓝 0) := by
  obtain ⟨C, hbound⟩ := hfinite (optimizedParameters c)
    (optimizedParameters_feasible c hc hquarter)
  exact optimized_convergence_of_finite_chain_bound c C hc hquarter err hzero hbound

end SKConstants
