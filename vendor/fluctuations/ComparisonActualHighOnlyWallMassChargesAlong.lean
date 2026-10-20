module

public import ComparisonActualHighOnlyInitialCharges

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 2000000
namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_small_mass_ratio_tendsto_zero_along
    (hC0 : 0 < C0) (hm : 0 < m)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ W n) :
    Tendsto (fun n=>(M n).data.U/W n) atTop (𝓝 0) := by
  have Hp : Tendsto (fun n=>((dim n+1:ℕ):ℝ)^(-(3*m))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (show 0<3*m by positivity)).comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Hlim:=Hp.const_mul (C0^3)
  simp only [mul_zero] at Hlim
  apply squeeze_zero (fun n=>div_nonneg (M n).data.hU.le
    ((M n).hxs.trans_le (hxs n)).le) _ Hlim
  intro n
  exact (div_le_div_of_nonneg_left (M n).data.hU.le (M n).hxs (hxs n)).trans
    (by simpa only [ActualHighOnlyComparisonData.N,neg_mul] using (M n).canonical_mass_small_ratio hC0)

theorem actual_omitted_wall_mass_ratio_tendsto_zero_along
    (hC0 : 0 < C0) (hm : 0 < m)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ W n)
    (hs : Tendsto (fun n=>(M n).data.s/W n) atTop (𝓝 0)) :
    Tendsto (fun n=>max (M n).data.U (M n).data.s/W n) atTop (𝓝 0) := by
  have H:=(actual_small_mass_ratio_tendsto_zero_along hC0 hm dim hdim M W hxs).max hs
  simp only [max_self] at H
  have heq n : max (M n).data.U (M n).data.s/W n=
      max ((M n).data.U/W n) ((M n).data.s/W n) := by
    have hw : 0 < W n:=(M n).hxs.trans_le (hxs n)
    by_cases hc : (M n).data.U ≤ (M n).data.s
    · rw [max_eq_right hc,max_eq_right (div_le_div_of_nonneg_right hc hw.le)]
    · rw [max_eq_left (le_of_not_ge hc),max_eq_left
        (div_le_div_of_nonneg_right (le_of_not_ge hc) hw.le)]
  simpa only [heq] using H

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
