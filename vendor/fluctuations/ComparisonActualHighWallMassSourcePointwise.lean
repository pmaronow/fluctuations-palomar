module

public import ComparisonActualHighWallHighMassScalarResponseExact
public import ComparisonActualHighWallCriticalMeanRadiusL1Along
public import ComparisonActualHighWallStarClockDistinct
public import ComparisonNativeActualNormalizedScalarGap
public import ComparisonScalarClosureIdentification

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 8000000

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem high_mass_scalar_response_source_bound
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : M.xs=M.data.d) (Gamma : ℝ→ℝ)
    {u : ℝ} (hu : u∈Icc M.data.s 1) :
    let K := actualMixedClock (n+1) M.bf M.hf u
    let S := orderedPathS (n+1) M.bf M.hf u
    let R := M.data.wallRadius M.alpha u
    |comparisonRescaledScalarResponse Gamma M.data.T M.xs
      (K/(M.data.T*M.xs))| ≤
      |(S-Gamma K)/M.xs^3|+
        (1/M.data.T)*|S/M.xs-R/M.xs| := by
  let K := actualMixedClock (n+1) M.bf M.hf u
  let S := orderedPathS (n+1) M.bf M.hf u
  let R := M.data.wallRadius M.alpha u
  let e := M.data.g R
  have he0 : 0 ≤ e :=
    (laplaceComparisonStrength_pos M.data.d (sq_pos_of_pos M.data.hd) R).le
  have he : e ≤ M.xs^2 := by
    simpa only [hfixed] using
      (laplaceComparisonStrength_le M.data.d (sq_nonneg M.data.d) R)
  have hres := M.high_mass_scalar_response_exact Gamma hu
  dsimp only at hres ⊢
  rw [hres]
  have htri := abs_add_le ((Gamma K-S)/M.xs^3) ((e/M.data.T)*(S-R)/M.xs^3)
  have hweight : |(e/M.data.T)*(S-R)/M.xs^3| ≤
      (1/M.data.T)*|S/M.xs-R/M.xs| := by
    have hcoef : e/M.data.T ≤ M.xs^2/M.data.T :=
      div_le_div_of_nonneg_right he M.data.hTpos.le
    have H := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (abs_nonneg (S-R)))
      (pow_pos M.hxs 3).le
    calc
      |(e/M.data.T)*(S-R)/M.xs^3| =
          ((e/M.data.T)*|S-R|)/M.xs^3 := by
            rw [abs_div,abs_mul,abs_of_nonneg
              (div_nonneg he0 M.data.hTpos.le),abs_of_pos (pow_pos M.hxs 3)]
      _ ≤ ((M.xs^2/M.data.T)*|S-R|)/M.xs^3 := H
      _ = (1/M.data.T)*|S/M.xs-R/M.xs| := by
        rw [←sub_div,abs_div,abs_of_pos M.hxs]
        field_simp [M.data.hTpos.ne',M.hxs.ne']
  have hflip : |(Gamma K-S)/M.xs^3|=|(S-Gamma K)/M.xs^3| := by
    rw [show Gamma K-S=-(S-Gamma K) by ring,neg_div,abs_neg]
  rw [hflip] at htri
  exact htri.trans (add_le_add le_rfl hweight)

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
