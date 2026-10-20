module

public import ComparisonActualHighWallStarPolynomialProducer
public import ComparisonActualHighWallCalibratedBandCore

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000
namespace ActualHighWallOverlapMinimum

theorem eventually_actual_high_wall_calibrated_mass_band
    {m delta cl cu Az C0 Ct D Bclock T0 L : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct)
    (hT0 : 0< T0) (hL : 0< L)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxsd : ∀n,(M n).xs≤ (M n).data.d) (hdW : ∀n,(M n).data.d≤ W n)
    (hWlim : Tendsto W atTop (𝓝 0)) (hsRatio : Tendsto (fun n=>(M n).data.s/W n) atTop (𝓝 0))
    (hT : ∀n,T0≤ (M n).data.T) :
    ∃Cs : ℝ,0< Cs ∧ ∀ᶠn in atTop,
      let a:=calibratedBandStart cu Az
      let b:=a+4*L
      let c:=starMassBandConstant cu Az/cu
      let S:=orderedPathS (n+1) (M n).bf (M n).hf
      MonotoneOn S (Icc (0:ℝ) 1) ∧ b*W n≤1 ∧
      (∀u∈Icc (a*W n) (b*W n),
        (3*c/4)*W n≤ S u ∧ S u≤ Cs*W n ∧
        (a/cu)*W n≤ (M n).data.wallRadius (M n).alpha u ∧
        (M n).data.wallRadius (M n).alpha u≤ (b/cl)*W n ∧
        (M n).xs≤ (M n).data.wallRadius (M n).alpha u ∧
        (M n).z≤ (M n).data.wallRadius (M n).alpha u/2) ∧
      S (b*W n)-S (a*W n)≤ Cs*W n := by
  let A:=starMassBandConstant cu Az
  let a:=calibratedBandStart cu Az
  let b:=a+4*L
  have hA : 0< A:=star_mass_band_constant_pos hcu hAz
  have ha : 0< a:=calibrated_band_start_pos hcu hAz
  have hb : 0< b:=by dsimp only [b];linarith
  have hgap : cu*Az< A:=by dsimp only [A,starMassBandConstant];linarith
  have hxs n : (M n).xs≤ W n:=(hxsd n).trans (hdW n)
  obtain ⟨B,hB,HU⟩:=eventually_actual_high_wall_mass_mean_upper Bclock hm hdelta hroom
    hcl hcu hAz hC0 hCt (D:=D)
  have HS:=eventually_actual_high_wall_polynomial_calibrated_star hm hdelta hroom hcl hcu hAz
    hC0 hCt hT0 M W hxsd hdW hWlim hsRatio hT
  have HP:=eventually_actual_high_wall_star_band_parameters hm hdelta hcl hcu hAz hC0 hgap
    M W hxs hsRatio
  have HB:=(hWlim.const_mul b).eventually (eventually_le_nhds (show b*(0:ℝ)<1 by simp))
  refine ⟨B*(1+b),mul_pos hB (by linarith),?_⟩
  filter_upwards [HU,HS,HP,HB] with n hu hs hp hbW
  obtain ⟨P,v,hv,hrest⟩:=hs
  have H:=(M n).calibrated_mass_band_of_point hcl hcu hAz
    ((M n).data.hd.trans_le (hdW n)) hL hB (hxs n) hbW hp.1.le hv hrest.2.2.2.1 (hu (M n))
  exact ⟨H.1,hbW,H.2.1,H.2.2⟩

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
