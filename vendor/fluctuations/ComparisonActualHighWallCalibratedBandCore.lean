module

public import ComparisonActualHighWallPolynomialStarCore
public import ComparisonSignedCavityActualCalibratedBand

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem calibrated_mass_band_of_point
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az)
    {W L B v : ℝ} (hW : 0< W) (hL : 0< L) (hB : 0< B) (hxs : M.xs≤ W)
    (hsmall : (calibratedBandStart cu Az+4*L)*W≤1)
    (hhigh : M.data.s≤ starMassBandConstant cu Az*W)
    (hv : v∈Ioo (starMassBandConstant cu Az*W) (2*starMassBandConstant cu Az*W))
    (hmean : (3*(starMassBandConstant cu Az/cu)/4)*W≤ orderedPathS (n+1) M.bf M.hf v)
    (hupper : ∀u∈Ioc (0:ℝ) 1,orderedPathS (n+1) M.bf M.hf u≤ B*(M.xs+u)) :
    let a:=calibratedBandStart cu Az
    let b:=a+4*L
    let Cs:=B*(1+b)
    let S:=orderedPathS (n+1) M.bf M.hf
    MonotoneOn S (Icc (0:ℝ) 1) ∧
    (∀u∈Icc (a*W) (b*W),
      (3*(starMassBandConstant cu Az/cu)/4)*W≤ S u ∧ S u≤ Cs*W ∧
      (a/cu)*W≤ M.data.wallRadius M.alpha u ∧ M.data.wallRadius M.alpha u≤(b/cl)*W ∧
      M.xs≤ M.data.wallRadius M.alpha u ∧ M.z≤ M.data.wallRadius M.alpha u/2) ∧
    S (b*W)-S (a*W)≤ Cs*W := by
  dsimp only
  let A:=starMassBandConstant cu Az
  let a:=calibratedBandStart cu Az
  let b:=a+4*L
  let Cs:=B*(1+b)
  have hA : 0< A:=star_mass_band_constant_pos hcu hAz
  have ha : 0< a:=calibrated_band_start_pos hcu hAz
  have hab : a≤ b:=by dsimp only [b];linarith
  have hAv : 2*A≤ a:=by dsimp only [a,calibratedBandStart,A];linarith
  have hav : A≤ a:=by linarith
  have hvi : v∈Icc (0:ℝ) 1:=⟨((mul_pos hA hW).trans hv.1).le,
    hv.2.le.trans ((mul_le_mul_of_nonneg_right (hAv.trans hab) hW.le).trans hsmall)⟩
  have hmono:=M.mass_mean_monotone
  have hall : ∀u∈Icc (a*W) (b*W),
      (3*(A/cu)/4)*W≤ orderedPathS (n+1) M.bf M.hf u ∧
      orderedPathS (n+1) M.bf M.hf u≤ Cs*W ∧
      (a/cu)*W≤ M.data.wallRadius M.alpha u ∧ M.data.wallRadius M.alpha u≤(b/cl)*W ∧
      M.xs≤ M.data.wallRadius M.alpha u ∧ M.z≤ M.data.wallRadius M.alpha u/2:=by
    intro u hu
    have hu0 : 0< u:=(mul_pos ha hW).trans_le hu.1
    have hui : u∈Icc (0:ℝ) 1:=⟨hu0.le,hu.2.trans hsmall⟩
    have hvu : v≤ u:=hv.2.le.trans ((mul_le_mul_of_nonneg_right hAv hW.le).trans hu.1)
    have HS:=hupper u ⟨hu0,hui.2⟩
    have Hsize : M.xs+u≤(1+b)*W:=by nlinarith only [hxs,hu.2]
    have Hup : orderedPathS (n+1) M.bf M.hf u≤ Cs*W:=HS.trans
      (by simpa only [Cs,mul_assoc] using mul_le_mul_of_nonneg_left Hsize hB.le)
    have HR:=M.actual_closed_regular_mass_band_radius_bounds hcl hcu hAz hW hxs hav hsmall
      (hhigh.trans (mul_le_mul_of_nonneg_right hav hW.le)) hu
    have Hlo : 2*W≤(a/cu)*W:=by
      apply mul_le_mul_of_nonneg_right _ hW.le
      apply (le_div_iff₀ hcu).mpr
      dsimp only [a,calibratedBandStart,A]
      linarith [star_mass_band_constant_pos hcu hAz]
    have Hzlo : 2*Az*W≤(a/cu)*W:=by
      have HC : 2*Az≤ a/cu:=by
        apply (le_div_iff₀ hcu).mpr
        dsimp only [a,calibratedBandStart,A,starMassBandConstant]
        nlinarith only [hcu]
      exact mul_le_mul_of_nonneg_right HC hW.le
    have HzW : M.z≤ Az*W:=M.hzxs.trans (mul_le_mul_of_nonneg_left hxs hAz)
    exact ⟨hmean.trans (hmono hvi hui hvu),Hup,HR.1,HR.2,
      hxs.trans (by linarith only [hW,Hlo,HR.1]),by linarith only [HzW,Hzlo,HR.1]⟩
  have hle : a*W≤ b*W:=mul_le_mul_of_nonneg_right hab hW.le
  have HS0:=M.mass_mean_nonneg ⟨(mul_pos ha hW).le,hle.trans hsmall⟩
  refine ⟨hmono,hall,?_⟩
  have Hend:=(hall (b*W) ⟨hle,le_rfl⟩).2.1
  linarith only [Hend,HS0]

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
