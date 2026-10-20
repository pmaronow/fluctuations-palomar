module

public import ComparisonSignedCavityActualPairedGammaRows

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
open Hierarchy Cavity

theorem actual_paired_far_radius_geometry
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    {Cmass Cnear W Rmacro u : ℝ} (hCm : 0 ≤ Cmass) (hW : 0 < W) (hxs : M.xs ≤ W)
    (hnear : 8*cu*((Az+1/cl)*(1+Cmass))+4*cu+cu*Az+1 ≤ Cnear)
    (hsmall : (Az+1/cl)*(1+Cmass)*W ≤ Rmacro/4)
    (hu : u∈Icc (0:ℝ) 1) (hfar : Cnear*W ≤ u) :
    4*W ≤ M.R u ∧ M.z ≤ min (M.R u/8) (Rmacro/4) ∧
      ∀v∈Icc (0:ℝ) 1,v ≤ Cmass*W → M.R v ≤ min (M.R u/8) (Rmacro/4) := by
  let Clow:=(Az+1/cl)*(1+Cmass)
  have hClow : 0 < Clow:=by dsimp only [Clow];positivity
  have hAzlow : Az ≤ Clow := by
    have hI : 0 < 1/cl:=one_div_pos.mpr hcl
    have H:=mul_nonneg (show 0 ≤ Az+1/cl by positivity) hCm
    dsimp only [Clow]
    nlinarith
  have hA : cu*Az < Cnear := by
    have H:=mul_nonneg hcu.le hClow.le
    nlinarith
  have h4 : 4*cu ≤ Cnear := by
    have H:=mul_nonneg hcu.le hClow.le
    have HA:=mul_nonneg hcu.le hAz
    nlinarith
  have h8 : 8*cu*Clow ≤ Cnear := by
    have HA:=mul_nonneg hcu.le hAz
    change 8*cu*((Az+1/cl)*(1+Cmass)) ≤ Cnear
    linarith
  have hR:=comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u
  have hspec:=comparisonSweepQuantile_spec M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha hu
  have hzR : M.z ≤ M.R u := by
    by_contra H
    have HA:=M.alpha.val.property.2 (le_of_not_ge H)
    rw [hspec] at HA
    have HR:=(M.regular M.z ⟨le_rfl,M.hz.2⟩).2
    have HZ:=mul_le_mul_of_nonneg_left M.hzxs hcu.le
    have HX:=mul_le_mul_of_nonneg_left hxs (mul_nonneg hcu.le hAz)
    have HAW:=mul_lt_mul_of_pos_right hA hW
    nlinarith
  have hreg:=(M.regular (M.R u) ⟨hzR,hR.2⟩).2
  rw [hspec] at hreg
  have h4W:=mul_le_mul_of_nonneg_right h4 hW.le
  have h8W:=mul_le_mul_of_nonneg_right h8 hW.le
  have hRW : Clow*W ≤ M.R u/8 := by nlinarith
  have hzW : M.z ≤ Clow*W := by
    have HZ:=mul_le_mul_of_nonneg_left hxs hAz
    have HA:=mul_le_mul_of_nonneg_right hAzlow hW.le
    exact M.hzxs.trans (HZ.trans HA)
  refine ⟨by nlinarith,le_min (hzW.trans hRW) (hzW.trans hsmall),?_⟩
  intro v hv hvW
  have HV:=M.inverse_radius_le_source_mass hcl hAz hv
  have Hsum : M.xs+v ≤ (1+Cmass)*W := by nlinarith
  have H:=mul_le_mul_of_nonneg_left Hsum (show 0 ≤ Az+1/cl by positivity)
  have HVW : M.R v ≤ Clow*W := by dsimp only [Clow];nlinarith
  exact le_min (HVW.trans hRW) (HVW.trans hsmall)

end OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
