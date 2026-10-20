module

public import ComparisonSignedCavityScalarFlatteningBound

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy
open GaussianCalculus Scalar
set_option maxHeartbeats 3000000

def scalarLowFlattenedSusceptibility {T m : ℝ} (hT : 0 < T)
    (alpha : boundedMassProfiles) (u : ℝ) (hm : 0 < m) : ℝ :=
  ((scalarTailJet hT alpha u).evolve hm (T*u)).H 0 0

theorem scalarLowFlattenedSusceptibility_abs_le_three {T m : ℝ} (hT : 0 < T)
    (alpha : boundedMassProfiles) (u : ℝ) (hm : 0 < m) (hm1 : m ≤ 1) :
    |scalarLowFlattenedSusceptibility hT alpha u hm| ≤ 3 := by
  have H:=clockGradient_abs_le (scalarTailJet hT alpha u).lipschitz
    ((scalarTailJet hT alpha u).smoothG 0) ((scalarTailJet hT alpha u).smoothG 0)
    ((scalarTailJet hT alpha u).smoothH 0) zero_le_one zero_le_one
    (scalarTailJet_G_bound hT alpha u 0) (scalarTailJet_G_bound hT alpha u 0)
    (scalarTailJet_H_abs_le hT alpha u) m (T*u) 0
  rw [abs_of_pos hm] at H
  change |clockGradient m (scalarTailJet hT alpha u).F ((scalarTailJet hT alpha u).G 0)
    ((scalarTailJet hT alpha u).G 0) ((scalarTailJet hT alpha u).H 0) (T*u) 0| ≤ 3
  linarith

theorem scalarPlantedCurvature_zero_eq_root_hessian_sq {T : ℝ} (hT : 0 < T)
    (alpha : boundedMassProfiles) :
    scalarPlantedCurvature hT alpha 0=((scalarTailJet hT alpha 0).H 0 0)^2 := by
  unfold scalarPlantedCurvature
  rw [mul_zero,Real.toNNReal_zero,HeatJet.nonnegativeProfileTest_zero _ _
    (fun s=>(alpha.property.1 (s/T)).2)]
  rfl

theorem scalarLowFlattenedSusceptibility_sq_error
    {T u m A W : ℝ} (hT : 0 < T) (alpha : boundedMassProfiles)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hm : 0 < m) (hm1 : m ≤ 1)
    (hW : 0 ≤ W) (hA : 0 ≤ A) (hmass : alpha.val u ≤ A*W) (hmcap : m ≤ A*W)
    (hcont : ∀s,ContinuousWithinAt alpha.val (Ici s) s) :
    |(scalarLowFlattenedSusceptibility hT alpha u hm)^2-scalarPlantedCurvature hT alpha 0| ≤
      68*T*A*W*u := by
  rw [scalarPlantedCurvature_zero_eq_root_hessian_sq]
  have hd:=scalar_low_flattening_curvature_bound hT alpha hu hu1 hm hm1 hW hA hmass hmcap hcont
  change |scalarLowFlattenedSusceptibility hT alpha u hm-
    (scalarTailJet hT alpha 0).H 0 0| ≤ 17*T*A*W*u at hd
  have hs:=scalarLowFlattenedSusceptibility_abs_le_three hT alpha u hm hm1
  have hh:=scalarTailJet_H_abs_le hT alpha 0 0
  rw [sq_sub_sq,abs_mul]
  have hadd:= (abs_add_le (scalarLowFlattenedSusceptibility hT alpha u hm)
    ((scalarTailJet hT alpha 0).H 0 0)).trans (add_le_add hs hh)
  have H:=mul_le_mul hd hadd (abs_nonneg _) (by positivity : 0 ≤ 17*T*A*W*u)
  nlinarith only [H]

theorem scalarCovarianceResponse_low_flattened_taylor
    {T W A R Ru q u m : ℝ} (hT : 0 < T) (alpha : boundedMassProfiles)
    (hW : 0 ≤ W) (hA : 0 ≤ A) (hR : 0 ≤ R) (hRu : 0 ≤ Ru)
    (hq : 0 ≤ q) (hqu : q ≤ u) (hu1 : u ≤ 1)
    (hqR : q ≤ R*W) (huR : u ≤ Ru*W) (hTq : T*q ≤ 1)
    (hm : 0 < m) (hm1 : m ≤ 1) (hmcap : m ≤ A*W) (hmass : alpha.val u ≤ A*W)
    (hcont : ∀s,ContinuousWithinAt alpha.val (Ici s) s) :
    |scalarCovarianceResponse hT alpha (T*q)-
        (scalarLowFlattenedSusceptibility hT alpha u hm)^2*(T*q)| ≤
      T^2*(scalarSmallClockFluxConstant T A R*R^2+68*A*Ru*R)*W^3 := by
  have hu : 0 ≤ u := hq.trans hqu
  have hmassq := (alpha.property.2 hqu).trans hmass
  have hrem := scalarPlantedEnergy_smallClock_taylor hT alpha hW hA hR hq hqR
    (hqu.trans hu1) hTq hmassq (fun s _=>hcont s)
  rw [scalarPlantedEnergy_zero,sub_zero] at hrem
  have hsq := scalarLowFlattenedSusceptibility_sq_error hT alpha hu hu1 hm hm1
    hW hA hmass hmcap hcont
  have hF : 0 ≤ scalarSmallClockFluxConstant T A R := by
    unfold scalarSmallClockFluxConstant
    positivity
  have hq2 : q^2 ≤ R^2*W^2 := by
    have H:=pow_le_pow_left₀ hq hqR 2
    simpa only [mul_pow] using H
  have hrem' : |scalarPlantedEnergy hT alpha q-T*scalarPlantedCurvature hT alpha 0*q| ≤
      T^2*scalarSmallClockFluxConstant T A R*R^2*W^3 := by
    have H:=mul_le_mul_of_nonneg_left hq2 (by positivity :
      0 ≤ T^2*scalarSmallClockFluxConstant T A R*W)
    exact hrem.trans (by nlinarith only [H])
  have hclockprod : |(scalarPlantedCurvature hT alpha 0-
      (scalarLowFlattenedSusceptibility hT alpha u hm)^2)*(T*q)| ≤
        68*T^2*A*Ru*R*W^3 := by
    rw [abs_mul,abs_sub_comm,abs_of_nonneg (mul_nonneg hT.le hq)]
    have H1:=mul_le_mul_of_nonneg_left huR (by positivity : 0 ≤ 68*T*A*W)
    have H2:=mul_le_mul (hsq.trans H1) (mul_le_mul_of_nonneg_left hqR hT.le)
      (mul_nonneg hT.le hq) (by positivity : 0 ≤ 68*T*A*W*(Ru*W))
    nlinarith only [H2]
  have H:=(abs_add_le
    (scalarPlantedEnergy hT alpha q-T*scalarPlantedCurvature hT alpha 0*q)
    ((scalarPlantedCurvature hT alpha 0-
      (scalarLowFlattenedSusceptibility hT alpha u hm)^2)*(T*q))).trans
      (add_le_add hrem' hclockprod)
  unfold scalarCovarianceResponse
  rw [mul_div_cancel_left₀ q hT.ne']
  have he : (scalarPlantedEnergy hT alpha q-T*scalarPlantedCurvature hT alpha 0*q)+
      (scalarPlantedCurvature hT alpha 0-
        (scalarLowFlattenedSusceptibility hT alpha u hm)^2)*(T*q)=
      scalarPlantedEnergy hT alpha q-
        (scalarLowFlattenedSusceptibility hT alpha u hm)^2*(T*q) := by ring
  rw [he] at H
  nlinarith only [H]

end OAI.SKFluctuations.Hierarchy
