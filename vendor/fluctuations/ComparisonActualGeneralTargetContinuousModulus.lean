module

public import ComparisonActualGeneralTargetLocalThermalModulus

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000

theorem actual_general_target_mean_same_cut_continuous_modulus
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {Temp d Cm Cr Ct : ℝ} (_hd : 0 ≤ d) (hCr : 0 ≤ Cr)
    (P : ℝ→ℝ) (hP : ∀x,0≤x→0≤P x)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i U : ℕ) (hi : i < U) (hU : U ≤ as.length)
    (Hmean : |actualGeneralTargetOriginalMeanCorrection (n:=n) bf hf as i U| ≤ Cm*d^4)
    (Hresponse : |actualGeneralTargetLongitudinalResponse (n:=n) bf hf as i U| ≤
      Cr*P (nativeOriginalCutLowErrorRadius n bf hf as i+1/(n+1:ℕ)))
    (HTaylor : |actualGeneralTargetOriginalTaylorPart (n:=n) bf hf as i U| ≤
      Ct*P (nativeOriginalCutLowErrorRadius n bf hf as i+1/(n+1:ℕ))) :
    |nativePhysicalResourceCenter n bf hf as i-
      nativeOriginalScalarPairMean as (nativeContinuumMixedClock n bf hf as) i| ≤
      Cm*d^4+(2*Temp*Cr+Ct)*
        P (nativeOriginalCutLowErrorRadius n bf hf as i+1/(n+1:ℕ)) := by
  let Di:=nativeOriginalCutLowErrorRadius n bf hf as i+1/(n+1:ℕ)
  let B:=P Di
  have hDi : 0 ≤ Di := by dsimp only [Di,nativeOriginalCutLowErrorRadius]; positivity
  have hB : 0 ≤ B := hP Di hDi
  have Htransport : |actualGeneralTargetMeanTransportError (n:=n) bf hf as i U U| ≤ (0:ℝ) := by
    simp only [actualGeneralTargetMeanTransportError,sub_self,mul_zero,abs_zero,le_refl]
  have H:=actual_general_target_mean_gap_abs_le_of_bounds bf hf hbf hhf as i U U hi hU ho
    (Cm*d^4) (Cr*B) 0 (Ct*B) Hmean Hresponse Htransport HTaylor
  have Hchi:=actual_general_continuum_chi_mem_unit_on_any_grid (n:=n) bf hf hbf hhf as ho U (by omega) hU
  have Hb : (bf (partitionPoint 0 as i):ℝ) ≤ Temp := by
    have HH:=htotal _ (partitionPoint_mem as ho i)
    linarith only [HH,NNReal.coe_nonneg (hf (partitionPoint 0 as i))]
  have Hcoef : 2*(bf (partitionPoint 0 as i):ℝ)*
      (scalarTerminal.schedule (scalarBoundaryClocks as
        (relocatedClock U 0 (nativeContinuumMixedClock n bf hf as)))).H 0 0 ≤ 2*Temp := by
    have HH:=mul_le_mul_of_nonneg_left Hchi.2 (NNReal.coe_nonneg (bf (partitionPoint 0 as i)))
    nlinarith only [HH,Hb]
  have Hp:=mul_le_mul_of_nonneg_right Hcoef (mul_nonneg hCr hB)
  dsimp only [B,Di] at H Hp ⊢
  nlinarith only [H,Hp]

theorem actual_general_target_continuum_continuous_modulus
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hroot : hf 0=0) {Temp d Cm Cr Ct : ℝ} (hTemp : 0 < Temp)
    (hd : 0 ≤ d) (hCr : 0 ≤ Cr)
    (P : ℝ→ℝ) (hP : Continuous P) (hP0 : ∀x,0≤x→0≤P x)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) (u : PositiveMass) (hu : u∈us)
    (U : ℕ→ℕ)
    (Hprice : ∀ᶠk : ℕ in atTop,
      let as:=finiteCutMasses us k
      let i:=retainedMassPrefixIndex u.val as
      i<U k ∧ U k≤as.length ∧
      |actualGeneralTargetOriginalMeanCorrection (n:=n) bf hf as i (U k)|≤Cm*d^4 ∧
      |actualGeneralTargetLongitudinalResponse (n:=n) bf hf as i (U k)|≤
        Cr*P (nativeOriginalCutLowErrorRadius n bf hf as i+1/(n+1:ℕ)) ∧
      |actualGeneralTargetOriginalTaylorPart (n:=n) bf hf as i (U k)|≤
        Ct*P (nativeOriginalCutLowErrorRadius n bf hf as i+1/(n+1:ℕ))) :
    |orderedPathS (n+1) bf hf u.val-
      scalarCovarianceResponse hTemp (actualMixedMassProfile hTemp (n+1) (by omega) bf hf hbf hhf htotal)
        (actualMixedClock (n+1) bf hf u.val)|≤
      Cm*d^4+(2*Temp*Cr+Ct)*
        P (Real.sqrt (orderedPathB (n+1) bf hf u.val-
          (orderedPathS (n+1) bf hf u.val)^2)+1/(n+1:ℕ)) := by
  have Hgap:=(actual_general_target_mean_original_center_gap_tendsto (n:=n) bf hf hbf hhf
    hroot hTemp htotal us hus u hu).abs
  have Hrad:=native_original_retained_target_low_radius_tendsto n bf hf hbf hhf us hus u hu
  have HP:=((hP.continuousAt).tendsto.comp (Hrad.add_const (1/(n+1:ℕ):ℝ)))
  have Hbound:=(HP.const_mul (2*Temp*Cr+Ct)).const_add (Cm*d^4)
  apply le_of_tendsto_of_tendsto Hgap Hbound
  filter_upwards [Hprice] with k hk
  exact actual_general_target_mean_same_cut_continuous_modulus bf hf hbf hhf hd hCr P hP0 htotal
    _ (finiteCutMasses_ordered us hus k) _ _ hk.1 hk.2.1 hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2

end OAI.SKFluctuations.Cavity
