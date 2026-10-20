module

public import ComparisonActualGeneralTargetMeanBounds
public import ComparisonSignedCavityActualRetainedTargetRadiusLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000

theorem actual_general_target_mean_same_cut_local_thermal_modulus
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {Temp d Cm Cr Ct I a : ℝ} (hd : 0 ≤ d) (hCr : 0 ≤ Cr)
    (hI : 0 ≤ I) (ha : 0 ≤ a)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i U : ℕ) (hi : i < U) (hU : U ≤ as.length)
    (Hmean : |actualGeneralTargetOriginalMeanCorrection (n:=n) bf hf as i U| ≤ Cm*d^4)
    (Hresponse : |actualGeneralTargetLongitudinalResponse (n:=n) bf hf as i U| ≤
      Cr*(d^2*(nativeOriginalCutLowErrorRadius n bf hf as i+1/(n+1:ℕ))+d*I+a*d^3))
    (HTaylor : |actualGeneralTargetOriginalTaylorPart (n:=n) bf hf as i U| ≤
      Ct*(d^2*(nativeOriginalCutLowErrorRadius n bf hf as i+1/(n+1:ℕ))+d*I+a*d^3)) :
    |nativePhysicalResourceCenter n bf hf as i-
      nativeOriginalScalarPairMean as (nativeContinuumMixedClock n bf hf as) i| ≤
      Cm*d^4+(2*Temp*Cr+Ct)*
        (d^2*(nativeOriginalCutLowErrorRadius n bf hf as i+1/(n+1:ℕ))+d*I+a*d^3) := by
  let B:=d^2*(nativeOriginalCutLowErrorRadius n bf hf as i+1/(n+1:ℕ))+d*I+a*d^3
  have hB : 0 ≤ B:=by dsimp only [B,nativeOriginalCutLowErrorRadius];positivity
  have Htransport : |actualGeneralTargetMeanTransportError (n:=n) bf hf as i U U| ≤ (0:ℝ):=by
    simp only [actualGeneralTargetMeanTransportError,sub_self,mul_zero,abs_zero,le_refl]
  have H:=actual_general_target_mean_gap_abs_le_of_bounds bf hf hbf hhf as i U U hi hU ho
    (Cm*d^4) (Cr*B) 0 (Ct*B) Hmean Hresponse Htransport HTaylor
  have Hchi:=actual_general_continuum_chi_mem_unit_on_any_grid (n:=n) bf hf hbf hhf as ho U (by omega) hU
  have Hb : (bf (partitionPoint 0 as i):ℝ) ≤ Temp:=by
    have HH:=htotal _ (partitionPoint_mem as ho i)
    linarith only [HH,NNReal.coe_nonneg (hf (partitionPoint 0 as i))]
  have Hcoef : 2*(bf (partitionPoint 0 as i):ℝ)*
      (scalarTerminal.schedule (scalarBoundaryClocks as
        (relocatedClock U 0 (nativeContinuumMixedClock n bf hf as)))).H 0 0 ≤ 2*Temp:=by
    have HH:=mul_le_mul_of_nonneg_left Hchi.2 (NNReal.coe_nonneg (bf (partitionPoint 0 as i)))
    nlinarith only [HH,Hb]
  have Hp:=mul_le_mul_of_nonneg_right Hcoef (mul_nonneg hCr hB)
  dsimp only at H
  change _ ≤ Cm*d^4+(2*Temp*Cr+Ct)*B
  nlinarith only [H,Hp]

theorem actual_general_target_continuum_local_thermal_modulus
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hroot : hf 0=0) {Temp d Cm Cr Ct I a : ℝ} (hTemp : 0 < Temp)
    (hd : 0 ≤ d) (hCr : 0 ≤ Cr) (hI : 0 ≤ I) (ha : 0 ≤ a)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) (u : PositiveMass) (hu : u∈us)
    (U : ℕ→ℕ)
    (Hprice : ∀ᶠk : ℕ in atTop,
      let as:=finiteCutMasses us k
      let i:=retainedMassPrefixIndex u.val as
      i<U k ∧ U k≤as.length ∧
      |actualGeneralTargetOriginalMeanCorrection (n:=n) bf hf as i (U k)|≤Cm*d^4 ∧
      |actualGeneralTargetLongitudinalResponse (n:=n) bf hf as i (U k)|≤
        Cr*(d^2*(nativeOriginalCutLowErrorRadius n bf hf as i+1/(n+1:ℕ))+d*I+a*d^3) ∧
      |actualGeneralTargetOriginalTaylorPart (n:=n) bf hf as i (U k)|≤
        Ct*(d^2*(nativeOriginalCutLowErrorRadius n bf hf as i+1/(n+1:ℕ))+d*I+a*d^3)) :
    |orderedPathS (n+1) bf hf u.val-
      scalarCovarianceResponse hTemp (actualMixedMassProfile hTemp (n+1) (by omega) bf hf hbf hhf htotal)
        (actualMixedClock (n+1) bf hf u.val)|≤
      Cm*d^4+(2*Temp*Cr+Ct)*
        (d^2*(Real.sqrt (orderedPathB (n+1) bf hf u.val-(orderedPathS (n+1) bf hf u.val)^2)+
          1/(n+1:ℕ))+d*I+a*d^3) := by
  have Hgap:=(actual_general_target_mean_original_center_gap_tendsto (n:=n) bf hf hbf hhf
    hroot hTemp htotal us hus u hu).abs
  have Hrad:=native_original_retained_target_low_radius_tendsto n bf hf hbf hhf us hus u hu
  have Hbound:=((((Hrad.add_const (1/(n+1:ℕ):ℝ)).const_mul (d^2)).add_const (d*I)).add_const
    (a*d^3)).const_mul (2*Temp*Cr+Ct) |>.const_add (Cm*d^4)
  apply le_of_tendsto_of_tendsto Hgap Hbound
  filter_upwards [Hprice] with k hk
  exact actual_general_target_mean_same_cut_local_thermal_modulus bf hf hbf hhf hd hCr hI ha htotal
    _ (finiteCutMasses_ordered us hus k) _ _ hk.1 hk.2.1 hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2

theorem local_thermal_modulus_div_cube
    {d D I a : ℝ} (hd : d ≠ 0) :
    (d^4+d^2*D+d*I+a*d^3)/d^3=d+D/d+I/d^2+a := by
  field_simp

theorem local_thermal_modulus_normalized_tendsto_zero
    (d D I a : ℕ→ℝ) (hd : ∀n,d n≠0)
    (Hd : Tendsto d atTop (𝓝 0))
    (HD : Tendsto (fun n=>D n/d n) atTop (𝓝 0))
    (HI : Tendsto (fun n=>I n/(d n)^2) atTop (𝓝 0))
    (Ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n=>((d n)^4+(d n)^2*D n+d n*I n+a n*(d n)^3)/(d n)^3) atTop (𝓝 0) := by
  have H:=((Hd.add HD).add HI).add Ha
  simp only [add_zero] at H
  exact H.congr (fun n=>(local_thermal_modulus_div_cube (hd n)).symm)

end OAI.SKFluctuations.Cavity
