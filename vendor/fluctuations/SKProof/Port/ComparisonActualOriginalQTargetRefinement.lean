module

public import SKProof.Port.ComparisonActualOriginalQCriticalScaleNumerics
public import ComparisonNativeContinuumScalarPairRefinement
public import ComparisonSignedCavityActualRetainedTargetRadiusLimit
public import SKProof.Port.OriginalQHighOnlyBridge

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option maxHeartbeats 16000000
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem inherited_continuum_retained_scalar_pair_error_eventually
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤T) (hroot : M.h 0=0)
    (us : List PositiveMass) (hus : ∀u∈us,u.val≤1) (u : PositiveMass) (hu : u∈us)
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠk in atTop,
      |nativeOriginalScalarPairMean (finiteCutMasses us k)
          (nativeContinuumMixedClock n M.sweepBf M.sweepHf (finiteCutMasses us k))
          (retainedMassPrefixIndex u.val (finiteCutMasses us k))-
        scalarCovarianceResponse hT (M.inheritedScalarMassProfileBare hT htotal)
          (actualMixedClock (n+1) M.sweepBf M.sweepHf u.val)|≤eps :=
  continuum_retained_scalar_pair_error_eventually n M.sweepBf M.sweepHf M.inherited_bf_monotone
    M.inherited_hf_monotone (M.inherited_zero_root_field hroot) hT
    (M.inherited_total_clock_le htotal) us hus u hu eps heps

theorem inherited_continuum_scalar_pair_errors_on_all_retained_masses
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤T) (hroot : M.h 0=0)
    (us : List PositiveMass) (hus : ∀u∈us,u.val≤1) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠk in atTop,∀u∈us,
      |nativeOriginalScalarPairMean (finiteCutMasses us k)
          (nativeContinuumMixedClock n M.sweepBf M.sweepHf (finiteCutMasses us k))
          (retainedMassPrefixIndex u.val (finiteCutMasses us k))-
        scalarCovarianceResponse hT (M.inheritedScalarMassProfileBare hT htotal)
          (actualMixedClock (n+1) M.sweepBf M.sweepHf u.val)|≤eps := by
  have Hfin (vs : List PositiveMass) (hvs : ∀u∈vs,u∈us) :
      ∀ᶠk in atTop,∀u∈vs,
        |nativeOriginalScalarPairMean (finiteCutMasses us k)
            (nativeContinuumMixedClock n M.sweepBf M.sweepHf (finiteCutMasses us k))
            (retainedMassPrefixIndex u.val (finiteCutMasses us k))-
          scalarCovarianceResponse hT (M.inheritedScalarMassProfileBare hT htotal)
            (actualMixedClock (n+1) M.sweepBf M.sweepHf u.val)|≤eps := by
    induction vs with
    | nil=>exact Eventually.of_forall (by simp)
    | cons v vs ih=>
      have Hv:=M.inherited_continuum_retained_scalar_pair_error_eventually hT htotal hroot
        us hus v (hvs v (List.mem_cons_self)) eps heps
      have Hvs:=ih (by intro u hu;exact hvs u (List.mem_cons_of_mem v hu))
      filter_upwards [Hv,Hvs] with k hkv hkvs
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact hkv
      · exact hkvs u hu
  exact Hfin us (fun _ hu=>hu)

end ActualThetaZeroOverlapMinimum

end OAI.SKFluctuations.LaplaceWindowFormalization
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal
theorem actual_low_error_omitted_site_ratio_le_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (hC0 : 0 < C0) :
    (1/(n+1:ℕ):ℝ)/a.xs^2 ≤ C0^2*a.data.N^(-((2:ℝ)/3+2*m)) := by
  have H:=a.canonical_high_mass_inverse_power hC0 2
  simp only [Nat.cast_ofNat,show (2:ℝ)/6=(1:ℝ)/3 by norm_num] at H
  have HM:=mul_le_mul_of_nonneg_left H (Real.rpow_nonneg a.data.hN.le (-((2:ℝ)/3)))
  have HE : a.data.N^(-((2:ℝ)/3))=a.data.N^((1:ℝ)/3)/a.data.N := by
    calc
      _=a.data.N^(((1:ℝ)/3)-1) := by congr 1;ring
      _=a.data.N^((1:ℝ)/3)/a.data.N^((1:ℝ)) := Real.rpow_sub a.data.hN _ _
      _=_ := by rw [Real.rpow_one]
  have HL : a.data.N^(-((2:ℝ)/3))*(1/(a.data.N^((1:ℝ)/3)*a.xs^2))=
      (1/(n+1:ℕ):ℝ)/a.xs^2 := by
    rw [HE]
    have hpow : a.data.N^((1:ℝ)/3)≠0:=(Real.rpow_pos_of_pos a.data.hN _).ne'
    have hx:=a.hxs.ne'
    have hN:=a.data.hN.ne'
    change _=(1/a.data.N)/a.xs^2
    field_simp
  have HR : a.data.N^(-((2:ℝ)/3))*(C0^2*a.data.N^(-(2:ℝ)*m))=
      C0^2*a.data.N^(-((2:ℝ)/3+2*m)) := by
    rw [mul_left_comm,←Real.rpow_add a.data.hN]
    congr 2
    ring
  rw [HL,HR] at HM
  exact HM

theorem actual_low_error_omitted_site_ratio_tendsto_zero_along_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (a : (n : ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock) :
    Tendsto (fun n=>(1/(dim n+1:ℕ):ℝ)/(a n).xs^2) atTop (𝓝 0) := by
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < (2:ℝ)/3+2*m by positivity)).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Hlim:=Hpow.const_mul (C0^2)
  simp only [mul_zero] at Hlim
  apply squeeze_zero (fun n=>by have hx:=(a n).hxs;positivity)
    (fun n=>actual_low_error_omitted_site_ratio_le_original_q (a n) hC0)
  simpa only [NativeOverlapContext.N,Function.comp_def] using Hlim

theorem actual_original_retained_target_low_radius_tendsto_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (us : List PositiveMass) (hus : ∀v∈us,v.val ≤ 1) (u : PositiveMass) (hu : u∈us) :
    Tendsto (fun j=>nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf (finiteCutMasses us j)
      (retainedMassPrefixIndex u.val (finiteCutMasses us j))) atTop
      (𝓝 (Real.sqrt (orderedPathB (n+1) M.sweepBf M.sweepHf u.val-(orderedPathS (n+1) M.sweepBf M.sweepHf u.val)^2))) :=
  native_original_retained_target_low_radius_tendsto n M.sweepBf M.sweepHf
    M.inherited_bf_monotone M.inherited_hf_monotone us hus u hu

theorem actual_original_retained_target_low_radius_with_site_tendsto_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (us : List PositiveMass) (hus : ∀v∈us,v.val ≤ 1) (u : PositiveMass) (hu : u∈us) :
    Tendsto (fun j=>nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf (finiteCutMasses us j)
      (retainedMassPrefixIndex u.val (finiteCutMasses us j))+1/(n+1:ℕ)) atTop
      (𝓝 (Real.sqrt (orderedPathB (n+1) M.sweepBf M.sweepHf u.val-(orderedPathS (n+1) M.sweepBf M.sweepHf u.val)^2)+
        1/(n+1:ℕ))) :=
  (actual_original_retained_target_low_radius_tendsto_original_q M us hus u hu).add_const _

end OAI.SKFluctuations.Cavity
