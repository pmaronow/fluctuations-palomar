module

public import ComparisonNativeActualInitialCompactClockAlong
public import ComparisonHighStrengthUniformClock

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 8000000
namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock T Tloc : ℝ}

theorem actual_scaled_radius_scalar_integrability
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (hTloc : 0 < Tloc) (alpha : boundedMassProfiles) (a b : ℝ) :
    let S := fun t=>orderedPathS (n+1) M.bf M.hf (M.alpha.val.val (M.xs*t))
    let K := fun t=>actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val (M.xs*t))
    let Gamma := scalarCovarianceResponse hT alpha
    IntegrableOn S (Icc a b) ∧ IntegrableOn K (Icc a b) ∧
    IntegrableOn (fun t=>(S t-Gamma (K t))/M.xs^3) (Icc a b) ∧
    IntegrableOn (fun t=>comparisonRescaledScalarResponse Gamma Tloc M.xs (K t/(Tloc*M.xs))) (Icc a b) ∧
    IntegrableOn (fun t=>((M.b (M.alpha.val.val (M.xs*t))-Tloc)*S t+
      M.h (M.alpha.val.val (M.xs*t)))/M.xs^3) (Icc a b) := by
  intro S K Gamma
  have hu t : M.alpha.val.val (M.xs*t)∈Icc (0:ℝ) 1 := M.alpha.val.property.1 _
  have hmono : Monotone (fun t=>M.alpha.val.val (M.xs*t)) :=
    fun _ _ h=>M.alpha.val.property.2 (mul_le_mul_of_nonneg_left h M.hxs.le)
  have hS : Monotone S := fun s t h=>M.mass_mean_monotone (hu s) (hu t) (hmono h)
  have hS0 t : 0 ≤ S t := M.mass_mean_nonneg (hu t)
  have hK : Monotone K := by
    intro s t h
    exact add_le_add (M.inherited_hf_monotone (hu s) (hu t) (hmono h))
      (mul_le_mul (M.inherited_bf_monotone (hu s) (hu t) (hmono h)) (hS h)
        (hS0 s) (NNReal.coe_nonneg _))
  have hSi := (hS.monotoneOn (Icc a b)).integrableOn_isCompact (μ:=volume) isCompact_Icc
  have hKi := (hK.monotoneOn (Icc a b)).integrableOn_isCompact (μ:=volume) isCompact_Icc
  have hGi : IntegrableOn (fun t=>Gamma (K t)) (Icc a b) := by
    apply Integrable.of_bound
      ((scalarPlantedEnergy_continuous hT alpha).comp_aestronglyMeasurable
        (hKi.div_const T).aestronglyMeasurable) 1
    filter_upwards [] with t
    rw [Real.norm_eq_abs,abs_of_nonneg (scalarPlantedEnergy_bounds hT alpha _).1]
    exact (scalarPlantedEnergy_bounds hT alpha _).2
  refine ⟨hSi,hKi,(hSi.sub hGi).div_const _,?_,?_⟩
  · have H := (hGi.sub (hKi.div_const Tloc)).div_const (M.xs^3)
    apply H.congr
    filter_upwards [] with t
    change (Gamma (K t)-K t/Tloc)/M.xs^3 =
      (Gamma (Tloc*M.xs*(K t/(Tloc*M.xs)))-M.xs*(K t/(Tloc*M.xs)))/M.xs^3
    have he : Tloc*M.xs*(K t/(Tloc*M.xs))=K t := by field_simp [M.hxs.ne',hTloc.ne']
    rw [he]
    congr 1
    field_simp [M.hxs.ne',hTloc.ne']
  · have hb : Monotone (fun t=>M.b (M.alpha.val.val (M.xs*t))) :=
      fun s t h=>M.hb (hu s) (hu t) (hmono h)
    have hh : Monotone (fun t=>M.h (M.alpha.val.val (M.xs*t))) :=
      fun s t h=>M.hh (hu s) (hu t) (hmono h)
    have hb0 t : 0 ≤ M.b (M.alpha.val.val (M.xs*t)) :=
      (M.hlam.le.trans M.hlb).trans (M.hb (by norm_num) (hu t) (hu t).1)
    have hbs : Monotone (fun t=>M.b (M.alpha.val.val (M.xs*t))*S t) :=
      fun s t h=>mul_le_mul (hb h) (hS h) (hS0 s) (hb0 t)
    have H := ((((hbs.monotoneOn (Icc a b)).integrableOn_isCompact (μ:=volume) isCompact_Icc).sub
      (hSi.const_mul Tloc)).add
      ((hh.monotoneOn (Icc a b)).integrableOn_isCompact (μ:=volume) isCompact_Icc)).div_const (M.xs^3)
    apply H.congr
    filter_upwards [] with t
    simp only [Pi.add_apply,Pi.sub_apply]
    ring

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
