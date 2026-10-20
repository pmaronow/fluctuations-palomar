module

public import ComparisonSignedCavitySecondLowSoleRootTargetDensityIntegral

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 36000000
set_option backward.isDefEq.respectTransparency false

theorem actual_general_second_low_literal_moving_density_target_integral_on_every_final_net
    (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (scale : ℝ) (hscale : 0 < scale)
    (Couter : ℝ) (hCouter : 0 ≤ Couter) (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) :
    ∀ᶠk : ℕ in atTop,
      let as:=finiteCutMasses us k
      ∀(i U : ℕ) (x : ℝ),U≤as.length → scale≤x → partitionPoint 0 as U≤Couter*x →
        nativeSecondLowLiteralMovingEntryDensity n bf hf as i i U≤
          (∫u in 0..min (Couter*x) 1,Real.sqrt (orderedPathB (n+1) bf hf u-
            (orderedPathS (n+1) bf hf u)^2))+(1+Couter)*x/(n+1:ℕ) := by
  have hb:=hbf
  have hh:=hhf
  let A:=3*physicalBApproximationConstant n bf hf+1
  have Hlim : Tendsto (fun k=>Real.sqrt (((k+1:ℕ):ℝ)⁻¹*A)) atTop (𝓝 0):=by
    have H:=(uniformMasses_mesh_tendsto.mul_const A).sqrt
    simpa only [zero_mul,Real.sqrt_zero] using H
  have HE:=Hlim.eventually (eventually_le_nhds (div_pos hscale (by positivity : 0<((n+1:ℕ):ℝ))))
  filter_upwards [HE] with k hk
  dsimp only
  intro i U x hU hxsx houter
  let as:=finiteCutMasses us k
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hm:partitionPoint 0 as U∈Icc (0:ℝ) 1:=partitionPoint_mem as ho U
  have hx : 0<x:=hscale.trans_le hxsx
  have hq : min (Couter*x) 1∈Icc (0:ℝ) 1:=⟨le_min (mul_nonneg hCouter hx.le) zero_le_one,min_le_right _ _⟩
  have Hcut : partitionPoint 0 as U ≤ min (Couter*x) 1:=le_min houter hm.2
  have HP:=native_second_low_literal_moving_density_le_original_prefix_integral n bf hf as ho i U hU
  have HF:=physicalSampledCutLowError_integral_error n bf hf hb hh as ho
    (finiteCutMasses_end us hus k) (finiteCutMasses_mesh us hus k) hm
  have Hupper:=(abs_le.mp HF).2
  have Hsample : (∫u in 0..partitionPoint 0 as U,
      Real.sqrt (physicalSampledCutLowErrorSecond n bf hf as ho u))≤
      (∫u in 0..partitionPoint 0 as U,Real.sqrt (orderedPathB (n+1) bf hf u-
        (orderedPathS (n+1) bf hf u)^2))+scale/(n+1:ℕ):=by
    have HH:=Hupper
    change _≤Real.sqrt (((k+1:ℕ):ℝ)⁻¹*A) at HH
    linarith
  have HI:=native_intervalIntegrable_sqrt_of_intervalIntegrable (physicalOrderedThermal_intervalIntegrable n bf hf hb hh)
  have HIq:=HI.mono_set (by
    rw [uIcc_of_le hq.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hq.2)
  have Hmono:=intervalIntegral.integral_mono_interval le_rfl hm.1 Hcut
    (ae_of_all _ (fun u=>Real.sqrt_nonneg (orderedPathB (n+1) bf hf u-(orderedPathS (n+1) bf hf u)^2))) HIq
  have Hsite : scale/(n+1:ℕ)+partitionPoint 0 as U/(n+1:ℕ)≤(1+Couter)*x/(n+1:ℕ):=by
    rw [←add_div]
    apply (div_le_div_of_nonneg_right (add_le_add hxsx houter) (by positivity : (0:ℝ)≤(n+1:ℕ))).trans_eq
    ring
  apply (HP.trans (add_le_add Hsample (le_refl (partitionPoint 0 as U/(n+1:ℕ))))).trans
  have HH:=add_le_add Hmono Hsite
  simpa only [add_assoc] using HH

end OAI.SKFluctuations.Cavity
