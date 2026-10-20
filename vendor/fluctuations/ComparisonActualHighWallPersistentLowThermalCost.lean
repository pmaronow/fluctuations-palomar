module

public import ComparisonActualHighWallLowDensity
public import ComparisonNativeActualUniformBandL1Density
public import ComparisonSignedCavityTransientForkCost
public import ComparisonSignedCavityTransientLowMovingDensity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000

theorem actual_high_wall_persistent_LOW_thermal_cost_on_final_nets
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Ccut : ℝ) (hCcut : 0 ≤ Ccut)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) :
    ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
      let K:=nativeContinuumMixedClock n M.bf M.hf as
      let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
      ∀(i star U rBound : ℕ) (T : ClockTree (Spin n×Bool) as),
      NativePersistentLowForks i star U T → i ≤ star → star < U → U ≤ as.length →
      T.leaves ≤ rBound → Ccut*M.data.d ≤ 1 → partitionPoint 0 as U ≤ Ccut*M.data.d →
      ∀l t : ℝ,l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
      let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutLowError n U b h K)
      let Cerr:=actualLowErrorComparisonConstant (2*M.data.T) M.data.T
      let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
      let ds:=nativeOriginalCutLowErrorRadius n M.bf M.hf as star+1/(n+1:ℕ)
      T.forkCost R+edgeBudget 0 as R ≤ Cerr*((rBound:ℝ)*(di+ds)+
        (∫u in 0..Ccut*M.data.d,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
          (orderedPathS (n+1) M.bf M.hf u)^2))+3/(n+1:ℕ)) := by
  filter_upwards [original_band_l1_density_on_all_final_nets n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)] with jGrid hband
  dsimp only
  intro i star U rBound T hT hi hs hU hleaf hcut1 hcut l t hl ht
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutLowError n U b h K)
  let Cerr:=actualLowErrorComparisonConstant (2*M.data.T) M.data.T
  let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
  let ds:=nativeOriginalCutLowErrorRadius n M.bf M.hf as star+1/(n+1:ℕ)
  let I:=∫u in 0..Ccut*M.data.d,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
    (orderedPathS (n+1) M.bf M.hf u)^2)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hCe : 0 ≤ Cerr:=actualLowErrorComparisonConstant_nonneg _
    (M.data.hepsilon.1.trans M.data.hepsilon.2).le
  have hR j : 0 ≤ R j:=nativeWholeLawErrorRadius_nonneg _ _ _ _ _
  have Hi : R i ≤ Cerr*di:=by
    have H:=M.data.current_low_error_radius_le_original M.alpha as ho U hl ht i (hi.trans (hs.le.trans hU))
    change R i ≤ if i<U then Cerr*di else 0 at H
    simpa only [show i<U from hi.trans_lt hs,ite_true] using H
  have Hs : R star ≤ Cerr*ds:=by
    have H:=M.data.current_low_error_radius_le_original M.alpha as ho U hl ht star (hs.le.trans hU)
    change R star ≤ if star<U then Cerr*ds else 0 at H
    simpa only [hs,ite_true] using H
  have HF : T.forkCost R ≤ (rBound:ℝ)*Cerr*(di+ds):=by
    have H:=hT.low_forkCost_le R hR
      (fun j hj=>native_low_error_radius_above_cut_zero n U b h K as _ j hj)
    have Hcast : (T.leaves:ℝ)-1 ≤ rBound:=by
      have HH : (T.leaves:ℝ) ≤ rBound:=by exact_mod_cast hleaf
      linarith only [HH]
    have HH:=mul_le_mul_of_nonneg_left (add_le_add Hi Hs) (Nat.cast_nonneg rBound)
    exact (H.trans (mul_le_mul_of_nonneg_right Hcast (add_nonneg (hR i) (hR star)))).trans
      (HH.trans_eq (by ring))
  have HD : edgeBudget 0 as R ≤ Cerr*(I+3/(n+1:ℕ)):=by
    have Hmono:=actual_low_edgeBudget_mono ho (fun j hj=>
      M.data.current_low_error_radius_le_original M.alpha as ho U hl ht j hj)
    have Heq : (fun j=>if j<U then Cerr*(nativeOriginalCutLowErrorRadius n M.bf M.hf as j+1/(n+1:ℕ)) else 0)=
        (fun j=>Cerr*(if j<U then nativeOriginalCutLowErrorRadius n M.bf M.hf as j+1/(n+1:ℕ) else 0)+0*(0:ℝ)):=by
      funext j
      split_ifs <;> simp
    change edgeBudget 0 as R ≤ edgeBudget 0 as _ at Hmono
    rw [Heq,actual_low_edgeBudget_linear] at Hmono
    simp only [zero_mul,add_zero] at Hmono
    have HB:=hband us hus 0 U (Nat.zero_le _) hU
    simp only [Nat.not_lt_zero,ite_false] at HB
    have hz : partitionPoint 0 (finiteCutMasses us jGrid) 0=0:=by cases finiteCutMasses us jGrid <;> rfl
    rw [hz] at HB
    change edgeBudget 0 as (fun j=>if j<U then nativeOriginalCutLowErrorRadius n M.bf M.hf as j+1/(n+1:ℕ) else 0) ≤
      (∫u in 0..partitionPoint 0 as U,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
        (orderedPathS (n+1) M.bf M.hf u)^2))+3/(n+1:ℕ) at HB
    have HI:=native_intervalIntegrable_sqrt_of_intervalIntegrable
      ((physicalOrderedThermal_intervalIntegrable n M.bf M.hf (M.data.bf_monotone M.alpha)
        (M.data.hf_monotone M.alpha)).mono_set (by
          rw [uIcc_of_le (mul_nonneg hCcut M.data.hd.le),uIcc_of_le zero_le_one]
          exact Icc_subset_Icc le_rfl hcut1))
    have HImono : (∫u in 0..partitionPoint 0 as U,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
        (orderedPathS (n+1) M.bf M.hf u)^2)) ≤ I:=
      intervalIntegral.integral_mono_interval le_rfl (partitionPoint_mem as ho U).1 hcut
        (ae_of_all _ (fun _=>Real.sqrt_nonneg _)) HI
    exact Hmono.trans (mul_le_mul_of_nonneg_left (HB.trans (add_le_add HImono le_rfl)) hCe)
  exact (add_le_add HF HD).trans_eq (by ring)

end OAI.SKFluctuations.Cavity
