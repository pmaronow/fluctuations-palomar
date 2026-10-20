module

public import ComparisonSignedCavityPhysicalMeanUniform
public import ComparisonSignedCavityActualTerminalDepth
public import ComparisonNativeActualInheritedClocks

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization NativeOverlapMinimum

theorem eventually_actual_inherited_original_clock_longitudinal_mean_saving
    (r : ℕ) (Bclock Temp : ℝ) (hTemp : 0 ≤ Temp)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp) → M.h 0=0 →
      ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) →
      ∀ᶠk : ℕ in atTop,
        let as := finiteCutMasses us k
        let b := fun j => (M.bf (partitionPoint 0 as j):ℝ)
        let h := fun j => (M.hf (partitionPoint 0 as j):ℝ)
        ∀(K : ℕ→ℝ) (T : ClockTree (Spin n×Bool) as) (U : ℕ) (a : T.Slot),T.leaves ≤ r →
          |nativeOriginalLongitudinalMean T U K
            b h (nativePhysicalResourceCenter n M.bf M.hf as) a| ≤
              ((n+1:ℕ):ℝ)^(-(1:ℝ)/3)*M.xs^2 := by
  let A := 8*(r:ℝ)*(r+1)*(r+2)*Temp
  have hA : 0 ≤ A := by dsimp [A];positivity
  have Hrate := (tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=(2:ℝ)/3+2*m) (s:=(1:ℝ)/3)
      (by linarith) 0 (2*A*C0^2))
  filter_upwards [Hrate] with n hn
  intro M htotal hroot0 us hus
  have had := comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hbf : MonotoneOn M.bf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.1
  have hhf : MonotoneOn M.hf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.2.1
  have hroot := M.inherited_zero_root_field hroot0
  let Cphys := 2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) (completedPathClock (n+1) M.bf M.hf)
  have Hmesh := (uniformMasses_mesh_tendsto.mul_const Cphys).eventually
    (gt_mem_nhds (show (0:ℝ)*Cphys<1/(n+1:ℕ) by simpa only [zero_mul] using
      (show (0:ℝ)<1/(n+1:ℕ) by positivity)))
  filter_upwards [Hmesh] with k hk
  dsimp only
  let as := finiteCutMasses us k
  let b := fun j => (M.bf (partitionPoint 0 as j):ℝ)
  let h := fun j => (M.hf (partitionPoint 0 as j):ℝ)
  have ho : MassOrdered 0 as := finiteCutMasses_ordered us hus k
  have Hcenter (j : ℕ) (hj : j ≤ as.length) :
      |finitePhysicalMean (n+1) as b h j-nativePhysicalResourceCenter n M.bf M.hf as j| ≤
        1/(n+1:ℕ) := by
    exact (finite_physical_mean_uniform_continuum_error n M.bf M.hf hbf hhf hroot as ho
      (finiteCutMasses_end us hus k) (by positivity) (finiteCutMasses_mesh us hus k) j hj).trans hk.le
  have Hbond (j : ℕ) (_hj : j ≤ as.length) : |b j| ≤ Temp := by
    rw [abs_of_nonneg (NNReal.coe_nonneg _)]
    have Htotal:=M.inherited_total_clock_le htotal _ (partitionPoint_mem as ho j)
    linarith [(M.hf (partitionPoint 0 as j)).coe_nonneg]
  have Hnum := M.actual_terminal_power_over_scale hC0 (show 0 ≤ 2*A by positivity)
    (gamma:=1) 1
  simp only [Nat.cast_one,mul_one] at Hnum
  rw [show (1:ℝ)-(1:ℝ)/3+2*m=(2:ℝ)/3+2*m by ring] at Hnum
  have Hsave : 2*A/((n+1:ℕ):ℝ) ≤ ((n+1:ℕ):ℝ)^(-(1:ℝ)/3)*M.xs^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos M.hxs)).mp
    have Hnorm : (2*A/((n+1:ℕ):ℝ))/M.xs^2 ≤
        (2*A*C0^2)*((n+1:ℕ):ℝ)^(-((2:ℝ)/3+2*m)) := by
      simpa only [NativeOverlapContext.N,Real.rpow_neg_one,div_eq_mul_inv,mul_assoc] using Hnum
    exact Hnorm.trans (by simpa only [pow_zero,mul_one,neg_div] using hn)
  intro K T U a hleaves
  have HM := native_original_longitudinal_mean_abs_le T ho U K
    b h (nativePhysicalResourceCenter n M.bf M.hf as) a hTemp (by positivity) Hbond Hcenter
  have Hpoly : 8*(T.leaves:ℝ)*(T.leaves+1)*(T.leaves+2)*Temp ≤ A := by
    dsimp only [A]
    have Hle : (T.leaves:ℝ) ≤ r := by exact_mod_cast hleaves
    gcongr
  apply HM.trans
  apply le_trans _ Hsave
  have HH := mul_le_mul_of_nonneg_right Hpoly
    (show (0:ℝ) ≤ 1/(n+1:ℕ)+1/(n+1:ℕ) by positivity)
  convert HH using 1
  ring

end OAI.SKFluctuations.Cavity
