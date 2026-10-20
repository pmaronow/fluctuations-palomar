module

public import ComparisonSignedCavityPhysicalMeanUniform
public import ComparisonSignedCavityActualTerminalDepth

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

theorem eventually_native_finite_physical_mean_uniform_center
    (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hb : MonotoneOn bf (Icc (0:ℝ) 1)) (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    (hroot : hf 0=0) (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠk : ℕ in atTop,
      let as:=finiteCutMasses us k
      let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
      ∀j ≤ as.length,
        |finitePhysicalMean (n+1) as b h j-nativePhysicalResourceCenter n bf hf as j| ≤ ε := by
  let C:=2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) (completedPathClock (n+1) bf hf)
  have H:=(uniformMasses_mesh_tendsto.mul_const C).eventually
    (gt_mem_nhds (by simpa only [zero_mul] using hε))
  filter_upwards [H] with k hk
  dsimp only
  intro j hj
  exact (finite_physical_mean_uniform_continuum_error n bf hf hb hh hroot
    (finiteCutMasses us k) (finiteCutMasses_ordered us hus k)
    (finiteCutMasses_end us hus k) (by positivity) (finiteCutMasses_mesh us hus k) j hj).trans hk.le

theorem eventually_native_finite_mixed_clock_uniform_center
    (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hb : MonotoneOn bf (Icc (0:ℝ) 1)) (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    (hroot : hf 0=0) (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠk : ℕ in atTop,
      let as:=finiteCutMasses us k
      let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
      ∀j ≤ as.length,
        |finitePhysicalMixedClock (n+1) as b h j-
          (h j+b j*nativePhysicalResourceCenter n bf hf as j)| ≤ ε := by
  let B:=(bf 1:ℝ)+1
  have hB : 0 < B:=by dsimp only [B];positivity
  filter_upwards [eventually_native_finite_physical_mean_uniform_center n bf hf hb hh hroot us hus
    (ε/B) (div_pos hε hB)] with k hk
  dsimp only at hk ⊢
  intro j hj
  have hbj : (bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ) ≤ B:=by
    have H:=hb (partitionPoint_mem _ (finiteCutMasses_ordered us hus k) j) (by norm_num : (1:ℝ)∈Icc 0 1)
      (partitionPoint_mem _ (finiteCutMasses_ordered us hus k) j).2
    have HC : (bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ) ≤ bf 1:=by exact_mod_cast H
    dsimp only [B]
    linarith only [HC]
  unfold finitePhysicalMixedClock
  rw [show (hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)+
      (bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)*finitePhysicalMean (n+1) (finiteCutMasses us k)
        (fun j=>(bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
        (fun j=>(hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)) j-
      ((hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)+
        (bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)*nativePhysicalResourceCenter n bf hf (finiteCutMasses us k) j)=
      (bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)*
        (finitePhysicalMean (n+1) (finiteCutMasses us k)
          (fun j=>(bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
          (fun j=>(hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)) j-
          nativePhysicalResourceCenter n bf hf (finiteCutMasses us k) j) by ring]
  rw [abs_mul,abs_of_nonneg (NNReal.coe_nonneg _)]
  exact (mul_le_mul hbj (hk j hj) (abs_nonneg _) hB.le).trans_eq (mul_div_cancel₀ ε hB.ne')

end OAI.SKFluctuations.Cavity
