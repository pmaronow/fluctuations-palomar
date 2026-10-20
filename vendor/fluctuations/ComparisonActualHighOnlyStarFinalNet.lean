module

public import ComparisonNativeInheritedStarActualFinalNet
public import ComparisonActualHighOnlyAnalyticBasics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
def ActualNativeStarOrderSavingAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (p : ℕ) (Craw saving : ℝ)
    {dim : ℕ → ℕ}
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,
    ∀extra : List PositiveMass,(∀u∈extra,u.val ≤ 1) →
    ∃us : List PositiveMass,(∀u∈us,u.val ≤ 1) ∧ (∀u∈extra,u∈us) ∧ (w n).star∈us ∧
      ∀ᶠj : ℕ in atTop,
        let as := finiteCutMasses us j
        let q := completedPathClock (dim n+1) (M n).bf (M n).hf
        let steps := sampleClockSteps q 0 as
        (physicalRawRatio (dim n+1) (p+1) steps 0 (M n).xs
          (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id)^2 ≤ 2*Craw ∧
        nativeRetainedCenteredMoment (dim n) (p+1) (M n).bf (M n).hf as (w n).star.val
          (orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val) ≤
            (((dim n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1))

def ActualNativeStarMomentOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (p : ℕ) (saving : ℝ)
    {dim : ℕ → ℕ}
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,
    ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) → (w n).star∈us →
    ∀ᶠj : ℕ in atTop,
      nativeRetainedCenteredMoment (dim n) (p+1) (M n).bf (M n).hf (finiteCutMasses us j)
        (w n).star.val (orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val) ≤
          (((dim n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1))

theorem actual_native_star_order_saving_on_every_final_net_along_high_only
    {m delta cl cu Az C0 Ct D Bclock Craw saving : ℝ}
    (p : ℕ) (hsaving : 0 < saving)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW : ∀n,0 < W n) (w : ℕ→ActualSlowWindowChoice)
    (H : ActualNativeStarOrderSavingAlong_high_only p Craw saving M W w) :
    ActualNativeStarMomentOnEveryFinalNetAlong_high_only p (saving/2) M W w := by
  filter_upwards [H,hdim.eventually (eventually_gt_atTop (0:ℕ))] with n hn hn0
  intro us hus hstar
  have hWn := hW n
  have hN : 1 < ((dim n+1:ℕ):ℝ) := by exact_mod_cast (by omega : 1 < dim n+1)
  let S := orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val
  let P : Spin (dim n+1) → Spin (dim n+1) → ℝ := fun σ τ=>|orderedOverlap (dim n+1) σ τ-S|^(2*(p+1))
  have hbf := (M n).bf_monotone
  have hhf := (M n).hf_monotone
  obtain ⟨source,hsource,_,hstarsource,Hsource⟩ := hn [] (by simp)
  have HsourceLimit := nativeRetainedPairValue_tendsto (dim n) (M n).bf (M n).hf hbf hhf
    source hsource (w n).star hstarsource P
  have HsourceBound : ∀ᶠj : ℕ in atTop,
      nativeRetainedPairValue (dim n) (M n).bf (M n).hf (finiteCutMasses source j) (w n).star.val P ≤
        (((dim n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1)) := by
    filter_upwards [Hsource] with j hj
    exact hj.2
  have Horiginal : orderedPathPair (dim n+1) (M n).bf (M n).hf P (w n).star.val ≤
      (((dim n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1)) :=
    le_of_tendsto HsourceLimit HsourceBound
  have Hstrict : (((dim n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1)) <
      (((dim n+1:ℕ):ℝ)^(-(saving/2))*W n)^(2*(p+1)) := by
    apply pow_lt_pow_left₀
      (mul_lt_mul_of_pos_right (Real.rpow_lt_rpow_of_exponent_lt hN (by linarith)) hWn)
      (by positivity)
    omega
  have HfinalLimit := nativeRetainedPairValue_tendsto (dim n) (M n).bf (M n).hf hbf hhf
    us hus (w n).star hstar P
  have Hfinal := HfinalLimit.eventually (gt_mem_nhds (Horiginal.trans_lt Hstrict))
  filter_upwards [Hfinal] with j hj
  exact hj.le

def ActualNativeStarFiniteDegreeOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (A : ℕ) (saving : ℝ)
    {dim : ℕ → ℕ}
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,
    ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) → (w n).star∈us →
    ∀ᶠj : ℕ in atTop,∀l : ℕ,0 < l → l ≤ A →
      nativeRetainedCenteredMoment (dim n) l (M n).bf (M n).hf (finiteCutMasses us j)
        (w n).star.val (orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val) ≤
          (((dim n+1:ℕ):ℝ)^(-saving)*W n)^(2*l)

theorem actual_native_star_final_net_to_finite_degrees_along_high_only
    {m delta cl cu Az C0 Ct D Bclock saving : ℝ}
    (A : ℕ) (hA : 0 < A)
    {dim : ℕ → ℕ}
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW : ∀n,0 ≤ W n) (w : ℕ→ActualSlowWindowChoice)
    (H : ActualNativeStarMomentOnEveryFinalNetAlong_high_only (A-1) saving M W w) :
    ActualNativeStarFiniteDegreeOnEveryFinalNetAlong_high_only A saving M W w := by
  have horder : A-1+1=A := by omega
  unfold ActualNativeStarMomentOnEveryFinalNetAlong_high_only at H
  simp only [horder] at H
  filter_upwards [H] with n hn
  intro us hus hstar
  filter_upwards [hn us hus hstar] with j hj
  intro l hl hlA
  exact nativeRetainedCenteredMoment_lower_order (dim n) l A hl hlA (M n).bf (M n).hf
    (finiteCutMasses us j) (finiteCutMasses_ordered us hus j) (w n).star.val
    (orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val)
    (((dim n+1:ℕ):ℝ)^(-saving)*W n)
    (mul_nonneg (Real.rpow_nonneg (by positivity) _) (hW n)) hj

end OAI.SKFluctuations.LaplaceWindowFormalization
