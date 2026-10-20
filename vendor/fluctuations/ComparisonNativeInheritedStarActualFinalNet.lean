module

public import ComparisonNativeStarActualFiniteDegrees
public import ComparisonNativeStarActualFinalNet
public import ComparisonNativeInheritedStarActualAllOrder

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 5000000

def ActualNativeStarMomentOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (p : ℕ) (saving : ℝ)
    {dim : ℕ → ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,
    ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) → (w n).star∈us →
    ∀ᶠj : ℕ in atTop,
      nativeRetainedCenteredMoment (dim n) (p+1) (M n).bf (M n).hf (finiteCutMasses us j)
        (w n).star.val (orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val) ≤
          (((dim n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1))

theorem actual_native_star_order_saving_on_every_final_net_along
    {m delta cl cu Az C0 Ct D Bclock Craw saving : ℝ}
    (p : ℕ) (hsaving : 0 < saving)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW : ∀n,0 < W n) (w : ℕ→ActualSlowWindowChoice)
    (H : ActualNativeStarOrderSavingAlong p Craw saving M W w) :
    ActualNativeStarMomentOnEveryFinalNetAlong p (saving/2) M W w := by
  filter_upwards [H,hdim.eventually (eventually_gt_atTop (0:ℕ))] with n hn hn0
  intro us hus hstar
  have hWn := hW n
  have hN : 1 < ((dim n+1:ℕ):ℝ) := by exact_mod_cast (by omega : 1 < dim n+1)
  let S := orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val
  let P : Spin (dim n+1) → Spin (dim n+1) → ℝ := fun σ τ=>|orderedOverlap (dim n+1) σ τ-S|^(2*(p+1))
  have had := comparisonVariableEndpoint_clocks_admissible (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).context.hm (M n).context.hM (M n).b (M n).h
    (M n).context.hd.ne' (M n).hlam.le (M n).hlb (M n).hb (M n).hh (M n).hh0 (M n).alpha
  have hbf := toNNReal_monotoneOn had.1
  have hhf := toNNReal_monotoneOn had.2.1
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

def ActualNativeStarFiniteDegreeOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (A : ℕ) (saving : ℝ)
    {dim : ℕ → ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,
    ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) → (w n).star∈us →
    ∀ᶠj : ℕ in atTop,∀l : ℕ,0 < l → l ≤ A →
      nativeRetainedCenteredMoment (dim n) l (M n).bf (M n).hf (finiteCutMasses us j)
        (w n).star.val (orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val) ≤
          (((dim n+1:ℕ):ℝ)^(-saving)*W n)^(2*l)

theorem actual_native_star_final_net_to_finite_degrees_along
    {m delta cl cu Az C0 Ct D Bclock saving : ℝ}
    (A : ℕ) (hA : 0 < A)
    {dim : ℕ → ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW : ∀n,0 ≤ W n) (w : ℕ→ActualSlowWindowChoice)
    (H : ActualNativeStarMomentOnEveryFinalNetAlong (A-1) saving M W w) :
    ActualNativeStarFiniteDegreeOnEveryFinalNetAlong A saving M W w := by
  have horder : A-1+1=A := by omega
  unfold ActualNativeStarMomentOnEveryFinalNetAlong at H
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

theorem actual_native_star_final_net_along_id
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (p : ℕ) (saving : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) :
    ActualNativeStarMomentOnEveryFinalNetAlong (dim:=id) p saving M W w ↔
      ActualNativeStarMomentOnEveryFinalNet p saving M W w := Iff.rfl

theorem actual_native_star_finite_degree_along_id
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (A : ℕ) (saving : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) :
    ActualNativeStarFiniteDegreeOnEveryFinalNetAlong (dim:=id) A saving M W w ↔
      ActualNativeStarFiniteDegreeOnEveryFinalNet A saving M W w := Iff.rfl

end OAI.SKFluctuations.LaplaceWindowFormalization
