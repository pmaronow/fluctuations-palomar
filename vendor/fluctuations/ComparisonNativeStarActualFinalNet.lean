module

public import ComparisonNativeStarActualFiniteDegrees

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 5000000

def ActualNativeStarMomentOnEveryFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (p : ℕ) (saving : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,
    ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) → (w n).star∈us →
    ∀ᶠj : ℕ in atTop,
      nativeRetainedCenteredMoment n (p+1) (M n).bf (M n).hf (finiteCutMasses us j)
        (w n).star.val (orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val) ≤
          (((n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1))

theorem actual_native_star_order_saving_on_every_final_net
    {m delta cl cu Az C0 Ct D Bclock Craw saving : ℝ}
    (p : ℕ) (hsaving : 0 < saving)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW : ∀n,0 < W n) (w : ℕ→ActualSlowWindowChoice)
    (H : ActualNativeStarOrderSaving p Craw saving M W w) :
    ActualNativeStarMomentOnEveryFinalNet p (saving/2) M W w := by
  filter_upwards [H,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro us hus hstar
  have hWn := hW n
  have hN : 1 < ((n+1:ℕ):ℝ) := by exact_mod_cast (by omega : 1 < n+1)
  let S := orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val
  let P : Spin (n+1) → Spin (n+1) → ℝ := fun σ τ=>|orderedOverlap (n+1) σ τ-S|^(2*(p+1))
  have had := comparisonVariableEndpoint_clocks_admissible (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).context.hm (M n).context.hM (M n).b (M n).h
    (M n).context.hd.ne' (M n).hlam.le (M n).hlb (M n).hb (M n).hh (M n).hh0 (M n).alpha
  have hbf := toNNReal_monotoneOn had.1
  have hhf := toNNReal_monotoneOn had.2.1
  obtain ⟨source,hsource,_,hstarsource,Hsource⟩ := hn [] (by simp)
  have HsourceLimit := nativeRetainedPairValue_tendsto n (M n).bf (M n).hf hbf hhf
    source hsource (w n).star hstarsource P
  have HsourceBound : ∀ᶠj : ℕ in atTop,
      nativeRetainedPairValue n (M n).bf (M n).hf (finiteCutMasses source j) (w n).star.val P ≤
        (((n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1)) := by
    filter_upwards [Hsource] with j hj
    exact hj.2
  have Horiginal : orderedPathPair (n+1) (M n).bf (M n).hf P (w n).star.val ≤
      (((n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1)) :=
    le_of_tendsto HsourceLimit HsourceBound
  have Hstrict : (((n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1)) <
      (((n+1:ℕ):ℝ)^(-(saving/2))*W n)^(2*(p+1)) := by
    apply pow_lt_pow_left₀
      (mul_lt_mul_of_pos_right (Real.rpow_lt_rpow_of_exponent_lt hN (by linarith)) hWn)
      (by positivity)
    omega
  have HfinalLimit := nativeRetainedPairValue_tendsto n (M n).bf (M n).hf hbf hhf
    us hus (w n).star hstar P
  have Hfinal := HfinalLimit.eventually (gt_mem_nhds (Horiginal.trans_lt Hstrict))
  filter_upwards [Hfinal] with j hj
  exact hj.le

def ActualNativeStarFiniteDegreeOnEveryFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (A : ℕ) (saving : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,
    ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) → (w n).star∈us →
    ∀ᶠj : ℕ in atTop,∀l : ℕ,0 < l → l ≤ A →
      nativeRetainedCenteredMoment n l (M n).bf (M n).hf (finiteCutMasses us j)
        (w n).star.val (orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val) ≤
          (((n+1:ℕ):ℝ)^(-saving)*W n)^(2*l)

theorem actual_native_star_final_net_to_finite_degrees
    {m delta cl cu Az C0 Ct D Bclock saving : ℝ}
    (A : ℕ) (hA : 0 < A)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW : ∀n,0 ≤ W n) (w : ℕ→ActualSlowWindowChoice)
    (H : ActualNativeStarMomentOnEveryFinalNet (A-1) saving M W w) :
    ActualNativeStarFiniteDegreeOnEveryFinalNet A saving M W w := by
  have horder : A-1+1=A := by omega
  unfold ActualNativeStarMomentOnEveryFinalNet at H
  simp only [horder] at H
  filter_upwards [H] with n hn
  intro us hus hstar
  filter_upwards [hn us hus hstar] with j hj
  intro l hl hlA
  exact nativeRetainedCenteredMoment_lower_order n l A hl hlA (M n).bf (M n).hf
    (finiteCutMasses us j) (finiteCutMasses_ordered us hus j) (w n).star.val
    (orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val)
    (((n+1:ℕ):ℝ)^(-saving)*W n)
    (mul_nonneg (Real.rpow_nonneg (by positivity) _) (hW n)) hj

theorem exists_actual_bare_native_star_on_every_final_net
    {m delta cl cu Az C0 Ct D Bclock T L Ccal : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hT : 0 < T) (hL : 0 < L) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ)
    (hcanonical : ∀n,W n=max (M n).xs
      (Real.sqrt (laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)))
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hb : ∀n u,(M n).b u=T) (hh : ∀n u,(M n).h u=0) :
    let saving := actualSlowWindowExponent m delta/128
    0 < saving ∧ ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn : ℕ in atTop,IsActualCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
      (∀p : ℕ,ActualNativeStarMomentOnEveryFinalNet p saving M W w) ∧
      ∀A : ℕ,0 < A → ActualNativeStarFiniteDegreeOnEveryFinalNet A saving M W w := by
  obtain ⟨hs,Cs,hCs,w,hw,H⟩ := exists_actual_bare_native_star_all_orders
    hm hdelta hroom hcl hcu hAz hC0 hCt hT hL hCcal M W hcanonical hWlim hcompare hb hh
  have hW n : 0 < W n := by
    rw [hcanonical]
    exact (M n).hxs.trans_le (le_max_left _ _)
  have Hfinal (p : ℕ) : ActualNativeStarMomentOnEveryFinalNet p
      (actualSlowWindowExponent m delta/128) M W w := by
    obtain ⟨Craw,_,Horder⟩ := H p
    have HG := actual_native_star_order_saving_on_every_final_net p hs M W hW w Horder
    simpa only [show (actualSlowWindowExponent m delta/64)/2=
      actualSlowWindowExponent m delta/128 by ring] using HG
  refine ⟨by linarith,Cs,hCs,w,hw,Hfinal,?_⟩
  intro A hA
  exact actual_native_star_final_net_to_finite_degrees A hA M W (fun n=>(hW n).le) w (Hfinal (A-1))

end OAI.SKFluctuations.LaplaceWindowFormalization
