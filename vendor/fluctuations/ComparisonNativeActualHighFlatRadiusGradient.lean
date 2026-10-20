module

public import ComparisonNativeActualVirtualControl
public import ComparisonNativeActualInheritedClocks
public import ComparisonHighStrengthIdentification

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_high_flat_radius_gradient_closure {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Gamma : ℝ→ℝ) (T : ℝ) (hT : 0 < T) {t : ℝ}
    (hrad : M.xs*t∈Icc (0:ℝ) 1)
    (hflat : laplaceComparisonStrength M.context.d M.lam (M.xs*t)=M.lam)
    (hderiv : HasDerivAt (laplaceComparisonStrength M.context.d M.lam) 0 (M.xs*t)) :
    let u := M.alpha.val.val (M.xs*t)
    let S := orderedPathS (n+1) M.bf M.hf u
    let K := actualMixedClock (n+1) M.bf M.hf u
    K=comparisonNativeScalarClock (M.h u) (M.b u) M.lam (M.xs*t) S ∧
      M.actualVirtualScaledGradient t =
        -2*T*(comparisonRescaledScalarResponse Gamma T M.xs (K/(T*M.xs))+
          (S-Gamma K)/M.xs^3)-2*((M.b u-T)*S+M.h u)/M.xs^3 := by
  intro u S K
  have hinv := comparisonSweepQuantile_inverse M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha hrad
  change M.R (M.alpha.val.val (M.xs*t))=M.xs*t at hinv
  have hK : K=comparisonNativeScalarClock (M.h u) (M.b u) M.lam (M.xs*t) S := by
    have H := M.inherited_mixed_clock_eq_nativeScalarClock (M.alpha.val.property.1 (M.xs*t))
    rw [hinv,hflat] at H
    exact H
  refine ⟨hK,?_⟩
  have hP : comparisonRescaledScalarResponse Gamma T M.xs (K/(T*M.xs))=
      (Gamma K-K/T)/M.xs^3 := by
    have harg : T*M.xs*(K/(T*M.xs))=K := by field_simp [hT.ne',M.hxs.ne']
    have harg' : M.xs*(K/(T*M.xs))=K/T := by field_simp [hT.ne',M.hxs.ne']
    simp only [comparisonRescaledScalarResponse,harg,harg']
  have H := comparison_constant_strength_gradient_exact Gamma M.alpha.val.val
    (orderedPathS (n+1) M.bf M.hf) (orderedPathB (n+1) M.bf M.hf)
    (h0:=M.h u) (b0:=M.b u) (e:=M.lam) (r:=M.xs*t) hT.ne' M.hxs.ne'
  change radiusComparisonGradient (fun _=>M.lam) M.alpha.val.val
      (orderedPathS (n+1) M.bf M.hf) (orderedPathB (n+1) M.bf M.hf) (M.xs*t)/M.xs^3 =
    -2*T*((Gamma (comparisonNativeScalarClock (M.h u) (M.b u) M.lam (M.xs*t) S)-
      comparisonNativeScalarClock (M.h u) (M.b u) M.lam (M.xs*t) S/T)/M.xs^3+
      (S-Gamma (comparisonNativeScalarClock (M.h u) (M.b u) M.lam (M.xs*t) S))/M.xs^3)-
      2*((M.b u-T)*S+M.h u)/M.xs^3 at H
  rw [←hK] at H
  rw [hP]
  unfold actualVirtualScaledGradient
  rw [comparison_flat_native_gradient M.alpha.val.val (orderedPathS (n+1) M.bf M.hf)
    (orderedPathB (n+1) M.bf M.hf) hflat hderiv]
  exact H

theorem eventually_actual_high_flat_radius_gradient_closure
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (Gamma : ℕ→ℝ→ℝ) (T : ℝ) (hT : 0 < T) :
    ∀ᶠn in atTop,∀t∈Icc a b,
      let u := (M n).alpha.val.val ((M n).xs*t)
      let S := orderedPathS (dim n+1) (M n).bf (M n).hf u
      let K := actualMixedClock (dim n+1) (M n).bf (M n).hf u
      K=comparisonNativeScalarClock ((M n).h u) ((M n).b u) (M n).lam ((M n).xs*t) S ∧
        (M n).actualVirtualScaledGradient t =
          -2*T*(comparisonRescaledScalarResponse (Gamma n) T (M n).xs (K/(T*(M n).xs))+
            (S-Gamma n K)/(M n).xs^3)-2*(((M n).b u-T)*S+(M n).h u)/(M n).xs^3 := by
  have Hflat := comparison_strength_eventually_flat_of_divergence
    (fun n=>(M n).context.d) (fun n=>(M n).lam) (fun n=>(M n).xs)
    (Eventually.of_forall (fun n=>⟨(M n).context.hd,(M n).hlam,(M n).hxs,(M n).hld⟩))
    hlarge (ha.trans_lt hab)
  have Hsmall : ∀ᶠn in atTop,(M n).xs*b ≤ 1 := by
    have H : Tendsto (fun n=>(M n).xs*b) atTop (𝓝 0) := by
      simpa only [zero_mul] using hxs.mul_const b
    exact H.eventually (eventually_le_nhds zero_lt_one)
  filter_upwards [Hflat,Hsmall] with n hn hs t ht
  have ht0 : 0 ≤ t := ha.trans ht.1
  exact (M n).actual_high_flat_radius_gradient_closure (Gamma n) T hT
    ⟨mul_nonneg (M n).hxs.le ht0,(mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans hs⟩
    (hn t ⟨ht0,ht.2⟩).1 (hn t ⟨ht0,ht.2⟩).2.2

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
