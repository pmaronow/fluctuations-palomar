module

public import SKProof.Port.ComparisonActualOriginalQVirtualControl
public import SKProof.Port.ComparisonActualOriginalQClocks
public import ComparisonHighStrengthIdentification
public import SKProof.Port.OriginalQHighOnlyBridge

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000
namespace ActualThetaZeroOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_high_flat_radius_gradient_closure {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Gamma : ℝ→ℝ) (T : ℝ) (hT : 0 < T) {t : ℝ}
    (hrad : M.xs*t∈Icc M.data.rmin 1)
    (hflat : laplaceComparisonStrength M.data.d M.lam (M.xs*t)=M.lam)
    (hderiv : HasDerivAt (laplaceComparisonStrength M.data.d M.lam) 0 (M.xs*t)) :
    let u := M.alpha.val.val (M.xs*t)
    let S := orderedPathS (n+1) M.sweepBf M.sweepHf u
    let K := actualMixedClock (n+1) M.sweepBf M.sweepHf u
    K=comparisonNativeScalarClock (M.h u) (M.b u) M.lam (M.xs*t) S ∧
      M.actualVirtualScaledGradient t =
        -2*T*(comparisonRescaledScalarResponse Gamma T M.xs (K/(T*M.xs))+
          (S-Gamma K)/M.xs^3)-2*((M.b u-T)*S+M.h u)/M.xs^3 := by
  intro u S K
  have hinv := M.sweepRadius_inverse hrad

  change M.sweepRadius (M.alpha.val.val (M.xs*t))=M.xs*t at hinv
  have hK : K=comparisonNativeScalarClock (M.h u) (M.b u) M.lam (M.xs*t) S := by
    have H := M.inherited_mixed_clock_eq_nativeScalarClock (M.alpha.val.property.1 (M.xs*t))
    have hmass:M.data.s≤u:=by
      have HH:=M.alpha.val.property.2 hrad.1
      rw [M.alpha.property.1] at HH
      exact HH
    have he:M.sweepCoefficient u=laplaceComparisonStrength M.data.d M.lam (M.sweepRadius u):=by
      change omittedStrengthCoefficient M.data.d M.data.s M.sweepRadius M.lam u=_
      rw [omittedStrengthCoefficient,ite_eq_left hmass]
    rw [he,hinv,hflat] at H
    exact H
  refine ⟨hK,?_⟩
  have hP : comparisonRescaledScalarResponse Gamma T M.xs (K/(T*M.xs))=
      (Gamma K-K/T)/M.xs^3 := by
    have harg : T*M.xs*(K/(T*M.xs))=K := by field_simp [hT.ne',M.hxs.ne']
    have harg' : M.xs*(K/(T*M.xs))=K/T := by field_simp [hT.ne',M.hxs.ne']
    simp only [comparisonRescaledScalarResponse,harg,harg']
  have H := comparison_constant_strength_gradient_exact Gamma M.alpha.val.val
    (orderedPathS (n+1) M.sweepBf M.sweepHf) (orderedPathB (n+1) M.sweepBf M.sweepHf)
    (h0:=M.h u) (b0:=M.b u) (e:=M.lam) (r:=M.xs*t) hT.ne' M.hxs.ne'
  change radiusComparisonGradient (fun _=>M.lam) M.alpha.val.val
      (orderedPathS (n+1) M.sweepBf M.sweepHf) (orderedPathB (n+1) M.sweepBf M.sweepHf) (M.xs*t)/M.xs^3 =
    -2*T*((Gamma (comparisonNativeScalarClock (M.h u) (M.b u) M.lam (M.xs*t) S)-
      comparisonNativeScalarClock (M.h u) (M.b u) M.lam (M.xs*t) S/T)/M.xs^3+
      (S-Gamma (comparisonNativeScalarClock (M.h u) (M.b u) M.lam (M.xs*t) S))/M.xs^3)-
      2*((M.b u-T)*S+M.h u)/M.xs^3 at H
  rw [←hK] at H
  rw [hP]
  unfold actualVirtualScaledGradient
  rw [comparison_flat_native_gradient M.alpha.val.val (orderedPathS (n+1) M.sweepBf M.sweepHf)
    (orderedPathB (n+1) M.sweepBf M.sweepHf) hflat hderiv]
  exact H

theorem eventually_actual_high_flat_radius_gradient_closure
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (Gamma : ℕ→ℝ→ℝ) (T : ℝ) (hT : 0 < T) :
    ∀ᶠn in atTop,∀t∈Icc (max a ((M n).data.rmin/(M n).xs)) b,
      let u := (M n).alpha.val.val ((M n).xs*t)
      let S := orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u
      let K := actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf u
      K=comparisonNativeScalarClock ((M n).h u) ((M n).b u) (M n).lam ((M n).xs*t) S ∧
        (M n).actualVirtualScaledGradient t =
          -2*T*(comparisonRescaledScalarResponse (Gamma n) T (M n).xs (K/(T*(M n).xs))+
            (S-Gamma n K)/(M n).xs^3)-2*(((M n).b u-T)*S+(M n).h u)/(M n).xs^3 := by
  have Hflat := comparison_strength_eventually_flat_of_divergence
    (fun n=>(M n).data.d) (fun n=>(M n).lam) (fun n=>(M n).xs)
    (Eventually.of_forall (fun n=>⟨(M n).data.hd,(M n).hlam,(M n).hxs,(M n).hld⟩))
    hlarge (ha.trans_lt hab)
  have Hsmall : ∀ᶠn in atTop,(M n).xs*b ≤ 1 := by
    have H : Tendsto (fun n=>(M n).xs*b) atTop (𝓝 0) := by
      simpa only [zero_mul] using hxs.mul_const b
    exact H.eventually (eventually_le_nhds zero_lt_one)
  filter_upwards [Hflat,Hsmall] with n hn hs t ht
  have hta : a ≤ t := (le_max_left _ _).trans ht.1
  have ht0 : 0 ≤ t := ha.trans hta
  have hphysical : (M n).data.rmin ≤ (M n).xs*t := by
    have H := (div_le_iff₀ (M n).hxs).mp ((le_max_right _ _).trans ht.1)
    simpa only [mul_comm] using H
  exact (M n).actual_high_flat_radius_gradient_closure (Gamma n) T hT
    ⟨hphysical,(mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans hs⟩
    (hn t ⟨ht0,ht.2⟩).1 (hn t ⟨ht0,ht.2⟩).2.2

theorem eventually_actual_high_flat_radius_gradient_closure_of_origin_small
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (horigin : Tendsto (fun n=>(M n).data.rmin/(M n).xs) atTop (𝓝 0))
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (Gamma : ℕ→ℝ→ℝ) (T : ℝ) (hT : 0 < T) :
    ∀ᶠn in atTop,∀t∈Icc a b,
      let u := (M n).alpha.val.val ((M n).xs*t)
      let S := orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u
      let K := actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf u
      K=comparisonNativeScalarClock ((M n).h u) ((M n).b u) (M n).lam ((M n).xs*t) S ∧
        (M n).actualVirtualScaledGradient t =
          -2*T*(comparisonRescaledScalarResponse (Gamma n) T (M n).xs (K/(T*(M n).xs))+
            (S-Gamma n K)/(M n).xs^3)-2*(((M n).b u-T)*S+(M n).h u)/(M n).xs^3 := by
  have Hclosure := eventually_actual_high_flat_radius_gradient_closure
    dim M hxs hlarge a b ha.le hab Gamma T hT
  filter_upwards [Hclosure,horigin.eventually (eventually_le_nhds ha)] with n hn ho t ht
  exact hn t ⟨max_le ht.1 (ho.trans ht.1),ht.2⟩

theorem eventually_actual_high_flat_radius_gradient_closure_above_mass
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (homission : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (c : ℝ) (hc : 0 < c)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (Gamma : ℕ→ℝ→ℝ) (T : ℝ) (hT : 0 < T) :
    ∀ᶠn in atTop,∀t∈Icc a b,
      c*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*t) →
      let u := (M n).alpha.val.val ((M n).xs*t)
      let S := orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u
      let K := actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf u
      K=comparisonNativeScalarClock ((M n).h u) ((M n).b u) (M n).lam ((M n).xs*t) S ∧
        (M n).actualVirtualScaledGradient t =
          -2*T*(comparisonRescaledScalarResponse (Gamma n) T (M n).xs (K/(T*(M n).xs))+
            (S-Gamma n K)/(M n).xs^3)-2*(((M n).b u-T)*S+(M n).h u)/(M n).xs^3 := by
  have Hclosure := eventually_actual_high_flat_radius_gradient_closure
    dim M hxs hlarge a b ha hab Gamma T hT
  filter_upwards [Hclosure,homission.eventually (eventually_lt_nhds hc)] with n hn ho t ht hm
  have hs : (M n).data.s < c*(M n).xs := (div_lt_iff₀ (M n).hxs).mp ho
  have hphysical : (M n).data.rmin ≤ (M n).xs*t := by
    by_contra h
    have H := (M n).alpha.val.property.2 (le_of_not_ge h)
    rw [(M n).alpha.property.1] at H
    exact (hs.trans_le (hm.trans H)).false
  have hscaled : (M n).data.rmin/(M n).xs ≤ t := by
    apply (div_le_iff₀ (M n).hxs).mpr
    simpa only [mul_comm] using hphysical
  exact hn t ⟨max_le ht.1 hscaled,ht.2⟩

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
