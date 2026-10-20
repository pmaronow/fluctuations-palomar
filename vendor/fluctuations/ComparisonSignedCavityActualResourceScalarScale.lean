module

public import ComparisonSignedCavityActualFrozenResourceMoments
public import ComparisonSignedCavityActualResourceHistories

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open Set Filter MeasureTheory ProbabilityTheory Cavity
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
variable {S ι : Type} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
variable {as : List PositiveMass}

theorem actual_resource_raw_scale_pos (rs : List NativeResourceMark)
    {x W : ℝ} (hx : 0 < x) (hW : 0 < W) : 0 < nativeResourceScale x W 1 rs := by
  induction rs with
  | nil=>simp [nativeResourceScale]
  | cons m rs ih=>
    change 0 < m.savedScale x W 1*nativeResourceScale x W 1 rs
    exact mul_pos (m.savedScale_pos hx hW zero_lt_one) ih

theorem actual_resource_scale_le_raw (rs : List NativeResourceMark)
    {x W ε : ℝ} (hx : 0 < x) (hW : 0 < W) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    nativeResourceScale x W ε rs ≤ nativeResourceScale x W 1 rs := by
  induction rs with
  | nil=>rfl
  | cons m rs ih=>
    change m.savedScale x W ε*nativeResourceScale x W ε rs ≤
      m.savedScale x W 1*nativeResourceScale x W 1 rs
    have H : m.savedScale x W ε ≤ m.savedScale x W 1:=by
      cases m with
      | initial => exact le_rfl
      | oldStar => exact le_rfl
      | markedStar k =>
        simpa only [NativeResourceMark.savedScale,one_mul] using
          mul_le_mul_of_nonneg_right hε1 hW.le
    have hscale : 0 ≤ nativeResourceScale x W ε rs:=by
      have HE:=nativeResourceEnvelope_pos rs zero_lt_one hx hW hε
      simpa only [nativeResourceEnvelope_scale,one_pow,one_mul] using HE.le
    exact mul_le_mul H ih hscale (m.savedScale_pos hx hW zero_lt_one).le

theorem NativeActualResourceGenerated.normalized_original_scalar_times_live_raw_scale_le
    {i star U k degree : ℕ} {seed : List NativeResourceMark}
    {T : ClockTree S as} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P)
    (hdepth : seed.length+k ≤ degree) {w : S→ℝ} (hw : ∀σ,0 < w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (ho : MassOrdered 0 as)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (x₀ : ι→ℝ) (R : S→S→ℝ) (C : ℕ→ℝ)
    (A x W ε : ℝ) (hA : 1 ≤ A) (hx : 0 < x) (hW : 0 < W) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hi : i  ≤  star) (hstar : star  <  as.length)
    (hm : P.PairMomentBudget w φ v q R C x₀ A x W ε) :
    |(W⁻¹)^k*P.scalar w φ v q R C x₀| *nativeResourceScale x W 1 P.live.tags ≤
      |P.coefficient| *A^degree*nativeResourceScale x W 1 seed := by
  let Fs:=P.frozen.flatMap (fun F=>F.monomial.tags)
  have HA : 0 < A:=zero_lt_one.trans_le hA
  have HF:=frozen_resource_original_product_abs_le P.frozen hw φ ho v q R C x₀
    A x W ε HA hx hW hε hi hstar hm.2
  rw [nativeResourceEnvelope_scale] at HF
  have Hraw:=actual_resource_scale_le_raw Fs hx hW hε hε1
  have Hscalar : |P.scalar w φ v q R C x₀| ≤ |P.coefficient| *(A^Fs.length*nativeResourceScale x W 1 Fs):=by
    have H0:=HF.trans (mul_le_mul_of_nonneg_left Hraw (pow_nonneg HA.le _))
    simpa only [NativeResourceTerm.scalar,Fs,abs_mul] using
      mul_le_mul_of_nonneg_left H0 (abs_nonneg P.coefficient)
  have Hlen : Fs.length ≤ degree:=by
    have H:=hP.total_factor_depth
    simp only [NativeResourceTerm.resources,List.length_append] at H
    dsimp only [Fs]
    omega
  have HPow:=pow_le_pow_right₀ hA Hlen
  have hLive : 0 ≤ nativeResourceScale x W 1 P.live.tags:=(actual_resource_raw_scale_pos _ hx hW).le
  have hFrozen : 0 ≤ nativeResourceScale x W 1 Fs:=(actual_resource_raw_scale_pos _ hx hW).le
  have Hscalar' : |P.scalar w φ v q R C x₀| ≤ |P.coefficient| *(A^degree*nativeResourceScale x W 1 Fs):=
    Hscalar.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right HPow hFrozen) (abs_nonneg P.coefficient))
  have H:=mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right Hscalar' hLive)
    (pow_nonneg (inv_nonneg.mpr hW.le) k)
  have Hscale : nativeResourceScale x W 1 P.live.tags*nativeResourceScale x W 1 Fs=
      nativeResourceScale x W 1 seed*W^k:=by
    calc
      nativeResourceScale x W 1 P.live.tags*nativeResourceScale x W 1 Fs=
        nativeResourceScale x W 1 Fs*nativeResourceScale x W 1 P.live.tags:=mul_comm _ _
      _=nativeResourceScale x W 1 seed*W^k:=by
        have H:=hP.saved_scale x W 1
        simpa only [NativeResourceTerm.resources,Fs,nativeResourceScale,List.map_append,
          List.prod_append,one_mul] using H
  have hcancel : (W⁻¹)^k*W^k=1:=by rw [←mul_pow,inv_mul_cancel₀ hW.ne',one_pow]
  rw [abs_mul,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hW.le) k)]
  calc
    (W⁻¹)^k*|P.scalar w φ v q R C x₀| *nativeResourceScale x W 1 P.live.tags ≤
      (W⁻¹)^k*(|P.coefficient| *(A^degree*nativeResourceScale x W 1 Fs)*nativeResourceScale x W 1 P.live.tags):=by
        simpa only [mul_assoc] using H
    _=|P.coefficient| *A^degree*nativeResourceScale x W 1 seed:=by
      calc
        _=|P.coefficient| *A^degree*(W⁻¹)^k*
          (nativeResourceScale x W 1 P.live.tags*nativeResourceScale x W 1 Fs):=by ring
        _=|P.coefficient| *A^degree*nativeResourceScale x W 1 seed*((W⁻¹)^k*W^k):=by rw [Hscale];ring
        _= _:=by rw [hcancel,mul_one]

end OAI.SKFluctuations.Hierarchy.ClockTree
