module

public import ComparisonNativeNumericScaledGradientBound
public import ComparisonScaledStrengthDerivativeBound
public import ComparisonNativeActualMeanRawUpper

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 20000000

 theorem eventually_actual_bounded_strength_gradient_uniform_along
    {m delta cl cu Az C0 Ct D Bclock Ccal : ℝ}
    (K B C : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/(M n).xs^2 ≤ K) :
    ∃Cg : ℝ,0 < Cg ∧ ∀ᶠn in atTop,∀t∈Icc (0:ℝ) B,
      (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs →
        |(M n).actualVirtualScaledGradient t| ≤ Cg := by
  have hCp : 0 < Ccal:=zero_lt_one.trans_le hCcal
  obtain ⟨Dder,hDder,HDder⟩:=exists_comparison_strength_scaled_derivative_bound Ccal B K hCp.le hB hK
  obtain ⟨Kb,hKb,HB⟩:=eventually_native_comparison_B_normalized (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Ks,hKs,HS⟩:=eventually_actual_minimum_mass_mean_upper (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cs:=Ks*(1+C)
  let Cq:=Kb*(1+C)^2
  have hCs : 0 ≤ Cs:=by dsimp only [Cs];positivity
  have hCq : 0 ≤ Cq:=by dsimp only [Cq];positivity
  let Cg:=Dder*(Cq+2*B*Cs+B^2)+2*(K+1)*(B+Cs)+1
  have hCg : 0 < Cg:=by dsimp only [Cg];positivity
  refine ⟨Cg,hCg,?_⟩
  have Hphysical : ∀ᶠn in atTop,(M n).xs*B ≤ 1:=by
    have H:=(hxlim.mul_const B).eventually (eventually_le_nhds (by simp : (0:ℝ)*B<1))
    simpa only [zero_mul] using H
  filter_upwards [hwork,((tendsto_add_atTop_nat 1).comp hdim).eventually HB,
    hdim.eventually HS,Hphysical] with n hnwork hnB hnS hnphysical
  intro t ht huC
  let u:=(M n).alpha.val.val ((M n).xs*t)
  have hu : u∈Icc (0:ℝ) 1:=(M n).alpha.val.property.1 ((M n).xs*t)
  have hr : (M n).xs*t∈Icc (0:ℝ) 1:=
    ⟨mul_nonneg (M n).hxs.le ht.1,(mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans hnphysical⟩
  have Hmom:=comparisonVariableEndpoint_radius_moments (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).context.hm (M n).context.hM (dim n+1) (by omega)
    (M n).b (M n).h (M n).context.hd.ne' (M n).hlam.le (M n).hlb
    (M n).hb (M n).hh (M n).hh0 (M n).alpha
  have hS0 : 0 ≤ orderedPathS (dim n+1) (M n).bf (M n).hf u:=(M n).mass_mean_nonneg hu
  have hQ0 : 0 ≤ orderedPathB (dim n+1) (M n).bf (M n).hf u:=
    (sq_nonneg _).trans ((Hmom.2.2 _ hr).2.1)
  have hSu : orderedPathS (dim n+1) (M n).bf (M n).hf u ≤ Cs*(M n).xs:=by
    by_cases hu0 : u=0
    · simp only [hu0,orderedPathS,orderedPathPair_zero]
      exact mul_nonneg hCs (M n).hxs.le
    · have H:=hnS (M n) u ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),hu.2⟩
      have Hx:=(mul_le_mul_of_nonneg_left (show (M n).xs+u ≤ (1+C)*(M n).xs by linarith only [huC]) hKs.le)
      exact H.trans (by dsimp only [Cs];nlinarith only [Hx])
  have hQu : orderedPathB (dim n+1) (M n).bf (M n).hf u ≤ Cq*(M n).xs^2:=by
    by_cases hu0 : u=0
    · simp only [hu0,orderedPathB,orderedPathPair_zero]
      exact mul_nonneg hCq (sq_nonneg _)
    · have H:=hnB (M n) u ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),hu.2⟩
      dsimp only [Function.comp_def] at H
      have HH:=pow_le_pow_left₀ (add_nonneg (M n).hxs.le hu.1)
        (show (M n).xs+u ≤ (1+C)*(M n).xs by linarith only [huC]) 2
      apply H.trans
      convert mul_le_mul_of_nonneg_left HH hKb.le using 1
      dsimp only [Cq];ring
  have hxd : (M n).xs ≤ Ccal*(M n).context.d:=by
    apply (sq_le_sq₀ (M n).hxs.le (mul_nonneg hCp.le (M n).context.hd.le)).mp
    have H:=(hcompare n).trans (mul_le_mul_of_nonneg_left
      ((laplaceComparisonStrength_le (M n).context.d (M n).hlam.le (M n).xs).trans (M n).hld) (sq_nonneg Ccal))
    nlinarith only [H]
  have hlamnorm:=comparison_zero_strength_bound_of_working (M n).context.hd (M n).hlam.le
    (M n).hxs (M n).hld hK hnwork
  have HE:=comparison_strength_uniform_bound_of_working (M n).context.hd (M n).hlam.le
    (M n).hxs (M n).hld hK hnwork ((M n).xs*t)
  have HD:=HDder (M n).context.d (M n).lam (M n).xs t (M n).context.hd (M n).hlam.le
    (M n).hxs (M n).hld hxd hlamnorm ht
  have hdscaled : |deriv (laplaceComparisonStrength (M n).context.d (M n).lam) ((M n).xs*t)/(M n).xs| ≤ Dder:=by
    rw [abs_div,abs_of_pos (M n).hxs]
    exact (div_le_iff₀ (M n).hxs).mpr HD
  have hescaled : |laplaceComparisonStrength (M n).context.d (M n).lam ((M n).xs*t)/(M n).xs^2| ≤ K+1:=by
    rw [abs_of_nonneg HE.1];exact HE.2
  have hsscaled : |orderedPathS (dim n+1) (M n).bf (M n).hf u/(M n).xs| ≤ Cs:=by
    rw [abs_div,abs_of_nonneg hS0,abs_of_pos (M n).hxs]
    exact (div_le_iff₀ (M n).hxs).mpr hSu
  have hqscaled : |orderedPathB (dim n+1) (M n).bf (M n).hf u/(M n).xs^2| ≤ Cq:=by
    rw [abs_div,abs_of_nonneg hQ0,abs_of_pos (sq_pos_of_pos (M n).hxs)]
    exact (div_le_iff₀ (sq_pos_of_pos (M n).hxs)).mpr hQu
  have Hid : (M n).actualVirtualScaledGradient t=
      (deriv (laplaceComparisonStrength (M n).context.d (M n).lam) ((M n).xs*t)/(M n).xs)*
        (orderedPathB (dim n+1) (M n).bf (M n).hf u/(M n).xs^2-
          2*t*(orderedPathS (dim n+1) (M n).bf (M n).hf u/(M n).xs)+t^2)+
        2*(laplaceComparisonStrength (M n).context.d (M n).lam ((M n).xs*t)/(M n).xs^2)*
          (t-orderedPathS (dim n+1) (M n).bf (M n).hf u/(M n).xs):=by
    dsimp only [actualVirtualScaledGradient,radiusComparisonGradient,u]
    field_simp [(M n).hxs.ne'];ring
  rw [Hid]
  apply (native_numeric_scaled_gradient_bound (by linarith only [hK]) hDder hCs hCq hB
    hescaled hdscaled hsscaled hqscaled (by rw [abs_of_nonneg ht.1];exact ht.2)).trans
  dsimp only [Cg]
  linarith

theorem eventually_actual_bounded_strength_gradient_uniform_on_band_along
    {m delta cl cu Az C0 Ct D Bclock Ccal : ℝ}
    (K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/(M n).xs^2 ≤ K) :
    ∃Cg : ℝ,0 < Cg ∧ ∀ᶠn in atTop,∀t∈Icc (0:ℝ) B,
      |(M n).actualVirtualScaledGradient t| ≤ Cg := by
  let C:=cu*(B+Az)
  have hC : 0 ≤ C:=mul_nonneg hcu.le (add_nonneg hB hAz)
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_bounded_strength_gradient_uniform_along
    K B C hK hB hC hm hdelta hroom hcl hcu hAz hC0 hCt hCcal dim hdim M hxlim hcompare hwork
  have Hphysical : ∀ᶠn in atTop,(M n).xs*B ≤ 1:=by
    have H:=(hxlim.mul_const B).eventually (eventually_le_nhds (by simp : (0:ℝ)*B<1))
    simpa only [zero_mul] using H
  refine ⟨Cg,hCg,?_⟩
  filter_upwards [HG,Hphysical] with n hn hnphysical
  intro t ht
  apply hn t ht
  have har : (M n).alpha.val.val ((M n).xs*t) ≤
      cu*max (M n).z ((M n).xs*t) :=
    ((M n).alpha.val.property.2 (le_max_right _ _)).trans
      (((M n).regular _ ⟨le_max_left _ _,max_le (M n).hz.2
        ((mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans hnphysical)⟩).2)
  have hz : max (M n).z ((M n).xs*t) ≤ (B+Az)*(M n).xs:=by
    apply max_le
    · nlinarith only [(M n).hzxs,mul_nonneg hB (M n).hxs.le]
    · nlinarith only [mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le,mul_nonneg hAz (M n).hxs.le]
  exact har.trans ((mul_le_mul_of_nonneg_left hz hcu.le).trans_eq (by dsimp only [C];ring))

end OAI.SKFluctuations.LaplaceWindowFormalization
