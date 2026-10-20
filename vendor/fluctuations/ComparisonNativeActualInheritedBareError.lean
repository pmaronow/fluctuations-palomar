module

public import ComparisonNativeActualInheritedCalibration
public import ComparisonOriginalMassCauchy

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 7000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem inherited_bare_residual_integrable {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (mu : Measure ParisiFinite.OrderPoint) [IsFiniteMeasure mu] (x : ℝ) :
    Integrable (fun w : ParisiFinite.OrderPoint=>
      (((M.b w-T)*orderedPathS (n+1) M.bf M.hf w+M.h w)/x^3)) mu := by
  have hbm : Measurable (fun w : ParisiFinite.OrderPoint=>M.b w) :=
    (show Monotone (fun w : ParisiFinite.OrderPoint=>M.b w) from
      fun u v huv=>M.hb u.property v.property huv).measurable
  have hhm : Measurable (fun w : ParisiFinite.OrderPoint=>M.h w) :=
    (show Monotone (fun w : ParisiFinite.OrderPoint=>M.h w) from
      fun u v huv=>M.hh u.property v.property huv).measurable
  have hsm : Measurable (fun w : ParisiFinite.OrderPoint=>orderedPathS (n+1) M.bf M.hf w) :=
    (show Monotone (fun w : ParisiFinite.OrderPoint=>orderedPathS (n+1) M.bf M.hf w) from
      fun u v huv=>M.mass_mean_monotone u.property v.property huv).measurable
  have hmeas:=((hbm.sub_const T).mul hsm).add hhm
  have hi : Integrable (fun w : ParisiFinite.OrderPoint=>
      (M.b w-T)*orderedPathS (n+1) M.bf M.hf w+M.h w) mu := by
    apply (integrable_const (M.b 1+|T|+M.h 1)).mono' hmeas.aestronglyMeasurable
    filter_upwards [] with w
    have hb0 : 0 ≤ M.b w := (M.hlam.le.trans M.hlb).trans (M.hb (by norm_num) w.property w.property.1)
    have hb1 : M.b w ≤ M.b 1 := M.hb w.property (by norm_num) w.property.2
    have hh0 : 0 ≤ M.h w := M.hh0.trans (M.hh (by norm_num) w.property w.property.1)
    have hh1 : M.h w ≤ M.h 1 := M.hh w.property (by norm_num) w.property.2
    have hs:=M.mass_mean_unit_bounds w.property
    have hbabs : |M.b w-T| ≤ M.b 1+|T| :=
      (abs_sub (M.b w) T).trans (by rw [abs_of_nonneg hb0];linarith)
    have hm:=mul_le_mul hbabs hs.2 hs.1 (by linarith [abs_nonneg T])
    have H:=abs_add_le ((M.b w-T)*orderedPathS (n+1) M.bf M.hf w) (M.h w)
    change |(M.b w-T)*orderedPathS (n+1) M.bf M.hf w+M.h w| ≤ _
    rw [abs_mul,abs_of_nonneg hs.1,abs_of_nonneg hh0] at H
    nlinarith only [H,hm,hh1]
  exact hi.div_const _

theorem actual_inherited_restricted_bare_error_tendsto_zero
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n : ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W epsilon : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n)
    (hepsilon : ∀n,0 ≤ epsilon n) (hepslim : Tendsto epsilon atTop (𝓝 0))
    (F : ℕ→Set ParisiFinite.OrderPoint) (hF : ∀n,MeasurableSet (F n))
    (C : ℝ) (hC : 0 < C) (hcut : ∀n w,w∈F n → (w:ℝ) ≤ C*W n)
    (hEq4 : ∀ᶠn in atTop,∀w∈F n,
      |(M n).b w-T| ≤ epsilon n*(W n)^2 ∧ |(M n).h w| ≤ epsilon n*(W n)^3) :
    let nu:=fun n=>ENNReal.ofReal (1/W n) •
      (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict (F n)
    (∀n,Integrable (fun w : ParisiFinite.OrderPoint=>
      (((M n).b w-T)*orderedPathS (n+1) (M n).bf (M n).hf w+(M n).h w)/(W n)^3) (nu n)) ∧
    Tendsto (fun n=>∫w : ParisiFinite.OrderPoint,
      |(((M n).b w-T)*orderedPathS (n+1) (M n).bf (M n).hf w+(M n).h w)/(W n)^3|
        ∂nu n) atTop (𝓝 0) := by
  dsimp only
  let mu:=fun n=>(uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict (F n)
  let nu:=fun n=>ENNReal.ofReal (1/W n) • mu n
  have (n : ℕ) : IsFiniteMeasure (nu n) := by
    constructor
    simp only [nu,Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hW n : 0 < W n := (M n).hxs.trans_le (hxs n)
  have hmass n : (mu n).real univ ≤ C*W n := by
    have hv : min (C*W n) 1∈Icc (0:ℝ) 1 :=
      ⟨le_min (mul_nonneg hC.le (hW n).le) zero_le_one,min_le_right _ _⟩
    have hsub : F n ⊆ {w : ParisiFinite.OrderPoint | (w:ℝ) ≤ min (C*W n) 1} :=
      fun w hw=>le_min (hcut n w hw) w.property.2
    change ((uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict (F n)).real univ ≤ _
    rw [measureReal_restrict_apply' (hF n),univ_inter]
    exact (measureReal_mono (μ:=(uniformOrderMass : Measure ParisiFinite.OrderPoint)) hsub).trans
      ((uniformOrderMass_atMost hv).le.trans (min_le_left _ _))
  have hnMass n : (nu n).real univ ≤ C := by
    change (ENNReal.ofReal (1/W n) • mu n).real univ ≤ C
    rw [measureReal_ennreal_smul_apply,ENNReal.toReal_ofReal (one_div_nonneg.mpr (hW n).le)]
    have H:=mul_le_mul_of_nonneg_left (hmass n) (one_div_nonneg.mpr (hW n).le)
    exact H.trans_eq (by field_simp [(hW n).ne'])
  have hi n := (M n).inherited_bare_residual_integrable (T:=T) (nu n) (W n)
  refine ⟨hi,?_⟩
  obtain ⟨B,hB,Hmean⟩:=eventually_actual_minimum_mass_mean_upper (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cs:=B*(1+C)
  have hCs : 0 < Cs := by dsimp [Cs];positivity
  apply squeeze_zero' (Eventually.of_forall fun _=>integral_nonneg (fun _=>abs_nonneg _)) _
    (by simpa only [mul_zero] using hepslim.const_mul (C*(Cs+1)))
  filter_upwards [Hmean,hEq4] with n hn hnEq
  have hw:=hW n
  have hpoint0 : ∀ᵐ(w : ParisiFinite.OrderPoint)∂mu n,
      |(((M n).b w-T)*orderedPathS (n+1) (M n).bf (M n).hf w+(M n).h w)/(W n)^3| ≤
        (Cs+1)*epsilon n := by
    filter_upwards [ae_restrict_mem (hF n)] with w hwF
    have hs0:=(M n).mass_mean_nonneg w.property
    have hs : orderedPathS (n+1) (M n).bf (M n).hf w ≤ Cs*W n := by
      by_cases hz : (w:ℝ)=0
      · simp only [hz,orderedPathS,orderedPathPair_zero];positivity
      · have H:=hn (M n) w ⟨lt_of_le_of_ne w.property.1 (Ne.symm hz),w.property.2⟩
        have hsmall : (M n).xs+(w:ℝ) ≤ (1+C)*W n := by nlinarith [hxs n,hcut n w hwF]
        have Hsmall:=mul_le_mul_of_nonneg_left hsmall hB.le
        exact H.trans (by dsimp [Cs];nlinarith only [Hsmall])
    obtain ⟨hb,hh⟩:=hnEq w hwF
    have Hmul:=mul_le_mul hb hs hs0 (mul_nonneg (hepsilon n) (sq_nonneg (W n)))
    rw [abs_div,abs_of_pos (pow_pos hw 3)]
    apply (div_le_iff₀ (pow_pos hw 3)).mpr
    have H:=abs_add_le (((M n).b w-T)*orderedPathS (n+1) (M n).bf (M n).hf w) ((M n).h w)
    rw [abs_mul,abs_of_nonneg hs0] at H
    nlinarith only [H,Hmul,hh]
  have hpoint : ∀ᵐ(w : ParisiFinite.OrderPoint)∂nu n,
      |(((M n).b w-T)*orderedPathS (n+1) (M n).bf (M n).hf w+(M n).h w)/(W n)^3| ≤
        (Cs+1)*epsilon n := by
    rw [ae_iff] at hpoint0 ⊢
    change (ENNReal.ofReal (1/W n) • mu n) _=0
    rw [Measure.smul_apply,hpoint0,smul_zero]
  have H:=integral_mono_ae (hi n).abs (integrable_const ((Cs+1)*epsilon n)) hpoint
  rw [integral_const,smul_eq_mul] at H
  have Hmass:=mul_le_mul_of_nonneg_right (hnMass n)
    (show 0 ≤ (Cs+1)*epsilon n from mul_nonneg (by linarith) (hepsilon n))
  exact H.trans (by nlinarith only [Hmass])

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
