module

public import ComparisonNativeActualInheritedBareErrorAlong
public import ComparisonNativeActualHistoryNearBareClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 7000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem actual_inherited_restricted_bare_error_of_vanishing_clocks_along
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n)
    (F : ℕ→Set ParisiFinite.OrderPoint) (hF : ∀n,MeasurableSet (F n))
    (C : ℝ) (hC : 0 < C) (hcut : ∀n w,w∈F n → (w:ℝ) ≤ C*W n)
    (hEq4 : ∀epsilon > 0,∀ᶠn in atTop,∀w∈F n,
      |(M n).b w-T| ≤ epsilon*(W n)^2 ∧ |(M n).h w| ≤ epsilon*(W n)^3) :
    let nu:=fun n=>ENNReal.ofReal (1/W n) •
      (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict (F n)
    (∀n,Integrable (fun w : ParisiFinite.OrderPoint=>
      (((M n).b w-T)*orderedPathS (dim n+1) (M n).bf (M n).hf w+(M n).h w)/(W n)^3) (nu n)) ∧
    Tendsto (fun n=>∫w : ParisiFinite.OrderPoint,
      |(((M n).b w-T)*orderedPathS (dim n+1) (M n).bf (M n).hf w+(M n).h w)/(W n)^3|
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
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun _=>ha.trans_le (integral_nonneg (fun _=>abs_nonneg _))
  · intro e he
    let epsilon:=e/(2*C*(Cs+1))
    have hepsilon : 0 < epsilon:=by dsimp only [epsilon];positivity
    filter_upwards [hdim.eventually Hmean,hEq4 epsilon hepsilon] with n hn hnEq
    have hw:=hW n
    have hpoint0 : ∀ᵐ(w : ParisiFinite.OrderPoint)∂mu n,
        |(((M n).b w-T)*orderedPathS (dim n+1) (M n).bf (M n).hf w+(M n).h w)/(W n)^3| ≤
          (Cs+1)*epsilon := by
      filter_upwards [ae_restrict_mem (hF n)] with w hwF
      have hs0:=(M n).mass_mean_nonneg w.property
      have hs : orderedPathS (dim n+1) (M n).bf (M n).hf w ≤ Cs*W n := by
        by_cases hz : (w:ℝ)=0
        · simp only [hz,orderedPathS,orderedPathPair_zero];positivity
        · have H:=hn (M n) w ⟨lt_of_le_of_ne w.property.1 (Ne.symm hz),w.property.2⟩
          have hsmall : (M n).xs+(w:ℝ) ≤ (1+C)*W n := by nlinarith [hxs n,hcut n w hwF]
          have Hsmall:=mul_le_mul_of_nonneg_left hsmall hB.le
          exact H.trans (by dsimp [Cs];nlinarith only [Hsmall])
      obtain ⟨hb,hh⟩:=hnEq w hwF
      have Hmul:=mul_le_mul hb hs hs0 (mul_nonneg hepsilon.le (sq_nonneg (W n)))
      rw [abs_div,abs_of_pos (pow_pos hw 3)]
      apply (div_le_iff₀ (pow_pos hw 3)).mpr
      have H:=abs_add_le (((M n).b w-T)*orderedPathS (dim n+1) (M n).bf (M n).hf w) ((M n).h w)
      rw [abs_mul,abs_of_nonneg hs0] at H
      nlinarith only [H,Hmul,hh]
    have hpoint : ∀ᵐ(w : ParisiFinite.OrderPoint)∂nu n,
        |(((M n).b w-T)*orderedPathS (dim n+1) (M n).bf (M n).hf w+(M n).h w)/(W n)^3| ≤
          (Cs+1)*epsilon := by
      rw [ae_iff] at hpoint0 ⊢
      change (ENNReal.ofReal (1/W n) • mu n) _=0
      rw [Measure.smul_apply,hpoint0,smul_zero]
    have H:=integral_mono_ae (hi n).abs (integrable_const ((Cs+1)*epsilon)) hpoint
    rw [integral_const,smul_eq_mul] at H
    have Hmass:=mul_le_mul_of_nonneg_right (hnMass n)
      (show 0 ≤ (Cs+1)*epsilon from mul_nonneg (by linarith) hepsilon.le)
    have Hbound : (∫w : ParisiFinite.OrderPoint,
        |(((M n).b w-T)*orderedPathS (dim n+1) (M n).bf (M n).hf w+(M n).h w)/(W n)^3|
          ∂nu n) ≤ C*(Cs+1)*epsilon := H.trans (by nlinarith only [Hmass])
    apply Hbound.trans_lt
    have heq : C*(Cs+1)*epsilon=e/2:=by
      dsimp only [epsilon]
      field_simp
    rw [heq]
    linarith

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
