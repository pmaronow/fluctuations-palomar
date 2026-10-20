module

public import ComparisonSignedCavityActualStarSubtreeProjection

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity

def jointFiniteExpect {P S : Type} [MeasurableSpace P] [Fintype S]
    (μ : Measure P) (w : P→S→ℝ) (J : P→S→ℝ) : ℝ :=
  ∫z,∑s,w z s*J z s ∂μ

theorem jointFiniteExpect_nonneg {P S : Type} [MeasurableSpace P] [Fintype S]
    (μ : Measure P) (w : P→S→ℝ) (hw : ∀z s,0 ≤ w z s)
    (J : P→S→ℝ) (hJ : ∀z s,0 ≤ J z s) : 0 ≤ jointFiniteExpect μ w J := by
  apply integral_nonneg
  intro z
  exact Finset.sum_nonneg fun s _=>mul_nonneg (hw z s) (hJ z s)

theorem jointFiniteExpect_integrable {P S : Type} [MeasurableSpace P] [Fintype S]
    (μ : Measure P) [IsFiniteMeasure μ] (w : P→S→ℝ)
    (hw : ∀z s,0 ≤ w z s) (hsum : ∀z,∑s,w z s=1)
    (hwm : ∀s,Measurable (fun z=>w z s))
    (J : P→S→ℝ) (hJ : ∀s,Measurable (fun z=>J z s))
    (C : ℝ) (hbound : ∀z s,|J z s| ≤ C) :
    Integrable (fun z=>∑s,w z s*J z s) μ := by
  apply Integrable.of_bound (Finset.measurable_sum _ (fun s _=>(hwm s).mul (hJ s))).aestronglyMeasurable C
  apply Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ∑s,|w z s*J z s|:=Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑s,w z s*C:=Finset.sum_le_sum fun s _=>by
      rw [abs_mul,abs_of_nonneg (hw z s)]
      exact mul_le_mul_of_nonneg_left (hbound z s) (hw z s)
    _=C:=by rw [←Finset.sum_mul,hsum z,one_mul]

theorem jointFiniteExpect_mul_sq_le {P S : Type} [MeasurableSpace P] [Fintype S]
    (μ : Measure P) [IsFiniteMeasure μ] (w : P→S→ℝ)
    (hw : ∀z s,0 ≤ w z s) (hsum : ∀z,∑s,w z s=1)
    (hwm : ∀s,Measurable (fun z=>w z s))
    (J L : P→S→ℝ) (hJ : ∀s,Measurable (fun z=>J z s))
    (hL : ∀s,Measurable (fun z=>L z s))
    (C D : ℝ) (hC : 0 ≤ C)
    (hJb : ∀z s,|J z s| ≤ C) (hLb : ∀z s,|L z s| ≤ D) :
    jointFiniteExpect μ w (fun z s=>J z s*L z s)^2 ≤
      jointFiniteExpect μ w (fun z s=>J z s^2)*jointFiniteExpect μ w (fun z s=>L z s^2) := by
  have hJJ:=jointFiniteExpect_integrable μ w hw hsum hwm (fun z s=>J z s^2)
    (fun s=>(hJ s).pow_const 2) (C^2)
    (fun z s=>by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hJb z s) 2)
  have hLL:=jointFiniteExpect_integrable μ w hw hsum hwm (fun z s=>L z s^2)
    (fun s=>(hL s).pow_const 2) (D^2)
    (fun z s=>by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hLb z s) 2)
  have hJL:=jointFiniteExpect_integrable μ w hw hsum hwm (fun z s=>J z s*L z s)
    (fun s=>(hJ s).mul (hL s)) (C*D)
    (fun z s=>by rw [abs_mul];exact mul_le_mul (hJb z s) (hLb z s) (abs_nonneg _) hC)
  have hpos (t : ℝ) : 0 ≤
      jointFiniteExpect μ w (fun z s=>J z s^2)*(t*t)+
      (2*jointFiniteExpect μ w (fun z s=>J z s*L z s))*t+
      jointFiniteExpect μ w (fun z s=>L z s^2) := by
    have H:=jointFiniteExpect_nonneg μ w hw (fun z s=>(t*J z s+L z s)^2) (fun _ _=>sq_nonneg _)
    have he z : (∑s,w z s*(t*J z s+L z s)^2)=
        t^2*(∑s,w z s*J z s^2)+(2*t)*(∑s,w z s*(J z s*L z s))+
          ∑s,w z s*L z s^2 := by
      simp only [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      ring
    unfold jointFiniteExpect at H ⊢
    simp_rw [he] at H
    have e1:=integral_add ((hJJ.const_mul (t^2)).add (hJL.const_mul (2*t))) hLL
    have e2:=integral_add (hJJ.const_mul (t^2)) (hJL.const_mul (2*t))
    simp only [Pi.add_apply] at e1 e2
    rw [e1,e2,integral_const_mul,integral_const_mul] at H
    nlinarith
  have H:=discrim_le_zero hpos
  dsimp only [discrim] at H
  nlinarith

theorem jointFiniteExpect_old_second_projection_fourth
    {P S : Type} [MeasurableSpace P] [Fintype S]
    (μ : Measure P) [IsProbabilityMeasure μ] (w : P→S→ℝ)
    (hw : ∀z s,0 ≤ w z s) (hsum : ∀z,∑s,w z s=1)
    (hwm : ∀s,Measurable (fun z=>w z s))
    (Z A : P→S→ℝ) (hZ : ∀s,Measurable (fun z=>Z z s))
    (hA : ∀s,Measurable (fun z=>A z s))
    (C D : ℝ) (hC : 0 ≤ C)
    (hZb : ∀z s,|Z z s| ≤ C) (hAb : ∀z s,|A z s| ≤ D)
    {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hZ2 : jointFiniteExpect μ w (fun z s=>Z z s^2) ≤ p^2)
    (hA4 : jointFiniteExpect μ w (fun z s=>A z s^4) ≤ r^4) :
    |jointFiniteExpect μ w (fun z s=>Z z s*A z s)| ≤ p*r := by
  have H:=jointFiniteExpect_mul_sq_le μ w hw hsum hwm Z A hZ hA C D hC hZb hAb
  have HA:=jointFiniteExpect_mul_sq_le μ w hw hsum hwm (fun z s=>A z s^2) (fun _ _=>1)
    (fun s=>(hA s).pow_const 2) (fun _=>measurable_const) (D^2) 1 (sq_nonneg _)
    (fun z s=>by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hAb z s) 2)
    (fun _ _=>by norm_num)
  have hone : jointFiniteExpect μ w (fun _ _=>1)=1 := by
    unfold jointFiniteExpect
    simp_rw [mul_one,hsum]
    simp
  have he : (fun z s=>(A z s^2)^2)=(fun z s=>A z s^4):=by funext z s;ring
  simp only [mul_one,one_pow,he,hone] at HA
  have hA2n:=jointFiniteExpect_nonneg μ w hw (fun z s=>A z s^2) (fun _ _=>sq_nonneg _)
  have hA2 : jointFiniteExpect μ w (fun z s=>A z s^2) ≤ r^2 := by
    have HH:=HA.trans hA4
    nlinarith [sq_nonneg (jointFiniteExpect μ w (fun z s=>A z s^2)+r^2)]
  have Hfinal:=H.trans ((mul_le_mul_of_nonneg_right hZ2 hA2n).trans
    (mul_le_mul_of_nonneg_left hA2 (sq_nonneg p)))
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hp hr)).mp
  simpa only [sq_abs,mul_pow] using Hfinal

end OAI.SKFluctuations.Cavity
