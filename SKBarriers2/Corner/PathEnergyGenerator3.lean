module

public import SKBarriers2.Corner.PathEnergyProof3

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

section NoiseTangents

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

theorem covariance_noise_tangent_eq {f g : ℝ → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hi : MemLp (fun t : ℝ => t) 2 μ)
    (f₀ g₀ a b : ℝ) :
    covariance f g μ-a*b*covariance (fun t : ℝ => t) (fun t : ℝ => t) μ =
      covariance (fun t => f t-f₀-a*t) (fun t => g t-g₀) μ+
        a*covariance (fun t : ℝ => t) (fun t => g t-g₀-b*t) μ := by
  have hgc := hg.sub (memLp_const g₀)
  have hfc := hf.sub (memLp_const f₀)
  have hat := hi.const_mul a
  have hbt := hi.const_mul b
  change _ = covariance ((f-fun _ => f₀)-(fun t => a*t)) (g-fun _ => g₀) μ+
    a*covariance (fun t : ℝ => t) ((g-fun _ => g₀)-(fun t => b*t)) μ
  rw [covariance_sub_left hfc hat hgc,covariance_sub_left hf (memLp_const f₀) hgc,
    covariance_const_left,covariance_const_mul_left,
    covariance_sub_right hi hgc hbt,covariance_const_mul_right,
    covariance_sub_right hf hg (memLp_const g₀),covariance_const_right,
    covariance_sub_right hi hg (memLp_const g₀),covariance_const_right]
  ring

theorem abs_covariance_noise_tangent_le {f g : ℝ → ℝ}
    {f₀ g₀ a b AL BL AR BR V d M₁ M₂ M₃ : ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hi : MemLp (fun t : ℝ => t) 2 μ)
    (hAL : 0 ≤ AL) (hBL : 0 ≤ BL) (hAR : 0 ≤ AR) (hBR : 0 ≤ BR)
    (hd : 0 ≤ d)
    (ha : |a| ≤ AL*d) (hb : |b| ≤ BL*d)
    (hgc : ∀ t, |g t-g₀| ≤ BL*d*|t|)
    (hfr : ∀ t, |f t-f₀-a*t| ≤ AR*d^2*|t|^2)
    (hgr : ∀ t, |g t-g₀-b*t| ≤ BR*d^2*|t|^2)
    (hi₁ : Integrable (fun t : ℝ => |t|) μ)
    (hi₂ : Integrable (fun t : ℝ => |t|^2) μ)
    (hi₃ : Integrable (fun t : ℝ => |t|^3) μ)
    (hM₁ : (∫ t : ℝ, |t| ∂μ) ≤ M₁)
    (hM₂ : (∫ t : ℝ, |t|^2 ∂μ) ≤ M₂)
    (hM₃ : (∫ t : ℝ, |t|^3 ∂μ) ≤ M₃)
    (hvar : |covariance (fun t : ℝ => t) (fun t : ℝ => t) μ-1| ≤ V*d) :
    |covariance f g μ-a*b| ≤
      ((AR*BL+AL*BR)*(M₃+M₂*M₁)+AL*BL*V)*d^3 := by
  have hM₁0 : 0 ≤ M₁ := (integral_nonneg (fun _ => abs_nonneg _)).trans hM₁
  have hM₂0 : 0 ≤ M₂ := (integral_nonneg (fun _ => sq_nonneg _)).trans hM₂
  have hM₃0 : 0 ≤ M₃ := (integral_nonneg (fun _ => by positivity)).trans hM₃
  have hfc := hf.sub (memLp_const f₀)
  have hgc' := hg.sub (memLp_const g₀)
  have hfr' := hfc.sub (hi.const_mul a)
  have hgr' := hgc'.sub (hi.const_mul b)
  have hleft := abs_covariance_le_noise_moments (p := 2) (q := 1) hfr' hgc'
    (by positivity : 0 ≤ AR*d^2) (by positivity : 0 ≤ BL*d)
    hfr (by simpa only [pow_one,Pi.sub_apply] using hgc)
    hi₂ (by simpa only [pow_one] using hi₁) hi₃ hM₂
    (by simpa only [pow_one] using hM₁) hM₃
  have hright := abs_covariance_le_noise_moments (p := 1) (q := 2) hi hgr'
    (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ BR*d^2)
    (by intro t; simp only [pow_one,one_mul,le_refl]) hgr
    (by simpa only [pow_one] using hi₁) hi₂ hi₃
    (by simpa only [pow_one] using hM₁) hM₂ hM₃
  have he : covariance f g μ-a*b =
      covariance (fun t => f t-f₀-a*t) (fun t => g t-g₀) μ+
        a*covariance (fun t : ℝ => t) (fun t => g t-g₀-b*t) μ+
          a*b*(covariance (fun t : ℝ => t) (fun t : ℝ => t) μ-1) := by
    have H' := covariance_noise_tangent_eq hf hg hi f₀ g₀ a b
    linarith only [H']
  rw [he]
  calc
    _ ≤ |covariance (fun t => f t-f₀-a*t) (fun t => g t-g₀) μ|+
        |a| *|covariance (fun t : ℝ => t) (fun t => g t-g₀-b*t) μ|+
          |a| *|b| *|covariance (fun t : ℝ => t) (fun t : ℝ => t) μ-1| := by
      have htri (x y z : ℝ) : |x+y+z| ≤ |x|+|y|+|z| :=
        (abs_add_le (x+y) z).trans (add_le_add (abs_add_le x y) le_rfl)
      simpa only [abs_mul] using htri
        (covariance (fun t => f t-f₀-a*t) (fun t => g t-g₀) μ)
        (a*covariance (fun t : ℝ => t) (fun t => g t-g₀-b*t) μ)
        (a*b*(covariance (fun t : ℝ => t) (fun t : ℝ => t) μ-1))
    _ ≤ (AR*d^2)*(BL*d)*(M₃+M₂*M₁)+
        (AL*d)*(1*(BR*d^2)*(M₃+M₁*M₂))+(AL*d)*(BL*d)*(V*d) := by
      refine add_le_add (add_le_add ?_ ?_) ?_
      · exact hleft
      · exact mul_le_mul ha hright (abs_nonneg _) (by positivity)
      · exact mul_le_mul (mul_le_mul ha hb (abs_nonneg _) (by positivity)) hvar
          (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem abs_noise_score_cumulant_le {g s : ℝ → ℝ} {g₀ C S d M₁ M₂ M₃ : ℝ}
    (hg : MemLp g 2 μ) (hs : MemLp s 2 μ) (hss : MemLp (fun t => s t^2) 2 μ)
    (hC : 0 ≤ C) (hS : 0 ≤ S) (hd : 0 ≤ d)
    (hgc : ∀ t, |g t-g₀| ≤ C*d*|t|) (hsc : ∀ t, |s t| ≤ S*d*|t|)
    (hi₁ : Integrable (fun t : ℝ => |t|) μ)
    (hi₂ : Integrable (fun t : ℝ => |t|^2) μ)
    (hi₃ : Integrable (fun t : ℝ => |t|^3) μ)
    (hM₁ : (∫ t : ℝ, |t| ∂μ) ≤ M₁)
    (hM₂ : (∫ t : ℝ, |t|^2 ∂μ) ≤ M₂)
    (hM₃ : (∫ t : ℝ, |t|^3 ∂μ) ≤ M₃) :
    |covariance g (fun t => s t^2) μ-2*(∫ t, s t ∂μ)*covariance g s μ| ≤
      C*S^2*((M₃+M₁*M₂)+2*M₁*(M₂+M₁^2))*d^3 := by
  have hM₁0 : 0 ≤ M₁ := (integral_nonneg (fun _ => abs_nonneg _)).trans hM₁
  have hM₂0 : 0 ≤ M₂ := (integral_nonneg (fun _ => sq_nonneg _)).trans hM₂
  have hM₃0 : 0 ≤ M₃ := (integral_nonneg (fun _ => by positivity)).trans hM₃
  have hgc' := hg.sub (memLp_const g₀)
  have hssb (t : ℝ) : |s t^2| ≤ (S*d)^2*|t|^2 := by
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg _) (hsc t) 2).trans_eq (by ring)
  have hq := abs_covariance_le_noise_moments (p := 1) (q := 2) hgc' hss
    (by positivity : 0 ≤ C*d) (sq_nonneg (S*d))
    (by simpa only [pow_one,Pi.sub_apply] using hgc) hssb
    (by simpa only [pow_one] using hi₁) hi₂ hi₃
    (by simpa only [pow_one] using hM₁) hM₂ hM₃
  rw [covariance_sub_left hg (memLp_const g₀) hss,covariance_const_left,sub_zero] at hq
  have hl := abs_covariance_le_noise_moments (p := 1) (q := 1) hgc' hs
    (by positivity : 0 ≤ C*d) (by positivity : 0 ≤ S*d)
    (by simpa only [pow_one,Pi.sub_apply] using hgc) (by simpa only [pow_one] using hsc)
    (by simpa only [pow_one] using hi₁) (by simpa only [pow_one] using hi₁)
    hi₂ (by simpa only [pow_one] using hM₁) (by simpa only [pow_one] using hM₁) hM₂
  rw [covariance_sub_left hg (memLp_const g₀) hs,covariance_const_left,sub_zero] at hl
  have hm := abs_integral_le_noise_moment (p := 1)
    (by simpa only [pow_one] using hi₁) (by positivity : 0 ≤ S*d)
    (by simpa only [pow_one] using hsc) (by simpa only [pow_one] using hM₁)
  calc
    _ ≤ |covariance g (fun t => s t^2) μ|+
        2*|∫ t, s t ∂μ| *|covariance g s μ| := by
      simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)] using abs_sub
        (covariance g (fun t => s t^2) μ) (2*(∫ t, s t ∂μ)*covariance g s μ)
    _ ≤ (C*d)*(S*d)^2*(M₃+M₁*M₂)+
        2*((S*d)*M₁)*((C*d)*(S*d)*(M₂+M₁*M₁)) := by gcongr
    _ = _ := by ring

end NoiseTangents

section SecondWeakCancellation

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

theorem abs_secondAverageTransport_sub_tangents_le
    {g a b s t : ℝ → ℝ} {g₀ a₀ tg ta ts tt P C J W V d M₁ M₂ M₃ : ℝ}
    (hg : MemLp g 2 μ) (ha : MemLp a 2 μ) (hs : MemLp s 2 μ)
    (ht : MemLp t 2 μ) (hss : MemLp (fun x => s x^2) 2 μ)
    (hi : MemLp (fun x : ℝ => x) 2 μ)
    (hC : 0 ≤ C) (hJ : 0 ≤ J) (hW : 0 ≤ W) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hgc : ∀ x, |g x-g₀| ≤ C*d*|x|)
    (hsc : ∀ x, |s x| ≤ (3*J)*d*|x|)
    (htg : |tg| ≤ C*d) (hta : |ta| ≤ (2*C)*d)
    (hts : |ts| ≤ (3*J)*d) (htt : |tt| ≤ (9*J)*d)
    (hgr : ∀ x, |g x-g₀-tg*x| ≤ C*d^2*|x|^2)
    (har : ∀ x, |a x-a₀-ta*x| ≤ (2*C)*d^2*|x|^2)
    (hsr : ∀ x, |s x-ts*x| ≤ (3*J)*d^2*|x|^2)
    (htr : ∀ x, |t x-tt*x| ≤ (10*J)*d^2*|x|^2)
    (hi₁ : Integrable (fun x : ℝ => |x|) μ)
    (hi₂ : Integrable (fun x : ℝ => |x|^2) μ)
    (hi₃ : Integrable (fun x : ℝ => |x|^3) μ)
    (hM₁ : (∫ x : ℝ, |x| ∂μ) ≤ M₁)
    (hM₂ : (∫ x : ℝ, |x|^2 ∂μ) ≤ M₂)
    (hM₃ : (∫ x : ℝ, |x|^3 ∂μ) ≤ M₃)
    (hvar : |covariance (fun x : ℝ => x) (fun x : ℝ => x) μ-1| ≤ V*d)
    (havg : |(∫ x, b x ∂μ)-P| ≤ C*W*d^4) :
    |secondAverageTransport μ g a b s t-(P+2*ta*ts+tg*tt)| ≤
      C*(W+43*J*(M₃+M₂*M₁)+21*J*V+
        9*J^2*((M₃+M₁*M₂)+2*M₁*(M₂+M₁^2)))*d^3 := by
  have hTS := abs_covariance_noise_tangent_le (f₀ := a₀) (g₀ := 0)
    ha hs hi (by positivity : 0 ≤ 2*C) (by positivity : 0 ≤ 3*J)
    (by positivity : 0 ≤ 2*C) (by positivity : 0 ≤ 3*J) hd hta hts
    (by simpa only [sub_zero] using hsc) har (by simpa only [sub_zero] using hsr)
    hi₁ hi₂ hi₃ hM₁ hM₂ hM₃ hvar
  have hRG := abs_covariance_noise_tangent_le (f₀ := 0) (g₀ := g₀)
    ht hg hi (by positivity : 0 ≤ 9*J) hC (by positivity : 0 ≤ 10*J) hC hd htt htg
    hgc (by simpa only [sub_zero] using htr) hgr hi₁ hi₂ hi₃ hM₁ hM₂ hM₃ hvar
  rw [covariance_comm] at hRG
  have hGR : |covariance g t μ-tg*tt| ≤
      ((10*J*C+9*J*C)*(M₃+M₂*M₁)+9*J*C*V)*d^3 := by
    simpa only [mul_comm tg tt] using hRG
  have hcum := abs_noise_score_cumulant_le hg hs hss hC (by positivity : 0 ≤ 3*J)
    hd hgc hsc hi₁ hi₂ hi₃ hM₁ hM₂ hM₃
  have hd43 : d^4 ≤ d^3 := by
    nlinarith only [mul_nonneg (pow_nonneg hd 3) (sub_nonneg.mpr hd1)]
  have havg' : |(∫ x, b x ∂μ)-P| ≤ C*W*d^3 :=
    havg.trans (mul_le_mul_of_nonneg_left hd43 (mul_nonneg hC hW))
  have he : secondAverageTransport μ g a b s t-(P+2*ta*ts+tg*tt) =
      ((∫ x, b x ∂μ)-P)+2*(covariance a s μ-ta*ts)+(covariance g t μ-tg*tt)+
        (covariance g (fun x => s x^2) μ-2*(∫ x, s x ∂μ)*covariance g s μ) := by
    dsimp only [secondAverageTransport]
    ring
  rw [he]
  have htri (u z y x : ℝ) : |u+2*z+y+x| ≤ |u|+2*|z|+|y|+|x| := by
    apply (abs_add_le _ _).trans
    apply add_le_add _ le_rfl
    apply (abs_add_le _ _).trans
    apply add_le_add _ le_rfl
    simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)] using abs_add_le u (2*z)
  apply (htri _ _ _ _).trans
  calc
    _ ≤ C*W*d^3+
        2*(((2*C*(3*J)+2*C*(3*J))*(M₃+M₂*M₁)+2*C*(3*J)*V)*d^3)+
        ((10*J*C+9*J*C)*(M₃+M₂*M₁)+9*J*C*V)*d^3+
        C*(3*J)^2*((M₃+M₁*M₂)+2*M₁*(M₂+M₁^2))*d^3 :=
      add_le_add (add_le_add (add_le_add havg'
        (mul_le_mul_of_nonneg_left hTS (by norm_num : (0:ℝ) ≤ 2))) hGR) hcum
    _ = _ := by ring

end SecondWeakCancellation

end SKBarriers2.StepCalculus
