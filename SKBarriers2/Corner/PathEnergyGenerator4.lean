module

public import SKBarriers2.Corner.PathEnergyRecursions2
public import SKBarriers2.Corner.PathEnergyGenerator3

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

theorem abs_firstAverageScore_tangent_le {B A m dm d : ℝ} {f f₁ : E → ℝ}
    (hf : QPotential 3 B f) (hf₁ : QBoundedJets 3 A f₁)
    (hm : |m| ≤ 1) (hdm : |dm| ≤ 1)
    (v w x : E) (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d) :
    |dm*fderiv ℝ f x v+m*(fderiv ℝ f₁ x v+fderiv ℝ f x w)| ≤ (2*B+A)*d := by
  have hB := hf.nonneg
  have hA := hf₁.nonneg
  have h₁ := (qBoundedJets_iff_qBddSmooth.mp hf₁).potential
  calc
    _ ≤ |dm| *|fderiv ℝ f x v|+|m| *(|fderiv ℝ f₁ x v|+|fderiv ℝ f x w|) := by
      exact (abs_add_le _ _).trans (by rw [abs_mul,abs_mul]; gcongr; exact abs_add_le _ _)
    _ ≤ 1*(B*‖v‖)+1*(A*‖v‖+B*‖w‖) := by
      gcongr
      · exact hf.directional_le (by norm_num) x v
      · exact h₁.directional_le (by norm_num) x v
      · exact hf.directional_le (by norm_num) x w
    _ ≤ 1*(B*d)+1*(A*d+B*d) := by gcongr
    _ = _ := by ring

theorem abs_secondAverageScore_tangent_le {B A H m dm ddm d : ℝ} {f f₁ f₂ : E → ℝ}
    (hf : QPotential 3 B f) (hf₁ : QBoundedJets 3 A f₁) (hf₂ : QBoundedJets 2 H f₂)
    (hm : |m| ≤ 1) (hdm : |dm| ≤ 1) (hddm : |ddm| ≤ 1)
    (v w b x : E) (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d) (hb : ‖b‖ ≤ d) :
    |ddm*fderiv ℝ f x v+2*dm*(fderiv ℝ f₁ x v+fderiv ℝ f x w)+
        m*(fderiv ℝ f₂ x v+2*fderiv ℝ f₁ x w+fderiv ℝ f x b)| ≤ (4*B+4*A+H)*d := by
  have hB := hf.nonneg
  have hA := hf₁.nonneg
  have hH := hf₂.nonneg
  have h₁ := (qBoundedJets_iff_qBddSmooth.mp hf₁).potential
  have h₂ := (qBoundedJets_iff_qBddSmooth.mp hf₂).potential
  have hinner : |fderiv ℝ f₂ x v+2*fderiv ℝ f₁ x w+fderiv ℝ f x b| ≤
      |fderiv ℝ f₂ x v|+2*|fderiv ℝ f₁ x w|+|fderiv ℝ f x b| := by
    apply (abs_add_le _ _).trans
    apply add_le_add _ le_rfl
    simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)] using
      abs_add_le (fderiv ℝ f₂ x v) (2*fderiv ℝ f₁ x w)
  calc
    _ ≤ |ddm| *|fderiv ℝ f x v|+2*|dm| *(|fderiv ℝ f₁ x v|+|fderiv ℝ f x w|)+
        |m| *(|fderiv ℝ f₂ x v|+2*|fderiv ℝ f₁ x w|+|fderiv ℝ f x b|) := by
      apply (abs_add_le _ _).trans
      apply add_le_add _ (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hinner (abs_nonneg m))
      apply (abs_add_le _ _).trans
      rw [abs_mul,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
      gcongr
      exact abs_add_le _ _
    _ ≤ 1*(B*‖v‖)+2*1*(A*‖v‖+B*‖w‖)+
        1*(H*‖v‖+2*(A*‖w‖)+B*‖b‖) := by
      gcongr
      · exact hf.directional_le (by norm_num) x v
      · exact h₁.directional_le (by norm_num) x v
      · exact hf.directional_le (by norm_num) x w
      · exact h₂.directional_le (by norm_num) x v
      · exact h₁.directional_le (by norm_num) x w
      · exact hf.directional_le (by norm_num) x b
    _ ≤ 1*(B*d)+2*1*(A*d+B*d)+1*(H*d+2*(A*d)+B*d) := by gcongr
    _ = _ := by ring

theorem abs_movingTestFirst_sub_tangent {C D d : ℝ} {g a : E → ℝ}
    (hg : QBoundedJets 3 C g) (ha : QBoundedJets 2 D a) (hd : 0 ≤ d)
    (v w x : E) (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d) (t : ℝ) :
    |movingAverageTestFirst v w g a x t-a x-
        t*(fderiv ℝ a x v+fderiv ℝ g x w)| ≤ (C+D)*d^2*|t|^2 := by
  have hA := abs_potential_noise_linear_remainder
    (qBoundedJets_iff_qBddSmooth.mp ha).potential v x t
  have hG := abs_noisy_gradient_sub_local (qBoundedJets_iff_qBddSmooth.mp hg).potential v w x t
  have he : movingAverageTestFirst v w g a x t-a x-
      t*(fderiv ℝ a x v+fderiv ℝ g x w) =
      (a (x+t • v)-a x-t*fderiv ℝ a x v)+
        t*(fderiv ℝ g (x+t • v) w-fderiv ℝ g x w) := by
    dsimp only [movingAverageTestFirst]
    ring
  rw [he]
  calc
    _ ≤ |a (x+t • v)-a x-t*fderiv ℝ a x v|+
        |t*(fderiv ℝ g (x+t • v) w-fderiv ℝ g x w)| := abs_add_le _ _
    _ ≤ D*‖v‖^2*|t|^2+C*‖v‖*‖w‖*|t|^2 := add_le_add hA hG
    _ ≤ D*d^2*|t|^2+C*d*d*|t|^2 := by
      have hC := hg.nonneg
      have hD := ha.nonneg
      gcongr
    _ = _ := by ring

theorem abs_secondAverageScore_sub_tangent {B A H m dm ddm d : ℝ}
    {f f₁ f₂ : E → ℝ}
    (hf : QPotential 3 B f) (hf₁ : QBoundedJets 3 A f₁)
    (hf₂ : QBoundedJets 2 H f₂) (hd : 0 ≤ d)
    (v w b x : E) (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d) (hb : ‖b‖ ≤ d) (t : ℝ) :
    |secondAverageScoreLinear m dm ddm v w b f f₁ f₂ x t+
        secondAverageScoreQuadratic m v w f x t-
      t*(ddm*fderiv ℝ f x v+2*dm*(fderiv ℝ f₁ x v+fderiv ℝ f x w)+
        m*(fderiv ℝ f₂ x v+2*fderiv ℝ f₁ x w+fderiv ℝ f x b))| ≤
      (|ddm| *B+2*|dm| *(A+B)+|m| *(H+2*A+2*B))*d^2*|t|^2 := by
  have hB := hf.nonneg
  have hA := hf₁.nonneg
  have hH := hf₂.nonneg
  have hF := abs_potential_noise_linear_remainder (hf.of_le (by norm_num : 2 ≤ 3)) v x t
  have hF₁ := abs_potential_noise_linear_remainder
    (qBoundedJets_iff_qBddSmooth.mp (hf₁.of_le (by norm_num : 2 ≤ 3))).potential v x t
  have hF₂ := abs_potential_noise_linear_remainder
    (qBoundedJets_iff_qBddSmooth.mp hf₂).potential v x t
  have hW := abs_noisy_gradient_sub_local hf v w x t
  have hB' := abs_noisy_gradient_sub_local hf v b x t
  have hW₁ := abs_noisy_gradient_sub_local
    (qBoundedJets_iff_qBddSmooth.mp hf₁).potential v w x t
  have hQ : |secondAverageScoreQuadratic m v w f x t| ≤ |m| *B*d^2*|t|^2 := by
    dsimp only [secondAverageScoreQuadratic]
    rw [abs_mul,abs_mul,abs_pow,sq_abs]
    calc
      _ ≤ |m| *t^2*(B*‖w‖*‖w‖) := by
        exact mul_le_mul_of_nonneg_left (hf.second_directional_le (by norm_num) _ w w)
          (by positivity)
      _ ≤ |m| *t^2*(B*d*d) := by gcongr
      _ = _ := by ring
  have he : secondAverageScoreLinear m dm ddm v w b f f₁ f₂ x t+
      secondAverageScoreQuadratic m v w f x t-
      t*(ddm*fderiv ℝ f x v+2*dm*(fderiv ℝ f₁ x v+fderiv ℝ f x w)+
        m*(fderiv ℝ f₂ x v+2*fderiv ℝ f₁ x w+fderiv ℝ f x b)) =
      ddm*(f (x+t • v)-f x-t*fderiv ℝ f x v)+
      2*dm*((f₁ (x+t • v)-f₁ x-t*fderiv ℝ f₁ x v)+
        t*(fderiv ℝ f (x+t • v) w-fderiv ℝ f x w))+
      m*((f₂ (x+t • v)-f₂ x-t*fderiv ℝ f₂ x v)+
        2*(t*(fderiv ℝ f₁ (x+t • v) w-fderiv ℝ f₁ x w))+
        t*(fderiv ℝ f (x+t • v) b-fderiv ℝ f x b))+
      secondAverageScoreQuadratic m v w f x t := by
    dsimp only [secondAverageScoreLinear]
    ring
  rw [he]
  calc
    _ ≤ |ddm| *|f (x+t • v)-f x-t*fderiv ℝ f x v|+
        2*|dm| *(|f₁ (x+t • v)-f₁ x-t*fderiv ℝ f₁ x v|+
          |t*(fderiv ℝ f (x+t • v) w-fderiv ℝ f x w)|)+
        |m| *(|f₂ (x+t • v)-f₂ x-t*fderiv ℝ f₂ x v|+
          2*|t*(fderiv ℝ f₁ (x+t • v) w-fderiv ℝ f₁ x w)|+
          |t*(fderiv ℝ f (x+t • v) b-fderiv ℝ f x b)|)+
        |secondAverageScoreQuadratic m v w f x t| := by
      apply (abs_add_le _ _).trans
      apply add_le_add _ le_rfl
      apply (abs_add_le _ _).trans
      apply add_le_add _ (by
        rw [abs_mul]
        gcongr
        apply (abs_add_le _ _).trans
        apply add_le_add _ le_rfl
        simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)] using
          abs_add_le (f₂ (x+t • v)-f₂ x-t*fderiv ℝ f₂ x v)
            (2*(t*(fderiv ℝ f₁ (x+t • v) w-fderiv ℝ f₁ x w))))
      apply (abs_add_le _ _).trans
      rw [abs_mul,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
      gcongr
      exact abs_add_le _ _
    _ ≤ |ddm| *(B*‖v‖^2*|t|^2)+
        2*|dm| *(A*‖v‖^2*|t|^2+B*‖v‖*‖w‖*|t|^2)+
        |m| *(H*‖v‖^2*|t|^2+2*(A*‖v‖*‖w‖*|t|^2)+B*‖v‖*‖b‖*|t|^2)+
        |m| *B*d^2*|t|^2 := by gcongr
    _ ≤ |ddm| *(B*d^2*|t|^2)+2*|dm| *(A*d^2*|t|^2+B*d*d*|t|^2)+
        |m| *(H*d^2*|t|^2+2*(A*d*d*|t|^2)+B*d*d*|t|^2)+
        |m| *B*d^2*|t|^2 := by gcongr
    _ = _ := by ring

end SKBarriers2.StepCalculus
