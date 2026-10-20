module

public import SKBarriers2.Corner.PathEnergyInner3

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

private theorem inner_mul_norm_norm_le {C d : ℝ} (hC : 0 ≤ C) (hd : 0 ≤ d)
    {v w : E} (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d) :
    C*‖v‖*‖w‖ ≤ C*d^2 := by
  calc
    _ = C*(‖v‖*‖w‖) := by ring
    _ ≤ C*(d*d) := mul_le_mul_of_nonneg_left
      (mul_le_mul hv hw (norm_nonneg _) hd) hC
    _ = _ := by ring

theorem abs_second_directional_sub_le {B H : ℝ} {f F : E → ℝ}
    (hf : QPotential 4 B f) (hF : QPotential 4 B F)
    (hδ : QBoundedJets 3 H (fun y => F y-f y)) (x v w : E) :
    |fderiv ℝ (fderiv ℝ F) x v w-fderiv ℝ (fderiv ℝ f) x v w| ≤
      H*‖v‖*‖w‖ := by
  have he : fderiv ℝ (fun y => F y-f y) =
      fun y => fderiv ℝ F y-fderiv ℝ f y := by
    funext y
    exact fderiv_fun_sub (hF.smooth.differentiable (by norm_num) y)
      (hf.smooth.differentiable (by norm_num) y)
  have H := ((hδ.derivativeJets.derivativeJets.apply_const v).apply_const w).norm_le x
  rw [he,fderiv_fun_sub
    (hF.derivativeJets.smooth.differentiable (by norm_num) x)
    (hf.derivativeJets.smooth.differentiable (by norm_num) x)] at H
  simpa only [sub_apply,Real.norm_eq_abs,mul_assoc] using H

theorem abs_gradient_product_sub_le {B H : ℝ} {f F : E → ℝ}
    (hf : QPotential 4 B f) (hF : QPotential 4 B F)
    (hδ : QBoundedJets 3 H (fun y => F y-f y)) (x v w : E) :
    |fderiv ℝ F x v*fderiv ℝ F x w-fderiv ℝ f x v*fderiv ℝ f x w| ≤
      2*B*H*‖v‖*‖w‖ := by
  have hB := hf.nonneg
  have hH := hδ.nonneg
  have hd (u : E) : |fderiv ℝ F x u-fderiv ℝ f x u| ≤ H*‖u‖ := by
    have H := (qBoundedJets_iff_qBddSmooth.mp hδ).potential.directional_le
      (by norm_num) x u
    rw [fderiv_fun_sub (hF.smooth.differentiable (by norm_num) x)
      (hf.smooth.differentiable (by norm_num) x)] at H
    exact H
  have hv := hf.directional_le (by norm_num) x v
  have hw := hF.directional_le (by norm_num) x w
  have he : fderiv ℝ F x v*fderiv ℝ F x w-fderiv ℝ f x v*fderiv ℝ f x w =
      (fderiv ℝ F x v-fderiv ℝ f x v)*fderiv ℝ F x w+
        fderiv ℝ f x v*(fderiv ℝ F x w-fderiv ℝ f x w) := by ring
  rw [he]
  calc
    _ ≤ |(fderiv ℝ F x v-fderiv ℝ f x v)*fderiv ℝ F x w|+
        |fderiv ℝ f x v*(fderiv ℝ F x w-fderiv ℝ f x w)| := abs_add_le _ _
    _ ≤ (H*‖v‖)*(B*‖w‖)+(B*‖v‖)*(H*‖w‖) := by
      simp only [abs_mul]
      exact add_le_add
        (mul_le_mul (hd v) hw (abs_nonneg _) (by positivity))
        (mul_le_mul hv (hd w) (abs_nonneg _) (by positivity))
    _ = _ := by ring

theorem abs_directionSource_sub_le {B H : ℝ} {f F : E → ℝ}
    (hf : QPotential 4 B f) (hF : QPotential 4 B F)
    (hδ : QBoundedJets 3 H (fun y => F y-f y))
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (x v w : E) :
    |directionSource m v w F x-directionSource m v w f x| ≤
      (1+2*B)*H*‖v‖*‖w‖ := by
  have hh := abs_second_directional_sub_le hf hF hδ x v w
  have hp := abs_gradient_product_sub_le hf hF hδ x v w
  have he : directionSource m v w F x-directionSource m v w f x =
      (fderiv ℝ (fderiv ℝ F) x v w-fderiv ℝ (fderiv ℝ f) x v w)+
        m*(fderiv ℝ F x v*fderiv ℝ F x w-fderiv ℝ f x v*fderiv ℝ f x w) := by
    dsimp only [directionSource]
    ring
  rw [he]
  calc
    _ ≤ |fderiv ℝ (fderiv ℝ F) x v w-fderiv ℝ (fderiv ℝ f) x v w|+
        |m*(fderiv ℝ F x v*fderiv ℝ F x w-fderiv ℝ f x v*fderiv ℝ f x w)| := abs_add_le _ _
    _ ≤ H*‖v‖*‖w‖+1*(2*B*H*‖v‖*‖w‖) := by
      rw [abs_mul,abs_of_nonneg hm.1]
      gcongr
      exact hm.2
    _ = _ := by ring

theorem abs_stepQuadraticFirstSource_sub_terminal_le {B A H d : ℝ}
    {f F g : E → ℝ} (hf : QPotential 4 B f) (hF : QPotential 4 B F)
    (hδ : QBoundedJets 3 H (fun y => F y-f y)) (hg : QBoundedJets 4 A g)
    {m dm : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (hdm : |dm| ≤ 1) (hd : 0 ≤ d)
    (x v w : E) (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d) :
    |stepQuadraticFirstSource m v F g dm w x-g x-
      stepQuadraticFirstSource m v f (fun _ => 0) dm w x| ≤
      ((4*B+1)*A+(1+3*B)*H)*d^2 := by
  have hB := hf.nonneg
  have hA := hg.nonneg
  have hH := hδ.nonneg
  have hgen := (qBoundedJets_pathGenerator (hF.of_le (by norm_num)) hg hm v).norm_le x
  have hprod := abs_gradient_product_sub_le hf hF hδ x v v
  have hdir := abs_directionSource_sub_le hf hF hδ hm x v w
  have he : stepQuadraticFirstSource m v F g dm w x-g x-
      stepQuadraticFirstSource m v f (fun _ => 0) dm w x =
      pathGenerator m v F g x+(dm/2)*
        (fderiv ℝ F x v*fderiv ℝ F x v-fderiv ℝ f x v*fderiv ℝ f x v)+
        (directionSource m v w F x-directionSource m v w f x) := by
    simp only [stepQuadraticFirstSource,fderiv_fun_const,Pi.zero_apply,zero_apply,
      directionalJet,mul_zero,zero_add,add_zero,zero_div]
    dsimp only [pathGenerator,directionalJet]
    ring
  rw [he]
  calc
    _ ≤ |pathGenerator m v F g x|+|(dm/2)*
        (fderiv ℝ F x v*fderiv ℝ F x v-fderiv ℝ f x v*fderiv ℝ f x v)|+
        |directionSource m v w F x-directionSource m v w f x| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (4*B+1)*A*d^2+(1/2:ℝ)*(2*B*H*d*d)+(1+2*B)*H*d*d := by
      apply add_le_add
      · apply add_le_add
        · simpa only [Real.norm_eq_abs] using hgen.trans (by gcongr)
        · rw [abs_mul,abs_div]
          norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 2)]
          apply mul_le_mul
          · exact div_le_div_of_nonneg_right hdm (by norm_num)
          · convert hprod.trans (inner_mul_norm_norm_le (by positivity) hd hv hv) using 1; ring
          · exact abs_nonneg _
          · norm_num
      · convert hdir.trans (inner_mul_norm_norm_le (by positivity) hd hv hw) using 1; ring
    _ = _ := by ring

private theorem inner_abs_seven_add_le (a b c d e f g : ℝ) :
    |a+b+c+d+e+f+g| ≤ |a|+|b|+|c|+|d|+|e|+|f|+|g| := by
  have H := Finset.abs_sum_le_sum_abs
    (fun i : Fin 7 => ![a,b,c,d,e,f,g] i) Finset.univ
  simpa only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,add_zero,add_assoc] using H

theorem abs_stepQuadraticSecondSource_sub_terminal_le {B R d : ℝ}
    {f F g q : E → ℝ} (hf : QPotential 4 B f) (hF : QPotential 4 B F)
    (hδ : QBoundedJets 3 R (fun y => F y-f y))
    (hg : QBoundedJets 4 R g) (hq : QBoundedJets 4 R q) (hR1 : R ≤ 1)
    {m dm ddm : ℝ} (hm : m ∈ Icc (0:ℝ) 1)
    (hdm : |dm| ≤ 1) (hddm : |ddm| ≤ 1) (hd : 0 ≤ d)
    (x v w b : E) (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d) (hb : ‖b‖ ≤ d) :
    |stepQuadraticSecondSource m v F g q dm ddm w b x-q x-
      stepQuadraticSecondSource m v f (fun _ => 0) (fun _ => 0) dm ddm w b x| ≤
      (21*B+6)*R*d^2 := by
  have hB := hf.nonneg
  have hR := hg.nonneg
  have hgen : |pathGenerator m v F q x| ≤ (4*B+1)*R*d^2 := by
    have H := (qBoundedJets_pathGenerator (hF.of_le (by norm_num)) hq hm v).norm_le x
    have H' : |pathGenerator m v F q x| ≤ (4*B+1)*R*‖v‖^2 := by
      simpa only [Real.norm_eq_abs] using H
    exact H'.trans (by gcongr)
  have hmix : |2*mixedDirectionSource m v w F g x| ≤
      2*(1+2*B)*R*d^2 := by
    have H := (qBoundedJets_mixedDirectionSource (hF.of_le (by norm_num))
      (hg.of_le (by norm_num)) hm v w).norm_le x
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have H' : |mixedDirectionSource m v w F g x| ≤ (1+2*B)*R*‖v‖*‖w‖ := by
      simpa only [Real.norm_eq_abs] using H
    calc
      _ ≤ 2*((1+2*B)*R*‖v‖*‖w‖) := mul_le_mul_of_nonneg_left H' (by norm_num)
      _ ≤ 2*((1+2*B)*R*d*d) := by gcongr
      _ = _ := by ring
  have hhess : |fderiv ℝ (fderiv ℝ F) x w w-fderiv ℝ (fderiv ℝ f) x w w| ≤ R*d^2 :=
    (abs_second_directional_sub_le hf hF hδ x w w).trans
      (inner_mul_norm_norm_le hR hd hw hw)
  have hdir : |directionSource m v b F x-directionSource m v b f x| ≤
      (1+2*B)*R*d^2 :=
    (abs_directionSource_sub_le hf hF hδ hm x v b).trans
      (inner_mul_norm_norm_le (by positivity) hd hv hb)
  have hgv : |fderiv ℝ g x v| ≤ R*d :=
    ((qBoundedJets_iff_qBddSmooth.mp hg).potential.directional_le
      (by norm_num) x v).trans (by gcongr)
  have hFv : |fderiv ℝ F x v| ≤ B*d :=
    (hF.directional_le (by norm_num) x v).trans (by gcongr)
  have hFw : |fderiv ℝ F x w| ≤ B*d :=
    (hF.directional_le (by norm_num) x w).trans (by gcongr)
  have hprod (u z : E) (hu : ‖u‖ ≤ d) (hz : ‖z‖ ≤ d) :
      |fderiv ℝ F x u*fderiv ℝ F x z-fderiv ℝ f x u*fderiv ℝ f x z| ≤
        2*B*R*d^2 :=
    (abs_gradient_product_sub_le hf hF hδ x u z).trans
      (inner_mul_norm_norm_le (by positivity) hd hu hz)
  have hscore : |m*((fderiv ℝ g x v+fderiv ℝ F x w)^2-(fderiv ℝ f x w)^2)| ≤
      (1+4*B)*R*d^2 := by
    have he : (fderiv ℝ g x v+fderiv ℝ F x w)^2-(fderiv ℝ f x w)^2 =
        (fderiv ℝ g x v)^2+2*(fderiv ℝ g x v*fderiv ℝ F x w)+
        (fderiv ℝ F x w*fderiv ℝ F x w-fderiv ℝ f x w*fderiv ℝ f x w) := by ring
    have hs : |(fderiv ℝ g x v+fderiv ℝ F x w)^2-(fderiv ℝ f x w)^2| ≤
        (1+4*B)*R*d^2 := by
      rw [he]
      calc
        _ ≤ |(fderiv ℝ g x v)^2|+|2*(fderiv ℝ g x v*fderiv ℝ F x w)|+
            |fderiv ℝ F x w*fderiv ℝ F x w-fderiv ℝ f x w*fderiv ℝ f x w| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ (R*d)^2+2*((R*d)*(B*d))+2*B*R*d^2 := by
          simp only [abs_mul,abs_pow,abs_of_pos (by norm_num : (0:ℝ) < 2)]
          gcongr
          exact hprod w w hw hw
        _ ≤ (1+4*B)*R*d^2 := by
          have H := mul_le_of_le_one_right hR hR1
          nlinarith only [mul_nonneg (sub_nonneg.mpr H) (sq_nonneg d)]
    rw [abs_mul,abs_of_nonneg hm.1]
    exact (mul_le_mul_of_nonneg_left hs hm.1).trans
      (mul_le_of_le_one_left (by positivity) hm.2)
  have hmass : |2*dm*(fderiv ℝ F x v*(fderiv ℝ g x v+fderiv ℝ F x w)-
      fderiv ℝ f x v*fderiv ℝ f x w)| ≤ 6*B*R*d^2 := by
    have he : fderiv ℝ F x v*(fderiv ℝ g x v+fderiv ℝ F x w)-
        fderiv ℝ f x v*fderiv ℝ f x w =
        fderiv ℝ F x v*fderiv ℝ g x v+
          (fderiv ℝ F x v*fderiv ℝ F x w-fderiv ℝ f x v*fderiv ℝ f x w) := by ring
    rw [he,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have H : |fderiv ℝ F x v*fderiv ℝ g x v+
        (fderiv ℝ F x v*fderiv ℝ F x w-fderiv ℝ f x v*fderiv ℝ f x w)| ≤
        (B*d)*(R*d)+2*B*R*d^2 := by
      exact (abs_add_le _ _).trans (add_le_add (by rw [abs_mul]; gcongr)
        (hprod v w hv hw))
    calc
      _ ≤ (2*1)*((B*d)*(R*d)+2*B*R*d^2) := by gcongr
      _ = _ := by ring
  have hlast : |(ddm/2)*(fderiv ℝ F x v*fderiv ℝ F x v-
      fderiv ℝ f x v*fderiv ℝ f x v)| ≤ B*R*d^2 := by
    rw [abs_mul,abs_div]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 2)]
    calc
      _ ≤ (1/2:ℝ)*(2*B*R*d^2) := by gcongr; exact hprod v v hv hv
      _ = _ := by ring
  have he : stepQuadraticSecondSource m v F g q dm ddm w b x-q x-
      stepQuadraticSecondSource m v f (fun _ => 0) (fun _ => 0) dm ddm w b x =
      pathGenerator m v F q x+2*mixedDirectionSource m v w F g x+
      (fderiv ℝ (fderiv ℝ F) x w w-fderiv ℝ (fderiv ℝ f) x w w)+
      (directionSource m v b F x-directionSource m v b f x)+
      m*((fderiv ℝ g x v+fderiv ℝ F x w)^2-(fderiv ℝ f x w)^2)+
      2*dm*(fderiv ℝ F x v*(fderiv ℝ g x v+fderiv ℝ F x w)-
        fderiv ℝ f x v*fderiv ℝ f x w)+
      (ddm/2)*(fderiv ℝ F x v*fderiv ℝ F x v-fderiv ℝ f x v*fderiv ℝ f x v) := by
    simp only [stepQuadraticSecondSource,mixedDirectionSource,
      fderiv_fun_const,fderiv_zero,Pi.zero_apply,zero_apply,directionalJet,
      zero_mul,mul_zero,zero_add,add_zero,zero_div]
    dsimp only [pathGenerator,directionalJet]
    ring
  rw [he]
  exact (inner_abs_seven_add_le _ _ _ _ _ _ _).trans
    ((add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add hgen hmix) hhess) hdir) hscore) hmass) hlast).trans_eq (by ring))

end SKBarriers2.StepCalculus
