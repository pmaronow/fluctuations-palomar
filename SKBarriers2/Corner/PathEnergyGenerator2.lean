module

public import SKBarriers2.Analysis.StepStability
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

def generatorProductJet (m dm ddm : ℝ) (A B : Fin 3 → E → ℝ) : Fin 3 → E → ℝ :=
  ![fun x => m*A 0 x*B 0 x,
    fun x => dm*A 0 x*B 0 x+m*A 1 x*B 0 x+m*A 0 x*B 1 x,
    fun x => ddm*A 0 x*B 0 x+2*(dm*A 1 x*B 0 x)+2*(dm*A 0 x*B 1 x)+
      m*A 2 x*B 0 x+2*(m*A 1 x*B 1 x)+m*A 0 x*B 2 x]

private theorem qBoundedJets_scaled_product {n : ℕ} {H C c : ℝ} {a b : E → ℝ}
    (ha : QBoundedJets n H a) (hb : QBoundedJets n C b) (hc : |c| ≤ 1) :
    QBoundedJets n ((2:ℝ)^n*H*C) (fun x => c*a x*b x) := by
  have H' := (ha.mul hb).const_smul c
  have H'' := H'.mono (mul_le_of_le_one_left (ha.mul hb).nonneg hc)
  convert H'' using 1
  funext x
  simp only [smul_eq_mul]
  ring

theorem qBoundedJets_generatorProductJet {H C m dm ddm : ℝ} {A B : Fin 3 → E → ℝ}
    (hA₀ : QBoundedJets 4 H (A 0)) (hA₁ : QBoundedJets 2 H (A 1))
    (hA₂ : QBoundedJets 0 H (A 2))
    (hB₀ : QBoundedJets 4 C (B 0)) (hB₁ : QBoundedJets 2 C (B 1))
    (hB₂ : QBoundedJets 0 C (B 2))
    (hm : |m| ≤ 1) (hdm : |dm| ≤ 1) (hddm : |ddm| ≤ 1) :
    QBoundedJets 4 (16*H*C) (generatorProductJet m dm ddm A B 0) ∧
      QBoundedJets 2 (16*H*C) (generatorProductJet m dm ddm A B 1) ∧
      QBoundedJets 0 (16*H*C) (generatorProductJet m dm ddm A B 2) := by
  have hH := hA₀.nonneg
  have hC := hB₀.nonneg
  have hzero := qBoundedJets_scaled_product hA₀ hB₀ hm
  have hfirst := ((qBoundedJets_scaled_product (hA₀.of_le (by norm_num : 2 ≤ 4))
    (hB₀.of_le (by norm_num : 2 ≤ 4)) hdm).add
      (qBoundedJets_scaled_product hA₁ (hB₀.of_le (by norm_num : 2 ≤ 4)) hm)).add
        (qBoundedJets_scaled_product (hA₀.of_le (by norm_num : 2 ≤ 4)) hB₁ hm)
  have hsecond := (((((qBoundedJets_scaled_product (hA₀.of_le (by norm_num : 0 ≤ 4))
    (hB₀.of_le (by norm_num : 0 ≤ 4)) hddm).add
      ((qBoundedJets_scaled_product (hA₁.of_le (by norm_num : 0 ≤ 2))
        (hB₀.of_le (by norm_num : 0 ≤ 4)) hdm).const_smul 2)).add
      ((qBoundedJets_scaled_product (hA₀.of_le (by norm_num : 0 ≤ 4))
        (hB₁.of_le (by norm_num : 0 ≤ 2)) hdm).const_smul 2)).add
      (qBoundedJets_scaled_product hA₂ (hB₀.of_le (by norm_num : 0 ≤ 4)) hm)).add
      ((qBoundedJets_scaled_product (hA₁.of_le (by norm_num : 0 ≤ 2))
        (hB₁.of_le (by norm_num : 0 ≤ 2)) hm).const_smul 2)).add
      (qBoundedJets_scaled_product (hA₀.of_le (by norm_num : 0 ≤ 4)) hB₂ hm)
  refine ⟨?_,?_,?_⟩
  · convert hzero using 1 <;> norm_num [generatorProductJet]
  · convert hfirst.mono (show
      (2:ℝ)^2*H*C+(2:ℝ)^2*H*C+(2:ℝ)^2*H*C ≤ 16*H*C by
        nlinarith only [mul_nonneg hH hC]) using 1
    funext x
    simp only [generatorProductJet,Matrix.cons_val_one,Matrix.cons_val_zero]
  · convert hsecond.mono (show
      (2:ℝ)^0*H*C+|2| *((2:ℝ)^0*H*C)+|2| *((2:ℝ)^0*H*C)+
        (2:ℝ)^0*H*C+|2| *((2:ℝ)^0*H*C)+(2:ℝ)^0*H*C ≤ 16*H*C by
          norm_num
          nlinarith only [mul_nonneg hH hC]) using 1
    funext x
    norm_num [generatorProductJet,smul_eq_mul]

def generatorDirectionalJet (F F₁ F₂ : E → ℝ) (v v₁ v₂ : E) : Fin 3 → E → ℝ :=
  ![fun x => fderiv ℝ F x v,
    fun x => fderiv ℝ F₁ x v+fderiv ℝ F x v₁,
    fun x => fderiv ℝ F₂ x v+2*fderiv ℝ F₁ x v₁+fderiv ℝ F x v₂]

theorem qBoundedJets_generatorDirectionalJet {H d : ℝ} {F F₁ F₂ : E → ℝ}
    (hF : QBoundedJets 5 H F) (hF₁ : QBoundedJets 3 H F₁)
    (hF₂ : QBoundedJets 1 H F₂) (hd : 0 ≤ d) (v v₁ v₂ : E)
    (hv : ‖v‖ ≤ d) (hv₁ : ‖v₁‖ ≤ d) (hv₂ : ‖v₂‖ ≤ d) :
    QBoundedJets 4 (4*H*d) (generatorDirectionalJet F F₁ F₂ v v₁ v₂ 0) ∧
      QBoundedJets 2 (4*H*d) (generatorDirectionalJet F F₁ F₂ v v₁ v₂ 1) ∧
      QBoundedJets 0 (4*H*d) (generatorDirectionalJet F F₁ F₂ v v₁ v₂ 2) := by
  have hH := hF.nonneg
  have hzero (w : E) (hw : ‖w‖ ≤ d) :
      QBoundedJets 4 (H*d) (fun x => fderiv ℝ F x w) :=
    (hF.derivativeJets.apply_const w).mono (mul_le_mul_of_nonneg_left hw hH)
  have hfirst (w : E) (hw : ‖w‖ ≤ d) :
      QBoundedJets 2 (H*d) (fun x => fderiv ℝ F₁ x w) :=
    (hF₁.derivativeJets.apply_const w).mono (mul_le_mul_of_nonneg_left hw hH)
  have hsecond := (hF₂.derivativeJets.apply_const v).mono
    (mul_le_mul_of_nonneg_left hv hH)
  refine ⟨?_,?_,?_⟩
  · convert (hzero v hv).mono (show H*d ≤ 4*H*d by nlinarith only [mul_nonneg hH hd]) using 1
    funext x
    norm_num [generatorDirectionalJet]
  · have H' := (hfirst v hv).add ((hzero v₁ hv₁).of_le (by norm_num : 2 ≤ 4))
    convert H'.mono (show H*d+H*d ≤ 4*H*d by nlinarith only [mul_nonneg hH hd]) using 1
    funext x
    norm_num [generatorDirectionalJet]
  · have H' := (hsecond.add (((hfirst v₁ hv₁).of_le (by norm_num : 0 ≤ 2)).const_smul 2)).add
      ((hzero v₂ hv₂).of_le (by norm_num : 0 ≤ 4))
    convert H' using 1
    · norm_num
      ring
    · funext x
      norm_num [generatorDirectionalJet,smul_eq_mul]

theorem qBoundedJets_generatorComparisonJet {H C e m dm ddm : ℝ}
    {F F₁ F₂ g a q : E → ℝ}
    (hF : QBoundedJets 5 H F) (hF₁ : QBoundedJets 3 H F₁)
    (hF₂ : QBoundedJets 1 H F₂)
    (hg : QBoundedJets 5 C g) (ha : QBoundedJets 3 C a) (hq : QBoundedJets 1 C q)
    (hm : |m| ≤ 1) (hdm : |dm| ≤ 1) (hddm : |ddm| ≤ 1)
    (v v₁ v₂ : E) (he : ‖v‖^2+‖v₁‖^2+‖v₂‖^2 ≤ e) :
    let A := generatorDirectionalJet F F₁ F₂ v v₁ v₂
    let B := generatorDirectionalJet g a q v v₁ v₂
    QBoundedJets 4 (256*H*C*e) (generatorProductJet m dm ddm A B 0) ∧
      QBoundedJets 2 (256*H*C*e) (generatorProductJet m dm ddm A B 1) ∧
      QBoundedJets 0 (256*H*C*e) (generatorProductJet m dm ddm A B 2) := by
  have he0 : 0 ≤ e := by nlinarith only [he,sq_nonneg ‖v‖,sq_nonneg ‖v₁‖,sq_nonneg ‖v₂‖]
  have hnorm (w : E) (hw : ‖w‖^2 ≤ e) : ‖w‖ ≤ Real.sqrt e :=
    Real.le_sqrt_of_sq_le hw
  have hv : ‖v‖ ≤ Real.sqrt e := hnorm v (by nlinarith only [he,sq_nonneg ‖v₁‖,sq_nonneg ‖v₂‖])
  have hv₁ : ‖v₁‖ ≤ Real.sqrt e := hnorm v₁ (by nlinarith only [he,sq_nonneg ‖v‖,sq_nonneg ‖v₂‖])
  have hv₂ : ‖v₂‖ ≤ Real.sqrt e := hnorm v₂ (by nlinarith only [he,sq_nonneg ‖v‖,sq_nonneg ‖v₁‖])
  obtain ⟨hA₀,hA₁,hA₂⟩ := qBoundedJets_generatorDirectionalJet hF hF₁ hF₂
    (Real.sqrt_nonneg e) v v₁ v₂ hv hv₁ hv₂
  obtain ⟨hB₀,hB₁,hB₂⟩ := qBoundedJets_generatorDirectionalJet hg ha hq
    (Real.sqrt_nonneg e) v v₁ v₂ hv hv₁ hv₂
  have H' := qBoundedJets_generatorProductJet hA₀ hA₁ hA₂ hB₀ hB₁ hB₂ hm hdm hddm
  convert H' using 1 <;>
    rw [show 16*(4*H*Real.sqrt e)*(4*C*Real.sqrt e) =
      256*H*C*(Real.sqrt e)^2 by ring,Real.sq_sqrt he0]

theorem generatorProductJet_eq_iteratedDeriv {m : ℝ → ℝ} {A B : ℝ → E → ℝ}
    {k : ℝ} (hm : ContDiffAt ℝ 2 m k)
    (hA : ∀ x, ContDiffAt ℝ 2 (fun t => A t x) k)
    (hB : ∀ x, ContDiffAt ℝ 2 (fun t => B t x) k) (c : Fin 3) (x : E) :
    generatorProductJet (m k) (deriv m k) (deriv (deriv m) k)
      (fun c x => iteratedDeriv c.val (fun t => A t x) k)
      (fun c x => iteratedDeriv c.val (fun t => B t x) k) c x =
      iteratedDeriv c.val (fun t => m t*A t x*B t x) k := by
  let U := fun t => m t*A t x
  have hU : ContDiffAt ℝ 2 U k := hm.mul (hA x)
  have hU₁ : deriv U k = deriv m k*A k x+m k*deriv (fun t => A t x) k :=
    deriv_fun_mul (hm.differentiableAt (by norm_num)) ((hA x).differentiableAt (by norm_num))
  have hU₂ : iteratedDeriv 2 U k =
      deriv (deriv m) k*A k x+2*deriv m k*deriv (fun t => A t x) k+
        m k*deriv (deriv (fun t => A t x)) k := by
    rw [iteratedDeriv_fun_mul hm (hA x)]
    norm_num [Finset.sum_range_succ,iteratedDeriv_succ,iteratedDeriv_zero]
    ring
  fin_cases c
  · simp [generatorProductJet]
  · change generatorProductJet _ _ _ _ _ 1 x = iteratedDeriv 1 (fun t => U t*B t x) k
    rw [iteratedDeriv_fun_mul (hU.of_le (by norm_num)) ((hB x).of_le (by norm_num))]
    norm_num [Finset.sum_range_succ,iteratedDeriv_one,generatorProductJet,iteratedDeriv_zero]
    rw [hU₁]
    dsimp only [U]
    ring
  · change generatorProductJet _ _ _ _ _ 2 x = iteratedDeriv 2 (fun t => U t*B t x) k
    rw [iteratedDeriv_fun_mul hU (hB x)]
    norm_num [Finset.sum_range_succ,generatorProductJet,iteratedDeriv_zero]
    rw [hU₂]
    simp only [hU₁,iteratedDeriv_succ,iteratedDeriv_zero]
    dsimp only [U]
    ring

def terminalGradientSquareJet (f : E → ℝ) (w w₁ w₂ : E) : Fin 3 → E → ℝ :=
  ![fun x => (fderiv ℝ f x w)^2,
    fun x => 2*fderiv ℝ f x w*fderiv ℝ f x w₁,
    fun x => 2*(fderiv ℝ f x w₁)^2+2*fderiv ℝ f x w*fderiv ℝ f x w₂]

theorem qBoundedJets_terminalGradientSquareJet {B d : ℝ} {f : E → ℝ}
    (hf : QPotential 9 B f) (w w₁ w₂ : E)
    (hw : ‖w‖ ≤ d) (hw₁ : ‖w₁‖ ≤ d) (hw₂ : ‖w₂‖ ≤ d) (c : Fin 3) :
    QBoundedJets 8 (1024*B^2*d^2) (terminalGradientSquareJet f w w₁ w₂ c) := by
  have hB := hf.nonneg
  have hdw (v : E) (hv : ‖v‖ ≤ d) : QBoundedJets 8 (B*d)
      (fun x => fderiv ℝ f x v) :=
    (hf.derivativeJets.apply_const v).mono (mul_le_mul_of_nonneg_left hv hB)
  have hww := (hdw w hw).mul (hdw w hw)
  have hww₁ := ((hdw w hw).mul (hdw w₁ hw₁)).const_smul 2
  have hsecond := (((hdw w₁ hw₁).mul (hdw w₁ hw₁)).const_smul 2).add
    (((hdw w hw).mul (hdw w₂ hw₂)).const_smul 2)
  fin_cases c
  · convert hww.mono (show (2:ℝ)^8*(B*d)*(B*d) ≤ 1024*B^2*d^2 by
      norm_num; nlinarith only [sq_nonneg (B*d)]) using 1
    funext x
    norm_num [terminalGradientSquareJet]
    ring
  · convert hww₁.mono (show |2| *((2:ℝ)^8*(B*d)*(B*d)) ≤ 1024*B^2*d^2 by
      norm_num; nlinarith only [sq_nonneg (B*d)]) using 1
    funext x
    norm_num [terminalGradientSquareJet,smul_eq_mul]
    ring
  · convert hsecond using 1
    · norm_num
      ring
    · funext x
      norm_num [terminalGradientSquareJet,smul_eq_mul]
      ring

theorem terminalGradientSquareJet_eq_iteratedDeriv {f : E → ℝ} {w : ℝ → E}
    {k : ℝ} (hw : ContDiffAt ℝ 2 w k) (c : Fin 3) (x : E) :
    terminalGradientSquareJet f (w k) (deriv w k) (deriv (deriv w) k) c x =
      iteratedDeriv c.val (fun t => (fderiv ℝ f x (w t))^2) k := by
  let L := fderiv ℝ f x
  let A := fun t => L (w t)
  have hA : ContDiffAt ℝ 2 A k := L.contDiff.contDiffAt.comp k hw
  have he (n : ℕ) (hn : n ≤ 2) : iteratedDeriv n A k = L (iteratedDeriv n w k) := by
    simp only [iteratedDeriv_eq_iteratedFDeriv]
    have H' := L.iteratedFDeriv_comp_left (hw.of_le (by exact_mod_cast hn)) le_rfl
    exact congrArg (fun T => T (fun _ : Fin n => (1:ℝ))) H'
  have he₁ : deriv A k = L (deriv w k) := by simpa only [iteratedDeriv_one] using he 1 (by norm_num)
  have he₂ : iteratedDeriv 2 A k = L (deriv (deriv w) k) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using he 2 (by norm_num)
  fin_cases c
  · norm_num [terminalGradientSquareJet,iteratedDeriv_zero]
  · simp only [pow_two]
    change terminalGradientSquareJet _ _ _ _ 1 x = iteratedDeriv 1 (fun t => A t*A t) k
    rw [iteratedDeriv_fun_mul (hA.of_le (by norm_num)) (hA.of_le (by norm_num))]
    norm_num [terminalGradientSquareJet,Finset.sum_range_succ,iteratedDeriv_one,iteratedDeriv_zero]
    rw [he₁]
    dsimp only [A,L]
    ring
  · simp only [pow_two]
    change terminalGradientSquareJet _ _ _ _ 2 x = iteratedDeriv 2 (fun t => A t*A t) k
    rw [iteratedDeriv_fun_mul hA hA]
    norm_num [terminalGradientSquareJet,Finset.sum_range_succ,iteratedDeriv_zero]
    rw [he₂]
    simp only [he₁]
    dsimp only [A,L]
    ring

end SKBarriers2.StepCalculus
