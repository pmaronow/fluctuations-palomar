module

public import ScalarLowClockCalibration
public import SKFluctuationsOAI.Probability.SKFluctuations.ScalarFlattenCurvature

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy
open GaussianCalculus Scalar
set_option maxHeartbeats 4000000

theorem scalar_square_evolved_second_abs_le_34 {T m : ℝ} (hT : 0 < T)
    (alpha : boundedMassProfiles) (q t : ℝ) (hm : 0 < m) (hm1 : m ≤ 1)
    (x : Fin 1 → ℝ) :
    |(((scalarTailJet hT alpha q).square).evolve hm t).A₂ 0 x| ≤ 34 := by
  let R:=scalarTailJet hT alpha q
  let J:=R.square
  have hG (y : Fin 1 → ℝ) : |J.G 0 y| ≤ 1 := scalarTailJet_G_bound hT alpha q 0 y
  have hH (y : Fin 1 → ℝ) : |J.H 0 y| ≤ 1 := scalarTailJet_H_abs_le hT alpha q y
  have hRA (y : Fin 1 → ℝ) : |R.A y| ≤ 1 := scalarTailJet_G_bound hT alpha q 0 y
  have hRA1 (y : Fin 1 → ℝ) : |R.A₁ 0 y| ≤ 1 := scalarTailJet_H_abs_le hT alpha q y
  have hRA2 (y : Fin 1 → ℝ) : |R.A₂ 0 y| ≤ 8 := by
    have H:=scalarProfileJet_bound (rescaledMassProfile alpha hT)
      (fun s=>(alpha.property.1 (s/T)).2) (T*q)
      (Real.toNNReal (T*(1-q))) 2 (y 0)
    norm_num [R,scalarTailJet,scalarProfileHeatJet,ReplicaTree.attachmentCount] at H ⊢
    exact H
  have hA (y : Fin 1 → ℝ) : |J.A y| ≤ 1 := by
    dsimp only [J,HeatJet.square]
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg _) (hRA y) 2).trans_eq (by norm_num)
  have hA1 (y : Fin 1 → ℝ) : |J.A₁ 0 y| ≤ 2 := by
    dsimp only [J,HeatJet.square]
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have H:=mul_le_mul (hRA y) (hRA1 y) (abs_nonneg _) zero_le_one
    nlinarith only [H]
  have hA2 (y : Fin 1 → ℝ) : |J.A₂ 0 y| ≤ 18 := by
    dsimp only [J,HeatJet.square]
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have H1:=pow_le_pow_left₀ (abs_nonneg _) (hRA1 y) 2
    have H2:=mul_le_mul (hRA y) (hRA2 y) (abs_nonneg _) zero_le_one
    have H:=(abs_add_le ((R.A₁ 0 y)^2) (R.A y*R.A₂ 0 y)).trans
      (add_le_add (by simpa only [abs_pow,one_pow] using H1)
        (by simpa only [abs_mul,one_mul] using H2))
    nlinarith only [H]
  have hAG (y : Fin 1 → ℝ) : |J.A y*J.G 0 y| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hA y) (hG y) (abs_nonneg _) zero_le_one
  have hAG1 (y : Fin 1 → ℝ) : |J.A₁ 0 y*J.G 0 y+J.A y*J.H 0 y| ≤ 3 := by
    have H1:=mul_le_mul (hA1 y) (hG y) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
    have H2:=mul_le_mul (hA y) (hH y) (abs_nonneg _) zero_le_one
    have H:=(abs_add_le (J.A₁ 0 y*J.G 0 y) (J.A y*J.H 0 y)).trans (add_le_add
      (by simpa only [abs_mul,mul_one] using H1)
      (by simpa only [abs_mul,one_mul] using H2))
    norm_num at H
    exact H
  have hfirst : |clockGradient m J.F (J.G 0) (J.A₁ 0) (J.A₂ 0) t x| ≤ 22 := by
    have H:=clockGradient_abs_le J.lipschitz (J.smoothG 0) (J.smoothA₁ 0)
      (J.smoothA₂ 0) (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 2)
      hG hA1 hA2 m t x
    rw [abs_of_pos hm] at H
    linarith
  have hsecond : |clockGradient m J.F (J.G 0) (fun y=>J.A y*J.G 0 y)
      (fun y=>J.A₁ 0 y*J.G 0 y+J.A y*J.H 0 y) t x| ≤ 5 := by
    have H:=clockGradient_abs_le J.lipschitz (J.smoothG 0)
      (J.smoothA.mul (J.smoothG 0))
      (((J.smoothA₁ 0).mul (J.smoothG 0)).add (J.smoothA.mul (J.smoothH 0)))
      zero_le_one zero_le_one hG hAG hAG1 m t x
    rw [abs_of_pos hm] at H
    linarith
  have hthird : |clockGradient m J.F (J.G 0) J.A (J.A₁ 0) t x| ≤ 4 := by
    have H:=clockGradient_abs_le J.lipschitz (J.smoothG 0) J.smoothA
      (J.smoothA₁ 0) zero_le_one zero_le_one hG hA hA1 m t x
    rw [abs_of_pos hm] at H
    linarith
  have hfourth : |clockGradient m J.F (J.G 0) (J.G 0) (J.H 0) t x| ≤ 3 := by
    have H:=clockGradient_abs_le J.lipschitz (J.smoothG 0) (J.smoothG 0)
      (J.smoothH 0) zero_le_one zero_le_one hG hG hH m t x
    rw [abs_of_pos hm] at H
    linarith
  have hTG:=clockTest_abs_le J.lipschitz (J.smoothG 0) hG m t x
  have hTA:=clockTest_abs_le J.lipschitz J.smoothA hA m t x
  have hprod1 : |clockGradient m J.F (J.G 0) J.A (J.A₁ 0) t x*
      clockTest m J.F (J.G 0) t x| ≤ 4 := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul hthird hTG (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 4)
  have hprod2 : |clockTest m J.F J.A t x*
      clockGradient m J.F (J.G 0) (J.G 0) (J.H 0) t x| ≤ 3 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul hTA hfourth (abs_nonneg _) zero_le_one
  have hinner := (abs_sub _ _).trans (add_le_add hsecond
    ((abs_add_le _ _).trans (add_le_add hprod1 hprod2)))
  have hscaled : |m*(clockGradient m J.F (J.G 0) (fun y=>J.A y*J.G 0 y)
      (fun y=>J.A₁ 0 y*J.G 0 y+J.A y*J.H 0 y) t x-
      (clockGradient m J.F (J.G 0) J.A (J.A₁ 0) t x*clockTest m J.F (J.G 0) t x+
       clockTest m J.F J.A t x*clockGradient m J.F (J.G 0) (J.G 0) (J.H 0) t x))| ≤ 12 := by
    rw [abs_mul,abs_of_pos hm]
    have H:=mul_le_mul hm1 hinner (abs_nonneg _) zero_le_one
    norm_num at H
    exact H
  change |clockSecond m J.F (J.G 0) (J.H 0) J.A (J.A₁ 0) (J.A₂ 0) t x| ≤ 34
  unfold clockSecond
  exact (abs_add_le _ _).trans (by linarith [hfirst,hscaled])

theorem scalar_low_flattening_curvature_bound {T q m A W : ℝ} (hT : 0 < T)
    (alpha : boundedMassProfiles) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hm : 0 < m) (hm1 : m ≤ 1) (hW : 0 ≤ W) (hA : 0 ≤ A)
    (hmass : alpha.val q ≤ A*W) (hmcap : m ≤ A*W)
    (hcont : ∀s,ContinuousWithinAt alpha.val (Ici s) s) :
    |((scalarTailJet hT alpha q).evolve hm (T*q)).H 0 0-
      (scalarTailJet hT alpha 0).H 0 0| ≤ 17*T*A*W*q := by
  have H:=scalarTailJet_flatten_curvature_difference hT (q:=0) le_rfl hq hq1 alpha hm hm1 hcont 0
  change ((scalarTailJet hT alpha q).evolve hm (T*q)).H 0 0-
    ((scalarTailJet hT alpha 0).evolve hm (T*0)).H 0 0=
      T/2*(∫s in (0:ℝ)..q,(m-alpha.val s)*
        (((scalarTailJet hT alpha s).square).evolve hm (T*s)).A₂ 0 0) at H
  have hzero : ((scalarTailJet hT alpha 0).evolve hm (T*0)).H 0 0=
      (scalarTailJet hT alpha 0).H 0 0 := by
    apply congrFun (HeatJet.H_congr_F _) 0
    funext x
    simp only [HeatJet.evolve,mul_zero,clockContinuation_zero hm.ne']
  rw [hzero] at H
  rw [H,abs_mul,abs_of_pos (div_pos hT (by norm_num : (0:ℝ) < 2))]
  have hbound : ∀s∈Icc (0:ℝ) q,
      |(m-alpha.val s)*(((scalarTailJet hT alpha s).square).evolve hm (T*s)).A₂ 0 0| ≤ 34*A*W := by
    intro s hs
    have hmasss := (alpha.property.2 hs.2).trans hmass
    have hmabs : |m-alpha.val s| ≤ A*W :=
      abs_le.mpr ⟨by linarith [(alpha.property.1 s).1],by linarith [(alpha.property.1 s).1]⟩
    rw [abs_mul]
    have hh:=scalar_square_evolved_second_abs_le_34 hT alpha s (T*s) hm hm1 0
    have HH:=mul_le_mul hmabs hh (abs_nonneg _) (mul_nonneg hA hW)
    nlinarith only [HH]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=q) (C:=34*A*W)
    (f:=fun s=>(m-alpha.val s)*(((scalarTailJet hT alpha s).square).evolve hm (T*s)).A₂ 0 0)
    (fun s hs=>by
      rw [uIoc_of_le hq] at hs
      rw [Real.norm_eq_abs]
      exact hbound s ⟨hs.1.le,hs.2⟩)
  simp only [Real.norm_eq_abs,sub_zero,abs_of_nonneg hq] at hi
  nlinarith [mul_le_mul_of_nonneg_left hi hT.le]

end OAI.SKFluctuations.Hierarchy
