module

public import SKBarriers2.Corner.MassSensitivity
public import SKBarriers2.Corner.MassVariationAlgebra
public import SKBarriers2.Corner.CoreIdentity
public import SKBarriers2.Analysis.StepExpansion

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
open OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def projectionMass (l : List (ℝ × Vec3)) : ℝ :=
  (l.map (fun q => q.1 * (∑ i, q.2 i) ^ 2)).sum

def quarticMass (l : List (ℝ × Vec3)) : ℝ :=
  (l.map (fun q => q.1 * (∑ i, q.2 i ^ 2) ^ 2)).sum

def massLeadingEnergy (b u chi w h : ℝ) (mu : Vec3) :
    List (ℝ × Vec3) → (Fin 3 → Fin 3 → ℝ) → ℝ
  | [], _ => 0
  | q::l, Q => q.1 *
      (u ^ 2 * (∑ i, q.2 i) ^ 2 +
        2*b*u^2*chi*(∑ i, q.2 i)*(∑ i, q.2 i*mu i) +
        4*b*h*u*w*(∑ i, q.2 i)^2 + b*chi^2*matrixQuadratic Q q.2) +
      massLeadingEnergy b u chi w h mu l (Q+rankOneMatrix q.2)

private theorem matrixQuadratic_add_constant (Q : Fin 3 → Fin 3 → ℝ)
    (v : Vec3) (s : ℝ) :
    matrixQuadratic (Q+fun _ _ => s) v = matrixQuadratic Q v + s*(∑ i, v i)^2 := by
  simp only [matrixQuadratic, Pi.add_apply, mul_add, add_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem projectionMass_eq_translation (l : List (ℝ × Vec3)) :
    projectionMass l = ∑ i, translation l i := by
  induction l with
  | nil => simp only [projectionMass, translation, List.map_nil, List.sum_nil,
      Pi.zero_apply, Finset.sum_const_zero]
  | cons q l ih =>
    change q.1*(∑ i, q.2 i)^2 + projectionMass l =
      ∑ i, (q.1 • ((∑ j, q.2 j) • q.2) + translation l) i
    rw [ih]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    ring

theorem massLeadingEnergy_penalty_cancellation (b u chi w h s : ℝ) (mu : Vec3)
    (l : List (ℝ × Vec3)) (Q : Fin 3 → Fin 3 → ℝ) :
    b/2 * massLeadingEnergy b u chi w h mu l Q -
        (b^2*chi^2/4) * matrixChainPenalty l (Q+fun _ _ => s) =
      (b*u^2/2+2*b^2*h*u*w-2*s*(b^2*chi^2/4))*projectionMass l +
        b^2*u^2*chi*(∑ i, translation l i*mu i) -
        (b^2*chi^2/4)*quarticMass l := by
  induction l generalizing Q with
  | nil => simp [massLeadingEnergy, matrixChainPenalty, chainPotentialPenalty,
      projectionMass, quarticMass, translation]
  | cons q l ih =>
    rw [massLeadingEnergy, matrixChainPenalty_cons, matrixSquare_rankOne_increment,
      matrixQuadratic_add_constant]
    have he : (Q+fun _ _ => s)+rankOneMatrix q.2 =
        (Q+rankOneMatrix q.2)+fun _ _ => s := by abel
    rw [he]
    have H := ih (Q+rankOneMatrix q.2)
    change _ = _*(q.1*(∑ i, q.2 i)^2+projectionMass l) +
      b^2*u^2*chi*(∑ i, (q.1 • ((∑ j, q.2 j) • q.2) + translation l) i*mu i) -
        (b^2*chi^2/4)*(q.1*(∑ i, q.2 i^2)^2+quarticMass l)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib]
    have hsum : (∑ i, q.1*((∑ j, q.2 j)*q.2 i)*mu i) =
        q.1*(∑ j, q.2 j)*(∑ i, q.2 i*mu i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    linear_combination H

theorem massVariation_projection (α : ℝ → ℝ) (a p s h k : ℝ) {N : ℕ}
    (hN : 0 < N) (hh : 0 ≤ h) (hp : p ∈ Icc (0 : ℝ) 1)
    (hl : OW.repairLength p k ∈ Icc (0 : ℝ) 2) :
    projectionMass (massVariationWindow α a p s h k N) =
      3*(scalarTranslation α p s h k N-4*a*h) := by
  rw [projectionMass_eq_translation, massVariation_translation α a p s h k hN hh hp hl]
  simp [ones, contrast, Fin.sum_univ_succ]
  ring

def windowLeadingEnergy (b u chi w : ℝ) (α γ : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ) : ℝ :=
  massLeadingEnergy b u chi w h (translation (OW.window γ p s h k N))
    (massVariationWindow α a p s h k N) 0

theorem windowLeadingEnergy_difference (b u chi w : ℝ) (α γ : ℝ → ℝ)
    (a p s h k : ℝ) {N : ℕ} (hN : 0 < N) (hh : 0 ≤ h)
    (hp : p ∈ Icc (0 : ℝ) 1) (hl : OW.repairLength p k ∈ Icc (0 : ℝ) 2) :
    b/2 * (windowLeadingEnergy b u chi w α γ a p s h k N -
        windowLeadingEnergy b u chi w α γ a p s h 0 N) -
      (b^2*chi^2/4)*(massVariationPenalty α a p s h k N-massVariationPenalty α a p s h 0 N) =
      3*(b*u^2/2+2*b^2*h*u*w-2*s*(b^2*chi^2/4))*
        (scalarTranslation α p s h k N-scalarTranslation α p s h 0 N) +
      b^2*u^2*chi*(
        2*k^2*zeta γ p s h N*zeta (fun t => α t-a) p s h N +
        3*(scalarTranslation γ p s h k N-scalarTranslation γ p s h 0 N)*
          (scalarTranslation α p s h k N-4*a*h) +
        3*scalarTranslation γ p s h 0 N*
          (scalarTranslation α p s h k N-scalarTranslation α p s h 0 N)) -
      (b^2*chi^2/4)*(quarticMass (massVariationWindow α a p s h k N)-
        quarticMass (massVariationWindow α a p s h 0 N)) := by
  have hl0 : OW.repairLength p 0 ∈ Icc (0 : ℝ) 2 := by norm_num [OW.repairLength]
  have Hk := massLeadingEnergy_penalty_cancellation b u chi w h s
    (translation (OW.window γ p s h k N)) (massVariationWindow α a p s h k N) 0
  have H0 := massLeadingEnergy_penalty_cancellation b u chi w h s
    (translation (OW.window γ p s h 0 N)) (massVariationWindow α a p s h 0 N) 0
  rw [massVariation_projection α a p s h k hN hh hp hl] at Hk
  rw [massVariation_projection α a p s h 0 hN hh hp hl0] at H0
  simp only [zero_add, ← massVariationPenalty_eq] at Hk H0
  have ht := massVariation_translation_contraction α γ a p s h k hN hh hp hl
  have hb : (∑ i, translation (OW.window γ p s h 0 N) i *
      (translation (massVariationWindow α a p s h k N) i-
        translation (massVariationWindow α a p s h 0 N) i)) =
      3*scalarTranslation γ p s h 0 N*
        (scalarTranslation α p s h k N-scalarTranslation α p s h 0 N) := by
    rw [window_translation γ p s h 0 N hh hp hl0,
      massVariation_translation α a p s h k hN hh hp hl,
      massVariation_translation α a p s h 0 hN hh hp hl0]
    simp [ones, contrast, Fin.sum_univ_succ]
    ring
  have hd : (∑ i, translation (massVariationWindow α a p s h k N) i*
        translation (OW.window γ p s h k N) i) -
      (∑ i, translation (massVariationWindow α a p s h 0 N) i*
        translation (OW.window γ p s h 0 N) i) =
      (∑ i, (translation (OW.window γ p s h k N)-
          translation (OW.window γ p s h 0 N)) i*
        translation (massVariationWindow α a p s h k N) i) +
      (∑ i, translation (OW.window γ p s h 0 N) i*
        (translation (massVariationWindow α a p s h k N) i-
          translation (massVariationWindow α a p s h 0 N) i)) := by
    simp only [Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
    have hcomm (v w : Vec3) : (∑ i, v i*w i) = ∑ i, w i*v i :=
      Finset.sum_congr rfl (fun i _ => mul_comm (v i) (w i))
    rw [hcomm (translation (massVariationWindow α a p s h k N)),
      hcomm (translation (massVariationWindow α a p s h 0 N))]
    ring
  rw [ht, hb] at hd
  dsimp only [windowLeadingEnergy]
  have H := congrArg (fun y : ℝ => b^2*u^2*chi*y) hd
  linear_combination Hk-H0+H

private theorem stageIntegral_interpolated (α : ℝ → ℝ) (a lam s h t len : ℝ) (N : ℕ) :
    stageIntegral (interpolatedProfile α a lam) s h N t len =
      stageIntegral (fun _ => a) s h N t len +
        lam*(stageIntegral α s h N t len-stageIntegral (fun _ => a) s h N t len) := by
  simp only [stageIntegral, interpolatedProfile, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem scalarTranslation_interpolated (α : ℝ → ℝ) (a lam p s h k : ℝ)
    {N : ℕ} (hN : 0 < N) :
    scalarTranslation (interpolatedProfile α a lam) p s h k N =
      4*a*h+lam*(scalarTranslation α p s h k N-4*a*h) := by
  unfold scalarTranslation
  simp_rw [stageIntegral_interpolated, stageIntegral_const a s h hN]
  ring

theorem zeta_interpolated (α : ℝ → ℝ) (a lam p s h : ℝ)
    {N : ℕ} (hN : 0 < N) (hp : p ≠ 2) :
    zeta (interpolatedProfile α a lam) p s h N = lam*zeta α p s h N := by
  have hc := zeta_const a p s h hN hp
  unfold zeta at hc ⊢
  simp_rw [stageIntegral_interpolated]
  linear_combination (1-lam)*hc

private theorem leadingEnergy_continuous (b u chi w h : ℝ)
    (l : List (ℝ × Vec3)) (Q : Fin 3 → Fin 3 → ℝ) :
    Continuous (fun mu => massLeadingEnergy b u chi w h mu l Q) := by
  induction l generalizing Q with
  | nil => exact continuous_const
  | cons q l ih =>
    simp only [massLeadingEnergy]
    have hc : Continuous (fun mu : Vec3 => q.1*
        (u^2*(∑ i, q.2 i)^2+2*b*u^2*chi*(∑ i, q.2 i)*(∑ i, q.2 i*mu i)+
          4*b*h*u*w*(∑ i, q.2 i)^2+b*chi^2*matrixQuadratic Q q.2)) := by fun_prop
    exact hc.add (ih (Q+rankOneMatrix q.2))

private theorem interpolatedTranslation_continuous (α : ℝ → ℝ) (a p s h k : ℝ)
    {N : ℕ} (hN : 0 < N) (hh : 0 ≤ h) (hp : p ∈ Icc (0 : ℝ) 1)
    (hl : OW.repairLength p k ∈ Icc (0 : ℝ) 2) :
    Continuous (fun lam => translation (OW.window (interpolatedProfile α a lam) p s h k N)) := by
  have he (lam : ℝ) := window_translation (interpolatedProfile α a lam) p s h k N hh hp hl
  simp_rw [he, scalarTranslation_interpolated α a _ p s h k hN,
    zeta_interpolated α a _ p s h hN (by linarith [hp.2])]
  fun_prop

private theorem integral_affine (A B : ℝ) :
    (∫ lam in (0 : ℝ)..1, A+lam*B) = A+B/2 := by
  have hc : Continuous (fun lam : ℝ => lam*B) := continuous_id.mul_const B
  rw [intervalIntegral.integral_add (f := fun _ : ℝ => A) (g := fun lam : ℝ => lam*B)
    intervalIntegrable_const (hc.intervalIntegrable 0 1),
    intervalIntegral.integral_const, intervalIntegral.integral_mul_const, integral_id]
  ring

theorem integrated_windowLeadingEnergy (b u chi w : ℝ) (α : ℝ → ℝ)
    (a p s h k : ℝ) {N : ℕ} (hN : 0 < N) (hh : 0 ≤ h)
    (hp : p ∈ Icc (0 : ℝ) 1) (hl : OW.repairLength p k ∈ Icc (0 : ℝ) 2) :
    b/2 * (∫ lam in (0 : ℝ)..1,
      windowLeadingEnergy b u chi w α (interpolatedProfile α a lam) a p s h k N -
        windowLeadingEnergy b u chi w α (interpolatedProfile α a lam) a p s h 0 N) -
      (b^2*chi^2/4)*(massVariationPenalty α a p s h k N-massVariationPenalty α a p s h 0 N) =
      3*(b*u^2/2+2*b^2*h*u*w-2*s*(b^2*chi^2/4))*
        (scalarTranslation α p s h k N-scalarTranslation α p s h 0 N) +
      b^2*u^2*chi*(k^2*zeta α p s h N^2+
        (3/2:ℝ)*(scalarTranslation α p s h k N^2-scalarTranslation α p s h 0 N^2)) -
      (b^2*chi^2/4)*(quarticMass (massVariationWindow α a p s h k N)-
        quarticMass (massVariationWindow α a p s h 0 N)) := by
  let A := b*u^2/2+2*b^2*h*u*w-2*s*(b^2*chi^2/4)
  let B := b^2*u^2*chi
  let D := scalarTranslation α p s h k N-scalarTranslation α p s h 0 N
  let P := massVariationPenalty α a p s h k N-massVariationPenalty α a p s h 0 N
  let J := quarticMass (massVariationWindow α a p s h k N)-
    quarticMass (massVariationWindow α a p s h 0 N)
  let C := 3*A*D+B*(12*a*h*D)-(b^2*chi^2/4)*J
  let R := B*(2*k^2*zeta α p s h N^2+
    3*D*(scalarTranslation α p s h k N+scalarTranslation α p s h 0 N-8*a*h))
  let E := fun lam =>
    windowLeadingEnergy b u chi w α (interpolatedProfile α a lam) a p s h k N -
      windowLeadingEnergy b u chi w α (interpolatedProfile α a lam) a p s h 0 N
  have he (lam : ℝ) : b/2*E lam-(b^2*chi^2/4)*P = C+lam*R := by
    have H := windowLeadingEnergy_difference b u chi w α (interpolatedProfile α a lam)
      a p s h k hN hh hp hl
    rw [scalarTranslation_interpolated α a lam p s h k hN,
      scalarTranslation_interpolated α a lam p s h 0 hN,
      zeta_interpolated α a lam p s h hN (by linarith [hp.2]),
      ← zeta_centered α a p s h hN (by linarith [hp.2])] at H
    apply H.trans
    dsimp only [A, B, C, R, D, J]
    ring
  have hl0 : OW.repairLength p 0 ∈ Icc (0 : ℝ) 2 := by norm_num [OW.repairLength]
  have hEc : Continuous E :=
    ((leadingEnergy_continuous b u chi w h _ 0).comp
      (interpolatedTranslation_continuous α a p s h k hN hh hp hl)).sub
    ((leadingEnergy_continuous b u chi w h _ 0).comp
      (interpolatedTranslation_continuous α a p s h 0 hN hh hp hl0))
  have H : (∫ lam in (0 : ℝ)..1, b/2*E lam-(b^2*chi^2/4)*P) = C+R/2 := by
    rw [intervalIntegral.integral_congr (fun lam _ => he lam), integral_affine]
  rw [intervalIntegral.integral_sub ((hEc.const_mul (b/2)).intervalIntegrable 0 1)
    intervalIntegrable_const, intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at H
  change b/2*(∫ lam in (0 : ℝ)..1, E lam)-(b^2*chi^2/4)*P = _
  calc
    _ = C+R/2 := by simpa only [sub_zero, one_smul] using H
    _ = _ := by dsimp only [A, B, C, R, D, J]; ring

theorem integrated_windowLeadingEnergy_tendsto (b u chi w : ℝ) (α : ℝ → ℝ)
    (a p s h k S Z : ℝ) (hh : 0 ≤ h) (hp : p ∈ Icc (0 : ℝ) 1)
    (hl : OW.repairLength p k ∈ Icc (0 : ℝ) 2)
    (hSk : Tendsto (fun N => scalarTranslation α p s h k N) atTop (𝓝 S))
    (hS0 : Tendsto (fun N => scalarTranslation α p s h 0 N) atTop (𝓝 S))
    (hZ : Tendsto (fun N => zeta α p s h N) atTop (𝓝 Z))
    (hJ : Tendsto (fun N => quarticMass (massVariationWindow α a p s h k N)-
      quarticMass (massVariationWindow α a p s h 0 N)) atTop (𝓝 0)) :
    Tendsto (fun N => b/2*(∫ lam in (0 : ℝ)..1,
      windowLeadingEnergy b u chi w α (interpolatedProfile α a lam) a p s h k N -
        windowLeadingEnergy b u chi w α (interpolatedProfile α a lam) a p s h 0 N) -
      (b^2*chi^2/4)*(massVariationPenalty α a p s h k N-massVariationPenalty α a p s h 0 N))
      atTop (𝓝 (b^2*u^2*chi*(k^2*Z^2))) := by
  have H := (((hSk.sub hS0).const_mul
      (3*(b*u^2/2+2*b^2*h*u*w-2*s*(b^2*chi^2/4)))).add
    ((((hZ.pow 2).const_mul (k^2)).add
      (((hSk.pow 2).sub (hS0.pow 2)).const_mul (3/2:ℝ))).const_mul (b^2*u^2*chi))).sub
        (hJ.const_mul (b^2*chi^2/4))
  have H' : Tendsto (fun N =>
      3*(b*u^2/2+2*b^2*h*u*w-2*s*(b^2*chi^2/4))*
        (scalarTranslation α p s h k N-scalarTranslation α p s h 0 N) +
      b^2*u^2*chi*(k^2*zeta α p s h N^2+
        (3/2:ℝ)*(scalarTranslation α p s h k N^2-scalarTranslation α p s h 0 N^2)) -
      (b^2*chi^2/4)*(quarticMass (massVariationWindow α a p s h k N)-
        quarticMass (massVariationWindow α a p s h 0 N)))
      atTop (𝓝 (b^2*u^2*chi*(k^2*Z^2))) := by
    simpa only [sub_self, mul_zero, zero_add, add_zero, sub_zero] using H
  apply H'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  exact (integrated_windowLeadingEnergy b u chi w α a p s h k hN hh hp hl).symm

theorem massStepDerivative_first_order {F : Vec3 → ℝ} {B a0 m : ℝ}
    (hF : QPotential 4 B F) (ha0 : 0 < a0) (hm : m ∈ Icc a0 1)
    (v x : Vec3) (hv : ‖v‖ ≤ 1) :
    |massStepDerivative m v F x-(fderiv ℝ F x v)^2/2| ≤
      (2*B*StepCalculus.pathExpansionConstant B/a0)*‖v‖^4 := by
  rw [← (vectorStep_hasDerivAt_mass (hF.boundedDerivs (by norm_num))
    (ne_of_gt (ha0.trans_le hm.1)) v x).deriv]
  exact StepCalculus.abs_mass_deriv_remainder_le hF (by norm_num) ha0 hm v x hv

private theorem incrementAverage_nonexpansive (l : List (ℝ × Vec3))
    {F G H : Vec3 → ℝ} (hF : BoundedDerivs F)
    (hGc : Continuous G) (hHc : Continuous H) (hG : HasExpGrowth G) (hH : HasExpGrowth H)
    {C : ℝ} (hb : ∀ x, |G x-H x| ≤ C) (x : Vec3) :
    |vectorIncrementAverage l F G x-vectorIncrementAverage l F H x| ≤ C := by
  have hu := vectorIncrementAverage_mono l (g := G) (h := fun y => H y+C)
    hF hGc (hHc.add continuous_const) hG
    (hH.add (HasExpGrowth.const C)) (fun y => by linarith [(abs_le.mp (hb y)).2]) x
  have hl := vectorIncrementAverage_mono l (g := H) (h := fun y => G y+C)
    hF hHc (hGc.add continuous_const) hH
    (hG.add (HasExpGrowth.const C)) (fun y => by linarith [(abs_le.mp (hb y)).1]) x
  rw [vectorIncrementAverage_add l hF hHc continuous_const hH (HasExpGrowth.const C),
    vectorIncrementAverage_const l hF] at hu
  rw [vectorIncrementAverage_add l hF hGc continuous_const hG (HasExpGrowth.const C),
    vectorIncrementAverage_const l hF] at hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem massPathSensitivity_first_order (l : List (MassPathEntry Vec3)) {f : Vec3 → ℝ}
    (hf : BoundedDerivs f) (lam : ℝ) (j : Fin l.length) {B a0 : ℝ}
    (hinner : QPotential 4 B (vectorIncrementChain (massPath (l.drop (j.val+1)) lam) f))
    (ha0 : 0 < a0) (hm : (l.get j).1+lam*(l.get j).2.1 ∈ Icc a0 1)
    (hv : ‖(l.get j).2.2‖ ≤ 1) (x : Vec3) :
    |massPathSensitivity l f lam j x - (1/2:ℝ)*
      vectorIncrementAverage (massPath (l.take j.val) lam)
        (vectorIncrementChain (massPath (l.drop j.val) lam) f)
        (fun y => (fderiv ℝ (vectorIncrementChain (massPath (l.drop (j.val+1)) lam) f)
          y (l.get j).2.2)^2) x| ≤
      (2*B*StepCalculus.pathExpansionConstant B/a0)*‖(l.get j).2.2‖^4 := by
  let F := vectorIncrementChain (massPath (l.drop (j.val+1)) lam) f
  let v := (l.get j).2.2
  let m := (l.get j).1+lam*(l.get j).2.1
  have hS := massStepDerivative_regular (hinner.boundedDerivs (by norm_num)) m v
  have hdc : Continuous (fun y => fderiv ℝ F y v) :=
    (hinner.smooth.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdE : HasExpGrowth (fun y => fderiv ℝ F y v) :=
    HasExpGrowth.of_bounded (mul_nonneg hinner.nonneg (norm_nonneg v))
      (fun y => hinner.directional_le (by norm_num) y v)
  have H := incrementAverage_nonexpansive (massPath (l.take j.val) lam)
    (F := vectorIncrementChain (massPath (l.drop j.val) lam) f)
    (G := massStepDerivative m v F) (H := fun y => (1/2:ℝ)*(fderiv ℝ F y v)^2)
    (C := (2*B*StepCalculus.pathExpansionConstant B/a0)*‖v‖^4)
    (vectorIncrementChain_regular _ hf) hS.1 (continuous_const.mul (hdc.pow 2)) hS.2
    ((HasExpGrowth.const (1/2:ℝ)).mul (hdE.pow 2))
    (fun y => by simpa only [F, m, one_div, div_eq_mul_inv, one_mul, mul_comm] using
      massStepDerivative_first_order hinner ha0 hm v y hv) x
  rw [vectorIncrementAverage_const_mul] at H
  exact H

def cornerMassVariation (β : ℝ) (α : ℝ → ℝ) (r h k : ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  (OW.boundary β α (1/2) (r-h) h k N z -
    interpolatedBoundary β α (α (r-h)) 0 (1/2) (r-h) h k N z) -
  (OW.boundary β α (1/2) (r-h) h 0 N z -
    interpolatedBoundary β α (α (r-h)) 0 (1/2) (r-h) h 0 N z)

def cornerMassVariationPenalty (α : ℝ → ℝ) (r h k : ℝ) (N : ℕ) : ℝ :=
  massVariationPenalty α (α (r-h)) (1/2) (r-h) h k N -
    massVariationPenalty α (α (r-h)) (1/2) (r-h) h 0 N

def WindowMassRegularity (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ) : Prop :=
  MassPathRegular (windowMassPath β α a p s h k N) (massVariationTerminal β α s h) ∧
    ∀ lam ∈ Icc (0 : ℝ) 1, ∀ q ∈ windowMassPath β α a p s h k N,
      q.1+lam*q.2.1 ≠ 0

theorem massPathRegular_of_windowMassRegularity {β : ℝ} {α : ℝ → ℝ}
    {a p s h k : ℝ} {N : ℕ} (hA : WindowMassRegularity β α a p s h k N) :
    MassPathRegular (windowMassPath β α a p s h k N) (massVariationTerminal β α s h) := by
  exact hA.1

theorem interpolatedBoundary_sub_eq_integral_of_A (β : ℝ) (α : ℝ → ℝ)
    (a p s h k : ℝ) (N : ℕ)
    (hPhi : BoundedDerivs (Phi β α (s+4*h)))
    (hA : WindowMassRegularity β α a p s h k N) (z : ℝ) :
    OW.boundary β α p s h k N z-interpolatedBoundary β α a 0 p s h k N z =
      ∫ lam in (0 : ℝ)..1,
        ∑ j : Fin (windowMassPath β α a p s h k N).length,
          ((windowMassPath β α a p s h k N).get j).2.1 *
            massPathSensitivity (windowMassPath β α a p s h k N)
              (massVariationTerminal β α s h) lam j (fun _ => z) := by
  exact interpolatedBoundary_sub_eq_integral β α a p s h k N
    (massVariationTerminal_regular β α s h hPhi)
    (massPathRegular_of_windowMassRegularity hA) hA.2 z

theorem cornerMassVariation_eq_integral_difference (β : ℝ) (α : ℝ → ℝ)
    (r h k : ℝ) (N : ℕ)
    (hf : BoundedDerivs (massVariationTerminal β α (r-h) h))
    (hRk : WindowMassRegularity β α (α (r-h)) (1/2) (r-h) h k N)
    (hR0 : WindowMassRegularity β α (α (r-h)) (1/2) (r-h) h 0 N) (z : ℝ) :
    cornerMassVariation β α r h k N z =
      (∫ lam in (0 : ℝ)..1,
        ∑ j : Fin (windowMassPath β α (α (r-h)) (1/2) (r-h) h k N).length,
          ((windowMassPath β α (α (r-h)) (1/2) (r-h) h k N).get j).2.1 *
            massPathSensitivity (windowMassPath β α (α (r-h)) (1/2) (r-h) h k N)
              (massVariationTerminal β α (r-h) h) lam j (fun _ => z)) -
      (∫ lam in (0 : ℝ)..1,
        ∑ j : Fin (windowMassPath β α (α (r-h)) (1/2) (r-h) h 0 N).length,
          ((windowMassPath β α (α (r-h)) (1/2) (r-h) h 0 N).get j).2.1 *
            massPathSensitivity (windowMassPath β α (α (r-h)) (1/2) (r-h) h 0 N)
              (massVariationTerminal β α (r-h) h) lam j (fun _ => z)) := by
  unfold cornerMassVariation
  rw [interpolatedBoundary_sub_eq_integral β α (α (r-h)) (1/2) (r-h) h k N hf hRk.1 hRk.2,
    interpolatedBoundary_sub_eq_integral β α (α (r-h)) (1/2) (r-h) h 0 N hf hR0.1 hR0.2]

theorem cornerV_massVariation_split (β : ℝ) (α : ℝ → ℝ) (r h k : ℝ) (N : ℕ) (z : ℝ) :
    cornerV β α r h k N z =
      (interpolatedBoundary β α (α (r-h)) 0 (1/2) (r-h) h k N z -
        interpolatedBoundary β α (α (r-h)) 0 (1/2) (r-h) h 0 N z) +
      cornerMassVariation β α r h k N z := by
  unfold cornerV cornerMassVariation
  ring

theorem cornerPenalty_massVariation_split (α : ℝ → ℝ) (r h k : ℝ) {N : ℕ}
    (hN : 0 < N) (hh : 0 ≤ h) (hl : OW.repairLength (1/2) k ∈ Icc (0 : ℝ) 2) :
    cornerPenalty α r h k N =
      h^2*α (r-h)*penaltyPolynomial (1/2) k+cornerMassVariationPenalty α r h k N := by
  have H := frozen_penalty_difference (α (r-h)) (1/2) (r-h) h k hN hh
    (by norm_num : (1/2:ℝ) ∈ Icc (0:ℝ) 1) hl
  unfold cornerPenalty cornerMassVariationPenalty massVariationPenalty
  linear_combination H

def WindowInnerJets (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ) (lam B : ℝ) : Prop :=
  ∀ j : ℕ, j < (windowMassPath β α a p s h k N).length →
    QPotential 10 B (vectorIncrementChain
      ((massPath (windowMassPath β α a p s h k N) lam).drop (j+1))
      (massVariationTerminal β α s h))

def WindowTiltJets (β : ℝ) (α : ℝ → ℝ) (a p s h : ℝ) (N : ℕ) (lam B kap : ℝ) : Prop :=
  ∀ k : ℝ, |k| ≤ kap → ∀ j : ℕ,
    j < (windowMassPath β α a p s h k N).length →
    ∀ c : ℕ, c = 1 ∨ c = 2 →
      QBddSmooth 8 (B*h) (fun x => iteratedDeriv c (fun t => vectorIncrementChain
        ((massPath (windowMassPath β α a p s h t N) lam).drop (j+1))
        (massVariationTerminal β α s h) x) k)

def windowRawDirection (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ)
    (j : Fin (windowMassPath β α a p s h k N).length) : Vec3 :=
  ((windowMassSamples p s h k N).get
    ⟨j.val, by simpa only [windowMassPath, List.length_map] using j.isLt⟩).2.2

def windowMassEnergyEntry (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ)
    (lam : ℝ) (j : Fin (windowMassPath β α a p s h k N).length) (z : ℝ) : ℝ :=
  let u := jet β α 1 (s+4*h) z
  let chi := jet β α 2 (s+4*h) z
  let w := jet β α 3 (s+4*h) z
  let v := windowRawDirection β α a p s h k N j
  let mu := translation (OW.window (interpolatedProfile α a lam) p s h k N)
  let Q := strictPrefix
    (fun i => rankOneMatrix (windowRawDirection β α a p s h k N i)) j
  u^2*(∑ i, v i)^2 + 2*β^2*u^2*chi*(∑ i, v i)*(∑ i, v i*mu i) +
    4*β^2*h*u*w*(∑ i, v i)^2 + β^2*chi^2*matrixQuadratic Q v

def MassSensitivityExpansion (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h0 kap : ℝ, 0 ≤ C ∧ 0 < h0 ∧ 0 < kap ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ k : ℝ, |k| ≤ kap →
      ∀ eps : ℝ, 0 < eps → ∀ᶠ N : ℕ in atTop,
        ∀ lam ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, ∀ j : ℕ,
          ∀ hjk : j < (windowMassPath β α (α (r-h)) (1/2) (r-h) h k N).length,
          ∀ hj0 : j < (windowMassPath β α (α (r-h)) (1/2) (r-h) h 0 N).length,
          |(massPathSensitivity (windowMassPath β α (α (r-h)) (1/2) (r-h) h k N)
                (massVariationTerminal β α (r-h) h) lam ⟨j,hjk⟩ (fun _ => z) -
              massPathSensitivity (windowMassPath β α (α (r-h)) (1/2) (r-h) h 0 N)
                (massVariationTerminal β α (r-h) h) lam ⟨j,hj0⟩ (fun _ => z)) -
            (β^2/2)*(windowMassEnergyEntry β α (α (r-h)) (1/2) (r-h) h k N lam ⟨j,hjk⟩ z -
              windowMassEnergyEntry β α (α (r-h)) (1/2) (r-h) h 0 N lam ⟨j,hj0⟩ z)| ≤
            C*(Real.sqrt h*h^2*k^2+h^2*|k|^3)/(N:ℝ)+eps/(N:ℝ)

theorem contrast_energy_abs_le (b u chi h k zeta C : ℝ)
    (hC : 0 ≤ C) (hz : |zeta| ≤ C*h^2) :
    |b^2*u^2*chi*(k^2*zeta^2)| ≤ b^2*u^2*|chi| *C^2*h^4*k^2 := by
  have hsq : zeta^2 ≤ (C*h^2)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg zeta)
      (mul_nonneg hC (sq_nonneg h))).mpr hz
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_mul, abs_pow, abs_pow,
    sq_abs, sq_abs, sq_abs, sq_abs]
  calc
    _ ≤ b^2*u^2*|chi| *(k^2*(C*h^2)^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (sq_nonneg k)) (by positivity)
    _ = _ := by ring

theorem fourth_order_le_corner_error {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) (k : ℝ) :
    h^4*k^2 ≤ Real.sqrt h*h^3*k^2+h^3*|k|^3 := by
  have hs : h ≤ Real.sqrt h := by
    apply (sq_le_sq₀ hh (Real.sqrt_nonneg h)).mp
    rw [Real.sq_sqrt hh]
    nlinarith
  have H := mul_le_mul_of_nonneg_right hs (mul_nonneg (pow_nonneg hh 3) (sq_nonneg k))
  have hn : 0 ≤ h^3*|k|^3 := mul_nonneg (pow_nonneg hh 3) (pow_nonneg (abs_nonneg k) 3)
  nlinarith only [H, hn]

def MassVariationBound (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h0 kap : ℝ, 0 ≤ C ∧ 0 < h0 ∧ 0 < kap ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ k : ℝ, |k| ≤ kap →
      ∀ eps : ℝ, 0 < eps → ∀ᶠ N : ℕ in atTop, ∀ z : ℝ,
        |cornerMassVariation β α r h k N z -
          cornerQuadratic β α (r-h) z * cornerMassVariationPenalty α r h k N| ≤
          C*(Real.sqrt h*h^3*k^2+h^3*|k|^3)+eps

def windowGradientEnergy (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ)
    (lam : ℝ) (j : Fin (windowMassPath β α a p s h k N).length) (z : ℝ) : ℝ :=
  let l := windowMassPath β α a p s h k N
  let f := massVariationTerminal β α s h
  vectorIncrementAverage (massPath (l.take j.val) lam)
    (vectorIncrementChain (massPath (l.drop j.val) lam) f)
    (fun y => (fderiv ℝ (vectorIncrementChain (massPath (l.drop (j.val+1)) lam) f)
      y (l.get j).2.2)^2) (fun _ => z)

def UniformWindowEntropyInputs (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ B a0 D h0 kap : ℝ, 0 ≤ B ∧ 0 < a0 ∧ 0 ≤ D ∧ 0 < h0 ∧ 0 < kap ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ k : ℝ, |k| ≤ kap →
      ∀ N : ℕ, 1 ≤ N →
      BoundedDerivs (massVariationTerminal β α (r-h) h) ∧
      ∀ lam ∈ Icc (0 : ℝ) 1,
        WindowInnerJets β α (α (r-h)) (1/2) (r-h) h k N lam B ∧
        ∀ j : Fin (windowMassPath β α (α (r-h)) (1/2) (r-h) h k N).length,
          ((windowMassPath β α (α (r-h)) (1/2) (r-h) h k N).get j).1+
            lam*((windowMassPath β α (α (r-h)) (1/2) (r-h) h k N).get j).2.1 ∈ Icc a0 1 ∧
          ‖((windowMassPath β α (α (r-h)) (1/2) (r-h) h k N).get j).2.2‖^2 ≤ D*h/(N:ℝ)

def PathEnergyExpansion (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h0 kap : ℝ, 0 ≤ C ∧ 0 < h0 ∧ 0 < kap ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ k : ℝ, |k| ≤ kap →
      ∀ eps : ℝ, 0 < eps → ∀ᶠ N : ℕ in atTop,
        ∀ lam ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, ∀ j : ℕ,
          ∀ hjk : j < (windowMassPath β α (α (r-h)) (1/2) (r-h) h k N).length,
          ∀ hj0 : j < (windowMassPath β α (α (r-h)) (1/2) (r-h) h 0 N).length,
          |(1/2:ℝ)*(windowGradientEnergy β α (α (r-h)) (1/2) (r-h) h k N lam ⟨j,hjk⟩ z -
              windowGradientEnergy β α (α (r-h)) (1/2) (r-h) h 0 N lam ⟨j,hj0⟩ z) -
            (β^2/2)*(windowMassEnergyEntry β α (α (r-h)) (1/2) (r-h) h k N lam ⟨j,hjk⟩ z -
              windowMassEnergyEntry β α (α (r-h)) (1/2) (r-h) h 0 N lam ⟨j,hj0⟩ z)| ≤
            C*(Real.sqrt h*h^2*k^2+h^2*|k|^3)/(N:ℝ)+eps/(N:ℝ)

private theorem abs_sensitivity_transfer {s t p q e A B C : ℝ}
    (hs : |s-(1/2:ℝ)*p| ≤ A) (ht : |t-(1/2:ℝ)*q| ≤ B)
    (he : |(1/2:ℝ)*(p-q)-e| ≤ C) : |(s-t)-e| ≤ A+B+C := by
  have hid : (s-t)-e = (s-(1/2:ℝ)*p)-(t-(1/2:ℝ)*q)+((1/2:ℝ)*(p-q)-e) := by ring
  rw [hid]
  exact ((abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
    (add_le_add (add_le_add hs ht) he)

theorem massSensitivityExpansion_of_pathEnergyExpansion {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    (hA : UniformWindowEntropyInputs β α I) (hP : PathEnergyExpansion β α I) :
    MassSensitivityExpansion β α I := by
  obtain ⟨B,a0,D,hA0,kapA,hB,ha0,hD,hhA,hkapA,hA⟩ := hA
  obtain ⟨C,hP0,kapP,hC,hhP,hkapP,hP⟩ := hP
  refine ⟨C,min hA0 hP0,min kapA kapP,hC,lt_min hhA hhP,lt_min hkapA hkapP,?_⟩
  intro r hr h hh hh0 k hk eps heps
  have hhA' : h ≤ hA0 := hh0.trans (min_le_left _ _)
  have hhP' : h ≤ hP0 := hh0.trans (min_le_right _ _)
  have hkA : |k| ≤ kapA := hk.trans (min_le_left _ _)
  have hkP : |k| ≤ kapP := hk.trans (min_le_right _ _)
  let K := 2*B*StepCalculus.pathExpansionConstant B/a0
  have hK : 0 ≤ K := div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hB) (StepCalculus.pathExpansionConstant_nonneg hB)) ha0.le
  have hlim : Tendsto (fun N : ℕ => K*D^2*h^2/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hvlim : Tendsto (fun N : ℕ => D*h/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsmall := hlim.eventually (eventually_le_nhds (by positivity : (0:ℝ) < eps/3))
  have hvsmall := hvlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [hP r hr h hh hhP' k hkP (eps/3) (by positivity),
    hsmall,hvsmall,eventually_ge_atTop (1:ℕ)] with N hPN hsmallN hvsmallN hN
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hs (t : ℝ) (ht : |t| ≤ kapA) (lam : ℝ) (hlam : lam ∈ Icc (0:ℝ) 1)
      (j : Fin (windowMassPath β α (α (r-h)) (1/2) (r-h) h t N).length) (z : ℝ) :
      |massPathSensitivity (windowMassPath β α (α (r-h)) (1/2) (r-h) h t N)
        (massVariationTerminal β α (r-h) h) lam j (fun _ => z) -
        (1/2:ℝ)*windowGradientEnergy β α (α (r-h)) (1/2) (r-h) h t N lam j z| ≤
        (eps/3)/(N:ℝ) := by
    obtain ⟨hf,hjets⟩ := hA r hr h hh hhA' t ht N hN
    obtain ⟨hinner,hstep⟩ := hjets lam hlam
    have hj := (hinner j.val j.isLt).of_le (by norm_num : 4 ≤ 10)
    have hinner' : QPotential 4 B (vectorIncrementChain
        (massPath ((windowMassPath β α (α (r-h)) (1/2) (r-h) h t N).drop (j.val+1)) lam)
        (massVariationTerminal β α (r-h) h)) := by
      simpa only [massPath, List.map_drop] using hj
    have hdir := (hstep j).2
    have hv : ‖((windowMassPath β α (α (r-h)) (1/2) (r-h) h t N).get j).2.2‖ ≤ 1 := by
      nlinarith [norm_nonneg (((windowMassPath β α (α (r-h)) (1/2) (r-h) h t N).get j).2.2)]
    have H := massPathSensitivity_first_order _ hf lam j hinner' ha0 (hstep j).1 hv (fun _ => z)
    change |_ - (1/2:ℝ)*windowGradientEnergy β α (α (r-h)) (1/2) (r-h) h t N lam j z| ≤
      K*‖((windowMassPath β α (α (r-h)) (1/2) (r-h) h t N).get j).2.2‖^4 at H
    have hfour : ‖((windowMassPath β α (α (r-h)) (1/2) (r-h) h t N).get j).2.2‖^4 ≤
        (D*h/(N:ℝ))^2 := by
      simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg _) hdir 2
    calc
      _ ≤ K*(D*h/(N:ℝ))^2 := H.trans (mul_le_mul_of_nonneg_left hfour hK)
      _ = (K*D^2*h^2/(N:ℝ))/(N:ℝ) := by field_simp
      _ ≤ (eps/3)/(N:ℝ) := div_le_div_of_nonneg_right hsmallN hn.le
  intro lam hlam z j hjk hj0
  have H := abs_sensitivity_transfer (hs k hkA lam hlam ⟨j,hjk⟩ z)
    (hs 0 (by simpa only [abs_zero] using hkapA.le) lam hlam ⟨j,hj0⟩ z)
    (hPN lam hlam z j hjk hj0)
  exact H.trans_eq (by ring)

theorem leftQuadrature_error {f : ℝ → ℝ} {K : NNReal} {a d : ℝ}
    (hd : 0 ≤ d) (hf : LipschitzOnWith K f (Icc a (a+d))) {N : ℕ} (hN : 0 < N) :
    |(d/(N:ℝ))*∑ j ∈ Finset.range N, f (a+d*(j:ℝ)/(N:ℝ)) -
      ∫ x in a..a+d, f x| ≤ (K:ℝ)*d^2/(N:ℝ) := by
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  let x := fun j : ℕ => a+d*(j:ℝ)/(N:ℝ)
  have hx (j : ℕ) (hj : j ≤ N) : x j ∈ Icc a (a+d) := by
    dsimp only [x]
    constructor
    · have H : 0 ≤ d*(j:ℝ)/(N:ℝ) := by positivity
      linarith
    · have hj' : (j:ℝ) ≤ N := Nat.cast_le.mpr hj
      have H : d*(j:ℝ)/(N:ℝ) ≤ d := (div_le_iff₀ hn).mpr
        (mul_le_mul_of_nonneg_left hj' hd)
      linarith
  have hinc (j : ℕ) : x (j+1)-x j = d/(N:ℝ) := by
    dsimp only [x]
    push_cast
    ring
  have hmono (j : ℕ) : x j ≤ x (j+1) := by
    have H := hinc j
    have H' : 0 ≤ d/(N:ℝ) := div_nonneg hd hn.le
    linarith
  have hint (j : ℕ) (hj : j < N) : IntervalIntegrable f volume (x j) (x (j+1)) :=
    ContinuousOn.intervalIntegrable_of_Icc (hmono j)
      (hf.continuousOn.mono (Icc_subset_Icc (hx j hj.le).1 (hx (j+1) hj).2))
  have he (j : ℕ) (hj : j < N) :
      |(d/(N:ℝ))*f (x j)-∫ t in x j..x (j+1), f t| ≤ (K:ℝ)*(d/(N:ℝ))^2 := by
    have hid : (d/(N:ℝ))*f (x j)-∫ t in x j..x (j+1), f t =
        ∫ t in x j..x (j+1), f (x j)-f t := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_const) (hint j hj),
        intervalIntegral.integral_const, smul_eq_mul, hinc]
    rw [hid]
    have H := intervalIntegral.norm_integral_le_of_norm_le_const (a := x j) (b := x (j+1))
      (C := (K:ℝ)*(d/(N:ℝ))) (f := fun t => f (x j)-f t) (by
        intro t ht
        rw [uIoc_of_le (hmono j)] at ht
        have ht' : t ∈ Icc a (a+d) := ⟨(hx j hj.le).1.trans ht.1.le,
          ht.2.trans (hx (j+1) hj).2⟩
        have Hlip := hf.norm_sub_le (hx j hj.le) ht'
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonpos (sub_nonpos.mpr ht.1.le)] at Hlip
        rw [Real.norm_eq_abs]
        exact Hlip.trans (mul_le_mul_of_nonneg_left (by linarith [hinc j, ht.2]) K.coe_nonneg))
    rw [Real.norm_eq_abs, hinc, abs_of_nonneg (div_nonneg hd hn.le)] at H
    exact H.trans_eq (by ring)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have hx0 : x 0 = a := by simp only [x, Nat.cast_zero, mul_zero, zero_div, add_zero]
  have hxN : x N = a+d := by dsimp only [x]; field_simp
  rw [hx0,hxN] at hsum
  rw [← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range N, |d/(N:ℝ)*f (x j)-∫ t in x j..x (j+1), f t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N, (K:ℝ)*(d/(N:ℝ))^2 :=
      Finset.sum_le_sum (fun j hj => he j (Finset.mem_range.mp hj))
    _ = (K:ℝ)*d^2/(N:ℝ) := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp

theorem stageIntegral_tendsto {α : ℝ → ℝ} {K : NNReal} {s h a len : ℝ}
    (hd : 0 ≤ h*len)
    (hα : LipschitzOnWith K α (Icc (s+h*a) (s+h*(a+len)))) :
    Tendsto (fun N : ℕ => stageIntegral α s h N a len) atTop
      (𝓝 (∫ t in s+h*a..s+h*(a+len), α t)) := by
  have hα' : LipschitzOnWith K α (Icc (s+h*a) ((s+h*a)+h*len)) := by
    rw [show (s+h*a)+h*len=s+h*(a+len) by ring]
    exact hα
  have hlim : Tendsto (fun N : ℕ => (K:ℝ)*(h*len)^2/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  have H := leftQuadrature_error hd hα' hN
  have he (j : ℕ) : (s+h*a)+h*len*(j:ℝ)/(N:ℝ) =
      s+h*(a+len*(j:ℝ)/(N:ℝ)) := by ring
  simpa only [stageIntegral, he, show (s+h*a)+h*len=s+h*(a+len) by ring,
    Real.norm_eq_abs] using H

theorem windowStage_tendsto {α : ℝ → ℝ} {K : NNReal} {s h a len : ℝ}
    (hh : 0 ≤ h) (ha : 0 ≤ a) (hl : 0 ≤ len) (hal : a+len ≤ 4)
    (hα : LipschitzOnWith K α (Icc s (s+4*h))) :
    Tendsto (fun N : ℕ => stageIntegral α s h N a len) atTop
      (𝓝 (∫ t in s+h*a..s+h*(a+len), α t)) := by
  apply stageIntegral_tendsto (mul_nonneg hh hl)
  apply hα.mono
  apply Icc_subset_Icc
  · nlinarith
  · nlinarith

theorem scalarTranslation_tendsto {α : ℝ → ℝ} {K : NNReal} {p s h k : ℝ}
    (hh : 0 ≤ h) (hp : p ∈ Icc (0:ℝ) 1)
    (hl : OW.repairLength p k ∈ Icc (0:ℝ) 2)
    (hα : LipschitzOnWith K α (Icc s (s+4*h))) :
    Tendsto (fun N : ℕ => scalarTranslation α p s h k N) atTop
      (𝓝 (∫ t in s..s+4*h, α t)) := by
  let L := OW.repairLength p k
  have h0 := windowStage_tendsto hh (by norm_num : (0:ℝ) ≤ 0)
    (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ)+1 ≤ 4) hα
  have h1 := windowStage_tendsto hh (by norm_num : (0:ℝ) ≤ 1) hp.1
    (by linarith [hp.2] : 1+p ≤ 4) hα
  have h2 := windowStage_tendsto hh (by linarith [hp.1] : 0 ≤ 1+p)
    (by linarith [hp.2] : 0 ≤ 1-p) (by linarith : (1+p)+(1-p) ≤ (4:ℝ)) hα
  have h3 := windowStage_tendsto hh (by norm_num : (0:ℝ) ≤ 2) hl.1
    (by linarith [hl.2] : 2+OW.repairLength p k ≤ 4) hα
  have h4 := windowStage_tendsto hh (by linarith [hl.1] : 0 ≤ 2+OW.repairLength p k)
    (by linarith [hl.2] : 0 ≤ 2-OW.repairLength p k)
    (by linarith : (2+OW.repairLength p k)+(2-OW.repairLength p k) ≤ (4:ℝ)) hα
  have hi (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 4) :
      IntervalIntegrable α volume (s+h*u) (s+h*v) :=
    ContinuousOn.intervalIntegrable_of_Icc (by nlinarith)
      (hα.continuousOn.mono (Icc_subset_Icc (by nlinarith) (by nlinarith)))
  have hi0 := hi 0 1 (by norm_num) (by norm_num) (by norm_num)
  have hi1 := hi 1 (1+p) (by norm_num) (by linarith [hp.1]) (by linarith [hp.2])
  have hi2 := hi (1+p) 2 (by linarith [hp.1]) (by linarith [hp.2]) (by norm_num)
  have hi3 := hi 2 (2+L) (by norm_num) (by linarith [hl.1]) (by linarith [hl.2])
  have hi4 := hi (2+L) 4 (by linarith [hl.1]) (by linarith [hl.2]) (by norm_num)
  have H := (((h0.add h1).add h2).add h3).add h4
  have he2 : (1+p)+(1-p) = (2:ℝ) := by ring
  have he4 : (2+OW.repairLength p k)+(2-OW.repairLength p k) = (4:ℝ) := by ring
  simp only [zero_add, mul_zero, add_zero, mul_one, he2, he4] at H hi0 hi1 hi2 hi3 hi4
  rw [intervalIntegral.integral_add_adjacent_intervals hi0 hi1,
    intervalIntegral.integral_add_adjacent_intervals (hi0.trans hi1) hi2,
    intervalIntegral.integral_add_adjacent_intervals ((hi0.trans hi1).trans hi2) hi3,
    intervalIntegral.integral_add_adjacent_intervals (((hi0.trans hi1).trans hi2).trans hi3) hi4] at H
  simpa only [scalarTranslation, mul_comm h 4] using H

def zetaIntegral (α : ℝ → ℝ) (p s h : ℝ) : ℝ :=
  tentWeight p*(∫ t in s..s+h, α t) +
    (rampWeight p-tentWeight p)*(∫ t in s+h..s+h*(1+p), α t) +
    (rampWeight p-2*tentWeight p)*(∫ t in s+h*(1+p)..s+2*h, α t)

theorem zeta_tendsto {α : ℝ → ℝ} {K : NNReal} {p s h : ℝ}
    (hh : 0 ≤ h) (hp : p ∈ Icc (0:ℝ) 1)
    (hα : LipschitzOnWith K α (Icc s (s+4*h))) :
    Tendsto (fun N : ℕ => zeta α p s h N) atTop (𝓝 (zetaIntegral α p s h)) := by
  have h0 := windowStage_tendsto hh (by norm_num : (0:ℝ) ≤ 0)
    (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ)+1 ≤ 4) hα
  have h1 := windowStage_tendsto hh (by norm_num : (0:ℝ) ≤ 1) hp.1
    (by linarith [hp.2] : 1+p ≤ 4) hα
  have h2 := windowStage_tendsto hh (by linarith [hp.1] : 0 ≤ 1+p)
    (by linarith [hp.2] : 0 ≤ 1-p) (by linarith : (1+p)+(1-p) ≤ (4:ℝ)) hα
  have H := ((h0.const_mul (tentWeight p)).add
    (h1.const_mul (rampWeight p-tentWeight p))).add
    (h2.const_mul (rampWeight p-2*tentWeight p))
  simpa only [zeta, zetaIntegral, zero_add, mul_zero, add_zero, mul_one,
    show (1+p)+(1-p)=(2:ℝ) by ring, mul_comm h 2] using H

theorem zetaIntegral_half_abs_le {α : ℝ → ℝ} {K : NNReal} {s h : ℝ}
    (hh : 0 ≤ h) (hα : LipschitzOnWith K α (Icc s (s+4*h))) :
    |zetaIntegral α (1/2) s h| ≤ (8/3:ℝ)*(K:ℝ)*h^2 := by
  apply le_of_tendsto (zeta_tendsto hh (by norm_num) hα).abs
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  apply zeta_half_abs_le α s h K hN hh K.coe_nonneg
  intro t ht
  have hs : s ∈ Icc s (s+4*h) := ⟨le_rfl, by linarith⟩
  have ht' : t ∈ Icc s (s+4*h) := ⟨ht.1, by linarith [ht.2]⟩
  simpa only [Real.norm_eq_abs] using hα.norm_sub_le ht' hs

theorem weighted_remainder_sum_le {n : ℕ} {wk w0 rk r0 : Fin n → ℝ}
    {W D A B : ℝ} (hW : 0 ≤ W) (hD : 0 ≤ D)
    (hw : ∀ j, |wk j| ≤ W) (hd : ∀ j, |wk j-w0 j| ≤ D)
    (hr : ∀ j, |rk j-r0 j| ≤ A) (hr0 : ∀ j, |r0 j| ≤ B) :
    |∑ j, (wk j*rk j-w0 j*r0 j)| ≤ (n:ℝ)*(W*A+D*B) := by
  calc
    _ ≤ ∑ j, |wk j*rk j-w0 j*r0 j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin n, (W*A+D*B) := by
      apply Finset.sum_le_sum
      intro j _
      have he : wk j*rk j-w0 j*r0 j = wk j*(rk j-r0 j)+(wk j-w0 j)*r0 j := by ring
      rw [he]
      exact (abs_add_le _ _).trans (add_le_add
        (by rw [abs_mul]; exact mul_le_mul (hw j) (hr j) (abs_nonneg _) hW)
        (by rw [abs_mul]; exact mul_le_mul (hd j) (hr0 j) (abs_nonneg _) hD))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem weighted_window_remainder_le {N : ℕ} (hN : 0 < N)
    {wk w0 rk r0 : Fin (12*N) → ℝ} {M C h k eta : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hh : 0 ≤ h) (_heta : 0 ≤ eta)
    (hw : ∀ j, |wk j| ≤ M*h) (hd : ∀ j, |wk j-w0 j| ≤ M*h*k^2)
    (hr : ∀ j, |rk j-r0 j| ≤ C*(Real.sqrt h*h^2*k^2+h^2*|k|^3)/(N:ℝ)+eta/(N:ℝ))
    (hr0 : ∀ j, |r0 j| ≤ C*(Real.sqrt h*h^2)/(N:ℝ)+eta/(N:ℝ)) :
    |∑ j, (wk j*rk j-w0 j*r0 j)| ≤
      24*M*C*(Real.sqrt h*h^3*k^2+h^3*|k|^3)+12*M*h*(1+k^2)*eta := by
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have H := weighted_remainder_sum_le (mul_nonneg hM hh)
    (mul_nonneg (mul_nonneg hM hh) (sq_nonneg k))
    hw hd hr hr0
  apply H.trans
  have he : ((12*N:ℕ):ℝ)*((M*h)*(C*(Real.sqrt h*h^2*k^2+h^2*|k|^3)/(N:ℝ)+eta/(N:ℝ))+
      (M*h*k^2)*(C*(Real.sqrt h*h^2)/(N:ℝ)+eta/(N:ℝ))) =
      24*M*C*(Real.sqrt h*h^3*k^2+h^3*|k|^3)+12*M*h*(1+k^2)*eta-
        12*M*C*h^3*|k|^3 := by
    push_cast
    field_simp
    ring
  rw [he]
  have hp : 0 ≤ 12*M*C*h^3*|k|^3 := by positivity
  linarith

theorem cornerQuadratic_time_shift {β : ℝ} {α : ℝ → ℝ} {s h B D : ℝ}
    {dchi : ℝ → ℝ → ℝ} (hh : 0 ≤ h) (_hB : 0 ≤ B) (hD : 0 ≤ D)
    (hder : ∀ t ∈ Icc s (s+4*h), ∀ z,
      HasDerivAt (fun u => jet β α 2 u z) (dchi t z) t)
    (hdt : ∀ t ∈ Icc s (s+4*h), ∀ z, |dchi t z| ≤ D)
    (hchi : ∀ t ∈ Icc s (s+4*h), ∀ z, |jet β α 2 t z| ≤ B) (z : ℝ) :
    |cornerQuadratic β α (s+4*h) z-cornerQuadratic β α s z| ≤ 2*β^4*B*D*h := by
  have hs : s ∈ Icc s (s+4*h) := ⟨le_rfl, by linarith⟩
  have ht : s+4*h ∈ Icc s (s+4*h) := ⟨by linarith, le_rfl⟩
  have H := (convex_Icc s (s+4*h)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hder t ht z).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using hdt t ht z) hs ht
  have hdiff : |jet β α 2 (s+4*h) z-jet β α 2 s z| ≤ 4*D*h := by
    simpa only [Real.norm_eq_abs, add_sub_cancel_left, abs_of_nonneg (by positivity : 0 ≤ 4*h),
      show D*(4*h)=4*D*h by ring] using H
  have hsum : |jet β α 2 (s+4*h) z+jet β α 2 s z| ≤ 2*B :=
    (abs_add_le _ _).trans ((add_le_add (hchi _ ht z) (hchi _ hs z)).trans_eq (by ring))
  have he : cornerQuadratic β α (s+4*h) z-cornerQuadratic β α s z =
      (β^4/4)*(jet β α 2 (s+4*h) z-jet β α 2 s z)*
        (jet β α 2 (s+4*h) z+jet β α 2 s z) := by unfold cornerQuadratic; ring
  rw [he, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ β^4/4)]
  calc
    _ ≤ (β^4/4)*(4*D*h)*(2*B) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hdiff (by positivity)) hsum (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem uniform_scalar_mesh_cancellation {S Z k M : ℝ}
    {Sk S0 Zn J : ℕ → ℝ} {A B Q : ℝ → ℝ} (_hM : 0 ≤ M)
    (hSk : Tendsto Sk atTop (𝓝 S)) (hS0 : Tendsto S0 atTop (𝓝 S))
    (hZ : Tendsto Zn atTop (𝓝 Z)) (hJ : Tendsto J atTop (𝓝 0))
    (hA : ∀ z, |A z| ≤ M) (hB : ∀ z, |B z| ≤ M) (hQ : ∀ z, |Q z| ≤ M)
    {eps : ℝ} (heps : 0 < eps) : ∀ᶠ N : ℕ in atTop, ∀ z : ℝ,
      |A z*(Sk N-S0 N)+B z*(k^2*Zn N^2+(3/2:ℝ)*(Sk N^2-S0 N^2))-Q z*J N-
        B z*(k^2*Z^2)| ≤ eps := by
  let d := fun N => k^2*(Zn N^2-Z^2)+(3/2:ℝ)*(Sk N^2-S0 N^2)
  have hd : Tendsto d atTop (𝓝 0) := by
    have H := (((hZ.pow 2).sub_const (Z^2)).const_mul (k^2)).add
      (((hSk.pow 2).sub (hS0.pow 2)).const_mul (3/2:ℝ))
    simpa only [sub_self, mul_zero, add_zero, d] using H
  have hlim : Tendsto (fun N => M*(|Sk N-S0 N|+|d N|+|J N|)) atTop (𝓝 0) := by
    have H := ((((hSk.sub hS0).abs).add hd.abs).add hJ.abs).const_mul M
    simpa only [sub_self, abs_zero, zero_add, mul_zero] using H
  filter_upwards [hlim.eventually (eventually_le_nhds heps)] with N hN z
  have he : A z*(Sk N-S0 N)+B z*(k^2*Zn N^2+(3/2:ℝ)*(Sk N^2-S0 N^2))-Q z*J N-
      B z*(k^2*Z^2) = A z*(Sk N-S0 N)+B z*d N-Q z*J N := by dsimp only [d]; ring
  rw [he]
  calc
    _ ≤ |A z*(Sk N-S0 N)|+|B z*d N|+|Q z*J N| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ M*|Sk N-S0 N|+M*|d N|+M*|J N| := by
      simp only [abs_mul]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right (hA z) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (hB z) (abs_nonneg _)))
        (mul_le_mul_of_nonneg_right (hQ z) (abs_nonneg _))
    _ = M*(|Sk N-S0 N|+|d N|+|J N|) := by ring
    _ ≤ eps := hN

theorem integrated_windowLeadingEnergy_uniform {b a p s h k M : ℝ}
    {α : ℝ → ℝ} {K : NNReal} {u chi w : ℝ → ℝ} (hh : 0 ≤ h)
    (hp : p ∈ Icc (0:ℝ) 1) (hl : OW.repairLength p k ∈ Icc (0:ℝ) 2)
    (hα : LipschitzOnWith K α (Icc s (s+4*h))) (hM : 0 ≤ M)
    (hA : ∀ z, |3*(b*(u z)^2/2+2*b^2*h*u z*w z-2*s*(b^2*(chi z)^2/4))| ≤ M)
    (hB : ∀ z, |b^2*(u z)^2*chi z| ≤ M)
    (hQ : ∀ z, |b^2*(chi z)^2/4| ≤ M)
    (hJ : Tendsto (fun N => quarticMass (massVariationWindow α a p s h k N)-
      quarticMass (massVariationWindow α a p s h 0 N)) atTop (𝓝 0))
    {eps : ℝ} (heps : 0 < eps) : ∀ᶠ N : ℕ in atTop, ∀ z : ℝ,
      |b/2*(∫ lam in (0:ℝ)..1,
          windowLeadingEnergy b (u z) (chi z) (w z) α (interpolatedProfile α a lam) a p s h k N-
          windowLeadingEnergy b (u z) (chi z) (w z) α (interpolatedProfile α a lam) a p s h 0 N)-
        (b^2*(chi z)^2/4)*(massVariationPenalty α a p s h k N-massVariationPenalty α a p s h 0 N)-
        b^2*(u z)^2*chi z*(k^2*(zetaIntegral α p s h)^2)| ≤ eps := by
  have hl0 : OW.repairLength p 0 ∈ Icc (0:ℝ) 2 := by norm_num [OW.repairLength]
  have H := uniform_scalar_mesh_cancellation (k := k) hM
    (scalarTranslation_tendsto hh hp hl hα) (scalarTranslation_tendsto hh hp hl0 hα)
    (zeta_tendsto hh hp hα) hJ hA hB hQ heps
  filter_upwards [H,eventually_gt_atTop (0:ℕ)] with N hN hNpos z
  rw [integrated_windowLeadingEnergy b (u z) (chi z) (w z) α a p s h k hNpos hh hp hl]
  exact hN z

theorem terminal_initial_penalty_shift {β : ℝ} {α : ℝ → ℝ} {s h k B D P : ℝ}
    {dchi : ℝ → ℝ → ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hP : 0 ≤ P)
    (hder : ∀ t ∈ Icc s (s+4*h), ∀ z,
      HasDerivAt (fun u => jet β α 2 u z) (dchi t z) t)
    (hdt : ∀ t ∈ Icc s (s+4*h), ∀ z, |dchi t z| ≤ D)
    (hchi : ∀ t ∈ Icc s (s+4*h), ∀ z, |jet β α 2 t z| ≤ B)
    {pen : ℝ} (hpen : |pen| ≤ P*h^3*k^2) (z : ℝ) :
    |(cornerQuadratic β α (s+4*h) z-cornerQuadratic β α s z)*pen| ≤
      (2*β^4*B*D*P)*(Real.sqrt h*h^3*k^2+h^3*|k|^3) := by
  rw [abs_mul]
  calc
    _ ≤ (2*β^4*B*D*h)*(P*h^3*k^2) :=
      mul_le_mul (cornerQuadratic_time_shift hh hB hD hder hdt hchi z) hpen
        (abs_nonneg _) (by positivity)
    _ = (2*β^4*B*D*P)*(h^4*k^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (fourth_order_le_corner_error hh hh1 k) (by positivity)

theorem massLeadingEnergy_append (b u chi w h : ℝ) (mu : Vec3)
    (l r : List (ℝ × Vec3)) (Q : Fin 3 → Fin 3 → ℝ) :
    massLeadingEnergy b u chi w h mu (l++r) Q =
      massLeadingEnergy b u chi w h mu l Q+
        massLeadingEnergy b u chi w h mu r (Q+matrixChainCovariance l) := by
  induction l generalizing Q with
  | nil => simp only [List.nil_append, massLeadingEnergy, matrixChainCovariance,
      List.map_nil, chainSum, List.sum_nil, add_zero, zero_add]
  | cons q l ih =>
    simp only [List.cons_append, massLeadingEnergy, ih, matrixChainCovariance,
      List.map_cons, chainSum_cons, add_assoc]

private theorem massLeadingEnergy_ofFn (n : ℕ) (p : Fin n → ℝ × Vec3)
    (b u chi w h : ℝ) (mu : Vec3) (Q : Fin 3 → Fin 3 → ℝ) :
    massLeadingEnergy b u chi w h mu (List.ofFn p) Q =
      ∑ j, (p j).1*(u^2*(∑ i, (p j).2 i)^2+
        2*b*u^2*chi*(∑ i, (p j).2 i)*(∑ i, (p j).2 i*mu i)+
        4*b*h*u*w*(∑ i, (p j).2 i)^2+
        b*chi^2*matrixQuadratic (Q+strictPrefix (fun i => rankOneMatrix (p i).2) j) (p j).2) := by
  induction n with
  | zero => simp only [List.ofFn_zero, massLeadingEnergy, Finset.univ_eq_empty,
      Finset.sum_empty]
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, massLeadingEnergy_append, ih]
    simp only [massLeadingEnergy, add_zero, matrixChainCovariance, List.map_ofFn,
      chainSum_ofFn, Fin.sum_univ_castSucc, strictPrefix_castSucc, strictPrefix_last,
      Function.comp_def]

theorem massLeadingEnergy_eq_sum (b u chi w h : ℝ) (mu : Vec3)
    (l : List (ℝ × Vec3)) (Q : Fin 3 → Fin 3 → ℝ) :
    massLeadingEnergy b u chi w h mu l Q =
      ∑ j : Fin l.length, (l.get j).1*(u^2*(∑ i, (l.get j).2 i)^2+
        2*b*u^2*chi*(∑ i, (l.get j).2 i)*(∑ i, (l.get j).2 i*mu i)+
        4*b*h*u*w*(∑ i, (l.get j).2 i)^2+
        b*chi^2*matrixQuadratic (Q+strictPrefix (fun i => rankOneMatrix (l.get i).2) j) (l.get j).2) := by
  have H := massLeadingEnergy_ofFn l.length l.get b u chi w h mu Q
  rw [List.ofFn_get] at H
  exact H

private theorem subtractMasses_samples (l : List (ℝ × ℝ × Vec3)) (α : ℝ → ℝ) (a : ℝ) :
    subtractMasses (l.map (fun q => (α q.1/q.2.1,q.2.2)))
      (l.map (fun q => (a/q.2.1,q.2.2))) =
      l.map (fun q => ((α q.1-a)/q.2.1,q.2.2)) := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    simp only [List.map_cons, subtractMasses, List.zipWith_cons_cons] at ih ⊢
    rw [ih]
    congr 2
    ring

theorem massVariationWindow_eq_samples (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ) :
    massVariationWindow α a p s h k N = (windowMassSamples p s h k N).map
      (fun q => ((α q.1-a)/q.2.1,q.2.2)) := by
  rw [massVariationWindow, window_eq_massSamples, window_eq_massSamples]
  exact subtractMasses_samples _ α a

theorem windowMassEnergyEntry_sum (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ)
    (N : ℕ) (lam z : ℝ) :
    (∑ j : Fin (windowMassPath β α a p s h k N).length,
      ((windowMassPath β α a p s h k N).get j).2.1 *
        windowMassEnergyEntry β α a p s h k N lam j z) =
    windowLeadingEnergy (β^2) (jet β α 1 (s+4*h) z)
      (jet β α 2 (s+4*h) z) (jet β α 3 (s+4*h) z)
      α (interpolatedProfile α a lam) a p s h k N := by
  rw [windowLeadingEnergy, massLeadingEnergy_eq_sum]
  have hlen : (windowMassPath β α a p s h k N).length =
      (massVariationWindow α a p s h k N).length := by
    simp only [windowMassPath, massVariationWindow_eq_samples, List.length_map]
  apply Fintype.sum_equiv (finCongr hlen)
  intro j
  have hprefix : strictPrefix
      (fun i => rankOneMatrix (windowRawDirection β α a p s h k N i)) j =
      strictPrefix (fun i => rankOneMatrix ((massVariationWindow α a p s h k N).get i).2)
        ((finCongr hlen) j) := by
    unfold strictPrefix
    apply Fintype.sum_equiv (finCongr hlen)
    intro i
    simp only [Fin.lt_def, finCongr_apply, Fin.val_cast, windowRawDirection,
      massVariationWindow_eq_samples, List.get_eq_getElem, List.getElem_map]
  have hm : ((windowMassPath β α a p s h k N).get j).2.1 =
      ((massVariationWindow α a p s h k N).get ((finCongr hlen) j)).1 := by
    change (((windowMassSamples p s h k N).map
      (fun q => (a/q.2.1,(α q.1-a)/q.2.1,β • q.2.2)))[j.val]'_).2.1 = _
    simp only [massVariationWindow_eq_samples, List.get_eq_getElem, List.getElem_map]
    rfl
  have hv : windowRawDirection β α a p s h k N j =
      ((massVariationWindow α a p s h k N).get ((finCongr hlen) j)).2 := by
    simp only [windowRawDirection, massVariationWindow_eq_samples,
      List.get_eq_getElem, List.getElem_map]
    rfl
  dsimp only [windowMassEnergyEntry]
  rw [hm, hprefix, hv, zero_add]

def windowWeightedRemainder (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ)
    (N : ℕ) (lam z : ℝ) : ℝ :=
  ∑ j : Fin (windowMassPath β α a p s h k N).length,
    ((windowMassPath β α a p s h k N).get j).2.1 *
      (massPathSensitivity (windowMassPath β α a p s h k N)
        (massVariationTerminal β α s h) lam j (fun _ => z)-
        (β^2/2)*windowMassEnergyEntry β α a p s h k N lam j z)

theorem windowWeightedRemainder_eq (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ)
    (N : ℕ) (lam z : ℝ) :
    windowWeightedRemainder β α a p s h k N lam z =
      (∑ j : Fin (windowMassPath β α a p s h k N).length,
        ((windowMassPath β α a p s h k N).get j).2.1 *
          massPathSensitivity (windowMassPath β α a p s h k N)
            (massVariationTerminal β α s h) lam j (fun _ => z))-
      (β^2/2)*windowLeadingEnergy (β^2) (jet β α 1 (s+4*h) z)
        (jet β α 2 (s+4*h) z) (jet β α 3 (s+4*h) z)
        α (interpolatedProfile α a lam) a p s h k N := by
  rw [← windowMassEnergyEntry_sum]
  simp only [windowWeightedRemainder, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem sensitivitySum_intervalIntegrable (l : List (MassPathEntry Vec3))
    {f : Vec3 → ℝ} (hf : BoundedDerivs f) (hR : MassPathRegular l f)
    (hm : ∀ lam ∈ Icc (0:ℝ) 1, ∀ q ∈ l, q.1+lam*q.2.1 ≠ 0) (x : Vec3) :
    IntervalIntegrable (fun lam => ∑ j : Fin l.length,
      (l.get j).2.1*massPathSensitivity l f lam j x) volume 0 1 := by
  have hc : ContinuousOn (fun lam => massPathDerivative l f lam x) (Icc (0:ℝ) 1) := by
    have H : ContinuousOn (deriv (fun t => massPathValue l f (t,x))) (Icc (0:ℝ) 1) := by
      intro lam hlam
      exact ((massPathValue_contDiffAt l f hR (hm lam hlam) x).derivWithin
        (m := 0) (by norm_num)).continuousAt.continuousWithinAt
    apply H.congr
    intro lam hlam
    exact (massPath_hasDerivAt l f hR (hm lam hlam) x).deriv.symm
  have he (lam : ℝ) := massPathDerivative_eq_sum l hf lam x
  simp_rw [he] at hc
  exact ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le zero_le_one] using hc)

theorem cornerMassVariation_sub_leading_eq_integral (β : ℝ) (α : ℝ → ℝ)
    (r h k : ℝ) {N : ℕ} (hN : 0 < N) (hh : 0 ≤ h)
    (hl : OW.repairLength (1/2) k ∈ Icc (0:ℝ) 2)
    (hf : BoundedDerivs (massVariationTerminal β α (r-h) h))
    (hRk : WindowMassRegularity β α (α (r-h)) (1/2) (r-h) h k N)
    (hR0 : WindowMassRegularity β α (α (r-h)) (1/2) (r-h) h 0 N) (z : ℝ) :
    cornerMassVariation β α r h k N z-
      (β^2/2)*(∫ lam in (0:ℝ)..1,
        windowLeadingEnergy (β^2) (jet β α 1 ((r-h)+4*h) z)
          (jet β α 2 ((r-h)+4*h) z) (jet β α 3 ((r-h)+4*h) z)
          α (interpolatedProfile α (α (r-h)) lam) (α (r-h)) (1/2) (r-h) h k N-
        windowLeadingEnergy (β^2) (jet β α 1 ((r-h)+4*h) z)
          (jet β α 2 ((r-h)+4*h) z) (jet β α 3 ((r-h)+4*h) z)
          α (interpolatedProfile α (α (r-h)) lam) (α (r-h)) (1/2) (r-h) h 0 N) =
      ∫ lam in (0:ℝ)..1,
        windowWeightedRemainder β α (α (r-h)) (1/2) (r-h) h k N lam z-
        windowWeightedRemainder β α (α (r-h)) (1/2) (r-h) h 0 N lam z := by
  let E := fun t lam => windowLeadingEnergy (β^2) (jet β α 1 ((r-h)+4*h) z)
    (jet β α 2 ((r-h)+4*h) z) (jet β α 3 ((r-h)+4*h) z)
    α (interpolatedProfile α (α (r-h)) lam) (α (r-h)) (1/2) (r-h) h t N
  have hiE (t : ℝ) (ht : OW.repairLength (1/2) t ∈ Icc (0:ℝ) 2) :
      IntervalIntegrable (E t) volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact (leadingEnergy_continuous _ _ _ _ _ _ _).comp
      (interpolatedTranslation_continuous _ _ _ _ _ _ hN hh (by norm_num) ht)
  have hiEk := hiE k hl
  have hiE0 := hiE 0 (by norm_num [OW.repairLength])
  have hiSk := sensitivitySum_intervalIntegrable _ hf hRk.1 hRk.2 (fun _ => z)
  have hiS0 := sensitivitySum_intervalIntegrable _ hf hR0.1 hR0.2 (fun _ => z)
  rw [cornerMassVariation_eq_integral_difference β α r h k N hf hRk hR0 z]
  symm
  simp_rw [windowWeightedRemainder_eq]
  rw [intervalIntegral.integral_sub (hiSk.sub (hiEk.const_mul _)) (hiS0.sub (hiE0.const_mul _)),
    intervalIntegral.integral_sub hiSk (hiEk.const_mul _),
    intervalIntegral.integral_sub hiS0 (hiE0.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hiEk hiE0]
  ring

theorem scalarTranslation_neg (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ) :
    scalarTranslation α p s h (-k) N = scalarTranslation α p s h k N := by
  simp only [scalarTranslation, OW.repairLength, neg_sq]

theorem massVariationPenalty_neg (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ) :
    massVariationPenalty α a p s h (-k) N = massVariationPenalty α a p s h k N := by
  simp only [massVariationPenalty, OW.window_penalty_even]

private theorem quarticMass_append (l r : List (ℝ × Vec3)) :
    quarticMass (l++r) = quarticMass l+quarticMass r := by
  simp only [quarticMass, List.map_append, List.sum_append]

private theorem quarticMass_block (m t : ℝ) (vs : List Vec3) :
    quarticMass (vs.map (fun v => (m,t • v))) =
      m*t^4*(vs.map (fun v => (∑ a, (v a)^2)^2)).sum := by
  induction vs with
  | nil => simp only [List.map_nil, quarticMass, List.sum_nil, mul_zero]
  | cons v vs ih =>
    change m*(∑ a, (t*v a)^2)^2+quarticMass (vs.map (fun v => (m,t • v))) = _
    rw [ih]
    simp only [List.map_cons, List.sum_cons, mul_pow, ← Finset.mul_sum]
    ring

private theorem quarticMass_flatMap (js : List ℕ) (m : ℕ → ℝ) (t : ℝ)
    (vs : List Vec3) :
    quarticMass (js.flatMap (fun j => vs.map (fun v => (m j,t • v)))) =
      (js.map m).sum*t^4*(vs.map (fun v => (∑ a, (v a)^2)^2)).sum := by
  induction js with
  | nil => simp only [List.flatMap_nil, quarticMass, List.map_nil, List.sum_nil, zero_mul]
  | cons j js ih =>
    rw [List.flatMap_cons, quarticMass_append, quarticMass_block, ih]
    simp only [List.map_cons, List.sum_cons]
    ring

private theorem quarticMass_grid (α : ℝ → ℝ) (s h a len c : ℝ) (N : ℕ)
    (vs : List Vec3) :
    quarticMass (OW.windowGrid α s h N a len c vs) =
      ((List.range N).map (fun (j : ℕ) => α (s+h*(a+len*(j:ℝ)/(N:ℝ)))/c)).sum *
        (Real.sqrt (h*len/(N:ℝ)))^4*(vs.map (fun v => (∑ a, (v a)^2)^2)).sum := by
  exact quarticMass_flatMap _ _ _ _

private theorem quarticMass_repair (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ)
    (vs : List Vec3) :
    quarticMass (OW.windowRepairGrid α p s h k N vs) =
      ((List.range N).map (fun (j : ℕ) => α (s+h*(2+OW.repairLength p k*(j:ℝ)/(N:ℝ)))/1)).sum *
        (k*Real.sqrt (h*(4*varianceCoefficient p)/(N:ℝ)))^4 *
          (vs.map (fun v => (∑ a, (v a)^2)^2)).sum := by
  exact quarticMass_flatMap _ _ _ _

private theorem quartic_direction_sums_neg (p k : ℝ) :
    (∑ a, (commonVector p (-k) a)^2)^2 = (∑ a, (commonVector p k a)^2)^2 ∧
    (∑ a, (sharedVector p (-k) a)^2)^2 = (∑ a, (sharedVector p k a)^2)^2 ∧
    (∑ a, (rampVector p (-k) a)^2)^2 = (∑ a, (rampVector p k a)^2)^2 ∧
    (∑ a, (postXVector p (-k) a)^2)^2+(∑ a, (postYVector p (-k) a)^2)^2 =
      (∑ a, (postXVector p k a)^2)^2+(∑ a, (postYVector p k a)^2)^2 := by
  simp only [commonVector, sharedVector, rampVector, postXVector, postYVector,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem quarticMass_window_neg (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ) :
    quarticMass (OW.window α p s h (-k) N) = quarticMass (OW.window α p s h k N) := by
  obtain ⟨hc,hs,hv,hxy⟩ := quartic_direction_sums_neg p k
  have hrepair : ((-k)*Real.sqrt (h*(4*varianceCoefficient p)/(N:ℝ)))^4 =
      (k*Real.sqrt (h*(4*varianceCoefficient p)/(N:ℝ)))^4 := by ring
  rw [OW.window_eq, OW.window_eq]
  simp only [quarticMass_append, quarticMass_grid, quarticMass_repair,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    OW.repairLength, neg_sq, hrepair, hc, hs, hv, hxy]

private theorem quarticMass_subtract (l r : List (ℝ × Vec3))
    (hv : l.map Prod.snd = r.map Prod.snd) :
    quarticMass (subtractMasses l r) = quarticMass l-quarticMass r := by
  induction l generalizing r with
  | nil => cases r <;> simp_all [quarticMass, subtractMasses]
  | cons q l ih =>
    cases r with
    | nil => simp only [List.map_cons, List.map_nil] at hv; contradiction
    | cons t r =>
      have he := List.cons.inj hv
      change q.2=t.2 ∧ l.map Prod.snd=r.map Prod.snd at he
      change (q.1-t.1)*(∑ a, (q.2 a)^2)^2+quarticMass (subtractMasses l r) =
        (q.1*(∑ a, (q.2 a)^2)^2+quarticMass l)-
          (t.1*(∑ a, (t.2 a)^2)^2+quarticMass r)
      rw [ih r he.2, ← he.1]
      ring

theorem quarticMass_massVariation_neg (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ) :
    quarticMass (massVariationWindow α a p s h (-k) N) =
      quarticMass (massVariationWindow α a p s h k N) := by
  simp only [massVariationWindow, quarticMass_subtract _ _ (window_directions _ _ _ _ _ _ _),
    quarticMass_window_neg]

private theorem massLeadingEnergy_zero (u chi w h : ℝ) (mu : Vec3)
    (l : List (ℝ × Vec3)) (Q : Fin 3 → Fin 3 → ℝ) :
    massLeadingEnergy 0 u chi w h mu l Q = u^2*projectionMass l := by
  induction l generalizing Q with
  | nil => simp only [massLeadingEnergy, projectionMass, List.map_nil, List.sum_nil, mul_zero]
  | cons q l ih =>
    simp only [massLeadingEnergy, ih, projectionMass, List.map_cons, List.sum_cons]
    ring

theorem windowLeadingEnergy_neg (b u chi w : ℝ) (α γ : ℝ → ℝ)
    (a p s h k : ℝ) {N : ℕ} (hN : 0 < N) (hh : 0 ≤ h)
    (hp : p ∈ Icc (0:ℝ) 1) (hl : OW.repairLength p k ∈ Icc (0:ℝ) 2) :
    windowLeadingEnergy b u chi w α γ a p s h (-k) N =
      windowLeadingEnergy b u chi w α γ a p s h k N := by
  have hlneg : OW.repairLength p (-k) ∈ Icc (0:ℝ) 2 := by
    simpa only [OW.repairLength, neg_sq] using hl
  by_cases hb : b=0
  · subst b
    simp only [windowLeadingEnergy, massLeadingEnergy_zero,
      massVariation_projection α a p s h (-k) hN hh hp hlneg,
      massVariation_projection α a p s h k hN hh hp hl, scalarTranslation_neg]
  · have Hk := windowLeadingEnergy_difference b u chi w α γ a p s h k hN hh hp hl
    have Hn := windowLeadingEnergy_difference b u chi w α γ a p s h (-k) hN hh hp hlneg
    rw [massVariationPenalty_neg, scalarTranslation_neg, scalarTranslation_neg,
      quarticMass_massVariation_neg, neg_sq] at Hn
    have H : (b/2)*(windowLeadingEnergy b u chi w α γ a p s h (-k) N-
        windowLeadingEnergy b u chi w α γ a p s h k N)=0 := by linarith only [Hk,Hn]
    exact sub_eq_zero.mp ((mul_eq_zero.mp H).resolve_left (div_ne_zero hb (by norm_num)))

def cornerMassLeadingPart (β : ℝ) (α : ℝ → ℝ) (r h k : ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  (β^2/2)*(∫ lam in (0:ℝ)..1,
    windowLeadingEnergy (β^2) (jet β α 1 ((r-h)+4*h) z)
      (jet β α 2 ((r-h)+4*h) z) (jet β α 3 ((r-h)+4*h) z)
      α (interpolatedProfile α (α (r-h)) lam) (α (r-h)) (1/2) (r-h) h k N-
    windowLeadingEnergy (β^2) (jet β α 1 ((r-h)+4*h) z)
      (jet β α 2 ((r-h)+4*h) z) (jet β α 3 ((r-h)+4*h) z)
      α (interpolatedProfile α (α (r-h)) lam) (α (r-h)) (1/2) (r-h) h 0 N)

def cornerMassRemainder (β : ℝ) (α : ℝ → ℝ) (r h k : ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  cornerMassVariation β α r h k N z-cornerMassLeadingPart β α r h k N z

theorem cornerMassLeadingPart_neg (β : ℝ) (α : ℝ → ℝ) (r h k : ℝ)
    {N : ℕ} (hN : 0 < N) (hh : 0 ≤ h) (hk : |k| ≤ 1/2) (z : ℝ) :
    cornerMassLeadingPart β α r h (-k) N z = cornerMassLeadingPart β α r h k N z := by
  unfold cornerMassLeadingPart
  congr 1
  apply intervalIntegral.integral_congr
  intro lam _
  dsimp only
  congr 1
  exact windowLeadingEnergy_neg (β^2) (jet β α 1 ((r-h)+4*h) z)
    (jet β α 2 ((r-h)+4*h) z) (jet β α 3 ((r-h)+4*h) z)
    α (interpolatedProfile α (α (r-h)) lam) (α (r-h)) (1/2) (r-h) h k
    hN hh (by norm_num) (OW.repairLength_mem (by norm_num) hk)

private theorem massVariationTerminal_swap (β : ℝ) (α : ℝ → ℝ) (s h : ℝ) :
    massVariationTerminal β α s h ∘ OW.swap23 = massVariationTerminal β α s h := by
  funext x
  norm_num [Function.comp_def, massVariationTerminal, Fin.sum_univ_succ, OW.swap23_apply]
  ring

theorem interpolatedBoundary_neg (β : ℝ) (α : ℝ → ℝ) (a lam p s h k : ℝ)
    (N : ℕ) (hf : BoundedDerivs (massVariationTerminal β α s h)) (z : ℝ) :
    interpolatedBoundary β α a lam p s h (-k) N z =
      interpolatedBoundary β α a lam p s h k N z := by
  exact interpolated_chain_even β α a lam p s h k N hf
    (massVariationTerminal_swap β α s h) z

theorem cornerMassVariation_neg (β : ℝ) (α : ℝ → ℝ) (r h k : ℝ) (N : ℕ)
    (hPhi : BoundedDerivs (Phi β α ((r-h)+4*h))) (z : ℝ) :
    cornerMassVariation β α r h (-k) N z = cornerMassVariation β α r h k N z := by
  unfold cornerMassVariation
  rw [boundary_even β α _ _ _ _ _ hPhi,
    interpolatedBoundary_neg β α _ _ _ _ _ _ _
      (massVariationTerminal_regular β α (r-h) h hPhi)]

theorem cornerMassRemainder_neg (β : ℝ) (α : ℝ → ℝ) (r h k : ℝ)
    {N : ℕ} (hN : 0 < N) (hh : 0 ≤ h) (hk : |k| ≤ 1/2)
    (hPhi : BoundedDerivs (Phi β α ((r-h)+4*h))) (z : ℝ) :
    cornerMassRemainder β α r h (-k) N z = cornerMassRemainder β α r h k N z := by
  rw [cornerMassRemainder, cornerMassRemainder,
    cornerMassVariation_neg β α r h k N hPhi,
    cornerMassLeadingPart_neg β α r h k hN hh hk]

theorem cornerMassRemainder_zero (β : ℝ) (α : ℝ → ℝ) (r h : ℝ)
    (N : ℕ) (z : ℝ) : cornerMassRemainder β α r h 0 N z = 0 := by
  simp only [cornerMassRemainder, cornerMassLeadingPart, cornerMassVariation,
    sub_self, intervalIntegral.integral_zero, mul_zero]

theorem windowWeightedRemainder_intervalIntegrable (β : ℝ) (α : ℝ → ℝ)
    (a p s h k : ℝ) {N : ℕ} (hN : 0 < N) (hh : 0 ≤ h)
    (hp : p ∈ Icc (0:ℝ) 1) (hl : OW.repairLength p k ∈ Icc (0:ℝ) 2)
    (hf : BoundedDerivs (massVariationTerminal β α s h))
    (hR : WindowMassRegularity β α a p s h k N) (z : ℝ) :
    IntervalIntegrable (fun lam => windowWeightedRemainder β α a p s h k N lam z)
      volume 0 1 := by
  have hiS := sensitivitySum_intervalIntegrable _ hf hR.1 hR.2 (fun _ => z)
  have hiE : IntervalIntegrable (fun lam => windowLeadingEnergy (β^2)
      (jet β α 1 (s+4*h) z) (jet β α 2 (s+4*h) z) (jet β α 3 (s+4*h) z)
      α (interpolatedProfile α a lam) a p s h k N) volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact (leadingEnergy_continuous _ _ _ _ _ _ _).comp
      (interpolatedTranslation_continuous _ _ _ _ _ _ hN hh hp hl)
  simp_rw [windowWeightedRemainder_eq]
  exact hiS.sub (hiE.const_mul _)

theorem cornerMassRemainder_eq_integral (β : ℝ) (α : ℝ → ℝ)
    (r h k : ℝ) {N : ℕ} (hN : 0 < N) (hh : 0 ≤ h)
    (hl : OW.repairLength (1/2) k ∈ Icc (0:ℝ) 2)
    (hf : BoundedDerivs (massVariationTerminal β α (r-h) h))
    (hRk : WindowMassRegularity β α (α (r-h)) (1/2) (r-h) h k N)
    (hR0 : WindowMassRegularity β α (α (r-h)) (1/2) (r-h) h 0 N) (z : ℝ) :
    cornerMassRemainder β α r h k N z = ∫ lam in (0:ℝ)..1,
      windowWeightedRemainder β α (α (r-h)) (1/2) (r-h) h k N lam z-
      windowWeightedRemainder β α (α (r-h)) (1/2) (r-h) h 0 N lam z := by
  exact cornerMassVariation_sub_leading_eq_integral β α r h k hN hh hl hf hRk hR0 z

end SKBarriers2.Corner
