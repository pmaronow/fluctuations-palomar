module

public import SKBarriers2.Analysis.WeightedJets
public import SKBarriers2.Corner.FrozenRowsQR

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def epsilonFrameResidual (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (G : Vec3 → ℝ) (ε : ℝ) : Vec3 → ℝ :=
  epsilonSuffixRemainder l (Q.scale (1 - ε)) (fun y => ε * G y) 1

theorem epsilonFrameResidual_eq_actual (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (G : Vec3 → ℝ) (ε : ℝ) (x : Vec3) :
    epsilonFrameResidual l Q G ε x =
      epsilonChain l Q (fun y => G y - Q.value y) ε x -
        (riccatiRecursion l (Q.scale (1 - ε))).value x := by
  rw [epsilonChain_alternative_split]
  simp only [epsilonFrameResidual, epsilonSuffixRemainder, epsilonChain, one_mul]

theorem epsilonFrameResidual_nil (Q : QuadraticTerminal) (G : Vec3 → ℝ) (ε : ℝ) (x : Vec3) :
    epsilonFrameResidual [] Q G ε x = ε * G x := by
  exact (epsilonSuffixRemainder_nil _ _ _ _).trans (one_mul _)

theorem epsilonFrameResidual_cons (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (G : Vec3 → ℝ) (ε : ℝ) (u : ℝ × Vec3) (x : Vec3)
    (hc : Continuous (epsilonFrameResidual l Q G ε)) (hm : u.1 ≠ 0)
    (hD : 0 < (riccatiRecursion l (Q.scale (1 - ε))).precision u.1 u.2)
    (hpos : 0 < quadraticAverage (riccatiRecursion l (Q.scale (1 - ε))) u.1 u.2
      (fun y => Real.exp (u.1 * epsilonFrameResidual l Q G ε y)) x) :
    epsilonFrameResidual (u :: l) Q G ε x =
      let P := riccatiRecursion l (Q.scale (1 - ε))
      StepCalculus.tiltedAffineStep u.1 (quadraticMeanLinear P u.1 u.2)
        (quadraticNoiseConstant P u.1 u.2) ((Real.sqrt (P.precision u.1 u.2)⁻¹) • u.2)
        (epsilonFrameResidual l Q G ε) x := by
  have hExp : Continuous (fun y => Real.exp (u.1 * epsilonFrameResidual l Q G ε y)) :=
    Real.continuous_exp.comp ((continuous_const : Continuous (fun _ : Vec3 => u.1)).mul hc)
  change epsilonSuffixRemainder (u :: l) (Q.scale (1 - ε)) (fun y => ε * G y) 1 x = _
  rw [epsilonSuffixRemainder_cons l _ _ u 1 x hm hD hpos,
    quadraticAverage_eq_standard _ u.1 u.2 x hD
      (g := fun y => Real.exp (u.1 * epsilonSuffixRemainder l (Q.scale (1 - ε))
        (fun y => ε * G y) 1 y)) hExp,
    quadraticMeanTransition_eq_affine]
  simp only [StepCalculus.tiltedAffineStep, vectorStep, gaussianStep,
    ite_eq_right hm, positiveGaussianLogStep]
  rfl

theorem epsilonFrameResidual_cons_qPotential {r : ℕ} {B ε : ℝ}
    (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (G : Vec3 → ℝ) (u : ℝ × Vec3)
    (hr : 2 ≤ r) (hf : QPotential r B (epsilonFrameResidual l Q G ε))
    (hm : u.1 ∈ Ioc (0 : ℝ) 1)
    (hD : 0 < (riccatiRecursion l (Q.scale (1 - ε))).precision u.1 u.2)
    (hsmall : u.1 * (B * ‖(Real.sqrt
      ((riccatiRecursion l (Q.scale (1 - ε))).precision u.1 u.2)⁻¹) • u.2‖ ^ 2) ≤ 1 / 2) :
    let P := riccatiRecursion l (Q.scale (1 - ε))
    let w := (Real.sqrt (P.precision u.1 u.2)⁻¹) • u.2
    QPotential r ((B + StepCalculus.stepStabilityCoefficient r B * ‖w‖ ^ 2) *
      max 1 ‖quadraticMeanLinear P u.1 u.2‖ ^ r) (epsilonFrameResidual (u :: l) Q G ε) := by
  let P := riccatiRecursion l (Q.scale (1 - ε))
  let w := (Real.sqrt (P.precision u.1 u.2)⁻¹) • u.2
  have hLip (x y : Vec3) : |epsilonFrameResidual l Q G ε x - epsilonFrameResidual l Q G ε y| ≤
      B * ‖x - y‖ := by
    exact (hf.lipschitzWith (by omega)).norm_sub_le x y
  have hpos (x : Vec3) : 0 < quadraticAverage P u.1 u.2
      (fun y => Real.exp (u.1 * epsilonFrameResidual l Q G ε y)) x := by
    rw [quadraticAverage_eq_standard P u.1 u.2 x hD
      (g := fun y => Real.exp (u.1 * epsilonFrameResidual l Q G ε y))
      (Real.continuous_exp.comp
        ((continuous_const : Continuous (fun _ : Vec3 => u.1)).mul hf.smooth.continuous))]
    exact integral_exp_pos (integrable_exp_lipschitz_line hf.smooth.continuous hLip
      u.1 (quadraticMeanTransition P u.1 u.2 x) w)
  have heq : epsilonFrameResidual (u :: l) Q G ε =
      StepCalculus.tiltedAffineStep u.1 (quadraticMeanLinear P u.1 u.2)
        (quadraticNoiseConstant P u.1 u.2) w (epsilonFrameResidual l Q G ε) := by
    funext x
    exact epsilonFrameResidual_cons l Q G ε u x hf.smooth.continuous hm.1.ne' hD (hpos x)
  rw [heq]
  exact StepCalculus.qPotential_tiltedAffineStep hf hr ⟨hm.1.le, hm.2⟩ _ _ _ hsmall

theorem wJets_affine_tiltedAverage {n p : ℕ} {B C m : ℝ} {f g : Vec3 → ℝ}
    (hf : QPotential (n + 1) B f) (hg : WJets n C p g)
    (hm : m ∈ Icc (0 : ℝ) 1) (A : Vec3 →L[ℝ] Vec3) (b v : Vec3) (hv : ‖v‖ ≤ 1) :
    WJets n ((StepCalculus.noiseAverageCoefficient n p B * C) *
      (1 + ‖A‖ + ‖b‖) ^ p * max 1 ‖A‖ ^ n) p
      (fun x => StepCalculus.tiltedAverage m v f g (A x + b)) := by
  exact (StepCalculus.wJets_tiltedAverage hf hg hm v hv).comp_affine A b

theorem scalarData_centered_terminal_wJets {β s h : ℝ} (D : ScalarData β)
    (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) (r : ℕ) (hr : 1 ≤ r) (z : ℝ) :
    WJets r (terminalJetBound D r) 1
      (fun x : Vec3 => frozenTerminal β (cdf (D.μ : Measure ℝ)) s h (x + (fun _ => z)) -
        frozenTerminal β (cdf (D.μ : Measure ℝ)) s h (fun _ => z)) := by
  exact (scalarData_frozenTerminal_qPotential D r ht).centered_wJets hr _

theorem scalarData_epsilonFrameResidual_nil_wJets {β s h : ℝ} (D : ScalarData β)
    (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) (r : ℕ) (hr : 1 ≤ r) (z ε : ℝ) :
    WJets r (|ε| * terminalJetBound D r) 1
      (fun x : Vec3 => epsilonFrameResidual []
        (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) s h z)
        (frozenTerminal β (cdf (D.μ : Measure ℝ)) s h) ε (x + (fun _ => z)) -
          ε * frozenTerminal β (cdf (D.μ : Measure ℝ)) s h (fun _ => z)) := by
  have heq : (fun x : Vec3 => epsilonFrameResidual []
        (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) s h z)
        (frozenTerminal β (cdf (D.μ : Measure ℝ)) s h) ε (x + (fun _ => z)) -
          ε * frozenTerminal β (cdf (D.μ : Measure ℝ)) s h (fun _ => z)) =
      fun x : Vec3 => ε • (frozenTerminal β (cdf (D.μ : Measure ℝ)) s h (x + (fun _ => z)) -
        frozenTerminal β (cdf (D.μ : Measure ℝ)) s h (fun _ => z)) := by
    funext x
    rw [epsilonFrameResidual_nil]
    simp only [smul_eq_mul, mul_sub]
  rw [heq]
  exact (scalarData_centered_terminal_wJets D ht r hr z).const_smul ε

def frameSpatialBudget (r : ℕ) (B : ℝ) : ℕ → ℝ
  | 0 => B
  | n + 1 => (2 : ℝ) ^ r * (frameSpatialBudget r B n +
      StepCalculus.stepStabilityCoefficient r (frameSpatialBudget r B n))

theorem frameSpatialBudget_nonneg (r n : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ frameSpatialBudget r B n := by
  induction n with
  | zero => exact hB
  | succ n ih =>
    exact mul_nonneg (by positivity)
      (add_nonneg ih (StepCalculus.stepStabilityCoefficient_nonneg r ih))

theorem frameSpatialBudget_mono (r : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    Monotone (frameSpatialBudget r B) := by
  apply monotone_nat_of_le_succ
  intro n
  have hN := frameSpatialBudget_nonneg r n hB
  have hK := StepCalculus.stepStabilityCoefficient_nonneg r hN
  have H := mul_le_mul_of_nonneg_right
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ) ^ r) (add_nonneg hN hK)
  change frameSpatialBudget r B n ≤ (2 : ℝ) ^ r * (_ + _)
  nlinarith

theorem epsilonFrameResidual_qPotential_of_geometry {r : ℕ} {B ε : ℝ}
    (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (G : Vec3 → ℝ) (hr : 2 ≤ r)
    (hbase : QPotential r B (fun x => ε * G x))
    (H : ∀ u t, u :: t <:+ l →
      let P := riccatiRecursion t (Q.scale (1 - ε))
      let w := (Real.sqrt (P.precision u.1 u.2)⁻¹) • u.2
      u.1 ∈ Ioc (0 : ℝ) 1 ∧ 0 < P.precision u.1 u.2 ∧
        ‖quadraticMeanLinear P u.1 u.2‖ ≤ 2 ∧ ‖w‖ ≤ 1 ∧
          u.1 * (frameSpatialBudget r B t.length * ‖w‖ ^ 2) ≤ 1 / 2) :
    QPotential r (frameSpatialBudget r B l.length) (epsilonFrameResidual l Q G ε) := by
  induction l with
  | nil =>
    have heq : epsilonFrameResidual [] Q G ε = fun x => ε * G x :=
      funext (epsilonFrameResidual_nil Q G ε)
    rw [heq]
    exact hbase
  | cons u t ih =>
    have HI := ih (fun v s hs => H v s (hs.trans (List.suffix_cons u t)))
    rcases H u t (List.suffix_refl _) with ⟨hm, hD, hA, hw, hsmall⟩
    have hstep := epsilonFrameResidual_cons_qPotential t Q G u hr HI hm hD hsmall
    have hN := frameSpatialBudget_nonneg r t.length hbase.nonneg
    have hK := StepCalculus.stepStabilityCoefficient_nonneg r hN
    apply hstep.mono
    change (_ + _ * _ ^ 2) * max 1 ‖quadraticMeanLinear
      (riccatiRecursion t (Q.scale (1 - ε))) u.1 u.2‖ ^ r ≤
        (2 : ℝ) ^ r * (frameSpatialBudget r B t.length + _)
    have hw2 : ‖(Real.sqrt ((riccatiRecursion t (Q.scale (1 - ε))).precision u.1 u.2)⁻¹) • u.2‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg ((Real.sqrt
        ((riccatiRecursion t (Q.scale (1 - ε))).precision u.1 u.2)⁻¹) • u.2)]
    calc
      _ ≤ (frameSpatialBudget r B t.length +
          StepCalculus.stepStabilityCoefficient r (frameSpatialBudget r B t.length)) * (2 : ℝ) ^ r := by
        apply mul_le_mul
        · nlinarith [mul_le_mul_of_nonneg_left hw2 hK]
        · exact pow_le_pow_left₀ (by positivity) (max_le (by norm_num) hA) r
        · positivity
        · exact add_nonneg hN hK
      _ = _ := by ring

theorem quadraticMeanLinear_norm_le_two {P : QuadraticTerminal} {H m : ℝ}
    (hH : 0 ≤ H) (hP : ∀ i j, |P.hessian i j| ≤ H) (hm : m ∈ Icc (0 : ℝ) 1)
    (v : Vec3) (hD : 1 / 2 ≤ P.precision m v) (hsmall : 6 * H * directionEnergy v ≤ 1) :
    ‖quadraticMeanLinear P m v‖ ≤ 2 := by
  have hDpos : 0 < P.precision m v := by linarith
  have hnum : 3 * m * H * directionEnergy v ≤ 3 * H * directionEnergy v := by
    nlinarith [mul_le_mul_of_nonneg_right hm.2
      (by positivity [directionEnergy_nonneg v] : 0 ≤ 3 * H * directionEnergy v)]
  have hfrac : 3 * m * H * directionEnergy v / P.precision m v ≤ 1 := by
    apply (div_le_iff₀ hDpos).mpr
    linarith
  apply (quadraticMeanLinear P m v).opNorm_le_bound (by norm_num : (0 : ℝ) ≤ 2)
  intro x
  have HL := quadraticMeanTransition_lipschitz P hH hP hm.1 v hDpos x 0
  rw [quadraticMeanTransition_eq_affine, quadraticMeanTransition_eq_affine] at HL
  simp only [map_zero, zero_add, add_sub_cancel_right, sub_zero] at HL
  have hcoef : 1 + 3 * m * H * directionEnergy v / P.precision m v ≤ 2 := by linarith
  exact HL.trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg x))

theorem quadraticNoise_norm_sq_le {P : QuadraticTerminal} {m : ℝ} (v : Vec3)
    (hD : 1 / 2 ≤ P.precision m v) :
    ‖(Real.sqrt (P.precision m v)⁻¹) • v‖ ^ 2 ≤ 2 * directionEnergy v := by
  have hDpos : 0 < P.precision m v := by linarith
  have hInv : (P.precision m v)⁻¹ ≤ 2 := by
    have H := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hD
    norm_num at H
    exact H
  have hv : ‖v‖ ^ 2 ≤ directionEnergy v :=
    pow_le_pow_left₀ (norm_nonneg v) (norm_le_directionSize v) 2
  calc
    _ = (P.precision m v)⁻¹ * ‖v‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
        Real.sq_sqrt (inv_nonneg.mpr hDpos.le)]
    _ ≤ 2 * directionEnergy v :=
      mul_le_mul hInv hv (sq_nonneg _) (by norm_num)

theorem epsilonFrameResidual_qPotential_of_small_directions {r : ℕ} {B C ε : ℝ}
    (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (G : Vec3 → ℝ) (hr : 2 ≤ r)
    (hbase : QPotential r B (fun x => ε * G x)) (hC : 0 < C)
    (hQ : ∀ i j, |(Q.scale (1 - ε)).hessian i j| ≤ C) (hlen : l.length ≤ 12)
    (hm : ∀ u ∈ l, u.1 ∈ Ioc (0 : ℝ) 1)
    (hv : ∀ u ∈ l,
      (6 * ((2 : ℝ) ^ 12 * C) + 4 * frameSpatialBudget r B 12 + 2) * directionEnergy u.2 ≤ 1) :
    QPotential r (frameSpatialBudget r B l.length) (epsilonFrameResidual l Q G ε) := by
  let H := (2 : ℝ) ^ 12 * C
  let S := 6 * H + 4 * frameSpatialBudget r B 12 + 2
  have hH : 0 < H := by dsimp only [H]; positivity
  have hT := frameSpatialBudget_nonneg r 12 hbase.nonneg
  have hSH : 6 * H ≤ S := by dsimp only [S]; linarith
  have hST : 4 * frameSpatialBudget r B 12 ≤ S := by dsimp only [S]; linarith
  have hS2 : 2 ≤ S := by dsimp only [S]; linarith
  apply epsilonFrameResidual_qPotential_of_geometry l Q G hr hbase
  intro u t hs
  have htlen : t.length ≤ 12 := by have HH := hs.length_le; simp only [List.length_cons] at HH; omega
  have hPow : (2 : ℝ) ^ t.length * C ≤ H :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) htlen) hC.le
  have hsub : t ⊆ l := ((List.suffix_cons u t).trans hs).subset
  have hmu := hm u (hs.subset List.mem_cons_self)
  have hE : S * directionEnergy u.2 ≤ 1 := hv u (hs.subset List.mem_cons_self)
  have h6 : 6 * H * directionEnergy u.2 ≤ 1 :=
    (mul_le_mul_of_nonneg_right hSH (directionEnergy_nonneg _)).trans hE
  have h2 : 2 * H * directionEnergy u.2 ≤ 1 := by
    nlinarith [mul_nonneg hH.le (directionEnergy_nonneg u.2)]
  have hPt := riccatiAdmissible_of_small_directions t (Q.scale (1 - ε)) hC hQ
    (fun v hv' => hm v (hsub hv')) (fun v hv' => by
      have hV := hv v (hsub hv')
      have hc : 2 * ((2 : ℝ) ^ t.length * C) ≤ S := by linarith
      exact (mul_le_mul_of_nonneg_right hc (directionEnergy_nonneg _)).trans hV)
  let P := riccatiRecursion t (Q.scale (1 - ε))
  have hP : ∀ i j, |P.hessian i j| ≤ H := fun i j => (hPt.2 i j).trans hPow
  have hD := (P.update_small hH hP ⟨hmu.1.le, hmu.2⟩ u.2 h2).1
  have hA := quadraticMeanLinear_norm_le_two hH.le hP ⟨hmu.1.le, hmu.2⟩ u.2 hD h6
  have hw2 := quadraticNoise_norm_sq_le u.2 hD
  have hnoise : 2 * directionEnergy u.2 ≤ 1 :=
    (mul_le_mul_of_nonneg_right hS2 (directionEnergy_nonneg _)).trans hE
  have hw : ‖(Real.sqrt (P.precision u.1 u.2)⁻¹) • u.2‖ ≤ 1 := by
    nlinarith [norm_nonneg ((Real.sqrt (P.precision u.1 u.2)⁻¹) • u.2)]
  have hBT : frameSpatialBudget r B t.length ≤ frameSpatialBudget r B 12 :=
    frameSpatialBudget_mono r hbase.nonneg htlen
  have hBn := frameSpatialBudget_nonneg r t.length hbase.nonneg
  have hprod : u.1 * (frameSpatialBudget r B t.length *
      ‖(Real.sqrt (P.precision u.1 u.2)⁻¹) • u.2‖ ^ 2) ≤
        2 * frameSpatialBudget r B 12 * directionEnergy u.2 := by
    calc
      _ ≤ frameSpatialBudget r B t.length * ‖(Real.sqrt (P.precision u.1 u.2)⁻¹) • u.2‖ ^ 2 :=
        mul_le_of_le_one_left (by positivity) hmu.2
      _ ≤ frameSpatialBudget r B 12 * (2 * directionEnergy u.2) :=
        mul_le_mul hBT hw2 (sq_nonneg _) hT
      _ = _ := by ring
  have hfour : 4 * frameSpatialBudget r B 12 * directionEnergy u.2 ≤ 1 :=
    (mul_le_mul_of_nonneg_right hST (directionEnergy_nonneg _)).trans hE
  exact ⟨hmu, by linarith, hA, hw, by linarith⟩

theorem scalarData_epsilonFrameResidual_spatial_qPotential {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) (R : ℕ) (hR : 2 ≤ R) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ ε ∈ Icc (-1 : ℝ) 2, ∀ t : List (ℝ × Vec3),
      t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
      QPotential R C (epsilonFrameResidual t
        (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
        (frozenTerminal β (cdf (D.μ : Measure ℝ)) (r - h) h) ε) := by
  let B := 2 * terminalJetBound D R + 1
  let J := 2 * scalarTerminalJetBound D 2 + 1
  let C := frameSpatialBudget R B 12
  let S := 6 * ((2 : ℝ) ^ 12 * J) + 4 * C + 2
  let K := 6 * (|β| + 1)
  have hB : 0 < B := by dsimp only [B]; positivity [terminalJetBound_nonneg D R]
  have hJ : 0 < J := by dsimp only [J]; positivity [scalarTerminalJetBound_nonneg D 2]
  have hC : 0 < C := hB.trans_le (frameSpatialBudget_mono R hB.le (by omega : 0 ≤ 12))
  have hS : 0 < S := by dsimp only [S]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  let h₀ := min (l / 2) (min ((D.q - u) / 6) (S * K ^ 2)⁻¹)
  have hh₀ : 0 < h₀ := lt_min (by positivity)
    (lt_min (by positivity) (inv_pos.mpr (by positivity)))
  refine ⟨C, h₀, hC, hh₀, ?_⟩
  intro r hr h hh hhsmall k hk z ε hε t ht
  have hhl : h ≤ l / 2 := hhsmall.trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 6 := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhS : h ≤ (S * K ^ 2)⁻¹ := (hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hs : 0 < r - h := by linarith [hr.1]
  have htime : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith
    · linarith [hr.2, D.q_mem.2]
  have he : |ε| ≤ 2 := abs_le.mpr ⟨by linarith [hε.1], hε.2⟩
  have he' : |1 - ε| ≤ 2 := abs_le.mpr ⟨by linarith [hε.2], by linarith [hε.1]⟩
  let α := cdf (D.μ : Measure ℝ)
  let Q := terminalTaylorQuadratic β α (r - h) h z
  let G := frozenTerminal β α (r - h) h
  have hbase : QPotential R B (fun x => ε * G x) := by
    apply ((scalarData_frozenTerminal_qPotential D R htime).const_mul ε).mono
    have H := mul_le_mul_of_nonneg_right he (terminalJetBound_nonneg D R)
    dsimp only [B]
    linarith
  have hQ : ∀ i j, |(Q.scale (1 - ε)).hessian i j| ≤ J := by
    have HQ := terminalTaylorQuadratic_hessian_bound β α (r - h) h z
      (scalarTerminalJetBound D 2) (scalarTerminalJetBound_nonneg D 2)
      (scalarData_jet_le D (by norm_num : 1 ≤ 2) le_rfl htime z)
    intro i j
    change |(1 - ε) * Q.hessian i j| ≤ J
    rw [abs_mul]
    have H := mul_le_mul he' (HQ i j) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    exact H.trans (by dsimp only [J]; linarith)
  have hlen : t.length ≤ 12 := by simpa only [frozenSchedule_length] using ht.length_le
  have hmass := frozenSchedule_masses β (α (r - h)) (1 / 2) h k
    ⟨scalarData_cdf_pos_of_pos D hs, cdf_le_one _ _⟩
  have hsmall : (S * K ^ 2) * h ≤ 1 :=
    (mul_le_mul_of_nonneg_left hhS (by positivity : 0 ≤ S * K ^ 2)).trans_eq
      (mul_inv_cancel₀ (by positivity))
  have hv (v : ℝ × Vec3) (hv : v ∈ t) :
      (6 * ((2 : ℝ) ^ 12 * J) + 4 * frameSpatialBudget R B 12 + 2) * directionEnergy v.2 ≤ 1 := by
    have HE := (frozenSchedule_centered_direction_scale hh.le hk (ht.subset hv)).2
    rw [Real.sq_sqrt hh.le] at HE
    change S * directionEnergy v.2 ≤ 1
    calc
      _ ≤ S * (K ^ 2 * h) := mul_le_mul_of_nonneg_left HE hS.le
      _ = (S * K ^ 2) * h := by ring
      _ ≤ 1 := hsmall
  have H := epsilonFrameResidual_qPotential_of_small_directions t Q G hR hbase hJ hQ hlen
    (fun v hv' => hmass v (ht.subset hv')) hv
  exact H.mono (frameSpatialBudget_mono R hB.le hlen)

end SKBarriers2.Corner
