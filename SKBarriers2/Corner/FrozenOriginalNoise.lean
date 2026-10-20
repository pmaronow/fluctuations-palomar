module

public import SKBarriers2.Corner.FrozenDirections
public import SKBarriers2.Corner.FrozenCoefficientRegularity

@[expose] public section

noncomputable section
open scoped BigOperators Matrix ContDiff Topology NNReal
open Set MeasureTheory ProbabilityTheory Filter OAI.SK.Analytic SKOptimized.Overshoot
namespace SKBarriers2.Corner

def SameQuadraticHessian (Q R : QuadraticTerminal) : Prop :=
  ∀ i j, Q.hessian i j = R.hessian i j

private theorem sameHessian_precision {Q R : QuadraticTerminal}
    (H : SameQuadraticHessian Q R) (m : ℝ) (v : Vec3) :
    Q.precision m v = R.precision m v := by
  change ∀ i j, Q.hessian i j = R.hessian i j at H
  simp only [QuadraticTerminal.precision, QuadraticTerminal.curvature,
    QuadraticTerminal.hessianDirection, H]

private theorem sameHessian_update {Q R : QuadraticTerminal}
    (H : SameQuadraticHessian Q R) (m : ℝ) (v : Vec3) :
    SameQuadraticHessian (Q.update m v) (R.update m v) := by
  change ∀ i j, Q.hessian i j = R.hessian i j at H
  intro i j
  simp only [QuadraticTerminal.update, QuadraticTerminal.hessianDirection,
    H, sameHessian_precision H]

private theorem sameHessian_recursion {Q R : QuadraticTerminal}
    (H : SameQuadraticHessian Q R) (l : List (ℝ × Vec3)) :
    SameQuadraticHessian (riccatiRecursion l Q) (riccatiRecursion l R) := by
  induction l with
  | nil => exact H
  | cons u l ih => exact sameHessian_update ih u.1 u.2

def labelledQuadraticPath {ι : Type} (m : ι → ℝ) (v : ι → Vec3) :
    List ι → QuadraticTerminal → Vec3 → (ι → ℝ) → Vec3
  | [], _, x, _ => x
  | j :: l, Q, x, g => labelledQuadraticPath m v l Q
      (quadraticNoiseConstant (riccatiRecursion (l.map (fun i => (m i, v i))) Q) (m j) (v j) +
        quadraticNoiseCLM (riccatiRecursion (l.map (fun i => (m i, v i))) Q) (m j) (v j) (x, g j)) g

theorem labelledQuadraticPath_map {ι κ : Type} (f : ι → κ)
    (m : κ → ℝ) (v : κ → Vec3) (l : List ι) (Q : QuadraticTerminal) (x : Vec3) (g : κ → ℝ) :
    labelledQuadraticPath m v (l.map f) Q x g =
      labelledQuadraticPath (m ∘ f) (v ∘ f) l Q x (g ∘ f) := by
  induction l generalizing x with
  | nil => rfl
  | cons j l ih => simp only [List.map_cons, labelledQuadraticPath, List.map_map, ih, Function.comp_def]

theorem labelledQuadraticPath_append {ι : Type} (m : ι → ℝ) (v : ι → Vec3)
    (l t : List ι) (Q : QuadraticTerminal) (x : Vec3) (g : ι → ℝ) :
    labelledQuadraticPath m v (l ++ t) Q x g =
      labelledQuadraticPath m v t Q
        (labelledQuadraticPath m v l (riccatiRecursion (t.map (fun i => (m i, v i))) Q) x g) g := by
  induction l generalizing x with
  | nil => rfl
  | cons j l ih =>
    simp only [List.cons_append, labelledQuadraticPath, List.map_append,
      riccatiRecursion_append, ih]

theorem quadraticNoisePath_shift (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (x w : Vec3) (g : Fin l.length → ℝ) (t : ℝ) :
    quadraticNoisePath l Q (x + t • w) g =
      quadraticNoisePath l Q x g + t • gaussianPathLinear l Q w := by
  obtain ⟨c, L, hL⟩ := quadraticNoisePath_affine l Q
  have hz : L (w, 0) = gaussianPathLinear l Q w := by
    have H := gaussianPathMean_shift l Q 0 w 1
    rw [← quadraticNoisePath_zero, ← quadraticNoisePath_zero] at H
    simp only [zero_add, one_smul] at H
    rw [hL (w, 0), hL (0, 0)] at H
    have hz : L (0, 0) = 0 := map_zero L
    rw [hz, add_zero] at H
    exact add_left_cancel H
  have hp : (x + t • w, g) = (x, g) + t • (w, (0 : Fin l.length → ℝ)) := by simp
  rw [hL (x + t • w, g), hp, map_add, map_smul, hz, hL (x, g)]
  exact (add_assoc _ _ _).symm

def quadraticNoisePart (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (g : Fin l.length → ℝ) : Vec3 := quadraticNoisePath l Q 0 g - quadraticNoisePath l Q 0 0

theorem quadraticNoisePath_eq_mean_add_noise (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (x : Vec3) (g : Fin l.length → ℝ) :
    quadraticNoisePath l Q x g = gaussianPathMean l Q x + quadraticNoisePart l Q g := by
  obtain ⟨c, L, hL⟩ := quadraticNoisePath_affine l Q
  rw [← quadraticNoisePath_zero, quadraticNoisePart, hL (x, g), hL (x, 0), hL (0, g), hL (0, 0)]
  have hp : (x, g) = (x, (0 : Fin l.length → ℝ)) + (0, g) := by simp
  have hz : L (0, 0) = 0 := map_zero L
  rw [hp, map_add, hz]
  abel

theorem quadraticNoisePart_cons (u : ℝ × Vec3) (l : List (ℝ × Vec3))
    (Q : QuadraticTerminal) (g : Fin (u :: l).length → ℝ) :
    quadraticNoisePart (u :: l) Q g =
      (Real.sqrt (((riccatiRecursion l Q).precision u.1 u.2)⁻¹) * g 0) •
        gaussianPathLinear l Q u.2 + quadraticNoisePart l Q (fun i => g i.succ) := by
  have he (x : Vec3) (g : Fin (u :: l).length → ℝ) :
      quadraticNoisePath (u :: l) Q x g =
        quadraticNoisePath l Q
          (quadraticMeanTransition (riccatiRecursion l Q) u.1 u.2 x +
            (Real.sqrt (((riccatiRecursion l Q).precision u.1 u.2)⁻¹) * g 0) • u.2)
          (fun i => g i.succ) := by
    rw [quadraticNoisePath, quadraticNoise_affine]
    apply congrArg (fun y => quadraticNoisePath l Q y (fun i => g i.succ))
    unfold quadraticMeanTransition
    module
  rw [quadraticNoisePart, he, he, quadraticNoisePath_shift]
  simp only [Pi.zero_apply, mul_zero, zero_smul, add_zero]
  rw [quadraticNoisePath_eq_mean_add_noise l Q _ (fun i => g i.succ)]
  have hz : quadraticNoisePath l Q
      (quadraticMeanTransition (riccatiRecursion l Q) u.1 u.2 0) (fun _ => 0) =
      gaussianPathMean l Q (quadraticMeanTransition (riccatiRecursion l Q) u.1 u.2 0) :=
    quadraticNoisePath_zero l Q _
  rw [hz]
  abel

def labelledNoisePart {ι : Type} (m : ι → ℝ) (v : ι → Vec3) :
    List ι → QuadraticTerminal → (ι → ℝ) → Vec3
  | [], _, _ => 0
  | j :: l, Q, g =>
      (Real.sqrt (((riccatiRecursion (l.map (fun i => (m i, v i))) Q).precision (m j) (v j))⁻¹) * g j) •
        gaussianPathLinear (l.map (fun i => (m i, v i))) Q (v j) + labelledNoisePart m v l Q g

theorem labelledQuadraticPath_eq_original {ι : Type} (m : ι → ℝ) (v : ι → Vec3)
    (l : List ι) (Q : QuadraticTerminal) (x : Vec3) (g : ι → ℝ) :
    labelledQuadraticPath m v l Q x g =
      quadraticNoisePath (l.map (fun j => (m j, v j))) Q x
        (fun j => g (l[j.val]'(by simpa using j.isLt))) := by
  induction l generalizing x with
  | nil => rfl
  | cons j l ih => exact ih _

theorem labelledNoisePart_eq_original {ι : Type} (m : ι → ℝ) (v : ι → Vec3)
    (l : List ι) (Q : QuadraticTerminal) (g : ι → ℝ) :
    labelledNoisePart m v l Q g =
      quadraticNoisePart (l.map (fun j => (m j, v j))) Q
        (fun j => g (l[j.val]'(by simpa using j.isLt))) := by
  induction l with
  | nil => change (0 : Vec3) = 0 - 0; simp
  | cons j l ih =>
    change labelledNoisePart m v (j :: l) Q g =
      quadraticNoisePart ((m j, v j) :: l.map (fun j => (m j, v j))) Q
        (fun i => g ((j :: l)[i.val]'(by simpa using i.isLt)))
    rw [labelledNoisePart, quadraticNoisePart_cons]
    exact congrArg (fun z =>
      (Real.sqrt (((riccatiRecursion (l.map (fun i => (m i, v i))) Q).precision (m j) (v j))⁻¹) * g j) •
        gaussianPathLinear (l.map (fun i => (m i, v i))) Q (v j) + z) ih

private theorem gaussianPathLinear_sameHessian {Q R : QuadraticTerminal}
    (H : SameQuadraticHessian Q R) (l : List (ℝ × Vec3)) (w : Vec3) :
    gaussianPathLinear l Q w = gaussianPathLinear l R w := by
  induction l generalizing w with
  | nil => rfl
  | cons u l ih =>
    have HR := sameHessian_recursion H l
    change ∀ i j, (riccatiRecursion l Q).hessian i j = (riccatiRecursion l R).hessian i j at HR
    simp only [gaussianPathLinear, sameHessian_precision HR,
      QuadraticTerminal.hessianDirection, HR, ih]

private theorem labelledNoisePart_sameHessian {ι : Type} {Q R : QuadraticTerminal}
    (H : SameQuadraticHessian Q R) (m : ι → ℝ) (v : ι → Vec3) (l : List ι) (g : ι → ℝ) :
    labelledNoisePart m v l Q g = labelledNoisePart m v l R g := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [labelledNoisePart, sameHessian_precision (sameHessian_recursion H _),
      gaussianPathLinear_sameHessian H, ih]

private theorem hessian_scaled_precision {Q R : QuadraticTerminal} {χ a c m : ℝ}
    (H : ∀ i j, Q.hessian i j = χ * R.hessian i j) (v : Vec3) :
    Q.precision (a * m) (c • v) = R.precision ((a * χ * c ^ 2) * m) v := by
  simp only [QuadraticTerminal.precision, QuadraticTerminal.curvature,
    QuadraticTerminal.hessianDirection, H, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_succ]
  ring

private theorem hessian_scaled_update {Q R : QuadraticTerminal} {χ a c m : ℝ}
    (H : ∀ i j, Q.hessian i j = χ * R.hessian i j) (v : Vec3) :
    ∀ i j, (Q.update (a * m) (c • v)).hessian i j =
      χ * (R.update ((a * χ * c ^ 2) * m) v).hessian i j := by
  intro i j
  simp only [QuadraticTerminal.update, hessian_scaled_precision H,
    QuadraticTerminal.hessianDirection, H, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_succ,
    div_eq_mul_inv]
  ring

theorem riccatiRecursion_hessian_scaled {ι : Type} (m : ι → ℝ) (v : ι → Vec3)
    (l : List ι) {Q R : QuadraticTerminal} {χ a c : ℝ}
    (H : ∀ i j, Q.hessian i j = χ * R.hessian i j) :
    ∀ i j,
      (riccatiRecursion (l.map (fun j => (a * m j, c • v j))) Q).hessian i j =
        χ * (riccatiRecursion (l.map (fun j => ((a * χ * c ^ 2) * m j, v j))) R).hessian i j := by
  induction l with
  | nil => exact H
  | cons j l ih => exact hessian_scaled_update ih (v j)

theorem gaussianPathLinear_scaled {ι : Type} (m : ι → ℝ) (v : ι → Vec3)
    (l : List ι) {Q R : QuadraticTerminal} {χ a c : ℝ}
    (H : ∀ i j, Q.hessian i j = χ * R.hessian i j) (w : Vec3) :
    gaussianPathLinear (l.map (fun j => (a * m j, c • v j))) Q (c • w) =
      c • gaussianPathLinear (l.map (fun j => ((a * χ * c ^ 2) * m j, v j))) R w := by
  induction l generalizing w with
  | nil => rfl
  | cons j l ih =>
    have HR := riccatiRecursion_hessian_scaled m v l (a := a) (c := c) H
    have hp := hessian_scaled_precision (a := a) (c := c) (m := m j) HR (v j)
    have he : c • w + (a * m j /
        (riccatiRecursion (l.map (fun j => (a * m j, c • v j))) Q).precision
          (a * m j) (c • v j) *
        (∑ i, (c • w) i *
          (riccatiRecursion (l.map (fun j => (a * m j, c • v j))) Q).hessianDirection (c • v j) i)) •
          (c • v j) =
        c • (w + ((a * χ * c ^ 2) * m j /
          (riccatiRecursion (l.map (fun j => ((a * χ * c ^ 2) * m j, v j))) R).precision
            ((a * χ * c ^ 2) * m j) (v j) *
          (∑ i, w i *
            (riccatiRecursion (l.map (fun j => ((a * χ * c ^ 2) * m j, v j))) R).hessianDirection (v j) i)) • v j) := by
      ext i
      simp only [hp, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        QuadraticTerminal.hessianDirection, HR, Fin.sum_univ_succ, div_eq_mul_inv]
      ring
    simp only [List.map_cons, gaussianPathLinear, he, ih]

theorem labelledNoisePart_scaled {ι : Type} (m : ι → ℝ) (v : ι → Vec3)
    (l : List ι) {Q R : QuadraticTerminal} {χ a c : ℝ}
    (H : ∀ i j, Q.hessian i j = χ * R.hessian i j) (g : ι → ℝ) :
    labelledNoisePart (fun j => a * m j) (fun j => c • v j) l Q g =
      c • labelledNoisePart (fun j => (a * χ * c ^ 2) * m j) v l R g := by
  induction l with
  | nil => simp only [labelledNoisePart, smul_zero]
  | cons j l ih =>
    have HR := riccatiRecursion_hessian_scaled m v l (a := a) (c := c) H
    simp only [labelledNoisePart, hessian_scaled_precision HR,
      gaussianPathLinear_scaled m v l H, ih, smul_add, smul_smul]
    congr 1
    congr 1
    ring

private theorem noisePrecisionsPositive_cons (u : ℝ × Vec3) (l : List (ℝ × Vec3))
    (Q : QuadraticTerminal) :
    NoisePrecisionsPositive (u :: l) Q ↔
      NoisePrecisionsPositive l Q ∧ 0 < (riccatiRecursion l Q).precision u.1 u.2 := by
  simp only [NoisePrecisionsPositive, riccatiPrecisions, List.mem_cons, forall_eq_or_imp, and_comm]

private theorem parameter_precision_contDiffAt {E ι : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : List ι) (m : ι → E → ℝ) (v : ι → E → Vec3) (Q : E → QuadraticTerminal) {p : E}
    (hm : ∀ j ∈ l, ContDiffAt ℝ ∞ (m j) p)
    (hv : ∀ j ∈ l, ∀ i, ContDiffAt ℝ ∞ (fun x => v j x i) p)
    (hQ : ∀ i j, ContDiffAt ℝ ∞ (fun x => (Q x).hessian i j) p)
    (hP : NoisePrecisionsPositive (l.map (fun j => (m j p, v j p))) (Q p))
    {b : E → ℝ} {w : E → Vec3} (hb : ContDiffAt ℝ ∞ b p)
    (hw : ∀ i, ContDiffAt ℝ ∞ (fun x => w x i) p) :
    ContDiffAt ℝ ∞ (fun x =>
      (riccatiRecursion (l.map (fun j => (m j x, v j x))) (Q x)).precision (b x) (w x)) p := by
  have hH := riccatiRecursion_hessian_contDiffAt l m v Q hm hv hQ hP
  exact contDiffAt_const.sub (hb.mul (ContDiffAt.sum (fun i _ => (hw i).mul
    (ContDiffAt.sum (fun j _ => (hH i j).mul (hw j))))))

theorem labelledNoisePart_contDiffAt {E ι : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : List ι) (m : ι → E → ℝ) (v : ι → E → Vec3) (Q : E → QuadraticTerminal) {p : E}
    (hm : ∀ j ∈ l, ContDiffAt ℝ ∞ (m j) p)
    (hv : ∀ j ∈ l, ∀ i, ContDiffAt ℝ ∞ (fun x => v j x i) p)
    (hQ : ∀ i j, ContDiffAt ℝ ∞ (fun x => (Q x).hessian i j) p)
    (hP : NoisePrecisionsPositive (l.map (fun j => (m j p, v j p))) (Q p))
    (g : ι → ℝ) :
    ∀ i, ContDiffAt ℝ ∞ (fun x => labelledNoisePart (fun j => m j x) (fun j => v j x) l (Q x) g i) p := by
  induction l with
  | nil => intro i; exact contDiffAt_const
  | cons j l ih =>
    have HP := (noisePrecisionsPositive_cons _ _ _).mp hP
    have hmt := fun j hj => hm j (List.mem_cons_of_mem _ hj)
    have hvt := fun j hj => hv j (List.mem_cons_of_mem _ hj)
    have hmj := hm j List.mem_cons_self
    have hvj := hv j List.mem_cons_self
    have hPrec := parameter_precision_contDiffAt l m v Q hmt hvt hQ HP.1 hmj hvj
    have hS := (hPrec.inv (ne_of_gt HP.2)).sqrt (inv_ne_zero (ne_of_gt HP.2))
    have hL := gaussianPathLinear_contDiffAt l m v Q hmt hvt hQ HP.1 (v j) hvj
    have hN := ih hmt hvt HP.1
    intro i
    exact ((hS.mul contDiffAt_const).mul (hL i)).add (hN i)

def normalizedNoiseQuadratic : QuadraticTerminal := separableTaylorQuadratic 0 0 1 0

def frozenNoiseBaseDomain : Set (ℝ × ℝ) := {x | |x.2| < 3 / 5}

private theorem frozenNoiseBaseDomain_isOpen : IsOpen frozenNoiseBaseDomain :=
  isOpen_lt (continuous_abs.comp continuous_snd) continuous_const

private theorem frozenUnitDirection_contDiffAt (β : ℝ) {x : ℝ × ℝ}
    (hx : x ∈ frozenNoiseBaseDomain) (j : Fin 12) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => frozenUnitDirection β p.2 j i) x := by
  have hr : 0 < 2 - OW.repairLength (1 / 2) x.2 := by
    have hk : |x.2| < 3 / 5 := hx
    have hsq : x.2 ^ 2 < (3 / 5 : ℝ) ^ 2 := by
      have H := mul_pos (sub_pos.mpr hk) (by positivity : 0 < (3 / 5 : ℝ) + |x.2|)
      nlinarith [sq_abs x.2]
    norm_num [OW.repairLength, varianceCoefficient, tentWeight, rampWeight]
    nlinarith
  have hroot : ContDiffAt ℝ ∞
      (fun p : ℝ × ℝ => Real.sqrt (2 - OW.repairLength (1 / 2) p.2)) x := by
    have H : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => 2 - OW.repairLength (1 / 2) p.2) x := by
      unfold OW.repairLength
      fun_prop
    exact H.sqrt (ne_of_gt hr)
  fin_cases j <;> fin_cases i <;>
    dsimp [frozenUnitDirection, Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go,
      commonVector, sharedVector,
      rampVector, postXVector, postYVector, contrast] <;> fun_prop

def frozenOriginalNoiseDomain (β : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ frozenNoiseBaseDomain ∧
    NoisePrecisionsPositive
      ((List.finRange 12).map (fun j => (p.1 * frozenUnitMass j, frozenUnitDirection β p.2 j)))
      normalizedNoiseQuadratic}

theorem frozenOriginalNoiseDomain_isOpen (β : ℝ) : IsOpen (frozenOriginalNoiseDomain β) := by
  apply noisePrecisionsPositive_isOpen
    (List.finRange 12) (fun j p => p.1 * frozenUnitMass j)
    (fun j p => frozenUnitDirection β p.2 j) (fun _ => normalizedNoiseQuadratic)
    frozenNoiseBaseDomain frozenNoiseBaseDomain_isOpen
  · intro j _
    fun_prop
  · intro j _ i p hp
    exact (frozenUnitDirection_contDiffAt β hp j i).contDiffWithinAt
  · intro i j
    exact contDiffOn_const

private theorem noisePrecisionsPositive_zeroMass {ι : Type} (l : List ι)
    (v : ι → Vec3) (Q : QuadraticTerminal) :
    NoisePrecisionsPositive (l.map (fun j => (0, v j))) Q := by
  induction l with
  | nil => simp [NoisePrecisionsPositive, riccatiPrecisions]
  | cons j l ih =>
    apply (noisePrecisionsPositive_cons _ _ _).mpr
    exact ⟨ih, by simp [QuadraticTerminal.precision]⟩

theorem frozenOriginalNoiseDomain_contains_rectangle (β : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      Icc (-δ) δ ×ˢ Icc (-(1 / 2) : ℝ) (1 / 2) ⊆ frozenOriginalNoiseDomain β := by
  have hzero : ({0} : Set ℝ) ×ˢ Icc (-(1 / 2) : ℝ) (1 / 2) ⊆ frozenOriginalNoiseDomain β := by
    rintro ⟨t, k⟩ ⟨ht, hk⟩
    have ht0 : t = 0 := ht
    subst t
    refine ⟨by change |k| < 3 / 5; rw [abs_lt]; constructor <;> linarith [hk.1, hk.2], ?_⟩
    simpa only [zero_mul] using noisePrecisionsPositive_zeroMass (List.finRange 12)
      (frozenUnitDirection β k) normalizedNoiseQuadratic
  obtain ⟨U, V, hU, _, h0, hK, hUV⟩ := generalized_tube_lemma isCompact_singleton
    isCompact_Icc (frozenOriginalNoiseDomain_isOpen β) hzero
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp
    (hU.mem_nhds (h0 (show (0 : ℝ) ∈ ({0} : Set ℝ) from rfl)))
  refine ⟨ε / 2, by positivity, ?_⟩
  rintro ⟨t, k⟩ ⟨ht, hk⟩
  apply hUV
  refine ⟨hεU ?_, hK hk⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero]
  have H := abs_le.mpr ht
  linarith

def frozenNormalizedNoise (β : ℝ) (j : Fin 12) (i : Fin 3) (p : ℝ × ℝ) : ℝ :=
  labelledNoisePart (fun j => p.1 * frozenUnitMass j)
    (frozenUnitDirection β p.2) (List.finRange 12) normalizedNoiseQuadratic (Pi.single j 1) i

set_option maxHeartbeats 1000000 in
theorem frozenNormalizedNoise_contDiffOn (β : ℝ) (j : Fin 12) (i : Fin 3) :
    ContDiffOn ℝ ∞ (frozenNormalizedNoise β j i) (frozenOriginalNoiseDomain β) := by
  intro p hp
  have H := labelledNoisePart_contDiffAt (List.finRange 12)
    (fun j (p : ℝ × ℝ) => p.1 * frozenUnitMass j)
    (fun j (p : ℝ × ℝ) => frozenUnitDirection β p.2 j)
    (fun _ => normalizedNoiseQuadratic) (p := p)
    (fun _ _ => by fun_prop)
    (fun j _ i => frozenUnitDirection_contDiffAt β hp.1 j i)
    (fun _ _ => contDiffAt_const) hp.2 (Pi.single j 1)
  exact (H i).contDiffWithinAt

theorem frozenNormalizedNoise_uniform_control (β : ℝ) :
    ∃ M δ : ℝ, 0 < M ∧ 0 < δ ∧
      ∀ j : Fin 12, ∀ i : Fin 3, ∀ t k : ℝ, |t| ≤ δ → |k| ≤ 1 / 2 →
        |frozenNormalizedNoise β j i (t, k)| ≤ M ∧
        |verticalDerivative (frozenNormalizedNoise β j i) (t, k)| ≤ M ∧
        |verticalDerivative (verticalDerivative (frozenNormalizedNoise β j i)) (t, k)| ≤ M ∧
        HasDerivAt (fun k => frozenNormalizedNoise β j i (t, k))
          (verticalDerivative (frozenNormalizedNoise β j i) (t, k)) k ∧
        HasDerivAt (fun k => verticalDerivative (frozenNormalizedNoise β j i) (t, k))
          (verticalDerivative (verticalDerivative (frozenNormalizedNoise β j i)) (t, k)) k := by
  obtain ⟨δ, hδ, hK⟩ := frozenOriginalNoiseDomain_contains_rectangle β
  choose S hS hbound using fun ji : Fin 12 × Fin 3 =>
    smoothOn_uniform_vertical_bounds (frozenOriginalNoiseDomain_isOpen β)
      (frozenNormalizedNoise_contDiffOn β ji.1 ji.2) δ hK
  let M := 1 + ∑ ji : Fin 12 × Fin 3, S ji
  have hsum : 0 ≤ ∑ ji : Fin 12 × Fin 3, S ji := Finset.sum_nonneg (fun ji _ => (hS ji).le)
  have hM : 0 < M := by dsimp only [M]; linarith
  refine ⟨M, δ, hM, hδ, ?_⟩
  intro j i t k ht hk
  have hx := hK (show (t, k) ∈ Icc (-δ) δ ×ˢ Icc (-(1 / 2) : ℝ) (1 / 2) from
    ⟨abs_le.mp ht, abs_le.mp hk⟩)
  have hSM : S (j, i) ≤ M := by
    have H := Finset.single_le_sum (f := S) (fun ji _ => (hS ji).le) (Finset.mem_univ (j, i))
    dsimp only [M]
    linarith
  have H := hbound (j, i) t (abs_le.mp ht) k (abs_le.mp hk)
  have hF := frozenNormalizedNoise_contDiffOn β j i
  have hU := frozenOriginalNoiseDomain_isOpen β
  have hF₁ : ContDiffOn ℝ ∞ (verticalDerivative (frozenNormalizedNoise β j i)) (frozenOriginalNoiseDomain β) :=
    (hF.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  exact ⟨H.1.trans hSM, H.2.1.trans hSM, H.2.2.trans hSM,
    verticalDerivative_hasDerivAt_on hU hF t k hx,
    verticalDerivative_hasDerivAt_on hU hF₁ t k hx⟩

def frozenOriginalAffine (β a u χ h z : ℝ) (i : Fin 3) : Fin 13 → ℝ → ℝ :=
  Fin.cons (fun _ => frozenGaussianMean β a u χ h z)
    (fun j k => Real.sqrt h * frozenNormalizedNoise β j i (a * χ * h, k))

def frozenOriginalAffineFirst (β a χ h : ℝ) (i : Fin 3) : Fin 13 → ℝ → ℝ :=
  Fin.cons (fun _ => 0)
    (fun j k => Real.sqrt h * verticalDerivative (frozenNormalizedNoise β j i) (a * χ * h, k))

def frozenOriginalAffineSecond (β a χ h : ℝ) (i : Fin 3) : Fin 13 → ℝ → ℝ :=
  Fin.cons (fun _ => 0)
    (fun j k => Real.sqrt h *
      verticalDerivative (verticalDerivative (frozenNormalizedNoise β j i)) (a * χ * h, k))

theorem frozenOriginalAffine_uniform_control (β B : ℝ) (hB : 0 < B) :
    ∃ M h₀ : ℝ, 0 < M ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ a u χ h z : ℝ, a ∈ Ioc (0 : ℝ) 1 → |u| ≤ B → |χ| ≤ B → 0 ≤ h → h ≤ h₀ →
      ∀ i : Fin 3,
        VectorAffineRegularOn (frozenOriginalAffine β a u χ h z i)
          (frozenOriginalAffineFirst β a χ h i) (frozenOriginalAffineSecond β a χ h i)
          (Ioo (-(1 / 2) : ℝ) (1 / 2)) ∧
        VectorAffineScaleBound (frozenOriginalAffine β a u χ h z i)
          (frozenOriginalAffineFirst β a χ h i) (frozenOriginalAffineSecond β a χ h i)
          (Ioo (-(1 / 2) : ℝ) (1 / 2)) z M (Real.sqrt h) := by
  obtain ⟨S, δ, hS, hδ, HS⟩ := frozenNormalizedNoise_uniform_control β
  obtain ⟨T, η, hT, hη, hη₁, HT⟩ := frozenGaussianParameter_uniform_control β B hB
  let M := S + T
  let ζ := min η (δ / (B + 1))
  refine ⟨M, ζ, add_pos hS hT, lt_min hη (by positivity),
    (min_le_left _ _).trans hη₁, ?_⟩
  intro a u χ h z ha hu hχ hh hhζ i
  have hhη : h ≤ η := hhζ.trans (min_le_left _ _)
  have ht : |a * χ * h| ≤ δ := by
    have hha : |a| ≤ 1 := by rw [abs_of_pos ha.1]; exact ha.2
    have hscale : |a * χ * h| ≤ B * h := by
      rw [abs_mul, abs_mul, abs_of_nonneg hh]
      calc
        _ ≤ 1 * B * h := by gcongr
        _ = B * h := by ring
    have H := (le_div_iff₀ (by positivity : 0 < B + 1)).mp
      (hhζ.trans (min_le_right _ _))
    exact hscale.trans (by nlinarith)
  have hbound (j : Fin 12) (k : ℝ) (hk : k ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :=
    HS j i (a * χ * h) k ht (abs_le.mpr ⟨hk.1.le, hk.2.le⟩)
  have hSM : S ≤ M := by dsimp only [M]; linarith
  have hTM : T ≤ M := by dsimp only [M]; linarith
  have Hmean : |frozenGaussianMean β a u χ h z - z| ≤ M * Real.sqrt h :=
    (HT a u χ h z ha hu hχ hh hhη i 0 (by norm_num)).2.1.trans
      (mul_le_mul_of_nonneg_right hTM (Real.sqrt_nonneg h))
  constructor
  · intro k hk j
    refine Fin.cases ?_ (fun j => ?_) j
    · exact ⟨hasDerivAt_const k _, hasDerivAt_const k _⟩
    · exact ⟨(hbound j k hk).2.2.2.1.const_mul (Real.sqrt h),
        (hbound j k hk).2.2.2.2.const_mul (Real.sqrt h)⟩
  · intro k hk j
    refine Fin.cases ?_ (fun j => ?_) j
    · change |frozenGaussianMean β a u χ h z - z| ≤ _ ∧ |(0 : ℝ)| ≤ _ ∧ |(0 : ℝ)| ≤ _
      refine ⟨Hmean, ?_, ?_⟩ <;> simpa only [abs_zero] using
        (mul_nonneg (add_nonneg hS.le hT.le) (Real.sqrt_nonneg h))
    · have H := hbound j k hk
      have hb {x : ℝ} (hx : |x| ≤ S) : |Real.sqrt h * x| ≤ M * Real.sqrt h := by
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg h)]
        calc
          _ ≤ Real.sqrt h * M := mul_le_mul_of_nonneg_left (hx.trans hSM) (Real.sqrt_nonneg h)
          _ = _ := mul_comm _ _
      change |Real.sqrt h * frozenNormalizedNoise β j i (a * χ * h, k) - 0| ≤ _ ∧
        |Real.sqrt h * verticalDerivative (frozenNormalizedNoise β j i) (a * χ * h, k)| ≤ _ ∧
        |Real.sqrt h * verticalDerivative (verticalDerivative (frozenNormalizedNoise β j i)) (a * χ * h, k)| ≤ _
      exact ⟨by simpa only [sub_zero] using hb H.1, hb H.2.1, hb H.2.2.1⟩

theorem quadraticNoiseCoefficients_succ (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (x : Vec3) (i : Fin 3) (j : Fin l.length) :
    quadraticNoiseCoefficients l Q x i j.succ = quadraticNoisePart l Q (Pi.single j 1) i := by
  simp only [quadraticNoiseCoefficients, Fin.cons_succ]
  rw [quadraticNoisePath_eq_mean_add_noise, quadraticNoisePath_zero]
  simp only [Pi.add_apply, add_sub_cancel_left]

theorem frozen_labelledNoisePart_scaled (β a c u χ h z k : ℝ) (hh : 0 ≤ h)
    (j : Fin 12) (i : Fin 3) :
    labelledNoisePart (fun j => a * frozenUnitMass j)
      (fun j => Real.sqrt h • frozenUnitDirection β k j) (List.finRange 12)
      (separableTaylorQuadratic c u χ z) (Pi.single j 1) i =
      Real.sqrt h * frozenNormalizedNoise β j i (a * χ * h, k) := by
  have H : ∀ i j, (separableTaylorQuadratic c u χ z).hessian i j =
      χ * normalizedNoiseQuadratic.hessian i j := by
    intro i j
    by_cases hij : i = j <;> simp [separableTaylorQuadratic, normalizedNoiseQuadratic, hij]
  have HE := labelledNoisePart_scaled frozenUnitMass (frozenUnitDirection β k)
    (List.finRange 12) (a := a) (c := Real.sqrt h) H (Pi.single j 1)
  rw [Real.sq_sqrt hh] at HE
  exact congrFun HE i

def labelledNoiseLinearMap {ι : Type} (m : ι → ℝ) (v : ι → Vec3)
    (l : List ι) (Q : QuadraticTerminal) : (ι → ℝ) →ₗ[ℝ] Vec3 where
  toFun := labelledNoisePart m v l Q
  map_add' g w := by
    induction l with
    | nil => simp only [labelledNoisePart, zero_add]
    | cons j l ih =>
      simp only [labelledNoisePart, Pi.add_apply, mul_add, add_smul, ih]
      abel
  map_smul' c g := by
    induction l with
    | nil => simp only [labelledNoisePart, smul_zero]
    | cons j l ih =>
      simp only [labelledNoisePart, Pi.smul_apply, smul_eq_mul, smul_add, smul_smul, ih, RingHom.id_apply]
      congr 1
      congr 1
      ring

theorem labelledNoisePart_sum {n : ℕ} (m : Fin n → ℝ) (v : Fin n → Vec3)
    (l : List (Fin n)) (Q : QuadraticTerminal) (g : Fin n → ℝ) :
    labelledNoisePart m v l Q g =
      ∑ j : Fin n, g j • labelledNoisePart m v l Q (Pi.single j 1) := by
  have hg : g = ∑ j : Fin n, g j • Pi.single j (1 : ℝ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have H := congrArg (labelledNoiseLinearMap m v l Q) hg
  simpa only [map_sum, map_smul, labelledNoiseLinearMap, LinearMap.coe_mk, AddHom.coe_mk] using H

theorem labelledQuadraticPath_eq_mean_add_noise {ι : Type} (m : ι → ℝ) (v : ι → Vec3)
    (l : List ι) (Q : QuadraticTerminal) (x : Vec3) (g : ι → ℝ) :
    labelledQuadraticPath m v l Q x g =
      gaussianPathMean (l.map (fun j => (m j, v j))) Q x + labelledNoisePart m v l Q g := by
  rw [labelledQuadraticPath_eq_original, quadraticNoisePath_eq_mean_add_noise,
    ← labelledNoisePart_eq_original]

theorem frozenOriginalAffine_represents (β a c u χ h z k : ℝ) (hh : 0 ≤ h)
    (hk : |k| ≤ 1 / 2)
    (hQ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z))
    (g : Fin 12 → ℝ) (i : Fin 3) :
    labelledQuadraticPath (fun j => a * frozenUnitMass j)
      (fun j => Real.sqrt h • frozenUnitDirection β k j) (List.finRange 12)
      (separableTaylorQuadratic c u χ z) (fun _ => z) g i =
      gaussianVectorAffine (frozenOriginalAffine β a u χ h z i) k g := by
  rw [labelledQuadraticPath_eq_mean_add_noise,
    ← frozenSchedule_eq_labelled β a h k hh,
    labelledNoisePart_sum]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    frozen_labelledNoisePart_scaled β a c u χ h z k hh,
    frozenSchedule_pathMean β a h k c u χ z hh hk hQ i]
  unfold gaussianVectorAffine frozenOriginalAffine frozenGaussianMean
  simp only [Fin.cons_zero, Fin.cons_succ]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

end SKBarriers2.Corner
