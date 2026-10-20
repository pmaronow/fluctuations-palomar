module

public import SKBarriers2.Corner.FrozenCoef5

@[expose] public section

noncomputable section
open scoped BigOperators Matrix ContDiff Topology NNReal
open Set MeasureTheory ProbabilityTheory Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

instance quadraticGaussian_isGaussian (D L : ℝ) : IsGaussian (quadraticGaussian D L) := by
  unfold quadraticGaussian
  infer_instance

private theorem hasExpGrowth_affine {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℝ} (hf : HasExpGrowth f) (c : F) (L : E →L[ℝ] F) :
    HasExpGrowth (fun x => f (c + L x)) := by
  obtain ⟨C, M, hC, hM, hb⟩ := hf
  refine ⟨C * Real.exp (M * ‖c‖), M * ‖L‖, by positivity, by positivity, ?_⟩
  intro x
  calc
    _ ≤ C * Real.exp (M * ‖c + L x‖) := hb _
    _ ≤ C * Real.exp (M * (‖c‖ + ‖L‖ * ‖x‖)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
          (add_le_add (le_refl ‖c‖) (L.le_opNorm x))) hM)) hC
    _ = _ := by rw [mul_add, ← mul_assoc M ‖L‖ ‖x‖, Real.exp_add]; ring1

def quadraticNoiseLinear (Q : QuadraticTerminal) (m : ℝ) (v : Vec3) :
    (Vec3 × ℝ) →ₗ[ℝ] Vec3 where
  toFun p := p.1 + (m / Q.precision m v *
    (∑ i, p.1 i * Q.hessianDirection v i) + Real.sqrt ((Q.precision m v)⁻¹) * p.2) • v
  map_add' p q := by
    ext i
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Fin.sum_univ_succ]
    ring1
  map_smul' c p := by
    ext i
    change c * p.1 i + (m / Q.precision m v *
      (∑ j, c * p.1 j * Q.hessianDirection v j) +
      Real.sqrt ((Q.precision m v)⁻¹) * (c * p.2)) * v i =
      c * (p.1 i + (m / Q.precision m v * (∑ j, p.1 j * Q.hessianDirection v j) +
        Real.sqrt ((Q.precision m v)⁻¹) * p.2) * v i)
    simp only [Fin.sum_univ_succ]
    ring1

def quadraticNoiseCLM (Q : QuadraticTerminal) (m : ℝ) (v : Vec3) :
    (Vec3 × ℝ) →L[ℝ] Vec3 := (quadraticNoiseLinear Q m v).toContinuousLinearMap

def quadraticNoiseConstant (Q : QuadraticTerminal) (m : ℝ) (v : Vec3) : Vec3 :=
  (m * Q.linearDirection v / Q.precision m v) • v

theorem quadraticNoise_affine (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3) (g : ℝ) :
    quadraticNoiseConstant Q m v + quadraticNoiseCLM Q m v (x, g) =
      x + (m * Q.slope v x / Q.precision m v + Real.sqrt ((Q.precision m v)⁻¹) * g) • v := by
  ext i
  change (m * Q.linearDirection v / Q.precision m v) * v i +
    (quadraticNoiseLinear Q m v (x, g)) i = _
  simp only [quadraticNoiseLinear, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, QuadraticTerminal.slope]
  ring1

theorem quadraticAverage_eq_standard_of_kernel (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3)
    (hP : 0 < Q.precision m v) {K : Vec3 → ℝ} (hK : Continuous K) :
    quadraticAverage Q m v K x =
      ∫ g : ℝ, K (quadraticNoiseConstant Q m v + quadraticNoiseCLM Q m v (x, g))
        ∂gaussianReal 0 1 := by
  have H := gaussian_integral_eq_standard_affine (fun t : ℝ => K (x + t • v))
    (by fun_prop) (m * Q.slope v x / Q.precision m v) (Real.sqrt ((Q.precision m v)⁻¹))
  simp only [Real.sq_sqrt (inv_nonneg.mpr hP.le)] at H
  simpa only [quadraticAverage, quadraticGaussian, quadraticNoise_affine] using H

theorem quadraticAverage_continuous_expGrowth (Q : QuadraticTerminal) (m : ℝ) (v : Vec3)
    (hP : 0 < Q.precision m v) {K : Vec3 → ℝ} (hK : Continuous K) (hg : HasExpGrowth K) :
    Continuous (quadraticAverage Q m v K) ∧ HasExpGrowth (quadraticAverage Q m v K) := by
  let F : Vec3 × ℝ → ℝ := fun p => K (quadraticNoiseConstant Q m v + quadraticNoiseCLM Q m v p)
  have hF : Continuous F := by dsimp only [F]; fun_prop
  have hFg : HasExpGrowth F := hasExpGrowth_affine hg _ _
  have he : quadraticAverage Q m v K = fun x => ∫ g, F (x, g) ∂gaussianReal 0 1 :=
    funext (fun x => quadraticAverage_eq_standard_of_kernel Q m v x hP hK)
  rw [he]
  exact ⟨hFg.continuous_gaussian_integral hF, hFg.gaussian_integral⟩

theorem quadraticFirst_continuous_expGrowth (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible l Q) {K : Vec3 → ℝ} (hK : Continuous K) (hg : HasExpGrowth K) :
    Continuous (quadraticFirst l Q K) ∧ HasExpGrowth (quadraticFirst l Q K) := by
  induction l with
  | nil => exact ⟨hK, hg⟩
  | cons u l ih =>
    have HI := ih hl.1
    exact quadraticAverage_continuous_expGrowth _ u.1 u.2 hl.2.2 HI.1 HI.2

theorem quadraticFirst_line_integrable (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible l Q) {K : Vec3 → ℝ} (hK : Continuous K) (hg : HasExpGrowth K)
    (x v : Vec3) (m : ℝ) (σ : ℝ≥0) :
    Integrable (fun t : ℝ => quadraticFirst l Q K (x + t • v)) (gaussianReal m σ) := by
  have H := quadraticFirst_continuous_expGrowth l Q hl hK hg
  have HG := hasExpGrowth_affine H.2 x (ContinuousLinearMap.toSpanSingleton ℝ v)
  exact HG.integrable_gaussianMeasure (H.1.comp
    (continuous_const.add (ContinuousLinearMap.toSpanSingleton ℝ v).continuous))

private theorem hasExpGrowth_sub {E : Type} [NormedAddCommGroup E]
    {f g : E → ℝ} (hf : HasExpGrowth f) (hg : HasExpGrowth g) :
    HasExpGrowth (fun x => f x - g x) := by
  simpa only [neg_one_mul, sub_eq_add_neg] using hf.add ((HasExpGrowth.const (-1 : ℝ)).mul hg)

theorem quadraticFirst_line_memLp_two (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible l Q) {K : Vec3 → ℝ} (hK : Continuous K) (hg : HasExpGrowth K)
    (x v : Vec3) (m : ℝ) (σ : ℝ≥0) :
    MemLp (fun t : ℝ => quadraticFirst l Q K (x + t • v)) 2 (gaussianReal m σ) := by
  have H := quadraticFirst_continuous_expGrowth l Q hl hK hg
  have HG := hasExpGrowth_affine H.2 x (ContinuousLinearMap.toSpanSingleton ℝ v)
  have HC : Continuous (fun t : ℝ => quadraticFirst l Q K (x + t • v)) :=
    H.1.comp (continuous_const.add (ContinuousLinearMap.toSpanSingleton ℝ v).continuous)
  exact (memLp_two_iff_integrable_sq HC.aestronglyMeasurable).mpr
    ((HG.pow 2).integrable_gaussianMeasure (HC.pow 2))

theorem quadraticAverage_const_mul (Q : QuadraticTerminal) (m : ℝ) (v : Vec3)
    (K : Vec3 → ℝ) (c : ℝ) (x : Vec3) :
    quadraticAverage Q m v (fun y => c * K y) x = c * quadraticAverage Q m v K x := by
  exact integral_const_mul c _

theorem quadraticFirst_const_mul (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (K : Vec3 → ℝ) (c : ℝ) :
    quadraticFirst l Q (fun y => c * K y) = fun x => c * quadraticFirst l Q K x := by
  induction l with
  | nil => rfl
  | cons u l ih =>
    funext x
    rw [quadraticFirst, ih, quadraticAverage_const_mul]
    rfl

theorem quadraticAverage_add (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3)
    {F G : Vec3 → ℝ} (hF : Continuous F) (hgF : HasExpGrowth F)
    (hG : Continuous G) (hgG : HasExpGrowth G) :
    quadraticAverage Q m v (fun y => F y + G y) x =
      quadraticAverage Q m v F x + quadraticAverage Q m v G x := by
  have HI (K : Vec3 → ℝ) (hK : Continuous K) (hg : HasExpGrowth K) :
      Integrable (fun t : ℝ => K (x + t • v))
        (quadraticGaussian (Q.precision m v) (m * Q.slope v x)) := by
    exact (hasExpGrowth_affine hg x (ContinuousLinearMap.toSpanSingleton ℝ v)).integrable_gaussianMeasure
      (by fun_prop)
  exact integral_add (HI F hF hgF) (HI G hG hgG)

theorem quadraticSecond_continuous_expGrowth (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible l Q) {K : Vec3 → ℝ} (hK : Continuous K) (hg : HasExpGrowth K) :
    Continuous (quadraticSecond l Q K) ∧ HasExpGrowth (quadraticSecond l Q K) := by
  induction l with
  | nil => exact ⟨continuous_const, HasExpGrowth.const 0⟩
  | cons u l ih =>
    have HS := ih hl.1
    have HF := quadraticFirst_continuous_expGrowth l Q hl.1 hK hg
    have HA := quadraticAverage_continuous_expGrowth (riccatiRecursion l Q) u.1 u.2 hl.2.2
      (HS.1.add (continuous_const.mul (HF.1.pow 2)))
      (HS.2.add ((HasExpGrowth.const u.1).mul (HF.2.pow 2)))
    have HB := quadraticFirst_continuous_expGrowth (u :: l) Q hl hK hg
    exact ⟨HA.1.sub (continuous_const.mul (HB.1.pow 2)),
      hasExpGrowth_sub HA.2 ((HasExpGrowth.const u.1).mul (HB.2.pow 2))⟩

theorem quadraticSecond_constant_mass (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (K : Vec3 → ℝ) (m : ℝ) (hm : ∀ u ∈ l, u.1 = m) :
    quadraticSecond l Q K = fun x =>
      m * (quadraticFirst l Q (fun y => K y ^ 2) x - quadraticFirst l Q K x ^ 2) := by
  induction l with
  | nil => funext x; simp only [quadraticSecond, quadraticFirst, sub_self, mul_zero]
  | cons u l ih =>
    have hu : u.1 = m := hm u (List.mem_cons_self ..)
    have ht : ∀ v ∈ l, v.1 = m := fun v hv => hm v (List.mem_cons_of_mem u hv)
    funext x
    rw [quadraticSecond, ih ht, hu]
    have he : (fun y => m * (quadraticFirst l Q (fun z => K z ^ 2) y - quadraticFirst l Q K y ^ 2) +
        m * quadraticFirst l Q K y ^ 2) = fun y => m * quadraticFirst l Q (fun z => K z ^ 2) y := by
      funext y
      ring1
    rw [he]
    dsimp only
    rw [quadraticAverage_const_mul]
    simp only [quadraticFirst, hu]
    ring1

theorem riccatiRecursion_append (l t : List (ℝ × Vec3)) (Q : QuadraticTerminal) :
    riccatiRecursion (l ++ t) Q = riccatiRecursion l (riccatiRecursion t Q) := by
  induction l with
  | nil => rfl
  | cons u l ih => simp only [List.cons_append, riccatiRecursion, ih]

theorem quadraticFirst_append (l t : List (ℝ × Vec3)) (Q : QuadraticTerminal) (K : Vec3 → ℝ) :
    quadraticFirst (l ++ t) Q K = quadraticFirst l (riccatiRecursion t Q) (quadraticFirst t Q K) := by
  induction l with
  | nil => rfl
  | cons u l ih => simp only [List.cons_append, quadraticFirst, riccatiRecursion_append, ih]

theorem quadraticFirst_add (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible l Q) {F G : Vec3 → ℝ}
    (hF : Continuous F) (hgF : HasExpGrowth F) (hG : Continuous G) (hgG : HasExpGrowth G) :
    quadraticFirst l Q (fun y => F y + G y) =
      fun x => quadraticFirst l Q F x + quadraticFirst l Q G x := by
  induction l with
  | nil => rfl
  | cons u l ih =>
    have HF := quadraticFirst_continuous_expGrowth l Q hl.1 hF hgF
    have HG := quadraticFirst_continuous_expGrowth l Q hl.1 hG hgG
    funext x
    rw [quadraticFirst, ih hl.1]
    exact quadraticAverage_add _ u.1 u.2 x HF.1 HF.2 HG.1 HG.2

theorem quadraticFirst_finsetSum {ι : Type} (s : Finset ι)
    (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (hl : RiccatiAdmissible l Q)
    (F : ι → Vec3 → ℝ) (hF : ∀ i ∈ s, Continuous (F i)) (hg : ∀ i ∈ s, HasExpGrowth (F i)) :
    quadraticFirst l Q (fun y => ∑ i ∈ s, F i y) =
      fun x => ∑ i ∈ s, quadraticFirst l Q (F i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, zero_mul] using
      quadraticFirst_const_mul l Q (fun _ => (0 : ℝ)) 0
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [quadraticFirst_add l Q hl (hF i (Finset.mem_insert_self i s))
      (hg i (Finset.mem_insert_self i s))
      (continuous_finsetSum _ (fun j hj => hF j (Finset.mem_insert_of_mem hj)))
      (HasExpGrowth.finsetSum s F (fun j hj => hg j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
        (fun j hj => hg j (Finset.mem_insert_of_mem hj))]

theorem scalarTerminalResidual_hasExpGrowth (β : ℝ) (α : ℝ → ℝ) (s h z : ℝ)
    (hφ : BoundedDerivs (Phi β α (s + 4 * h))) :
    HasExpGrowth (scalarTerminalResidual β α s h z) := by
  have hid : HasExpGrowth (fun y : ℝ => y) :=
    HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)
  have hshift : HasExpGrowth (fun y : ℝ => y - z) := hid.sub_real (HasExpGrowth.const z)
  exact hφ.hasExpGrowth.sub_real (((HasExpGrowth.const (Phi β α (s + 4 * h) z)).add
    ((HasExpGrowth.const (jet β α 1 (s + 4 * h) z)).mul hshift)).add
      ((HasExpGrowth.const (jet β α 2 (s + 4 * h) z / 2)).mul (hshift.pow 2)))

theorem terminalResidual_hasExpGrowth (β : ℝ) (α : ℝ → ℝ) (s h z : ℝ)
    (hφ : BoundedDerivs (Phi β α (s + 4 * h))) :
    HasExpGrowth (terminalResidual β α s h z) := by
  rw [terminalResidual_eq_scalar_sum]
  apply HasExpGrowth.finsetSum
  intro i _
  let L : Vec3 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have H := (scalarTerminalResidual_hasExpGrowth β α s h z hφ).compCLM L
  simpa only [Function.comp_def, L, ContinuousLinearMap.proj_apply] using H

theorem terminalCubicResidual_continuous_expGrowth (β : ℝ) (α : ℝ → ℝ) (s h z : ℝ) :
    Continuous (terminalCubicResidual β α s h z) ∧ HasExpGrowth (terminalCubicResidual β α s h z) := by
  refine ⟨by unfold terminalCubicResidual; fun_prop, ?_⟩
  unfold terminalCubicResidual
  apply HasExpGrowth.finsetSum
  intro i _
  have hi : HasExpGrowth (fun x : Vec3 => x i - z) := by
    let L : Vec3 →L[ℝ] ℝ := ContinuousLinearMap.proj i
    have H := hasExpGrowth_sub (HasExpGrowth.linear L) (HasExpGrowth.const z)
    simpa only [L, ContinuousLinearMap.proj_apply] using H
  have H := ((HasExpGrowth.const (jet β α 3 (s + 4 * h) z)).mul (hi.pow 3)).mul
    (HasExpGrowth.const (6 : ℝ)⁻¹)
  simpa only [div_eq_mul_inv] using H

theorem scalarData_quadraticFirst_memLp_two {β : ℝ} (D : ScalarData β)
    {s h : ℝ} (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) (z : ℝ)
    (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (hl : RiccatiAdmissible l Q)
    (x v : Vec3) (m : ℝ) (σ : ℝ≥0) :
    MemLp (fun t : ℝ => quadraticFirst l Q (terminalResidual β (cdf (D.μ : Measure ℝ)) s h z)
      (x + t • v)) 2 (gaussianReal m σ) ∧
    MemLp (fun t : ℝ => quadraticFirst l Q (terminalCubicResidual β (cdf (D.μ : Measure ℝ)) s h z)
      (x + t • v)) 2 (gaussianReal m σ) := by
  have hφ := scalarData_phi_regular D ht
  have hK := terminalCubicResidual_continuous_expGrowth β (cdf (D.μ : Measure ℝ)) s h z
  exact ⟨quadraticFirst_line_memLp_two l Q hl (terminalResidual_continuous _ _ s h z hφ)
      (terminalResidual_hasExpGrowth _ _ s h z hφ) x v m σ,
    quadraticFirst_line_memLp_two l Q hl hK.1 hK.2 x v m σ⟩

theorem quadraticSecond_two_outer_constant_mass (u v : ℝ × Vec3)
    (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) {K : Vec3 → ℝ}
    (hQ : RiccatiAdmissible (u :: v :: l) Q) (hK : Continuous K) (hg : HasExpGrowth K)
    (m : ℝ) (hm : ∀ w ∈ l, w.1 = m) (x : Vec3) :
    quadraticSecond (u :: v :: l) Q K x =
      m * quadraticFirst (u :: v :: l) Q (fun y => K y ^ 2) x +
      (v.1 - m) * quadraticAverage (riccatiRecursion (v :: l) Q) u.1 u.2
        (quadraticAverage (riccatiRecursion l Q) v.1 v.2 (fun y => quadraticFirst l Q K y ^ 2)) x +
      (u.1 - v.1) * quadraticAverage (riccatiRecursion (v :: l) Q) u.1 u.2
        (fun y => quadraticFirst (v :: l) Q K y ^ 2) x -
      u.1 * quadraticFirst (u :: v :: l) Q K x ^ 2 := by
  let R := riccatiRecursion l Q
  let S := riccatiRecursion (v :: l) Q
  let A := quadraticFirst l Q K
  let B := quadraticFirst (v :: l) Q K
  let P := quadraticFirst l Q (fun y => K y ^ 2)
  let T := quadraticFirst (v :: l) Q (fun y => K y ^ 2)
  have HA := quadraticFirst_continuous_expGrowth l Q hQ.1.1 hK hg
  have HB := quadraticFirst_continuous_expGrowth (v :: l) Q hQ.1 hK hg
  have HP := quadraticFirst_continuous_expGrowth l Q hQ.1.1 (hK.pow 2) (hg.pow 2)
  have HT := quadraticFirst_continuous_expGrowth (v :: l) Q hQ.1 (hK.pow 2) (hg.pow 2)
  have HV := quadraticAverage_continuous_expGrowth R v.1 v.2 hQ.1.2.2 (HA.1.pow 2) (HA.2.pow 2)
  have Hshared : quadraticSecond (v :: l) Q K = fun y =>
      m * T y + (v.1 - m) * quadraticAverage R v.1 v.2 (fun z => A z ^ 2) y - v.1 * B y ^ 2 := by
    funext y
    rw [quadraticSecond, quadraticSecond_constant_mass l Q K m hm]
    have he : (fun z => m * (P z - A z ^ 2) + v.1 * A z ^ 2) =
        fun z => m * P z + (v.1 - m) * A z ^ 2 := by
      funext z
      ring1
    change quadraticAverage R v.1 v.2 (fun z => m * (P z - A z ^ 2) + v.1 * A z ^ 2) y -
      v.1 * B y ^ 2 = _
    rw [he, quadraticAverage_add R v.1 v.2 y
      (F := fun z => m * P z) (G := fun z => (v.1 - m) * A z ^ 2)
      (continuous_const.mul HP.1) ((HasExpGrowth.const m).mul HP.2)
      (continuous_const.mul (HA.1.pow 2)) ((HasExpGrowth.const (v.1 - m)).mul (HA.2.pow 2)),
      quadraticAverage_const_mul, quadraticAverage_const_mul]
    rfl
  rw [quadraticSecond, Hshared]
  have he : (fun y => (m * T y + (v.1 - m) * quadraticAverage R v.1 v.2 (fun z => A z ^ 2) y -
        v.1 * B y ^ 2) + u.1 * B y ^ 2) = fun y =>
      (m * T y + (v.1 - m) * quadraticAverage R v.1 v.2 (fun z => A z ^ 2) y) +
        (u.1 - v.1) * B y ^ 2 := by
    funext y
    ring1
  change quadraticAverage S u.1 u.2
    (fun y => (m * T y + (v.1 - m) * quadraticAverage R v.1 v.2 (fun z => A z ^ 2) y -
      v.1 * B y ^ 2) + u.1 * B y ^ 2) x - u.1 * quadraticFirst (u :: v :: l) Q K x ^ 2 = _
  rw [he, quadraticAverage_add S u.1 u.2 x
    (F := fun y => m * T y + (v.1 - m) * quadraticAverage R v.1 v.2 (fun z => A z ^ 2) y)
    (G := fun y => (u.1 - v.1) * B y ^ 2)
    ((continuous_const.mul HT.1).add (continuous_const.mul HV.1))
    (((HasExpGrowth.const m).mul HT.2).add ((HasExpGrowth.const (v.1 - m)).mul HV.2))
    (continuous_const.mul (HB.1.pow 2)) ((HasExpGrowth.const (u.1 - v.1)).mul (HB.2.pow 2)),
    quadraticAverage_add S u.1 u.2 x
      (F := fun y => m * T y)
      (G := fun y => (v.1 - m) * quadraticAverage R v.1 v.2 (fun z => A z ^ 2) y)
      (continuous_const.mul HT.1) ((HasExpGrowth.const m).mul HT.2)
      (continuous_const.mul HV.1) ((HasExpGrowth.const (v.1 - m)).mul HV.2),
    quadraticAverage_const_mul, quadraticAverage_const_mul, quadraticAverage_const_mul]
  rfl

theorem frozenSchedule_second_nested_squares (β a h k : ℝ) (Q : QuadraticTerminal)
    {K : Vec3 → ℝ} (hQ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) Q)
    (hK : Continuous K) (hg : HasExpGrowth K) (x : Vec3) :
    quadraticSecond (frozenSchedule β a (1 / 2) h k) Q K x =
      a * quadraticFirst (frozenSchedule β a (1 / 2) h k) Q (fun y => K y ^ 2) x -
      a / 2 * quadraticFirst (frozenCommon β a (1 / 2) h k ++ frozenShared β a (1 / 2) h k)
        (riccatiRecursion (frozenInner β a (1 / 2) h k) Q)
        (fun y => quadraticFirst (frozenInner β a (1 / 2) h k) Q K y ^ 2) x -
      a / 6 * quadraticFirst (frozenCommon β a (1 / 2) h k)
        (riccatiRecursion (frozenShared β a (1 / 2) h k ++ frozenInner β a (1 / 2) h k) Q)
        (fun y => quadraticFirst (frozenShared β a (1 / 2) h k ++ frozenInner β a (1 / 2) h k) Q K y ^ 2) x -
      a / 3 * quadraticFirst (frozenSchedule β a (1 / 2) h k) Q K x ^ 2 := by
  have hm : ∀ w ∈ frozenInner β a (1 / 2) h k, w.1 = a := by
    intro w hw
    simp only [frozenInner, List.mem_append, List.mem_singleton, List.mem_map] at hw
    rcases hw with ((rfl | ⟨t, _, rfl⟩) | ⟨t, _, rfl⟩) | ⟨t, _, rfl⟩ <;> rfl
  have H := quadraticSecond_two_outer_constant_mass
    (a / 3, (β * Real.sqrt h) • commonVector (1 / 2) k)
    (a / 2, (β * Real.sqrt (h * (1 / 2))) • sharedVector (1 / 2) k)
    (frozenInner β a (1 / 2) h k) Q hQ hK hg a hm x
  change quadraticSecond (frozenSchedule β a (1 / 2) h k) Q K x = _ at H
  rw [H]
  simp only [frozenSchedule, frozenCommon, frozenShared, List.cons_append,
    List.nil_append, quadraticFirst,
    riccatiRecursion]
  ring1

theorem gaussianPathCovariance_symmetric (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (i j : Fin 3) : gaussianPathCovariance l Q i j = gaussianPathCovariance l Q j i := by
  induction l with
  | nil => rfl
  | cons u l ih =>
    simp only [gaussianPathCovariance, ih]
    ring1

def gaussianPathCross (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (w v : Vec3) : ℝ :=
  ∑ i, ∑ j, w i * gaussianPathCovariance l Q i j * v j

theorem gaussianPathVariance_linear_combination (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (w v : Vec3) (a b : ℝ) :
    gaussianPathVariance l Q (fun i => a * w i + b * v i) =
      a ^ 2 * gaussianPathVariance l Q w + 2 * a * b * gaussianPathCross l Q w v +
        b ^ 2 * gaussianPathVariance l Q v := by
  simp only [gaussianPathVariance, gaussianPathCross, Fin.sum_univ_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  rw [gaussianPathCovariance_symmetric l Q 1 0, gaussianPathCovariance_symmetric l Q 2 0,
    gaussianPathCovariance_symmetric l Q 2 1]
  ring1

def affineGaussianTest (c : ℝ) (w y : Vec3) : ℝ := c + ∑ i, w i * y i

private def dotCLM (w : Vec3) : Vec3 →L[ℝ] ℝ := ∑ i : Fin 3, w i • ContinuousLinearMap.proj i

private theorem dotCLM_apply (w x : Vec3) : dotCLM w x = ∑ i, w i * x i := by
  simp only [dotCLM, sum_apply, smul_apply,
    smul_eq_mul, ContinuousLinearMap.proj_apply]

theorem affineGaussianTest_continuous_expGrowth (c : ℝ) (w : Vec3) :
    Continuous (affineGaussianTest c w) ∧ HasExpGrowth (affineGaussianTest c w) := by
  refine ⟨by unfold affineGaussianTest; fun_prop, ?_⟩
  change HasExpGrowth (fun y : Vec3 => c + ∑ i, w i * y i)
  have H : HasExpGrowth (fun y : Vec3 => c + dotCLM w y) :=
    (HasExpGrowth.const c).add (HasExpGrowth.linear (dotCLM w))
  simpa only [dotCLM_apply] using H

theorem affineGaussianTest_linear_combination (a b c d : ℝ) (w v y : Vec3) :
    affineGaussianTest (a * c + b * d) (fun i => a * w i + b * v i) y =
      a * affineGaussianTest c w y + b * affineGaussianTest d v y := by
  simp only [affineGaussianTest, Fin.sum_univ_succ]
  ring1

theorem quadraticFirst_affine_sixth (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible l Q) (c : ℝ) (w x : Vec3) :
    let m := affineGaussianTest c w (gaussianPathMean l Q x)
    let V := gaussianPathVariance l Q w
    quadraticFirst l Q (fun y => affineGaussianTest c w y ^ 6) x =
      m ^ 6 + 15 * m ^ 4 * V + 45 * m ^ 2 * V ^ 2 + 15 * V ^ 3 := by
  dsimp only
  let φ : ℝ → ℝ := fun t => (c + t) ^ 6
  have hg : HasExpGrowth φ :=
    ((HasExpGrowth.const c).add (HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ))).pow 6
  have hi (m : ℝ) (V : ℝ≥0) : Integrable φ (gaussianReal m V) :=
    hg.integrable_gaussianMeasure (by fun_prop)
  change quadraticFirst l Q (fun y => φ (∑ i, w i * y i)) x = _
  rw [quadraticFirst_projection l Q hl φ (by fun_prop) hi w x]
  have he : φ = fun t => (t - (-c)) ^ 6 := by
    funext t
    dsimp only [φ]
    congr 1
    ring1
  rw [he, gaussian_integral_centered_sixth,
    Real.toNNReal_of_nonneg (gaussianPathVariance_nonneg l Q hl w)]
  simp only [NNReal.coe_mk]
  unfold affineGaussianTest
  ring1

private def cubicPolarizationPairs : Fin 6 → ℝ × ℝ :=
  ![(1, 1), (1, -1), (1, 2), (1, -2), (2, 1), (2, -1)]

private def cubicPolarizationWeights : Fin 6 → ℝ :=
  ![34 / 720, -34 / 720, -1 / 720, 1 / 720, -1 / 720, 1 / 720]

private theorem cubicPolarization_identity (x y : ℝ) :
    x ^ 3 * y ^ 3 = ∑ j : Fin 6, cubicPolarizationWeights j *
      ((cubicPolarizationPairs j).1 * x + (cubicPolarizationPairs j).2 * y) ^ 6 := by
  norm_num [cubicPolarizationWeights, cubicPolarizationPairs, Fin.sum_univ_succ]
  ring1

def cubicGaussianProduct (m n V W C : ℝ) : ℝ :=
  (m ^ 3 + 3 * m * V) * (n ^ 3 + 3 * n * W) +
    9 * (m ^ 2 + V) * (n ^ 2 + W) * C + 18 * m * n * C ^ 2 + 6 * C ^ 3

theorem quadraticFirst_cubic_pair (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible l Q) (c d : ℝ) (w v x : Vec3) :
    quadraticFirst l Q (fun y => affineGaussianTest c w y ^ 3 * affineGaussianTest d v y ^ 3) x =
      cubicGaussianProduct (affineGaussianTest c w (gaussianPathMean l Q x))
        (affineGaussianTest d v (gaussianPathMean l Q x))
        (gaussianPathVariance l Q w) (gaussianPathVariance l Q v) (gaussianPathCross l Q w v) := by
  let F (j : Fin 6) : Vec3 → ℝ := fun y => cubicPolarizationWeights j *
    affineGaussianTest ((cubicPolarizationPairs j).1 * c + (cubicPolarizationPairs j).2 * d)
      (fun i => (cubicPolarizationPairs j).1 * w i + (cubicPolarizationPairs j).2 * v i) y ^ 6
  have hF (j : Fin 6) : Continuous (F j) := by
    have H := (affineGaussianTest_continuous_expGrowth
      ((cubicPolarizationPairs j).1 * c + (cubicPolarizationPairs j).2 * d)
      (fun i => (cubicPolarizationPairs j).1 * w i + (cubicPolarizationPairs j).2 * v i)).1
    exact continuous_const.mul (H.pow 6)
  have hgF (j : Fin 6) : HasExpGrowth (F j) :=
    (HasExpGrowth.const (cubicPolarizationWeights j)).mul
      ((affineGaussianTest_continuous_expGrowth
        ((cubicPolarizationPairs j).1 * c + (cubicPolarizationPairs j).2 * d)
        (fun i => (cubicPolarizationPairs j).1 * w i + (cubicPolarizationPairs j).2 * v i)).2.pow 6)
  have he : (fun y => affineGaussianTest c w y ^ 3 * affineGaussianTest d v y ^ 3) =
      fun y => ∑ j : Fin 6, F j y := by
    funext y
    dsimp only [F]
    simp_rw [affineGaussianTest_linear_combination]
    exact cubicPolarization_identity _ _
  rw [he, quadraticFirst_finsetSum Finset.univ l Q hl F (fun j _ => hF j) (fun j _ => hgF j)]
  dsimp only [F]
  simp_rw [quadraticFirst_const_mul, quadraticFirst_affine_sixth l Q hl,
    affineGaussianTest_linear_combination, gaussianPathVariance_linear_combination]
  norm_num [cubicPolarizationWeights, cubicPolarizationPairs, Fin.sum_univ_succ]
  unfold cubicGaussianProduct
  ring1

theorem quadraticFirst_double_sum {ι κ : Type} [Fintype ι] [Fintype κ]
    (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (hl : RiccatiAdmissible l Q)
    (F : ι → κ → Vec3 → ℝ) (hF : ∀ i j, Continuous (F i j))
    (hg : ∀ i j, HasExpGrowth (F i j)) :
    quadraticFirst l Q (fun y => ∑ i, ∑ j, F i j y) =
      fun x => ∑ i, ∑ j, quadraticFirst l Q (F i j) x := by
  rw [quadraticFirst_finsetSum Finset.univ l Q hl (fun i y => ∑ j, F i j y)
    (fun i _ => continuous_finsetSum _ (fun j _ => hF i j))
    (fun i _ => HasExpGrowth.finsetSum _ (F i) (fun j _ => hg i j))]
  funext x
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (quadraticFirst_finsetSum Finset.univ l Q hl (F i)
    (fun j _ => hF i j) (fun j _ => hg i j)) x

private def cubicLinearShifts : Fin 3 → ℝ := ![0, 1, -1]

private def cubicLinearWeights (r : ℝ) : Fin 3 → ℝ := ![1 - r, r / 2, r / 2]

private theorem cubicLinear_identity (r x : ℝ) :
    x ^ 3 + 3 * r * x = ∑ i : Fin 3, cubicLinearWeights r i * (x + cubicLinearShifts i) ^ 3 := by
  norm_num [cubicLinearWeights, cubicLinearShifts, Fin.sum_univ_succ]
  ring1

def cubicLinearGaussianProduct (m n V W C r s : ℝ) : ℝ :=
  (m ^ 3 + 3 * m * (V + r)) * (n ^ 3 + 3 * n * (W + s)) +
    9 * (m ^ 2 + V + r) * (n ^ 2 + W + s) * C + 18 * m * n * C ^ 2 + 6 * C ^ 3

theorem quadraticFirst_cubic_linear_pair (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible l Q) (c d r s : ℝ) (w v x : Vec3) :
    quadraticFirst l Q (fun y =>
      (affineGaussianTest c w y ^ 3 + 3 * r * affineGaussianTest c w y) *
        (affineGaussianTest d v y ^ 3 + 3 * s * affineGaussianTest d v y)) x =
      cubicLinearGaussianProduct (affineGaussianTest c w (gaussianPathMean l Q x))
        (affineGaussianTest d v (gaussianPathMean l Q x))
        (gaussianPathVariance l Q w) (gaussianPathVariance l Q v) (gaussianPathCross l Q w v) r s := by
  let F (i j : Fin 3) : Vec3 → ℝ := fun y =>
    (cubicLinearWeights r i * cubicLinearWeights s j) *
      (affineGaussianTest (c + cubicLinearShifts i) w y ^ 3 *
        affineGaussianTest (d + cubicLinearShifts j) v y ^ 3)
  have hF (i j : Fin 3) : Continuous (F i j) := by
    have HA := (affineGaussianTest_continuous_expGrowth (c + cubicLinearShifts i) w).1
    have HB := (affineGaussianTest_continuous_expGrowth (d + cubicLinearShifts j) v).1
    exact continuous_const.mul ((HA.pow 3).mul (HB.pow 3))
  have hgF (i j : Fin 3) : HasExpGrowth (F i j) :=
    (HasExpGrowth.const _).mul
      (((affineGaussianTest_continuous_expGrowth (c + cubicLinearShifts i) w).2.pow 3).mul
        ((affineGaussianTest_continuous_expGrowth (d + cubicLinearShifts j) v).2.pow 3))
  have he : (fun y => (affineGaussianTest c w y ^ 3 + 3 * r * affineGaussianTest c w y) *
        (affineGaussianTest d v y ^ 3 + 3 * s * affineGaussianTest d v y)) =
      fun y => ∑ i : Fin 3, ∑ j : Fin 3, F i j y := by
    funext y
    have ha (c t : ℝ) (w : Vec3) : affineGaussianTest (c + t) w y = affineGaussianTest c w y + t := by
      unfold affineGaussianTest
      ring1
    dsimp only [F]
    simp_rw [ha]
    rw [cubicLinear_identity r, cubicLinear_identity s]
    simp only [Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    ring1
  rw [he, quadraticFirst_double_sum l Q hl F hF hgF]
  dsimp only [F]
  simp_rw [quadraticFirst_const_mul, quadraticFirst_cubic_pair l Q hl]
  have ha (c t : ℝ) (w : Vec3) :
      affineGaussianTest (c + t) w (gaussianPathMean l Q x) =
        affineGaussianTest c w (gaussianPathMean l Q x) + t := by
    unfold affineGaussianTest
    ring1
  simp_rw [ha]
  norm_num [cubicLinearWeights, cubicLinearShifts, Fin.sum_univ_succ]
  unfold cubicGaussianProduct cubicLinearGaussianProduct
  ring1

theorem affineGaussianTest_coordinate_center (z : ℝ) (i : Fin 3) (y : Vec3) :
    affineGaussianTest (-z) (Pi.single i 1) y = y i - z := by
  simp only [affineGaussianTest, Pi.single_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring1

theorem gaussianPathVariance_coordinate (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (i : Fin 3) :
    gaussianPathVariance l Q (Pi.single i 1) = gaussianPathCovariance l Q i i := by
  simp [gaussianPathVariance, Pi.single_apply]

theorem gaussianPathCross_coordinate (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (i j : Fin 3) :
    gaussianPathCross l Q (Pi.single i 1) (Pi.single j 1) = gaussianPathCovariance l Q i j := by
  simp [gaussianPathCross, Pi.single_apply]

theorem quadraticFirst_terminalCubicResidual_square (β : ℝ) (α : ℝ → ℝ) (s h z : ℝ)
    (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (hl : RiccatiAdmissible l Q) (x : Vec3) :
    quadraticFirst l Q (fun y => terminalCubicResidual β α s h z y ^ 2) x =
      (jet β α 3 (s + 4 * h) z / 6) ^ 2 *
        ∑ i : Fin 3, ∑ j : Fin 3, cubicGaussianProduct
          (gaussianPathMean l Q x i - z) (gaussianPathMean l Q x j - z)
          (gaussianPathCovariance l Q i i) (gaussianPathCovariance l Q j j)
          (gaussianPathCovariance l Q i j) := by
  let F (i j : Fin 3) (y : Vec3) : ℝ :=
    affineGaussianTest (-z) (Pi.single i 1) y ^ 3 * affineGaussianTest (-z) (Pi.single j 1) y ^ 3
  have hF (i j : Fin 3) : Continuous (F i j) :=
    ((affineGaussianTest_continuous_expGrowth (-z) (Pi.single i 1)).1.pow 3).mul
      ((affineGaussianTest_continuous_expGrowth (-z) (Pi.single j 1)).1.pow 3)
  have hgF (i j : Fin 3) : HasExpGrowth (F i j) :=
    ((affineGaussianTest_continuous_expGrowth (-z) (Pi.single i 1)).2.pow 3).mul
      ((affineGaussianTest_continuous_expGrowth (-z) (Pi.single j 1)).2.pow 3)
  have he : (fun y => terminalCubicResidual β α s h z y ^ 2) =
      fun y => (jet β α 3 (s + 4 * h) z / 6) ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, F i j y := by
    funext y
    simp only [terminalCubicResidual, F, affineGaussianTest_coordinate_center,
      Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    ring1
  rw [he, quadraticFirst_const_mul, quadraticFirst_double_sum l Q hl F hF hgF]
  dsimp only [F]
  simp_rw [quadraticFirst_cubic_pair l Q hl, affineGaussianTest_coordinate_center,
    gaussianPathVariance_coordinate, gaussianPathCross_coordinate]

def gaussianPathLinearMap : (l : List (ℝ × Vec3)) → QuadraticTerminal → Vec3 →ₗ[ℝ] Vec3
  | [], _ => LinearMap.id
  | u :: l, Q => (gaussianPathLinearMap l Q).comp
      ((quadraticNoiseLinear (riccatiRecursion l Q) u.1 u.2).comp (LinearMap.inl ℝ Vec3 ℝ))

theorem gaussianPathLinearMap_apply (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (w : Vec3) :
    gaussianPathLinearMap l Q w = gaussianPathLinear l Q w := by
  induction l generalizing w with
  | nil => rfl
  | cons u l ih =>
    simp only [gaussianPathLinearMap, LinearMap.comp_apply, LinearMap.inl_apply,
      quadraticNoiseLinear, LinearMap.coe_mk, AddHom.coe_mk, mul_zero, add_zero, ih]
    rfl

def gaussianPathLinearRows (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) : Mat3 :=
  fun i j => gaussianPathLinear l Q (Pi.single j 1) i

theorem gaussianPathLinear_rows (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (w : Vec3) (i : Fin 3) :
    gaussianPathLinear l Q w i = ∑ j, gaussianPathLinearRows l Q i j * w j := by
  have hw : w = ∑ j : Fin 3, w j • Pi.single j (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc
    _ = (gaussianPathLinearMap l Q) (∑ j : Fin 3, w j • Pi.single j (1 : ℝ)) i := by
      rw [gaussianPathLinearMap_apply, ← hw]
    _ = _ := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        gaussianPathLinearMap_apply, gaussianPathLinearRows]
      apply Finset.sum_congr rfl
      intro j _
      ring1

theorem gaussianPathMean_coordinate_affine (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (z : ℝ) (y : Vec3) (i : Fin 3) :
    gaussianPathMean l Q y i - z =
      affineGaussianTest (gaussianPathMean l Q 0 i - z) (gaussianPathLinearRows l Q i) y := by
  have H := congrFun (gaussianPathMean_shift l Q 0 y 1) i
  simp only [zero_add, one_smul, Pi.add_apply] at H
  rw [H, gaussianPathLinear_rows]
  unfold affineGaussianTest
  ring1

theorem gaussianPathMean_append (l t : List (ℝ × Vec3)) (Q : QuadraticTerminal) (x : Vec3) :
    gaussianPathMean (l ++ t) Q x =
      gaussianPathMean t Q (gaussianPathMean l (riccatiRecursion t Q) x) := by
  induction l generalizing x with
  | nil => rfl
  | cons u l ih =>
    simp only [List.cons_append, gaussianPathMean, riccatiRecursion_append]
    exact ih _

theorem gaussianPathLinear_append (l t : List (ℝ × Vec3)) (Q : QuadraticTerminal) (w : Vec3) :
    gaussianPathLinear (l ++ t) Q w =
      gaussianPathLinear t Q (gaussianPathLinear l (riccatiRecursion t Q) w) := by
  induction l generalizing w with
  | nil => rfl
  | cons u l ih =>
    simp only [List.cons_append, gaussianPathLinear, riccatiRecursion_append]
    exact ih _

theorem gaussianPathCovariance_append (l t : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (i j : Fin 3) :
    gaussianPathCovariance (l ++ t) Q i j = gaussianPathCovariance t Q i j +
      ∑ p : Fin 3, ∑ q : Fin 3, gaussianPathLinearRows t Q i p *
        gaussianPathCovariance l (riccatiRecursion t Q) p q * gaussianPathLinearRows t Q j q := by
  induction l generalizing i j with
  | nil => simp [gaussianPathCovariance]
  | cons u l ih =>
    simp only [List.cons_append, gaussianPathCovariance, riccatiRecursion_append,
      gaussianPathLinear_append, ih]
    rw [gaussianPathLinear_rows t Q _ i, gaussianPathLinear_rows t Q _ j]
    simp only [Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    ring1

theorem riccatiAdmissible_append (l t : List (ℝ × Vec3)) (Q : QuadraticTerminal) :
    RiccatiAdmissible (l ++ t) Q ↔
      RiccatiAdmissible t Q ∧ RiccatiAdmissible l (riccatiRecursion t Q) := by
  induction l with
  | nil => simp [RiccatiAdmissible]
  | cons u l ih =>
    simp only [List.cons_append, RiccatiAdmissible, riccatiRecursion_append, ih]
    tauto

theorem quadraticFirst_conditional_cubic_square (β : ℝ) (α : ℝ → ℝ) (s h z : ℝ)
    (l t : List (ℝ × Vec3)) (Q : QuadraticTerminal) (hl : RiccatiAdmissible (l ++ t) Q) (x : Vec3) :
    quadraticFirst l (riccatiRecursion t Q)
        (fun y => quadraticFirst t Q (terminalCubicResidual β α s h z) y ^ 2) x =
      (jet β α 3 (s + 4 * h) z / 6) ^ 2 *
        ∑ i : Fin 3, ∑ j : Fin 3, cubicGaussianProduct
          (gaussianPathMean (l ++ t) Q x i - z) (gaussianPathMean (l ++ t) Q x j - z)
          (gaussianPathCovariance (l ++ t) Q i i) (gaussianPathCovariance (l ++ t) Q j j)
          (gaussianPathCovariance (l ++ t) Q i j - gaussianPathCovariance t Q i j) := by
  have hparts := (riccatiAdmissible_append l t Q).mp hl
  let R := riccatiRecursion t Q
  let c : Fin 3 → ℝ := fun i => gaussianPathMean t Q 0 i - z
  let w : Fin 3 → Vec3 := gaussianPathLinearRows t Q
  let B : Mat3 := gaussianPathCovariance t Q
  let A (i : Fin 3) (y : Vec3) : ℝ :=
    affineGaussianTest (c i) (w i) y ^ 3 + 3 * B i i * affineGaussianTest (c i) (w i) y
  let F (i j : Fin 3) (y : Vec3) : ℝ := A i y * A j y
  have HA (i : Fin 3) : Continuous (A i) ∧ HasExpGrowth (A i) := by
    have H := affineGaussianTest_continuous_expGrowth (c i) (w i)
    exact ⟨(H.1.pow 3).add (continuous_const.mul H.1),
      (H.2.pow 3).add ((HasExpGrowth.const (3 * B i i)).mul H.2)⟩
  have hF (i j : Fin 3) : Continuous (F i j) := (HA i).1.mul (HA j).1
  have hgF (i j : Fin 3) : HasExpGrowth (F i j) := (HA i).2.mul (HA j).2
  have he : (fun y => quadraticFirst t Q (terminalCubicResidual β α s h z) y ^ 2) =
      fun y => (jet β α 3 (s + 4 * h) z / 6) ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, F i j y := by
    funext y
    rw [quadraticFirst_terminalCubicResidual β α s h z t Q hparts.1]
    simp_rw [gaussianPathMean_coordinate_affine t Q z y]
    simp only [F, A, c, w, B, Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    ring1
  rw [he, quadraticFirst_const_mul, quadraticFirst_double_sum l R hparts.2 F hF hgF]
  dsimp only [F, A]
  simp_rw [quadraticFirst_cubic_linear_pair l R hparts.2]
  have hm (i : Fin 3) : affineGaussianTest (c i) (w i) (gaussianPathMean l R x) =
      gaussianPathMean (l ++ t) Q x i - z := by
    rw [gaussianPathMean_append]
    exact (gaussianPathMean_coordinate_affine t Q z _ i).symm
  have hC (i j : Fin 3) : gaussianPathCross l R (w i) (w j) =
      gaussianPathCovariance (l ++ t) Q i j - B i j := by
    have H := gaussianPathCovariance_append l t Q i j
    change _ = B i j + gaussianPathCross l R (w i) (w j) at H
    linarith
  have hV (i : Fin 3) : gaussianPathVariance l R (w i) =
      gaussianPathCovariance (l ++ t) Q i i - B i i := hC i i
  simp_rw [hm, hC, hV]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold cubicLinearGaussianProduct cubicGaussianProduct
  ring1

def cubicGaussianCovariance (m n V W C : ℝ) : ℝ :=
  9 * (m ^ 2 + V) * (n ^ 2 + W) * C + 18 * m * n * C ^ 2 + 6 * C ^ 3

def frozenNestedCubicPolynomial (a w : ℝ) (m : Vec3) (V B₁ B₂ : Mat3) : ℝ :=
  (w / 6) ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
    (a * cubicGaussianCovariance (m i) (m j) (V i i) (V j j) (V i j) -
      a / 2 * cubicGaussianCovariance (m i) (m j) (V i i) (V j j) (V i j - B₂ i j) -
      a / 6 * cubicGaussianCovariance (m i) (m j) (V i i) (V j j) (V i j - B₁ i j))

theorem quadraticSecond_terminalCubicResidual (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ)
    (Q : QuadraticTerminal) (hQ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) Q) :
    quadraticSecond (frozenSchedule β a (1 / 2) h k) Q (terminalCubicResidual β α s h z) (fun _ => z) =
      frozenNestedCubicPolynomial a (jet β α 3 (s + 4 * h) z)
        (fun i => gaussianPathMean (frozenSchedule β a (1 / 2) h k) Q (fun _ => z) i - z)
        (gaussianPathCovariance (frozenSchedule β a (1 / 2) h k) Q)
        (gaussianPathCovariance (frozenShared β a (1 / 2) h k ++ frozenInner β a (1 / 2) h k) Q)
        (gaussianPathCovariance (frozenInner β a (1 / 2) h k) Q) := by
  let K := terminalCubicResidual β α s h z
  let c := frozenCommon β a (1 / 2) h k
  let d := frozenShared β a (1 / 2) h k
  let t := frozenInner β a (1 / 2) h k
  let full := frozenSchedule β a (1 / 2) h k
  have hK := terminalCubicResidual_continuous_expGrowth β α s h z
  rw [frozenSchedule_second_nested_squares β a h k Q hQ hK.1 hK.2]
  rw [quadraticFirst_terminalCubicResidual_square β α s h z full Q hQ]
  have h₁ : RiccatiAdmissible (c ++ (d ++ t)) Q := by
    simpa only [c, d, t, frozenSchedule, List.append_assoc] using hQ
  have h₂ : RiccatiAdmissible ((c ++ d) ++ t) Q := by
    simpa only [List.append_assoc] using h₁
  have H₁ := quadraticFirst_conditional_cubic_square β α s h z c (d ++ t) Q h₁ (fun _ => z)
  have H₂ := quadraticFirst_conditional_cubic_square β α s h z (c ++ d) t Q h₂ (fun _ => z)
  have he₁ : c ++ (d ++ t) = full := by simp only [c, d, t, full, frozenSchedule, List.append_assoc]
  have he₂ : (c ++ d) ++ t = full := by rw [List.append_assoc]; exact he₁
  rw [he₁] at H₁
  rw [he₂] at H₂
  rw [H₁, H₂, quadraticFirst_terminalCubicResidual β α s h z full Q hQ]
  simp only [frozenNestedCubicPolynomial, cubicGaussianProduct, cubicGaussianCovariance,
    full, d, t, Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ring1

theorem frozenNestedCubicPolynomial_zero_mean (a w : ℝ) (V B₁ B₂ : Mat3) :
    frozenNestedCubicPolynomial a w 0 V B₁ B₂ =
      a * w ^ 2 / 4 * (∑ i : Fin 3, ∑ j : Fin 3, V i i * V j j *
        (V i j - (V i j - B₂ i j) / 2 - (V i j - B₁ i j) / 6)) +
      a * w ^ 2 / 6 * (entryCubeSum V - entryCubeSum (V - B₂) / 2 - entryCubeSum (V - B₁) / 6) := by
  simp only [frozenNestedCubicPolynomial, cubicGaussianCovariance, Pi.zero_apply,
    entryCubeSum, Matrix.sub_apply, Fin.sum_univ_succ]
  ring1

def frozenNestedCubicLeading (a b w k : ℝ) : ℝ :=
  frozenNestedCubicPolynomial a w 0
    (b • (q0 (1 / 2) k + q1 (1 / 2) k + physicalInner k))
    (b • (q1 (1 / 2) k + physicalInner k)) (b • physicalInner k)

private theorem entryCubeSum_smul (b : ℝ) (A : Mat3) :
    entryCubeSum (b • A) = b ^ 3 * entryCubeSum A := by
  simp only [entryCubeSum, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ]
  ring1

private theorem frozenWeightedCovariance_entryTotal (k : ℝ) :
    matrixEntryTotal (frozenRiccatiCovariance₀ k) = 12 := by
  have H₀ := congrFun (frozenRiccatiCovariance₀_ones k) 0
  have H₁ := congrFun (frozenRiccatiCovariance₀_ones k) 1
  have H₂ := congrFun (frozenRiccatiCovariance₀_ones k) 2
  norm_num [Matrix.mulVec, dotProduct, ones, matrixEntryTotal, Fin.sum_univ_succ] at H₀ H₁ H₂ ⊢
  linarith

theorem frozenNestedCubicLeading_eq (a b w k : ℝ) :
    frozenNestedCubicLeading a b w k = 48 * a * b ^ 3 * w ^ 2 +
      2 * a * b ^ 3 * w ^ 2 * physicalWick k := by
  let U := q0 (1 / 2) k
  let W := q1 (1 / 2) k
  let Z := physicalInner k
  have hV : U + W + Z = frozenCovarianceLinear k := by
    unfold U W Z frozenCovarianceLinear frozenRiccatiCovariance₀ frozenRiccatiCovariance₁ frozenRiccatiCovariance₂
    module
  have hdiag (i : Fin 3) : (U + W + Z) i i = 4 := by
    rw [hV]
    exact frozenCovarianceLinear_diagonal k i
  have hsum : (∑ i : Fin 3, ∑ j : Fin 3,
      ((U + W + Z) i j - (U + W) i j / 2 - U i j / 6)) = 12 := by
    have H := frozenWeightedCovariance_entryTotal k
    simp only [matrixEntryTotal, frozenRiccatiCovariance₀, frozenRiccatiCovariance₁,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ] at H
    dsimp only [U, W, Z]
    simp only [Matrix.add_apply, Fin.sum_univ_succ]
    linear_combination H
  have hsub₁ : b • (U + W + Z) - b • (W + Z) = b • U := by module
  have hsub₂ : b • (U + W + Z) - b • Z = b • (U + W) := by module
  unfold frozenNestedCubicLeading
  change frozenNestedCubicPolynomial a w 0 (b • (U + W + Z)) (b • (W + Z)) (b • Z) = _
  rw [frozenNestedCubicPolynomial_zero_mean, hsub₁, hsub₂,
    entryCubeSum_smul, entryCubeSum_smul, entryCubeSum_smul]
  have hlin : (∑ i : Fin 3, ∑ j : Fin 3, (b • (U + W + Z)) i i * (b • (U + W + Z)) j j *
        ((b • (U + W + Z)) i j - ((b • (U + W + Z)) i j - (b • Z) i j) / 2 -
          ((b • (U + W + Z)) i j - (b • (W + Z)) i j) / 6)) = 192 * b ^ 3 := by
    simp only [Matrix.smul_apply, smul_eq_mul, hdiag]
    simp only [Matrix.add_apply, Fin.sum_univ_succ] at hsum ⊢
    linear_combination (16 * b ^ 3) * hsum
  rw [hlin]
  change _ = 48 * a * b ^ 3 * w ^ 2 + 2 * a * b ^ 3 * w ^ 2 *
    wickContraction U W Z
  unfold wickContraction
  ring1

theorem frozenNestedCubicLeading_difference (a b w k : ℝ) :
    (frozenNestedCubicLeading a b w k - frozenNestedCubicLeading a b w 0) / 2 =
      a * b ^ 3 * w ^ 2 * (wickJet (1 / 2) k - wickJet (1 / 2) 0) := by
  rw [frozenNestedCubicLeading_eq, frozenNestedCubicLeading_eq]
  have H := physical_wick_difference k
  linear_combination (a * b ^ 3 * w ^ 2) * H

def cubicCovarianceScaledRemainder (h D v w c e f g : ℝ) : ℝ :=
  let A := D ^ 2 + e
  let B := D ^ 2 + f
  9 * (A * w * c + v * B * c + v * w * g +
    h * (A * B * c + A * w * g + v * B * g) + h ^ 2 * A * B * g) +
    18 * D ^ 2 * (c + h * g) ^ 2 +
    6 * (3 * c ^ 2 * g + 3 * h * c * g ^ 2 + h ^ 2 * g ^ 3)

theorem cubicGaussianCovariance_scaled_expansion (h D v w c e f g : ℝ) :
    cubicGaussianCovariance (h * D) (h * D) (h * v + h ^ 2 * e)
        (h * w + h ^ 2 * f) (h * c + h ^ 2 * g) =
      h ^ 3 * cubicGaussianCovariance 0 0 v w c +
        h ^ 4 * cubicCovarianceScaledRemainder h D v w c e f g := by
  unfold cubicGaussianCovariance cubicCovarianceScaledRemainder
  ring1

theorem matrix_resolvent_linear_taylor (A : Mat3) (t : ℝ) (hA : IsUnit (1 - t • A).det) :
    (1 - t • A)⁻¹ = 1 + t • A + t ^ 2 • (A * A * (1 - t • A)⁻¹) := by
  have he : (1 + t • A) * (1 - t • A) = 1 - t ^ 2 • (A * A) := by
    simp only [add_mul, mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    module
  have H := congrArg (fun B : Mat3 => B * (1 - t • A)⁻¹) he
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_one,
    sub_mul, Matrix.one_mul, Matrix.smul_mul] at H
  exact sub_eq_iff_eq_add.mp H.symm

def frozenSuffixList (β a h k : ℝ) : Fin 3 → List (ℝ × Vec3) :=
  ![frozenSchedule β a (1 / 2) h k,
    frozenShared β a (1 / 2) h k ++ frozenInner β a (1 / 2) h k,
    frozenInner β a (1 / 2) h k]

private theorem frozenSuffixList_admissible (β a h k : ℝ) (Q : QuadraticTerminal)
    (hQ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) Q) (j : Fin 3) :
    RiccatiAdmissible (frozenSuffixList β a h k j) Q := by
  have h₁ := riccatiAdmissible_suffix (frozenCommon β a (1 / 2) h k)
    (frozenShared β a (1 / 2) h k ++ frozenInner β a (1 / 2) h k) Q hQ
  have h₂ := riccatiAdmissible_suffix (frozenShared β a (1 / 2) h k)
    (frozenInner β a (1 / 2) h k) Q h₁
  fin_cases j
  · exact hQ
  · exact h₁
  · exact h₂

private theorem frozenSuffixList_precisionMatrix (β a h k χ : ℝ)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) (j : Fin 3) :
    riccatiPrecisionMatrix (frozenSuffixList β a h k j) χ =
      1 - (a * β ^ 2 * χ * h) • frozenRiccatiCovariance j k := by
  fin_cases j
  · change riccatiPrecisionMatrix (frozenSchedule β a (1 / 2) h k) χ =
      1 - (a * β ^ 2 * χ * h) • frozenRiccatiCovariance₀ k
    rw [riccatiPrecisionMatrix, frozenSchedule_weightedCovariance β a h k hh hk]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring1
  · change riccatiPrecisionMatrix (frozenShared β a (1 / 2) h k ++ frozenInner β a (1 / 2) h k) χ =
      1 - (a * β ^ 2 * χ * h) • frozenRiccatiCovariance₁ k
    rw [riccatiPrecisionMatrix, riccatiWeightedCovariance_append,
      frozenShared_weightedCovariance β a h k hh, frozenInner_weightedCovariance β a h k hh hk]
    ext i j
    simp only [frozenRiccatiCovariance₁,
      frozenRiccatiCovariance₂, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring1
  · change riccatiPrecisionMatrix (frozenInner β a (1 / 2) h k) χ =
      1 - (a * β ^ 2 * χ * h) • frozenRiccatiCovariance₂ k
    rw [riccatiPrecisionMatrix, frozenInner_weightedCovariance β a h k hh hk]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring1

private theorem frozenSuffixList_hessian (β a h k c u χ z : ℝ)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hQ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z))
    (j i l : Fin 3) :
    (riccatiRecursion (frozenSuffixList β a h k j) (separableTaylorQuadratic c u χ z)).hessian i l =
      χ * frozenCovarianceResolvent j (a * β ^ 2 * χ * h) k i l := by
  have H := congrFun (congrFun (riccatiRecursion_hessian_resolvent _ c u χ z
    (frozenSuffixList_admissible β a h k _ hQ j)) i) l
  rw [frozenSuffixList_precisionMatrix β a h k χ hh hk j] at H
  exact H

def frozenPrefixPathCovariance (β a h k : ℝ) (Q : QuadraticTerminal) : Fin 3 → Mat3 :=
  ![gaussianPathCovariance (frozenSuffixList β a h k 0) Q -
      gaussianPathCovariance (frozenSuffixList β a h k 1) Q,
    gaussianPathCovariance (frozenSuffixList β a h k 0) Q -
      gaussianPathCovariance (frozenSuffixList β a h k 2) Q,
    gaussianPathCovariance (frozenSuffixList β a h k 0) Q]

def frozenPrefixResolventCombination (t k : ℝ) : Fin 3 → Mat3 :=
  ![(3 : ℝ) • (frozenCovarianceResolvent 0 t k - frozenCovarianceResolvent 1 t k),
    (3 : ℝ) • frozenCovarianceResolvent 0 t k - frozenCovarianceResolvent 1 t k -
      (2 : ℝ) • frozenCovarianceResolvent 2 t k,
    (3 : ℝ) • frozenCovarianceResolvent 0 t k - frozenCovarianceResolvent 1 t k -
      frozenCovarianceResolvent 2 t k - 1]

theorem frozenPrefixPathCovariance_resolvent (β a h k c u χ z : ℝ)
    (ha : a ≠ 0) (hχ : χ ≠ 0) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hQ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z))
    (j i l : Fin 3) :
    frozenPrefixPathCovariance β a h k (separableTaylorQuadratic c u χ z) j i l =
      frozenPrefixResolventCombination (a * β ^ 2 * χ * h) k j i l / (a * χ) := by
  let Q := separableTaylorQuadratic c u χ z
  have H₀ := frozenSuffixList_hessian β a h k c u χ z hh hk hQ 0 i l
  have H₁ := frozenSuffixList_hessian β a h k c u χ z hh hk hQ 1 i l
  have H₂ := frozenSuffixList_hessian β a h k c u χ z hh hk hQ 2 i l
  change (riccatiRecursion (frozenSchedule β a (1 / 2) h k) Q).hessian i l = _ at H₀
  change (riccatiRecursion (frozenShared β a (1 / 2) h k ++ frozenInner β a (1 / 2) h k) Q).hessian i l = _ at H₁
  change (riccatiRecursion (frozenInner β a (1 / 2) h k) Q).hessian i l = _ at H₂
  have HC := gaussianPathCovariance_block (frozenCommon β a (1 / 2) h k)
    (frozenShared β a (1 / 2) h k ++ frozenInner β a (1 / 2) h k) c u χ z (a / 3)
    (div_ne_zero ha (by norm_num)) hχ (by simp [frozenCommon]) i l
  change gaussianPathCovariance (frozenSuffixList β a h k 0) Q i l -
    gaussianPathCovariance (frozenSuffixList β a h k 1) Q i l =
      ((riccatiRecursion (frozenSchedule β a (1 / 2) h k) Q).hessian i l -
        (riccatiRecursion (frozenShared β a (1 / 2) h k ++ frozenInner β a (1 / 2) h k) Q).hessian i l) /
          (a / 3 * χ ^ 2) at HC
  rw [H₀, H₁] at HC
  have HI := gaussianPathCovariance_block (frozenInner β a (1 / 2) h k) [] c u χ z a ha hχ
    (by simp [frozenInner]) i l
  simp only [List.append_nil, gaussianPathCovariance, riccatiRecursion,
    separableTaylorQuadratic, sub_zero] at HI
  change gaussianPathCovariance (frozenSuffixList β a h k 2) Q i l =
    ((riccatiRecursion (frozenInner β a (1 / 2) h k) Q).hessian i l - (if i = l then χ else 0)) /
      (a * χ ^ 2) at HI
  rw [H₂] at HI
  have HF := frozenSchedule_pathCovariance_resolvent β a h k c u χ z ha hχ hh hk hQ i l
  fin_cases j
  · change gaussianPathCovariance (frozenSuffixList β a h k 0) Q i l -
      gaussianPathCovariance (frozenSuffixList β a h k 1) Q i l = _
    rw [HC]
    change _ = 3 * (frozenCovarianceResolvent 0 (a * β ^ 2 * χ * h) k i l -
      frozenCovarianceResolvent 1 (a * β ^ 2 * χ * h) k i l) / (a * χ)
    field_simp [ha, hχ]
  · change gaussianPathCovariance (frozenSchedule β a (1 / 2) h k) Q i l -
      gaussianPathCovariance (frozenSuffixList β a h k 2) Q i l =
        (3 * frozenCovarianceResolvent 0 (a * β ^ 2 * χ * h) k i l -
          frozenCovarianceResolvent 1 (a * β ^ 2 * χ * h) k i l -
          2 * frozenCovarianceResolvent 2 (a * β ^ 2 * χ * h) k i l) / (a * χ)
    rw [HF, HI]
    split_ifs <;> field_simp [ha, hχ] <;> ring1
  · change gaussianPathCovariance (frozenSchedule β a (1 / 2) h k) Q i l = _
    rw [HF]
    rfl

def frozenPrefixCovarianceLinear (k : ℝ) : Fin 3 → Mat3 :=
  ![(3 : ℝ) • (frozenRiccatiCovariance₀ k - frozenRiccatiCovariance₁ k),
    (3 : ℝ) • frozenRiccatiCovariance₀ k - frozenRiccatiCovariance₁ k -
      (2 : ℝ) • frozenRiccatiCovariance₂ k,
    frozenCovarianceLinear k]

theorem frozenPrefixCovarianceLinear_eq (k : ℝ) :
    frozenPrefixCovarianceLinear k =
      ![q0 (1 / 2) k, q0 (1 / 2) k + q1 (1 / 2) k,
        q0 (1 / 2) k + q1 (1 / 2) k + physicalInner k] := by
  funext j
  fin_cases j <;>
    simp only [frozenPrefixCovarianceLinear, Matrix.cons_val_zero', Matrix.cons_val_succ', frozenCovarianceLinear,
      frozenRiccatiCovariance₀, frozenRiccatiCovariance₁, frozenRiccatiCovariance₂] <;> module

def frozenResolventSquare (j : Fin 3) (t k : ℝ) : Mat3 :=
  frozenRiccatiCovariance j k * frozenRiccatiCovariance j k * frozenCovarianceResolvent j t k

def frozenPrefixCovarianceRemainder (t k : ℝ) : Fin 3 → Mat3 :=
  ![(3 : ℝ) • (frozenResolventSquare 0 t k - frozenResolventSquare 1 t k),
    (3 : ℝ) • frozenResolventSquare 0 t k - frozenResolventSquare 1 t k -
      (2 : ℝ) • frozenResolventSquare 2 t k,
    (3 : ℝ) • frozenResolventSquare 0 t k - frozenResolventSquare 1 t k - frozenResolventSquare 2 t k]

theorem frozenPrefixPathCovariance_expansion (β a h k c u χ z : ℝ)
    (ha : a ≠ 0) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hQ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z))
    (j i l : Fin 3) :
    frozenPrefixPathCovariance β a h k (separableTaylorQuadratic c u χ z) j i l =
      β ^ 2 * h * frozenPrefixCovarianceLinear k j i l +
        a * β ^ 4 * χ * h ^ 2 * frozenPrefixCovarianceRemainder (a * β ^ 2 * χ * h) k j i l := by
  by_cases hχ : χ = 0
  · subst χ
    have hzero (l : List (ℝ × Vec3)) : gaussianPathCovariance l (separableTaylorQuadratic c u 0 z) =
        matrixChainCovariance l := by
      funext i j
      exact gaussianPathCovariance_zero_curvature l c u z i j
    have HI := frozenInner_covariance β a (1 / 2) 0 h k hh (by norm_num)
      (OW.repairLength_mem (by norm_num) hk)
    change matrixChainCovariance (frozenInner β a (1 / 2) h k) =
      (β ^ 2 * h) • physicalInner k at HI
    have HG : frozenPrefixPathCovariance β a h k (separableTaylorQuadratic c u 0 z) j =
        (β ^ 2 * h) • frozenPrefixCovarianceLinear k j := by
      unfold frozenPrefixPathCovariance frozenSuffixList
      simp_rw [hzero]
      rw [frozenPrefixCovarianceLinear_eq]
      fin_cases j
      · change matrixChainCovariance (frozenSchedule β a (1 / 2) h k) -
          matrixChainCovariance (frozenShared β a (1 / 2) h k ++ frozenInner β a (1 / 2) h k) =
            (β ^ 2 * h) • q0 (1 / 2) k
        rw [frozenSchedule]
        simp_rw [matrixChainCovariance_append]
        rw [frozenCommon_covariance β a (1 / 2) h k hh,
          frozenShared_covariance β a (1 / 2) h k hh (by norm_num), HI]
        ext p q
        change ((β ^ 2 * h * q0 (1 / 2) k p q + β ^ 2 * h * q1 (1 / 2) k p q) +
          β ^ 2 * h * physicalInner k p q) -
          (β ^ 2 * h * q1 (1 / 2) k p q + β ^ 2 * h * physicalInner k p q) =
          β ^ 2 * h * q0 (1 / 2) k p q
        ring1
      · change matrixChainCovariance (frozenSchedule β a (1 / 2) h k) -
          matrixChainCovariance (frozenInner β a (1 / 2) h k) =
            (β ^ 2 * h) • (q0 (1 / 2) k + q1 (1 / 2) k)
        rw [frozenSchedule]
        simp_rw [matrixChainCovariance_append]
        rw [frozenCommon_covariance β a (1 / 2) h k hh,
          frozenShared_covariance β a (1 / 2) h k hh (by norm_num), HI]
        ext p q
        change ((β ^ 2 * h * q0 (1 / 2) k p q + β ^ 2 * h * q1 (1 / 2) k p q) +
          β ^ 2 * h * physicalInner k p q) - β ^ 2 * h * physicalInner k p q =
          β ^ 2 * h * (q0 (1 / 2) k p q + q1 (1 / 2) k p q)
        ring1
      · change matrixChainCovariance (frozenSchedule β a (1 / 2) h k) =
          (β ^ 2 * h) • (q0 (1 / 2) k + q1 (1 / 2) k + physicalInner k)
        rw [frozenSchedule]
        simp_rw [matrixChainCovariance_append]
        rw [frozenCommon_covariance β a (1 / 2) h k hh,
          frozenShared_covariance β a (1 / 2) h k hh (by norm_num), HI]
        ext p q
        change (β ^ 2 * h * q0 (1 / 2) k p q + β ^ 2 * h * q1 (1 / 2) k p q) +
          β ^ 2 * h * physicalInner k p q =
          β ^ 2 * h * ((q0 (1 / 2) k p q + q1 (1 / 2) k p q) + physicalInner k p q)
        ring1
    rw [show frozenPrefixPathCovariance β a h k (separableTaylorQuadratic c u 0 z) j i l =
      β ^ 2 * h * frozenPrefixCovarianceLinear k j i l from congrFun (congrFun HG i) l]
    ring1
  · have hunit := frozenSchedule_resolvent_units β a h k c u χ z hh hk hQ
    have HR (r : Fin 3) : frozenCovarianceResolvent r (a * β ^ 2 * χ * h) k i l =
        (if i = l then 1 else 0) + (a * β ^ 2 * χ * h) * frozenRiccatiCovariance r k i l +
          (a * β ^ 2 * χ * h) ^ 2 * frozenResolventSquare r (a * β ^ 2 * χ * h) k i l := by
      have H := congrFun (congrFun (matrix_resolvent_linear_taylor (frozenRiccatiCovariance r k)
        (a * β ^ 2 * χ * h) (hunit r)) i) l
      simpa only [frozenCovarianceResolvent, frozenResolventSquare, Matrix.add_apply,
        Matrix.one_apply, Matrix.smul_apply, smul_eq_mul] using H
    rw [frozenPrefixPathCovariance_resolvent β a h k c u χ z ha hχ hh hk hQ]
    fin_cases j <;>
      simp only [frozenPrefixResolventCombination, frozenPrefixCovarianceLinear,
        frozenPrefixCovarianceRemainder, Matrix.cons_val_zero', Matrix.cons_val_succ', frozenCovarianceLinear,
        Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] <;>
      rw [HR 0, HR 1] <;> try rw [HR 2]
    all_goals
      simp only [frozenRiccatiCovariance, Matrix.cons_val]
      split_ifs <;> field_simp [ha, hχ] <;> ring1

def frozenCubicRemainderKernel (h a b χ D t k : ℝ) (j i l : Fin 3) : ℝ :=
  cubicCovarianceScaledRemainder h D
    (b * frozenPrefixCovarianceLinear k 2 i i) (b * frozenPrefixCovarianceLinear k 2 l l)
    (b * frozenPrefixCovarianceLinear k j i l)
    (a * b ^ 2 * χ * frozenPrefixCovarianceRemainder t k 2 i i)
    (a * b ^ 2 * χ * frozenPrefixCovarianceRemainder t k 2 l l)
    (a * b ^ 2 * χ * frozenPrefixCovarianceRemainder t k j i l)

def frozenCubicNormalizedRemainder (h a b χ w D t k : ℝ) : ℝ :=
  (w / 6) ^ 2 * ∑ i : Fin 3, ∑ l : Fin 3,
    (a * frozenCubicRemainderKernel h a b χ D t k 2 i l -
      a / 2 * frozenCubicRemainderKernel h a b χ D t k 1 i l -
      a / 6 * frozenCubicRemainderKernel h a b χ D t k 0 i l)

private theorem frozenNestedCubicLeading_prefix (a b w k : ℝ) :
    frozenNestedCubicLeading a b w k = (w / 6) ^ 2 * ∑ i : Fin 3, ∑ l : Fin 3,
      (a * cubicGaussianCovariance 0 0
          (b * frozenPrefixCovarianceLinear k 2 i i) (b * frozenPrefixCovarianceLinear k 2 l l)
          (b * frozenPrefixCovarianceLinear k 2 i l) -
        a / 2 * cubicGaussianCovariance 0 0
          (b * frozenPrefixCovarianceLinear k 2 i i) (b * frozenPrefixCovarianceLinear k 2 l l)
          (b * frozenPrefixCovarianceLinear k 1 i l) -
        a / 6 * cubicGaussianCovariance 0 0
          (b * frozenPrefixCovarianceLinear k 2 i i) (b * frozenPrefixCovarianceLinear k 2 l l)
          (b * frozenPrefixCovarianceLinear k 0 i l)) := by
  rw [frozenPrefixCovarianceLinear_eq]
  unfold frozenNestedCubicLeading frozenNestedCubicPolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  simp only [Matrix.cons_val, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Pi.zero_apply]
  unfold cubicGaussianCovariance
  ring1

theorem frozenNestedCubicPolynomial_scaled (h a b χ w D t k : ℝ) (C : Fin 3 → Mat3)
    (hC : ∀ j i l, C j i l = h * (b * frozenPrefixCovarianceLinear k j i l) +
      h ^ 2 * (a * b ^ 2 * χ * frozenPrefixCovarianceRemainder t k j i l)) :
    frozenNestedCubicPolynomial a w (fun _ => h * D) (C 2) (C 2 - C 0) (C 2 - C 1) =
      h ^ 3 * frozenNestedCubicLeading a b w k +
        h ^ 4 * frozenCubicNormalizedRemainder h a b χ w D t k := by
  rw [frozenNestedCubicLeading_prefix]
  unfold frozenNestedCubicPolynomial
  simp only [Matrix.sub_apply, sub_sub_cancel]
  simp_rw [hC, cubicGaussianCovariance_scaled_expansion]
  unfold frozenCubicNormalizedRemainder frozenCubicRemainderKernel
  simp only [Fin.sum_univ_succ]
  ring1

theorem quadraticSecond_terminalCubicResidual_expansion (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ)
    (ha : a ≠ 0) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hQ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z)) :
    let u := jet β α 1 (s + 4 * h) z
    let χ := jet β α 2 (s + 4 * h) z
    let w := jet β α 3 (s + 4 * h) z
    let D := 4 * a * β ^ 2 * u / (1 - 4 * a * β ^ 2 * χ * h)
    quadraticSecond (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z)
        (terminalCubicResidual β α s h z) (fun _ => z) =
      h ^ 3 * frozenNestedCubicLeading a (β ^ 2) w k +
        h ^ 4 * frozenCubicNormalizedRemainder h a (β ^ 2) χ w D (a * β ^ 2 * χ * h) k := by
  dsimp only
  let Q := terminalTaylorQuadratic β α s h z
  let χ := jet β α 2 (s + 4 * h) z
  let w := jet β α 3 (s + 4 * h) z
  let D := 4 * a * β ^ 2 * jet β α 1 (s + 4 * h) z / (1 - 4 * a * β ^ 2 * χ * h)
  let C := frozenPrefixPathCovariance β a h k Q
  have hm : (fun i => gaussianPathMean (frozenSchedule β a (1 / 2) h k) Q (fun _ => z) i - z) =
      fun _ => h * D := by
    funext i
    unfold Q terminalTaylorQuadratic
    unfold terminalTaylorQuadratic at hQ
    rw [frozenSchedule_pathMean β a h k _ _ _ z hh hk hQ i]
    dsimp only [D, χ]
    ring1
  have hC (j i l : Fin 3) : C j i l = h * (β ^ 2 * frozenPrefixCovarianceLinear k j i l) +
      h ^ 2 * (a * (β ^ 2) ^ 2 * χ * frozenPrefixCovarianceRemainder (a * β ^ 2 * χ * h) k j i l) := by
    have H := frozenPrefixPathCovariance_expansion β a h k _ _ _ z ha hh hk hQ j i l
    change C j i l = _ at H
    rw [H]
    ring1
  rw [quadraticSecond_terminalCubicResidual β α a s h k z Q hQ, hm]
  have hB₁ : gaussianPathCovariance (frozenShared β a (1 / 2) h k ++ frozenInner β a (1 / 2) h k) Q =
      C 2 - C 0 := by
    funext i l
    change gaussianPathCovariance (frozenShared β a (1 / 2) h k ++ frozenInner β a (1 / 2) h k) Q i l =
      gaussianPathCovariance (frozenSchedule β a (1 / 2) h k) Q i l -
      (gaussianPathCovariance (frozenSchedule β a (1 / 2) h k) Q i l -
        gaussianPathCovariance (frozenShared β a (1 / 2) h k ++ frozenInner β a (1 / 2) h k) Q i l)
    ring1
  have hB₂ : gaussianPathCovariance (frozenInner β a (1 / 2) h k) Q = C 2 - C 1 := by
    funext i l
    change gaussianPathCovariance (frozenInner β a (1 / 2) h k) Q i l =
      gaussianPathCovariance (frozenSchedule β a (1 / 2) h k) Q i l -
      (gaussianPathCovariance (frozenSchedule β a (1 / 2) h k) Q i l -
        gaussianPathCovariance (frozenInner β a (1 / 2) h k) Q i l)
    ring1
  rw [hB₁, hB₂]
  exact frozenNestedCubicPolynomial_scaled h a (β ^ 2) χ w D (a * β ^ 2 * χ * h) k C hC

theorem frozenPrefixCovarianceLinear_entry_contDiff (j i l : Fin 3) :
    ContDiff ℝ ∞ (fun x : ℝ × ℝ => frozenPrefixCovarianceLinear x.2 j i l) := by
  have hC := frozenRiccatiCovariance_entry_contDiff
  fin_cases j <;>
    simp only [frozenPrefixCovarianceLinear, Matrix.cons_val_zero', Matrix.cons_val_succ',
      frozenCovarianceLinear, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  · change ContDiff ℝ ∞ (fun x : ℝ × ℝ =>
      3 * (frozenRiccatiCovariance 0 x.2 i l - frozenRiccatiCovariance 1 x.2 i l))
    fun_prop
  · change ContDiff ℝ ∞ (fun x : ℝ × ℝ =>
      3 * frozenRiccatiCovariance 0 x.2 i l - frozenRiccatiCovariance 1 x.2 i l -
        2 * frozenRiccatiCovariance 2 x.2 i l)
    fun_prop
  · change ContDiff ℝ ∞ (fun x : ℝ × ℝ =>
      3 * frozenRiccatiCovariance 0 x.2 i l - frozenRiccatiCovariance 1 x.2 i l -
        frozenRiccatiCovariance 2 x.2 i l)
    fun_prop

theorem frozenResolventSquare_entry_contDiffOn (j i l : Fin 3) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => frozenResolventSquare j x.1 x.2 i l) frozenResolventDomain := by
  have hC := frozenRiccatiCovariance_entry_contDiff
  have hR := frozenCovarianceResolvent_entry_contDiffOn
  change ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => ∑ p, (∑ q,
    frozenRiccatiCovariance j x.2 i q * frozenRiccatiCovariance j x.2 q p) *
      frozenCovarianceResolvent j x.1 x.2 p l) frozenResolventDomain
  fun_prop

theorem frozenPrefixCovarianceRemainder_entry_contDiffOn (j i l : Fin 3) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => frozenPrefixCovarianceRemainder x.1 x.2 j i l)
      frozenResolventDomain := by
  have hR := frozenResolventSquare_entry_contDiffOn
  fin_cases j <;>
    simp only [frozenPrefixCovarianceRemainder, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] <;> fun_prop

private theorem cubicCovarianceScaledRemainder_contDiff :
    ContDiff ℝ ∞ (fun p : Fin 8 → ℝ =>
      cubicCovarianceScaledRemainder (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) (p 7)) := by
  unfold cubicCovarianceScaledRemainder
  fun_prop

def frozenCubicParameterRemainder (x : (Fin 10 → ℝ) × ℝ) : ℝ :=
  frozenCubicNormalizedRemainder (x.1 0) (x.1 1) (x.1 2) (x.1 3) (x.1 4) (x.1 5) (x.1 9) x.2

theorem frozenCubicParameterRemainder_contDiffOn :
    ContDiffOn ℝ ∞ frozenCubicParameterRemainder firstTaylorParameterDomain := by
  have hp (i : Fin 10) : ContDiff ℝ ∞ (fun x : (Fin 10 → ℝ) × ℝ => x.1 i) := by fun_prop
  have hm : ContDiff ℝ ∞ (fun x : (Fin 10 → ℝ) × ℝ => (x.1 9, x.2)) := by fun_prop
  have hn : ContDiff ℝ ∞ (fun x : (Fin 10 → ℝ) × ℝ => ((0 : ℝ), x.2)) := by fun_prop
  have hL (j i l : Fin 3) : ContDiffOn ℝ ∞
      (fun x : (Fin 10 → ℝ) × ℝ => frozenPrefixCovarianceLinear x.2 j i l) firstTaylorParameterDomain := by
    have H := (frozenPrefixCovarianceLinear_entry_contDiff j i l).comp hn
    simpa only [Function.comp_def] using H.contDiffOn (s := firstTaylorParameterDomain)
  have hR (j i l : Fin 3) : ContDiffOn ℝ ∞
      (fun x : (Fin 10 → ℝ) × ℝ => frozenPrefixCovarianceRemainder (x.1 9) x.2 j i l)
      firstTaylorParameterDomain := by
    have H := (frozenPrefixCovarianceRemainder_entry_contDiffOn j i l).comp
      (hm.contDiffOn (s := firstTaylorParameterDomain))
      (show MapsTo (fun x : (Fin 10 → ℝ) × ℝ => (x.1 9, x.2))
        firstTaylorParameterDomain frozenResolventDomain from fun _ hx => hx.1)
    simpa only [Function.comp_def] using H
  have HK (j i l : Fin 3) : ContDiffOn ℝ ∞
      (fun x : (Fin 10 → ℝ) × ℝ => frozenCubicRemainderKernel
        (x.1 0) (x.1 1) (x.1 2) (x.1 3) (x.1 5) (x.1 9) x.2 j i l) firstTaylorParameterDomain := by
    let v : ((Fin 10 → ℝ) × ℝ) → (Fin 8 → ℝ) := fun x =>
      ![x.1 0, x.1 5, x.1 2 * frozenPrefixCovarianceLinear x.2 2 i i,
        x.1 2 * frozenPrefixCovarianceLinear x.2 2 l l, x.1 2 * frozenPrefixCovarianceLinear x.2 j i l,
        x.1 1 * (x.1 2) ^ 2 * x.1 3 * frozenPrefixCovarianceRemainder (x.1 9) x.2 2 i i,
        x.1 1 * (x.1 2) ^ 2 * x.1 3 * frozenPrefixCovarianceRemainder (x.1 9) x.2 2 l l,
        x.1 1 * (x.1 2) ^ 2 * x.1 3 * frozenPrefixCovarianceRemainder (x.1 9) x.2 j i l]
    have hv : ContDiffOn ℝ ∞ v firstTaylorParameterDomain := by
      apply contDiffOn_pi.mpr
      intro q
      fin_cases q
      · exact (hp 0).contDiffOn
      · exact (hp 5).contDiffOn
      · exact (hp 2).contDiffOn.mul (hL 2 i i)
      · exact (hp 2).contDiffOn.mul (hL 2 l l)
      · exact (hp 2).contDiffOn.mul (hL j i l)
      · exact (((hp 1).contDiffOn.mul ((hp 2).contDiffOn.pow 2)).mul (hp 3).contDiffOn).mul (hR 2 i i)
      · exact (((hp 1).contDiffOn.mul ((hp 2).contDiffOn.pow 2)).mul (hp 3).contDiffOn).mul (hR 2 l l)
      · exact (((hp 1).contDiffOn.mul ((hp 2).contDiffOn.pow 2)).mul (hp 3).contDiffOn).mul (hR j i l)
    have H := cubicCovarianceScaledRemainder_contDiff.comp_contDiffOn hv
    simpa only [Function.comp_def, v, Matrix.cons_val, frozenCubicRemainderKernel] using H
  unfold frozenCubicParameterRemainder frozenCubicNormalizedRemainder
  fun_prop

theorem frozenResolventSquare_neg (j : Fin 3) (t k : ℝ) :
    frozenResolventSquare j t (-k) = (frozenResolventSquare j t k).submatrix frozenTiltSwap frozenTiltSwap := by
  unfold frozenResolventSquare
  rw [frozenRiccatiCovariance_neg, frozenCovarianceResolvent_neg]
  simp only [Matrix.submatrix_mul_equiv]

theorem frozenPrefixCovarianceLinear_neg (k : ℝ) (j : Fin 3) :
    frozenPrefixCovarianceLinear (-k) j =
      (frozenPrefixCovarianceLinear k j).submatrix frozenTiltSwap frozenTiltSwap := by
  have H₀ := frozenRiccatiCovariance_neg 0 k
  have H₁ := frozenRiccatiCovariance_neg 1 k
  have H₂ := frozenRiccatiCovariance_neg 2 k
  change frozenRiccatiCovariance₀ (-k) = (frozenRiccatiCovariance₀ k).submatrix frozenTiltSwap frozenTiltSwap at H₀
  change frozenRiccatiCovariance₁ (-k) = (frozenRiccatiCovariance₁ k).submatrix frozenTiltSwap frozenTiltSwap at H₁
  change frozenRiccatiCovariance₂ (-k) = (frozenRiccatiCovariance₂ k).submatrix frozenTiltSwap frozenTiltSwap at H₂
  fin_cases j <;>
    simp only [frozenPrefixCovarianceLinear, Matrix.cons_val_zero', Matrix.cons_val_succ', frozenCovarianceLinear] <;>
    rw [H₀, H₁] <;> try rw [H₂]
  all_goals rfl

theorem frozenPrefixCovarianceRemainder_neg (t k : ℝ) (j : Fin 3) :
    frozenPrefixCovarianceRemainder t (-k) j =
      (frozenPrefixCovarianceRemainder t k j).submatrix frozenTiltSwap frozenTiltSwap := by
  fin_cases j <;>
    simp only [frozenPrefixCovarianceRemainder, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    rw [frozenResolventSquare_neg, frozenResolventSquare_neg] <;> try rw [frozenResolventSquare_neg]
  all_goals rfl

theorem frozenCubicNormalizedRemainder_even (h a b χ w D t k : ℝ) :
    frozenCubicNormalizedRemainder h a b χ w D t (-k) = frozenCubicNormalizedRemainder h a b χ w D t k := by
  unfold frozenCubicNormalizedRemainder frozenCubicRemainderKernel
  simp_rw [frozenPrefixCovarianceLinear_neg, frozenPrefixCovarianceRemainder_neg, Matrix.submatrix_apply]
  congr 1
  let F (i l : Fin 3) : ℝ :=
    a * frozenCubicRemainderKernel h a b χ D t k 2 i l -
      a / 2 * frozenCubicRemainderKernel h a b χ D t k 1 i l -
      a / 6 * frozenCubicRemainderKernel h a b χ D t k 0 i l
  change (∑ i : Fin 3, ∑ l : Fin 3, F (frozenTiltSwap i) (frozenTiltSwap l)) = ∑ i, ∑ l, F i l
  calc
    _ = ∑ i : Fin 3, ∑ l : Fin 3, F i (frozenTiltSwap l) :=
      Equiv.sum_comp frozenTiltSwap (fun i => ∑ l : Fin 3, F i (frozenTiltSwap l))
    _ = _ := Finset.sum_congr rfl (fun i _ => Equiv.sum_comp frozenTiltSwap (F i))

private def cubicTiltDerivative (F : (Fin 10 → ℝ) × ℝ → ℝ)
    (x : (Fin 10 → ℝ) × ℝ) : ℝ := fderiv ℝ F x (0, 1)

theorem frozenCubicParameterRemainder_uniform_control (M : ℝ) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ 1 / 8 ∧
      ∀ p : Fin 10 → ℝ, (∀ i, |p i| ≤ M) → |p 9| ≤ δ →
        EvenSecondControl (fun k => frozenCubicParameterRemainder (p, k)) (1 / 2) C 0 := by
  let F := frozenCubicParameterRemainder
  have hF := frozenCubicParameterRemainder_contDiffOn
  have hU := firstTaylorParameterDomain_isOpen
  have hF₁ : ContDiffOn ℝ ∞ (cubicTiltDerivative F) firstTaylorParameterDomain :=
    (hF.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  have hF₂ : ContDiffOn ℝ ∞ (cubicTiltDerivative (cubicTiltDerivative F)) firstTaylorParameterDomain :=
    (hF₁.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  obtain ⟨δ₀, hδ₀, _, hrect⟩ := frozenResolventDomain_contains_rectangle
  let δ := min δ₀ (1 / 8)
  let K : Set (Fin 10 → ℝ) :=
    (Set.pi Set.univ (fun _ => Icc (-M) M)) ∩ {p | p 9 ∈ Icc (-δ) δ}
  have hK : IsCompact K := (isCompact_univ_pi (fun _ => isCompact_Icc)).inter_right
    (isClosed_Icc.preimage (by fun_prop))
  have hKU : K ×ˢ Icc (-(1 / 2) : ℝ) (1 / 2) ⊆ firstTaylorParameterDomain := by
    rintro ⟨p, k⟩ ⟨hp, hk⟩
    have ht : p 9 ∈ Icc (-δ₀) δ₀ :=
      ⟨(neg_le_neg (min_le_left _ _)).trans hp.2.1, hp.2.2.trans (min_le_left _ _)⟩
    refine ⟨hrect ⟨ht, hk⟩, ?_⟩
    have H : p 9 ≤ 1 / 8 := hp.2.2.trans (min_le_right _ _)
    linarith
  obtain ⟨B, hB⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn (hF₂.continuousOn.mono hKU)
  refine ⟨1 + |B|, δ, by positivity, lt_min hδ₀ (by norm_num), min_le_right _ _, ?_⟩
  intro p hp ht
  have hpK : p ∈ K := ⟨fun i _ => abs_le.mp (hp i), abs_le.mp ht⟩
  refine ⟨fun k => cubicTiltDerivative F (p, k),
    fun k => cubicTiltDerivative (cubicTiltDerivative F) (p, k), ?_, ?_, ?_⟩
  · intro k hk
    have hx := hKU (show (p, k) ∈ K ×ˢ Icc (-(1 / 2) : ℝ) (1 / 2) from ⟨hpK, hk⟩)
    have hline : HasDerivAt (fun t : ℝ => (p, t)) (0, 1) k :=
      (hasDerivAt_const k p).prodMk (hasDerivAt_id k)
    exact ⟨((hF.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt k hline,
      ((hF₁.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt k hline⟩
  · intro k hk
    have HB : |cubicTiltDerivative (cubicTiltDerivative F) (p, k)| ≤ B := hB (p, k) ⟨hpK, hk⟩
    simp only [zero_mul, add_zero]
    linarith [le_abs_self B]
  · intro k _
    exact frozenCubicNormalizedRemainder_even _ _ _ _ _ _ _ k

def cubicWickCoefficientError (β : ℝ) (α : ℝ → ℝ) (a s h z k : ℝ) : ℝ :=
  (quadraticSecond (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z)
      (terminalCubicResidual β α s h z) (fun _ => z) -
    quadraticSecond (frozenSchedule β a (1 / 2) h 0) (terminalTaylorQuadratic β α s h z)
      (terminalCubicResidual β α s h z) (fun _ => z)) / 2 -
    wickRow k h a (β ^ 2) (jet β α 3 (s + 4 * h) z)

theorem cubicWickCoefficientError_uniform_control (β B : ℝ) (hB : 0 < B) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ (α : ℝ → ℝ) (a s h z : ℝ),
      a ∈ Ioc (0 : ℝ) 1 → 0 ≤ h → h ≤ h₀ →
      (∀ j ∈ Icc (1 : ℕ) 3, |jet β α j (s + 4 * h) z| ≤ B) →
      EvenSecondControl (cubicWickCoefficientError β α a s h z) (1 / 4) (C * h ^ 4) 0 := by
  let M := β ^ 2 + B + 8 * β ^ 2 * B + 2
  obtain ⟨C, δ, hC, hδ, hδ₈, H⟩ := frozenCubicParameterRemainder_uniform_control M
  obtain ⟨η, hη, hA⟩ := terminalTaylorQuadratic_uniform_admissible β B hB
  let T := (β ^ 2 + 1) * (B + 1)
  have hT : 0 < T := by dsimp only [T]; positivity
  refine ⟨C, min (min η 1) (δ / T), hC, by positivity, ?_⟩
  intro α a s h z ha hh hh₀ hj
  let u := jet β α 1 (s + 4 * h) z
  let χ := jet β α 2 (s + 4 * h) z
  let w := jet β α 3 (s + 4 * h) z
  let t := a * β ^ 2 * χ * h
  let D := 4 * a * β ^ 2 * u / (1 - 4 * a * β ^ 2 * χ * h)
  let p : Fin 10 → ℝ := ![h, a, β ^ 2, χ, w, D, 0, 0, 0, t]
  have hhη : h ≤ η := (hh₀.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hh₁ : h ≤ 1 := (hh₀.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hu : |u| ≤ B := hj 1 (by norm_num)
  have hχ : |χ| ≤ B := hj 2 (by norm_num)
  have hw : |w| ≤ B := hj 3 (by norm_num)
  have ht : |t| ≤ δ := by
    have hta : |t| ≤ T * h := by
      dsimp only [t, T]
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos ha.1,
        abs_of_nonneg (sq_nonneg β), abs_of_nonneg hh]
      calc
        _ ≤ 1 * (β ^ 2 + 1) * (B + 1) * h := by gcongr <;> linarith [ha.2, hχ]
        _ = _ := by ring1
    exact hta.trans (by simpa only [mul_comm] using
      (le_div_iff₀ hT).mp (hh₀.trans (min_le_right _ _)))
  have hd : (1 / 2 : ℝ) ≤ 1 - 4 * a * β ^ 2 * χ * h := by
    have Ht := (le_abs_self t).trans (ht.trans hδ₈)
    dsimp only [t] at Ht
    nlinarith
  have hD : |D| ≤ 8 * β ^ 2 * B := by
    dsimp only [D]
    rw [abs_div, abs_of_pos (by linarith : 0 < 1 - 4 * a * β ^ 2 * χ * h)]
    apply (div_le_iff₀ (by linarith : 0 < 1 - 4 * a * β ^ 2 * χ * h)).mpr
    have Hn : |4 * a * β ^ 2 * u| ≤ 4 * β ^ 2 * B := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
        abs_of_pos ha.1, abs_of_nonneg (sq_nonneg β)]
      calc
        _ ≤ 4 * 1 * β ^ 2 * B := by gcongr; linarith [ha.2]
        _ = _ := by ring1
    nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 8 * β ^ 2 * B)]
  have h₁M : 1 ≤ M := by
    dsimp only [M]
    nlinarith [sq_nonneg β, mul_nonneg (sq_nonneg β) hB.le]
  have hBM : B ≤ M := by
    dsimp only [M]
    nlinarith [sq_nonneg β, mul_nonneg (sq_nonneg β) hB.le]
  have hDM : 8 * β ^ 2 * B ≤ M := by
    dsimp only [M]
    nlinarith [sq_nonneg β]
  have hp : ∀ i, |p i| ≤ M := by
    intro i
    fin_cases i
    · change |h| ≤ M; rw [abs_of_nonneg hh]; exact hh₁.trans h₁M
    · change |a| ≤ M; rw [abs_of_pos ha.1]; exact ha.2.trans h₁M
    · change |β ^ 2| ≤ M
      rw [abs_of_nonneg (sq_nonneg β)]
      dsimp only [M]
      nlinarith [mul_nonneg (sq_nonneg β) hB.le]
    · exact hχ.trans hBM
    · exact hw.trans hBM
    · exact hD.trans hDM
    · change |(0 : ℝ)| ≤ M; exact (abs_zero.trans_le (by linarith))
    · change |(0 : ℝ)| ≤ M; exact (abs_zero.trans_le (by linarith))
    · change |(0 : ℝ)| ≤ M; exact (abs_zero.trans_le (by linarith))
    · exact ht.trans (hδ₈.trans ((by norm_num : (1 / 8 : ℝ) ≤ 1).trans h₁M))
  have HG := ((H p hp ht).sub_const (frozenCubicParameterRemainder (p, 0))).const_mul (h ^ 4 / 2)
  have HE : EvenSecondControl
      (fun k => h ^ 4 / 2 * (frozenCubicParameterRemainder (p, k) - frozenCubicParameterRemainder (p, 0)))
      (1 / 2) (C * h ^ 4) 0 := by
    apply HG.mono
    · rw [abs_of_nonneg (by positivity : 0 ≤ h ^ 4 / 2)]
      nlinarith [mul_nonneg hC.le (pow_nonneg hh 4)]
    · rw [mul_zero]
  refine HE.transfer (by norm_num) ?_
  intro k hk
  have HK := quadraticSecond_terminalCubicResidual_expansion β α a s h k z (ne_of_gt ha.1) hh (abs_le.mpr hk)
    (hA α a s h k z ha hh hhη (abs_le.mpr hk) hχ)
  have H₀ := quadraticSecond_terminalCubicResidual_expansion β α a s h 0 z (ne_of_gt ha.1) hh (by norm_num)
    (hA α a s h 0 z ha hh hhη (by norm_num) hχ)
  have HL := frozenNestedCubicLeading_difference a (β ^ 2) w k
  unfold cubicWickCoefficientError wickRow
  simp only [frozenCubicParameterRemainder, p, Matrix.cons_val] at ⊢
  dsimp only [u, χ, w, D, t] at HK H₀ HL ⊢
  linear_combination HK / 2 - H₀ / 2 + h ^ 3 * HL

theorem scalarData_cubicWickCoefficientError_control {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      EvenSecondControl
        (cubicWickCoefficientError β (cdf (D.μ : Measure ℝ))
          (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z)
        (1 / 4) (C * h ^ 4) 0 := by
  let B := scalarTerminalJetBound D 3 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 3]
  obtain ⟨C, η, hC, hη, H⟩ := cubicWickCoefficientError_uniform_control β B hB
  obtain ⟨c, T, hc, hT, hlin⟩ := D.lin_lower
  let v := min (l / 2) T
  have hv : 0 < v := lt_min (by positivity) hT
  refine ⟨C, min η (min (l / 2) ((D.q - u) / 3)), hC, by positivity, ?_⟩
  intro r hr h hh hh₀ z
  have hhη : h ≤ η := hh₀.trans (min_le_left _ _)
  have hhl : h ≤ l / 2 := (hh₀.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 3 := (hh₀.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hs : v ≤ r - h := (min_le_left _ _).trans (by linarith [hr.1])
  have ha : cdf (D.μ : Measure ℝ) (r - h) ∈ Ioc (0 : ℝ) 1 := by
    refine ⟨?_, cdf_le_one _ _⟩
    exact (mul_pos hc hv).trans_le ((hlin v ⟨hv.le, min_le_right _ _⟩).trans
      ((cdf (D.μ : Measure ℝ)).mono hs))
  have ht : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith [hr.1]
    · linarith [hr.2, D.q_mem.2]
  apply H _ _ (r - h) h z ha hh.le hhη
  intro j hj
  exact (scalarData_jet_le D hj.1 hj.2 ht z).trans (by dsimp only [B]; linarith)

theorem scalarData_quadraticFirst_tail_memLp_two {β : ℝ} (D : ScalarData β)
    {s h : ℝ} (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) (z : ℝ)
    (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (hl : RiccatiAdmissible l Q)
    (x v : Vec3) (m : ℝ) (σ : ℝ≥0) :
    MemLp (fun t : ℝ => quadraticFirst l Q
      (fun y => terminalResidual β (cdf (D.μ : Measure ℝ)) s h z y -
        terminalCubicResidual β (cdf (D.μ : Measure ℝ)) s h z y) (x + t • v))
      2 (gaussianReal m σ) := by
  have hφ := scalarData_phi_regular D ht
  have hK := terminalCubicResidual_continuous_expGrowth β (cdf (D.μ : Measure ℝ)) s h z
  exact quadraticFirst_line_memLp_two l Q hl
    ((terminalResidual_continuous _ _ s h z hφ).sub hK.1)
    (hasExpGrowth_sub (terminalResidual_hasExpGrowth _ _ s h z hφ) hK.2) x v m σ

theorem quadraticAverage_mono (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3)
    {F G : Vec3 → ℝ} (hF : Continuous F) (hgF : HasExpGrowth F)
    (hG : Continuous G) (hgG : HasExpGrowth G) (hFG : ∀ y, F y ≤ G y) :
    quadraticAverage Q m v F x ≤ quadraticAverage Q m v G x := by
  have HI (K : Vec3 → ℝ) (hK : Continuous K) (hg : HasExpGrowth K) :
      Integrable (fun t : ℝ => K (x + t • v))
        (quadraticGaussian (Q.precision m v) (m * Q.slope v x)) := by
    exact (hasExpGrowth_affine hg x (ContinuousLinearMap.toSpanSingleton ℝ v)).integrable_gaussianMeasure
      (by fun_prop)
  exact integral_mono (HI F hF hgF) (HI G hG hgG) (fun t => hFG (x + t • v))

theorem quadraticFirst_mono (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible l Q) {F G : Vec3 → ℝ}
    (hF : Continuous F) (hgF : HasExpGrowth F) (hG : Continuous G) (hgG : HasExpGrowth G)
    (hFG : ∀ y, F y ≤ G y) (x : Vec3) :
    quadraticFirst l Q F x ≤ quadraticFirst l Q G x := by
  induction l generalizing x with
  | nil => exact hFG x
  | cons u l ih =>
    have HF := quadraticFirst_continuous_expGrowth l Q hl.1 hF hgF
    have HG := quadraticFirst_continuous_expGrowth l Q hl.1 hG hgG
    exact quadraticAverage_mono _ _ _ x HF.1 HF.2 HG.1 HG.2 (ih hl.1)

theorem quadraticAverage_square_le (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3)
    {K : Vec3 → ℝ} (hK : Continuous K) (hg : HasExpGrowth K) :
    quadraticAverage Q m v K x ^ 2 ≤ quadraticAverage Q m v (fun y => K y ^ 2) x := by
  have hM := quadraticFirst_line_memLp_two [] Q (by trivial) hK hg x v
    (m * Q.slope v x / Q.precision m v) ((Q.precision m v)⁻¹).toNNReal
  change MemLp (fun t => K (x + t • v)) 2
    (quadraticGaussian (Q.precision m v) (m * Q.slope v x)) at hM
  have H := variance_nonneg (fun t => K (x + t • v))
    (quadraticGaussian (Q.precision m v) (m * Q.slope v x))
  rw [← quadraticVariance_eq_variance Q m v x K hM] at H
  unfold quadraticVariance at H
  linarith

theorem quadraticFirst_square_le (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible l Q) {K : Vec3 → ℝ} (hK : Continuous K) (hg : HasExpGrowth K) (x : Vec3) :
    quadraticFirst l Q K x ^ 2 ≤ quadraticFirst l Q (fun y => K y ^ 2) x := by
  induction l generalizing x with
  | nil => exact le_rfl
  | cons u l ih =>
    have HF := quadraticFirst_continuous_expGrowth l Q hl.1 hK hg
    have HG := quadraticFirst_continuous_expGrowth l Q hl.1 (hK.pow 2) (hg.pow 2)
    calc
      _ ≤ quadraticAverage (riccatiRecursion l Q) u.1 u.2
          (fun y => quadraticFirst l Q K y ^ 2) x := quadraticAverage_square_le _ _ _ x HF.1 HF.2
      _ ≤ _ := quadraticAverage_mono _ _ _ x (HF.1.pow 2) (HF.2.pow 2) HG.1 HG.2 (ih hl.1)

theorem quadraticFirst_conditional_square_le (l t : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible (l ++ t) Q) {K : Vec3 → ℝ}
    (hK : Continuous K) (hg : HasExpGrowth K) (x : Vec3) :
    quadraticFirst l (riccatiRecursion t Q) (fun y => quadraticFirst t Q K y ^ 2) x ≤
      quadraticFirst (l ++ t) Q (fun y => K y ^ 2) x := by
  have hparts := (riccatiAdmissible_append l t Q).mp hl
  have HF := quadraticFirst_continuous_expGrowth t Q hparts.1 hK hg
  have HG := quadraticFirst_continuous_expGrowth t Q hparts.1 (hK.pow 2) (hg.pow 2)
  rw [quadraticFirst_append]
  exact quadraticFirst_mono l _ hparts.2 (HF.1.pow 2) (HF.2.pow 2) HG.1 HG.2
    (quadraticFirst_square_le t Q hparts.1 hK hg) x

private theorem scalarTaylorPolynomial_hasExpGrowth (f : ℝ → ℝ) (n : ℕ) (z : ℝ) :
    HasExpGrowth (scalarTaylorPolynomial f n z) := by
  have hid : HasExpGrowth (fun y : ℝ => y) := HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)
  have hshift : HasExpGrowth (fun y : ℝ => y - z) := hasExpGrowth_sub hid (HasExpGrowth.const z)
  unfold scalarTaylorPolynomial
  apply HasExpGrowth.finsetSum
  intro j _
  have H : HasExpGrowth (fun y : ℝ =>
      iteratedDeriv j f z * (y - z) ^ j * (j.factorial : ℝ)⁻¹) :=
    ((HasExpGrowth.const (iteratedDeriv j f z)).mul (hshift.pow j)).mul (HasExpGrowth.const _)
  simpa only [div_eq_mul_inv] using H

set_option maxHeartbeats 800000 in
theorem scalarData_terminalTailSquare_le {β : ℝ} (D : ScalarData β) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ a s h z : ℝ,
      a ∈ Ioc (0 : ℝ) 1 → 0 ≤ h → h ≤ h₀ → s + 4 * h ∈ Icc (0 : ℝ) 1 →
      ∀ k ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
        quadraticFirst (frozenSchedule β a (1 / 2) h k)
          (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) s h z)
          (fun y => (terminalResidual β (cdf (D.μ : Measure ℝ)) s h z y -
            terminalCubicResidual β (cdf (D.μ : Measure ℝ)) s h z y) ^ 2) (fun _ => z) ≤ C * h ^ 4 := by
  obtain ⟨C, η, hC, hη, HT⟩ := scalarData_fourthTailSquareCoordinate_control D
  let B := scalarTerminalJetBound D 2 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 2]
  obtain ⟨ξ, hξ, hA⟩ := terminalTaylorQuadratic_uniform_admissible β B hB
  refine ⟨9 * C, min η ξ, by positivity, by positivity, ?_⟩
  intro a s h z ha hh hh₀ ht k hk
  let α := cdf (D.μ : Measure ℝ)
  let f := Phi β α (s + 4 * h)
  let Q := terminalTaylorQuadratic β α s h z
  let l := frozenSchedule β a (1 / 2) h k
  let T : Vec3 → ℝ := fun y => terminalResidual β α s h z y - terminalCubicResidual β α s h z y
  let F (i : Fin 3) : Vec3 → ℝ := fun y => scalarFourthTail f z (y i) ^ 2
  have hφ := scalarData_phi_regular D ht
  have hf : Continuous f := (scalarData_phi_contDiff D ht).continuous
  have hT : Continuous T := (terminalResidual_continuous β α s h z hφ).sub
    (terminalCubicResidual_continuous_expGrowth β α s h z).1
  have hgT : HasExpGrowth T := hasExpGrowth_sub (terminalResidual_hasExpGrowth β α s h z hφ)
    (terminalCubicResidual_continuous_expGrowth β α s h z).2
  have hft : Continuous (scalarFourthTail f z) := hf.sub (scalarTaylorPolynomial_contDiff f 3 z).continuous
  have hgft : HasExpGrowth (scalarFourthTail f z) :=
    hasExpGrowth_sub hφ.hasExpGrowth (scalarTaylorPolynomial_hasExpGrowth f 3 z)
  have hF (i : Fin 3) : Continuous (F i) := by
    exact (hft.comp (continuous_apply i)).pow 2
  have hgF (i : Fin 3) : HasExpGrowth (F i) := by
    let L : Vec3 →L[ℝ] ℝ := ContinuousLinearMap.proj i
    have H := (hgft.compCLM L).pow 2
    simpa only [Function.comp_def, L, ContinuousLinearMap.proj_apply] using H
  have hQ : RiccatiAdmissible l Q := hA α a s h k z ha hh (hh₀.trans (min_le_right _ _))
    (by rw [abs_le]; constructor <;> linarith [hk.1, hk.2])
    ((scalarData_jet_le D (by norm_num) le_rfl ht z).trans (by dsimp only [B]; linarith))
  have hp (y : Vec3) : T y ^ 2 ≤ 3 * ∑ i : Fin 3, F i y := by
    dsimp only [T]
    rw [terminalResidual_sub_cubic_eq]
    change (∑ i : Fin 3, scalarFourthTail f z (y i)) ^ 2 ≤ 3 * ∑ i : Fin 3, F i y
    simp only [F, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    nlinarith [sq_nonneg (scalarFourthTail f z (y 0) - scalarFourthTail f z (y 1)),
      sq_nonneg (scalarFourthTail f z (y 0) - scalarFourthTail f z (y 2)),
      sq_nonneg (scalarFourthTail f z (y 1) - scalarFourthTail f z (y 2))]
  have H := quadraticFirst_mono l Q hQ (F := fun y => T y ^ 2)
    (G := fun y => 3 * ∑ i : Fin 3, F i y) (hT.pow 2) (hgT.pow 2)
    (continuous_const.mul (continuous_finsetSum _ (fun i _ => hF i)))
    ((HasExpGrowth.const 3).mul (HasExpGrowth.finsetSum Finset.univ F (fun i _ => hgF i))) hp (fun _ => z)
  rw [quadraticFirst_const_mul, quadraticFirst_finsetSum Finset.univ l Q hQ F
    (fun i _ => hF i) (fun i _ => hgF i)] at H
  have HC (i : Fin 3) : quadraticFirst l Q (F i) (fun _ => z) ≤ C * h ^ 4 := by
    obtain ⟨g₁, g₂, HG⟩ := HT a s h z ha hh (hh₀.trans (min_le_left _ _)) ht i
    exact (le_abs_self _).trans (HG k hk).2.2.1
  calc
    _ ≤ 3 * ∑ i : Fin 3, quadraticFirst l Q (F i) (fun _ => z) := H
    _ ≤ 3 * ∑ _ : Fin 3, C * h ^ 4 := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i _ => HC i)) (by norm_num)
    _ = _ := by simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]; ring1

set_option maxHeartbeats 800000 in
theorem scalarData_terminalCubicSquare_le {β : ℝ} (D : ScalarData β) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ a s h z : ℝ,
      a ∈ Ioc (0 : ℝ) 1 → 0 ≤ h → h ≤ h₀ → s + 4 * h ∈ Icc (0 : ℝ) 1 →
      ∀ k ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
        quadraticFirst (frozenSchedule β a (1 / 2) h k)
          (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) s h z)
          (fun y => terminalCubicResidual β (cdf (D.μ : Measure ℝ)) s h z y ^ 2)
          (fun _ => z) ≤ C * h ^ 3 := by
  let B := scalarTerminalJetBound D 3 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 3]
  obtain ⟨M, η, hM, hη, _, HP⟩ := frozenGaussianParameter_uniform_control β B hB
  obtain ⟨ξ, hξ, hA⟩ := terminalTaylorQuadratic_uniform_admissible β B hB
  let J := ∫ g, gaussianPolynomialWeight 6 g ∂gaussianReal 0 1
  have hJ : 0 ≤ J := integral_nonneg (fun _ => by unfold gaussianPolynomialWeight; positivity)
  refine ⟨B ^ 2 * M ^ 6 * (J + 1), min η ξ, by positivity, by positivity, ?_⟩
  intro a s h z ha hh hh₀ ht k hk
  let α := cdf (D.μ : Measure ℝ)
  let Q := terminalTaylorQuadratic β α s h z
  let l := frozenSchedule β a (1 / 2) h k
  let w := jet β α 3 (s + 4 * h) z
  let u := jet β α 1 (s + 4 * h) z
  let χ := jet β α 2 (s + 4 * h) z
  let F (i : Fin 3) : Vec3 → ℝ := fun y => (y i - z) ^ 6
  have hj (j : ℕ) (hj₁ : 1 ≤ j) (hj₃ : j ≤ 3) : |jet β α j (s + 4 * h) z| ≤ B :=
    (scalarData_jet_le D hj₁ hj₃ ht z).trans (by dsimp only [B]; linarith)
  have hw : |w| ≤ B := hj 3 (by norm_num) le_rfl
  have hk' : |k| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hk.1, hk.2]
  have hQ : RiccatiAdmissible l Q := hA α a s h k z ha hh (hh₀.trans (min_le_right _ _)) hk'
    (hj 2 (by norm_num) (by norm_num))
  have hF (i : Fin 3) : Continuous (F i) := by unfold F; fun_prop
  have hgF (i : Fin 3) : HasExpGrowth (F i) := by
    let L : Vec3 →L[ℝ] ℝ := ContinuousLinearMap.proj i
    have H : HasExpGrowth (fun y : Vec3 => y i - z) := by
      simpa only [L, ContinuousLinearMap.proj_apply] using
        hasExpGrowth_sub (HasExpGrowth.linear L) (HasExpGrowth.const z)
    exact H.pow 6
  have hK := terminalCubicResidual_continuous_expGrowth β α s h z
  have hp (y : Vec3) : terminalCubicResidual β α s h z y ^ 2 ≤ B ^ 2 / 12 * ∑ i : Fin 3, F i y := by
    have hsum : (∑ i : Fin 3, (y i - z) ^ 3) ^ 2 ≤ 3 * ∑ i : Fin 3, F i y := by
      simp only [F, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
        Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
      nlinarith [sq_nonneg ((y 0 - z) ^ 3 - (y 1 - z) ^ 3),
        sq_nonneg ((y 0 - z) ^ 3 - (y 2 - z) ^ 3),
        sq_nonneg ((y 1 - z) ^ 3 - (y 2 - z) ^ 3)]
    have hw₂ : w ^ 2 ≤ B ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg w) hw 2
    have hsum₀ : 0 ≤ ∑ i : Fin 3, F i y := Finset.sum_nonneg (fun i _ => by unfold F; positivity)
    calc
      _ = (w / 6) ^ 2 * (∑ i : Fin 3, (y i - z) ^ 3) ^ 2 := by
        simp only [terminalCubicResidual, w, Fin.sum_univ_succ]
        ring1
      _ ≤ (w / 6) ^ 2 * (3 * ∑ i : Fin 3, F i y) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = w ^ 2 / 12 * ∑ i : Fin 3, F i y := by ring1
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hsum₀
  have H := quadraticFirst_mono l Q hQ (F := fun y => terminalCubicResidual β α s h z y ^ 2)
    (G := fun y => B ^ 2 / 12 * ∑ i : Fin 3, F i y) (hK.1.pow 2) (hK.2.pow 2)
    (continuous_const.mul (continuous_finsetSum _ (fun i _ => hF i)))
    ((HasExpGrowth.const (B ^ 2 / 12)).mul
      (HasExpGrowth.finsetSum Finset.univ F (fun i _ => hgF i))) hp (fun _ => z)
  rw [quadraticFirst_const_mul, quadraticFirst_finsetSum Finset.univ l Q hQ F
    (fun i _ => hF i) (fun i _ => hgF i)] at H
  have HC (i : Fin 3) : quadraticFirst l Q (F i) (fun _ => z) ≤ M ^ 6 * h ^ 3 * J := by
    have Hpar := HP a u χ h z ha (hj 1 le_rfl (by norm_num))
      (hj 2 (by norm_num) (by norm_num)) hh (hh₀.trans (min_le_left _ _)) i k hk'
    have hi (m : ℝ) (v : ℝ≥0) : Integrable (fun y : ℝ => (y - z) ^ 6) (gaussianReal m v) := by
      have hid : HasExpGrowth (fun y : ℝ => y) := HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)
      exact ((hasExpGrowth_sub hid (HasExpGrowth.const z)).pow 6).integrable_gaussianMeasure (by fun_prop)
    have HE := frozenSchedule_coordinate_standardGaussian β a h k (Phi β α (s + 4 * h) z) u χ z
      (ne_of_gt ha.1) hh hk' hQ Hpar.1 (fun y : ℝ => (y - z) ^ 6) (by fun_prop) hi i
    change quadraticFirst l Q (F i) (fun _ => z) = _ at HE
    rw [HE]
    have hb (g : ℝ) : |(frozenGaussianMean β a u χ h z + frozenGaussianScale β a χ h i k * g - z) ^ 6| ≤
        (M ^ 6 * Real.sqrt h ^ 6) * gaussianPolynomialWeight 6 g := by
      have Haff : |frozenGaussianMean β a u χ h z + frozenGaussianScale β a χ h i k * g - z| ≤
          M * Real.sqrt h * (1 + |g|) := by
        calc
          _ = |(frozenGaussianMean β a u χ h z - z) + frozenGaussianScale β a χ h i k * g| := by congr 1; ring1
          _ ≤ |frozenGaussianMean β a u χ h z - z| + |frozenGaussianScale β a χ h i k| * |g| :=
            (abs_add_le _ _).trans_eq (by rw [abs_mul])
          _ ≤ M * Real.sqrt h + (M * Real.sqrt h) * |g| :=
            add_le_add Hpar.2.1 (mul_le_mul_of_nonneg_right Hpar.2.2.1 (abs_nonneg g))
          _ = _ := by ring1
      rw [abs_pow]
      calc
        _ ≤ (M * Real.sqrt h * (1 + |g|)) ^ 6 := pow_le_pow_left₀ (abs_nonneg _) Haff 6
        _ = _ := by unfold gaussianPolynomialWeight; ring1
    have HG := gaussian_integral_abs_le_polynomial hb
    have hs : Real.sqrt h ^ 6 = h ^ 3 := by
      rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, Real.sq_sqrt hh]
    exact (le_abs_self _).trans (by simpa only [hs, J] using HG)
  calc
    _ ≤ B ^ 2 / 12 * ∑ i : Fin 3, quadraticFirst l Q (F i) (fun _ => z) := H
    _ ≤ B ^ 2 / 12 * ∑ _ : Fin 3, M ^ 6 * h ^ 3 * J := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i _ => HC i)) (by positivity)
    _ ≤ _ := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      have HS : 0 ≤ B ^ 2 * M ^ 6 * h ^ 3 := by positivity
      nlinarith [mul_nonneg HS hJ]

theorem scalarData_conditional_cubic_tail_square_le {β : ℝ} (D : ScalarData β) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ a s h z : ℝ,
      a ∈ Ioc (0 : ℝ) 1 → 0 ≤ h → h ≤ h₀ → s + 4 * h ∈ Icc (0 : ℝ) 1 →
      ∀ k ∈ Icc (-(1 / 4) : ℝ) (1 / 4), ∀ l t : List (ℝ × Vec3),
      l ++ t = frozenSchedule β a (1 / 2) h k →
      let Q := terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) s h z
      quadraticFirst l (riccatiRecursion t Q)
        (fun y => quadraticFirst t Q (terminalCubicResidual β (cdf (D.μ : Measure ℝ)) s h z) y ^ 2)
        (fun _ => z) ≤ C * h ^ 3 ∧
      quadraticFirst l (riccatiRecursion t Q)
        (fun y => quadraticFirst t Q
          (fun x => terminalResidual β (cdf (D.μ : Measure ℝ)) s h z x -
            terminalCubicResidual β (cdf (D.μ : Measure ℝ)) s h z x) y ^ 2)
        (fun _ => z) ≤ C * h ^ 4 := by
  obtain ⟨C₁, η, hC₁, hη, HC⟩ := scalarData_terminalCubicSquare_le D
  obtain ⟨C₂, ζ, hC₂, hζ, HT⟩ := scalarData_terminalTailSquare_le D
  let B := scalarTerminalJetBound D 2 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 2]
  obtain ⟨ξ, hξ, hA⟩ := terminalTaylorQuadratic_uniform_admissible β B hB
  refine ⟨C₁ + C₂, min η (min ζ ξ), add_pos hC₁ hC₂, by positivity, ?_⟩
  intro a s h z ha hh hh₀ ht k hk l t he
  dsimp only
  let α : ℝ → ℝ := cdf (D.μ : Measure ℝ)
  let Q := terminalTaylorQuadratic β α s h z
  have hhη := hh₀.trans (min_le_left _ _)
  have hhζ := (hh₀.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhξ := (hh₀.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hQ : RiccatiAdmissible (l ++ t) Q := by
    rw [he]
    exact hA α a s h k z ha hh hhξ
      (by rw [abs_le]; constructor <;> linarith [hk.1, hk.2])
      ((scalarData_jet_le D (by norm_num) le_rfl ht z).trans (by dsimp only [B]; linarith))
  have hK := terminalCubicResidual_continuous_expGrowth β α s h z
  have hφ := scalarData_phi_regular D ht
  have hc : Continuous (fun y => terminalResidual β α s h z y - terminalCubicResidual β α s h z y) :=
    (terminalResidual_continuous β α s h z hφ).sub hK.1
  have hg : HasExpGrowth (fun y => terminalResidual β α s h z y - terminalCubicResidual β α s h z y) :=
    hasExpGrowth_sub (terminalResidual_hasExpGrowth β α s h z hφ) hK.2
  have H₁ := quadraticFirst_conditional_square_le l t Q hQ hK.1 hK.2 (fun _ => z)
  have H₂ := quadraticFirst_conditional_square_le l t Q hQ hc hg (fun _ => z)
  rw [he] at H₁ H₂
  refine ⟨H₁.trans ((HC a s h z ha hh hhη ht k hk).trans ?_),
    H₂.trans ((HT a s h z ha hh hhζ ht k hk).trans ?_)⟩
  · nlinarith [mul_nonneg hC₂.le (pow_nonneg hh 3)]
  · nlinarith [mul_nonneg hC₁.le (pow_nonneg hh 4)]

def wickTailCoefficientError (β : ℝ) (α : ℝ → ℝ) (a s h z k : ℝ) : ℝ :=
  ((frozenSecondMoment β α a s h k z -
      quadraticSecond (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z)
        (terminalCubicResidual β α s h z) (fun _ => z)) -
    (frozenSecondMoment β α a s h 0 z -
      quadraticSecond (frozenSchedule β a (1 / 2) h 0) (terminalTaylorQuadratic β α s h z)
        (terminalCubicResidual β α s h z) (fun _ => z))) / 2

theorem wickCoefficientError_split (β : ℝ) (α : ℝ → ℝ) (a s h z k : ℝ) :
    wickCoefficientError β α a s h z k =
      cubicWickCoefficientError β α a s h z k + wickTailCoefficientError β α a s h z k := by
  unfold wickCoefficientError cubicWickCoefficientError wickTailCoefficientError
  ring1

end SKBarriers2.Corner
