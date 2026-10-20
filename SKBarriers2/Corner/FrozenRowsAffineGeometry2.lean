module

public import SKBarriers2.Corner.FrozenRowsAffineGeometry

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set MeasureTheory ProbabilityTheory Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def gaussianPathLinearCLM (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) : Vec3 →L[ℝ] Vec3 :=
  (gaussianPathLinearMap l Q).toContinuousLinearMap

theorem gaussianPathLinearCLM_apply (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (x : Vec3) :
    gaussianPathLinearCLM l Q x = gaussianPathLinear l Q x :=
  gaussianPathLinearMap_apply l Q x

theorem gaussianPathLinearCLM_cons (u : ℝ × Vec3) (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) :
    gaussianPathLinearCLM (u :: l) Q =
      (gaussianPathLinearCLM l Q).comp (quadraticMeanLinear (riccatiRecursion l Q) u.1 u.2) := by
  ext x
  rfl

def gaussianPathLinearScaleFactor : List (ℝ × Vec3) → QuadraticTerminal → ℝ → (Vec3 →L[ℝ] Vec3)
  | [], _, _ => 0
  | u :: l, Q, ρ =>
      let R := riccatiRecursion (scaleDirections ρ l) Q
      let H := quadraticMeanCorrection R u.1 (R.precision u.1 (ρ • u.2)) u.2
      let T := gaussianPathLinearScaleFactor l Q ρ
      T + H + ρ ^ 2 • (T.comp H)

theorem gaussianPathLinearCLM_scale_factor (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (ρ : ℝ) :
    gaussianPathLinearCLM (scaleDirections ρ l) Q = ContinuousLinearMap.id ℝ Vec3 +
      ρ ^ 2 • gaussianPathLinearScaleFactor l Q ρ := by
  induction l with
  | nil =>
    ext x
    simp only [scaleDirections, List.map_nil, gaussianPathLinearScaleFactor,
      smul_zero, add_zero]
    rfl
  | cons u l ih =>
    simp only [scaleDirections, List.map_cons, gaussianPathLinearCLM_cons]
    rw [quadraticMeanLinear_scale_factor]
    change (gaussianPathLinearCLM (scaleDirections ρ l) Q).comp
      (ContinuousLinearMap.id ℝ Vec3 + ρ ^ 2 • _) = _
    rw [ih]
    ext x i
    simp only [gaussianPathLinearScaleFactor, scaleDirections, ContinuousLinearMap.comp_apply,
      add_apply, smul_apply, ContinuousLinearMap.id_apply, map_add, map_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

namespace QuadraticFamilyContDiffAt
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {Q : P → QuadraticTerminal} {p : P}

theorem meanCorrection (hQ : QuadraticFamilyContDiffAt Q p)
    {m D : P → ℝ} {w : P → Vec3}
    (hm : ContDiffAt ℝ ∞ m p) (hD : ContDiffAt ℝ ∞ D p) (hD0 : D p ≠ 0)
    (hw : ∀ i, ContDiffAt ℝ ∞ (fun q => w q i) p) :
    ContDiffAt ℝ ∞ (fun q => quadraticMeanCorrection (Q q) (m q) (D q) (w q)) p := by
  change ContDiffWithinAt ℝ ∞ _ univ p
  apply contDiffWithinAt_clm_apply.mpr
  intro x
  apply contDiffWithinAt_pi.mpr
  intro i
  have H : ContDiffAt ℝ ∞
      (fun q => (m q / D q * (∑ a : Fin 3, x a * (Q q).hessianDirection (w q) a)) * w q i) p :=
    ((hm.div hD hD0).mul (ContDiffAt.sum (fun a _ =>
      contDiffAt_const.mul (hQ.hessianDirection hw a)))).mul (hw i)
  convert H.contDiffWithinAt using 1
  funext q
  simp [quadraticMeanCorrection, Fin.sum_univ_succ]
  ring

end QuadraticFamilyContDiffAt

theorem gaussianPathLinearScaleFactor_contDiffAt {P ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (l : List ι) (m : ι → P → ℝ) (w : ι → P → Vec3)
    (Q : P → QuadraticTerminal) (ρ : P → ℝ) {p : P}
    (hm : ∀ j ∈ l, ContDiffAt ℝ ∞ (m j) p)
    (hw : ∀ j ∈ l, ∀ i, ContDiffAt ℝ ∞ (fun q => w j q i) p)
    (hQ : QuadraticFamilyContDiffAt Q p) (hρ : ContDiffAt ℝ ∞ ρ p)
    (hA : RiccatiAdmissible (l.map (fun j => (m j p, ρ p • w j p))) (Q p)) :
    ContDiffAt ℝ ∞ (fun q => gaussianPathLinearScaleFactor
      (l.map (fun j => (m j q, w j q))) (Q q) (ρ q)) p := by
  induction l with
  | nil => exact contDiffAt_const
  | cons j l ih =>
    have hwt (i : ι) (hi : i ∈ j :: l) (a : Fin 3) :
        ContDiffAt ℝ ∞ (fun q => (ρ q • w i q) a) p :=
      hρ.mul (hw i hi a)
    have hR := riccatiRecursion_coefficients_contDiffAt l m (fun j q => ρ q • w j q) Q
      (fun i hi => hm i (List.mem_cons_of_mem _ hi))
      (fun i hi => hwt i (List.mem_cons_of_mem _ hi)) hQ hA.1
    have hD := hR.precision (hm j List.mem_cons_self) (hwt j List.mem_cons_self)
    have hH := hR.meanCorrection (hm j List.mem_cons_self) hD hA.2.2.ne'
      (hw j List.mem_cons_self)
    have hT := ih (fun i hi => hm i (List.mem_cons_of_mem _ hi))
      (fun i hi => hw i (List.mem_cons_of_mem _ hi)) hA.1
    simpa only [List.map_cons, gaussianPathLinearScaleFactor, scaleDirections,
      List.map_map, Function.comp_def, Pi.smul_apply] using
      (hT.add hH).add ((hρ.pow 2).fun_smul (hT.clm_comp hH))

theorem CenteredQuadraticCoefficients.pathLinear {c : Vec3} {Q R : QuadraticTerminal}
    (H : CenteredQuadraticCoefficients c Q R) (l : List (ℝ × Vec3)) :
    gaussianPathLinearCLM l Q = gaussianPathLinearCLM l R := by
  induction l with
  | nil => rfl
  | cons u l ih =>
    rw [gaussianPathLinearCLM_cons, gaussianPathLinearCLM_cons, ih, (H.recursion l).meanLinear]

def frozenAffinePathLabels (n : ℕ) : List (Fin 12) := (List.finRange 12).drop n

def frozenAffinePathFactor (β : ℝ) (n : ℕ) (p : FrozenGeometryParameter) : Vec3 →L[ℝ] Vec3 :=
  gaussianPathLinearScaleFactor ((frozenAffinePathLabels n).map
    (fun j => (frozenGeometryMass j p, frozenUnitDirection β p.2 j))) (frozenGeometryQuadratic p) p.1.2

private theorem positivePrecisions_admissible (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hP : NoisePrecisionsPositive l Q) (hm : ∀ u ∈ l, u.1 ≠ 0) : RiccatiAdmissible l Q := by
  induction l with
  | nil => trivial
  | cons u l ih =>
    exact ⟨ih (fun D hD => hP D (List.mem_cons_of_mem _ hD))
      (fun v hv => hm v (List.mem_cons_of_mem _ hv)), hm u List.mem_cons_self,
      hP _ List.mem_cons_self⟩

theorem frozenAffinePath_admissible (β : ℝ) (n : ℕ) {p : FrozenGeometryParameter}
    (hp : p ∈ frozenGeometryDomain β) :
    RiccatiAdmissible ((frozenAffinePathLabels n).map
      (fun j => (frozenGeometryMass j p, frozenGeometryDirection β j p))) (frozenGeometryQuadratic p) := by
  have hfull : RiccatiAdmissible (frozenGeometrySchedule β p) (frozenGeometryQuadratic p) := by
    apply positivePrecisions_admissible _ _ hp.2
    intro u hu
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hu
    exact mul_ne_zero hp.1.2 (by fin_cases j <;> norm_num [frozenUnitMass])
  have H := riccatiAdmissible_suffix ((frozenGeometrySchedule β p).take n)
    ((frozenGeometrySchedule β p).drop n) (frozenGeometryQuadratic p)
      (by simpa only [List.take_append_drop] using hfull)
  simpa only [frozenGeometrySchedule, frozenAffinePathLabels, List.map_drop] using H

theorem frozenAffinePathFactor_contDiffOn (β : ℝ) (n : ℕ) :
    ContDiffOn ℝ ∞ (frozenAffinePathFactor β n) (frozenGeometryDomain β) := by
  intro p hp
  apply (gaussianPathLinearScaleFactor_contDiffAt (frozenAffinePathLabels n)
    frozenGeometryMass (fun j p => frozenUnitDirection β p.2 j) frozenGeometryQuadratic
    (fun p => p.1.2) ?_ ?_ (frozenGeometryQuadratic_contDiffAt p) (by fun_prop) ?_).contDiffWithinAt
  · intro j _
    unfold frozenGeometryMass
    fun_prop
  · intro j _ i
    exact (contDiffAt_pi.mp ((frozenUnitDirection_contDiffAt_k β hp.1.1 j).comp p contDiffAt_snd)) i
  · exact frozenAffinePath_admissible β n hp

theorem frozenAffinePath_uniform_jets (β a₀ B : ℝ) (ha₀ : 0 < a₀) :
    ∃ δ C : ℝ, 0 < δ ∧ 1 ≤ C ∧
      ∀ b ∈ frozenGeometryBaseBox a₀ B, ∀ ρ ∈ Icc (-δ) δ,
        ∀ k ∈ Icc (-(1 / 2) : ℝ) (1 / 2), ∀ n : Fin 13, ∀ i : Fin 3,
          ‖iteratedDeriv i.val (fun t => frozenAffinePathFactor β n.val ((b, ρ), t)) k‖ ≤ C := by
  classical
  obtain ⟨δ, hδ, hδU⟩ := frozenGeometry_uniform_domain β a₀ B ha₀
  let K := (frozenGeometryBaseBox a₀ B ×ˢ Icc (-δ) δ) ×ˢ Icc (-(1 / 2) : ℝ) (1 / 2)
  have hK : IsCompact K :=
    ((isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod isCompact_Icc).prod isCompact_Icc
  have hKU : K ⊆ frozenGeometryDomain β := by
    rintro ⟨⟨b, ρ⟩, k⟩ ⟨⟨hb, hρ⟩, hk⟩
    exact hδU b hb ρ hρ k hk
  have hU := frozenGeometryDomain_isOpen β
  choose S hS HS using fun n : Fin 13 => SKBarriers2.compact_affine_vertical_bounds hK hU
    (frozenAffinePathFactor_contDiffOn β n.val) hKU
  let C := 1 + ∑ n : Fin 13, S n
  have hC : 1 ≤ C := by
    have H := Finset.sum_nonneg (fun n (_ : n ∈ (Finset.univ : Finset (Fin 13))) => (hS n).le)
    dsimp only [C]
    linarith
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro b hb ρ hρ k hk n i
  have hpK : ((b, ρ), k) ∈ K := ⟨⟨hb, hρ⟩, hk⟩
  have hpU := hKU hpK
  have H := HS n ((b, ρ), k) hpK
  have hSC : S n ≤ C := by
    have H := Finset.single_le_sum (f := S) (fun j _ => (hS j).le) (Finset.mem_univ n)
    dsimp only [C]
    linarith
  fin_cases i
  · exact H.1.trans hSC
  · simpa only [iteratedDeriv_one, H.2.2.2.1.deriv] using H.2.1.trans hSC
  · rw [SKBarriers2.affineVerticalDerivative_two_eq_iteratedDeriv hU
      (frozenAffinePathFactor_contDiffOn β n.val) hpU]
    exact H.2.2.1.trans hSC

theorem frozenRows_path_linear_factor (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (hh : 0 < h) (n : ℕ) (k : ℝ) :
    let base := frozenAffineScalarBase β α a s h z ε
    let ρ := Real.sqrt h
    gaussianPathLinearCLM ((frozenSchedule β a (1 / 2) h k).drop n)
        ((terminalTaylorQuadratic β α s h z).scale (1 - ε)) =
      ContinuousLinearMap.id ℝ Vec3 + ρ ^ 2 • frozenAffinePathFactor β n ((base, ρ), k) := by
  let base := frozenAffineScalarBase β α a s h z ε
  let ρ := Real.sqrt h
  let p : FrozenGeometryParameter := ((base, ρ), k)
  let t := (frozenSchedule β a (1 / 2) h k).drop n
  let unit := (frozenAffinePathLabels n).map
    (fun j => (frozenGeometryMass j p, frozenUnitDirection β k j))
  have H := terminalTaylorQuadratic_centeredCoefficients β α s h z ε
  have hQ : separableTaylorQuadratic 0 ((1 - ε) * jet β α 1 (s + 4 * h) z)
      ((1 - ε) * jet β α 2 (s + 4 * h) z) 0 = frozenGeometryQuadratic p := rfl
  rw [hQ] at H
  have ht : t = scaleDirections ρ unit := by
    dsimp only [t]
    rw [frozenSchedule_eq_labelled β a h k hh.le, ← List.map_drop]
    simp only [scaleDirections, unit, List.map_map, Function.comp_def]
    rfl
  change gaussianPathLinearCLM t _ = _
  rw [H.pathLinear t, ht, gaussianPathLinearCLM_scale_factor]
  rfl

theorem scalarData_frozenRows_path_linear_geometry {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ 1 ≤ C ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ n : Fin 13, ∀ k : ℝ, |k| ≤ 1 / 2 →
        let α := cdf (D.μ : Measure ℝ)
        let a := α (r - h)
        let A := fun t => gaussianPathLinearCLM ((frozenSchedule β a (1 / 2) h t).drop n.val)
          ((terminalTaylorQuadratic β α (r - h) h z).scale (1 - ε))
        ‖A k‖ ≤ C ∧ ∀ i : Fin 2, ‖iteratedDeriv (i.val + 1) A k‖ ≤ C * h := by
  let a₀ := cdf (D.μ : Measure ℝ) (l / 2)
  let B := scalarTerminalJetBound D 2 + 1
  have ha₀ : 0 < a₀ := scalarData_cdf_pos_of_pos D (by positivity)
  obtain ⟨δ, K, hδ, hK, HK⟩ := frozenAffinePath_uniform_jets β a₀ B ha₀
  let h₀ := min (δ ^ 2) (min 1 (min (l / 2) ((D.q - u) / 6)))
  refine ⟨h₀, K + 2, lt_min (sq_pos_of_pos hδ)
    (lt_min (by norm_num) (lt_min (by positivity) (by positivity))), by linarith, ?_⟩
  intro r hr h hh hhsmall z ε hε n k hk
  let α := cdf (D.μ : Measure ℝ)
  let a := α (r - h)
  let ρ := Real.sqrt h
  let base := frozenAffineScalarBase β α a (r - h) h z ε
  have hhd : h ≤ δ ^ 2 := hhsmall.trans (min_le_left _ _)
  have hh₁ : h ≤ 1 := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhl : h ≤ l / 2 :=
    ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 6 :=
    ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have htime : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith [hr.1]
    · linarith [hr.2, D.q_mem.2]
  have hρ : 0 < ρ := Real.sqrt_pos.mpr hh
  have hρδ : ρ ≤ δ := (Real.sqrt_le_iff).mpr ⟨hδ.le, hhd⟩
  have heh : ρ ^ 2 = h := Real.sq_sqrt hh.le
  have heps : |1 - ε| ≤ 1 := by rw [abs_of_nonneg (by linarith [hε.2])]; linarith [hε.1]
  have hb : base ∈ frozenGeometryBaseBox a₀ B := by
    refine ⟨⟨?_, cdf_le_one _ _⟩, ?_, ?_⟩
    · exact monotone_cdf (D.μ : Measure ℝ) (by linarith [hr.1])
    · apply abs_le.mp
      change |(1 - ε) * jet β α 1 ((r - h) + 4 * h) z| ≤ B
      rw [abs_mul]
      apply (mul_le_mul heps (scalarData_jet_le D (r := 2) (by norm_num) (by norm_num) htime z)
        (abs_nonneg _) (by norm_num)).trans
      dsimp only [B]
      linarith
    · apply abs_le.mp
      change |(1 - ε) * jet β α 2 ((r - h) + 4 * h) z| ≤ B
      rw [abs_mul]
      apply (mul_le_mul heps (scalarData_jet_le D (r := 2) (by norm_num) (by norm_num) htime z)
        (abs_nonneg _) (by norm_num)).trans
      dsimp only [B]
      linarith
  have hρI : ρ ∈ Icc (-δ) δ := ⟨by linarith, hρδ⟩
  have hkI : k ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := abs_le.mp hk
  have HF := HK base hb ρ hρI k hkI n
  let A := fun t => gaussianPathLinearCLM ((frozenSchedule β a (1 / 2) h t).drop n.val)
    ((terminalTaylorQuadratic β α (r - h) h z).scale (1 - ε))
  have hA : A = fun t => ContinuousLinearMap.id ℝ Vec3 +
      ρ ^ 2 • frozenAffinePathFactor β n.val ((base, ρ), t) :=
    funext (fun t => frozenRows_path_linear_factor β α a (r - h) h z ε hh n.val t)
  change ‖A k‖ ≤ K + 2 ∧ ∀ i : Fin 2,
    ‖iteratedDeriv (i.val+1) A k‖ ≤ (K+2)*h
  rw [hA]
  constructor
  · calc
      _ ≤ ‖ContinuousLinearMap.id ℝ Vec3‖ + ‖ρ ^ 2 • frozenAffinePathFactor β n.val ((base, ρ), k)‖ := norm_add_le _ _
      _ ≤ 1 + h * K := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ρ), heh]
        exact add_le_add ContinuousLinearMap.norm_id_le (mul_le_mul_of_nonneg_left (HF 0) hh.le)
      _ ≤ K + 2 := by nlinarith [mul_le_of_le_one_left (by linarith : 0 ≤ K) hh₁]
  · intro i
    rw [iteratedDeriv_const_add (by omega), iteratedDeriv_fun_const_smul_field,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ρ), heh]
    exact (mul_le_mul_of_nonneg_left (HF ⟨i.val + 1, by omega⟩) hh.le).trans (by nlinarith)

end SKBarriers2.Corner
