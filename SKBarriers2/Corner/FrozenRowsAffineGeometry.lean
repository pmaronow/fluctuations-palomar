module

public import SKBarriers2.Corner.FrozenRowsGeometry
public import SKBarriers2.Corner.FrozenRowsMixed2

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set MeasureTheory ProbabilityTheory Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2
variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def affineVerticalDerivative (f : P × ℝ → F) (p : P × ℝ) : F :=
  fderiv ℝ f p (0, 1)

theorem affineVerticalDerivative_contDiffOn {f : P × ℝ → F} {U : Set (P × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (affineVerticalDerivative f) U :=
  (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

theorem affineVerticalDerivative_hasDerivAt {f : P × ℝ → F} {U : Set (P × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {p : P} {k : ℝ}
    (hx : (p, k) ∈ U) :
    HasDerivAt (fun t => f (p, t)) (affineVerticalDerivative f (p, k)) k := by
  have hline : HasDerivAt (fun t : ℝ => (p, t)) (0, 1) k :=
    (hasDerivAt_const k p).prodMk (hasDerivAt_id k)
  exact ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt k hline

theorem affineVerticalDerivative_two_eq_iteratedDeriv {f : P × ℝ → F} {U : Set (P × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {p : P} {k : ℝ}
    (hx : (p, k) ∈ U) :
    iteratedDeriv 2 (fun t => f (p, t)) k =
      affineVerticalDerivative (affineVerticalDerivative f) (p, k) := by
  have he : (fun t => deriv (fun s => f (p, s)) t) =ᶠ[𝓝 k]
      (fun t => affineVerticalDerivative f (p, t)) := by
    filter_upwards [((hU.preimage (continuous_const.prodMk continuous_id)).mem_nhds hx)] with t ht
    exact (affineVerticalDerivative_hasDerivAt hU hf ht).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, he.deriv_eq]
  exact (affineVerticalDerivative_hasDerivAt hU (affineVerticalDerivative_contDiffOn hU hf) hx).deriv

theorem compact_affine_vertical_bounds {f : P × ℝ → F} {K U : Set (P × ℝ)}
    (hK : IsCompact K) (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hKU : K ⊆ U) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ K,
      ‖f x‖ ≤ B ∧ ‖affineVerticalDerivative f x‖ ≤ B ∧
        ‖affineVerticalDerivative (affineVerticalDerivative f) x‖ ≤ B ∧
        HasDerivAt (fun t => f (x.1, t)) (affineVerticalDerivative f x) x.2 ∧
        HasDerivAt (fun t => affineVerticalDerivative f (x.1, t))
          (affineVerticalDerivative (affineVerticalDerivative f) x) x.2 := by
  have hf₁ := affineVerticalDerivative_contDiffOn hU hf
  have hf₂ := affineVerticalDerivative_contDiffOn hU hf₁
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn (hf.continuousOn.mono hKU)
  obtain ⟨B₁, hB₁⟩ := hK.exists_bound_of_continuousOn (hf₁.continuousOn.mono hKU)
  obtain ⟨B₂, hB₂⟩ := hK.exists_bound_of_continuousOn (hf₂.continuousOn.mono hKU)
  refine ⟨1 + |B₀| + |B₁| + |B₂|, by positivity, ?_⟩
  intro x hx
  refine ⟨?_, ?_, ?_, affineVerticalDerivative_hasDerivAt hU hf (hKU hx),
    affineVerticalDerivative_hasDerivAt hU hf₁ (hKU hx)⟩ <;>
    linarith [hB₀ x hx, hB₁ x hx, hB₂ x hx,
      le_abs_self B₀, le_abs_self B₁, le_abs_self B₂,
      abs_nonneg B₀, abs_nonneg B₁, abs_nonneg B₂]

end SKBarriers2

namespace SKBarriers2.Corner

structure CenteredQuadraticCoefficients (c : Vec3) (Q R : QuadraticTerminal) : Prop where
  hessian : ∀ i j, Q.hessian i j = R.hessian i j
  gradient : ∀ i, Q.slopeVector c i = R.linear i

namespace CenteredQuadraticCoefficients
variable {c : Vec3} {Q R : QuadraticTerminal}

theorem precision (H : CenteredQuadraticCoefficients c Q R) (m : ℝ) (v : Vec3) :
    Q.precision m v = R.precision m v := by
  simp only [QuadraticTerminal.precision, QuadraticTerminal.curvature,
    QuadraticTerminal.hessianDirection, H.hessian]

theorem slope (H : CenteredQuadraticCoefficients c Q R) (v : Vec3) :
    Q.slope v c = R.linearDirection v := by
  have he : Q.slope v c = ∑ i, Q.slopeVector c i * v i := by
    simp only [QuadraticTerminal.slope, QuadraticTerminal.slopeVector,
      QuadraticTerminal.linearDirection, QuadraticTerminal.hessianDirection, Fin.sum_univ_succ]
    ring
  simp only [he, H.gradient, QuadraticTerminal.linearDirection]

theorem meanLinear (H : CenteredQuadraticCoefficients c Q R) (m : ℝ) (v : Vec3) :
    quadraticMeanLinear Q m v = quadraticMeanLinear R m v := by
  ext x i
  change (quadraticNoiseLinear Q m v (x, 0)) i = (quadraticNoiseLinear R m v (x, 0)) i
  simp only [quadraticNoiseLinear, LinearMap.coe_mk, AddHom.coe_mk,
    H.precision, QuadraticTerminal.hessianDirection, H.hessian]

theorem update (H : CenteredQuadraticCoefficients c Q R) (m : ℝ) (v : Vec3) :
    CenteredQuadraticCoefficients c (Q.update m v) (R.update m v) := by
  have hd (i : Fin 3) : Q.hessianDirection v i = R.hessianDirection v i := by
    simp only [QuadraticTerminal.hessianDirection, H.hessian]
  refine ⟨?_, ?_⟩
  · intro i j
    simp only [QuadraticTerminal.update, H.hessian, H.precision, hd]
  · intro i
    have he : (Q.update m v).slopeVector c i = Q.slopeVector c i +
        m / Q.precision m v * Q.slope v c * Q.hessianDirection v i := by
      simp only [QuadraticTerminal.slopeVector, QuadraticTerminal.update,
        QuadraticTerminal.slope, QuadraticTerminal.linearDirection, Fin.sum_univ_succ]
      ring
    rw [he, H.gradient, H.precision, H.slope, hd]
    rfl

theorem recursion (H : CenteredQuadraticCoefficients c Q R) (l : List (ℝ × Vec3)) :
    CenteredQuadraticCoefficients c (riccatiRecursion l Q) (riccatiRecursion l R) := by
  induction l with
  | nil => exact H
  | cons u l ih => exact ih.update u.1 u.2

end CenteredQuadraticCoefficients

def quadraticMeanCorrection (Q : QuadraticTerminal) (m D : ℝ) (w : Vec3) : Vec3 →L[ℝ] Vec3 :=
  (m / D) • ((∑ i : Fin 3, Q.hessianDirection w i • tripleCoordinate i).smulRight w)

theorem quadraticMeanLinear_scale_factor (Q : QuadraticTerminal) (m ρ : ℝ) (w : Vec3) :
    quadraticMeanLinear Q m (ρ • w) = ContinuousLinearMap.id ℝ Vec3 +
      ρ ^ 2 • quadraticMeanCorrection Q m (Q.precision m (ρ • w)) w := by
  ext x i
  change (quadraticNoiseLinear Q m (ρ • w) (x, 0)) i = _
  simp only [quadraticNoiseLinear, LinearMap.coe_mk, AddHom.coe_mk,
    quadraticMeanCorrection, add_apply,
    ContinuousLinearMap.id_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, sum_apply,
    tripleCoordinate_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    QuadraticTerminal.hessianDirection, Fin.sum_univ_succ, mul_zero, add_zero]
  ring

theorem quadraticMean_center_scale_factor {Q R : QuadraticTerminal} (c w : Vec3)
    (H : CenteredQuadraticCoefficients c Q R) (m ρ : ℝ) :
    quadraticMeanLinear Q m (ρ • w) c + quadraticNoiseConstant Q m (ρ • w) - c =
      ρ ^ 2 • ((m * R.linearDirection w / R.precision m (ρ • w)) • w) := by
  rw [← quadraticMeanTransition_eq_affine]
  ext i
  simp only [quadraticMeanTransition, H.precision, H.slope,
    QuadraticTerminal.linearDirection, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Fin.sum_univ_succ]
  ring

def frozenAffineRiccati (β : ℝ) (j : Fin 12) (p : FrozenGeometryParameter) : QuadraticTerminal :=
  riccatiRecursion ((frozenGeometryLabels j.val).map
    (fun i => (frozenGeometryMass i p, frozenGeometryDirection β i p)))
    (frozenGeometryQuadratic p)

def frozenAffinePrecision (β : ℝ) (j : Fin 12) (p : FrozenGeometryParameter) : ℝ :=
  (frozenAffineRiccati β j p).precision (frozenGeometryMass j p) (frozenGeometryDirection β j p)

def frozenAffineLinearFactor (β : ℝ) (j : Fin 12) (p : FrozenGeometryParameter) : Vec3 →L[ℝ] Vec3 :=
  quadraticMeanCorrection (frozenAffineRiccati β j p) (frozenGeometryMass j p)
    (frozenAffinePrecision β j p) (frozenUnitDirection β p.2 j)

def frozenAffineShiftFactor (β : ℝ) (j : Fin 12) (p : FrozenGeometryParameter) : Vec3 :=
  (frozenGeometryMass j p * (frozenAffineRiccati β j p).linearDirection
    (frozenUnitDirection β p.2 j) / frozenAffinePrecision β j p) • frozenUnitDirection β p.2 j

def frozenAffineNoiseFactor (β : ℝ) (j : Fin 12) (p : FrozenGeometryParameter) : Vec3 :=
  Real.sqrt ((frozenAffinePrecision β j p)⁻¹) • frozenUnitDirection β p.2 j

private theorem positivePrecisions_suffix (l t : List (ℝ × Vec3))
    (Q : QuadraticTerminal) (h : NoisePrecisionsPositive (l ++ t) Q) :
    NoisePrecisionsPositive t Q := by
  induction l with
  | nil => exact h
  | cons u l ih =>
    apply ih
    intro D hD
    exact h D (List.mem_cons_of_mem _ hD)

theorem frozenAffinePrecision_pos (β : ℝ) (j : Fin 12) {p : FrozenGeometryParameter}
    (hp : p ∈ frozenGeometryDomain β) : 0 < frozenAffinePrecision β j p := by
  let full := frozenGeometrySchedule β p
  have hdrop : NoisePrecisionsPositive (full.drop j.val) (frozenGeometryQuadratic p) :=
    positivePrecisions_suffix (full.take j.val) (full.drop j.val) _
      (by simpa only [List.take_append_drop] using hp.2)
  have heq : full.drop j.val =
      (frozenGeometryMass j p, frozenGeometryDirection β j p) ::
        (frozenGeometryLabels j.val).map
          (fun i => (frozenGeometryMass i p, frozenGeometryDirection β i p)) := by
    change ((List.finRange 12).map _).drop j.val = _
    rw [← List.map_drop, List.drop_eq_getElem_cons (by simp)]
    simp [frozenGeometryLabels]
  rw [heq] at hdrop
  exact hdrop _ List.mem_cons_self

theorem frozenAffineRiccati_contDiffAt (β : ℝ) (j : Fin 12) {p : FrozenGeometryParameter}
    (hp : p ∈ frozenGeometryDomain β) :
    QuadraticFamilyContDiffAt (frozenAffineRiccati β j) p := by
  apply riccatiRecursion_coefficients_contDiffAt (frozenGeometryLabels j.val)
    frozenGeometryMass (frozenGeometryDirection β) frozenGeometryQuadratic
  · intro i _
    unfold frozenGeometryMass
    fun_prop
  · intro i _ a
    exact frozenGeometryDirection_contDiffAt β hp.1.1 i a
  · exact frozenGeometryQuadratic_contDiffAt p
  · exact frozenGeometry_suffix_admissible β hp j.val

theorem frozenAffine_factors_contDiffOn (β : ℝ) (j : Fin 12) :
    ContDiffOn ℝ ∞ (frozenAffineLinearFactor β j) (frozenGeometryDomain β) ∧
      ContDiffOn ℝ ∞ (frozenAffineShiftFactor β j) (frozenGeometryDomain β) ∧
      ContDiffOn ℝ ∞ (frozenAffineNoiseFactor β j) (frozenGeometryDomain β) := by
  have hR {p : FrozenGeometryParameter} (hp : p ∈ frozenGeometryDomain β) :=
    frozenAffineRiccati_contDiffAt β j hp
  have hm (p : FrozenGeometryParameter) : ContDiffAt ℝ ∞ (frozenGeometryMass j) p := by
    unfold frozenGeometryMass
    fun_prop
  have hw {p : FrozenGeometryParameter} (hp : p ∈ frozenGeometryDomain β) :
      ContDiffAt ℝ ∞ (fun q : FrozenGeometryParameter => frozenUnitDirection β q.2 j) p :=
    (frozenUnitDirection_contDiffAt_k β hp.1.1 j).comp p contDiffAt_snd
  have hD {p : FrozenGeometryParameter} (hp : p ∈ frozenGeometryDomain β) :
      ContDiffAt ℝ ∞ (frozenAffinePrecision β j) p :=
    (hR hp).precision (hm p) (frozenGeometryDirection_contDiffAt β hp.1.1 j)
  constructor
  · intro p hp
    apply contDiffWithinAt_clm_apply.mpr
    intro x
    apply contDiffWithinAt_pi.mpr
    intro i
    have hscalar : ContDiffAt ℝ ∞
        (fun q : FrozenGeometryParameter => frozenGeometryMass j q / frozenAffinePrecision β j q *
          (∑ a : Fin 3, x a * (frozenAffineRiccati β j q).hessianDirection
            (frozenUnitDirection β q.2 j) a) * frozenUnitDirection β q.2 j i) p := by
      exact (((hm p).div (hD hp) (frozenAffinePrecision_pos β j hp).ne').mul
        (ContDiffAt.sum (fun a _ => (contDiffAt_const.mul
          ((hR hp).hessianDirection (contDiffAt_pi.mp (hw hp)) a))))).mul
            (contDiffAt_pi.mp (hw hp) i)
    convert hscalar.contDiffWithinAt using 1
    funext q
    simp [frozenAffineLinearFactor, quadraticMeanCorrection, Fin.sum_univ_succ]
    ring
  constructor
  · intro p hp
    apply (contDiffAt_pi.mpr ?_).contDiffWithinAt
    intro i
    exact ((((hm p).mul ((hR hp).linearDirection (contDiffAt_pi.mp (hw hp)))).div
      (hD hp) (frozenAffinePrecision_pos β j hp).ne').mul (contDiffAt_pi.mp (hw hp) i))
  · intro p hp
    apply (contDiffAt_pi.mpr ?_).contDiffWithinAt
    intro i
    exact (((hD hp).inv (frozenAffinePrecision_pos β j hp).ne').sqrt
      (inv_pos.mpr (frozenAffinePrecision_pos β j hp)).ne').mul
        (contDiffAt_pi.mp (hw hp) i)

theorem frozenAffine_uniform_factor_jets (β a₀ B : ℝ) (ha₀ : 0 < a₀) :
    ∃ δ C : ℝ, 0 < δ ∧ 1 ≤ C ∧
      ∀ b ∈ frozenGeometryBaseBox a₀ B, ∀ ρ ∈ Icc (-δ) δ,
        ∀ k ∈ Icc (-(1 / 2) : ℝ) (1 / 2), ∀ j : Fin 12, ∀ i : Fin 3,
          ‖iteratedDeriv i.val (fun t => frozenAffineLinearFactor β j ((b, ρ), t)) k‖ ≤ C ∧
          ‖iteratedDeriv i.val (fun t => frozenAffineShiftFactor β j ((b, ρ), t)) k‖ ≤ C ∧
          ‖iteratedDeriv i.val (fun t => frozenAffineNoiseFactor β j ((b, ρ), t)) k‖ ≤ C := by
  classical
  obtain ⟨δ, hδ, hδU⟩ := frozenGeometry_uniform_domain β a₀ B ha₀
  let K := (frozenGeometryBaseBox a₀ B ×ˢ Icc (-δ) δ) ×ˢ Icc (-(1 / 2) : ℝ) (1 / 2)
  have hK : IsCompact K :=
    ((isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod isCompact_Icc).prod isCompact_Icc
  have hKU : K ⊆ frozenGeometryDomain β := by
    rintro ⟨⟨b, ρ⟩, k⟩ ⟨⟨hb, hρ⟩, hk⟩
    exact hδU b hb ρ hρ k hk
  have hU := frozenGeometryDomain_isOpen β
  choose L hL HL using fun j : Fin 12 => SKBarriers2.compact_affine_vertical_bounds
    hK hU (frozenAffine_factors_contDiffOn β j).1 hKU
  choose S hS HS using fun j : Fin 12 => SKBarriers2.compact_affine_vertical_bounds
    hK hU (frozenAffine_factors_contDiffOn β j).2.1 hKU
  choose N hN HN using fun j : Fin 12 => SKBarriers2.compact_affine_vertical_bounds
    hK hU (frozenAffine_factors_contDiffOn β j).2.2 hKU
  let C := 1 + ∑ j : Fin 12, (L j + S j + N j)
  have hC : 1 ≤ C := by
    have H : 0 ≤ ∑ j : Fin 12, (L j + S j + N j) :=
      Finset.sum_nonneg (fun j _ => by linarith [hL j, hS j, hN j])
    dsimp only [C]
    linarith
  have hbudget (j : Fin 12) : L j ≤ C ∧ S j ≤ C ∧ N j ≤ C := by
    have H := Finset.single_le_sum
      (f := fun j => L j + S j + N j)
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin 12))) => by linarith [hL j, hS j, hN j])
      (Finset.mem_univ j)
    dsimp only [C]
    constructor
    · linarith [hS j, hN j]
    constructor <;> linarith [hL j, hS j, hN j]
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro b hb ρ hρ k hk j i
  have hpK : ((b, ρ), k) ∈ K := ⟨⟨hb, hρ⟩, hk⟩
  have hpU := hKU hpK
  have hLj := HL j ((b, ρ), k) hpK
  have hSj := HS j ((b, ρ), k) hpK
  have hNj := HN j ((b, ρ), k) hpK
  fin_cases i
  · exact ⟨hLj.1.trans (hbudget j).1, hSj.1.trans (hbudget j).2.1, hNj.1.trans (hbudget j).2.2⟩
  · simpa only [iteratedDeriv_one, hLj.2.2.2.1.deriv, hSj.2.2.2.1.deriv, hNj.2.2.2.1.deriv] using
      And.intro (hLj.2.1.trans (hbudget j).1)
        ⟨hSj.2.1.trans (hbudget j).2.1, hNj.2.1.trans (hbudget j).2.2⟩
  · rw [SKBarriers2.affineVerticalDerivative_two_eq_iteratedDeriv hU
      (frozenAffine_factors_contDiffOn β j).1 hpU,
      SKBarriers2.affineVerticalDerivative_two_eq_iteratedDeriv hU
        (frozenAffine_factors_contDiffOn β j).2.1 hpU,
      SKBarriers2.affineVerticalDerivative_two_eq_iteratedDeriv hU
        (frozenAffine_factors_contDiffOn β j).2.2 hpU]
    exact ⟨hLj.2.2.1.trans (hbudget j).1, hSj.2.2.1.trans (hbudget j).2.1,
      hNj.2.2.1.trans (hbudget j).2.2⟩

theorem terminalTaylorQuadratic_centeredCoefficients (β : ℝ) (α : ℝ → ℝ)
    (s h z ε : ℝ) : CenteredQuadraticCoefficients (fun _ => z)
      ((terminalTaylorQuadratic β α s h z).scale (1 - ε))
      (separableTaylorQuadratic 0 ((1 - ε) * jet β α 1 (s + 4 * h) z)
        ((1 - ε) * jet β α 2 (s + 4 * h) z) 0) := by
  constructor
  · intro i q
    by_cases hiq : i = q <;>
      simp only [terminalTaylorQuadratic, QuadraticTerminal.scale,
        separableTaylorQuadratic, hiq, ite_true, ite_false, mul_zero]
  · intro i
    rw [terminalTaylorQuadratic_scaled_centerGradient]
    simp only [separableTaylorQuadratic, mul_zero, sub_zero]

def frozenAffineScalarBase (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ) : FrozenGeometryBase :=
  (a, ((1 - ε) * jet β α 1 (s + 4 * h) z, (1 - ε) * jet β α 2 (s + 4 * h) z))

def frozenRowsCompletedMeanLinear (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (j : ℕ) (k : ℝ) : Vec3 →L[ℝ] Vec3 :=
  let w := frozenRowsHead β a h j k
  let t := (frozenSchedule β a (1 / 2) h k).drop (j + 1)
  quadraticMeanLinear (riccatiRecursion t ((terminalTaylorQuadratic β α s h z).scale (1 - ε))) w.1 w.2

def frozenRowsCompletedMeanShift (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (j : ℕ) (k : ℝ) : Vec3 :=
  let w := frozenRowsHead β a h j k
  let t := (frozenSchedule β a (1 / 2) h k).drop (j + 1)
  let P := riccatiRecursion t ((terminalTaylorQuadratic β α s h z).scale (1 - ε))
  let c : Vec3 := fun _ => z
  (Real.sqrt h)⁻¹ • (quadraticMeanLinear P w.1 w.2 c + quadraticNoiseConstant P w.1 w.2 - c)

def frozenRowsCompletedHeadDirection (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (j : ℕ) (k : ℝ) : Vec3 :=
  frozenRowsCompletedDirection β α s h z ε (frozenRowsHead β a h j k)
    ((frozenSchedule β a (1 / 2) h k).drop (j + 1))

theorem frozenRowsCompleted_affine_factors (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (hh : 0 < h) (j : Fin 12) (k : ℝ) :
    let b := frozenAffineScalarBase β α a s h z ε
    let ρ := Real.sqrt h
    let p : FrozenGeometryParameter := ((b, ρ), k)
    frozenRowsCompletedMeanLinear β α a s h z ε j.val k =
        ContinuousLinearMap.id ℝ Vec3 + ρ ^ 2 • frozenAffineLinearFactor β j p ∧
      frozenRowsCompletedMeanShift β α a s h z ε j.val k = ρ • frozenAffineShiftFactor β j p ∧
      frozenRowsCompletedHeadDirection β α a s h z ε j.val k = frozenAffineNoiseFactor β j p := by
  let b := frozenAffineScalarBase β α a s h z ε
  let ρ := Real.sqrt h
  let p : FrozenGeometryParameter := ((b, ρ), k)
  let c : Vec3 := fun _ => z
  let Q := (terminalTaylorQuadratic β α s h z).scale (1 - ε)
  let t := (frozenSchedule β a (1 / 2) h k).drop (j.val + 1)
  let w := frozenUnitDirection β k j
  let m := a * frozenUnitMass j
  have hρ : ρ ≠ 0 := (Real.sqrt_pos.mpr hh).ne'
  have hhead : frozenRowsHead β a h j.val k = (m, ρ • w) := by
    unfold frozenRowsHead
    rw [frozenSchedule_eq_labelled β a h k hh.le]
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp [m, w, ρ]
  have htail : t = (frozenGeometryLabels j.val).map
      (fun i => (frozenGeometryMass i p, frozenGeometryDirection β i p)) := by
    dsimp only [t]
    rw [frozenSchedule_eq_labelled β a h k hh.le]
    rw [← List.map_drop]
    rfl
  have Hbase : CenteredQuadraticCoefficients c Q (frozenGeometryQuadratic p) :=
    terminalTaylorQuadratic_centeredCoefficients β α s h z ε
  have HR := Hbase.recursion t
  have hR : riccatiRecursion t (frozenGeometryQuadratic p) = frozenAffineRiccati β j p := by
    rw [htail]
    rfl
  rw [hR] at HR
  have hprec := HR.precision m (ρ • w)
  refine ⟨?_, ?_, ?_⟩
  · change quadraticMeanLinear (riccatiRecursion t Q) _ _ = _
    rw [hhead, HR.meanLinear]
    exact quadraticMeanLinear_scale_factor (frozenAffineRiccati β j p) m ρ w
  · change ρ⁻¹ • (quadraticMeanLinear (riccatiRecursion t Q) _ _ c +
      quadraticNoiseConstant (riccatiRecursion t Q) _ _ - c) = _
    rw [hhead, quadraticMean_center_scale_factor c w HR m ρ]
    ext i
    simp only [frozenAffineShiftFactor, frozenAffinePrecision, frozenGeometryMass,
      frozenGeometryDirection, p, b, frozenAffineScalarBase, Pi.smul_apply, smul_eq_mul]
    field_simp [hρ]
    ring
  · change ρ⁻¹ • ((Real.sqrt ((riccatiRecursion t Q).precision _ _)⁻¹) • _) = _
    rw [hhead, hprec]
    ext i
    simp only [frozenAffineNoiseFactor, frozenAffinePrecision, frozenGeometryMass,
      frozenGeometryDirection, p, b, frozenAffineScalarBase, Pi.smul_apply, smul_eq_mul]
    field_simp [hρ]
    ring

theorem scalarData_frozenRows_affine_geometry {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ 1 ≤ C ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ j : Fin 12, ∀ k : ℝ, |k| ≤ 1 / 2 →
        let α := cdf (D.μ : Measure ℝ)
        let a := α (r - h)
        let A := frozenRowsCompletedMeanLinear β α a (r - h) h z ε j.val
        let b := frozenRowsCompletedMeanShift β α a (r - h) h z ε j.val
        let v := frozenRowsCompletedHeadDirection β α a (r - h) h z ε j.val
        ‖A k‖ ≤ C ∧
          (∀ i : Fin 2, ‖iteratedDeriv (i.val + 1) A k‖ ≤ C * h) ∧
          (∀ i : Fin 3, ‖iteratedDeriv i.val b k‖ ≤ C * Real.sqrt h ∧
            ‖iteratedDeriv i.val v k‖ ≤ C) := by
  let a₀ := cdf (D.μ : Measure ℝ) (l / 2)
  let B := scalarTerminalJetBound D 2 + 1
  have ha₀ : 0 < a₀ := scalarData_cdf_pos_of_pos D (by positivity)
  obtain ⟨δ, K, hδ, hK, HK⟩ := frozenAffine_uniform_factor_jets β a₀ B ha₀
  let h₀ := min (δ ^ 2) (min 1 (min (l / 2) ((D.q - u) / 6)))
  refine ⟨h₀, K + 2, lt_min (sq_pos_of_pos hδ)
    (lt_min (by norm_num) (lt_min (by positivity) (by positivity))), by linarith, ?_⟩
  intro r hr h hh hhsmall z ε hε j k hk
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
  have HF := HK base hb ρ hρI k hkI j
  have hA : frozenRowsCompletedMeanLinear β α a (r - h) h z ε j.val =
      fun t => ContinuousLinearMap.id ℝ Vec3 + ρ ^ 2 • frozenAffineLinearFactor β j ((base, ρ), t) :=
    funext (fun t => (frozenRowsCompleted_affine_factors β α a (r - h) h z ε hh j t).1)
  have hb' : frozenRowsCompletedMeanShift β α a (r - h) h z ε j.val =
      fun t => ρ • frozenAffineShiftFactor β j ((base, ρ), t) :=
    funext (fun t => (frozenRowsCompleted_affine_factors β α a (r - h) h z ε hh j t).2.1)
  have hv : frozenRowsCompletedHeadDirection β α a (r - h) h z ε j.val =
      fun t => frozenAffineNoiseFactor β j ((base, ρ), t) :=
    funext (fun t => (frozenRowsCompleted_affine_factors β α a (r - h) h z ε hh j t).2.2)
  change ‖frozenRowsCompletedMeanLinear β α a (r - h) h z ε j.val k‖ ≤ K + 2 ∧ _
  rw [hA, hb', hv]
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ ‖ContinuousLinearMap.id ℝ Vec3‖ + ‖ρ ^ 2 • frozenAffineLinearFactor β j ((base, ρ), k)‖ := norm_add_le _ _
      _ ≤ 1 + h * K := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ρ), heh]
        exact add_le_add (ContinuousLinearMap.norm_id_le) (mul_le_mul_of_nonneg_left (HF 0).1 hh.le)
      _ ≤ K + 2 := by nlinarith [mul_le_of_le_one_left (by linarith : 0 ≤ K) hh₁]
  · intro i
    rw [iteratedDeriv_const_add (by omega), iteratedDeriv_fun_const_smul_field,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ρ), heh]
    exact (mul_le_mul_of_nonneg_left (HF ⟨i.val + 1, by omega⟩).1 hh.le).trans (by nlinarith)
  · intro i
    rw [iteratedDeriv_fun_const_smul_field, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    exact ⟨(mul_le_mul_of_nonneg_left (HF i).2.1 hρ.le).trans (by nlinarith),
      (HF i).2.2.trans (by linarith)⟩

end SKBarriers2.Corner
