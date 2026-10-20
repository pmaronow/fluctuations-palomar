module

public import SKBarriers2.Corner.FrozenRowsAffineGeometry2

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set MeasureTheory ProbabilityTheory Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def frozenAffinePathMean (β : ℝ) (n : ℕ) (p : FrozenGeometryParameter) : Vec3 :=
  gaussianPathMean ((frozenAffinePathLabels n).map
    (fun j => (frozenGeometryMass j p, frozenGeometryDirection β j p))) (frozenGeometryQuadratic p) 0

theorem frozenAffinePathMean_contDiffOn (β : ℝ) (n : ℕ) :
    ContDiffOn ℝ ∞ (frozenAffinePathMean β n) (frozenGeometryDomain β) := by
  intro p hp
  apply (contDiffAt_pi.mpr (gaussianPathMean_contDiffAt (frozenAffinePathLabels n)
    frozenGeometryMass (frozenGeometryDirection β) frozenGeometryQuadratic
    ?_ ?_ (frozenGeometryQuadratic_contDiffAt p) (frozenAffinePath_admissible β n hp)
    (fun _ => (0 : Vec3)) (fun _ => contDiffAt_const))).contDiffWithinAt
  · intro j _
    unfold frozenGeometryMass
    fun_prop
  · intro j _ i
    exact frozenGeometryDirection_contDiffAt β hp.1.1 j i

theorem frozenAffinePathMean_uniform_regular_jets (β a₀ B : ℝ) (ha₀ : 0 < a₀) :
    ∃ δ C : ℝ, 0 < δ ∧ 1 ≤ C ∧
      ∀ b ∈ frozenGeometryBaseBox a₀ B, ∀ ρ ∈ Icc (-δ) δ,
        ∀ k ∈ Icc (-(1 / 2) : ℝ) (1 / 2), ∀ n : Fin 13,
          ContDiffAt ℝ ∞ (fun t => frozenAffinePathMean β n.val ((b, ρ), t)) k ∧
          ContDiffAt ℝ ∞ (fun t => frozenAffinePathFactor β n.val ((b, ρ), t)) k ∧
          ∀ i : Fin 3,
            ‖iteratedDeriv i.val (fun t => frozenAffinePathMean β n.val ((b, ρ), t)) k‖ ≤ C := by
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
    (frozenAffinePathMean_contDiffOn β n.val) hKU
  let C := 1 + ∑ n : Fin 13, S n
  have hC : 1 ≤ C := by
    have H := Finset.sum_nonneg (fun n (_ : n ∈ (Finset.univ : Finset (Fin 13))) => (hS n).le)
    dsimp only [C]
    linarith
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro b hb ρ hρ k hk n
  have hpK : ((b, ρ), k) ∈ K := ⟨⟨hb, hρ⟩, hk⟩
  have hpU := hKU hpK
  have H := HS n ((b, ρ), k) hpK
  have hSC : S n ≤ C := by
    have H := Finset.single_le_sum (f := S) (fun j _ => (hS j).le) (Finset.mem_univ n)
    dsimp only [C]
    linarith
  refine ⟨((frozenAffinePathMean_contDiffOn β n.val).contDiffAt (hU.mem_nhds hpU)).comp k
    (contDiffAt_const.prodMk contDiffAt_id),
    ((frozenAffinePathFactor_contDiffOn β n.val).contDiffAt (hU.mem_nhds hpU)).comp k
      (contDiffAt_const.prodMk contDiffAt_id), ?_⟩
  intro i
  fin_cases i
  · exact H.1.trans hSC
  · simpa only [iteratedDeriv_one, H.2.2.2.1.deriv] using H.2.1.trans hSC
  · rw [SKBarriers2.affineVerticalDerivative_two_eq_iteratedDeriv hU
      (frozenAffinePathMean_contDiffOn β n.val) hpU]
    exact H.2.2.1.trans hSC

theorem scalarData_frozenRows_path_mean_regular_geometry {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ 1 ≤ C ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ n : Fin 13, ∀ k : ℝ, |k| ≤ 1 / 2 →
        let α := cdf (D.μ : Measure ℝ)
        let a := α (r - h)
        let A := fun t => gaussianPathMean ((frozenSchedule β a (1 / 2) h t).drop n.val)
          (separableTaylorQuadratic 0 ((1-ε)*jet β α 1 ((r-h)+4*h) z)
            ((1-ε)*jet β α 2 ((r-h)+4*h) z) 0) 0
        ContDiffAt ℝ ∞ A k ∧
        ContDiffAt ℝ ∞ (fun t => gaussianPathLinearCLM
          ((frozenSchedule β a (1 / 2) h t).drop n.val)
          (separableTaylorQuadratic 0 ((1-ε)*jet β α 1 ((r-h)+4*h) z)
            ((1-ε)*jet β α 2 ((r-h)+4*h) z) 0)) k ∧
        ∀ i : Fin 3, ‖iteratedDeriv i.val A k‖ ≤ C := by
  let a₀ := cdf (D.μ : Measure ℝ) (l / 2)
  let B := scalarTerminalJetBound D 2 + 1
  have ha₀ : 0 < a₀ := scalarData_cdf_pos_of_pos D (by positivity)
  obtain ⟨δ, K, hδ, hK, HK⟩ := frozenAffinePathMean_uniform_regular_jets β a₀ B ha₀
  let h₀ := min (δ ^ 2) (min 1 (min (l / 2) ((D.q - u) / 6)))
  refine ⟨h₀, K, lt_min (sq_pos_of_pos hδ)
    (lt_min (by norm_num) (lt_min (by positivity) (by positivity))), hK, ?_⟩
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
  let A := fun t => gaussianPathMean ((frozenSchedule β a (1 / 2) h t).drop n.val)
    (separableTaylorQuadratic 0 ((1-ε)*jet β α 1 ((r-h)+4*h) z)
      ((1-ε)*jet β α 2 ((r-h)+4*h) z) 0) 0
  have hA : A = fun t => frozenAffinePathMean β n.val ((base, ρ), t) := by
    funext t
    dsimp only [A, frozenAffinePathMean]
    rw [frozenSchedule_eq_labelled β a h t hh.le, ← List.map_drop]
    rfl
  have hL : (fun t => gaussianPathLinearCLM ((frozenSchedule β a (1 / 2) h t).drop n.val)
      (separableTaylorQuadratic 0 ((1-ε)*jet β α 1 ((r-h)+4*h) z)
        ((1-ε)*jet β α 2 ((r-h)+4*h) z) 0)) =
      fun t => ContinuousLinearMap.id ℝ Vec3 + ρ ^ 2 • frozenAffinePathFactor β n.val ((base,ρ),t) := by
    funext t
    have H := frozenRows_path_linear_factor β α a (r-h) h z ε hh n.val t
    have HC := terminalTaylorQuadratic_centeredCoefficients β α (r-h) h z ε
    dsimp only at H
    rw [HC.pathLinear] at H
    exact H
  refine ⟨?_, ?_, ?_⟩
  · change ContDiffAt ℝ ∞ A k
    rw [hA]
    exact HF.1
  · rw [hL]
    exact contDiffAt_const.add ((HF.2.1).const_smul (ρ ^ 2))
  · change ∀ i : Fin 3, ‖iteratedDeriv i.val A k‖ ≤ K
    rw [hA]
    exact HF.2.2

end SKBarriers2.Corner
