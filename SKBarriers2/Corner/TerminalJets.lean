module

public import SKBarriers2.Analysis.QSmooth
public import SKBarriers2.Bridge.ScalarLawBasic
public import SKBarriers2.Corner.FrozenMerge
public import SKBarriers2.Corner.MassSensitivity
public import Paper.ParisiSpatialSmooth

@[expose] public section

noncomputable section
open scoped BigOperators ContDiff
open Set MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.Corner

local notation "E" => (Fin 3 → ℝ)

theorem scalarCDFOperator_spin_eq_Phi (β : ℝ) (α : ℝ → ℝ) (t : ℝ) :
    scalarCDFOperator β α t (Real.toNNReal (1 - t)) scalarSpinTerminal = Phi β α t := by
  rfl

theorem scalarData_phi_contDiff {β : ℝ} (D : ScalarData β) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ContDiff ℝ ∞ (Phi β (cdf (D.μ : Measure ℝ)) t) := by
  have hμ : Bridge.realMeasure (Bridge.overlapMeasure D.μ D.mass_one) = D.μ :=
    Bridge.realMeasure_overlapMeasure D.μ D.mass_one
  rw [← hμ, Bridge.Phi_eq_parisiPotential β _ t ht]
  exact (Paper.contDiff_parisiPotential_spatial β _ t ht).add contDiff_const

theorem scalarData_phi_regular {β : ℝ} (D : ScalarData β) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    BoundedDerivs (Phi β (cdf (D.μ : Measure ℝ)) t) := by
  have hμ : Bridge.realMeasure (Bridge.overlapMeasure D.μ D.mass_one) = D.μ :=
    Bridge.realMeasure_overlapMeasure D.μ D.mass_one
  rw [← hμ]
  exact Bridge.Phi_regular β _ t ht

def scalarTerminalJetBound {β : ℝ} (D : ScalarData β) (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range r, max 0 (D.jets j).choose

theorem scalarTerminalJetBound_nonneg {β : ℝ} (D : ScalarData β) (r : ℕ) :
    0 ≤ scalarTerminalJetBound D r := by
  exact Finset.sum_nonneg (fun j _ => le_max_left 0 (D.jets j).choose)

theorem scalarData_jet_le {β : ℝ} (D : ScalarData β) {r j : ℕ}
    (hj : 1 ≤ j) (hjr : j ≤ r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    |jet β (cdf (D.μ : Measure ℝ)) j t x| ≤ scalarTerminalJetBound D r := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  calc
    |jet β (cdf (D.μ : Measure ℝ)) (n + 1) t x| ≤ (D.jets n).choose :=
      (D.jets n).choose_spec t ht x
    _ ≤ max 0 (D.jets n).choose := le_max_right _ _
    _ ≤ scalarTerminalJetBound D r :=
      Finset.single_le_sum (fun i _ => le_max_left 0 (D.jets i).choose)
        (Finset.mem_range.mpr (by omega))

private theorem tripleCoordinate_norm_le (i : Fin 3) : ‖tripleCoordinate i‖ ≤ 1 := by
  apply (tripleCoordinate i).opNorm_le_bound (by norm_num : (0 : ℝ) ≤ 1)
  intro x
  simpa only [tripleCoordinate_apply, one_mul] using norm_le_pi_norm x i

theorem norm_iteratedFDeriv_coordinate_le {r j : ℕ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ r f) (hj : j ≤ r) (i : Fin 3) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y : E => f (y i)) x‖ ≤ |iteratedDeriv j f (x i)| := by
  change ‖iteratedFDeriv ℝ j (f ∘ tripleCoordinate i) x‖ ≤ _
  rw [(tripleCoordinate i).iteratedFDeriv_comp_right hf x (by exact_mod_cast hj)]
  calc
    ‖(iteratedFDeriv ℝ j f (tripleCoordinate i x)).compContinuousLinearMap
        (fun _ => tripleCoordinate i)‖ ≤
        ‖iteratedFDeriv ℝ j f (tripleCoordinate i x)‖ *
          ∏ _ : Fin j, ‖tripleCoordinate i‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ j f (tripleCoordinate i x)‖ * ∏ _ : Fin j, (1 : ℝ) := by
      gcongr with a
      exact tripleCoordinate_norm_le i
    _ = |iteratedDeriv j f (x i)| := by
      rw [Finset.prod_const_one, mul_one, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      rfl

theorem iteratedFDeriv_separable_sum_apply {r j : ℕ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ r f) (hj : j ≤ r) (x : E) (v : Fin j → E) :
    iteratedFDeriv ℝ j (fun y : E => ∑ i : Fin 3, f (y i)) x v =
      ∑ i : Fin 3, (∏ a : Fin j, v a i) * iteratedDeriv j f (x i) := by
  have hs (i : Fin 3) : ContDiff ℝ j (fun y : E => f (y i)) :=
    (hf.of_le (by exact_mod_cast hj)).comp (tripleCoordinate i).contDiff
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => (hs i).contDiffAt)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  change iteratedFDeriv ℝ j (f ∘ tripleCoordinate i) x v = _
  rw [(tripleCoordinate i).iteratedFDeriv_comp_right hf x (by exact_mod_cast hj),
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  rfl

theorem iteratedFDeriv_separable_sum_mixed_eq_zero {r j : ℕ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ r f) (hj : j ≤ r) (x : E) (index : Fin j → Fin 3)
    (hmixed : ∃ a b, index a ≠ index b) :
    iteratedFDeriv ℝ j (fun y : E => ∑ i : Fin 3, f (y i)) x
      (fun a => Pi.single (index a) (1 : ℝ)) = 0 := by
  obtain ⟨a, b, hab⟩ := hmixed
  rw [iteratedFDeriv_separable_sum_apply hf hj]
  apply Finset.sum_eq_zero
  intro i _
  have hmiss : ∃ c : Fin j, index c ≠ i := by
    by_cases ha : index a = i
    · exact ⟨b, fun hb => hab (ha.trans hb.symm)⟩
    · exact ⟨a, ha⟩
  obtain ⟨c, hc⟩ := hmiss
  have hz : (∏ d : Fin j, (Pi.single (index d) (1 : ℝ) : E) i) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    change (Pi.single (index c) (1 : ℝ) : E) i = 0
    exact Pi.single_eq_of_ne (M := fun _ : Fin 3 => ℝ) hc.symm (1 : ℝ)
  rw [hz, zero_mul]

theorem qPotential_separable_sum {r : ℕ} {B : ℝ} {f : ℝ → ℝ}
    (hB : 0 ≤ B) (hf : ContDiff ℝ r f)
    (hjets : ∀ j, 1 ≤ j → j ≤ r → ∀ x, |iteratedDeriv j f x| ≤ B) :
    QPotential r (3 * B) (fun x : E => ∑ i : Fin 3, f (x i)) := by
  have hs (i : Fin 3) : ContDiff ℝ r (fun x : E => f (x i)) :=
    hf.comp (tripleCoordinate i).contDiff
  refine ⟨mul_nonneg (by norm_num) hB, ContDiff.sum (fun i _ => hs i), ?_⟩
  intro j hj hjr x
  rw [iteratedFDeriv_fun_sum_apply (fun i _ =>
    ((hs i).of_le (by exact_mod_cast hjr)).contDiffAt)]
  calc
    ‖∑ i : Fin 3, iteratedFDeriv ℝ j (fun y : E => f (y i)) x‖ ≤
        ∑ i : Fin 3, ‖iteratedFDeriv ℝ j (fun y : E => f (y i)) x‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, B := Finset.sum_le_sum (fun i _ =>
      (norm_iteratedFDeriv_coordinate_le hf hjr i x).trans (hjets j hj hjr (x i)))
    _ = 3 * B := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat]

def terminalJetBound {β : ℝ} (D : ScalarData β) (r : ℕ) : ℝ :=
  3 * scalarTerminalJetBound D r

theorem terminalJetBound_nonneg {β : ℝ} (D : ScalarData β) (r : ℕ) :
    0 ≤ terminalJetBound D r := by
  exact mul_nonneg (by norm_num) (scalarTerminalJetBound_nonneg D r)

theorem scalarData_terminal_qPotential {β : ℝ} (D : ScalarData β) (r : ℕ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    QPotential r (terminalJetBound D r)
      (fun x : E => ∑ i : Fin 3,
        scalarCDFOperator β (cdf (D.μ : Measure ℝ)) t (Real.toNNReal (1 - t))
          scalarSpinTerminal (x i)) := by
  change QPotential r (3 * scalarTerminalJetBound D r)
    (fun x : E => ∑ i : Fin 3, Phi β (cdf (D.μ : Measure ℝ)) t (x i))
  exact qPotential_separable_sum (scalarTerminalJetBound_nonneg D r)
    ((scalarData_phi_contDiff D ht).of_le (by simp))
    (fun j hj hjr x => scalarData_jet_le D hj hjr ht x)

theorem scalarData_terminal_qPotential_uniform {β : ℝ} (D : ScalarData β) (r : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      QPotential r B (fun x : E => ∑ i : Fin 3,
        scalarCDFOperator β (cdf (D.μ : Measure ℝ)) t (Real.toNNReal (1 - t))
          scalarSpinTerminal (x i)) := by
  exact ⟨terminalJetBound D r, terminalJetBound_nonneg D r,
    fun _ ht => scalarData_terminal_qPotential D r ht⟩

theorem scalarData_terminal_regular {β : ℝ} (D : ScalarData β) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    BoundedDerivs (fun x : E => ∑ i : Fin 3,
      scalarCDFOperator β (cdf (D.μ : Measure ℝ)) t (Real.toNNReal (1 - t))
        scalarSpinTerminal (x i)) := by
  exact (scalarData_terminal_qPotential D 2 ht).boundedDerivs le_rfl

theorem scalarData_frozenTerminal_qPotential {β : ℝ} (D : ScalarData β) (r : ℕ)
    {s h : ℝ} (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) :
    QPotential r (terminalJetBound D r) (frozenTerminal β (cdf (D.μ : Measure ℝ)) s h) := by
  exact scalarData_terminal_qPotential D r ht

theorem scalarData_frozenTerminal_regular {β : ℝ} (D : ScalarData β)
    {s h : ℝ} (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) :
    BoundedDerivs (frozenTerminal β (cdf (D.μ : Measure ℝ)) s h) := by
  exact (scalarData_frozenTerminal_qPotential D 2 ht).boundedDerivs le_rfl

theorem scalarData_massVariationTerminal_qPotential {β : ℝ} (D : ScalarData β) (r : ℕ)
    {s h : ℝ} (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) :
    QPotential r (terminalJetBound D r)
      (massVariationTerminal β (cdf (D.μ : Measure ℝ)) s h) := by
  exact scalarData_terminal_qPotential D r ht

theorem scalarData_massVariationTerminal_regular {β : ℝ} (D : ScalarData β)
    {s h : ℝ} (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) :
    BoundedDerivs (massVariationTerminal β (cdf (D.μ : Measure ℝ)) s h) := by
  exact (scalarData_massVariationTerminal_qPotential D 2 ht).boundedDerivs le_rfl

end SKBarriers2.Corner
