module

public import SKBarriers2.Corner.FrozenRowsPotential4
public import SKBarriers2.Corner.FrozenOriginalNoise

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

theorem list_drop_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (j : ℕ) :
    (List.ofFn f).drop j =
      List.ofFn (fun i : Fin (n - j) => f ⟨j + i.val, by omega⟩) := by
  apply List.ext_get
  · simp
  · intro i h₁ h₂
    simp

theorem gaussianPathLinear_smul (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (c : ℝ) (v : Vec3) : gaussianPathLinear l Q (c • v) = c • gaussianPathLinear l Q v := by
  simp only [← gaussianPathLinearMap_apply, map_smul]

theorem labelledNoisePart_zero_of_zero {ι : Type} (m : ι → ℝ) (v : ι → Vec3)
    (l : List ι) (Q : QuadraticTerminal) (g : ι → ℝ)
    (H : ∀ j ∈ l, g j = 0) : labelledNoisePart m v l Q g = 0 := by
  induction l with
  | nil => rfl
  | cons j t ih =>
    rw [labelledNoisePart, H j List.mem_cons_self, mul_zero, zero_smul,
      ih (fun i hi => H i (List.mem_cons_of_mem j hi)), zero_add]

theorem completedSquareSchedule_eq_noiseCoefficients {ι : Type} [DecidableEq ι]
    (m : ι → ℝ) (v : ι → Vec3) (l : List ι) (Q : QuadraticTerminal) (hl : l.Nodup) :
    completedSquareSchedule (l.map (fun j => (m j, v j))) Q =
      l.map (fun j => (m j, labelledNoisePart m v l Q (Pi.single j 1))) := by
  induction l with
  | nil => rfl
  | cons j t ih =>
    have hjt : j ∉ t := (List.nodup_cons.mp hl).1
    have ht : t.Nodup := (List.nodup_cons.mp hl).2
    have hzero : labelledNoisePart m v t Q (Pi.single j 1) = 0 := by
      apply labelledNoisePart_zero_of_zero
      intro i hi
      have hij : i ≠ j := by intro he; subst i; exact hjt hi
      simp [hij]
    have hhead : labelledNoisePart m v (j :: t) Q (Pi.single j 1) =
        gaussianPathLinear (t.map (fun i => (m i, v i))) Q
          ((Real.sqrt ((riccatiRecursion (t.map (fun i => (m i, v i))) Q).precision
            (m j) (v j))⁻¹) • v j) := by
      rw [labelledNoisePart, Pi.single_eq_same, mul_one, hzero, add_zero,
        gaussianPathLinear_smul]
    have htail (i : ι) (hi : i ∈ t) :
        labelledNoisePart m v (j :: t) Q (Pi.single i 1) =
          labelledNoisePart m v t Q (Pi.single i 1) := by
      have hji : j ≠ i := by intro he; subst i; exact hjt hi
      have hz : (Pi.single i 1 : ι → ℝ) j = 0 := by simp [hji]
      rw [labelledNoisePart, hz, mul_zero, zero_smul, zero_add]
    simp only [List.map_cons, completedSquareSchedule, ih ht, hhead]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [htail i hi]

def frozenCompletedDirection (β a χ h : ℝ) (j : Fin 12) (k : ℝ) : Vec3 :=
  fun i => Real.sqrt h * frozenNormalizedNoise β j i (a * χ * h, k)

theorem completedSquareSchedule_frozen (β a c u χ h z k : ℝ) (hh : 0 ≤ h) :
    completedSquareSchedule (frozenSchedule β a (1 / 2) h k)
        (separableTaylorQuadratic c u χ z) =
      List.ofFn (fun j : Fin 12 => (a * frozenUnitMass j, frozenCompletedDirection β a χ h j k)) := by
  rw [frozenSchedule_eq_labelled β a h k hh,
    completedSquareSchedule_eq_noiseCoefficients _ _ _ _ (List.nodup_finRange 12),
    ← List.ofFn_eq_map]
  apply congrArg List.ofFn
  funext j
  apply Prod.ext
  · rfl
  · funext i
    exact frozen_labelledNoisePart_scaled β a c u χ h z k hh j i

def frozenCompletedDirectionFirst (β a χ h : ℝ) (j : Fin 12) (k : ℝ) : Vec3 :=
  fun i => Real.sqrt h * verticalDerivative (frozenNormalizedNoise β j i) (a * χ * h, k)

def frozenCompletedDirectionSecond (β a χ h : ℝ) (j : Fin 12) (k : ℝ) : Vec3 :=
  fun i => Real.sqrt h * verticalDerivative (verticalDerivative
    (frozenNormalizedNoise β j i)) (a * χ * h, k)

theorem frozenCompletedDirection_contDiffAt (β a χ h : ℝ) (j : Fin 12) (k : ℝ)
    (hk : (a * χ * h, k) ∈ frozenOriginalNoiseDomain β) :
    ContDiffAt ℝ 2 (frozenCompletedDirection β a χ h j) k := by
  apply contDiffAt_pi.mpr
  intro i
  have hF := (frozenNormalizedNoise_contDiffOn β j i).contDiffAt
    ((frozenOriginalNoiseDomain_isOpen β).mem_nhds hk)
  exact (contDiffAt_const.mul (hF.comp k
    (contDiffAt_const.prodMk contDiffAt_id))).of_le (by simp)

theorem frozenCompletedDirection_uniform_control (β : ℝ) :
    ∃ M δ : ℝ, 0 < M ∧ 0 < δ ∧
      ∀ a χ h k : ℝ, |a * χ * h| ≤ δ → |k| ≤ 1 / 2 → ∀ j : Fin 12,
      ‖frozenCompletedDirection β a χ h j k‖ ≤ M * Real.sqrt h ∧
      ‖frozenCompletedDirectionFirst β a χ h j k‖ ≤ M * Real.sqrt h ∧
      ‖frozenCompletedDirectionSecond β a χ h j k‖ ≤ M * Real.sqrt h ∧
      HasDerivAt (frozenCompletedDirection β a χ h j)
        (frozenCompletedDirectionFirst β a χ h j k) k ∧
      HasDerivAt (frozenCompletedDirectionFirst β a χ h j)
        (frozenCompletedDirectionSecond β a χ h j k) k ∧
      ContDiffAt ℝ 2 (frozenCompletedDirection β a χ h j) k := by
  obtain ⟨M, δ₀, hM, hδ₀, H⟩ := frozenNormalizedNoise_uniform_control β
  obtain ⟨δ₁, hδ₁, HD⟩ := frozenOriginalNoiseDomain_contains_rectangle β
  refine ⟨M, min δ₀ δ₁, hM, lt_min hδ₀ hδ₁, ?_⟩
  intro a χ h k ht hk j
  have ht₀ : |a * χ * h| ≤ δ₀ := ht.trans (min_le_left _ _)
  have ht₁ : |a * χ * h| ≤ δ₁ := ht.trans (min_le_right _ _)
  have HB (f : Fin 3 → ℝ) (hf : ∀ i, |f i| ≤ M) :
      ‖fun i => Real.sqrt h * f i‖ ≤ M * Real.sqrt h := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM.le (Real.sqrt_nonneg h))).mpr
    intro i
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg h), mul_comm M]
    exact mul_le_mul_of_nonneg_left (hf i) (Real.sqrt_nonneg h)
  refine ⟨HB _ (fun i => (H j i _ k ht₀ hk).1),
    HB _ (fun i => (H j i _ k ht₀ hk).2.1),
    HB _ (fun i => (H j i _ k ht₀ hk).2.2.1), ?_, ?_, ?_⟩
  · apply hasDerivAt_pi.mpr
    intro i
    exact (H j i _ k ht₀ hk).2.2.2.1.const_mul (Real.sqrt h)
  · apply hasDerivAt_pi.mpr
    intro i
    exact (H j i _ k ht₀ hk).2.2.2.2.const_mul (Real.sqrt h)
  · exact frozenCompletedDirection_contDiffAt β a χ h j k
      (HD ⟨abs_le.mp ht₁, abs_le.mp hk⟩)

end SKBarriers2.Corner
