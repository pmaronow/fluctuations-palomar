module

public import SKBarriers2.Corner.FrozenRowsAffineGeometry
public import SKBarriers2.Corner.FrozenRowsNoise7

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set MeasureTheory ProbabilityTheory Filter OAI.SK.Analytic

namespace SKBarriers2.Corner

theorem frozenUnitDirection_uniform_jets (β : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j : Fin 12, ∀ k : ℝ, |k| ≤ 1 / 2 →
      ContDiffAt ℝ ∞ (fun t => frozenUnitDirection β t j) k ∧
      ∀ i : Fin 3, ‖iteratedDeriv i.val (fun t => frozenUnitDirection β t j) k‖ ≤ C := by
  classical
  let U : Set (ℝ × ℝ) := univ ×ˢ Ioo (-(3 / 5) : ℝ) (3 / 5)
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 0 ×ˢ Icc (-(1 / 2) : ℝ) (1 / 2)
  let f := fun j : Fin 12 => fun p : ℝ × ℝ => frozenUnitDirection β p.2 j
  have hU : IsOpen U := isOpen_univ.prod isOpen_Ioo
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKU : K ⊆ U := by
    rintro ⟨a,k⟩ ⟨_,hk⟩
    exact ⟨mem_univ _, by constructor <;> linarith [hk.1,hk.2]⟩
  have hf (j : Fin 12) : ContDiffOn ℝ ∞ (f j) U := by
    intro p hp
    have hk : |p.2| < 3 / 5 := abs_lt.mpr hp.2
    exact ((frozenUnitDirection_contDiffAt_k β hk j).comp p contDiffAt_snd).contDiffWithinAt
  choose B hB HB using fun j => SKBarriers2.compact_affine_vertical_bounds hK hU (hf j) hKU
  let C := 1+∑ j : Fin 12, B j
  have hC : 1 ≤ C := by
    have H := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin 12))) => (hB j).le)
    dsimp only [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro j k hk
  have hxK : ((0 : ℝ),k) ∈ K := ⟨⟨le_rfl,le_rfl⟩,abs_le.mp hk⟩
  have H := HB j (0,k) hxK
  have hBC : B j ≤ C := by
    have H := Finset.single_le_sum (f := B) (fun q _ => (hB q).le) (Finset.mem_univ j)
    dsimp only [C]
    linarith
  refine ⟨frozenUnitDirection_contDiffAt_k β (by linarith : |k| < 3/5) j, ?_⟩
  intro i
  fin_cases i
  · exact H.1.trans hBC
  · change ‖iteratedDeriv 1 (fun t => f j (0,t)) k‖ ≤ C
    rw [iteratedDeriv_one, H.2.2.2.1.deriv]
    exact H.2.1.trans hBC
  · change ‖iteratedDeriv 2 (fun t => f j (0,t)) k‖ ≤ C
    rw [SKBarriers2.affineVerticalDerivative_two_eq_iteratedDeriv hU (hf j) (hKU hxK)]
    exact H.2.2.1.trans hBC

theorem frozenRowsHead_direction_uniform_jets (β : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a h : ℝ, 0 ≤ h → ∀ j : Fin 12, ∀ k : ℝ, |k| ≤ 1 / 2 →
      let v := fun t => (frozenRowsHead β a h j.val t).2
      ContDiffAt ℝ ∞ v k ∧ ∀ i : Fin 3, ‖iteratedDeriv i.val v k‖ ≤ C * Real.sqrt h := by
  obtain ⟨C,hC,HC⟩ := frozenUnitDirection_uniform_jets β
  refine ⟨C,hC,?_⟩
  intro a h hh j k hk
  have hv : (fun t => (frozenRowsHead β a h j.val t).2) =
      fun t => Real.sqrt h • frozenUnitDirection β t j := by
    funext t
    rw [frozenRowsHead_eq_labelled β a h t hh j.val j.isLt]
  have H := HC j k hk
  dsimp only
  rw [hv]
  refine ⟨H.1.const_smul (Real.sqrt h), ?_⟩
  intro i
  rw [iteratedDeriv_fun_const_smul_field,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg h)]
  exact (mul_le_mul_of_nonneg_left (H.2 i) (Real.sqrt_nonneg h)).trans_eq (mul_comm _ _)

end SKBarriers2.Corner
