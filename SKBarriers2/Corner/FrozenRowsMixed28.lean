module

public import SKBarriers2.Corner.FrozenRowsMixed26
public import SKBarriers2.Corner.FrozenRowsMixed27
public import SKBarriers2.Corner.FrozenRowsAffineGeometry4

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic SKOptimized.Overshoot
namespace SKBarriers2.Corner

private theorem ordinary_three_jets_of_iterated {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : ℝ → Y} {k B : ℝ} (H : ∀ i : Fin 3, ‖iteratedDeriv i.val f k‖ ≤ B) :
    ‖f k‖ ≤ B ∧ ‖deriv f k‖ ≤ B ∧ ‖deriv (deriv f) k‖ ≤ B := by
  refine ⟨?_,?_,?_⟩
  · have H₀ : ‖iteratedDeriv 0 f k‖ ≤ B := H (0 : Fin 3)
    simpa only [iteratedDeriv_zero] using H₀
  · have H₁ : ‖iteratedDeriv 1 f k‖ ≤ B := H (1 : Fin 3)
    simpa only [iteratedDeriv_one] using H₁
  · have H₂ : ‖iteratedDeriv 2 f k‖ ≤ B := H (2 : Fin 3)
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using H₂

def frozenRowsMovingTestEndpoint (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (parent q : Fin 12) (g k t : ℝ) (y : Vec3) : Vec3 :=
  let A := frozenRowsCompletedMeanLinear β α a s h z ε q.val k
  A y+frozenRowsCompletedMeanShift β α a s h z ε q.val k+
    g • A (frozenUnitDirection β k parent)+t • frozenRowsCompletedHeadDirection β α a s h z ε q.val k

def frozenRowsMovingParameterCurve (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (parent q : Fin 12) (g : ℝ) : ℝ → ℝ × AffineRowParameters :=
  frozenRowsTranslatedParameterCurve β α a s h z ε q
    (fun κ => Real.sqrt h • (g • frozenUnitDirection β κ parent))

theorem frozenRowsMovingParameterCurve_eq_physical (β : ℝ) (α : ℝ → ℝ)
    (a s h z ε : ℝ) (hh : 0 ≤ h) (parent q : Fin 12) (g : ℝ) :
    frozenRowsMovingParameterCurve β α a s h z ε parent q g =
      frozenRowsTranslatedParameterCurve β α a s h z ε q
        (fun κ => g • (frozenRowsHead β a h parent.val κ).2) := by
  unfold frozenRowsMovingParameterCurve
  congr 1
  funext κ
  rw [frozenRowsHead_eq_labelled β a h κ hh parent.val parent.isLt]
  exact smul_comm _ _ _

theorem frozenRowsMovingParameterCurve_endpoint (β : ℝ) (α : ℝ → ℝ)
    (a s h z ε : ℝ) (ha : 0 < a) (hh : 0 < h)
    (parent q : Fin 12) (g k t : ℝ) (y : Vec3) :
    affineCoordinateEndpoint (frozenRowsNaturalHead h z q)
      (frozenRowsMovingParameterCurve β α a s h z ε parent q g k,(y,t)) =
      frozenRowsMovingTestEndpoint β α a s h z ε parent q g k t y := by
  have H := frozenRowsTranslated_head_values β α a s h z ε k ha hh.le q
    (fun κ => Real.sqrt h • (g • frozenUnitDirection β κ parent))
  dsimp only [affineCoordinateEndpoint,frozenRowsMovingParameterCurve]
  rw [H.2.1,H.2.2.2,H.2.2.1]
  unfold frozenRowsMovingTestEndpoint
  rw [map_smul,map_smul,smul_smul,inv_mul_cancel₀ (Real.sqrt_pos.mpr hh).ne',one_smul]
  abel

theorem scalarData_frozenRowsMovingTestEndpoint_geometry {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ K : ℝ, 0 < h₀ ∧ 1 ≤ K ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ parent q : Fin 12, ∀ k ∈ frozenRowsKDomain, ∀ g : ℝ,
      let α := cdf (D.μ : MeasureTheory.Measure ℝ)
      let a := α (r-h)
      let A := frozenRowsCompletedMeanLinear β α a (r-h) h z ε q.val k
      let d := frozenRowsCompletedMeanShift β α a (r-h) h z ε q.val k+
        g • A (frozenUnitDirection β k parent)
      let v := frozenRowsCompletedHeadDirection β α a (r-h) h z ε q.val k
      let σ := Real.sqrt h/(1+|g|)
      let δ := (Real.sqrt h)^3/(1+|g|)
      let X := frozenRowsMovingTestEndpoint β α a (r-h) h z ε parent q g
      ContDiffAt ℝ ∞ (frozenRowsMovingParameterCurve β α a (r-h) h z ε parent q g) k ∧
      ∃ V₀ W₀ : ℝ → Vec3, ∃ U V : Vec3 →L[ℝ] Vec3,
        ContDiff ℝ ∞ V₀ ∧ ContDiff ℝ ∞ W₀ ∧
        ‖A‖ ≤ K ∧ ‖d‖ ≤ K*(1+|g|) ∧ ‖v‖ ≤ K ∧ ‖U‖ ≤ K ∧ ‖V‖ ≤ K ∧
        (∀ t, ‖V₀ t‖ ≤ K*(1+|t|) ∧ ‖W₀ t‖ ≤ K*(1+|t|)) ∧
        (∀ t y, ContDiffAt ℝ 2 (fun κ => X κ t y) k) ∧
        (∀ t y, σ • deriv (fun κ => X κ t y) k = V₀ t+δ • U y) ∧
        (∀ t y, σ^2 • deriv (deriv (fun κ => X κ t y)) k = W₀ t+δ • V y) := by
  obtain ⟨hG,C,hhG,hC,HG⟩ := scalarData_frozenRows_affine_geometry D hl hu
  obtain ⟨hR,hhR,HR⟩ := scalarData_frozenRows_natural_realization D hl hu
  obtain ⟨E,hE,HE⟩ := frozenUnitDirection_uniform_jets β
  let h₀ := min hG (min hR 1)
  let K := 1+3*C+5*C*E
  have hC₀ : 0 ≤ C := by linarith
  have hE₀ : 0 ≤ E := by linarith
  have hCK : C ≤ K := by dsimp only [K]; nlinarith [mul_nonneg hC₀ hE₀]
  have hVK : 2*C+4*C*E ≤ K := by dsimp only [K]; nlinarith [mul_nonneg hC₀ hE₀]
  have hdK : C+C*E ≤ K := by dsimp only [K]; nlinarith [mul_nonneg hC₀ hE₀]
  refine ⟨h₀,K,lt_min hhG (lt_min hhR (by norm_num)),?_,?_⟩
  · dsimp only [K]
    nlinarith [mul_nonneg hC₀ hE₀]
  intro r hr h hh hhsmall z ε hε parent q k hk g
  have hhG' : h ≤ hG := hhsmall.trans (min_le_left _ _)
  have hhR' : h ≤ hR := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hh₁ : h ≤ 1 := (hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  let α := cdf (D.μ : MeasureTheory.Measure ℝ)
  let a := α (r-h)
  let A := frozenRowsCompletedMeanLinear β α a (r-h) h z ε q.val
  let b := frozenRowsCompletedMeanShift β α a (r-h) h z ε q.val
  let v := frozenRowsCompletedHeadDirection β α a (r-h) h z ε q.val
  let c := fun κ => frozenUnitDirection β κ parent
  let ρ := Real.sqrt h
  have hρ : 0 < ρ := Real.sqrt_pos.mpr hh
  have hρ₁ : ρ ≤ 1 := Real.sqrt_le_one.mpr hh₁
  have hρ₂ : ρ^2 = h := Real.sq_sqrt hh.le
  have hk' : |k| ≤ 1/2 := abs_le.mpr ⟨by linarith [hk.1],by linarith [hk.2]⟩
  have H := HG r hr h hh hhG' z ε hε q k hk'
  have Hreg := (HR r hr h hh hhR' z ε hε).head_contDiffAt hk q
  have Hc := HE parent k hk'
  have Hb := ordinary_three_jets_of_iterated (fun i => (H.2.2 i).1)
  have Hv := ordinary_three_jets_of_iterated (fun i => (H.2.2 i).2)
  have HcJ := ordinary_three_jets_of_iterated Hc.2
  have hb₁ : ‖deriv b k‖ ≤ C :=
    Hb.2.1.trans (mul_le_of_le_one_right hC₀ hρ₁)
  have hb₂ : ‖deriv (deriv b) k‖ ≤ C :=
    Hb.2.2.trans (mul_le_of_le_one_right hC₀ hρ₁)
  have hA₁ : ‖deriv A k‖ ≤ C*ρ^2 := by
    simpa only [Fin.val_zero,zero_add,iteratedDeriv_one,hρ₂] using H.2.1 (0 : Fin 2)
  have hA₂ : ‖deriv (deriv A) k‖ ≤ C*ρ^2 := by
    simpa only [Fin.val_one,show (1:ℕ)+1 = 2 from rfl,iteratedDeriv_succ,iteratedDeriv_zero,hρ₂]
      using H.2.1 (1 : Fin 2)
  obtain ⟨V₀,W₀,U,V,hV₀,hW₀,hA,hU,hV,hVW,hX,hfirst,hsecond⟩ :=
    affine_endpoint_normalized_small_score_geometry hρ hρ₁ hC₀ hE₀
      (Hreg.1.of_le (by simp)) (Hreg.2.1.of_le (by simp))
      (Hc.1.of_le (by simp)) (Hreg.2.2.of_le (by simp))
      H.1 hA₁ hA₂ hb₁ hb₂ Hv.2.1 Hv.2.2
      HcJ.1 HcJ.2.1 HcJ.2.2 g
  have hb₀ : ‖b k‖ ≤ C := Hb.1.trans (mul_le_of_le_one_right hC₀ hρ₁)
  have hd : ‖b k+g • A k (c k)‖ ≤ K*(1+|g|) := by
    calc
      _ ≤ ‖b k‖+‖g • A k (c k)‖ := norm_add_le _ _
      _ ≤ C+|g| *(C*E) := by
        rw [norm_smul,Real.norm_eq_abs]
        have hAc : ‖A k (c k)‖ ≤ C*E := ((A k).le_opNorm _).trans
          (mul_le_mul H.1 HcJ.1 (norm_nonneg _) hC₀)
        exact add_le_add hb₀ (mul_le_mul_of_nonneg_left hAc (abs_nonneg g))
      _ ≤ (C+C*E)*(1+|g|) := by nlinarith [mul_nonneg hC₀ (abs_nonneg g)]
      _ ≤ K*(1+|g|) := mul_le_mul_of_nonneg_right hdK (by positivity)
  have hcurve := frozenRowsTranslatedParameterCurve_contDiffAt β α a (r-h) h z ε q
    ((HR r hr h hh hhR' z ε hε).curve_smooth k hk) ((Hc.1.const_smul g).const_smul ρ)
  dsimp only
  refine ⟨hcurve,V₀,W₀,U,V,hV₀,hW₀,hA.trans hCK,hd,Hv.1.trans hCK,
    hU.trans hCK,hV.trans hCK,?_,hX,hfirst,hsecond⟩
  intro t
  exact ⟨(hVW t).1.trans (mul_le_mul_of_nonneg_right hVK (by positivity)),
    (hVW t).2.trans (mul_le_mul_of_nonneg_right hVK (by positivity))⟩

end SKBarriers2.Corner
