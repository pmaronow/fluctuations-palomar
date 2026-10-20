module

public import SKBarriers2.Corner.PathEnergyGenerator6

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

private structure GeneratorFirstDatum (B A : ℝ) where
  C : ℝ
  e : ℝ
  m : ℝ
  dm : ℝ
  f : E → ℝ
  f₁ : E → ℝ
  g : E → ℝ
  a : E → ℝ
  v : E
  w : E
  hC : 0 < C
  he : 0 < e
  hf : QPotential 6 B f
  hf₁ : QBoundedJets 4 A f₁
  hg : QBoundedJets 5 C g
  ha : QBoundedJets 5 C a
  hm : m ∈ Icc (0:ℝ) 1
  hdm : |dm| ≤ 1
  hdir : ‖v‖^2+‖w‖^2 ≤ e

private def GeneratorFirstDatum.error {B A : ℝ} (i : GeneratorFirstDatum B A) (x : E) : ℝ :=
  firstTiltedAverageSource i.m i.v i.f i.f₁ i.g i.a i.dm i.w x-
    firstMovingAverageQuadratic i.m i.dm i.v i.w i.f i.f₁ i.g i.a x

theorem normalized_firstMovingAverageDefect_spatial_eventually {B A L h : ℝ}
    (hB : 0 ≤ B) (hA : 0 ≤ A) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop, ∀ C e : ℝ, 0 < C → 0 < e →
      ∀ (f f₁ g a : E → ℝ), QPotential 6 B f → QBoundedJets 4 A f₁ →
      QBoundedJets 5 C g → QBoundedJets 5 C a →
      ∀ (m dm : ℝ), m ∈ Icc (0:ℝ) 1 → |dm| ≤ 1 →
      ∀ (v w : E), ‖v‖^2+‖w‖^2 ≤ e → e ≤ L*h/(N:ℝ) →
      QBoundedJets 2 (eps*C*e) (fun x =>
        firstTiltedAverageSource m v f f₁ g a dm w x-
          firstMovingAverageQuadratic m dm v w f f₁ g a x) := by
  classical
  let I := GeneratorFirstDatum B A
  let K := firstWeakSpatialCoefficient B A 1 1 1 1
  let V := firstWeakDefectCoefficient B A 1 1 1 1
  have hP := pathExpansionConstant_nonneg hB
  have hQ := potentialCovarianceDefectCoefficient_nonneg hB
  have hT := tiltedDifferenceCoefficient_nonneg 3 B
  have hK : 0 ≤ K := by dsimp only [K,firstWeakSpatialCoefficient]; positivity
  have hV : 0 ≤ V := by dsimp only [V,firstWeakDefectCoefficient]; positivity
  let F : ℕ → I → E → ℝ := fun N i x =>
    if i.e ≤ L*h/(N:ℝ) then (i.C*i.e)⁻¹*i.error x else 0
  have hlim : Tendsto (fun N : ℕ => L*h/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsteps : ∀ᶠ N : ℕ in atTop, ∀ i : I, i.e ≤ L*h/(N:ℝ) →
      ‖i.v‖ ≤ 1 ∧ i.m*(B*‖i.v‖^2) ≤ 1/2 := by
    filter_upwards [hlim.eventually (eventually_le_nhds
      (lt_min (by norm_num : (0:ℝ) < 1) (by positivity : 0 < 1/(2*B+1))))] with N hN i hi
    have he1 := hi.trans (hN.trans (min_le_left _ _))
    have hv2 : ‖i.v‖^2 ≤ i.e := by nlinarith only [i.hdir,sq_nonneg ‖i.w‖]
    have hv1 : ‖i.v‖ ≤ 1 := by nlinarith only [hv2,he1,norm_nonneg i.v]
    have heB := (le_div_iff₀ (by positivity : 0 < 2*B+1)).mp
      (hi.trans (hN.trans (min_le_right _ _)))
    have hmB := mul_le_of_le_one_left (mul_nonneg hB (sq_nonneg ‖i.v‖)) i.hm.2
    refine ⟨hv1,?_⟩
    nlinarith only [heB,hmB,mul_le_mul_of_nonneg_left hv2 hB,i.he.le]
  have hnorm (i : I) : ‖i.v‖ ≤ Real.sqrt i.e ∧ ‖i.w‖ ≤ Real.sqrt i.e := by
    constructor <;> apply Real.le_sqrt_of_sq_le <;>
      nlinarith only [i.hdir,sq_nonneg ‖i.v‖,sq_nonneg ‖i.w‖]
  have hcoef (i : I) :
      firstWeakSpatialCoefficient B A i.C i.C i.m i.dm ≤ i.C*K ∧
      firstWeakDefectCoefficient B A i.C i.C i.m i.dm ≤ i.C*V := by
    have hC := i.hC.le
    have hdm := i.hdm
    have hmabs : |i.m| ≤ 1 := by rw [abs_of_nonneg i.hm.1]; exact i.hm.2
    constructor
    · calc
        _ ≤ firstWeakSpatialCoefficient B A i.C i.C 1 1 := by
          dsimp only [firstWeakSpatialCoefficient]
          norm_num only [abs_one]
          gcongr
        _ = _ := by dsimp only [K,firstWeakSpatialCoefficient]; norm_num; ring
    · calc
        _ ≤ firstWeakDefectCoefficient B A i.C i.C 1 1 := by
          dsimp only [firstWeakDefectCoefficient]
          norm_num only [abs_one]
          gcongr <;> linarith only [hmabs,hdm]
        _ = _ := by dsimp only [V,firstWeakDefectCoefficient]; norm_num; ring
  have hhigh : ∀ᶠ N : ℕ in atTop, ∀ i : I, QBoundedJets 3 K (F N i) := by
    filter_upwards [hsteps] with N hs i
    by_cases hi : i.e ≤ L*h/(N:ℝ)
    · have H := (qBoundedJets_firstWeakDefect_coarse (dm := i.dm) i.hf i.hf₁ i.hg i.ha i.hm
        (Real.sqrt_nonneg i.e) i.v i.w (hnorm i).1 (hnorm i).2 (hs i hi).1 (hs i hi).2).mono
        (mul_le_mul_of_nonneg_right (hcoef i).1 (sq_nonneg (Real.sqrt i.e)))
      rw [Real.sq_sqrt i.he.le] at H
      have H' := H.const_smul (i.C*i.e)⁻¹
      convert H' using 1
      · rw [abs_inv,abs_of_pos (mul_pos i.hC i.he)]
        field_simp [i.hC.ne',i.he.ne']
      · funext x
        simp only [F,hi,ite_true,GeneratorFirstDatum.error,smul_eq_mul]
    · refine ⟨hK,?_,?_⟩
      · simpa only [F,hi,ite_false] using
          (contDiff_const : ContDiff ℝ (3:ℕ) (fun _ : E => (0:ℝ)))
      · intro j hj x
        simpa [F,hi] using hK
  have hvalue : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, ∀ i : I, ∀ x, ‖F N i x‖ ≤ δ := by
    intro δ hδ
    filter_upwards [hsteps,hlim.eventually (eventually_le_nhds
      (by positivity : 0 < δ/(V+1)))] with N hs hN i x
    by_cases hi : i.e ≤ L*h/(N:ℝ)
    · have H := (abs_firstMovingAverageSource_sub_quadratic_le (dm := i.dm)
        (i.hf.of_le (by norm_num : 5 ≤ 6)) i.hf₁
        (i.hg.of_le (by norm_num : 4 ≤ 5)) (i.ha.of_le (by norm_num : 4 ≤ 5))
        i.hm (Real.sqrt_nonneg i.e) i.v i.w x (hnorm i).1 (hnorm i).2
        (hs i hi).1 (hs i hi).2).trans
        (mul_le_mul_of_nonneg_right (hcoef i).2 (pow_nonneg (Real.sqrt_nonneg i.e) 4))
      have he4 : (Real.sqrt i.e)^4 = i.e^2 := by
        rw [show (Real.sqrt i.e)^4 = ((Real.sqrt i.e)^2)^2 by ring,Real.sq_sqrt i.he.le]
      rw [he4] at H
      calc
        _ = (i.C*i.e)⁻¹*|i.error x| := by
          simp only [F,hi,ite_true,Real.norm_eq_abs,abs_mul,abs_inv,
            abs_of_pos (mul_pos i.hC i.he)]
        _ ≤ (i.C*i.e)⁻¹*((i.C*V)*i.e^2) :=
          mul_le_mul_of_nonneg_left H (inv_nonneg.mpr (mul_pos i.hC i.he).le)
        _ = V*i.e := by field_simp [i.hC.ne',i.he.ne']
        _ ≤ V*(δ/(V+1)) := mul_le_mul_of_nonneg_left (hi.trans hN) hV
        _ ≤ δ := by
          convert mul_le_of_le_one_right hδ.le
            ((div_le_one (by positivity : 0 < V+1)).mpr (by linarith : V ≤ V+1)) using 1
          ring
    · simp only [F,hi,ite_false,norm_zero]
      exact hδ.le
  filter_upwards [QBoundedJets.eventually_small_of_values F 2 hK hhigh hvalue eps heps]
    with N hN C e hC he f f₁ g a hf hf₁ hg ha m dm hm hdm v w hdir hmesh
  let i : I := ⟨C,e,m,dm,f,f₁,g,a,v,w,hC,he,hf,hf₁,hg,ha,hm,hdm,hdir⟩
  have Hi := (hN i).const_smul (C*e)
  convert Hi using 1
  · rw [abs_of_pos (mul_pos hC he)]
    ring
  · funext x
    simp only [F,i,hmesh,ite_true,GeneratorFirstDatum.error,smul_eq_mul]
    rw [← mul_assoc,mul_inv_cancel₀ (mul_pos hC he).ne',one_mul]

theorem eventually_firstMovingAverageSource_energy_le {B A C₀ h eps L : ℝ}
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hC₀ : 0 < C₀) (hh : 0 < h) (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop, ∀ (f f₁ f₂ g a q : E → ℝ) (m dm ddm : ℝ)
      (v w b : E) (e : ℝ),
      QPotential 6 B f → QBoundedJets 4 A f₁ →
      QBoundedJets 5 (C₀*h/(N:ℝ)) g → QBoundedJets 5 (C₀*h/(N:ℝ)) a →
      m ∈ Icc (0:ℝ) 1 → |dm| ≤ 1 →
      ‖v‖^2+‖w‖^2 ≤ e → e ≤ L*h/(N:ℝ) →
      QBoundedJets 2 ((eps/(N:ℝ))*e) (fun x =>
        firstTiltedAverageSource m v f f₁ g a dm w x-a x-
          fullGeneratorJet m dm ddm f f₁ f₂ g a q v w b 1 x) := by
  let δ := eps/(C₀*h+1)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  filter_upwards [normalized_firstMovingAverageDefect_spatial_eventually
    (L := L) (h := h) hB hA hδ,eventually_ge_atTop (1:ℕ)] with N hN hN1
  intro f f₁ f₂ g a q m dm ddm v w b e hf hf₁ hg ha hm hdm he hmesh
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN1
  have hC : 0 < C₀*h/(N:ℝ) := by positivity
  have he0 : 0 ≤ e := by nlinarith only [he,sq_nonneg ‖v‖,sq_nonneg ‖w‖]
  have heq : (fun x => firstTiltedAverageSource m v f f₁ g a dm w x-a x-
      fullGeneratorJet m dm ddm f f₁ f₂ g a q v w b 1 x) =
      fun x => firstTiltedAverageSource m v f f₁ g a dm w x-
        firstMovingAverageQuadratic m dm v w f f₁ g a x := by
    funext x
    rw [← firstMovingAverageQuadratic_sub_test_eq_fullGeneratorJet
      (ha.smooth.of_le (by norm_num)) m dm ddm f f₁ f₂ g q v w b x]
    ring
  rw [heq]
  by_cases hepos : 0 < e
  · apply (hN _ _ hC hepos f f₁ g a hf hf₁ hg ha m dm hm hdm v w he hmesh).mono
    have hδC : δ*(C₀*h) ≤ eps := by
      calc
        _ = eps*((C₀*h)/(C₀*h+1)) := by dsimp only [δ]; ring
        _ ≤ eps*1 := mul_le_mul_of_nonneg_left
          ((div_le_one (by positivity : 0 < C₀*h+1)).mpr (by linarith)) heps.le
        _ = eps := mul_one _
    calc
      _ = (δ*(C₀*h)/(N:ℝ))*e := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hδC hn.le) he0
  · have hezero : e = 0 := le_antisymm (le_of_not_gt hepos) he0
    have hvzero : ‖v‖ ≤ (0:ℝ) := by nlinarith only [he,hezero,sq_nonneg ‖w‖,norm_nonneg v]
    have hwzero : ‖w‖ ≤ (0:ℝ) := by nlinarith only [he,hezero,sq_nonneg ‖v‖,norm_nonneg w]
    have hv : v = 0 := norm_eq_zero.mp (le_antisymm hvzero (norm_nonneg v))
    have H := qBoundedJets_firstWeakDefect_coarse (dm := dm) (d := 0) hf hf₁ hg ha hm le_rfl
      v w hvzero hwzero (hvzero.trans (by norm_num : (0:ℝ) ≤ 1)) (by simp [hv])
    have H' := H.of_le (by norm_num : 2 ≤ 3)
    simpa only [hezero,zero_pow (by norm_num : 2 ≠ 0),mul_zero] using H'

end SKBarriers2.StepCalculus
