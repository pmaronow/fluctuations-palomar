module

public import SKBarriers2.Corner.PathEnergyGenerator2

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic
namespace SKBarriers2.StepCalculus
local notation "E" => (Fin 3 → ℝ)
private theorem generatorSum_scaled_product {n : ℕ} {H C c : ℝ} {a b : E → ℝ}
    (ha : QBoundedJets n H a) (hb : QBoundedJets n C b) (hc : |c| ≤ 1) :
    QBoundedJets n ((2:ℝ)^n*H*C) (fun x => c*a x*b x) := by
  have H' := (ha.mul hb).const_smul c
  have H'' := H'.mono (mul_le_of_le_one_left (ha.mul hb).nonneg hc)
  convert H'' using 1
  funext x
  simp only [smul_eq_mul]
  ring

theorem qBoundedJets_generatorProductJet_642 {H C m dm ddm : ℝ} {A B : Fin 3 → E → ℝ}
    (hA₀ : QBoundedJets 6 H (A 0)) (hA₁ : QBoundedJets 4 H (A 1))
    (hA₂ : QBoundedJets 2 H (A 2))
    (hB₀ : QBoundedJets 6 C (B 0)) (hB₁ : QBoundedJets 4 C (B 1))
    (hB₂ : QBoundedJets 2 C (B 2))
    (hm : |m| ≤ 1) (hdm : |dm| ≤ 1) (hddm : |ddm| ≤ 1) :
    QBoundedJets 6 (64*H*C) (generatorProductJet m dm ddm A B 0) ∧
      QBoundedJets 4 (64*H*C) (generatorProductJet m dm ddm A B 1) ∧
      QBoundedJets 2 (64*H*C) (generatorProductJet m dm ddm A B 2) := by
  have hH := hA₀.nonneg
  have hC := hB₀.nonneg
  have hzero := generatorSum_scaled_product hA₀ hB₀ hm
  have hfirst := ((generatorSum_scaled_product (hA₀.of_le (by norm_num : 4 ≤ 6))
    (hB₀.of_le (by norm_num : 4 ≤ 6)) hdm).add
      (generatorSum_scaled_product hA₁ (hB₀.of_le (by norm_num : 4 ≤ 6)) hm)).add
        (generatorSum_scaled_product (hA₀.of_le (by norm_num : 4 ≤ 6)) hB₁ hm)
  have hsecond := (((((generatorSum_scaled_product (hA₀.of_le (by norm_num : 2 ≤ 6))
    (hB₀.of_le (by norm_num : 2 ≤ 6)) hddm).add
      ((generatorSum_scaled_product (hA₁.of_le (by norm_num : 2 ≤ 4))
        (hB₀.of_le (by norm_num : 2 ≤ 6)) hdm).const_smul 2)).add
      ((generatorSum_scaled_product (hA₀.of_le (by norm_num : 2 ≤ 6))
        (hB₁.of_le (by norm_num : 2 ≤ 4)) hdm).const_smul 2)).add
      (generatorSum_scaled_product hA₂ (hB₀.of_le (by norm_num : 2 ≤ 6)) hm)).add
      ((generatorSum_scaled_product (hA₁.of_le (by norm_num : 2 ≤ 4))
        (hB₁.of_le (by norm_num : 2 ≤ 4)) hm).const_smul 2)).add
      (generatorSum_scaled_product (hA₀.of_le (by norm_num : 2 ≤ 6)) hB₂ hm)
  refine ⟨?_,?_,?_⟩
  · convert hzero using 1 <;> norm_num [generatorProductJet]
  · convert hfirst.mono (show
      (2:ℝ)^4*H*C+(2:ℝ)^4*H*C+(2:ℝ)^4*H*C ≤ 64*H*C by
        nlinarith only [mul_nonneg hH hC]) using 1
    funext x
    simp only [generatorProductJet,Matrix.cons_val_one,Matrix.cons_val_zero]
  · convert hsecond.mono (show
      (2:ℝ)^2*H*C+|2| *((2:ℝ)^2*H*C)+|2| *((2:ℝ)^2*H*C)+
        (2:ℝ)^2*H*C+|2| *((2:ℝ)^2*H*C)+(2:ℝ)^2*H*C ≤ 64*H*C by
          norm_num
          nlinarith only [mul_nonneg hH hC]) using 1
    funext x
    norm_num [generatorProductJet,smul_eq_mul]

theorem qBoundedJets_generatorDirectionalJet_642 {H d : ℝ} {F F₁ F₂ : E → ℝ}
    (hF : QPotential 7 H F) (hF₁ : QBoundedJets 5 H F₁)
    (hF₂ : QBoundedJets 3 H F₂) (hd : 0 ≤ d) (v v₁ v₂ : E)
    (hv : ‖v‖ ≤ d) (hv₁ : ‖v₁‖ ≤ d) (hv₂ : ‖v₂‖ ≤ d) :
    QBoundedJets 6 (4*H*d) (generatorDirectionalJet F F₁ F₂ v v₁ v₂ 0) ∧
      QBoundedJets 4 (4*H*d) (generatorDirectionalJet F F₁ F₂ v v₁ v₂ 1) ∧
      QBoundedJets 2 (4*H*d) (generatorDirectionalJet F F₁ F₂ v v₁ v₂ 2) := by
  have hH := hF.nonneg
  have hzero (w : E) (hw : ‖w‖ ≤ d) :
      QBoundedJets 6 (H*d) (fun x => fderiv ℝ F x w) :=
    (hF.derivativeJets.apply_const w).mono (mul_le_mul_of_nonneg_left hw hH)
  have hfirst (w : E) (hw : ‖w‖ ≤ d) :
      QBoundedJets 4 (H*d) (fun x => fderiv ℝ F₁ x w) :=
    (hF₁.derivativeJets.apply_const w).mono (mul_le_mul_of_nonneg_left hw hH)
  have hsecond := (hF₂.derivativeJets.apply_const v).mono
    (mul_le_mul_of_nonneg_left hv hH)
  refine ⟨?_,?_,?_⟩
  · convert (hzero v hv).mono (show H*d ≤ 4*H*d by nlinarith only [mul_nonneg hH hd]) using 1
    funext x
    norm_num [generatorDirectionalJet]
  · have H' := (hfirst v hv).add ((hzero v₁ hv₁).of_le (by norm_num : 4 ≤ 6))
    convert H'.mono (show H*d+H*d ≤ 4*H*d by nlinarith only [mul_nonneg hH hd]) using 1
    funext x
    norm_num [generatorDirectionalJet]
  · have H' := (hsecond.add (((hfirst v₁ hv₁).of_le (by norm_num : 2 ≤ 4)).const_smul 2)).add
      ((hzero v₂ hv₂).of_le (by norm_num : 2 ≤ 6))
    convert H' using 1
    · norm_num
      ring
    · funext x
      norm_num [generatorDirectionalJet,smul_eq_mul]

def generatorHessianJet (g a q : E → ℝ) (v w b : E) : Fin 3 → E → ℝ :=
  ![fun x => fderiv ℝ (fderiv ℝ g) x v v / 2,
    fun x => fderiv ℝ (fderiv ℝ a) x v v / 2 + fderiv ℝ (fderiv ℝ g) x v w,
    fun x => fderiv ℝ (fderiv ℝ q) x v v / 2 + 2 * fderiv ℝ (fderiv ℝ a) x v w +
      fderiv ℝ (fderiv ℝ g) x w w + fderiv ℝ (fderiv ℝ g) x v b]

private theorem generator_hessian_common {n : ℕ} {C d : ℝ} {g : E → ℝ}
    (hg : QBoundedJets (n + 2) C g) {v w : E} (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d) :
    QBoundedJets n (C * d ^ 2) (fun x => fderiv ℝ (fderiv ℝ g) x v w) := by
  have H := (hg.derivativeJets.derivativeJets.apply_const v).apply_const w
  apply H.mono
  have hd : 0 ≤ d := (norm_nonneg _).trans hv
  calc
    _ = C * (‖v‖ * ‖w‖) := by ring
    _ ≤ C * (d * d) := mul_le_mul_of_nonneg_left
      (mul_le_mul hv hw (norm_nonneg _) hd) hg.nonneg
    _ = _ := by ring

theorem qBoundedJets_generatorHessianJet_642 {C d : ℝ} {g a q : E → ℝ}
    (hg : QBoundedJets 8 C g) (ha : QBoundedJets 6 C a) (hq : QBoundedJets 4 C q)
    {v w b : E} (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d) (hb : ‖b‖ ≤ d) :
    QBoundedJets 6 (5 * C * d ^ 2) (generatorHessianJet g a q v w b 0) ∧
      QBoundedJets 4 (5 * C * d ^ 2) (generatorHessianJet g a q v w b 1) ∧
      QBoundedJets 2 (5 * C * d ^ 2) (generatorHessianJet g a q v w b 2) := by
  have hC := hg.nonneg
  have h0 := (generator_hessian_common hg hv hv).const_smul (1 / 2 : ℝ)
  have h1 := ((generator_hessian_common ha hv hv).const_smul (1 / 2 : ℝ)).add
    (generator_hessian_common (hg.of_le (by norm_num : 6 ≤ 8)) hv hw)
  have h2 := ((((generator_hessian_common hq hv hv).const_smul (1 / 2 : ℝ)).add
    ((generator_hessian_common (ha.of_le (by norm_num : 4 ≤ 6)) hv hw).const_smul 2)).add
    (generator_hessian_common (hg.of_le (by norm_num : 4 ≤ 8)) hw hw)).add
    (generator_hessian_common (hg.of_le (by norm_num : 4 ≤ 8)) hv hb)
  refine ⟨?_, ?_, ?_⟩
  · convert h0.mono (show |(1 / 2 : ℝ)| * (C * d ^ 2) ≤ 5 * C * d ^ 2 by
      norm_num
      nlinarith only [mul_nonneg hC (sq_nonneg d)]) using 1
    funext x
    simp only [generatorHessianJet, Matrix.cons_val_zero, smul_eq_mul]
    ring
  · convert h1.mono (show |(1 / 2 : ℝ)| * (C * d ^ 2) + C * d ^ 2 ≤ 5 * C * d ^ 2 by
      norm_num
      nlinarith only [mul_nonneg hC (sq_nonneg d)]) using 1
    funext x
    simp only [generatorHessianJet, Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul]
    ring
  · convert h2.mono (show |(1 / 2 : ℝ)| * (C * d ^ 2) + |(2 : ℝ)| * (C * d ^ 2) +
        C * d ^ 2 + C * d ^ 2 ≤ 5 * C * d ^ 2 by
      norm_num
      nlinarith only [mul_nonneg hC (sq_nonneg d)]) using 1
    funext x
    norm_num [generatorHessianJet, smul_eq_mul]
    ring

def fullGeneratorJet (m dm ddm : ℝ) (f F Q g a q : E → ℝ) (v w b : E) :
    Fin 3 → E → ℝ :=
  fun c x => generatorProductJet m dm ddm
    (generatorDirectionalJet f F Q v w b) (generatorDirectionalJet g a q v w b) c x +
      generatorHessianJet g a q v w b c x

theorem qBoundedJets_fullGeneratorJet {B A H C e m dm ddm : ℝ}
    {f F Q g a q : E → ℝ}
    (hf : QPotential 7 B f) (hF : QBoundedJets 5 A F) (hQ : QBoundedJets 3 H Q)
    (hg : QBoundedJets 8 C g) (ha : QBoundedJets 6 C a) (hq : QBoundedJets 4 C q)
    (hm : |m| ≤ 1) (hdm : |dm| ≤ 1) (hddm : |ddm| ≤ 1)
    (v w b : E) (he : ‖v‖ ^ 2 + ‖w‖ ^ 2 + ‖b‖ ^ 2 ≤ e) :
    let K := (1024 * (B + A + H) + 5) * C * e
    QBoundedJets 6 K (fullGeneratorJet m dm ddm f F Q g a q v w b 0) ∧
      QBoundedJets 4 K (fullGeneratorJet m dm ddm f F Q g a q v w b 1) ∧
      QBoundedJets 2 K (fullGeneratorJet m dm ddm f F Q g a q v w b 2) := by
  let D := B + A + H
  have hB := hf.nonneg
  have hA := hF.nonneg
  have hH := hQ.nonneg
  have hC := hg.nonneg
  have he0 : 0 ≤ e := by nlinarith only [he, sq_nonneg ‖v‖, sq_nonneg ‖w‖, sq_nonneg ‖b‖]
  have hv : ‖v‖ ≤ Real.sqrt e := Real.le_sqrt_of_sq_le
    (by nlinarith only [he, sq_nonneg ‖w‖, sq_nonneg ‖b‖])
  have hw : ‖w‖ ≤ Real.sqrt e := Real.le_sqrt_of_sq_le
    (by nlinarith only [he, sq_nonneg ‖v‖, sq_nonneg ‖b‖])
  have hb : ‖b‖ ≤ Real.sqrt e := Real.le_sqrt_of_sq_le
    (by nlinarith only [he, sq_nonneg ‖v‖, sq_nonneg ‖w‖])
  have hfD := hf.mono (show B ≤ D by dsimp only [D]; linarith)
  have hFD := hF.mono (show A ≤ D by dsimp only [D]; linarith)
  have hQD := hQ.mono (show H ≤ D by dsimp only [D]; linarith)
  obtain ⟨h0, h1, h2⟩ := qBoundedJets_generatorDirectionalJet_642 hfD hFD hQD
    (Real.sqrt_nonneg e) v w b hv hw hb
  obtain ⟨hg0, hg1, hg2⟩ := qBoundedJets_generatorDirectionalJet_642
    (qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by norm_num : 7 ≤ 8))).potential
    (ha.of_le (by norm_num : 5 ≤ 6)) (hq.of_le (by norm_num : 3 ≤ 4))
    (Real.sqrt_nonneg e) v w b hv hw hb
  obtain ⟨hp0, hp1, hp2⟩ := qBoundedJets_generatorProductJet_642 h0 h1 h2 hg0 hg1 hg2 hm hdm hddm
  obtain ⟨hh0, hh1, hh2⟩ := qBoundedJets_generatorHessianJet_642 hg ha hq hv hw hb
  have hcoef : 64 * (4 * D * Real.sqrt e) * (4 * C * Real.sqrt e) + 5 * C * (Real.sqrt e) ^ 2 =
      (1024 * (B + A + H) + 5) * C * e := by
    rw [show 64 * (4 * D * Real.sqrt e) * (4 * C * Real.sqrt e) =
      1024 * D * C * (Real.sqrt e) ^ 2 by ring, Real.sq_sqrt he0]
    dsimp only [D]
    ring
  have H0 := hp0.add hh0
  have H1 := hp1.add hh1
  have H2 := hp2.add hh2
  rw [hcoef] at H0 H1 H2
  exact ⟨H0, H1, H2⟩

def fullGeneratorCurveSumJet (f F Q g a q : E → ℝ) (k : ℝ) :
    List (ℝ → ℝ × E) → Fin 3 → E → ℝ
  | [], _, _ => 0
  | p :: ps, c, x =>
      fullGeneratorJet (p k).1 (deriv (fun t => (p t).1) k)
        (deriv (deriv (fun t => (p t).1)) k) f F Q g a q
        (p k).2 (deriv (fun t => (p t).2) k)
        (deriv (deriv (fun t => (p t).2)) k) c x +
          fullGeneratorCurveSumJet f F Q g a q k ps c x

theorem qBoundedJets_fullGeneratorCurveSumJet {B A H C : ℝ}
    {f F Q g a q : E → ℝ}
    (hf : QPotential 7 B f) (hF : QBoundedJets 5 A F) (hQ : QBoundedJets 3 H Q)
    (hg : QBoundedJets 8 C g) (ha : QBoundedJets 6 C a) (hq : QBoundedJets 4 C q)
    (k : ℝ) (ps : List (ℝ → ℝ × E))
    (hm : ∀ p ∈ ps, |(p k).1| ≤ 1 ∧ |deriv (fun t => (p t).1) k| ≤ 1 ∧
      |deriv (deriv (fun t => (p t).1)) k| ≤ 1) :
    let K := (1024 * (B + A + H) + 5) * C *
      (ps.map (fun p => ‖(p k).2‖ ^ 2 + ‖deriv (fun t => (p t).2) k‖ ^ 2 +
        ‖deriv (deriv (fun t => (p t).2)) k‖ ^ 2)).sum
    QBoundedJets 6 K (fullGeneratorCurveSumJet f F Q g a q k ps 0) ∧
      QBoundedJets 4 K (fullGeneratorCurveSumJet f F Q g a q k ps 1) ∧
      QBoundedJets 2 K (fullGeneratorCurveSumJet f F Q g a q k ps 2) := by
  induction ps with
  | nil =>
    have hzero (n : ℕ) : QBoundedJets n 0 (fun _ : E => (0 : ℝ)) := by
      refine ⟨le_rfl, contDiff_const, ?_⟩
      intro j hj x
      simp
    simp only [List.map_nil, List.sum_nil, mul_zero]
    exact ⟨hzero 6, hzero 4, hzero 2⟩
  | cons p ps ih =>
    have hpm := hm p List.mem_cons_self
    have htail := ih (fun p hp => hm p (List.mem_cons_of_mem _ hp))
    have hhead := qBoundedJets_fullGeneratorJet hf hF hQ hg ha hq hpm.1 hpm.2.1 hpm.2.2
      (p k).2 (deriv (fun t => (p t).2) k)
      (deriv (deriv (fun t => (p t).2)) k) le_rfl
    exact ⟨by simpa only [fullGeneratorCurveSumJet, List.map_cons, List.sum_cons, mul_add]
        using hhead.1.add htail.1,
      by simpa only [fullGeneratorCurveSumJet, List.map_cons, List.sum_cons, mul_add]
        using hhead.2.1.add htail.2.1,
      by simpa only [fullGeneratorCurveSumJet, List.map_cons, List.sum_cons, mul_add]
        using hhead.2.2.add htail.2.2⟩

end SKBarriers2.StepCalculus
