module

public import SKBarriers2.Corner.FrozenRowsMovingTestSource

@[expose] public section

noncomputable section
open scoped Topology

namespace SKBarriers2

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem WJets.moving_firstSource_profile {r p : ℕ} {C L δ : ℝ}
    {a : E → ℝ} {F₁ : E → E →L[ℝ] ℝ} {V₀ V₁ : E → E}
    (hp : 1 ≤ p) (ha : WJets r C p a) (hf : WJets r C p F₁)
    (hδf : WJets r C (p-1) (fun x => δ • F₁ x))
    (hV₀ : WJets r L 0 V₀) (hV₁ : WJets r L 1 V₁) :
    WJets r (C*(1+2*(2:ℝ)^r*L)) p
      (fun x => a x+F₁ x (V₀ x+δ • V₁ x)) := by
  have h₀ := (hf.clm_apply hV₀).mono le_rfl (by omega : p+0 ≤ p)
  have h₁ := (hδf.clm_apply hV₁).mono le_rfl (by omega : p-1+1 ≤ p)
  convert (ha.add h₀).add h₁ using 1
  · ring
  · funext x
    simp only [map_add,map_smul,smul_apply,smul_eq_mul]
    ring

def movingTestFirstProfileCoefficient (r p : ℕ) (A : E →L[ℝ] E) (b : E) (L : ℝ) : ℝ :=
  (1+‖A‖+‖b‖)^p*max 1 ‖A‖^r*(1+2*(2:ℝ)^r*L)

theorem WJets.moving_firstSource_affine {r p : ℕ} {C L δ : ℝ} {f a : E → ℝ}
    {V₀ V₁ : E → E} (hp : 1 ≤ p)
    (hf : WJets (r+1) C p f) (ha : WJets r C p a)
    (hδf : WJets r C (p-1) (fun x => δ • fderiv ℝ f x))
    (hV₀ : WJets r L 0 V₀) (hV₁ : WJets r L 1 V₁)
    (A : E →L[ℝ] E) (d : E) :
    WJets r (C*movingTestFirstProfileCoefficient r p A d L) p
      (fun x => a (A x+d)+fderiv ℝ f (A x+d) (V₀ x+δ • V₁ x)) := by
  let G := 1+‖A‖+‖d‖
  let M := max 1 ‖A‖^r
  let D := C*G^p*M
  have hG : 1 ≤ G := by dsimp only [G]; linarith [norm_nonneg A,norm_nonneg d]
  have hδb : WJets r D (p-1) (fun x => δ • fderiv ℝ f (A x+d)) := by
    apply (hδf.comp_affine A d).mono _ le_rfl
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hG (by omega : p-1 ≤ p)) hδf.nonneg)
      (by positivity)
  have HS := WJets.moving_firstSource_profile hp (ha.comp_affine A d)
    (hf.derivativeJets.comp_affine A d) hδb hV₀ hV₁
  convert HS using 1
  dsimp only [D,G,M,movingTestFirstProfileCoefficient]
  ring

theorem WJets.moving_firstSource_contDiff
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {r p : ℕ} {C : ℝ} {f a : E → ℝ} {Y V : X → E}
    (hf : WJets (r+1) C p f) (ha : WJets r C p a)
    (hY : ContDiff ℝ r Y) (hV : ContDiff ℝ r V) :
    ContDiff ℝ r (fun z => a (Y z)+fderiv ℝ f (Y z) (V z)) :=
  (ha.smooth.comp hY).add ((hf.derivativeJets.smooth.comp hY).clm_apply hV)

theorem WJets.moving_secondSource_profile {r p : ℕ} {C L δ : ℝ}
    {b : E → ℝ} {A₁ F₁ : E → E →L[ℝ] ℝ} {F₂ : E → E →L[ℝ] E →L[ℝ] ℝ}
    {V₀ V₁ W₀ W₁ : E → E}
    (hp : 2 ≤ p) (hδ : |δ| ≤ 1)
    (hb : WJets r C p b) (ha : WJets r C p A₁)
    (hf₁ : WJets r C p F₁) (hf₂ : WJets r C p F₂)
    (hδa : WJets r C (p-1) (fun x => δ • A₁ x))
    (hδf₁ : WJets r C (p-2) (fun x => δ • F₁ x))
    (hδf₂ : WJets r C (p-2) (fun x => δ • F₂ x))
    (hV₀ : WJets r L 0 V₀) (hV₁ : WJets r L 1 V₁)
    (hW₀ : WJets r L 0 W₀) (hW₁ : WJets r L 1 W₁) :
    WJets r (C*(1+6*(2:ℝ)^r*L+4*((2:ℝ)^r)^2*L^2)) p
      (fun x => b x+2*A₁ x (V₀ x+δ • V₁ x)+
        F₂ x (V₀ x+δ • V₁ x) (V₀ x+δ • V₁ x)+
        F₁ x (W₀ x+δ • W₁ x)) := by
  have ha₀ := ((ha.clm_apply hV₀).mono le_rfl (by omega : p+0 ≤ p)).const_smul 2
  have ha₁ := ((hδa.clm_apply hV₁).mono le_rfl (by omega : p-1+1 ≤ p)).const_smul 2
  have hf₀₀ := ((hf₂.clm_apply hV₀).clm_apply hV₀).mono le_rfl (by omega : p+0+0 ≤ p)
  have hf₀₁ := ((hδf₂.clm_apply hV₀).clm_apply hV₁).mono le_rfl (by omega : p-2+0+1 ≤ p)
  have hf₁₀ := ((hδf₂.clm_apply hV₁).clm_apply hV₀).mono le_rfl (by omega : p-2+1+0 ≤ p)
  have hδδf₂ := (hδf₂.const_smul δ).mono
    (mul_le_of_le_one_left hδf₂.nonneg hδ) le_rfl
  have hf₁₁ := ((hδδf₂.clm_apply hV₁).clm_apply hV₁).mono le_rfl (by omega : p-2+1+1 ≤ p)
  have hw₀ := (hf₁.clm_apply hW₀).mono le_rfl (by omega : p+0 ≤ p)
  have hw₁ := (hδf₁.clm_apply hW₁).mono le_rfl (by omega : p-2+1 ≤ p)
  have HS := ((((((((hb.add ha₀).add ha₁).add hf₀₀).add hf₀₁).add hf₁₀).add hf₁₁).add hw₀).add hw₁)
  convert HS using 1
  · norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 2)]
    ring
  · funext x
    simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
    ring

def movingTestSecondCoefficient (r p : ℕ) (A : E →L[ℝ] E) (b : E) (L : ℝ) : ℝ :=
  (1+‖A‖+‖b‖)^p*max 1 ‖A‖^r*
    (1+6*(2:ℝ)^r*L+4*((2:ℝ)^r)^2*L^2)

theorem WJets.moving_secondSource_affine {r p : ℕ} {C L δ : ℝ} {f a b : E → ℝ}
    {V₀ V₁ W₀ W₁ : E → E}
    (hp : 2 ≤ p) (hδ : |δ| ≤ 1)
    (hf : WJets (r+2) C p f) (ha : WJets (r+1) C p a) (hb : WJets r C p b)
    (hδa : WJets r C (p-1) (fun x => δ • fderiv ℝ a x))
    (hδf₁ : WJets r C (p-2) (fun x => δ • fderiv ℝ f x))
    (hδf₂ : WJets r C (p-2) (fun x => δ • fderiv ℝ (fderiv ℝ f) x))
    (hV₀ : WJets r L 0 V₀) (hV₁ : WJets r L 1 V₁)
    (hW₀ : WJets r L 0 W₀) (hW₁ : WJets r L 1 W₁)
    (A : E →L[ℝ] E) (d : E) :
    WJets r (C*movingTestSecondCoefficient r p A d L) p
      (fun x => b (A x+d)+2*fderiv ℝ a (A x+d) (V₀ x+δ • V₁ x)+
        fderiv ℝ (fderiv ℝ f) (A x+d) (V₀ x+δ • V₁ x) (V₀ x+δ • V₁ x)+
        fderiv ℝ f (A x+d) (W₀ x+δ • W₁ x)) := by
  let G := 1+‖A‖+‖d‖
  let M := max 1 ‖A‖^r
  let D := C*G^p*M
  have hG : 1 ≤ G := by dsimp only [G]; linarith [norm_nonneg A,norm_nonneg d]
  have hc {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      {q : ℕ} {g : E → Y} (hg : WJets r C q g) (hq : q ≤ p) :
      WJets r D q (fun x => g (A x+d)) := by
    apply (hg.comp_affine A d).mono _ le_rfl
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hG hq) hg.nonneg) (by positivity)
  have hfb := hc hb le_rfl
  have hab := hc ha.derivativeJets le_rfl
  have hf₁b := hc (hf.derivativeJets.of_le (Nat.le_succ r)) le_rfl
  have hf₂b := hc hf.derivativeJets.derivativeJets le_rfl
  have hδab := hc hδa (by omega)
  have hδf₁b := hc hδf₁ (by omega)
  have hδf₂b := hc hδf₂ (by omega)
  have HS := WJets.moving_secondSource_profile hp hδ hfb hab hf₁b hf₂b
    hδab hδf₁b hδf₂b hV₀ hV₁ hW₀ hW₁
  convert HS using 1
  dsimp only [D,G,M,movingTestSecondCoefficient]
  ring

theorem WJets.moving_secondSource_contDiff
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {r p : ℕ} {C : ℝ} {f a b : E → ℝ} {Y V W : X → E}
    (hf : WJets (r+2) C p f) (ha : WJets (r+1) C p a) (hb : WJets r C p b)
    (hY : ContDiff ℝ r Y) (hV : ContDiff ℝ r V) (hW : ContDiff ℝ r W) :
    ContDiff ℝ r (fun z => b (Y z)+2*fderiv ℝ a (Y z) (V z)+
      fderiv ℝ (fderiv ℝ f) (Y z) (V z) (V z)+fderiv ℝ f (Y z) (W z)) := by
  have haD := ha.derivativeJets.smooth
  have hfD := (hf.derivativeJets.of_le (Nat.le_succ r)).smooth
  have hfDD := hf.derivativeJets.derivativeJets.smooth
  simpa only [smul_eq_mul,Function.comp_def] using
    (((hb.smooth.comp hY).add (((haD.comp hY).clm_apply hV).const_smul (2:ℝ))).add
      (((hfDD.comp hY).clm_apply hV).clm_apply hV)).add ((hfD.comp hY).clm_apply hW)

end SKBarriers2
