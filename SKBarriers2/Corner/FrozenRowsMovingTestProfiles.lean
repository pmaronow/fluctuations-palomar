module

public import SKBarriers2.Corner.FrozenRowsMovingSecondSource

@[expose] public section

noncomputable section
open scoped BigOperators Topology

namespace SKBarriers2
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def affineMovingRawFirst (f a : E → ℝ) (A : E →L[ℝ] E) (d v : E)
    (δ : ℝ) (V₀ : ℝ → E) (V₁ : E → E) (t : ℝ) (x : E) : ℝ :=
  a (A x+d+t • v)+fderiv ℝ f (A x+d+t • v) (V₀ t+δ • V₁ x)

def affineMovingCenteredValue (f : E → ℝ) (A : E →L[ℝ] E) (d v : E)
    (t : ℝ) (x : E) : ℝ := f (A x+d+t • v)-f (A x+d)

def affineMovingCenteredFirst (f a : E → ℝ) (A : E →L[ℝ] E) (d v : E)
    (δ : ℝ) (V₀ : ℝ → E) (V₁ : E → E) (t : ℝ) (x : E) : ℝ :=
  affineMovingRawFirst f a A d v δ V₀ V₁ t x-
    affineMovingRawFirst f a A d v δ V₀ V₁ 0 x

def affineMovingRawSecond (f a b : E → ℝ) (A : E →L[ℝ] E) (d v : E)
    (δ : ℝ) (V₀ W₀ : ℝ → E) (V₁ W₁ : E → E) (t : ℝ) (x : E) : ℝ :=
  b (A x+d+t • v)+2*fderiv ℝ a (A x+d+t • v) (V₀ t+δ • V₁ x)+
    fderiv ℝ (fderiv ℝ f) (A x+d+t • v) (V₀ t+δ • V₁ x) (V₀ t+δ • V₁ x)+
    fderiv ℝ f (A x+d+t • v) (W₀ t+δ • W₁ x)

structure MovingTestProfiles (r : ℕ) (C : ℝ) (p : ℕ) (δ : ℝ)
    (c a b : E → ℝ) : Prop where
  value : WJets r C p c
  first : WJets r C p a
  second : WJets r C p b
  coarse_value : WJets r C (p-2) (fun x => δ*c x)
  coarse_first : WJets r C (p-1) (fun x => δ*a x)

theorem MovingTestProfiles.mono {r p : ℕ} {C D δ : ℝ} {c a b : E → ℝ}
    (hf : MovingTestProfiles r C p δ c a b) (hCD : C ≤ D) :
    MovingTestProfiles r D p δ c a b :=
  ⟨hf.value.mono hCD le_rfl,hf.first.mono hCD le_rfl,hf.second.mono hCD le_rfl,
    hf.coarse_value.mono hCD le_rfl,hf.coarse_first.mono hCD le_rfl⟩

def movingTestCenteredSplitCoefficient (r p : ℕ) (A : E →L[ℝ] E) (d v : E) : ℝ :=
  ‖v‖*(1+‖v‖)^p*(1+‖A‖+‖d‖)^p*max 1 ‖A‖^r

theorem WQ.affine_noise_centered_jets_split {r p : ℕ} {B : ℝ} {f : E → ℝ}
    (hf : WQ (r+1) B p f) (A : E →L[ℝ] E) (d v : E) (t : ℝ) :
    WJets r (B*movingTestCenteredSplitCoefficient r p A d v*(1+|t|)^(p+1)) p
      (fun x => f (A x+d+t • v)-f (A x+d)) := by
  have H := (hf.increment (t • v)).comp_affine A d
  have hB := hf.nonneg
  have hnoise : 1+|t| * ‖v‖ ≤ (1+‖v‖)*(1+|t|) := by
    nlinarith [norm_nonneg v,abs_nonneg t]
  have hnorm : |t| * ‖v‖ ≤ (1+|t|)*‖v‖ := by
    exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg t]) (norm_nonneg v)
  apply H.mono _ le_rfl
  rw [norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ B*((1+|t|)*‖v‖)*((1+‖v‖)*(1+|t|))^p*
        (1+‖A‖+‖d‖)^p*max 1 ‖A‖^r := by gcongr
    _ = _ := by
      dsimp only [movingTestCenteredSplitCoefficient]
      rw [mul_pow,pow_succ]
      ring

def movingTestProfileBudgets (r p : ℕ) (A : E →L[ℝ] E) (d v : E) (L t : ℝ) : Fin 8 → ℝ :=
  ![(1+‖A‖+‖d+t • v‖)^p*max 1 ‖A‖^r,
    (1+‖A‖+‖d‖)^p*max 1 ‖A‖^r,
    movingTestFirstProfileCoefficient r p A (d+t • v) L,
    movingTestFirstProfileCoefficient r p A d L,
    movingTestSecondCoefficient r p A (d+t • v) L,
    movingTestCenteredSplitCoefficient r (p-2) A d v*(1+|t|)^(p-2+1),
    movingTestFirstProfileCoefficient r (p-1) A (d+t • v) L,
    movingTestFirstProfileCoefficient r (p-1) A d L]

def movingTestProfileCoefficient (r p : ℕ) (A : E →L[ℝ] E) (d v : E) (L t : ℝ) : ℝ :=
  2*∑ i : Fin 8, movingTestProfileBudgets r p A d v L t i

private theorem movingTestProfileBudgets_nonneg (r p : ℕ) (A : E →L[ℝ] E)
    (d v : E) {L : ℝ} (hL : 0 ≤ L) (t : ℝ) (i : Fin 8) :
    0 ≤ movingTestProfileBudgets r p A d v L t i := by
  fin_cases i <;> norm_num [movingTestProfileBudgets,movingTestFirstProfileCoefficient,
    movingTestSecondCoefficient,movingTestCenteredSplitCoefficient] <;> positivity

private theorem moving_scaled_first_profile {r p : ℕ} {C L δ : ℝ} {f a : E → ℝ}
    {V₀ V₁ : E → E} (hp : 2 ≤ p) (hδ : |δ| ≤ 1)
    (ha : WJets r C (p-1) (fun x => δ*a x))
    (hf : WJets r C (p-2) (fun x => δ • fderiv ℝ f x))
    (hV₀ : WJets r L 0 V₀) (hV₁ : WJets r L 1 V₁)
    (A : E →L[ℝ] E) (d : E) :
    WJets r (C*movingTestFirstProfileCoefficient r (p-1) A d L) (p-1)
      (fun x => δ*(a (A x+d)+fderiv ℝ f (A x+d) (V₀ x+δ • V₁ x))) := by
  let G := 1+‖A‖+‖d‖
  let M := max 1 ‖A‖^r
  let D := C*G^(p-1)*M
  have hG : 1 ≤ G := by dsimp only [G]; linarith [norm_nonneg A,norm_nonneg d]
  have hF : WJets r D (p-2) (fun x => δ • fderiv ℝ f (A x+d)) := by
    apply (hf.comp_affine A d).mono _ le_rfl
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hG (by omega : p-2 ≤ p-1)) hf.nonneg)
      (by positivity)
  have hFF := (hF.const_smul δ).mono (mul_le_of_le_one_left hF.nonneg hδ) le_rfl
  have hFF' : WJets r D (p-1-1) (fun x => δ • (δ • fderiv ℝ f (A x+d))) := by
    convert hFF using 1
  have HS := WJets.moving_firstSource_profile (by omega : 1 ≤ p-1)
    (ha.comp_affine A d) (hF.mono le_rfl (by omega : p-2 ≤ p-1)) hFF' hV₀ hV₁
  convert HS using 1
  · dsimp only [D,G,M,movingTestFirstProfileCoefficient]
    ring
  · funext x
    simp only [smul_apply,smul_eq_mul]
    ring

theorem movingTestProfiles_affine {r p : ℕ} {C L δ t : ℝ} {f a b : E → ℝ}
    {V₀ W₀ : ℝ → E} {V₁ W₁ : E → E}
    (hp : 2 ≤ p) (hδ : |δ| ≤ 1)
    (hf : WJets (r+2) C p f) (ha : WJets (r+1) C p a) (hb : WJets r C p b)
    (hδf : WQ (r+1) C (p-2) (fun x => δ*f x))
    (hδf₁ : WJets r C (p-2) (fun x => δ • fderiv ℝ f x))
    (hδf₂ : WJets r C (p-2) (fun x => δ • fderiv ℝ (fderiv ℝ f) x))
    (hδa : WJets r C (p-1) (fun x => δ*a x))
    (hδDa : WJets r C (p-1) (fun x => δ • fderiv ℝ a x))
    (hVt : WJets r L 0 (fun _ : E => V₀ t))
    (hVz : WJets r L 0 (fun _ : E => V₀ 0)) (hV₁ : WJets r L 1 V₁)
    (hWt : WJets r L 0 (fun _ : E => W₀ t)) (hW₁ : WJets r L 1 W₁)
    (A : E →L[ℝ] E) (d v : E) :
    MovingTestProfiles r (C*movingTestProfileCoefficient r p A d v L t) p δ
      (affineMovingCenteredValue f A d v t)
      (affineMovingCenteredFirst f a A d v δ V₀ V₁ t)
      (affineMovingRawSecond f a b A d v δ V₀ W₀ V₁ W₁ t) := by
  let K := movingTestProfileBudgets r p A d v L t
  let S := ∑ i : Fin 8, K i
  have hC := hf.nonneg
  have hL := hV₁.nonneg
  have hK (i : Fin 8) : 0 ≤ K i := movingTestProfileBudgets_nonneg r p A d v hL t i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => hK i)
  have hKS (i : Fin 8) : K i ≤ S := Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ i)
  have hpair (i j : Fin 8) : C*K i+C*K j ≤ C*movingTestProfileCoefficient r p A d v L t := by
    change C*K i+C*K j ≤ C*(2*S)
    nlinarith only [mul_le_mul_of_nonneg_left (hKS i) hC,mul_le_mul_of_nonneg_left (hKS j) hC]
  have hsingle (i : Fin 8) : C*K i ≤ C*movingTestProfileCoefficient r p A d v L t := by
    change C*K i ≤ C*(2*S)
    nlinarith only [mul_le_mul_of_nonneg_left (hKS i) hC,mul_nonneg hC hS]
  have hf₀ : WJets r C p f := hf.of_le (by omega)
  have hfirst (z : ℝ) (hvz : WJets r L 0 (fun _ : E => V₀ z)) :=
    WJets.moving_firstSource_affine (by omega : 1 ≤ p)
      (hf.of_le (by omega : r+1 ≤ r+2)) (ha.of_le (Nat.le_succ r))
      (hδf₁.mono le_rfl (by omega : p-2 ≤ p-1)) hvz hV₁ A (d+z • v)
  have hfirstt := hfirst t hVt
  have hfirstz := hfirst 0 hVz
  have hsecond := WJets.moving_secondSource_affine hp hδ hf ha hb hδDa hδf₁ hδf₂
    hVt hV₁ hWt hW₁ A (d+t • v)
  have hcent := hδf.affine_noise_centered_jets_split A d v t
  have hcoarset := moving_scaled_first_profile hp hδ hδa hδf₁ hVt hV₁ A (d+t • v)
  have hcoarsez := moving_scaled_first_profile hp hδ hδa hδf₁ hVz hV₁ A d
  refine ⟨?_,?_,?_,?_,?_⟩
  · have H := (hf₀.comp_affine A (d+t • v)).sub (hf₀.comp_affine A d)
    have H' : WJets r (C*K 0+C*K 1) p (affineMovingCenteredValue f A d v t) := by
      convert H using 1
      · norm_num [K,movingTestProfileBudgets]
        ring
      · funext x
        simp only [affineMovingCenteredValue,add_assoc]
    exact H'.mono (hpair 0 1) le_rfl
  · have H := hfirstt.sub hfirstz
    have H' : WJets r (C*K 2+C*K 3) p
        (affineMovingCenteredFirst f a A d v δ V₀ V₁ t) := by
      convert H using 1
      · norm_num [K,movingTestProfileBudgets]
      · funext x
        simp only [affineMovingCenteredFirst,affineMovingRawFirst,add_assoc,zero_smul,add_zero]
    exact H'.mono (hpair 2 3) le_rfl
  · have H' : WJets r (C*K 4) p (affineMovingRawSecond f a b A d v δ V₀ W₀ V₁ W₁ t) := by
      convert hsecond using 1
      · norm_num [K,movingTestProfileBudgets]
      · funext x
        simp only [affineMovingRawSecond,add_assoc]
    exact H'.mono (hsingle 4) le_rfl
  · have H' : WJets r (C*K 5) (p-2) (fun x => δ*affineMovingCenteredValue f A d v t x) := by
      convert hcent using 1
      · norm_num [K,movingTestProfileBudgets]
        ring
      · funext x
        dsimp only [affineMovingCenteredValue]
        ring
    exact H'.mono (hsingle 5) le_rfl
  · have H := hcoarset.sub hcoarsez
    have H' : WJets r (C*K 6+C*K 7) (p-1)
        (fun x => δ*affineMovingCenteredFirst f a A d v δ V₀ V₁ t x) := by
      convert H using 1
      · norm_num [K,movingTestProfileBudgets]
      · funext x
        simp only [affineMovingCenteredFirst,affineMovingRawFirst,add_assoc,zero_smul,add_zero]
        ring
    exact H'.mono (hpair 6 7) le_rfl

theorem movingValue_affine_profile {r p : ℕ} {C L t : ℝ} {f : E → ℝ}
    (hf : WJets r C p f) (hL : 0 ≤ L) (A : E →L[ℝ] E) (d v : E) :
    WJets r (C*movingTestProfileCoefficient r p A d v L t) p
      (fun x => f (A x+d+t • v)) := by
  let K := movingTestProfileBudgets r p A d v L t
  let S := ∑ i : Fin 8, K i
  have hK (i : Fin 8) : 0 ≤ K i := movingTestProfileBudgets_nonneg r p A d v hL t i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => hK i)
  have hKS : K 0 ≤ S := Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ 0)
  have hbound : C*((1+‖A‖+‖d+t • v‖)^p*max 1 ‖A‖^r) ≤
      C*movingTestProfileCoefficient r p A d v L t := by
    have H : C*K 0 ≤ C*(2*S) := by
      nlinarith only [mul_le_mul_of_nonneg_left hKS hf.nonneg,mul_nonneg hf.nonneg hS]
    convert H using 1
    · norm_num [K,movingTestProfileBudgets]
    · rfl
  convert (hf.comp_affine A (d+t • v)).mono (by simpa only [mul_assoc] using hbound) le_rfl using 1
  funext x
  rw [add_assoc]

theorem movingValue_affine_contDiff {r p : ℕ} {C : ℝ} {f : E → ℝ}
    (hf : WJets r C p f) (A : E →L[ℝ] E) (d v : E) :
    ContDiff ℝ r (fun z : ℝ × E => f (A z.2+d+z.1 • v)) :=
  hf.smooth.comp (by fun_prop)

theorem movingRawFirst_affine_profile {r p : ℕ} {C L δ t : ℝ} {f a : E → ℝ}
    {V₀ : ℝ → E} {V₁ : E → E} (hp : 1 ≤ p)
    (hf : WJets (r+1) C p f) (ha : WJets r C p a)
    (hδf : WJets r C (p-1) (fun x => δ • fderiv ℝ f x))
    (hV₀ : WJets r L 0 (fun _ : E => V₀ t)) (hV₁ : WJets r L 1 V₁)
    (A : E →L[ℝ] E) (d v : E) :
    WJets r (C*movingTestProfileCoefficient r p A d v L t) p
      (affineMovingRawFirst f a A d v δ V₀ V₁ t) := by
  let K := movingTestProfileBudgets r p A d v L t
  let S := ∑ i : Fin 8, K i
  have hK (i : Fin 8) : 0 ≤ K i := movingTestProfileBudgets_nonneg r p A d v hV₁.nonneg t i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => hK i)
  have hKS : K 2 ≤ S := Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ 2)
  have hbound : C*movingTestFirstProfileCoefficient r p A (d+t • v) L ≤
      C*movingTestProfileCoefficient r p A d v L t := by
    have H : C*K 2 ≤ C*(2*S) := by
      nlinarith only [mul_le_mul_of_nonneg_left hKS hf.nonneg,mul_nonneg hf.nonneg hS]
    convert H using 1
    · norm_num [K,movingTestProfileBudgets]
    · rfl
  have HS := WJets.moving_firstSource_affine hp hf ha hδf hV₀ hV₁ A (d+t • v)
  convert HS.mono hbound le_rfl using 1
  funext x
  simp only [affineMovingRawFirst,add_assoc]

theorem affineMovingRawFirst_contDiff {r p : ℕ} {C δ : ℝ} {f a : E → ℝ}
    {V₀ : ℝ → E} {V₁ : E → E}
    (hf : WJets (r+1) C p f) (ha : WJets r C p a)
    (hV₀ : ContDiff ℝ r V₀) (hV₁ : ContDiff ℝ r V₁)
    (A : E →L[ℝ] E) (d v : E) :
    ContDiff ℝ r (fun z : ℝ × E => affineMovingRawFirst f a A d v δ V₀ V₁ z.1 z.2) := by
  have hY : ContDiff ℝ r (fun z : ℝ × E => A z.2+d+z.1 • v) := by fun_prop
  have hV : ContDiff ℝ r (fun z : ℝ × E => V₀ z.1+δ • V₁ z.2) :=
    (hV₀.comp contDiff_fst).add ((hV₁.comp contDiff_snd).const_smul δ)
  exact WJets.moving_firstSource_contDiff hf ha hY hV

theorem movingTestProfiles_contDiff {r p : ℕ} {C δ : ℝ} {f a b : E → ℝ}
    {V₀ W₀ : ℝ → E} {V₁ W₁ : E → E}
    (hf : WJets (r+2) C p f) (ha : WJets (r+1) C p a) (hb : WJets r C p b)
    (hV₀ : ContDiff ℝ r V₀) (hW₀ : ContDiff ℝ r W₀)
    (hV₁ : ContDiff ℝ r V₁) (hW₁ : ContDiff ℝ r W₁)
    (A : E →L[ℝ] E) (d v : E) :
    ContDiff ℝ r (fun z : ℝ × E => affineMovingCenteredValue f A d v z.1 z.2) ∧
    ContDiff ℝ r (fun z : ℝ × E => affineMovingCenteredFirst f a A d v δ V₀ V₁ z.1 z.2) ∧
    ContDiff ℝ r (fun z : ℝ × E => affineMovingRawSecond f a b A d v δ V₀ W₀ V₁ W₁ z.1 z.2) := by
  have hY : ContDiff ℝ r (fun z : ℝ × E => A z.2+d+z.1 • v) := by fun_prop
  have hV : ContDiff ℝ r (fun z : ℝ × E => V₀ z.1+δ • V₁ z.2) :=
    (hV₀.comp contDiff_fst).add ((hV₁.comp contDiff_snd).const_smul δ)
  have hW : ContDiff ℝ r (fun z : ℝ × E => W₀ z.1+δ • W₁ z.2) :=
    (hW₀.comp contDiff_fst).add ((hW₁.comp contDiff_snd).const_smul δ)
  have hraw := WJets.moving_firstSource_contDiff (hf.of_le (by omega : r+1 ≤ r+2))
    (ha.of_le (Nat.le_succ r)) hY hV
  have hraw₀ : ContDiff ℝ r (fun z : ℝ × E =>
      a (A z.2+d)+fderiv ℝ f (A z.2+d) (V₀ 0+δ • V₁ z.2)) := by
    simpa only [Function.comp_def,zero_smul,add_zero] using
      hraw.comp (by fun_prop : ContDiff ℝ r (fun z : ℝ × E => ((0:ℝ),z.2)))
  refine ⟨?_,?_,?_⟩
  · have hs := (hf.of_le (by omega : r ≤ r+2)).smooth
    exact (hs.comp hY).sub (hs.comp (by fun_prop))
  · simpa only [affineMovingCenteredFirst,affineMovingRawFirst,zero_smul,add_zero] using hraw.sub hraw₀
  · exact WJets.moving_secondSource_contDiff hf ha hb hY hV hW

end SKBarriers2
