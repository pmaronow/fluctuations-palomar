module

public import SKBarriers2.Corner.PathEnergyAssembly

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem qBoundedJets_pathGenerator_order {n : ℕ} {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential (n+1) B f) (hg : QBoundedJets (n+2) C g)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (v : E) :
    QBoundedJets n (((2:ℝ)^n*B+1)*C*‖v‖^2) (pathGenerator m v f g) := by
  have hdF := hf.derivativeJets.apply_const v
  have hdG := (hg.derivativeJets.of_le (by omega : n ≤ n+1)).apply_const v
  have hprod := (hdF.mul hdG).const_smul m
  have hdd : QBoundedJets n (C*‖v‖^2) (directionalJet v 2 g) :=
    qBoundedJets_iff_qBddSmooth.mpr (directionalJet_smooth (r := n) 1
      (qBoundedJets_iff_qBddSmooth.mp hg).potential v)
  have H := hprod.add (hdd.const_smul (1/2:ℝ))
  have he : pathGenerator m v f g = fun x =>
      m*(fderiv ℝ f x v*fderiv ℝ g x v)+(1/2:ℝ)*directionalJet v 2 g x := by
    funext x
    dsimp only [pathGenerator]
    ring
  rw [he]
  apply H.mono
  rw [abs_of_nonneg hm.1,abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  have hB := hf.nonneg
  have hC := hg.nonneg
  calc
    _ ≤ (2:ℝ)^n*(B*‖v‖)*(C*‖v‖)+(C*‖v‖^2) := by
      apply add_le_add
      · exact mul_le_of_le_one_left (by positivity) hm.2
      · exact mul_le_of_le_one_left (by positivity) (by norm_num)
    _ = _ := by ring

theorem qBoundedJets_pathGeneratorSum_order {n : ℕ} {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential (n+1) B f) (hg : QBoundedJets (n+2) C g)
    (ps : List (ℝ × E)) (hm : ∀ p ∈ ps, p.1 ∈ Icc (0:ℝ) 1) :
    QBoundedJets n (((2:ℝ)^n*B+1)*C*chainEnergy ps) (pathGeneratorSum f g ps) := by
  induction ps with
  | nil =>
    refine ⟨by simp [chainEnergy],contDiff_const,?_⟩
    intro j hj x
    simp [pathGeneratorSum,chainEnergy]
  | cons p ps ih =>
    have hhead := qBoundedJets_pathGenerator_order hf hg (hm p (by simp)) p.2
    have htail := ih (fun q hq => hm q (by simp [hq]))
    simpa only [pathGeneratorSum,chainEnergy_cons,mul_add] using hhead.add htail

theorem pathGenerator_sub_potential {f F g : E → ℝ}
    (hf : Differentiable ℝ f) (hF : Differentiable ℝ F) (m : ℝ) (v x : E) :
    pathGenerator m v F g x-pathGenerator m v f g x =
      m*fderiv ℝ (fun y => F y-f y) x v*fderiv ℝ g x v := by
  rw [fderiv_fun_sub (hF x) (hf x)]
  simp only [sub_apply,pathGenerator]
  ring

theorem qBoundedJets_pathGenerator_sub_order {n : ℕ} {B C H : ℝ}
    {f F g : E → ℝ} (hf : QPotential (n+1) B f) (hF : QPotential (n+1) B F)
    (hdiff : QBoundedJets (n+1) H (fun x => F x-f x))
    (hg : QBoundedJets (n+1) C g) {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (v : E) :
    QBoundedJets n ((2:ℝ)^n*H*C*‖v‖^2)
      (fun x => pathGenerator m v F g x-pathGenerator m v f g x) := by
  have hprod := ((hdiff.derivativeJets.apply_const v).mul
    (hg.derivativeJets.apply_const v)).const_smul m
  have he : (fun x => pathGenerator m v F g x-pathGenerator m v f g x) =
      fun x => m*(fderiv ℝ (fun y => F y-f y) x v*fderiv ℝ g x v) := by
    funext x
    rw [pathGenerator_sub_potential (hf.smooth.differentiable (by simp))
      (hF.smooth.differentiable (by simp))]
    ring
  rw [he]
  apply hprod.mono
  rw [abs_of_nonneg hm.1]
  calc
    _ ≤ (2:ℝ)^n*(H*‖v‖)*(C*‖v‖) :=
      mul_le_of_le_one_left (by positivity [hdiff.nonneg,hg.nonneg]) hm.2
    _ = _ := by ring

theorem qBoundedJets_firstTiltedAverageSource_energy {B A C D R e : ℝ}
    {f F g a : E → ℝ} (hf : QPotential 5 B f) (hF : QBoundedJets 3 A F)
    (hg : QBoundedJets 4 C g) (ha : QBoundedJets 2 D a)
    (hR : 0 ≤ R) (hAR : A ≤ R) {m dm : ℝ} (hm : m ∈ Icc (0:ℝ) 1)
    (hdm : |dm| ≤ 1) (v w : E) (hv : ‖v‖ ≤ 1)
    (hsmall : m*(B*‖v‖^2) ≤ 1/2) (he : ‖v‖^2+‖w‖^2 ≤ e) :
    QBoundedJets 2
      ((1+|tiltedStabilityCoefficient 2 B| *e)*D+
        firstTiltedTransportCoefficient B R*C*e)
      (firstTiltedAverageSource m v f F g a dm w) := by
  apply (qBoundedJets_firstTiltedAverageSource hf hF hg ha hm dm v w hv hsmall).mono
  apply (firstTiltedAverageSourceBound_le hF.nonneg hg.nonneg ha.nonneg hR hAR
    hm hdm v w hv).trans
  have hvE : ‖v‖^2 ≤ e := by nlinarith only [he,sq_nonneg ‖w‖]
  have hK : 0 ≤ firstTiltedTransportCoefficient B R := by
    dsimp only [firstTiltedTransportCoefficient]
    positivity
  have hC := hg.nonneg
  have hD := ha.nonneg
  gcongr

set_option maxHeartbeats 600000 in
theorem abs_secondMovingAverageSource_energy {B A H C D Q e m dm ddm : ℝ}
    {f f₁ f₂ g a q : E → ℝ}
    (hf : QPotential 3 B f) (hf₁ : QBoundedJets 1 A f₁) (hf₂ : QBoundedJets 1 H f₂)
    (hg : QBoundedJets 2 C g) (ha : QBoundedJets 2 D a) (hq : QBoundedJets 0 Q q)
    (hm : m ∈ Icc (0:ℝ) 1) (hdm : |dm| ≤ 1) (hddm : |ddm| ≤ 1)
    (v w b : E) (he : ‖v‖^2+‖w‖^2+‖b‖^2 ≤ e) (he1 : e ≤ 1) (x : E) :
    |secondMovingAverageSource m dm ddm v w b f f₁ f₂ g a q x| ≤
      Q+secondAverageTransportCoefficient (secondMovingAverageScale B A H)
        (defectNoiseMomentBound 1 B) (defectNoiseMomentBound 2 B)
        (defectNoiseMomentBound 3 B)*(C+D)*e := by
  have he0 : 0 ≤ e := by
    nlinarith only [he,sq_nonneg ‖v‖,sq_nonneg ‖w‖,sq_nonneg ‖b‖]
  have hs : (Real.sqrt e)^2 = e := Real.sq_sqrt he0
  have hd1 : Real.sqrt e ≤ 1 := by
    nlinarith only [hs,he1,Real.sqrt_nonneg e]
  have hv : ‖v‖ ≤ Real.sqrt e := by
    nlinarith only [he,hs,norm_nonneg v,Real.sqrt_nonneg e,sq_nonneg ‖w‖,sq_nonneg ‖b‖]
  have hw : ‖w‖ ≤ Real.sqrt e := by
    nlinarith only [he,hs,norm_nonneg w,Real.sqrt_nonneg e,sq_nonneg ‖v‖,sq_nonneg ‖b‖]
  have hb : ‖b‖ ≤ Real.sqrt e := by
    nlinarith only [he,hs,norm_nonneg b,Real.sqrt_nonneg e,sq_nonneg ‖v‖,sq_nonneg ‖w‖]
  simpa only [hs] using abs_secondMovingAverageSource_le hf hf₁ hf₂ hg ha hq
    hm hdm hddm (Real.sqrt_nonneg e) hd1 v w b hv hw hb x

def tiltedGeneratorDefectCoarseCoefficient (n : ℕ) (B : ℝ) : ℝ :=
  tiltedDifferenceCoefficient n B+((2:ℝ)^n*B+1)

theorem qBoundedJets_tiltedGeneratorDefect_coarse (n : ℕ) {B C : ℝ}
    {f g : E → ℝ} (hf : QPotential (n+2) B f) (hg : QBoundedJets (n+2) C g)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (v : E) (hv : ‖v‖ ≤ 1)
    (hsmall : m*(B*‖v‖^2) ≤ 1/2) :
    QBoundedJets n (C*tiltedGeneratorDefectCoarseCoefficient n B*‖v‖^2)
      (tiltedGeneratorDefect m v f g) := by
  have hdiff := qBoundedJets_tiltedAverage_sub n hf (by omega) le_rfl hg hm v hv hsmall
  have hgen := qBoundedJets_pathGenerator_order (hf.of_le (by omega)) hg hm v
  convert hdiff.sub hgen using 1
  · dsimp only [tiltedGeneratorDefectCoarseCoefficient]
    ring
  · rfl

theorem qBoundedJets_normalized_tiltedGeneratorDefect (n : ℕ) {B C : ℝ}
    {f g : E → ℝ} (hf : QPotential (n+2) B f) (hg : QBoundedJets (n+2) C g)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (v : E) (hv : ‖v‖ ≤ 1)
    (hsmall : m*(B*‖v‖^2) ≤ 1/2) :
    QBoundedJets n (C*tiltedGeneratorDefectCoarseCoefficient n B)
      (fun x => (‖v‖^2)⁻¹*tiltedGeneratorDefect m v f g x) := by
  have H := (qBoundedJets_tiltedGeneratorDefect_coarse n hf hg hm v hv hsmall).const_smul
    (‖v‖^2)⁻¹
  apply H.mono
  have hK : 0 ≤ C*tiltedGeneratorDefectCoarseCoefficient n B := by
    have hT := tiltedDifferenceCoefficient_nonneg n B
    dsimp only [tiltedGeneratorDefectCoarseCoefficient]
    positivity [hf.nonneg,hg.nonneg]
  rw [abs_inv,abs_of_nonneg (sq_nonneg ‖v‖)]
  by_cases hv0 : ‖v‖^2=0
  · simp only [hv0,inv_zero,zero_mul,hK]
  · have hvnorm : ‖v‖ ≠ 0 := by intro h; exact hv0 (by rw [h]; norm_num)
    exact le_of_eq (by field_simp [hvnorm])

theorem abs_normalized_tiltedGeneratorDefect_le {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential 4 B f) (hg : QBoundedJets 4 C g)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (v : E) (hv : ‖v‖ ≤ 1) (x : E) :
    |(‖v‖^2)⁻¹*tiltedGeneratorDefect m v f g x| ≤ C*pathExpansionConstant B*‖v‖^2 := by
  have H : |tiltedGeneratorDefect m v f g x| ≤ C*pathExpansionConstant B*‖v‖^4 := by
    convert abs_noiseMean_generator_remainder_le hf (by norm_num)
      (qBoundedJets_iff_qBddSmooth.mp hg).potential (by norm_num) hm v x hv using 1
    congr 1
    dsimp only [tiltedGeneratorDefect,pathGenerator,tiltedAverage,noiseMean]
    ring
  rw [abs_mul,abs_inv,abs_of_nonneg (sq_nonneg ‖v‖)]
  by_cases hv0 : ‖v‖^2=0
  · simp [hv0]
  · calc
      _ ≤ (‖v‖^2)⁻¹*(C*pathExpansionConstant B*‖v‖^4) :=
        mul_le_mul_of_nonneg_left H (inv_nonneg.mpr (sq_nonneg _))
      _ = _ := by field_simp

theorem eventually_small_normalized_tiltedGeneratorDefect {J I : Type} {s : Filter J}
    (f g : J → I → E → ℝ) (m : J → I → ℝ) (v : J → I → E)
    (r : ℕ) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hf : ∀ᶠ n in s, ∀ i, QPotential (r+4) B (f n i))
    (hg : ∀ᶠ n in s, ∀ i, QBoundedJets (r+4) C (g n i))
    (hm : ∀ᶠ n in s, ∀ i, m n i ∈ Icc (0:ℝ) 1)
    (hv : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in s, ∀ i, ‖v n i‖^2 ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in s, ∀ i,
      QBoundedJets r ε
        (fun x => (‖v n i‖^2)⁻¹*tiltedGeneratorDefect (m n i) (v n i) (f n i) (g n i) x) := by
  let K := C*tiltedGeneratorDefectCoarseCoefficient (r+1) B
  have hK : 0 ≤ K := by
    have H := tiltedDifferenceCoefficient_nonneg (r+1) B
    dsimp only [K,tiltedGeneratorDefectCoarseCoefficient]
    positivity
  let η := min 1 (1/(2*B+1))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hsteps : ∀ᶠ n in s, ∀ i, ‖v n i‖ ≤ 1 ∧ m n i*(B*‖v n i‖^2) ≤ 1/2 := by
    filter_upwards [hm,hv η hη] with n hn he i
    have hv2 := (he i).trans (min_le_left _ _)
    have hv1 : ‖v n i‖ ≤ 1 := by nlinarith only [hv2,norm_nonneg (v n i)]
    have H := (le_div_iff₀ (by positivity : 0 < 2*B+1)).mp
      ((he i).trans (min_le_right _ _))
    have H' := mul_le_of_le_one_left (mul_nonneg hB (sq_nonneg ‖v n i‖)) (hn i).2
    refine ⟨hv1,?_⟩
    nlinarith only [H,H',sq_nonneg ‖v n i‖]
  have hhigh : ∀ᶠ n in s, ∀ i, QBoundedJets (r+1) K
      (fun x => (‖v n i‖^2)⁻¹*tiltedGeneratorDefect (m n i) (v n i) (f n i) (g n i) x) := by
    filter_upwards [hf,hg,hm,hsteps] with n hfn hgn hmn hs i
    exact qBoundedJets_normalized_tiltedGeneratorDefect (r+1)
      ((hfn i).of_le (by omega)) ((hgn i).of_le (by omega))
      (hmn i) (v n i) (hs i).1 (hs i).2
  have hvalue : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in s, ∀ i x,
      ‖(‖v n i‖^2)⁻¹*tiltedGeneratorDefect (m n i) (v n i) (f n i) (g n i) x‖ ≤ ε := by
    intro ε hε
    let A := C*pathExpansionConstant B
    have hA : 0 ≤ A := mul_nonneg hC (pathExpansionConstant_nonneg hB)
    filter_upwards [hf,hg,hm,hsteps,hv (ε/(A+1)) (by positivity)] with n hfn hgn hmn hs he i x
    rw [Real.norm_eq_abs]
    calc
      _ ≤ A*‖v n i‖^2 := abs_normalized_tiltedGeneratorDefect_le
        ((hfn i).of_le (by omega)) ((hgn i).of_le (by omega)) (hmn i) (v n i) (hs i).1 x
      _ ≤ A*(ε/(A+1)) := mul_le_mul_of_nonneg_left (he i) hA
      _ ≤ ε := by
        have H := mul_le_of_le_one_right hε.le
          ((div_le_one (by positivity : 0 < A+1)).mpr (by linarith : A ≤ A+1))
        convert H using 1; ring
  exact QBoundedJets.eventually_small_of_values _ r hK hhigh hvalue

theorem normalized_tiltedGeneratorDefect_spatial_eventually {B C M h : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ f g : E → ℝ, QPotential 8 B f → QBoundedJets 8 C g →
      ∀ m : ℝ, m ∈ Icc (0:ℝ) 1 → ∀ v : E, ‖v‖^2 ≤ M*h/(N:ℝ) →
      QBoundedJets 4 ε (fun x => (‖v‖^2)⁻¹*tiltedGeneratorDefect m v f g x) := by
  classical
  let I := {p : (E → ℝ) × (E → ℝ) × ℝ × E //
    QPotential 8 B p.1 ∧ QBoundedJets 8 C p.2.1 ∧ p.2.2.1 ∈ Icc (0:ℝ) 1}
  let F : ℕ → I → E → ℝ := fun _ i => i.val.1
  let G : ℕ → I → E → ℝ := fun _ i => i.val.2.1
  let m : ℕ → I → ℝ := fun _ i => i.val.2.2.1
  let v : ℕ → I → E := fun N i =>
    if ‖i.val.2.2.2‖^2 ≤ M*h/(N:ℝ) then i.val.2.2.2 else 0
  have hf : ∀ᶠ N : ℕ in atTop, ∀ i, QPotential 8 B (F N i) :=
    Eventually.of_forall (fun _ i => i.property.1)
  have hg : ∀ᶠ N : ℕ in atTop, ∀ i, QBoundedJets 8 C (G N i) :=
    Eventually.of_forall (fun _ i => i.property.2.1)
  have hm : ∀ᶠ N : ℕ in atTop, ∀ i, m N i ∈ Icc (0:ℝ) 1 :=
    Eventually.of_forall (fun _ i => i.property.2.2)
  have hlim : Tendsto (fun N : ℕ => M*h/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hv : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, ∀ i, ‖v N i‖^2 ≤ δ := by
    intro δ hδ
    filter_upwards [hlim.eventually (eventually_le_nhds hδ)] with N hn i
    dsimp only [v]
    split_ifs with hi
    · exact hi.trans hn
    · simpa only [norm_zero,zero_pow (by norm_num : 2 ≠ 0)] using hδ.le
  have H := eventually_small_normalized_tiltedGeneratorDefect F G m v 4 hB hC hf hg hm hv ε hε
  filter_upwards [H] with N hn f g hfn hgn a ha w hw
  let i : I := ⟨(f,g,a,w),hfn,hgn,ha⟩
  have Hi := hn i
  simpa only [F,G,m,v,i,ite_eq_left hw] using Hi

end SKBarriers2.StepCalculus

namespace SKBarriers2.ParamChain

local notation "E" => (Fin 3 → ℝ)

section PrefixRegularity

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

local instance : NormedAddCommGroup (P × E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (P × E →L[ℝ] ℝ) := inferInstance

private theorem recursion_smooth_sub {F G : P × E → ℝ}
    (hF : ParamSmooth F) (hG : ParamSmooth G) : ParamSmooth (fun z => F z-G z) := by
  convert hF.add (hG.const_mul (-1)) using 1
  funext z
  ring

private theorem recursion_apply_coordinate_sum (L : E →L[ℝ] ℝ) (v : E) :
    L v = ∑ i : Fin 3, v i*L (Pi.single i 1) := by
  have hv : v = ∑ i : Fin 3, v i • Pi.single i 1 := by
    ext i
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
    simp
  conv_lhs => rw [hv]
  rw [map_sum]
  simp only [map_smul,smul_eq_mul]

private theorem recursion_smooth_chainGradient {B : ℝ} {f : E → ℝ}
    (hf : QPotential 3 B f) (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E)))
    (i : Fin 3) : ParamSmooth (fun z : P × E => fderiv ℝ
      (vectorIncrementChain (exponentialSteps ps z.1) f) z.2 (Pi.single i 1)) := by
  have hd := hf.derivativeJets.apply_const (Pi.single i 1)
  have H := smooth_exponentialAverage ps (regular_fixedTerminal hf (by norm_num) P)
    (regular_fixedTerminal (qBoundedJets_iff_qBddSmooth.mp hd).potential le_rfl P).toSmooth
  have he : (fun z : P × E => fderiv ℝ
      (vectorIncrementChain (exponentialSteps ps z.1) f) z.2 (Pi.single i 1)) =
      exponentialAverage ps (fun z => f z.2) (fun z => fderiv ℝ f z.2 (Pi.single i 1)) := by
    funext z
    exact fderiv_chain_average _ (hf.boundedDerivs (by norm_num)) _ _
  rw [he]
  exact H

private theorem recursion_smooth_generator {F G : P × E → ℝ}
    (hF : ∀ i : Fin 3,
      ParamSmooth (fun z => fderiv ℝ (fun y => F (z.1,y)) z.2 (Pi.single i 1)))
    (hG : TestJetFamily G) (M : P →L[ℝ] ℝ) (V : P →L[ℝ] E) :
    ParamSmooth (fun z => StepCalculus.pathGenerator (Real.exp (M z.1)) (V z.1)
      (fun y => F (z.1,y)) (fun y => G (z.1,y)) z.2) := by
  let v : P × E → E := fun z => V z.1
  have hv (i : Fin 3) : ParamSmooth (fun z : P × E => v z i) := by
    let L : P →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp V
    let W : (P × E) →L[ℝ] ℝ := L.comp (ContinuousLinearMap.fst ℝ P E)
    have hD : fderiv ℝ (fun z : P × E => v z i) = fun _ => W :=
      funext (fun _ => W.fderiv)
    refine ⟨W.contDiff,?_,?_,?_⟩
    · intro R
      refine ⟨‖L‖*max R 0,0,by positivity,le_rfl,?_⟩
      intro p x hp
      simp only [zero_mul,Real.exp_zero,mul_one]
      change ‖L p‖ ≤ ‖L‖*max R 0
      exact (L.le_opNorm p).trans (mul_le_mul_of_nonneg_left
        (hp.trans (le_max_left _ _)) (norm_nonneg L))
    · rw [hD]
      exact ParamExpGrowth.of_bounded (norm_nonneg W) (fun _ => le_rfl)
    · rw [hD]
      have hDD : fderiv ℝ (fun _ : P × E => W) =
          fun _ => (0 : P × E →L[ℝ] P × E →L[ℝ] ℝ) :=
        funext (fun _ => fderiv_const_apply W)
      rw [hDD]
      exact ParamExpGrowth.of_bounded (C := 0) le_rfl (fun _ => le_of_eq
        ContinuousLinearMap.opNorm_zero)
  have hdf : ParamSmooth (fun z => fderiv ℝ (fun y => F (z.1,y)) z.2 (v z)) := by
    have H := ParamSmooth.sum Finset.univ _ (fun i : Fin 3 => fun _ => (hv i).mul (hF i))
    simpa only [← recursion_apply_coordinate_sum] using H
  have hdg : ParamSmooth (fun z => fderiv ℝ (fun y => G (z.1,y)) z.2 (v z)) := by
    have H := ParamSmooth.sum Finset.univ _
      (fun i : Fin 3 => fun _ => (hv i).mul (hG.first i))
    simpa only [← recursion_apply_coordinate_sum] using H
  have hddg : ParamSmooth (fun z => fderiv ℝ (fderiv ℝ (fun y => G (z.1,y)))
      z.2 (v z) (v z)) := by
    have H := ParamSmooth.sum Finset.univ _ (fun i : Fin 3 => fun _ =>
      ParamSmooth.sum Finset.univ _ (fun j : Fin 3 => fun _ =>
        ((hv i).mul (hv j)).mul (hG.second i j)))
    have he (z : P × E) : fderiv ℝ (fderiv ℝ (fun y => G (z.1,y))) z.2 (v z) (v z) =
        ∑ i : Fin 3, ∑ j : Fin 3, (v z i*v z j)*
          fderiv ℝ (fderiv ℝ (fun y => G (z.1,y))) z.2 (Pi.single i 1) (Pi.single j 1) := by
      have houter := recursion_apply_coordinate_sum
        ((ContinuousLinearMap.apply ℝ ℝ (v z)).comp
          (fderiv ℝ (fderiv ℝ (fun y => G (z.1,y))) z.2)) (v z)
      change fderiv ℝ (fderiv ℝ (fun y => G (z.1,y))) z.2 (v z) (v z) =
        ∑ i : Fin 3, v z i*fderiv ℝ (fderiv ℝ (fun y => G (z.1,y))) z.2
          (Pi.single i 1) (v z) at houter
      rw [houter]
      apply Finset.sum_congr rfl
      intro i _
      rw [recursion_apply_coordinate_sum
        (fderiv ℝ (fderiv ℝ (fun y => G (z.1,y))) z.2 (Pi.single i 1)),Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    simpa only [← he] using H
  have hGs (p : P) : ContDiff ℝ 2 (fun y => G (p,y)) :=
    hG.value.1.comp (contDiff_const.prodMk contDiff_id)
  have he (z : P × E) : StepCalculus.directionalJet (v z) 2 (fun y => G (z.1,y)) z.2 =
      fderiv ℝ (fderiv ℝ (fun y => G (z.1,y))) z.2 (v z) (v z) := by
    have H := ((ContinuousLinearMap.apply ℝ ℝ (v z)).hasFDerivAt.comp z.2
      (((hGs z.1).fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num) z.2).hasFDerivAt).fderiv
    change fderiv ℝ (fun y => fderiv ℝ (fun y => G (z.1,y)) y (v z)) z.2 (v z) = _
    change fderiv ℝ (fun y => fderiv ℝ (fun y => G (z.1,y)) y (v z)) z.2 = _ at H
    rw [H]
    rfl
  convert (((regular_exp_parameter (X := E) M).toSmooth.mul hdf).mul hdg).add
    (hddg.const_mul (1/2)) using 1
  funext z
  dsimp only [StepCalculus.pathGenerator]
  rw [he]
  ring

theorem smooth_exponentialPrefixDefect {B : ℝ} {f : E → ℝ}
    (hf : QPotential 3 B f) {G : P × E → ℝ} (hG : TestJetFamily G)
    (front middle : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) :
    ParamSmooth (fun z : P × E => StepCalculus.tiltedPathTaylorDefect
      (exponentialSteps front z.1) (vectorIncrementChain (exponentialSteps middle z.1) f)
      (fun y => G (z.1,y)) z.2) := by
  let F : P × E → ℝ := exponentialChain middle (fun z => f z.2)
  have hF : ParamRegular F := regular_exponentialChain middle
    (regular_fixedTerminal hf (by norm_num) P)
  have hsum (qs : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) :
      ParamSmooth (fun z : P × E => StepCalculus.pathGeneratorSum
        (fun y => F (z.1,y)) (fun y => G (z.1,y)) (exponentialSteps qs z.1) z.2) := by
    induction qs with
    | nil => exact paramSmooth_const 0
    | cons p qs ih =>
      exact (recursion_smooth_generator (fun i => recursion_smooth_chainGradient hf middle i)
        hG p.1 p.2).add ih
  exact recursion_smooth_sub
    (recursion_smooth_sub (smooth_exponentialAverage front hF hG.value) hG.value) (hsum front)

end PrefixRegularity

private theorem prefix_masses_eventually_positive (ps : List (ℝ → ℝ × E)) {k : ℝ}
    (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k) (hpos : ∀ p ∈ ps, 0 < (p k).1) :
    ∀ᶠ t in 𝓝 k, ∀ p ∈ ps, 0 < (p t).1 := by
  have H : ∀ᶠ t in 𝓝 k, ∀ i : Fin ps.length, 0 < (ps.get i t).1 := by
    apply Filter.eventually_all.mpr
    intro i
    exact (hreg _ (List.get_mem ps i)).fst.continuousAt.eventually
      (Ioi_mem_nhds (hpos _ (List.get_mem ps i)))
  filter_upwards [H] with t ht p hp
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hp
  exact ht i

theorem contDiffAt_curvePrefixDefect {B k : ℝ} {f : E → ℝ}
    (hf : QPotential 5 B f) (qs ms : List (ℝ → ℝ × E))
    (w : ℝ → E) (hw : ContDiffAt ℝ 2 w k)
    (hreg : ∀ p ∈ qs++ms, ContDiffAt ℝ 2 p k)
    (hpos : ∀ p ∈ qs++ms, 0 < (p k).1) (x : E) :
    ContDiffAt ℝ 2 (fun t => StepCalculus.tiltedPathTaylorDefect
      (qs.map (fun p => p t)) (vectorIncrementChain (ms.map (fun p => p t)) f)
      (fun y => (fderiv ℝ f y (w t))^2) x) k := by
  let ps := qs++ms
  let P := Coordinates ps.length E × E
  let L : P →L[ℝ] Coordinates ps.length E := ContinuousLinearMap.fst ℝ _ _
  let W : P →L[ℝ] E := ContinuousLinearMap.snd ℝ _ _
  let liftStep := fun p : (Coordinates ps.length E →L[ℝ] ℝ) ×
      (Coordinates ps.length E →L[ℝ] E) => (p.1.comp L,p.2.comp L)
  let us := (coordinateSteps (X := E) ps.length).map liftStep
  let Q : ℝ → P := fun t => (logParameters ps t,w t)
  have hQ : ContDiffAt ℝ 2 Q k := (logParameters_contDiffAt ps hreg hpos).prodMk hw
  have H := (smooth_exponentialPrefixDefect (hf.of_le (by norm_num : 3 ≤ 5))
    (testJetFamily_terminalGradient_sq hf W) (us.take qs.length) (us.drop qs.length)).1
  have H' := H.contDiffAt.comp k (hQ.prodMk (contDiffAt_const (c := x)))
  apply H'.congr_of_eventuallyEq
  filter_upwards [prefix_masses_eventually_positive ps hreg hpos] with t ht
  have hus : exponentialSteps us (Q t) = ps.map (fun p => p t) := by
    have Hs := coordinateSteps_apply ps t ht
    dsimp only [us,exponentialSteps]
    rw [List.map_map]
    exact Hs
  have hfront : exponentialSteps (us.take qs.length) (Q t) = qs.map (fun p => p t) := by
    rw [exponentialSteps,List.map_take]
    change (exponentialSteps us (Q t)).take qs.length = _
    rw [hus]
    dsimp only [ps]
    rw [List.map_append,← List.length_map (f := fun p : ℝ → ℝ × E => p t) (as := qs)]
    exact List.take_left
  have hmiddle : exponentialSteps (us.drop qs.length) (Q t) = ms.map (fun p => p t) := by
    rw [exponentialSteps,List.map_drop]
    change (exponentialSteps us (Q t)).drop qs.length = _
    rw [hus]
    dsimp only [ps]
    rw [List.map_append,← List.length_map (f := fun p : ℝ → ℝ × E => p t) (as := qs)]
    exact List.drop_left
  change StepCalculus.tiltedPathTaylorDefect (qs.map (fun p => p t))
    (vectorIncrementChain (ms.map (fun p => p t)) f)
    (fun y => (fderiv ℝ f y (w t))^2) x =
      StepCalculus.tiltedPathTaylorDefect (exponentialSteps (us.take qs.length) (Q t))
        (vectorIncrementChain (exponentialSteps (us.drop qs.length) (Q t)) f)
        (fun y => (fderiv ℝ f y (W (Q t)))^2) x
  rw [hfront,hmiddle]
  rfl

end SKBarriers2.ParamChain

namespace SKBarriers2.Corner

open StepCalculus
local notation "E" => (Fin 3 → ℝ)
local notation "Curve" => (ℝ → ℝ × E)

def prefixEnergyDefectTerms (β : ℝ) (α : ℝ → ℝ) (a s h : ℝ) (N : ℕ)
    (lam : ℝ) (j : Fin (12*N)) (p : Curve) (tail : List Curve)
    (k : ℝ) (x : E) (i : Fin 4) : ℝ :=
  let l := massPath (windowMassPath β α a (1/2) s h k N) lam
  let F := vectorIncrementChain (l.drop j.val) (massVariationTerminal β α s h)
  let w := (orderedWindowCurve β α a s h N lam j k).2
  tiltedPathDefectTerms (p k) (tail.map (fun q => q k)) F
    (fun y => (fderiv ℝ (massVariationTerminal β α s h) y w)^2) x i

theorem prefixEnergyDefect_cons_eq_sum {β : ℝ} {α : ℝ → ℝ} {a s h lam k : ℝ}
    {N : ℕ} (j : Fin (12*N)) (p : Curve) (tail : List Curve) {B C : ℝ}
    (hF : QPotential 5 B (vectorIncrementChain
      ((massPath (windowMassPath β α a (1/2) s h k N) lam).drop j.val)
      (massVariationTerminal β α s h)))
    (hf : QPotential 5 C (massVariationTerminal β α s h))
    (hm : ∀ q ∈ tail, (q k).1 ∈ Icc (0:ℝ) 1) (x : E) :
    prefixEnergyDefect β α a s h N lam j (p::tail) k x =
      ∑ i : Fin 4, prefixEnergyDefectTerms β α a s h N lam j p tail k x i := by
  have hd := hf.derivativeJets.apply_const
    (orderedWindowCurve β α a s h N lam j k).2
  have hg : QBoundedJets 4
      ((2:ℝ)^4*(C*‖(orderedWindowCurve β α a s h N lam j k).2‖)^2)
      (fun y => (fderiv ℝ (massVariationTerminal β α s h) y
        (orderedWindowCurve β α a s h N lam j k).2)^2) := by
    convert hd.mul hd using 1
    · ring
    · funext y; ring
  have hmass : ∀ q ∈ tail.map (fun q => q k), q.1 ∈ Icc (0:ℝ) 1 := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    exact hm p hp
  have H := tiltedPathTaylorDefect_cons_eq_sum
    (f := vectorIncrementChain
      ((massPath (windowMassPath β α a (1/2) s h k N) lam).drop j.val)
      (massVariationTerminal β α s h))
    (g := fun y => (fderiv ℝ (massVariationTerminal β α s h) y
      (orderedWindowCurve β α a s h N lam j k).2)^2)
    hF hg (p k) (tail.map (fun q => q k)) hmass x
  simpa only [prefixEnergyDefect,prefixEnergyDefectTerms,List.map_cons] using H

theorem scalarData_prefixEnergyDefect_contDiffAt {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ h0 : ℝ, 0 < h0 ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ N : ℕ, 1 ≤ N →
      ∀ lam ∈ Icc (0:ℝ) 1, ∀ j : Fin (12*N), ∀ k : ℝ, |k| ≤ 1/2 →
      let α := cdf (D.μ : Measure ℝ)
      let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
      ∀ front tail, ps.take j.val = front++tail → ∀ x : E,
        ContDiffAt ℝ 2 (fun t => prefixEnergyDefect β α (α (r-h)) (r-h) h N lam j tail t x) k := by
  by_cases hlu : l ≤ u
  · obtain ⟨hP,hhP,hregular⟩ := scalarData_interpolated_window_curve_regular D hl hlu hu
    refine ⟨min hP (kStabilityInteriorRadius D.q l u),
      lt_min hhP (kStabilityInteriorRadius_pos hl hu),?_⟩
    intro r hr h hh hh0 N hN lam hlam j k hk
    let α := cdf (D.μ : Measure ℝ)
    let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
    dsimp only
    intro front tail hsplit x
    have hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k :=
      fun p hp => (hregular r hr h hh (hh0.trans (min_le_left _ _)) N hN
        lam hlam p hp k hk).1
    have hpos : ∀ p ∈ ps, 0 < (p k).1 :=
      fun p hp => (hregular r hr h hh (hh0.trans (min_le_left _ _)) N hN
        lam hlam p hp k hk).2.1
    have hsub : ∀ p ∈ tail++ps.drop j.val, p ∈ ps := by
      intro p hp
      obtain hp | hp := List.mem_append.mp hp
      · apply List.mem_of_mem_take
        rw [hsplit]
        exact List.mem_append_right front hp
      · exact List.mem_of_mem_drop hp
    let w : ℝ → E := fun t => (orderedWindowCurve β α (α (r-h)) (r-h) h N lam j t).2
    have hw : ContDiffAt ℝ 2 w k :=
      (hreg _ (orderedWindowCurve_mem β α (α (r-h)) (r-h) h N lam j)).snd
    have ht := kStability_time_mem hr hh.le (hh0.trans (min_le_right _ _))
      (show (4:ℝ) ∈ Icc (0:ℝ) 4 by norm_num)
    have ht' : (r-h)+4*h ∈ Icc (0:ℝ) 1 := by
      constructor <;> linarith [ht.1,ht.2,D.q_mem.2]
    have hf : QPotential 5 (terminalJetBound D 5) (massVariationTerminal β α (r-h) h) :=
      scalarData_massVariationTerminal_qPotential D 5 ht'
    have H := ParamChain.contDiffAt_curvePrefixDefect hf tail (ps.drop j.val) w hw
      (fun p hp => hreg p (hsub p hp)) (fun p hp => hpos p (hsub p hp)) x
    have he (t : ℝ) : (ps.drop j.val).map (fun p => p t) =
        (massPath (windowMassPath β α (α (r-h)) (1/2) (r-h) h t N) lam).drop j.val := by
      rw [List.map_drop]
      dsimp only [ps]
      rw [windowKCurves_apply β _ (r-h) h t N hh.le,massPath_window_eq]
    simp_rw [he] at H
    exact H
  · refine ⟨1,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

end SKBarriers2.Corner
