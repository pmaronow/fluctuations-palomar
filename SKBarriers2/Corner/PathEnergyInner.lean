module

public import SKBarriers2.Corner.PathEnergyAssembly

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

def firstVariationTaylorDefect (m : ℝ) (v : E) (f g : E → ℝ)
    (dm : ℝ) (w : E) (x : E) : ℝ :=
  firstVariationStep m v f g dm w x-stepQuadraticFirstSource m v f g dm w x

def firstVariationSpatialCoefficient (B R : ℝ) : ℝ :=
  R*tiltedDifferenceCoefficient 3 B+|massSensitivityJetCoefficient 2 B|+
    8*B*R+R+8*B^2+|directionSensitivityCoefficient 3 B|+B+8*B^2

theorem firstVariationSpatialCoefficient_nonneg {B R : ℝ}
    (hB : 0 ≤ B) (hR : 0 ≤ R) :
    0 ≤ firstVariationSpatialCoefficient B R := by
  have hT := tiltedDifferenceCoefficient_nonneg 3 B
  unfold firstVariationSpatialCoefficient
  positivity

theorem qBoundedJets_firstVariationTaylorDefect_coarse {B R A m dm d : ℝ}
    {f g : E → ℝ} (hf : QPotential 6 B f) (hg : QBoundedJets 5 A g)
    (hAR : A ≤ R) (hm : m ∈ Ioc (0 : ℝ) 1) (hdm : |dm| ≤ 1)
    (hd : 0 ≤ d) (v w : E) (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d)
    (hv1 : ‖v‖ ≤ 1) (hsmall : B*‖v‖^2 ≤ 1/2) :
    QBoundedJets 3 (firstVariationSpatialCoefficient B R*d^2)
      (firstVariationTaylorDefect m v f g dm w) := by
  have hB := hf.nonneg
  have hA := hg.nonneg
  have hR := hA.trans hAR
  have hmcc : m ∈ Icc (0 : ℝ) 1 := ⟨hm.1.le,hm.2⟩
  have hmabs : |m| ≤ 1 := by rw [abs_of_pos hm.1]; exact hm.2
  have hcurv : m*(B*‖v‖^2) ≤ 1/2 :=
    (mul_le_of_le_one_left (by positivity) hm.2).trans hsmall
  have hT := qBoundedJets_tiltedAverage_sub 3 hf (by norm_num) (by norm_num)
    hg hmcc v hv1 hcurv
  have hM := (qBoundedJets_massSensitivity (hf.of_le (by norm_num : 5 ≤ 6))
    hm v hv1 hsmall).const_smul dm
  have hD := qBoundedJets_directionSensitivity (hf.of_le (by norm_num : 5 ≤ 6))
    hmcc v w
  have hfv := (hf.derivativeJets.of_le (by norm_num : 3 ≤ 5)).apply_const v
  have hgv := (hg.derivativeJets.of_le (by norm_num : 3 ≤ 4)).apply_const v
  have hP := (hfv.mul hgv).const_smul m
  have hH : QBoundedJets 3 (A*‖v‖^2) (directionalJet v 2 g) := by
    exact qBoundedJets_iff_qBddSmooth.mpr
      (directionalJet_smooth (r := 3) 1 (qBoundedJets_iff_qBddSmooth.mp hg).potential v)
  have hHhalf := (hH.const_smul (1/2 : ℝ)).mono
    (mul_le_of_le_one_left hH.nonneg (by norm_num))
  have hQ := (hfv.mul hfv).const_smul (dm/2)
  have hJ := qBoundedJets_directionSource (hf.of_le (by norm_num : 5 ≤ 6)) hmcc v w
  have H := ((hT.add hM).add hD).sub (((hP.add hHhalf).add hQ).add hJ)
  have he : (fun x =>
      ((tiltedAverage m v f g x-g x)+dm*massSensitivity m v f x)+
        tiltedAverage m v f (directionSource m v w f) x-
      (((m*(fderiv ℝ f x v*fderiv ℝ g x v)+(1/2:ℝ)*directionalJet v 2 g x)+
        (dm/2)*(fderiv ℝ f x v*fderiv ℝ f x v))+directionSource m v w f x)) =
      firstVariationTaylorDefect m v f g dm w := by
    funext x
    unfold firstVariationTaylorDefect firstVariationStep stepQuadraticFirstSource
    ring
  change QBoundedJets 3 _ (fun x =>
      ((tiltedAverage m v f g x-g x)+dm*massSensitivity m v f x)+
        tiltedAverage m v f (directionSource m v w f) x-
      (((m*(fderiv ℝ f x v*fderiv ℝ g x v)+(1/2:ℝ)*directionalJet v 2 g x)+
        (dm/2)*(fderiv ℝ f x v*fderiv ℝ f x v))+directionSource m v w f x)) at H
  rw [he] at H
  apply H.mono
  have hT0 := tiltedDifferenceCoefficient_nonneg 3 B
  have hM0 : 0 ≤ massSensitivityJetCoefficient 2 B :=
    (by positivity : (0 : ℝ) ≤ 2*B^2).trans (le_max_left _ _)
  have hdmhalf : |dm/2| ≤ 1 := by rw [abs_div]; norm_num; linarith
  norm_num only [show (2 : ℝ)^3 = 8 from by norm_num] at H ⊢
  have ht : A*tiltedDifferenceCoefficient 3 B*‖v‖^2 ≤
      R*tiltedDifferenceCoefficient 3 B*d^2 := by gcongr
  have hm' : |dm| *(massSensitivityJetCoefficient 2 B*‖v‖^2) ≤
      1*(|massSensitivityJetCoefficient 2 B| *d^2) := by
    gcongr
    exact le_abs_self _
  have hd' : directionSensitivityCoefficient 3 B*‖v‖*‖w‖ ≤
      |directionSensitivityCoefficient 3 B| *d*d := by
    gcongr
    exact le_abs_self _
  have hp : |m| *(8*(B*‖v‖)*(A*‖v‖)) ≤ 1*(8*(B*d)*(R*d)) := by gcongr
  have hh : A*‖v‖^2 ≤ R*d^2 := by gcongr
  have hq : |dm/2| *(8*(B*‖v‖)*(B*‖v‖)) ≤ 1*(8*(B*d)*(B*d)) := by gcongr
  have hj : (B+8*B^2)*‖v‖*‖w‖ ≤ (B+8*B^2)*d*d := by gcongr
  calc
    _ ≤ R*tiltedDifferenceCoefficient 3 B*d^2+
        1*(|massSensitivityJetCoefficient 2 B| *d^2)+
        |directionSensitivityCoefficient 3 B| *d*d+
        (1*(8*(B*d)*(R*d))+R*d^2+1*(8*(B*d)*(B*d))+(B+8*B^2)*d*d) :=
      add_le_add (add_le_add (add_le_add ht hm') hd')
        (add_le_add (add_le_add (add_le_add hp hh) hq) hj)
    _ = firstVariationSpatialCoefficient B R*d^2 := by
      unfold firstVariationSpatialCoefficient
      ring

def firstVariationValueCoefficient (B R a0 : ℝ) : ℝ :=
  R*pathExpansionConstant B+2*B*pathExpansionConstant B/a0+
    (B+4*B^2)*(1+B)^2

theorem firstVariationValueCoefficient_nonneg {B R a0 : ℝ}
    (hB : 0 ≤ B) (hR : 0 ≤ R) (ha0 : 0 < a0) :
    0 ≤ firstVariationValueCoefficient B R a0 := by
  have hP := pathExpansionConstant_nonneg hB
  unfold firstVariationValueCoefficient
  positivity

theorem abs_firstVariationTaylorDefect_le {B R A a0 m dm d : ℝ}
    {f g : E → ℝ} (hf : QPotential 4 B f) (hg : QBoundedJets 4 A g)
    (hAR : A ≤ R) (ha0 : 0 < a0) (hm : m ∈ Icc a0 1)
    (hdm : |dm| ≤ 1) (hd : 0 ≤ d) (v w x : E)
    (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d) (hv1 : ‖v‖ ≤ 1) :
    |firstVariationTaylorDefect m v f g dm w x| ≤
      firstVariationValueCoefficient B R a0*d^4 := by
  have hB := hf.nonneg
  have hA := hg.nonneg
  have hR := hA.trans hAR
  have hP := pathExpansionConstant_nonneg hB
  have H := abs_firstVariationStep_sub_quadratic_le hf hg ha0 hm dm v w x hv1
  apply H.trans
  calc
    _ ≤ (R*pathExpansionConstant B+1*(2*B*pathExpansionConstant B/a0))*d^4+
        (B+4*B^2)*(1+B)^2*d^3*d := by gcongr
    _ = _ := by unfold firstVariationValueCoefficient; ring

theorem eventually_small_firstVariationTaylorDefect {J I : Type} {s : Filter J}
    (f g : J → I → E → ℝ) (m dm : J → I → ℝ) (v w : J → I → E)
    (d : J → ℝ) {B R a0 : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R) (ha0 : 0 < a0)
    (hf : ∀ᶠ n in s, ∀ i, QPotential 6 B (f n i))
    (hg : ∀ᶠ n in s, ∀ i, QBoundedJets 5 R (g n i))
    (hm : ∀ᶠ n in s, ∀ i, m n i ∈ Icc a0 1)
    (hdm : ∀ᶠ n in s, ∀ i, |dm n i| ≤ 1)
    (hd : ∀ᶠ n in s, 0 < d n)
    (hvw : ∀ᶠ n in s, ∀ i, ‖v n i‖ ≤ d n ∧ ‖w n i‖ ≤ d n)
    (hlim : Tendsto (fun n => d n^2) s (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in s, ∀ i,
      QBoundedJets 2 (ε*d n^2)
        (firstVariationTaylorDefect (m n i) (v n i) (f n i) (g n i) (dm n i) (w n i)) := by
  let K := firstVariationSpatialCoefficient B R
  let V := firstVariationValueCoefficient B R a0
  have hK : 0 ≤ K := firstVariationSpatialCoefficient_nonneg hB hR
  have hV : 0 ≤ V := firstVariationValueCoefficient_nonneg hB hR ha0
  let F : J → I → E → ℝ := fun n i x => (d n^2)⁻¹*
    firstVariationTaylorDefect (m n i) (v n i) (f n i) (g n i) (dm n i) (w n i) x
  have hsteps : ∀ᶠ n in s, ∀ i, ‖v n i‖ ≤ 1 ∧ B*‖v n i‖^2 ≤ 1/2 := by
    filter_upwards [hvw,hlim.eventually
      (eventually_le_nhds (lt_min (by norm_num : (0 : ℝ) < 1)
        (by positivity : 0 < 1/(2*B+1))))] with n hn hs i
    have hs1 := hs.trans (min_le_left _ _)
    have hv2 : ‖v n i‖^2 ≤ d n^2 := pow_le_pow_left₀ (norm_nonneg _) (hn i).1 2
    have hshort : (2*B+1)*d n^2 ≤ 1 := by
      have H := (le_div_iff₀ (by positivity : 0 < 2*B+1)).mp
        (hs.trans (min_le_right _ _))
      nlinarith only [H]
    constructor
    · nlinarith only [hv2,hs1,norm_nonneg (v n i)]
    · have H := mul_le_mul_of_nonneg_left hv2 hB
      nlinarith only [H,hshort,sq_nonneg (d n)]
  have hhigh : ∀ᶠ n in s, ∀ i, QBoundedJets 3 K (F n i) := by
    filter_upwards [hf,hg,hm,hdm,hd,hvw,hsteps] with n hfn hgn hmn hdmn hdn hn hs i
    have H := (qBoundedJets_firstVariationTaylorDefect_coarse (hfn i) (hgn i) le_rfl
      ⟨ha0.trans_le (hmn i).1,(hmn i).2⟩ (hdmn i) hdn.le
      (v n i) (w n i) (hn i).1 (hn i).2 (hs i).1 (hs i).2).const_smul (d n^2)⁻¹
    apply H.mono
    rw [abs_inv,abs_of_nonneg (sq_nonneg (d n))]
    have hdn0 : d n ≠ 0 := hdn.ne'
    exact le_of_eq (by dsimp only [K]; field_simp)
  have hvalue : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in s, ∀ i x, ‖F n i x‖ ≤ ε := by
    intro ε hε
    filter_upwards [hf,hg,hm,hdm,hd,hvw,hsteps,
      hlim.eventually (eventually_le_nhds (by positivity : 0 < ε/(V+1)))] with
      n hfn hgn hmn hdmn hdn hn hs hsmall i x
    have H := abs_firstVariationTaylorDefect_le ((hfn i).of_le (by norm_num))
      ((hgn i).of_le (by norm_num)) le_rfl ha0 (hmn i) (hdmn i) hdn.le
      (v n i) (w n i) x (hn i).1 (hn i).2 (hs i).1
    have hdn0 : d n ≠ 0 := hdn.ne'
    calc
      ‖F n i x‖ = (d n^2)⁻¹*
          |firstVariationTaylorDefect (m n i) (v n i) (f n i) (g n i) (dm n i) (w n i) x| := by
        dsimp only [F]
        rw [Real.norm_eq_abs,abs_mul,abs_inv,abs_of_nonneg (sq_nonneg (d n))]
      _ ≤ (d n^2)⁻¹*(V*d n^4) :=
        mul_le_mul_of_nonneg_left H (inv_nonneg.mpr (sq_nonneg _))
      _ = V*d n^2 := by field_simp
      _ ≤ V*(ε/(V+1)) := mul_le_mul_of_nonneg_left hsmall hV
      _ ≤ ε := by
        have HV : V/(V+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
        convert mul_le_of_le_one_right hε.le HV using 1
        ring
  intro ε hε
  filter_upwards [QBoundedJets.eventually_small_of_values F 2 hK hhigh hvalue ε hε,hd] with
    n hn hdn i
  have H := (hn i).const_smul (d n^2)
  have hdn0 : d n^2 ≠ 0 := pow_ne_zero 2 hdn.ne'
  convert H using 1
  · rw [abs_of_nonneg (sq_nonneg (d n))]
    ring
  · funext x
    dsimp only [F]
    simp only [smul_eq_mul,← mul_assoc,mul_inv_cancel₀ hdn0,one_mul]

theorem firstVariationTaylorDefect_spatial_eventually {B R a0 L h ε : ℝ}
    (hB : 0 ≤ B) (hR : 0 ≤ R) (ha0 : 0 < a0) (hL : 0 ≤ L)
    (hh : 0 < h) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ f : E → ℝ, QPotential 6 B f →
      ∀ g : E → ℝ, QBoundedJets 5 R g → ∀ m : ℝ, m ∈ Icc a0 1 →
      ∀ dm : ℝ, |dm| ≤ 1 → ∀ v w : E,
      ‖v‖ ≤ L*Real.sqrt (h/(N : ℝ)) → ‖w‖ ≤ L*Real.sqrt (h/(N : ℝ)) →
      QBoundedJets 2 (ε*h/(N : ℝ)) (firstVariationTaylorDefect m v f g dm w) := by
  classical
  let I := {p : (E → ℝ) × (E → ℝ) × ℝ × ℝ × E × E //
    QPotential 6 B p.1 ∧ QBoundedJets 5 R p.2.1 ∧
      p.2.2.1 ∈ Icc a0 1 ∧ |p.2.2.2.1| ≤ 1}
  let F : ℕ → I → E → ℝ := fun _ i => i.val.1
  let G : ℕ → I → E → ℝ := fun _ i => i.val.2.1
  let M : ℕ → I → ℝ := fun _ i => i.val.2.2.1
  let DM : ℕ → I → ℝ := fun _ i => i.val.2.2.2.1
  let d : ℕ → ℝ := fun N => (L+1)*Real.sqrt (h/(N : ℝ))
  let V : ℕ → I → E := fun N i =>
    if ‖i.val.2.2.2.2.1‖ ≤ d N then i.val.2.2.2.2.1 else 0
  let W : ℕ → I → E := fun N i =>
    if ‖i.val.2.2.2.2.2‖ ≤ d N then i.val.2.2.2.2.2 else 0
  have hF : ∀ᶠ N : ℕ in atTop, ∀ i, QPotential 6 B (F N i) :=
    Eventually.of_forall (fun _ i => i.property.1)
  have hG : ∀ᶠ N : ℕ in atTop, ∀ i, QBoundedJets 5 R (G N i) :=
    Eventually.of_forall (fun _ i => i.property.2.1)
  have hM : ∀ᶠ N : ℕ in atTop, ∀ i, M N i ∈ Icc a0 1 :=
    Eventually.of_forall (fun _ i => i.property.2.2.1)
  have hDM : ∀ᶠ N : ℕ in atTop, ∀ i, |DM N i| ≤ 1 :=
    Eventually.of_forall (fun _ i => i.property.2.2.2)
  have hd : ∀ᶠ N : ℕ in atTop, 0 < d N := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    dsimp only [d]
    positivity
  have hVW : ∀ᶠ N : ℕ in atTop, ∀ i, ‖V N i‖ ≤ d N ∧ ‖W N i‖ ≤ d N := by
    filter_upwards [hd] with N hdn i
    constructor
    · dsimp only [V]
      split_ifs with hi
      · exact hi
      · simpa only [norm_zero] using hdn.le
    · dsimp only [W]
      split_ifs with hi
      · exact hi
      · simpa only [norm_zero] using hdn.le
  have hsq (N : ℕ) : d N^2 = (L+1)^2*h/(N : ℝ) := by
    dsimp only [d]
    rw [mul_pow,Real.sq_sqrt (div_nonneg hh.le (Nat.cast_nonneg N))]
    ring
  have hlim : Tendsto (fun N => d N^2) atTop (𝓝 0) := by
    simp_rw [hsq]
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hδ : 0 < ε/(L+1)^2 := by positivity
  filter_upwards [eventually_small_firstVariationTaylorDefect F G M DM V W d
    hB hR ha0 hF hG hM hDM hd hVW hlim (ε/(L+1)^2) hδ] with N hn
  intro f hf g hg m hm dm hdm v w hv hw
  let i : I := ⟨(f,g,m,dm,v,w),hf,hg,hm,hdm⟩
  have hL' : L*Real.sqrt (h/(N : ℝ)) ≤ d N := by
    dsimp only [d]
    gcongr
    linarith
  have hv' : ‖v‖ ≤ d N := hv.trans hL'
  have hw' : ‖w‖ ≤ d N := hw.trans hL'
  have H := hn i
  simp only [F,G,M,DM,V,W,i,ite_eq_left hv',ite_eq_left hw'] at H
  convert H using 1
  rw [hsq]
  have hL0 : L+1 ≠ 0 := by positivity
  field_simp

end SKBarriers2.StepCalculus

namespace SKBarriers2.Corner

open StepCalculus
local notation "E" => (Fin 3 → ℝ)

private theorem inner_window_direction_bound (β : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (α : ℝ → ℝ) (s h : ℝ), 0 ≤ h → ∀ N : ℕ,
      ∀ p ∈ windowKCurves β α s h N, ∀ k : ℝ, |k| ≤ 1/2 →
      ‖(p k).2‖ ≤ L*Real.sqrt (h/(N : ℝ)) ∧
        ‖deriv (fun t => (p t).2) k‖ ≤ L*Real.sqrt (h/(N : ℝ)) ∧
        ‖deriv (deriv (fun t => (p t).2)) k‖ ≤ L*Real.sqrt (h/(N : ℝ)) := by
  obtain ⟨A,hA,hbound⟩ := window_direction_budget
  refine ⟨A*|β|,by positivity,?_⟩
  intro α s h hh N p hp k hk
  obtain ⟨σ,_,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨j,_,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  exact (hbound β h hh N i k hk).2

theorem scalarData_window_firstVariationTaylorDefect_spatial_c2 {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ h0 kap : ℝ, 0 < h0 ∧ 0 < kap ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ lam ∈ Icc (0 : ℝ) 1, ∀ j : Fin (12*N),
      ∀ k : ℝ, |k| ≤ kap →
      let α := cdf (D.μ : Measure ℝ)
      let p := orderedWindowCurve β α (α (r-h)) (r-h) h N lam j
      let F := orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j k
      let G := orderedInnerVariation β α (α (r-h)) (1/2) (r-h) h N lam j 1 k
      QBoundedJets 2 (ε*h/(N : ℝ))
        (firstVariationTaylorDefect (p k).1 (p k).2 F G
          (deriv (fun t => (p t).1) k) (deriv (fun t => (p t).2) k)) := by
  by_cases hlu : l ≤ u
  · obtain ⟨A,a0,hV,_,ha0,hhV,hvar⟩ :=
      scalarData_interpolated_window_variation_inputs D hl hlu hu
    obtain ⟨R,hJ,hR,hhJ,hjets⟩ := scalarData_orderedInnerVariations_c6_c4 D hl hu
    obtain ⟨B,aE,S,hE,kapE,hB,_,_,hhE,hkapE,hentropy⟩ :=
      scalarData_uniformWindowEntropyInputs D hl hu
    obtain ⟨L,hL,hdir⟩ := inner_window_direction_bound β
    refine ⟨min hV (min hJ (min hE 1)),min kapE (1/2),
      lt_min hhV (lt_min hhJ (lt_min hhE (by norm_num))),
      lt_min hkapE (by norm_num),?_⟩
    intro r hr h hh hh0 ε hε
    have hhV' := hh0.trans (min_le_left _ _)
    have hhJ' := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hhE' := hh0.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    have hh1 : h ≤ 1 := hh0.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
    filter_upwards [firstVariationTaylorDefect_spatial_eventually hB hR.le ha0 hL hh hε,
      eventually_ge_atTop (1 : ℕ)] with N hn hN
    intro lam hlam j k hk
    dsimp only
    let α := cdf (D.μ : Measure ℝ)
    let p := orderedWindowCurve β α (α (r-h)) (r-h) h N lam j
    let F := orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j k
    let G := orderedInnerVariation β α (α (r-h)) (1/2) (r-h) h N lam j 1 k
    have hkhalf := hk.trans (min_le_right _ _)
    have hp : p ∈ windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N :=
      orderedWindowCurve_mem β α (α (r-h)) (r-h) h N lam j
    have hinputs := (hvar r hr h hh hhV' N hN lam hlam k hkhalf).2 p hp
    have hds := hdir _ _ _ hh.le N p hp k hkhalf
    have hG := (hjets r hr h hh hhJ' N hN lam hlam j k hkhalf).1
    have hg : QBoundedJets 5 R G := (hG.of_le (by norm_num : 5 ≤ 6)).mono
      (mul_le_of_le_one_right hR.le hh1)
    obtain ⟨_,hEN⟩ := hentropy r hr h hh hhE' k (hk.trans (min_le_left _ _)) N hN
    obtain ⟨hinner,_⟩ := hEN lam hlam
    have hf : QPotential 6 B F := by
      simpa only [F,orderedInnerChain,massPath,List.map_drop,windowEntryIndex] using
        (hinner j.val (by rw [windowMassPath_length]; exact j.isLt)).of_le (by norm_num : 6 ≤ 10)
    exact hn F hf G hg (p k).1 hinputs.2.1
      (deriv (fun t => (p t).1) k) hinputs.2.2.1 (p k).2
      (deriv (fun t => (p t).2) k) hds.1 hds.2.1
  · refine ⟨1,1,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

end SKBarriers2.Corner

namespace SKBarriers2.Corner.C2BoundAt

theorem linearObservation {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {d k : ℝ} {v : ℝ → X} (hd : 0 ≤ d) (hv : ContDiffAt ℝ 2 v k)
    (hb : ∀ c : ℕ, c ≤ 2 → ‖iteratedDeriv c v k‖ ≤ d) (L : X →L[ℝ] ℝ) :
    C2BoundAt (‖L‖*d) (fun t => L (v t)) k := by
  refine ⟨by positivity,L.contDiff.contDiffAt.comp k hv,?_⟩
  intro c hc
  have he : iteratedDeriv c (fun t => L (v t)) k = L (iteratedDeriv c v k) := by
    simp only [iteratedDeriv_eq_iteratedFDeriv]
    have H := L.iteratedFDeriv_comp_left (hv.of_le (by exact_mod_cast hc)) le_rfl
    exact congrArg (fun T => T (fun _ : Fin c => (1 : ℝ))) H
  rw [he,← Real.norm_eq_abs]
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb c hc) (norm_nonneg _))

theorem square_firstOrder {U H R k : ℝ} {A a b : ℝ → ℝ}
    (ha : C2BoundAt U a k) (hd : C2BoundAt H (fun t => A t-a t) k)
    (hr : C2BoundAt R (fun t => A t-a t-b t) k) :
    C2BoundAt (4*H^2+8*U*R) (fun t => A t^2-a t^2-2*a t*b t) k := by
  have H := (hd.mul hd).add ((ha.mul hr).const_mul 2)
  convert H using 1
  · norm_num
    ring
  · funext t
    ring

end SKBarriers2.Corner.C2BoundAt

namespace SKBarriers2.Corner

open StepCalculus
local notation "E" => (Fin 3 → ℝ)

theorem scalarData_window_terminalGradient_c2BoundAt {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ U h0 : ℝ, 0 ≤ U ∧ 0 < h0 ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ N : ℕ, 1 ≤ N →
      ∀ lam ∈ Icc (0 : ℝ) 1, ∀ j : Fin (12*N), ∀ k : ℝ, |k| ≤ 1/2 → ∀ x : E,
      let α := cdf (D.μ : Measure ℝ)
      C2BoundAt (U*Real.sqrt (h/(N : ℝ))) (fun t =>
        fderiv ℝ (massVariationTerminal β α (r-h) h) x
          (orderedWindowCurve β α (α (r-h)) (r-h) h N lam j t).2) k := by
  by_cases hlu : l ≤ u
  · obtain ⟨A,a0,hV,_,_,hhV,hvar⟩ :=
      scalarData_interpolated_window_variation_inputs D hl hlu hu
    obtain ⟨L,hL,hdir⟩ := inner_window_direction_bound β
    let B := terminalJetBound D 1
    have hB : 0 ≤ B := terminalJetBound_nonneg D 1
    refine ⟨B*L,min hV (kStabilityInteriorRadius D.q l u),by positivity,
      lt_min hhV (kStabilityInteriorRadius_pos hl hu),?_⟩
    intro r hr h hh hh0 N hN lam hlam j k hk x
    dsimp only
    let α := cdf (D.μ : Measure ℝ)
    let p := orderedWindowCurve β α (α (r-h)) (r-h) h N lam j
    have hp : p ∈ windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N :=
      orderedWindowCurve_mem β α (α (r-h)) (r-h) h N lam j
    have hpreg := ((hvar r hr h hh (hh0.trans (min_le_left _ _)) N hN
      lam hlam k hk).2 p hp).1.snd
    have hds := hdir _ _ _ hh.le N p hp k hk
    have hb : ∀ c : ℕ, c ≤ 2 →
        ‖iteratedDeriv c (fun t => (p t).2) k‖ ≤ L*Real.sqrt (h/(N : ℝ)) := by
      intro c hc
      interval_cases c
      · exact hds.1
      · simpa only [iteratedDeriv_one] using hds.2.1
      · simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hds.2.2
    have ht : (r-h)+4*h ∈ Icc (0 : ℝ) 1 := by
      have H := kStability_time_mem hr hh.le (hh0.trans (min_le_right _ _))
        (show (4 : ℝ) ∈ Icc (0 : ℝ) 4 by norm_num)
      constructor <;> linarith [H.1,H.2,D.q_mem.2]
    have hf := scalarData_massVariationTerminal_qPotential D 1 ht
    have H := C2BoundAt.linearObservation (by positivity : 0 ≤ L*Real.sqrt (h/(N : ℝ)))
      hpreg hb (fderiv ℝ (massVariationTerminal β α (r-h) h) x)
    apply H.mono
    calc
      _ ≤ B*(L*Real.sqrt (h/(N : ℝ))) :=
        mul_le_mul_of_nonneg_right (hf.fderiv_le le_rfl x) (by positivity)
      _ = _ := by ring
  · refine ⟨0,1,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

theorem orderedEnergyAssemblyTerm_inner_eq (β : ℝ) (α : ℝ → ℝ)
    (a s h : ℝ) (N : ℕ) (lam : ℝ) (j : Fin (12*N)) (hh : 0 ≤ h) (x : E) (k : ℝ) :
    orderedEnergyAssemblyTerm β α a s h N lam j x 0 k =
      let f := massVariationTerminal β α s h
      let w := (orderedWindowCurve β α a s h N lam j k).2
      let T := orderedInnerChain β α a (1/2) s h N lam j k
      let l := massPath (windowMassPath β α a (1/2) s h k N) lam
      (fderiv ℝ T x w)^2-(fderiv ℝ f x w)^2-
        2*fderiv ℝ f x w*pathGeneratorSum f (fun y => fderiv ℝ f y w) (l.drop (j.val+1)) x := by
  rw [orderedWindowCurve_apply β α a s h N lam j hh k]
  rfl

theorem orderedEnergyAssemblyTerm_inner_c2BoundAt (β : ℝ) (α : ℝ → ℝ)
    (a s h : ℝ) (N : ℕ) (lam : ℝ) (j : Fin (12*N)) (hh : 0 ≤ h) (x : E)
    {U H R k : ℝ}
    (ha : C2BoundAt U (fun t =>
      fderiv ℝ (massVariationTerminal β α s h) x
        (orderedWindowCurve β α a s h N lam j t).2) k)
    (hd : C2BoundAt H (fun t =>
      fderiv ℝ (orderedInnerChain β α a (1/2) s h N lam j t) x
        (orderedWindowCurve β α a s h N lam j t).2-
      fderiv ℝ (massVariationTerminal β α s h) x
        (orderedWindowCurve β α a s h N lam j t).2) k)
    (hr : C2BoundAt R (fun t =>
      fderiv ℝ (orderedInnerChain β α a (1/2) s h N lam j t) x
        (orderedWindowCurve β α a s h N lam j t).2-
      fderiv ℝ (massVariationTerminal β α s h) x
        (orderedWindowCurve β α a s h N lam j t).2-
      pathGeneratorSum (massVariationTerminal β α s h)
        (fun y => fderiv ℝ (massVariationTerminal β α s h) y
          (orderedWindowCurve β α a s h N lam j t).2)
        ((massPath (windowMassPath β α a (1/2) s h t N) lam).drop (j.val+1)) x) k) :
    C2BoundAt (4*H^2+8*U*R) (orderedEnergyAssemblyTerm β α a s h N lam j x 0) k := by
  have he : orderedEnergyAssemblyTerm β α a s h N lam j x 0 =
      (fun t =>
        (fderiv ℝ (orderedInnerChain β α a (1/2) s h N lam j t) x
          (orderedWindowCurve β α a s h N lam j t).2)^2-
        (fderiv ℝ (massVariationTerminal β α s h) x
          (orderedWindowCurve β α a s h N lam j t).2)^2-
        2*fderiv ℝ (massVariationTerminal β α s h) x
          (orderedWindowCurve β α a s h N lam j t).2*
        pathGeneratorSum (massVariationTerminal β α s h)
          (fun y => fderiv ℝ (massVariationTerminal β α s h) y
            (orderedWindowCurve β α a s h N lam j t).2)
          ((massPath (windowMassPath β α a (1/2) s h t N) lam).drop (j.val+1)) x) := by
    funext t
    exact orderedEnergyAssemblyTerm_inner_eq β α a s h N lam j hh x t
  rw [he]
  exact C2BoundAt.square_firstOrder ha hd hr

end SKBarriers2.Corner
