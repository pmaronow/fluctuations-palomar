module

public import SKBarriers2.Corner.PathEnergyProof4

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.Corner

open StepCalculus
local notation "E" => (Fin 3 → ℝ)
local notation "Curve" => (ℝ → ℝ × E)

def pathEnergyAssemblyTerms (front middle tail : List (ℝ × E))
    (f : E → ℝ) (w x : E) : Fin 4 → ℝ :=
  let F := vectorIncrementChain middle f
  let T := vectorIncrementChain tail f
  let psi := fun y => (fderiv ℝ f y w)^2
  let delta := fun y => (fderiv ℝ T y w)^2-psi y
  ![(fderiv ℝ T x w)^2-psi x-
      2*fderiv ℝ f x w*pathGeneratorSum f (fun y => fderiv ℝ f y w) tail x,
    tiltedPathTaylorDefect front F psi x,
    pathGeneratorSum F psi front x-pathGeneratorSum f psi front x,
    vectorIncrementAverage front F delta x-delta x]

def orderedEnergyAssemblyTerm (β : ℝ) (α : ℝ → ℝ) (a s h : ℝ) (N : ℕ)
    (lam : ℝ) (j : Fin (12*N)) (x : E) (i : Fin 4) (k : ℝ) : ℝ :=
  let l := massPath (windowMassPath β α a (1/2) s h k N) lam
  let jj := windowEntryIndex β α a (1/2) s h k N j
  pathEnergyAssemblyTerms (l.take j.val) (l.drop j.val) (l.drop (j.val+1))
    (massVariationTerminal β α s h)
    ((windowMassPath β α a (1/2) s h k N).get jj).2.2 x i

def WindowEnergyTermC2 (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) (i : Fin 4) : Prop :=
  ∃ C h0 kap : ℝ, 0 ≤ C ∧ 0 < h0 ∧ 0 < kap ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ eps : ℝ, 0 < eps →
      ∀ᶠ N : ℕ in atTop, ∀ lam ∈ Icc (0:ℝ) 1, ∀ j : Fin (12*N),
        ∀ k : ℝ, |k| ≤ kap → ∀ x : E,
          C2BoundAt (C*(Real.sqrt h*h^2)/(N:ℝ)+eps/(N:ℝ))
            (orderedEnergyAssemblyTerm β α (α (r-h)) (r-h) h N lam j x i) k

def WindowInnerEnergyC2 {β : ℝ} (D : ScalarData β) (I : Set ℝ) : Prop :=
  WindowEnergyTermC2 β (cdf (D.μ : Measure ℝ)) I 0

def WindowGeneratorComparisonC2 {β : ℝ} (D : ScalarData β) (I : Set ℝ) : Prop :=
  WindowEnergyTermC2 β (cdf (D.μ : Measure ℝ)) I 2

def WindowInnerBiasC2 {β : ℝ} (D : ScalarData β) (I : Set ℝ) : Prop :=
  WindowEnergyTermC2 β (cdf (D.μ : Measure ℝ)) I 3

def prefixEnergyDefect (β : ℝ) (α : ℝ → ℝ) (a s h : ℝ) (N : ℕ)
    (lam : ℝ) (j : Fin (12*N)) (qs : List Curve) (k : ℝ) (x : E) : ℝ :=
  let l := massPath (windowMassPath β α a (1/2) s h k N) lam
  let F := vectorIncrementChain (l.drop j.val) (massVariationTerminal β α s h)
  let w := (orderedWindowCurve β α a s h N lam j k).2
  tiltedPathTaylorDefect (qs.map (fun p => p k)) F
    (fun y => (fderiv ℝ (massVariationTerminal β α s h) y w)^2) x

def WindowPrefixEnergyRecursions {β : ℝ} (D : ScalarData β) (I : Set ℝ) : Prop :=
  ∃ K C h0 kap : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ 0 < h0 ∧ 0 < kap ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ eps : ℝ, 0 < eps →
      ∀ᶠ N : ℕ in atTop, ∀ lam ∈ Icc (0:ℝ) 1, ∀ j : Fin (12*N),
        ∀ k : ℝ, |k| ≤ kap →
          let α := cdf (D.μ : Measure ℝ)
          let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
          let qs := ps.take j.val
          let R := prefixEnergyDefect β α (α (r-h)) (r-h) h N lam j
          let e := windowVariationEnergy k
          let B := (C*(Real.sqrt h*h)+eps)/(N:ℝ)
          ∃ a b c : List Curve → ℝ,
            a [] ≤ 0 ∧ b [] ≤ 0 ∧ c [] ≤ 0 ∧
            (∀ front tail, qs = front++tail →
              (∀ x, ContDiffAt ℝ 2 (fun t => R tail t x) k) ∧
              QBoundedJets 4 (a tail) (R tail k) ∧
              QBoundedJets 2 (b tail) (fun x => deriv (fun t => R tail t x) k) ∧
              QBoundedJets 0 (c tail) (fun x => deriv (deriv (fun t => R tail t x)) k)) ∧
            (∀ front p tail, qs = front++p::tail →
              a (p::tail) ≤ (1+K*e p)*a tail+B*e p) ∧
            (∀ front p tail, qs = front++p::tail →
              b (p::tail) ≤ (1+K*e p)*b tail+K*e p*a tail+B*e p) ∧
            (∀ front p tail, qs = front++p::tail →
              c (p::tail) ≤ (1+K*e p)*c tail+K*e p*(a tail+b tail)+B*e p)

theorem prefixEnergyDefect_nil (β : ℝ) (α : ℝ → ℝ) (a s h : ℝ) (N : ℕ)
    (lam : ℝ) (j : Fin (12*N)) (k : ℝ) (x : E) :
    prefixEnergyDefect β α a s h N lam j [] k x = 0 := by
  simp only [prefixEnergyDefect,List.map_nil,tiltedPathTaylorDefect,
    vectorIncrementAverage,pathGeneratorSum,sub_self]

theorem prefixEnergyDefect_eq_term (β : ℝ) (α : ℝ → ℝ) (a s h : ℝ) (N : ℕ)
    (lam : ℝ) (j : Fin (12*N)) (hh : 0 ≤ h) (x : E) :
    (fun k => prefixEnergyDefect β α a s h N lam j
      ((windowKCurves β (interpolatedProfile α a lam) s h N).take j.val) k x) =
      orderedEnergyAssemblyTerm β α a s h N lam j x 1 := by
  funext k
  dsimp only [prefixEnergyDefect,orderedEnergyAssemblyTerm,pathEnergyAssemblyTerms]
  rw [List.map_take,windowKCurves_apply β _ s h k N hh,
    ← massPath_window_eq β α a lam (1/2) s h k N,
    orderedWindowCurve_apply β α a s h N lam j hh k]
  rfl

theorem windowEnergyTermC2_of_prefixRecursions {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (hparts : WindowPrefixEnergyRecursions D (Icc l u)) :
    WindowEnergyTermC2 β (cdf (D.μ : Measure ℝ)) (Icc l u) 1 := by
  by_cases hlu : l ≤ u
  · obtain ⟨K,C,hP,kap,hK,hC,hhP,hkap,hparts⟩ := hparts
    obtain ⟨A,a0,hV,hA,_,hhV,hvar⟩ :=
      scalarData_interpolated_window_variation_inputs D hl hlu hu
    have hden : 0 < 2*K*A+1 := by positivity
    refine ⟨8*A*C,min hP (min hV (min 1 (1/(2*K*A+1)))),min kap (1/2),
      by positivity,lt_min hhP (lt_min hhV (lt_min (by norm_num) (by positivity))),
      lt_min hkap (by norm_num),?_⟩
    intro r hr h hh hh0 eps heps
    have hhP' := hh0.trans (min_le_left _ _)
    have hhV' := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hh1 := hh0.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    have hhshort := hh0.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
    let δ := eps/(8*A+1)
    have hδ : 0 < δ := by dsimp only [δ]; positivity
    filter_upwards [hparts r hr h hh hhP' δ hδ,eventually_ge_atTop (1:ℕ)] with N hn hN
    intro lam hlam j k hk x
    let α := cdf (D.μ : Measure ℝ)
    let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
    let qs := ps.take j.val
    let e := windowVariationEnergy k
    let R := prefixEnergyDefect β α (α (r-h)) (r-h) h N lam j
    let B := (C*(Real.sqrt h*h)+δ)/(N:ℝ)
    have hB : 0 ≤ B := by dsimp only [B]; positivity
    have hNpos : (0:ℝ) < N := Nat.cast_pos.mpr hN
    have hE : variationEnergy e ps ≤ A*h :=
      (hvar r hr h hh hhV' N hN lam hlam k (hk.trans (min_le_right _ _))).1
    have hEq : variationEnergy e qs ≤ variationEnergy e ps := by
      have H := variationEnergy_nonneg
        (fun p (_ : p ∈ ps.drop j.val) => windowVariationEnergy_nonneg k p)
      have heq := congrArg (variationEnergy e) (List.take_append_drop j.val ps)
      rw [variationEnergy_append] at heq
      dsimp only [qs]
      linarith only [H,heq]
    have hsmall : 2*K*variationEnergy e qs ≤ 1 := by
      have H := (le_div_iff₀ hden).mp hhshort
      have HE := mul_le_mul_of_nonneg_left (hEq.trans hE) (show 0 ≤ 2*K by positivity)
      nlinarith only [H,HE,hh.le]
    obtain ⟨a,b,c,ha0,hb0,hc0,henv,hvalue,hfirst,hsecond⟩ :=
      hn lam hlam j k (hk.trans (min_le_left _ _))
    obtain ⟨ha,hb,hc⟩ := pathEnergy_three_level_recursion_le hK hB a b c qs
      (fun p _ => windowVariationEnergy_nonneg k p) ha0 hb0 hc0
      hvalue hfirst hsecond hsmall
    have hfinal : 8*B*variationEnergy e qs ≤
        (8*A*C)*(Real.sqrt h*h^2)/(N:ℝ)+eps/(N:ℝ) := by
      have hδeps : 8*A*δ ≤ eps := by
        have H : 8*A/(8*A+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
        have H' := mul_le_of_le_one_right heps.le H
        convert H' using 1
        dsimp only [δ]
        ring
      have hδh : 8*A*δ*h ≤ eps :=
        (mul_le_of_le_one_right (by positivity) hh1).trans hδeps
      calc
        _ ≤ 8*B*(A*h) := mul_le_mul_of_nonneg_left (hEq.trans hE) (by positivity)
        _ = (8*A*C)*(Real.sqrt h*h^2)/(N:ℝ)+(8*A*δ*h)/(N:ℝ) := by
          dsimp only [B]; ring
        _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_right hδh hNpos.le)
    obtain ⟨hRc,hRa,hRb,hRc2⟩ := henv [] qs rfl
    have hE0 := variationEnergy_nonneg (fun p (_ : p ∈ qs) => windowVariationEnergy_nonneg k p)
    have ha' : a qs ≤ (8*A*C)*(Real.sqrt h*h^2)/(N:ℝ)+eps/(N:ℝ) := by
      apply ha.trans
      apply le_trans _ hfinal
      nlinarith only [mul_nonneg hB hE0]
    have hb' : b qs ≤ (8*A*C)*(Real.sqrt h*h^2)/(N:ℝ)+eps/(N:ℝ) := by
      apply hb.trans
      apply le_trans _ hfinal
      nlinarith only [mul_nonneg hB hE0]
    have hc' := hc.trans hfinal
    have H : C2BoundAt ((8*A*C)*(Real.sqrt h*h^2)/(N:ℝ)+eps/(N:ℝ))
        (fun t => R qs t x) k := by
      refine ⟨by positivity,hRc x,?_⟩
      intro d hd
      interval_cases d
      · simpa only [iteratedDeriv_zero,Real.norm_eq_abs] using (hRa.norm_le x).trans ha'
      · simpa only [iteratedDeriv_one,Real.norm_eq_abs] using (hRb.norm_le x).trans hb'
      · simpa only [iteratedDeriv_succ,iteratedDeriv_zero,Real.norm_eq_abs] using
          (hRc2.norm_le x).trans hc'
    change C2BoundAt _ (orderedEnergyAssemblyTerm β α (α (r-h)) (r-h) h N lam j x 1) k
    rw [← prefixEnergyDefect_eq_term β α (α (r-h)) (r-h) h N lam j hh.le x]
    exact H
  · refine ⟨0,1,1,by norm_num,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

theorem pathEnergyAssemblyTerms_sum {B BT : ℝ} {f : E → ℝ}
    (front middle tail : List (ℝ × E)) (hf : QPotential 3 B f)
    (hT : QPotential 3 BT (vectorIncrementChain tail f))
    (w x : E) :
    vectorIncrementAverage front (vectorIncrementChain middle f)
        (fun y => (fderiv ℝ (vectorIncrementChain tail f) y w)^2) x-
      firstOrderPathEnergy front tail f w x =
        ∑ i : Fin 4, pathEnergyAssemblyTerms front middle tail f w x i := by
  let F := vectorIncrementChain middle f
  let T := vectorIncrementChain tail f
  let psi := fun y => (fderiv ℝ f y w)^2
  let delta := fun y => (fderiv ℝ T y w)^2-psi y
  have hD := hf.derivativeJets.apply_const w
  have hDT := hT.derivativeJets.apply_const w
  have hpsi : QBoundedJets 2 ((2:ℝ)^2*(B*‖w‖)*(B*‖w‖)) psi := by
    convert hD.mul hD using 1
    funext y; ring
  have hdelta : QBoundedJets 2
      ((2:ℝ)^2*(BT*‖w‖)*(BT*‖w‖)+(2:ℝ)^2*(B*‖w‖)*(B*‖w‖)) delta := by
    convert (hDT.mul hDT).sub hpsi using 1
    funext y; ring
  have hobs : (fun y => (fderiv ℝ T y w)^2) = fun y => psi y+delta y := by
    funext y
    dsimp only [delta]
    ring
  have hadd : vectorIncrementAverage front F (fun y => (fderiv ℝ T y w)^2) x =
      vectorIncrementAverage front F psi x+vectorIncrementAverage front F delta x := by
    rw [hobs]
    exact congrFun (vectorIncrementAverage_add front
      (vectorIncrementChain_regular middle (hf.boundedDerivs (by norm_num)))
      hpsi.smooth.continuous hdelta.smooth.continuous
      ((qBoundedJets_iff_qBddSmooth.mp hpsi).potential.boundedDerivs (by norm_num)).hasExpGrowth
      ((qBoundedJets_iff_qBddSmooth.mp hdelta).potential.boundedDerivs (by norm_num)).hasExpGrowth) x
  change vectorIncrementAverage front F (fun y => (fderiv ℝ T y w)^2) x-_ = _
  rw [hadd]
  simp only [pathEnergyAssemblyTerms,tiltedPathTaylorDefect,firstOrderPathEnergy,
    Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero]
  dsimp only [F,T,psi,delta]
  ring

theorem orderedPathExpansionRemainder_eq_terms {β : ℝ} {α : ℝ → ℝ}
    (a s h : ℝ) (N : ℕ) (lam : ℝ) (j : Fin (12*N)) (z k : ℝ)
    {B BT : ℝ} (hf : QPotential 3 B (massVariationTerminal β α s h))
    (hT : QPotential 3 BT (orderedInnerChain β α a (1/2) s h N lam j k)) :
    orderedPathExpansionRemainder β α a (1/2) s h N lam j z k =
      (∑ i : Fin 4, orderedEnergyAssemblyTerm β α a s h N lam j (fun _ => z) i k)/2 := by
  let l := massPath (windowMassPath β α a (1/2) s h k N) lam
  let w := ((windowMassPath β α a (1/2) s h k N).get
    (windowEntryIndex β α a (1/2) s h k N j)).2.2
  have H := pathEnergyAssemblyTerms_sum (l.take j.val) (l.drop j.val) (l.drop (j.val+1))
    hf hT w (fun _ => z)
  change (_-_)/2 = _
  unfold windowGradientEnergy
  simp only [massPath,List.map_take,List.map_drop] at H ⊢
  exact congrArg (fun t : ℝ => t/2) H

theorem scalarData_pathEnergyC2_of_parts {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (h1 : WindowInnerEnergyC2 D (Icc l u))
    (h2 : WindowGeneratorComparisonC2 D (Icc l u))
    (h3 : WindowInnerBiasC2 D (Icc l u))
    (h4 : WindowPrefixEnergyRecursions D (Icc l u)) :
    PathEnergyC2 β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  let α : ℝ → ℝ := cdf (D.μ : Measure ℝ)
  obtain ⟨C0,h00,kap0,hC0,hh00,hkap0,h0⟩ := h1
  obtain ⟨C1,h01,kap1,hC1,hh01,hkap1,h1⟩ :=
    windowEnergyTermC2_of_prefixRecursions D hl hu h4
  obtain ⟨C2,h02,kap2,hC2,hh02,hkap2,h2⟩ := h2
  obtain ⟨C3,h03,kap3,hC3,hh03,hkap3,h3⟩ := h3
  obtain ⟨K,hS,hK,hhS,hself⟩ := scalarData_orderedPathSelfInteraction_c2BoundAt D hl hu
  obtain ⟨B,a0,L,hE,kapE,_,_,_,hhE,hkapE,hentropy⟩ :=
    scalarData_uniformWindowEntropyInputs D hl hu
  let C := C0+C1+C2+C3
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C,min h00 (min h01 (min h02 (min h03 (min hS
      (min hE (kStabilityInteriorRadius D.q l u)))))),
    min kap0 (min kap1 (min kap2 (min kap3 (min (kapE/2) (1/4))))),hC,
    lt_min hh00 (lt_min hh01 (lt_min hh02 (lt_min hh03 (lt_min hhS
      (lt_min hhE (kStabilityInteriorRadius_pos hl hu)))))),
    lt_min hkap0 (lt_min hkap1 (lt_min hkap2 (lt_min hkap3
      (lt_min (by positivity) (by norm_num))))),?_⟩
  intro r hr h hh hh0 eps heps
  simp only [le_min_iff] at hh0
  obtain ⟨hh0,hh1,hh2,hh3,hhS',hhE',hhI⟩ := hh0
  have ht : (r-h)+4*h ∈ Icc (0:ℝ) 1 := by
    have H := kStability_time_mem hr hh.le hhI (show (4:ℝ) ∈ Icc (0:ℝ) 4 by norm_num)
    constructor <;> linarith [H.1,H.2,D.q_mem.2]
  have hf := scalarData_massVariationTerminal_qPotential D 3 ht
  have hφ : ContDiff ℝ 5 (Phi β α ((r-h)+4*h)) :=
    (scalarData_phi_contDiff D ht).of_le (by simp)
  have hlim : Tendsto (fun N : ℕ => K*h^2/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [h0 r hr h hh hh0 (eps/4) (by positivity),
    h1 r hr h hh hh1 (eps/4) (by positivity),
    h2 r hr h hh hh2 (eps/4) (by positivity),
    h3 r hr h hh hh3 (eps/4) (by positivity),
    hlim.eventually (eventually_le_nhds (by positivity : (0:ℝ) < eps/2)),
    eventually_ge_atTop (1:ℕ)] with N hn0 hn1 hn2 hn3 hsmall hN
  intro lam hlam z j k hk
  simp only [le_min_iff] at hk
  obtain ⟨hk0,hk1,hk2,hk3,hkE,hkquarter⟩ := hk
  have hkhalf : |k| ≤ 1/2 := hkquarter.trans (by norm_num)
  have hkEstrict : |k| < kapE := lt_of_le_of_lt hkE (by linarith)
  have hkstrict : |k| < min kapE (1/2) := lt_min hkEstrict (lt_of_le_of_lt hkquarter (by norm_num))
  let T := fun i => orderedEnergyAssemblyTerm β α (α (r-h)) (r-h) h N lam j (fun _ => z) i
  let U := fun t => (T 0 t+T 1 t+T 2 t+T 3 t)/2
  let S := orderedPathSelfInteraction β α (α (r-h)) (1/2) (r-h) h N lam j z
  let P := orderedPathEnergyRemainder β α (α (r-h)) (1/2) (r-h) h N lam j z
  have H0 := hn0 lam hlam j k hk0 (fun _ => z)
  have H1 := hn1 lam hlam j k hk1 (fun _ => z)
  have H2 := hn2 lam hlam j k hk2 (fun _ => z)
  have H3 := hn3 lam hlam j k hk3 (fun _ => z)
  have HU := (((H0.add H1).add H2).add H3).const_mul (1/2:ℝ)
  have HU' : C2BoundAt (C*(Real.sqrt h*h^2)/(N:ℝ)+((eps/2)/(N:ℝ))) U k := by
    have hUeq : (fun t => (1/2:ℝ)*
        (((T 0 t+T 1 t)+T 2 t)+T 3 t)) = U := by funext t; dsimp only [U]; ring
    change C2BoundAt _ (fun t => (1/2:ℝ)*(((T 0 t+T 1 t)+T 2 t)+T 3 t)) k at HU
    rw [hUeq] at HU
    apply HU.mono
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    have H : 0 ≤ C*(Real.sqrt h*h^2)/(N:ℝ) := by positivity
    calc
      _ = (1/2:ℝ)*(C*(Real.sqrt h*h^2)/(N:ℝ))+(eps/2)/(N:ℝ) := by
        dsimp only [C]; ring
      _ ≤ _ := add_le_add (mul_le_of_le_one_left H (by norm_num)) le_rfl
  have HS := hself r hr h hh hhS' N hN lam hlam z j k hkhalf
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hSsmall : K*h^2/(N:ℝ)^2 ≤ (eps/2)/(N:ℝ) := by
    have H := div_le_div_of_nonneg_right hsmall hn.le
    simpa only [div_div,← pow_two] using H
  have HS' : C2BoundAt ((eps/2)/(N:ℝ)) (fun t => (-1/2:ℝ)*S t) k := by
    apply (HS.const_mul (-1/2:ℝ)).mono
    norm_num only [abs_neg,abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    exact (mul_le_of_le_one_left (by positivity : 0 ≤ K*h^2/(N:ℝ)^2)
      (by norm_num : (1/2:ℝ) ≤ 1)).trans hSsmall
  have he : P =ᶠ[𝓝 k] (fun t => U t+(-1/2:ℝ)*S t) := by
    filter_upwards [continuous_abs.continuousAt.eventually (gt_mem_nhds hkstrict)] with t ht'
    have htE := (lt_min_iff.mp ht').1.le
    have hthalf := (lt_min_iff.mp ht').2.le
    obtain ⟨_,hEN⟩ := hentropy r hr h hh hhE' t htE N hN
    obtain ⟨hinner,_⟩ := hEN lam hlam
    have hT : QPotential 3 B (orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j t) := by
      simpa only [orderedInnerChain,massPath,List.map_drop,windowEntryIndex] using
        (hinner j.val (by rw [windowMassPath_length]; exact j.isLt)).of_le (by norm_num : 3 ≤ 10)
    change orderedPathEnergyRemainder β α (α (r-h)) (1/2) (r-h) h N lam j z t = _
    rw [orderedPathEnergyRemainder_eq_expansion_sub_self β α (α (r-h)) (r-h) h
      (by omega) lam j z t hh.le hthalf hφ,
      orderedPathExpansionRemainder_eq_terms (α := α) (α (r-h)) (r-h) h N lam j z t hf hT]
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (T 0 t+(T 1 t+(T 2 t+T 3 t)))/2-S t/2 = U t+(-1/2:ℝ)*S t
    dsimp only [U]
    ring
  have HP := HU'.add HS'
  refine ⟨HP.smooth.congr_of_eventuallyEq he,?_⟩
  rw [he.iteratedDeriv_eq 2]
  exact (HP.bound 2 le_rfl).trans_eq (by ring)

end SKBarriers2.Corner
