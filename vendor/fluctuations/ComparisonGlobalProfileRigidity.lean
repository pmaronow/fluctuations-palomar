module

public import FiniteProfileRigidity
public import ComparisonWholeCapEndpoints
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 5000000

def comparisonIncrementSupport (V : ℝ → ℝ) : Set ℝ :=
  {t | ∀eps : ℝ,0< eps → V (t-eps)< V (t+eps)}

theorem comparison_outside_increment_support_locally_constant
    {V : ℝ → ℝ} (hV : Monotone V) {t : ℝ} (ht : t∉comparisonIncrementSupport V) :
    ∃eps : ℝ,0< eps ∧ ∀r∈Icc (t-eps) (t+eps),V r=V t := by
  change ¬∀eps : ℝ,0< eps → V (t-eps)< V (t+eps) at ht
  push Not at ht
  obtain ⟨eps,heps,hh⟩ := ht
  have he : V (t-eps)=V (t+eps) := le_antisymm (hV (by linarith)) hh
  refine ⟨eps,heps,?_⟩
  intro r hr
  have hl := hV hr.1
  have hh := hV hr.2
  have ht1 := hV (show t-eps≤ t by linarith)
  have ht2 := hV (show t≤ t+eps by linarith)
  linarith

theorem comparison_increment_support_isClosed {V : ℝ → ℝ} (hV : Monotone V) :
    IsClosed (comparisonIncrementSupport V) := by
  rw [←isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  obtain ⟨eps,heps,hconst⟩ := comparison_outside_increment_support_locally_constant hV ht
  have hn : Ioo (t-eps/2) (t+eps/2)⊆(comparisonIncrementSupport V)ᶜ := by
    intro r hr hs
    have hsl := hs (eps/2) (by linarith)
    have hl := hconst (r-eps/2) ⟨by linarith [hr.1],by linarith [hr.2]⟩
    have hh := hconst (r+eps/2) ⟨by linarith [hr.1],by linarith [hr.2]⟩
    linarith
  exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds (show t∈Ioo (t-eps/2) (t+eps/2) by constructor <;> linarith)) hn

theorem comparison_increment_support_gap_constant {V : ℝ → ℝ} (hV : Monotone V)
    {a b : ℝ} (hgap : ∀r∈Ioo a b,r∉comparisonIncrementSupport V) :
    ∀r∈Ioo a b,∀s∈Ioo a b,V r=V s := by
  have hd r (hr : r∈Ioo a b) : HasDerivAt V 0 r := by
    obtain ⟨eps,heps,hconst⟩ := comparison_outside_increment_support_locally_constant hV (hgap r hr)
    apply (hasDerivAt_const r (V r)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds (show r∈Ioo (r-eps) (r+eps) by constructor <;> linarith)] with t ht
    exact hconst t ⟨ht.1.le,ht.2.le⟩
  intro r hr s hs
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun t ht=>(hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht=>(hd t ht).deriv) hr hs

theorem comparison_increment_support_nonnegative {V : ℝ → ℝ}
    (hnegative : ∀t<0,V t=0) : comparisonIncrementSupport V⊆Ici (0:ℝ) := by
  intro t ht
  by_contra hn
  have htn : t<0 := lt_of_not_ge hn
  have hh := ht (-t/2) (by linarith)
  rw [hnegative _ (by linarith),hnegative _ (by linarith)] at hh
  exact lt_irrefl _ hh

theorem comparison_cdf_nonnegative {V : ℝ → ℝ} (hV : Monotone V)
    (hnegative : ∀t<0,V t=0) (t : ℝ) : 0≤ V t := by
  by_cases ht : t<0
  · rw [hnegative t ht]
  · have hh := hV (show (-1:ℝ)≤ t by linarith [not_lt.mp ht])
    rw [hnegative (-1) (by norm_num)] at hh
    exact hh

theorem comparison_increment_support_positive_cdf_after {V : ℝ → ℝ} (hV : Monotone V)
    (hnegative : ∀t<0,V t=0) {a r : ℝ} (ha : a∈comparisonIncrementSupport V) (har : a< r) :
    0< V r := by
  have hp := ha ((r-a)/2) (by linarith)
  have hn := comparison_cdf_nonnegative hV hnegative (a-(r-a)/2)
  exact (lt_of_le_of_lt hn hp).trans_le (hV (by linarith))

theorem comparison_increment_support_unbounded {V : ℝ → ℝ} (hV : Monotone V)
    {c R : ℝ} (hc : 0< c) (hgrowth : ∀t,R≤ t → c*t≤ V t) :
    ¬BddAbove (comparisonIncrementSupport V) := by
  rintro ⟨M,hM⟩
  let a := M+1
  let b := max (max R (a+1)) ((V a+1)/c)
  have hab : a< b := lt_of_lt_of_le (by dsimp [a];linarith : a< a+1) ((le_max_right R (a+1)).trans (le_max_left _ _))
  have hbR : R≤ b := (le_max_left R (a+1)).trans (le_max_left _ _)
  have hbC : (V a+1)/c≤ b := le_max_right _ _
  have hgap : ∀r∈Ioo M (b+1),r∉comparisonIncrementSupport V := by
    intro r hr hs
    have hh := hM hs
    linarith [hr.1]
  have he := comparison_increment_support_gap_constant hV hgap a
    (show a∈Ioo M (b+1) by dsimp [a];constructor <;> linarith) b
    (show b∈Ioo M (b+1) by dsimp [a] at hab;constructor <;> linarith)
  have hh := hgrowth b hbR
  have hcb := (div_le_iff₀ hc).mp hbC
  linarith

structure ComparisonVirtualGapData (g : ℝ → ℝ) (a b : ℝ) where
  H : ℝ → ℝ
  F : ℝ → ℝ
  nonnegative : ∀t∈Icc a b,0≤ H t
  left_zero : H a=0
  right_zero : H b=0
  integrable : IntervalIntegrable F volume a b
  primitive_left : ∀z∈Icc a b,H z-H a=∫t in a..z,F t
  primitive_right : ∀z∈Icc a b,H b-H z=∫t in z..b,F t
  behavior : (∀ᵐ t ∂volume.restrict (Ioo a b),
      (0< g t → F t<0) ∧ (g t<0 → 0< F t)) ∨
    ∃spin strength : ℝ → ℝ,∀ᵐ t ∂volume.restrict (Ioo a b),
      spin t∈Icc a b ∧ 0< strength t ∧ g (spin t)=strength t*(spin t-t) ∧
      (t< spin t → F t<0) ∧ (spin t< t → 0< F t)

theorem comparison_affine_gap_derivative_from_primitive
    {U gp : ℝ → ℝ} {A B C a b : ℝ} (ha : 0≤ a) (_hab : a< b)
    (hprim : ∀s t,0≤ s → s≤ t → gp t-gp s=∫r in s..t,A*r-B*U r)
    (hconst : ∀ᵐ r ∂volume.restrict (Ioo a b),U r=C) :
    ∀t∈Ico a b,HasDerivWithinAt gp (A*t-B*C) (Ici t) t := by
  have hconstGlobal := (ae_restrict_iff' measurableSet_Ioo).mp hconst
  let p := fun t : ℝ=> gp a+A/2*(t^2-a^2)-B*C*(t-a)
  have hpd t : HasDerivAt p (A*t-B*C) t := by
    dsimp [p]
    convert ((hasDerivAt_const t (gp a)).add
      ((((hasDerivAt_id t).pow 2).sub_const (a^2)).const_mul (A/2))).sub
      (((hasDerivAt_id t).sub_const a).const_mul (B*C)) using 1 <;> (try ext y) <;> (dsimp; try ring)
  have he t (ht : t∈Icc a b) : gp t=p t := by
    have hint : (∫r in a..t,A*r-B*U r)=∫r in a..t,A*r-B*C := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hconstGlobal,volume.ae_ne b] with r hr hrb hri
      rw [uIoc_of_le ht.1] at hri
      have hgap : r∈Ioo a b := ⟨hri.1,lt_of_le_of_ne (hri.2.trans ht.2) hrb⟩
      rw [hr hgap]
    have hpoly : (∫r in a..t,A*r-B*C)=A/2*(t^2-a^2)-B*C*(t-a) := by
      have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun r _=> hpd r) ((continuous_const.mul continuous_id |>.sub continuous_const).intervalIntegrable a t)
      dsimp [p] at hh
      linarith
    have hp := hprim a t ha ht.1
    rw [hint,hpoly] at hp
    dsimp [p]
    linarith
  intro t ht
  have hlocal : gp =ᶠ[𝓝[Ici t] t] p := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds ht.2).filter_mono nhdsWithin_le_nhds] with r hr hrt
    exact he r ⟨ht.1.trans hr,hrt.le⟩
  exact (hpd t).hasDerivWithinAt.congr_of_eventuallyEq_of_mem hlocal (by simp)

theorem comparison_increment_gap_contradiction
    {U V g gp : ℝ → ℝ} {a b A B : ℝ} (hV : Monotone V) (hA : 0< A)
    (ha : 0≤ a) (hab : a< b) (hUV : U=ᵐ[volume] V)
    (hg : ∀t,0≤ t → HasDerivAt g (gp t) t) (hgpC : ContinuousOn gp (Ici (0:ℝ)))
    (hprim : ∀s t,0≤ s → s≤ t → gp t-gp s=∫r in s..t,A*r-B*U r)
    (hga : g a=0) (hgb : g b=0)
    (hgap : ∀r∈Ioo a b,r∉comparisonIncrementSupport V)
    (data : ComparisonVirtualGapData g a b) : False := by
  let C := V ((a+b)/2)
  have hconst : ∀ᵐ r ∂volume.restrict (Ioo a b),U r=C := by
    filter_upwards [ae_restrict_of_ae hUV,ae_restrict_mem measurableSet_Ioo] with r hr hri
    rw [hr]
    exact comparison_increment_support_gap_constant hV hgap r hri ((a+b)/2) (by constructor <;> linarith)
  have hgp := comparison_affine_gap_derivative_from_primitive ha hab hprim hconst
  have hsub : Icc a b⊆Ici (0:ℝ) := fun t ht=> ha.trans ht.1
  have hgc : ContinuousOn g (Icc a b) := fun t ht=>(hg t (hsub ht)).continuousAt.continuousWithinAt
  have hgpc := hgpC.mono hsub
  have hgd : ∀t∈Ico a b,HasDerivWithinAt g (gp t) (Ici t) t :=
    fun t ht=>(hg t (ha.trans ht.1)).hasDerivWithinAt
  rcases data.behavior with hs|⟨spin,strength,hs⟩
  · exact no_gap_of_scalar_sign_virtual_potential hab hA g gp data.H data.F hgc hgpc hgd hgp
      (hg a ha) (hg b (ha.trans hab.le)) hga hgb data.nonnegative data.left_zero data.right_zero
      data.integrable data.primitive_left data.primitive_right hs
  · exact no_gap_of_bounded_strength_virtual_potential hab hA g gp data.H data.F spin strength
      hgc hgpc hgd hgp (hg a ha) (hg b (ha.trans hab.le)) hga hgb data.nonnegative
      data.left_zero data.right_zero data.integrable data.primitive_left data.primitive_right hs

theorem comparison_increment_support_tail
    {V : ℝ → ℝ} (hV : Monotone V) (hnegative : ∀t<0,V t=0)
    (hunbounded : ¬BddAbove (comparisonIncrementSupport V))
    (hgapFalse : ∀a b,0≤ a → a< b → a∈comparisonIncrementSupport V → b∈comparisonIncrementSupport V → 
      (∀r∈Ioo a b,r∉comparisonIncrementSupport V) → False) :
    let S := comparisonIncrementSupport V
    S.Nonempty ∧ 0≤ sInf S ∧ sInf S∈S ∧ Ioi (sInf S)⊆S := by
  let S := comparisonIncrementSupport V
  have hne : S.Nonempty := by
    by_contra hn
    have he : S=∅ := Set.not_nonempty_iff_eq_empty.mp hn
    exact hunbounded (by change BddAbove S;rw [he];exact bddAbove_empty)
  have hlo : BddBelow S := ⟨0,comparison_increment_support_nonnegative hnegative⟩
  have hl : 0≤ sInf S := le_csInf hne (fun t ht=> comparison_increment_support_nonnegative hnegative ht)
  have hls : sInf S∈S := (comparison_increment_support_isClosed hV).csInf_mem hne hlo
  refine ⟨hne,hl,hls,?_⟩
  intro t ht
  by_contra hnt
  obtain ⟨a0,ha0,ha0t⟩ := exists_lt_of_csInf_lt hne ht
  have hex : ∃b0∈S,t< b0 := by
    by_contra hn
    push Not at hn
    exact hunbounded ⟨t,hn⟩
  obtain ⟨b0,hb0,htb0⟩ := hex
  let G := Ioo a0 b0∩Sᶜ
  have hG : IsOpen G := isOpen_Ioo.inter (comparison_increment_support_isClosed hV).isOpen_compl
  have htG : t∈G := ⟨⟨ha0t,htb0⟩,hnt⟩
  obtain ⟨hal,hat,htb,hbb,heq,haG,hbG⟩ := WholeUnitSideKernel.wholeCap_component_endpoints hG
    (show G⊆Icc a0 b0 from fun r hr=>⟨hr.1.1.le,hr.1.2.le⟩) htG
  let a := sInf (ordConnectedComponent G t)
  let b := sSup (ordConnectedComponent G t)
  change a0≤ a at hal
  change a< t at hat
  change t< b at htb
  change b≤ b0 at hbb
  have has : a∈S := by
    by_cases he : a=a0
    · simpa only [he] using ha0
    · by_contra hn
      exact haG ⟨⟨lt_of_le_of_ne hal (Ne.symm he),(hat.trans htb).trans_le hbb⟩,hn⟩
  have hbs : b∈S := by
    by_cases he : b=b0
    · simpa only [he] using hb0
    · by_contra hn
      exact hbG ⟨⟨hal.trans_lt (hat.trans htb),lt_of_le_of_ne hbb he⟩,hn⟩
  have hg : ∀r∈Ioo a b,r∉S := by
    intro r hr
    exact (ordConnectedComponent_subset (heq.symm ▸ hr)).2
  exact hgapFalse a b (comparison_increment_support_nonnegative hnegative has) (hat.trans htb) has hbs hg

theorem comparison_monotone_linear_ae_everywhere
    {U : ℝ → ℝ} {kappa : ℝ} (hU : Monotone U) (hk : 0< kappa)
    (hU0 : ∀t>0,0≤ U t) (hAE : ∀ᵐ t ∂volume,0< t → U t=kappa*t) :
    ∀t>0,U t=kappa*t := by
  have hselect a b (ha : 0≤ a) (hab : a< b) : ∃r∈Ioo a b,U r=kappa*r := by
    have hm : volume (Ioo a b)≠0 := by simp only [Real.volume_Ioo,ne_eq,ENNReal.ofReal_eq_zero];linarith
    obtain ⟨r,hr,he⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hm (ae_restrict_of_ae hAE)
    exact ⟨r,hr,he (ha.trans_lt hr.1)⟩
  intro t ht
  apply le_antisymm
  · by_contra hn
    have hh : kappa*t< U t := lt_of_not_ge hn
    let b := (U t/kappa+t)/2
    have htb : t< b := by dsimp [b];have he : t<U t/kappa := (lt_div_iff₀ hk).mpr (by nlinarith [hh]);nlinarith
    obtain ⟨r,hr,he⟩ := hselect t b ht.le htb
    have hm := hU hr.1.le
    rw [he] at hm
    have hkr : kappa*r< U t := by
      have hb := mul_lt_mul_of_pos_left hr.2 hk
      dsimp [b] at hb
      have he : kappa*(U t/kappa)=U t := mul_div_cancel₀ _ hk.ne'
      nlinarith
    linarith
  · by_contra hn
    have hh : U t< kappa*t := lt_of_not_ge hn
    let a := (U t/kappa+t)/2
    have hat : a< t := by dsimp [a];have he : U t/kappa<t := (div_lt_iff₀ hk).mpr (by nlinarith [hh]);nlinarith
    have ha : 0≤ a := by dsimp [a];exact div_nonneg (add_nonneg (div_nonneg (hU0 t ht) hk.le) ht.le) (by norm_num)
    obtain ⟨r,hr,he⟩ := hselect a t ha hat
    have hm := hU hr.2.le
    rw [he] at hm
    have hkr : U t< kappa*r := by
      have hb := mul_lt_mul_of_pos_left hr.1 hk
      dsimp [a] at hb
      have he : kappa*(U t/kappa)=U t := mul_div_cancel₀ _ hk.ne'
      nlinarith
    linarith

theorem comparison_global_profile_rigidity
    {U V g gp : ℝ → ℝ} {A B c R : ℝ}
    (hU : Monotone U) (hV : Monotone V) (hUV : U=ᵐ[volume] V)
    (hU0 : ∀t>0,0≤ U t) (hVneg : ∀t<0,V t=0)
    (hA : 0< A) (hB : 0< B) (hc : 0< c) (hgrowth : ∀t,R≤ t → c*t≤ V t)
    (hg : ∀t,0≤ t → HasDerivAt g (gp t) t) (hgpC : ContinuousOn gp (Ici (0:ℝ)))
    (hprim : ∀s t,0≤ s → s≤ t → gp t-gp s=∫r in s..t,A*r-B*U r)
    (hODE : ∀ᵐ t ∂volume,0< t → HasDerivAt gp (A*t-B*U t) t)
    (hg0 : g 0=0) (hzero : ∀t∈comparisonIncrementSupport V,g t=0)
    (hvirtual : ∀a b,0≤ a → a< b → a∈comparisonIncrementSupport V → b∈comparisonIncrementSupport V → 
      (∀r∈Ioo a b,r∉comparisonIncrementSupport V) → 0< V ((a+b)/2) → 
      Nonempty (ComparisonVirtualGapData g a b)) :
    (∀t>0,U t=(A/B)*t) ∧ (∀t>0,V t=(A/B)*t) := by
  have hgapFalse a b (ha : 0≤ a) (hab : a< b) (has : a∈comparisonIncrementSupport V)
      (hbs : b∈comparisonIncrementSupport V)
      (hgap : ∀r∈Ioo a b,r∉comparisonIncrementSupport V) : False := by
    have hmass : 0< V ((a+b)/2) := comparison_increment_support_positive_cdf_after hV hVneg has (by linarith)
    obtain ⟨data⟩ := hvirtual a b ha hab has hbs hgap hmass
    exact comparison_increment_gap_contradiction hV hA ha hab hUV hg hgpC hprim
      (hzero a has) (hzero b hbs) hgap data
  obtain ⟨hne,hl,hls,htail⟩ := comparison_increment_support_tail hV hVneg
    (comparison_increment_support_unbounded hV hc hgrowth) hgapFalse
  let l := sInf (comparisonIncrementSupport V)
  have hlo : BddBelow (comparisonIncrementSupport V) := ⟨0,comparison_increment_support_nonnegative hVneg⟩
  have hgpzero : ∀t∈Ioi l,gp t=0 := by
    intro t ht
    have hconst : g =ᶠ[𝓝 t] fun _=>0 := by
      filter_upwards [Ioi_mem_nhds ht] with r hr
      exact hzero r (htail hr)
    exact (hg t (hl.trans ht.le)).unique ((hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq hconst)
  have hgpL : gp l=0 := by
    have hclosed : IsClosed {t | t∈Ici (0:ℝ) ∧ gp t=0} := isClosed_Ici.isClosed_eq hgpC continuousOn_const
    have hsubset : Ioi l⊆{t | t∈Ici (0:ℝ) ∧ gp t=0} :=
      fun t ht=>⟨hl.trans ht.le,hgpzero t ht⟩
    have hh := closure_minimal hsubset hclosed
    rw [closure_Ioi] at hh
    exact (hh (show l∈Ici l from (show l≤l from le_rfl))).2
  have hlzero : l=0 := by
    apply le_antisymm _ hl
    by_contra hn
    have hlp : 0< l := lt_of_not_ge hn
    have hgap : ∀r∈Ioo (-1:ℝ) l,r∉comparisonIncrementSupport V := by
      intro r hr hs
      have hh := csInf_le hlo hs
      linarith [hr.2]
    have hconst : ∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) l),U r=0 := by
      filter_upwards [ae_restrict_of_ae hUV,ae_restrict_mem measurableSet_Ioo] with r hr hri
      rw [hr]
      have he := comparison_increment_support_gap_constant hV hgap r
        (show r∈Ioo (-1:ℝ) l from ⟨by linarith [hri.1],hri.2⟩) (-1/2)
        (show (-1/2:ℝ)∈Ioo (-1:ℝ) l by constructor <;> linarith)
      rw [he,hVneg (-1/2) (by norm_num)]
    have hp := comparison_affine_gap_derivative_from_primitive (show (0:ℝ)≤0 from le_rfl) hlp hprim hconst
    have hgc : ContinuousOn g (Icc (0:ℝ) l) := fun t ht=>(hg t ht.1).continuousAt.continuousWithinAt
    have hpc := hgpC.mono (show Icc (0:ℝ) l⊆Ici (0:ℝ) from fun _ ht=> ht.1)
    have hgd : ∀t∈Ico (0:ℝ) l,HasDerivWithinAt g (gp t) (Ici t) t :=
      fun t ht=>(hg t ht.1).hasDerivWithinAt
    have hpd : ∀t∈Ico (0:ℝ) l,HasDerivWithinAt gp (A*t) (Ici t) t := by
      simpa only [mul_zero,sub_zero] using hp
    exact no_positive_initial_gap hlp hA g gp hgc hpc hgd hpd hg0 (hzero l hls) hgpL
  have hAE : ∀ᵐ t ∂volume,0< t → U t=(A/B)*t := by
    filter_upwards [hODE] with t ht htp
    have hgpt : gp=ᶠ[𝓝 t] fun _=>0 := by
      filter_upwards [Ioi_mem_nhds htp] with r hr
      exact hgpzero r (by simpa only [hlzero] using hr)
    have hz := (ht htp).unique ((hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq hgpt)
    have he : U t=(A*t)/B := (eq_div_iff hB.ne').mpr (by nlinarith [hz])
    exact he.trans (by ring)
  have hk : 0< A/B := div_pos hA hB
  have hUall := comparison_monotone_linear_ae_everywhere hU hk hU0 hAE
  have hVAE : ∀ᵐ t ∂volume,0< t → V t=(A/B)*t := by
    filter_upwards [hUV,hAE] with t hUVt hEt ht
    rw [←hUVt]
    exact hEt ht
  exact ⟨hUall,comparison_monotone_linear_ae_everywhere hV hk
    (fun t _=> comparison_cdf_nonnegative hV hVneg t) hVAE⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
