module

public import ComparisonActualHighWallPotential
public import ComparisonCapIntervals

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 8000000

private theorem shifted_contact_lipschitz
    {left κ : ℝ} {p S B : ℝ → ℝ} (hl : 0 < left) (hκ : 0 < κ)
    (hp : MonotoneOn p (Ioc left 1))
    (hpb : ∀r∈Ioc left 1,p r∈Icc (0:ℝ) (1-κ))
    (hS : MonotoneOn S (Ioc left 1)) (hB : MonotoneOn B (Ioc left 1))
    (hSb : ∀r∈Ioc left 1,0≤S r) (hBb : ∀r∈Ioc left 1,(S r)^2≤B r) :
    LipschitzOnWith (Real.toNNReal (3/κ)) S
      {r | r∈Ioc left 1 ∧ comparisonBracket (p r) r (S r) (B r)=0} := by
  apply LipschitzOnWith.of_dist_le_mul
  have hcoe : (Real.toNNReal (3/κ):ℝ)=3/κ := Real.coe_toNNReal _ (by positivity)
  intro a ha b hb
  have hinc {a b : ℝ} (ha : a∈Ioc left 1) (hb : b∈Ioc left 1)
      (hab : a≤b) (hga : comparisonBracket (p a) a (S a) (B a)=0)
      (hgb : comparisonBracket (p b) b (S b) (B b)=0) :
      S b-S a≤(3/κ)*(b-a) := by
    have hi := comparisonBracket_endpoint_increment_uniform (hl.trans ha.1) hab hκ
      (hp ha hb hab) (hpb b hb) (hSb a ha) (hSb b hb) (hBb a ha) (hBb b hb)
      (hB ha hb hab) (by rw [hga]) (by rw [hgb])
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hκ).mpr
    nlinarith
  rcases le_total a b with hab|hba
  · rw [hcoe,Real.dist_eq,Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr (hS ha.1 hb.1 hab)),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    simpa only [neg_sub] using hinc ha.1 hb.1 hab ha.2 hb.2
  · rw [hcoe,Real.dist_eq,Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr (hS hb.1 ha.1 hba)),
      abs_of_nonneg (sub_nonneg.mpr hba)]
    exact hinc hb.1 ha.1 hba hb.2 ha.2

private theorem shifted_ae_deriv_le_of_lipschitzOn_subset
    {left : ℝ} {f : ℝ → ℝ} {A : Set ℝ} {C : ℝ≥0}
    (hA : A⊆Ioc left 1) (hmono : MonotoneOn f (Icc left 1))
    (hLip : LipschitzOnWith C f A) : ∀ᵐ r,r∈A→deriv f r≤C := by
  have hiso : {r∈A | 𝓝[A∩Ioi r] r=⊥}.Countable := countable_setOfPred_isolated_right_within
  filter_upwards [hiso.ae_notMem volume,hmono.ae_differentiableWithinAt_of_mem,
    volume.ae_ne (1:ℝ)] with r hri hdiff hr1 hrA
  have hr := hA hrA
  have hright : (𝓝[A∩Ioi r] r).NeBot := ⟨by
    intro he
    exact hri ⟨hrA,he⟩⟩
  have hacc : AccPt r (𝓟 A) := by
    apply accPt_principal_iff_nhdsWithin.mpr
    have := hright
    exact Filter.neBot_of_le (nhdsWithin_mono r (show A∩Ioi r⊆A\{r} from by
      intro x hx
      exact ⟨hx.1,by simpa only [mem_singleton_iff] using ne_of_gt hx.2⟩))
  have hderiv : DifferentiableAt ℝ f r :=
    (hdiff ⟨hr.1.le,hr.2⟩).differentiableAt
      (Icc_mem_nhds hr.1 (lt_of_le_of_ne hr.2 hr1))
  exact (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs] using
      HasDerivAt_norm_le_lipschitzOn_accPt hderiv.hasDerivAt hrA hacc hLip)

private theorem shifted_contact_ae_deriv_le
    {left κ : ℝ} {p S B : ℝ → ℝ} (hl : 0 < left) (hκ : 0 < κ)
    (hp : MonotoneOn p (Ioc left 1))
    (hpb : ∀r∈Ioc left 1,p r∈Icc (0:ℝ) (1-κ))
    (hS : MonotoneOn S (Icc left 1)) (hB : MonotoneOn B (Ioc left 1))
    (hSb : ∀r∈Ioc left 1,0≤S r) (hBb : ∀r∈Ioc left 1,(S r)^2≤B r) :
    ∀ᵐ r,r∈Ioc left 1→comparisonBracket (p r) r (S r) (B r)=0→deriv S r≤3/κ := by
  have hLip := shifted_contact_lipschitz hl hκ hp hpb
    (hS.mono Ioc_subset_Icc_self) hB hSb hBb
  have ha := shifted_ae_deriv_le_of_lipschitzOn_subset (fun _ hr=>hr.1) hS hLip
  filter_upwards [ha] with r hr hri hg
  simpa only [Real.coe_toNNReal _ (by positivity : 0≤3/κ)] using hr ⟨hri,hg⟩

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def radiusS (a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) : ℝ→ℝ :=
  fun r=>orderedPathS n a.bf a.hf (a.alpha.val.val r)
def radiusB (a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) : ℝ→ℝ :=
  fun r=>orderedPathB n a.bf a.hf (a.alpha.val.val r)

theorem radius_mass_mem
    (a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {r : ℝ} (hr : r∈Icc a.data.rmin 1) : a.alpha.val.val r∈Ioc (0:ℝ) 1 := by
  have hu := inverseConstraint_mass_mem a.data.hr a.data.hc a.data.hk a.data.hkc a.alpha hr
  exact ⟨a.data.hs.1.trans_le hu.1,hu.2⟩

theorem radius_moments
    (a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) :
    MonotoneOn a.radiusS (Icc a.data.rmin 1) ∧
    MonotoneOn a.radiusB (Icc a.data.rmin 1) ∧
    ∀r∈Icc a.data.rmin 1,a.radiusS r∈Icc (0:ℝ) 1 ∧
      (a.radiusS r)^2≤a.radiusB r ∧ a.radiusB r≤1 := by
  have hm := orderedPath_SK_monotone n a.data.hn a.bf a.hf
    (a.data.bf_monotone a.alpha) (a.data.hf_monotone a.alpha)
  have hα := (inverseConstraint_strictMonoOn a.data.hc a.data.hk a.data.hkc a.alpha.property).monotoneOn
  refine ⟨?_,?_,?_⟩
  · intro r hr t ht hrt
    exact hm.1 (a.radius_mass_mem hr) (a.radius_mass_mem ht) (hα hr ht hrt)
  · intro r hr t ht hrt
    exact hm.2 (a.radius_mass_mem hr) (a.radius_mass_mem ht) (hα hr ht hrt)
  · intro r hr
    have hb := orderedPath_SK_bounds n a.data.hn a.bf a.hf
      (a.data.bf_monotone a.alpha) (a.data.hf_monotone a.alpha) (a.radius_mass_mem hr)
    exact ⟨⟨hb.1,hb.2.1⟩,hb.2.2⟩

theorem Potential.contact_ae_deriv_le
    {a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) (hN : 1≤a.data.N) (hlog : 1≤Real.log a.data.N)
    (hnd : 1/a.data.N≤a.data.d) :
    ∀ᵐ r,r∈Icc a.data.rmin 1→P.H r=0→deriv a.radiusS r≤9*Real.log a.data.N := by
  let w := a.data
  let p := comparisonLogSlope w.g
  let κ := (1/3)/Real.log w.N
  have hlogp : 0<Real.log w.N := by linarith
  have hκ : 0<κ := div_pos (by norm_num) hlogp
  have hpm : MonotoneOn p (Ioc w.rmin 1) := by
    intro r hr t ht hrt
    dsimp only [p,ActualHighWallData.g]
    rw [laplaceComparisonStrength_logSlope w.hd.ne' (sq_pos_of_pos w.hd).ne',
      laplaceComparisonStrength_logSlope w.hd.ne' (sq_pos_of_pos w.hd).ne']
    exact laplaceComparisonSlope_monotone (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrt (sq_nonneg _)) (pow_nonneg w.hd.le _))
  have hpb (r : ℝ) (hr : r∈Ioc w.rmin 1) : p r∈Icc (0:ℝ) (1-κ) := by
    refine ⟨(laplaceComparisonStrength_logSlope_mem w.hd.ne' (sq_pos_of_pos w.hd).ne' r).1,?_⟩
    have hh := laplaceComparisonStrength_uniform_slope hN hlog w.hd hnd
      (sq_pos_of_pos w.hd) le_rfl ⟨w.hrbounds.1.le.trans hr.1.le,hr.2⟩
    dsimp only [κ,p,ActualHighWallData.g]
    linarith
  have hmom := a.radius_moments
  have hcontact := shifted_contact_ae_deriv_le w.hrbounds.1 hκ hpm hpb hmom.1
    (hmom.2.1.mono Ioc_subset_Icc_self)
    (fun r hr=>(hmom.2.2 r ⟨hr.1.le,hr.2⟩).1.1)
    (fun r hr=>(hmom.2.2 r ⟨hr.1.le,hr.2⟩).2.1)
  have hconstant : 3/κ=9*Real.log w.N := by dsimp only [κ];field_simp;ring
  filter_upwards [P.hzero,hcontact,volume.ae_ne w.rmin] with r hz hc hrmin hr hH
  have hrpos : 0<r := w.hrbounds.1.trans_le hr.1
  have hbr : comparisonBracket (p r) r (a.radiusS r) (a.radiusB r)=0 := by
    have hg0 := (hz hr hH).1
    rw [comparison_gradient_slope hrpos.ne' (laplaceComparisonStrength_pos w.d
      (sq_pos_of_pos w.hd) r).ne'] at hg0
    have hh : w.g r*comparisonBracket (p r) r (a.radiusS r) (a.radiusB r)=0 := by
      simpa only [p,radiusS,radiusB,comparisonBracket] using hg0
    exact (mul_eq_zero.mp hh).resolve_left (laplaceComparisonStrength_pos w.d
      (sq_pos_of_pos w.hd) r).ne'
  simpa only [hconstant] using hc ⟨lt_of_le_of_ne hr.1 hrmin.symm,hr.2⟩ hbr

theorem Potential.cap_density_on_interval
    {a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) {l r : ℝ} (hl : a.data.rmin≤l) (hr : r≤1)
    (hnegative : ∀t∈Ioo l r,P.H t<0) :
    ∀ᵐ t,t∈Icc l r→deriv a.alpha.val.val t=a.data.M (a.alpha.val.val t) := by
  filter_upwards [P.hbang,volume.ae_ne l,volume.ae_ne r] with t ht htl htr hti
  exact ht ⟨hl.trans hti.1,hti.2.trans hr⟩
    (hnegative t ⟨lt_of_le_of_ne hti.1 htl.symm,lt_of_le_of_ne hti.2 htr⟩)

def cavityCapTravel (a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) : ℝ :=
  (comparisonConstraintLength a.data.N a.data.E a.data.d/a.data.N^delta)*
    Real.log ((1+comparisonSmallMass a.data.N a.data.E)/comparisonSmallMass a.data.N a.data.E)

theorem Potential.cap_interval_travel
    {a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) {l r : ℝ} (hl : a.data.rmin≤l) (hlr : l≤r) (hr : r≤1)
    (hnegative : ∀t∈Ioo l r,P.H t<0) :
    (∫u in a.alpha.val.val l..a.alpha.val.val r,1/a.data.M u)=r-l ∧
    r-l≤a.cavityCapTravel ∧
    ∀v>0,v≤a.alpha.val.val l+comparisonSmallMass a.data.N a.data.E→
      r-l≤(a.alpha.val.val r-a.alpha.val.val l)*a.data.E/(a.data.N^delta*a.data.d^3*v^2) := by
  let w := a.data
  have hsub : Icc l r⊆Icc w.rmin 1 := Icc_subset_Icc hl hr
  have hα := (inverseIntegralConstraints_lipschitz w.hm w.hM a.alpha.property).mono hsub
  have hm := (inverseConstraint_strictMonoOn w.hc w.hk w.hkc a.alpha.property).mono hsub
  have hden := P.cap_density_on_interval hl hr hnegative
  have hαr (t : ℝ) (ht : t∈Icc l r) : a.alpha.val.val t∈Icc (0:ℝ) 1 :=
    ⟨(a.radius_mass_mem (hsub ht)).1.le,(a.radius_mass_mem (hsub ht)).2⟩
  have hM (u : ℝ) (hu : u∈Icc (0:ℝ) 1) : 0<w.M u :=
    (comparisonCap_first_term (δ:=delta) w.hN w.hU w.hL w.hE w.hd.le hu.1).1
  have heq := cap_travel_identity hlr hα hm (fun t ht=>hM _ (hαr t ht)) hden
  have ht := cap_travel_le_total hlr hα hm hαr
    (comparisonCap_continuous w.N delta (comparisonSmallMass w.N w.E)
      (comparisonConstraintLength w.N w.E w.d) w.E w.d).continuousOn hM hden
  have hW : (∫u in (0:ℝ)..1,1/w.M u)≤a.cavityCapTravel := by
    simpa only [cavityCapTravel,ActualHighWallData.M,concreteWallCap,w,zero_add] using comparisonCap_log_travel (δ:=delta)
      w.hN w.hU w.hL w.hE w.hd.le (a:=0) (b:=1) le_rfl zero_le_one
  refine ⟨heq,ht.trans hW,?_⟩
  intro v hv hva
  rw [←heq]
  exact comparisonCap_band_travel (δ:=delta) w.hN w.hU w.hL w.hE w.hd hv hva
    (hαr l ⟨le_rfl,hlr⟩).1 (hm.monotoneOn ⟨le_rfl,hlr⟩ ⟨hlr,le_rfl⟩ hlr)

end ActualHighWallOverlapMinimum

theorem eventually_actual_high_wall_contact_derivative
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (hm : 0 < m) (hC0 : 0 < C0) :
    ∀ᶠ n : ℕ in atTop,
      ∀ a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀ P : a.Potential,∀ᵐ r,r∈Icc a.data.rmin 1→P.H r=0→
        deriv a.radiusS r≤9*Real.log a.data.N := by
  have hlog : ∀ᶠ n : ℕ in atTop,1≤Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [eventually_comparisonLowerScale_depth hC0 hm,hlog,
    eventually_ge_atTop (1:ℕ)] with n hdepth hnlog hn1
  intro a P
  have hs : comparisonLowerScale n a.data.E a.data.d≤a.data.d := by
    unfold comparisonLowerScale
    exact (div_le_iff₀ a.data.hd).mpr (by simpa only [pow_two] using a.hupper)
  exact P.contact_ae_deriv_le (by exact_mod_cast hn1) hnlog
    ((hdepth a.data.E a.data.d a.data.hE a.data.hd a.hlower).trans hs)

theorem eventually_actual_high_wall_cap_travel_small
    {m delta cl cu Az C0 Ct D Bclock epsilon : ℝ}
    (hC0 : 0 < C0) (hroom : 0 < 3*m+delta) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      ∀ a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
        a.cavityCapTravel≤epsilon*a.xs ∧
        ∀ (P : a.Potential) (l r : ℝ), a.data.rmin ≤ l → l ≤ r → r ≤ 1 →
          (∀ t ∈ Ioo l r, P.H t < 0) → r-l ≤ epsilon*a.xs := by
  filter_upwards [eventually_comparisonTravel_small (C:=C0) (D:=D)
    hC0 hroom hepsilon] with n hn
  intro a
  have hc : a.cavityCapTravel≤epsilon*a.xs := by
    exact (hn a.data.E a.data.d a.data.hE a.data.hd a.hdD a.hupper a.hlower).trans
      (mul_le_mul_of_nonneg_left a.hscale hepsilon.le)
  refine ⟨hc,?_⟩
  intro P l r hl hlr hr hnegative
  exact (P.cap_interval_travel hl hlr hr hnegative).2.1.trans hc

end OAI.SKFluctuations.LaplaceWindowFormalization
