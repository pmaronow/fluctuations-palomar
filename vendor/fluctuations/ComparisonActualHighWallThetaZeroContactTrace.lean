module

public import ComparisonActualHighWallThetaZeroSelectedRadius
public import ComparisonActualHighWallContactGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000
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

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem Potential.contact_ae_deriv_le
    {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (P : Q.Potential) (hN : 1≤Q.data.N) (hlog : 1≤Real.log Q.data.N)
    (hnd : 1/Q.data.N≤Q.data.d) :
    ∀ᵐ r,r∈Icc Q.data.rmin 1→P.H r=0→deriv Q.radiusS r≤9*Real.log Q.data.N := by
  let w := Q.data
  let p := comparisonLogSlope (laplaceComparisonStrength w.d Q.lam)
  let κ := (1/3)/Real.log w.N
  have hlogp : 0<Real.log w.N := by linarith
  have hκ : 0<κ := div_pos (by norm_num) hlogp
  have hpm : MonotoneOn p (Ioc w.rmin 1) := by
    intro r hr t ht hrt
    dsimp only [p]
    rw [laplaceComparisonStrength_logSlope w.hd.ne' Q.hlam.ne',
      laplaceComparisonStrength_logSlope w.hd.ne' Q.hlam.ne']
    exact laplaceComparisonSlope_monotone (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrt Q.hlam.le) (pow_nonneg w.hd.le _))
  have hpb (r : ℝ) (hr : r∈Ioc w.rmin 1) : p r∈Icc (0:ℝ) (1-κ) := by
    refine ⟨(laplaceComparisonStrength_logSlope_mem w.hd.ne' Q.hlam.ne' r).1,?_⟩
    have hh := laplaceComparisonStrength_uniform_slope hN hlog w.hd hnd
      Q.hlam Q.hld ⟨w.hrbounds.1.le.trans hr.1.le,hr.2⟩
    dsimp only [κ,p]
    linarith
  have hmom := Q.radius_moments
  have hcontact := shifted_contact_ae_deriv_le w.hrbounds.1 hκ hpm hpb hmom.1
    (hmom.2.1.mono Ioc_subset_Icc_self)
    (fun r hr=>(hmom.2.2 r ⟨hr.1.le,hr.2⟩).1.1)
    (fun r hr=>(hmom.2.2 r ⟨hr.1.le,hr.2⟩).2.1)
  have hconstant : 3/κ=9*Real.log w.N := by dsimp only [κ];field_simp;ring
  filter_upwards [P.hzero,hcontact,volume.ae_ne w.rmin] with r hz hc hrmin hr hH
  have hrpos : 0<r := w.hrbounds.1.trans_le hr.1
  have hbr : comparisonBracket (p r) r (Q.radiusS r) (Q.radiusB r)=0 := by
    have hg0 := (hz hr hH).1
    rw [comparison_gradient_slope hrpos.ne' (laplaceComparisonStrength_pos w.d
      Q.hlam r).ne'] at hg0
    have hh : laplaceComparisonStrength w.d Q.lam r*comparisonBracket (p r) r (Q.radiusS r) (Q.radiusB r)=0 := by
      simpa only [p,radiusS,radiusB,comparisonBracket] using hg0
    exact (mul_eq_zero.mp hh).resolve_left (laplaceComparisonStrength_pos w.d
      Q.hlam r).ne'
  simpa only [hconstant] using hc ⟨lt_of_le_of_ne hr.1 hrmin.symm,hr.2⟩ hbr

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
