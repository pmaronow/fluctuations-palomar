module

public import ActualComparisonDefect
public import Mathlib.Analysis.Calculus.Monotone
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.Order.LeftRightNhds

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem comparison_contact_lipschitz
    {p S B : ℝ → ℝ} {κ : ℝ} (hκ : 0<κ)
    (hp : MonotoneOn p (Ioc (0:ℝ) 1))
    (hpb : ∀r∈Ioc (0:ℝ) 1,p r∈Icc (0:ℝ) (1-κ))
    (hS : MonotoneOn S (Ioc (0:ℝ) 1))
    (hB : MonotoneOn B (Ioc (0:ℝ) 1))
    (hSb : ∀r∈Ioc (0:ℝ) 1,0≤S r)
    (hBb : ∀r∈Ioc (0:ℝ) 1,(S r)^2≤B r) :
    LipschitzOnWith (Real.toNNReal (3/κ)) S
      {r | r∈Ioc (0:ℝ) 1 ∧ comparisonBracket (p r) r (S r) (B r)=0} := by
  apply LipschitzOnWith.of_dist_le_mul
  have hcoe : (Real.toNNReal (3/κ):ℝ)=3/κ := Real.coe_toNNReal _ (by positivity)
  intro a ha b hb
  have hinc {a b : ℝ} (ha : a∈Ioc (0:ℝ) 1) (hb : b∈Ioc (0:ℝ) 1)
      (hab : a≤b) (hga : comparisonBracket (p a) a (S a) (B a)=0)
      (hgb : comparisonBracket (p b) b (S b) (B b)=0) :
      S b-S a≤(3/κ)*(b-a) := by
    have hi := comparisonBracket_endpoint_increment_uniform ha.1 hab hκ
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

theorem HasDerivAt_norm_le_lipschitzOn_accPt
    {f : ℝ → ℝ} {f' x : ℝ} {A : Set ℝ} {C : ℝ≥0}
    (hf : HasDerivAt f f' x) (hx : x∈A) (ha : AccPt x (𝓟 A))
    (hLip : LipschitzOnWith C f A) : ‖f'‖≤C := by
  have : (𝓝[A\{x}] x).NeBot := accPt_principal_iff_nhdsWithin.mp ha
  apply le_of_tendsto ((hasDerivWithinAt_iff_tendsto_slope.mp
    (hf.hasDerivWithinAt (s:=A))).norm)
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hne : y-x≠0 := sub_ne_zero.mpr (by simpa only [mem_singleton_iff] using hy.2)
  rw [slope_def_field,Real.norm_eq_abs,abs_div]
  apply (div_le_iff₀ (abs_pos.mpr hne)).mpr
  simpa only [Real.dist_eq] using hLip.dist_le_mul y hy.1 x hx

theorem ae_deriv_le_of_lipschitzOn_subset
    {f : ℝ → ℝ} {A : Set ℝ} {C : ℝ≥0}
    (hA : A⊆Ioc (0:ℝ) 1) (hmono : MonotoneOn f (Icc (0:ℝ) 1))
    (hLip : LipschitzOnWith C f A) :
    ∀ᵐ r,r∈A→deriv f r≤C := by
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

theorem comparison_contact_ae_deriv_le
    {p S B : ℝ → ℝ} {κ : ℝ} (hκ : 0<κ)
    (hp : MonotoneOn p (Ioc (0:ℝ) 1))
    (hpb : ∀r∈Ioc (0:ℝ) 1,p r∈Icc (0:ℝ) (1-κ))
    (hS : MonotoneOn S (Icc (0:ℝ) 1))
    (hB : MonotoneOn B (Ioc (0:ℝ) 1))
    (hSb : ∀r∈Ioc (0:ℝ) 1,0≤S r)
    (hBb : ∀r∈Ioc (0:ℝ) 1,(S r)^2≤B r) :
    ∀ᵐ r,r∈Ioc (0:ℝ) 1→comparisonBracket (p r) r (S r) (B r)=0→
      deriv S r≤3/κ := by
  have hLip := comparison_contact_lipschitz hκ hp hpb
    (hS.mono Ioc_subset_Icc_self) hB hSb hBb
  have ha := ae_deriv_le_of_lipschitzOn_subset (fun _ hr=>hr.1) hS hLip
  filter_upwards [ha] with r hr hri hg
  simpa only [Real.coe_toNNReal _ (by positivity : 0≤3/κ)] using hr ⟨hri,hg⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
