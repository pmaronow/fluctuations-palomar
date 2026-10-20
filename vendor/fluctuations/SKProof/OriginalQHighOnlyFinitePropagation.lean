module

public import SKProof.OriginalQHighOnlyBadStrength
public import SKProof.OriginalQHighOnlyFiniteStep
public import ComparisonActualHighWallFixedCovarianceMargins

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
namespace ActualHighOnlyOverlapMinimum

theorem exists_finite_high_only_propagation_original_q
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ m cl cu Az C0 Ct D Bclock c0 margin : ℝ,
        0 < m → m ≤ (1:ℝ)/120 → 0 < cl → 0 < cu → cl≤cu →
        2≤Az → 1≤Ct → 0 < C0 → D≤1 →
        ∀ _hc0 : 0 < c0, c0≤1 → c0≤D → (beta:ℝ)^2≤Bclock →
        (((actualPropagationDepth (m/10000):ℕ):ℝ)+2)*c0^2≤ margin →
        margin≤(beta:ℝ)^2/8 → cl≤lower → upper≤cu →
        cl < (beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
        (beta:ℝ)^2*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
          (2*Real.exp (-12*(beta:ℝ)^2)) < cu →
        ∀ dim : ℕ→ℕ, Tendsto dim atTop atTop →
        ∀ root : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
          m (m/10000) cl cu Az C0 Ct D Bclock,
        ∀ G : OriginalQHighOnlyHistory root ((beta:ℝ)^2) c0,
        G.root = root →
        (∀ᶠ n in atTop, (beta:ℝ)^2/4≤(G.wall n).data.epsilon) →
        (∀ n, (root n).xs≤1) →
        (∀ᶠ n in atTop, comparisonConditionalScale (root n).context.N
          (m/10000) (root n).context.E (root n).lam≤(root n).xs) →
        (∀ᶠ n in atTop, ¬(cl*(root n).xs≤(root n).alpha.val.val (root n).xs ∧
          (root n).alpha.val.val (root n).xs≤cu*(root n).xs)) → False := by
  classical
  obtain ⟨lowerS, upperS, hlowerS, hupperS, Hstrength⟩ :=
    exists_high_only_history_bad_test_strength_saving_original_q hbeta hTemp
  obtain ⟨lowerC, upperC, hlowerC, hupperC, Hstep⟩ :=
    exists_weak_bad_parent_finite_child_step_constants_original_q hbeta hTemp
  refine ⟨min lowerS lowerC, max upperS upperC,
    lt_min hlowerS hlowerC, hupperS.trans_le (le_max_left _ _), ?_⟩
  intro m cl cu Az C0 Ct D Bclock c0 margin hm hmsmall hcl hcu hclcu
    hAz hCt hC0 hD hc0 hc01 hc0D hTB hbudget hmarginT hclBounds hcuBounds
    hclTemp hcuTemp dim hdim root G hGroot hWallEps hrootUnit hrootTarget hrootBad
  have hdelta : 0 < m/10000 := by positivity
  have hclS : cl≤lowerS := hclBounds.trans (min_le_left _ _)
  have hcuS : upperS≤cu := (le_max_left _ _).trans hcuBounds
  have hclC : cl≤lowerC := hclBounds.trans (min_le_right _ _)
  have hcuC : upperC≤cu := (le_max_right _ _).trans hcuBounds
  have hTempCost : cl < 2*(beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) := by
    have hp : 0 < (beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) :=
      mul_pos (zero_lt_one.trans hTemp) (Real.exp_pos _)
    linarith only [hclTemp,hp]
  have hrootPos : ∀ᶠ n in atTop, 0 < (G.root n).data.s := by
    filter_upwards [G.same_mass] with n hn
    rw [hn]
    exact (G.wall n).data.hs.1
  have hrootCap : ∀ᶠ n in atTop, (G.root n).context.d≤c0 := by
    filter_upwards [G.wall_unit, G.first_radius] with n hn hnd
    rw [hnd]
    simpa only [actualChildRadius, mul_one] using mul_le_mul_of_nonneg_left hn hc0.le
  have hWallDsquare : Tendsto (fun n=>(G.wall n).data.d^2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0)] using (G.wall_limits hmsmall hdim).2.pow 2
  have hWallD : ∀ᶠ n in atTop, (G.wall n).data.d^2≤(beta:ℝ)^2/8 :=
    hWallDsquare.eventually (eventually_le_nhds
      (show (0:ℝ)<(beta:ℝ)^2/8 by positivity))
  have hrootGap : ∀ᶠ n in atTop, ∀ u∈Ico (0:ℝ) (G.root n).data.s,
      (G.root n).b u+margin≤(G.root n).b (G.root n).data.s := by
    filter_upwards [G.root_gap hWallEps hWallD] with n hn u hu
    linarith only [hn u hu, hmarginT]
  let depth := actualPropagationDepth (m/10000)
  have Hchains : ∀ k : ℕ, k≤depth →
      ∃ phi : ℕ→ℕ, StrictMono phi ∧
      ∃ M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim (phi n)+1)
        m (m/10000) cl cu Az C0 Ct D Bclock,
        ActualFiniteWeakHighOnlyHistory c0 (fun n=>G.root (phi n)) k M ∧
        ActualHighOnlyErrorGrowthHistory (fun n=>G.root (phi n)) k M ∧
        (∀ n, (M n).xs≤1) ∧
        (∀ᶠ n in atTop, comparisonConditionalScale (M n).context.N
          (m/10000) (M n).context.E (M n).lam≤(M n).xs) ∧
        (∀ᶠ n in atTop, ¬(cl*(M n).xs≤(M n).alpha.val.val (M n).xs ∧
          (M n).alpha.val.val (M n).xs≤cu*(M n).xs)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have HF : ActualFiniteWeakHighOnlyHistory c0 G.root 0 root := by
        rw [hGroot]
        exact ActualFiniteWeakHighOnlyHistory.root root
      have HE : ActualHighOnlyErrorGrowthHistory G.root 0 root := by
        rw [hGroot]
        exact .root
      exact ⟨id, strictMono_id, root, HF, HE, hrootUnit, hrootTarget, hrootBad⟩
    | succ k ih =>
      intro hk
      obtain ⟨phi, hphi, M, Hfinite, Herror, Hunit, Htarget, Hbad⟩ :=
        ih (Nat.le_of_succ_le hk)
      let Gcurrent : OriginalQHighOnlyHistory M ((beta:ℝ)^2) c0 :=
        (G.comp phi hphi).with_current M Hfinite.weak
      have HfiniteCurrent : ActualFiniteWeakHighOnlyHistory c0 Gcurrent.root k M := Hfinite
      have HerrorCurrent : ActualHighOnlyErrorGrowthHistory Gcurrent.root k M := Herror
      have hbudgetK : ((k:ℝ)+2)*c0^2≤ margin := by
        have HK : (k:ℝ)≤(depth:ℝ) := by exact_mod_cast Nat.le_of_succ_le hk
        have HB : ((depth:ℝ)+2)*c0^2≤ margin := by simpa only [depth] using hbudget
        have Hmul : ((k:ℝ)+2)*c0^2≤((depth:ℝ)+2)*c0^2 := by
          simpa only [add_comm] using
            mul_le_mul_of_nonneg_right (add_le_add_right HK 2) (sq_nonneg c0)
        exact Hmul.trans HB
      have Hweak := Hstrength m cl cu Az C0 Ct D Bclock c0 hm hmsmall hcl hcu
        (by linarith : 0≤Az) hC0 (by linarith : 0≤Ct) hD hc0 hc01
        hclS hcuS hclTemp hcuTemp (fun n=>dim (phi n))
        (hdim.comp hphi.tendsto_atTop) M Gcurrent Hunit Hbad
      obtain ⟨N, Q, HF, HE, Hscale, HbadQ⟩ :=
        Hstep m cl cu Az C0 Ct D Bclock c0 margin hm hmsmall hcl hcu hclcu
          hAz hCt hC0 hc0 hc01 hc0D hTB hclC hcuC hTempCost hcuTemp
          (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop) M Gcurrent k
          HfiniteCurrent HerrorCurrent (hphi.tendsto_atTop.eventually hrootCap)
          (hphi.tendsto_atTop.eventually hrootGap)
          (hphi.tendsto_atTop.eventually hrootPos) hbudgetK Hunit Htarget Hweak Hbad
      let shift : ℕ→ℕ := fun n=>n+N
      have hshift : StrictMono shift := fun i j hij=>Nat.add_lt_add_right hij N
      let sigma := phi ∘ shift
      have hsigma : StrictMono sigma := hphi.comp hshift
      have HfiniteNew : ActualFiniteWeakHighOnlyHistory c0
          (fun n=>G.root (sigma n)) (k+1) Q := HF
      have HerrorNew : ActualHighOnlyErrorGrowthHistory
          (fun n=>G.root (sigma n)) (k+1) Q := HE
      have HbadNew : ∀ᶠ n in atTop, ¬(cl*(Q n).xs≤(Q n).alpha.val.val (Q n).xs ∧
          (Q n).alpha.val.val (Q n).xs≤cu*(Q n).xs) := by
        apply Eventually.of_forall
        intro n hn
        rcases HbadQ n with hlow | hhigh
        · exact (not_le.mpr hlow) hn.1
        · exact (not_le.mpr hhigh) hn.2
      exact ⟨sigma, hsigma, Q, HfiniteNew, HerrorNew, (fun n=>(Hscale n).2),
        Eventually.of_forall (fun n=>(Hscale n).1), HbadNew⟩
  obtain ⟨phi, hphi, M, Hfinite, Herror, _, _, _⟩ := Hchains depth le_rfl
  exact Herror.false_at_propagation_depth hm hdelta hC0 (hdim.comp hphi.tendsto_atTop)

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
