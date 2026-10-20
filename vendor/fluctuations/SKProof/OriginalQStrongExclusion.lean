module

public import SKProof.OriginalQStrongOnlyMain
public import SKProof.OriginalQStrongContext
public import SKProof.Port.ComparisonActualOriginalQCompleteComparableStrictTest

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open Set Filter Hierarchy
open scoped Topology NNReal
open OriginalQFixedTStoppingDraft ActualThetaZeroOverlapMinimum

theorem original_q_strong_exclusion {m cl cu Az C0 Ct D Bclock T : ℝ}
    (hT : 1 < T) (hm : 0 < m) (hmmax : m < 1/300) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hclm : cl < T*Real.exp (-12*T))
    (hcum : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu) :
    ∀ (dim : ℕ → ℕ) (_hdim : StrictMono dim)
      (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
        m (m/10000) cl cu Az C0 Ct D Bclock),
      (∀ n, RetainedBadQ T (dim n) (Q n)) →
      Tendsto (fun n => (Q n).xs) atTop (𝓝 0) →
      ∀ eta : ℝ, 0 < eta → ∀ phi : ℕ → ℕ, StrictMono phi →
        (∀ n, eta ≤ laplaceComparisonStrength (Q (phi n)).data.d
          (Q (phi n)).lam (Q (phi n)).xs / (Q (phi n)).xs^2) → False := by
  intro dim hdim Q hRet _hxs eta heta phi hphi hstrong
  obtain ⟨G, hcompare⟩ := original_q_comparable_band_context_of_concrete_original_q
    (dim := fun n => dim (phi n)) (zero_lt_one.trans hT) hm hmmax hC0 (hdim.comp hphi)
    (fun n => Q (phi n)) (fun n => (hRet (phi n)).1) (fun n => (hRet (phi n)).2.1)
    (fun n => (hRet (phi n)).2.2.1) (fun n => (hRet (phi n)).2.2.2.1)
    (fun n => (hRet (phi n)).2.2.2.2.2.2.2.2.1) heta hstrong
  have Hgood := eventually_actual_comparable_test_point_strict_profile_original_q
    (delta := m/10000) (Ccal := max 1 (1/eta)) (c0 := 1)
    hm (by positivity) (by linarith) hcl hcu hAz hC0 hCt (le_max_left _ _) one_pos le_rfl
    (by linarith) (by linarith) (by linarith)
    (fun n => dim (phi n)) (hdim.comp hphi).tendsto_atTop (fun n => Q (phi n)) G
    (G.W_zero.eventually (eventually_le_nhds zero_lt_one)) hclm hcum hcompare
  obtain ⟨n, hlo, hhi⟩ := Hgood.exists
  rcases (hRet (phi n)).2.2.2.2.2.2.2.2.2.2 with hbad | hbad
  · exact lt_asymm hbad hlo
  · exact lt_asymm hbad hhi

theorem strong_exclusion_inputs_original_q : ActualOriginalQStrongExclusionInputs := by
  intro T m cl cu hT hm hmmax hcl hcu hclm hcum
  exact original_q_strong_exclusion (Az := 2) (C0 := 1) (Ct := 1) (D := 1) (Bclock := T)
    hT hm hmmax hcl hcu (by norm_num) one_pos zero_le_one hclm hcum

end OAI.SKFluctuations.LaplaceWindowFormalization
