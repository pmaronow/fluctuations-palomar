module

public import ComparisonSignedCavityActualTripleAllRates
public import ComparisonSignedCavityEventuallyInheritedIncomingSourceErrorProductRate
public import ComparisonSignedCavityEventuallyInheritedStarIncomingSourceErrorProductRate
public import ComparisonSignedCavityEventuallyInheritedPowerSourceErrorProductRate

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

theorem eventually_inherited_same_star_triple_error_bounds
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Ccal : ℝ}
    (Cmass : ℝ) (hCm : 0 ≤ Cmass)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn : ℕ in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (saving : ℝ) (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNet j k saving M W w) :
      (∀a b d : ℕ,∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
        ∃Cpower Cbase : ℕ→ℝ,(∀j,0 < Cpower j ∧ 0 < Cbase j) ∧
        ActualGeneratedTripleIncomingErrorOnEveryFinalNet a b d eta saving Cmass Cp Ch Cpower Cbase M W w) ∧
      (∀a b d : ℕ,∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
        ∃Cpower Cbase : ℕ→ℝ,(∀j,0 < Cpower j ∧ 0 < Cbase j) ∧
        ActualGeneratedTripleStarIncomingErrorOnEveryFinalNet a b d eta saving Cmass Cp Ch Cpower Cbase M W w) ∧
      ∀b d : ℕ,∃Cpower Cbase : ℕ→ℝ,(∀j,0 < Cpower j ∧ 0 < Cbase j) ∧
        ActualGeneratedTriplePowerErrorOnEveryFinalNet b d eta saving Cmass Cpower Cbase M W w := by
  have HI (a j k : ℕ) :=
    eventually_inherited_canonical_incoming_source_error_product_from_same_star a j k Bclock Temp Cf Cmass Ccal
      hTemp hCf hCm hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt M W hcanonical hWlim
      hcompare hsource w (Hmixed (2*j) (2*k))
  have HS (a j k : ℕ) :=
    eventually_inherited_canonical_star_incoming_source_error_product_from_same_star a j k Bclock Temp Cf Cmass Ccal
      hTemp hCf hCm hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt M W hcanonical hWlim
      hcompare hsource w (Hmixed (2*j) (2*k))
  have HP (a j k : ℕ) :=
    eventually_inherited_canonical_power_source_error_product_from_same_star a j k Bclock Temp Cf Cmass Ccal
      hTemp hCf hCm hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt M W hcanonical hWlim
      hcompare hsource w (Hmixed (2*j) (2*k))
  refine ⟨?_,?_,?_⟩
  · intro a b d
    obtain ⟨Cp,hCp,Ch,hCh,Hin⟩:=HI a 0 d
    choose Cpower hCpower Cbase hCbase Hpower using fun j=>HP b j (d-1-j)
    exact ⟨Cp,hCp,Ch,hCh,Cpower,Cbase,fun j=>⟨hCpower j,hCbase j⟩,
      actual_generated_triple_incoming_error_from_canonical hCp.le hCh.le
        (fun j=>⟨(hCpower j).le,(hCbase j).le⟩)
        (actual_canonical_paired_incoming_source_error_from_products Hin Hpower)⟩
  · intro a b d
    obtain ⟨Cp,hCp,Ch,hCh,Hin⟩:=HS a 0 d
    choose Cpower hCpower Cbase hCbase Hpower using fun j=>HP b j (d-1-j)
    exact ⟨Cp,hCp,Ch,hCh,Cpower,Cbase,fun j=>⟨hCpower j,hCbase j⟩,
      actual_generated_triple_star_incoming_error_from_canonical hCp.le hCh.le
        (fun j=>⟨(hCpower j).le,(hCbase j).le⟩)
        (actual_canonical_paired_star_incoming_source_error_from_products Hin Hpower)⟩
  · intro b d
    choose Cpower hCpower Cbase hCbase Hpower using fun j=>HP b j (d-1-j)
    exact ⟨Cpower,Cbase,fun j=>⟨hCpower j,hCbase j⟩,
      actual_generated_triple_power_error_from_canonical
        (fun j=>⟨(hCpower j).le,(hCbase j).le⟩) Hpower⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
