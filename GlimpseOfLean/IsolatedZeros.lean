/-
Fragment of the Mathlib file `IsolatedZeros.lean`
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Order.Filter.EventuallyConst
public import Mathlib.Topology.Perfect

/-!
# Principle of isolated zeros

This file proves the fact that the zeros of a non-constant analytic function of one variable are
isolated. It also introduces a little bit of API in the `HasFPowerSeriesAt` namespace that is useful
in this setup.

## Main results

* `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` is the main statement that if a function is
  analytic at `z₀`, then either it is identically zero in a neighborhood of `z₀`, or it does not
  vanish in a punctured neighborhood of `z₀`.
* `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` is the identity theorem for analytic
  functions: if a function `f` is analytic on a connected set `U` and is zero on a set with an
  accumulation point in `U` then `f` is identically `0` on `U`.

## Applications

* Vanishing of products of analytic functions, `eq_zero_or_eq_zero_of_smul_eq_zero`: If `f, g` are
  analytic on a neighbourhood of the preconnected open set `U`, and `f • g = 0` on `U`, then either
  `f = 0` on `U` or `g = 0` on `U`.
* Preimages of codiscrete sets, `AnalyticOnNhd.preimage_mem_codiscreteWithin`: if `f` is analytic
  on a neighbourhood of `U` and not locally constant, then the preimage of any subset codiscrete
  within `f '' U` is codiscrete within `U`.
-/

public section

open Filter Function Module Nat FormalMultilinearSeries EMetric Set

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {s : E} {p q : FormalMultilinearSeries 𝕜 𝕜 E} {f g : 𝕜 → E} {n : ℕ} {z z₀ : 𝕜}

namespace HasSum

variable {a : ℕ → E}

theorem hasSum_at_zero (a : ℕ → E) : HasSum (fun n => (0 : 𝕜) ^ n • a n) (a 0) := by
  convert hasSum_single (α := E) 0 fun b h ↦ _ <;> simp [*]

theorem exists_hasSum_smul_of_apply_eq_zero (hs : HasSum (fun m => z ^ m • a m) s)
    (ha : ∀ k < n, a k = 0) : ∃ t : E, z ^ n • t = s ∧ HasSum (fun m => z ^ m • a (m + n)) t := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simpa
  by_cases h : z = 0
  · have : s = 0 := hs.unique (by simpa [ha 0 hn, h] using hasSum_at_zero a)
    exact ⟨a n, by simp [h, hn.ne', this], by simpa [h] using hasSum_at_zero fun m => a (m + n)⟩
  · refine ⟨(z ^ n)⁻¹ • s, by match_scalars; field, ?_⟩
    have h1 : ∑ i ∈ Finset.range n, z ^ i • a i = 0 :=
      Finset.sum_eq_zero fun k hk => by simp [ha k (Finset.mem_range.mp hk)]
    have h2 : HasSum (fun m => z ^ (m + n) • a (m + n)) s := by
      simpa [h1] using (hasSum_nat_add_iff' n).mpr hs
    convert h2.const_smul (z⁻¹ ^ n) using 2 with x
    · match_scalars
      simp [field, pow_add]
    · simp only [inv_pow]

end HasSum

namespace HasFPowerSeriesAt

theorem has_fpower_series_dslope_fslope (hp : HasFPowerSeriesAt f p z₀) :
    HasFPowerSeriesAt (dslope f z₀) p.fslope z₀ := by
  have hpd : deriv f z₀ = p.coeff 1 := hp.deriv
  have hp0 : p.coeff 0 = f z₀ := hp.coeff_zero 1
  simp only [hasFPowerSeriesAt_iff, coeff_fslope] at hp ⊢
  refine hp.mono fun x hx => ?_
  by_cases h : x = 0
  · convert hasSum_single (α := E) 0 _ <;> intros <;> simp [*]
  · have hxx : ∀ n : ℕ, x⁻¹ * x ^ (n + 1) = x ^ n := fun n => by simp [field, _root_.pow_succ]
    suffices HasSum (fun n => x⁻¹ • x ^ (n + 1) • p.coeff (n + 1)) (x⁻¹ • (f (z₀ + x) - f z₀)) by
      simpa [dslope, slope, h, smul_smul, hxx] using this
    simpa [hp0] using ((hasSum_nat_add_iff' 1).mpr hx).const_smul x⁻¹

theorem has_fpower_series_iterate_dslope_fslope (n : ℕ) (hp : HasFPowerSeriesAt f p z₀) :
    HasFPowerSeriesAt ((swap dslope z₀)^[n] f) (fslope^[n] p) z₀ := by
  induction n generalizing f p with
  | zero => exact hp
  | succ n ih => simpa using ih (has_fpower_series_dslope_fslope hp)

theorem iterate_dslope_fslope_ne_zero (hp : HasFPowerSeriesAt f p z₀) (h : p ≠ 0) :
    (swap dslope z₀)^[p.order] f z₀ ≠ 0 := by
  rw [← coeff_zero (has_fpower_series_iterate_dslope_fslope p.order hp) 1]
  simpa [coeff_eq_zero] using apply_order_ne_zero h

theorem eq_pow_order_mul_iterate_dslope (hp : HasFPowerSeriesAt f p z₀) :
    ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ p.order • (swap dslope z₀)^[p.order] f z := by
  have hq := hasFPowerSeriesAt_iff'.mp (has_fpower_series_iterate_dslope_fslope p.order hp)
  filter_upwards [hq, hasFPowerSeriesAt_iff'.mp hp] with x hx1 hx2
  have : ∀ k < p.order, p.coeff k = 0 := fun k hk => by
    simpa [coeff_eq_zero] using apply_eq_zero_of_lt_order hk
  obtain ⟨s, hs1, hs2⟩ := HasSum.exists_hasSum_smul_of_apply_eq_zero hx2 this
  convert hs1.symm
  simp only [coeff_iterate_fslope] at hx1
  exact hx1.unique hs2

theorem locally_ne_zero (hp : HasFPowerSeriesAt f p z₀) (h : p ≠ 0) : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 := by
  rw [eventually_nhdsWithin_iff]
  have h2 := (has_fpower_series_iterate_dslope_fslope p.order hp).continuousAt
  have h3 := h2.eventually_ne (iterate_dslope_fslope_ne_zero hp h)
  filter_upwards [eq_pow_order_mul_iterate_dslope hp, h3] with z e1 e2 e3
  simpa [e1, e2, e3] using pow_ne_zero p.order (sub_ne_zero.mpr e3)

theorem locally_zero_iff (hp : HasFPowerSeriesAt f p z₀) : (∀ᶠ z in 𝓝 z₀, f z = 0) ↔ p = 0 :=
  ⟨fun hf => hp.eq_zero_of_eventually hf, fun h => eventually_eq_zero (𝕜 := 𝕜) (by rwa [h] at hp)⟩

end HasFPowerSeriesAt

namespace AnalyticAt

/-- The *principle of isolated zeros* for an analytic function, local version: if a function is
analytic at `z₀`, then either it is identically zero in a neighborhood of `z₀`, or it does not
vanish in a punctured neighborhood of `z₀`. -/
theorem eventually_eq_zero_or_eventually_ne_zero (hf : AnalyticAt 𝕜 f z₀) :
    (∀ᶠ z in 𝓝 z₀, f z = 0) ∨ ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 := by
 sorry

 end AnalyticAt
