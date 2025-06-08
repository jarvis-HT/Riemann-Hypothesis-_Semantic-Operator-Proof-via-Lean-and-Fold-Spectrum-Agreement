/-!
# HilbertPolyaRHTheoremSlot

If the spectrum of a self-adjoint operator H agrees with
the nontrivial zeros of the Riemann zeta function,
then the Riemann Hypothesis is semantically supported.

This module encodes that implication in Lean.
-/

import Mathlib.Tactic
import ZetaSpectrumAgreementSlot

open ZetaSpectrumAgreementSlot

namespace HilbertPolyaRHTheoremSlot

/-! ## Formal statement of RH under operator spectrum assumption -/
def RH : Prop :=
  ∀ z ∈ zetaZeros, z.re = 0.5

theorem RH_from_spectrum (R : SpectrumAgreementResult) :
  R.agrees → RH :=
by
  intro hAgree
  unfold RH
  intros z hz
  -- since R.hypothesis.spectrum = zetaZeros, each z must be of form 0.5 + it
  have : z ∈ R.hypothesis.spectrum := by rw [←hAgree]; exact hz
  rcases List.mem_map.mp this with ⟨t, _, ht⟩
  rw [ht]; simp

end HilbertPolyaRHTheoremSlot