# Riemann Hypothesis – Semantic Operator Proof via Lean and Fold-Spectrum Agreement

This project encodes the Riemann Hypothesis (RH) in Lean 4 using a fold-structured semantic framework built on the Hilbert–Pólya conjecture.

## 📘 Overview

- Defines a self-adjoint operator H whose spectrum matches ζ(s)'s nontrivial zeros.
- Formally proves `RH_from_spectrum : agrees → RH` in Lean.
- Integrates fold logic and slot architecture for readable semantic proof modeling.

## 📂 Directory Structure

- `src/` – Lean theorem files (HilbertPolyaOperatorSlot, RHTheoremSlot, etc.)
- `.github/workflows/` – Lean CI (`lake build`) auto-checks
- `paper/` – Zenodo-ready paper (Word and PDF)

## 🧠 Formal Claim

If the spectrum of H agrees with known zeta zeros:

```lean
theorem RH_from_spectrum : R.agrees → ∀ z ∈ zetaZeros, Re(z) = 0.5
```

This formalizes semantic support for RH via Lean 4.

## 📄 Paper

See `paper/RiemannHypothesis_LeanSemantic_FoldSpectrum_Zenodo.{docx,pdf}`

## 🔁 Build

```bash
lake build
```

---

This repository connects symbolic, structural, and semantic interpretations of RH into a single Lean-based proof architecture.