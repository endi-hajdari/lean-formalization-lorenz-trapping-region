# Lean Formalization of the Lorenz Trapping Region Lemma

A [Lean 4](https://leanprover.github.io/) / [Mathlib](https://github.com/leanprover-community/mathlib4)
project developed for the **ICARM summer school**, formalizing the **Lorenz
system** — the classical model of deterministic chaos introduced by Edward N.
Lorenz in 1963:

$$
\dot x = \sigma\ (y - x), \qquad
\dot y = rx - y - xz, \qquad
\dot z = xy - bz.
$$

The long-term objective of this repository is to construct a fully machine-verified proof of the trapping region lemma and provide a foundation for further formalization of nonlinear dynamical systems in Lean.

---

## Repository Structure

```
.
├── LorenzTrappingRegionLemma/    # Lean source files
│   └── Basic.lean
├── Presentation/                 # ICARM Summer School presentation
├── assets/                       # Images and figures used by the presentation
├── README.md
├── lakefile.toml
├── lake-manifest.json
└── lean-toolchain
```

The formalization currently begins in

- `LorenzTrappingRegionLemma/Basic.lean`

which contains the initial definitions and lemmas that will be expanded throughout the project.

---

## Getting Started

Install **elan**, the official Lean toolchain manager:

https://github.com/leanprover/elan

Clone the repository and build the project:

```bash
lake update
lake exe cache get
lake build
```

Opening the repository in **Visual Studio Code** with the **Lean 4** extension provides interactive theorem proving, goal visualization, type information, and error reporting.

---

## Dependencies

- **Lean 4** (version pinned in `lean-toolchain`)
- **Mathlib** (version pinned in `lakefile.toml`)

---

## Project Goals

This project aims to formalize the mathematical development leading to the trapping region lemma for the Lorenz system, including:

- the Lorenz vector field;
- equilibrium points;
- invariant and trapping regions;
- Lyapunov-type estimates;
- the classical trapping region lemma;
- supporting analytical results from Mathlib.

The repository is intended to serve as a reusable foundation for future formalizations in nonlinear dynamical systems and rigorous computer-assisted mathematics.

---

## Presentation

The `Presentation/` directory contains materials developed for the **ICARM 2026 Summer School**, including:

- presentation slides;
- supporting figures, graphics, and other assets;
- an interactive HTML presentation;
- an interactive Lean blueprint outlining the structure, definitions, lemmas, and proof strategy for the Lorenz trapping region formalization.

The main presentation files are:

- [`Presentation/index.html`](Presentation/index.html) — the primary interactive presentation;
- [`Presentation/lorenz-lean-blueprint-final.html`](Presentation/lorenz-lean-blueprint-final.html) — the interactive Lean formalization blueprint.

---

## References

- Edward N. Lorenz, *Deterministic Nonperiodic Flow*, Journal of the Atmospheric Sciences, 1963.
- The Lean Theorem Prover: https://lean-lang.org/
- Mathlib: https://github.com/leanprover-community/mathlib4

---

## License

Unless otherwise stated, this project is released under the **Apache-2.0 License**.
