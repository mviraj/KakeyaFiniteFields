# Kakeya sets in finite fields

An AI-assisted Lean 4 formalization of the Kakeya set problem over finite fields, establishing a lower bound on the size of such sets.

This project formalizes the result of Dvir (2008) that any Kakeya set $K \subseteq \mathbb{F}_q^n$ (a set containing a line in every direction) must have size at least $C_n \cdot q^n$ for some constant $C_n > 0$ depending only on $n$.

All the Lean statements and proofs were produced by **Gauss**, Math Inc.'s autoformalization agent, guided by a LaTeX blueprint.

---

## Highlights

- **Target:** complete formalization of the finite field Kakeya theorem.
- **Scope:** ≈300 lines of Lean.
- **Workflow:** AI-generated formalization from a LaTeX blueprint with human scaffolding.
- **Foundation:** polynomial interpolation, homogeneous components, and vanishing arguments over finite fields.
- **Result:** a complete Lean theorem establishing that any Kakeya set in $\mathbb{F}_q^n$ has size at least $C_n \cdot q^n$.

---

## Links

- **Math Inc.:** <https://www.math.inc/>
- **Gauss (autoformalization agent):** <https://www.math.inc/gauss>

---

## Repository layout

- `KakeyaFiniteFields/` – main Lean development of the Kakeya set lower bound proof.
- `KakeyaFiniteFields.lean` – top-level Lean entry point.
- `blueprint/` – LaTeX blueprint, including the dependency graph and web/PDF build assets.
- `home_page/` – Jekyll-based landing page used for the project website.

---

## Building

You will need:

- [Lean 4](https://lean-lang.org/) with `lake`
- [uv](https://docs.astral.sh/uv/getting-started/installation/) for the
  blueprint tools
- A LaTeX installation (e.g. TeX Live) for the PDF

### Lean development

```bash
lake exe cache get && lake build
```

### Blueprint (PDF)

```bash
uvx leanblueprint pdf
```

### Blueprint (web + local server)

```bash
uvx leanblueprint web
uvx leanblueprint serve
```

The generated site is served locally; by default the blueprint index is at
`http://localhost:8000/`.

---

## About

This repository is part of Math Inc.'s broader effort to apply AI-assisted
formal verification to fundamental problems in mathematics. Faster, lower-friction formalization can make complex mathematical
results easier to verify, extend, and trust.

For questions or collaborations, please reach out via
<https://www.math.inc/>.

---

## References

- Zeev Dvir, *On the size of Kakeya sets in finite fields*,
  <https://www.cs.princeton.edu/~zdvir/papers/Dvir09.pdf>
