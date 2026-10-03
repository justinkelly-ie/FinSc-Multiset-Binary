# FinSc-Multiset-Binary

[![Idris 2 Verification](https://img.shields.io/badge/Idris_2-0.8.0-blue.svg)](https://www.idris-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

**Layer 2a Constructivist Boolean Field Engine, Möbius Transforms & Functional Probability for Idris 2**

`FinSc-Multiset-Binary` forms **Layer 2a** of the 10-layer constructive non-linear multiset science framework. Built on the discrete kernel of `FinSc-Multiset-Core` and `FinSc-Multiset-Transform`, it provides binary logic field engines ($\mathbb{F}_2$), George Boole's original polynomial algebra, Möbius spectral inversion transforms, digital gate circuits, syllogistic inference engines, and discrete functional probability bounds.

---

## 📦 Core Library Architecture & Staged Modules

### Stage 0: Binary Ground Interfaces
- **`Stage0.BinaryInterfaces`:** Core algebraic interfaces for binary Boolean logic, bit negation, conjunction, and disjunction over discrete `Bit` singletons.

### Stage 1: Boolean Polynomials, Circuits & Functional Probability
- **`Stage1.BooleFunction` & `Stage1.Bridge`:** Direct representations of Boolean functions, truth tables, and convertible bridge functions connecting binary logic quanta directly to multiset resource channels.
- **`Stage1.MobiusTransform`:** Forward and inverse discrete Möbius transforms mapping binary Boolean polynomials into functional probability distributions and sifting combinatorial state spaces into manifest dimensions.
- **`Stage1.BoolePolynumber` & `Stage1.LiftedPolynumber`:** Boolean polynomial rings over discrete `Bit` multisets with higher-order polynomial lifting.
- **`Stage1.Circuit`, `Stage1.OnCircuit` & `Stage1.Syllogism`:** Constructive digital gate circuits (`And`, `Or`, `Xor`, `Nand`, `Nor`), streaming circuit pipelines, and automated syllogistic inference engines.
- **`Stage1.FunctionalProbability` & `Stage1.InformationTheory`:** Exact rational probability bounds computed directly from Boolean multiset tallies without continuous real-number limits; Shannon-Huffman prefix coding, cross-entropy, and information quadrance.

---

## 🚀 Building & Installing

Built with Idris 2 (`0.8.0`) via `pack`:

```bash
pack build FinSc-Multiset-Binary.ipkg
pack install FinSc-Multiset-Binary.ipkg
```

---

## 🔬 Architectural Principles

- **Total Constructivism:** Enforces `%default total` across all binary logic and probability functions.
- **Exact Binary Spectral Analysis:** Discrete Möbius transforms replacing continuous probability density functions.
- **Zero Floating-Point Drift:** Rational probability bounds computed via Diophantine integer counts.
- **2LTT Staged Modularity:** Strict separation between ground binary interfaces (`Binary.Stage0`) and polynomial/circuit operators (`Binary.Stage1`).
