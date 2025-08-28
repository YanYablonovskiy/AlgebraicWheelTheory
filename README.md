# AlgebraicWheelTheory

[![Lean Action CI](https://github.com/YanYablonovskiy/AlgebraicWheelTheory/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/YanYablonovskiy/AlgebraicWheelTheory/actions/workflows/lean_action_ci.yml)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/YanYablonovskiy/GibbsMeasure)

This project aims to formalise some results of JESPER CARLSTRÖM[1] on algebraic wheels.

This repository aims to *digitize* various mathematical definitions, theorems, and their proofs. 

Digitization, a.k.a mechanization, involves converting traditional rigorous mathematical content (from sources like textbooks, PDFs, websites, or videos) into a type-checking system based on a computer-implemented *foundations of math framework*, such as set theory or type theory.

In this case the foundational theory is a form of caculus of constructions with inductive types, implemented in the Lean 4 functional programming language. Lean is being developed by the [Lean FRO](https://lean-fro.org/) AWS, and this project wouldn't be possible without Leonardo de Moura and his valued colleagues.

## Content

This project currently contains a definition of a Wheel, and a few basic results without any direct constructions as of yet.

### Code organisation

The Lean code is in the path `AlgebraicWheelTheory/`. Currently the Wheel definition and basic consequences are in `Basic.lean`, Involution Monoids are defined in `Defs.lean`.

## Build the Lean files

In order to compile the Lean files of this project, you need to have a working version of Lean.
See [the installation instructions](https://leanprover-community.github.io/get_started.html)
(under Regular install).
Another option to try is Gitpod. Click on the button below to open a Gitpod workspace containing the project.

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/YanYablonovskiy/AlgebraicWheelTheory)

Regardless, open cmd and run `lake exe cache get` followed by `lake build` to build the project.

## Build the blueprint

See instructions at https://github.com/PatrickMassot/leanblueprint/.

## Acknowledgements

Our project builds on Mathlib. I therefore thank its numerous contributors without whom this
project couldn't even begin.

Much of the project infrastructure has been adapted from
* [sphere eversion](https://leanprover-community.github.io/sphere-eversion/)
* [liquid tensor experiment](https://github.com/leanprover-community/liquid/)
* [unit fractions](https://github.com/b-mehta/unit-fractions/)
* [Gibbs Measures](https://github.com/james18lpc/GibbsMeasure/)

# References
[1] JESPER CARLSTRÖM. “Wheels – on division by zero”. In: Mathematical Structures in
Computer Science 14.1 (2004), pp. 143–184. doi: 10.1017/S0960129503004110.
