# Sphere Packing in Lean

[Completing the formal proof of higher-dimensional sphere packing](<https://math.inc/sphere-packing>).

This repository formalizes sphere-packing optimality in **dimensions 8 and 24**, together with **uniqueness among periodic packings in dimension 24**. It focuses on the sphere-packing breakthroughs recognized by *Maryna Viazovska's 2022 Fields Medal* ([IMU citation](https://www.mathunion.org/fileadmin/IMU/Prizes/Fields/2022/IMU_Fields22_Viazovska_citation.pdf)).

The dimension 8 optimality formalization was kickstarted at EPFL by Maryna Viazovska and Sidharth Hariharan in March 2024 ([link](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean)). That foundational work established the repository, blueprint, and proof direction this project builds on.

Building directly on that original repository and blueprint, [Math, Inc.](https://www.math.inc/)'s autoformalization agent Gauss completed dimension 8 in 5 days, expanding the codebase from 20,000 to 60,000 lines. In the same repository, dimension 24 optimality and periodic uniqueness were completed in about 2 weeks using the associated [paper](https://annals.math.princeton.edu/2017/185-3/p08) plus autonomous literature search to bridge gaps, especially for uniqueness ingredients proved across other papers. The final codebase is about 180,000 lines of Lean.

Thanks to recent progress on Gauss, this development required no additional human-written scaffolding or proof hints beyond the original repository and papers. This is a significant milestone for autoformalization, demonstrating that results at the research frontier can be fully formalized with minimal human intervention, building on Lean's existing ecosystem of formalized mathematics.

**Note:** All line-count figures are post-cleanup (refactoring, golfing, and removal of unused results and theory developments). At peak, the full formalization reached roughly 500,000 lines of code; after cleanup, the final codebase is about 180,000 lines of Lean.

Formalizations like this will soon be commonplace and making multi-million-LOC autoformalizations modular and reusable will be an important challenge in the coming months. At the same time, plentiful autoformalization will accelerate mathematical understanding and discovery, and we are honored to have collaborated with Sid, Maryna, and the rest of the sphere packing team on pushing these frontiers.

## Highlights

This project formalizes the following key results in the theory of sphere packing:

* Dimension 8 optimality
* Dimension 24 optimality
* Dimension 24 uniqueness among periodic packings (up to scaling and isometries)
* During autoformalization, Gauss caught and automatically fixed two small issues in the source arguments:
  * In dimension 8: a sign error (minus sign) in Proposition 7 and a corrected expression for the magic function `g`.
  * In dimension 24: an incomplete step in the computer-assisted Appendix A argument.
* These fixes highlight how autoformalization can strengthen mathematical rigor by surfacing and resolving subtle issues in complex proofs

## Key links

* [Sid Hariharan's original upstream repository](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean)
* [Official press release](https://math.inc/sphere-packing)
* [Math Inc.](https://www.math.inc/)
* [Gauss (autoformalization agent)](https://www.math.inc/gauss)

## Useful commands

Compile the Lean files (requires [`Lean`](https://docs.lean-lang.org/lean4/doc/quickstart.html)):

```sh
lake exe cache get && lake build
```

Build the blueprint PDF (requires [`uv`](https://docs.astral.sh/uv/)):

```sh
uvx leanblueprint pdf
```

Build and serve the blueprint website:

```sh
uvx leanblueprint web && uvx leanblueprint serve
```

## References

* Maryna S. Viazovska, *The sphere packing problem in dimension 8*, Annals of Mathematics 185(3), 2017, 991-1015. DOI: [10.4007/annals.2017.185.3.7](https://doi.org/10.4007/annals.2017.185.3.7), Annals page: [link](https://annals.math.princeton.edu/2017/185-3/p07), arXiv: [1603.04246](https://arxiv.org/abs/1603.04246)
* Henry Cohn, Abhinav Kumar, Stephen D. Miller, Danylo Radchenko, Maryna Viazovska, *The sphere packing problem in dimension 24*, Annals of Mathematics 185(3), 2017, 1017-1033. DOI: [10.4007/annals.2017.185.3.8](https://doi.org/10.4007/annals.2017.185.3.8), Annals page: [link](https://annals.math.princeton.edu/2017/185-3/p08), arXiv: [1603.06518](https://arxiv.org/abs/1603.06518)
* Henry Cohn and Abhinav Kumar, *Optimality and uniqueness of the Leech lattice among lattices*, Annals of Mathematics 170(3), 2009, 1003-1050. DOI: [10.4007/annals.2009.170.1003](https://doi.org/10.4007/annals.2009.170.1003), Annals page: [link](https://annals.math.princeton.edu/2009/170-3/p01), arXiv: [math/0403263](https://arxiv.org/abs/math/0403263)
* Eiichi Bannai and N. J. A. Sloane, *Uniqueness of Certain Spherical Codes*, Canadian Journal of Mathematics 33(2), 1981, 437-449. DOI: [10.4153/CJM-1981-038-7](https://doi.org/10.4153/CJM-1981-038-7), journal page: [link](https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/uniqueness-of-certain-spherical-codes/DC891B62D2C6DE939B3FAAD16EF91B75)
