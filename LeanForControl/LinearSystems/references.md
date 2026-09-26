# References for the Kalman and realization modules

The Lean files point to these sources beside the corresponding declarations. Section
numbers below were checked against the author's table of contents. A cited
textbook topic supports the control-theoretic result; quotient universal
properties, exact finite horizons, and matrix-coordinate bridges are formal
formulations or consequences proved in this library, not claims of verbatim
textbook statements.

- Joao P. Hespanha, *Linear Systems Theory*, 2nd ed., Princeton University
  Press, 2018. [Author's book page](https://web.ece.ucsb.edu/~hespanha/linearsystems/)
  and [table of contents](https://web.ece.ucsb.edu/~hespanha/linearsystems/TOC.pdf).
- R. E. Kalman, "Mathematical Description of Linear Dynamical Systems",
  *Journal of the Society for Industrial and Applied Mathematics, Series A:
  Control* 1(2), 152-192, 1963.
  [DOI: 10.1137/0301010](https://doi.org/10.1137/0301010).
- B. L. Ho and R. E. Kalman, "Effective construction of linear state-variable
  models from input/output functions", *at - Automatisierungstechnik* 14,
  545-548, 1966.
  [DOI: 10.1524/auto.1966.14.112.545](https://doi.org/10.1524/auto.1966.14.112.545).

| Lean result family | Source location | Scope of match |
| --- | --- | --- |
| Reachable subspace and controllable restriction | Hespanha §§11.1, 11.6, 13.2 | Finite-dimensional reachable dynamics and controllable decomposition |
| Unobservable subspace and observable quotient | Hespanha §§15.2, 16.1 | Observable decomposition; quotient maps give a coordinate-free formulation |
| Four Kalman sectors, their dimensions, and the reachable/unobservable core | Hespanha §16.2; Kalman (1963) | Canonical structure; quotient and dimension identities are formal consequences |
| Realization, Markov parameters, behavioral equivalence | Hespanha §§4.3-4.4, 17.2 | State-space behavior and Markov data |
| Hankel factorization and rank | Ho and Kalman (1966) | Finite block Hankel construction; arbitrary horizons are stated explicitly in Lean |
| Minimal reduction and minimality characterization | Hespanha §§16.2, 17.1; Kalman (1963) | Controllable-observable reduction and minimal realization |
| Similarity and uniqueness of minimal realizations | Hespanha §17.3 | State-coordinate equivalence of equal minimal behavior |
| Finite Markov determination | Hespanha §17.2 | The exact n1+n2 window is derived here from Cayley-Hamilton, not quoted verbatim |
| Finite Ho-Kalman synthesis and recovery | Ho and Kalman (1966); Hespanha §§17.1-17.3 | Range/shift realization; explicit compatibility, finite horizon, and zero-dimensional cases are Lean formulations |