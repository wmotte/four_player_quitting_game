# Literature

Core papers first, then a second shell. Theorem numbers for
Ashkenazi-Golan, Krasikov, Rainer and Solan (2024) are those of the journal
article, not of the arXiv preprint.

## The problem

Flesch, János, Frank Thuijsman, and O. J. Vrieze. 1997. “Cyclic Markov
equilibria in stochastic games.” *International Journal of Game Theory*
26(3): 303–314. doi:10.1007/BF01263273.

Solan, Eilon. 1999. “Three-player absorbing games.” *Mathematics of
Operations Research* 24(3): 669–698. doi:10.1287/moor.24.3.669.
Existence for at most three players. The method stops at three.

Solan, Eilon, and Nicolas Vieille. 2001. “Quitting games.” *Mathematics of
Operations Research* 26(2): 265–285. doi:10.1287/moor.26.2.265.10549.
Definition of the class; a uniform ε-equilibrium is an ε-equilibrium.

Solan, Eilon, and Nicolas Vieille. 2003. “Quitting games — an example.”
*International Journal of Game Theory* 31: 365–381.
doi:10.1007/s001820200125. Four-player example; period-2 profile. The same
derivation appears in Kellogg DP 1314 (22 January 2001). Crossref year 2003;
some copies are dated 2002.

Rassias, Michael Th., ed. 2021. “Solved and unsolved problems.” *EMS
Magazine* 121: 58–67. doi:10.4171/mag/38. Problem 251* (Solan): does every
quitting game with more than three players admit an ε-equilibrium for every
ε > 0? No meaning is attached here to the asterisk.

## Decomposition, complementarity, sunspots

Solan, Eilon, and Omri N. Solan. 2020. “Quitting games and linear
complementarity problems.” *Mathematics of Operations Research* 45(2):
434–454. doi:10.1287/moor.2019.0996. Every quitting game has a sunspot
ε-equilibrium. Q-matrix and LCP filters.

Ashkenazi-Golan, Galit, Ilia Krasikov, Catherine Rainer, and Eilon Solan.
2024. “Absorption paths and equilibria in quitting games.” *Mathematical
Programming* 203(1): 735–762. doi:10.1007/s10107-022-01807-6. Preprint:
arXiv:2012.04369. Theorem 3.4 is the decomposition used in this repository.
arXiv Theorem 4.13 is journal Theorem 4.15.

Ashkenazi-Golan, Galit, Ilia Krasikov, Catherine Rainer, and Eilon Solan.
2026. “The APS approach for undiscounted quitting games.” *International
Journal of Game Theory* 55(1). doi:10.1007/s00182-026-00982-6. Four authors;
the Krasikov is Ilia.

## Escape games and topology

Simon, Robert Samuel. 2007. “The structure of non-zero-sum stochastic
games.” *Advances in Applied Mathematics* 38(1): 1–26.
doi:10.1016/j.aam.2006.07.002. Theorem 4: escape games have approximate
equilibria.

Simon, Robert Samuel. 2012. “A topological approach to quitting games.”
*Mathematics of Operations Research* 37(1): 180–195.
doi:10.1287/moor.1110.0532. Theorem 4.1 and Question 1. A counterexample
with only normal players in the min-max sense would falsify that question.

Simon, Robert Samuel. 2016. “The challenge of non-zero-sum stochastic
games.” *International Journal of Game Theory* 46(1): 191–204. Survey,
including escape games. Some copies are dated 2015.

## Nearby

Solan, Eilon. 2001. “The dynamics of the Nash correspondence and n-player
stochastic games.” *International Game Theory Review* 3(4): 291–299.
Period unbounded; fully absorbing orbits.

## Tools used to produce the certificates

Berthomieu, Jérémy, Christian Eder, and Mohab Safey El Din. 2021. “msolve: a
library for solving polynomial systems.” In *ISSAC ’21*, 51–58. ACM.
doi:10.1145/3452143.3465545.

de Moura, Leonardo, and Sebastian Ullrich. 2021. “The Lean 4 theorem prover
and programming language.” In *CADE 28*, LNCS, 625–635.

The mathlib Community. 2020. “The Lean mathematical library.” In *CPP 2020*,
367–381.

## Not used as a result

Simon, Robert Samuel. 2023. “A stochastic game without approximate
equilibria.” arXiv:2310.04217. Withdrawn; the proof is flawed.
