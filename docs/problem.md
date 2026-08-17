# The four-player quitting problem

A *quitting game* is a stochastic game with the following rules. There is a
finite set of players. Each round, every player independently chooses to
continue or to quit. If everyone continues, the game is played again. If at
least one player quits, the game ends and each player receives a payoff that
depends on the set of players who quit at that round. Payoffs are bounded.
There is no discounting: what matters is the payoff at absorption, or a
prescribed continuation value if the game never ends.

The question is whether every such game admits a uniform ε-equilibrium for
every ε > 0: a strategy profile such that no player can gain more than ε by
deviating, uniformly in the horizon. Solan (1999) proved that the answer is
yes for at most three players. From four players on, the question is open.
It appears as Problem 251* in Rassias (ed.), *Solved and unsolved problems*,
EMS Magazine 121 (2021).

Two caveats belong with the question.

- Every quitting game has a *sunspot* ε-equilibrium (Solan and Solan 2020).
  Correlation through a public signal is enough. A negative answer can only
  concern *uncorrelated* equilibria.
- Simon (2007, Theorem 4) proved that every *escape game* has approximate
  equilibria. A candidate that satisfies his membership criterion is therefore
  not a counterexample, whatever else has been proved about it.

## The decomposition

Ashkenazi-Golan, Krasikov, Rainer and Solan, *Absorption paths and equilibria
in quitting games*, Mathematical Programming 203 (2024), Theorem 3.4, give
an if-and-only-if. A quitting game has an ε-equilibrium for every ε > 0
exactly when one of the following holds.

1. A stationary ε-equilibrium exists.
2. An ε-equilibrium that terminates in the first round exists.
3. There is an absorbing profile in which every player is sequentially
   ε-perfect.

The third branch splits. Jump-free absorption (Flesch paths; several players
quitting at positive rates at the same instant) is one piece. Paths that mix
continuous stretches with discrete jumps are the rest. Periodic profiles are
a computable subfamily of the mixed case, not a fourth branch of the
theorem.

A computational search can treat the theorem as a list of things to refute,
on one explicit game with rational payoffs. Closing the first two branches,
and the jump-free and periodic pieces of the third, is exact algebra. The
bounded mixed remainder is not: see [status.md](status.md).

## Why compute

For four players the strategy space is already too large for a hand
classification of all mixed paths. What can be done by machine, in exact
rationals, is: isolate every real root of a polynomial system and discard it
by a best-response inequality; certify emptiness of a subdivision by a sign
on every leaf; expand a Nullstellensatz identity; replay the same identity
in Lean. That is the route taken here, in Julia, because that is the
toolkit at hand. Heuristic search (random screening, then differential
evolution) only proposes a game. The certificates are the argument.
