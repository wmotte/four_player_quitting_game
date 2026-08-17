"""
    QuittingGames

The heuristic search for a four-player quitting game without uncorrelated
ε-equilibrium. Float64 throughout, except the filters and the escape screen,
which run in exact rationals. Output is a shortlist. Certificates live
elsewhere in this repository and are not produced here.

`x[i]` is the probability that player `i` quits. Coalitions are bitmasks:
player `i` is bit `i-1`.
"""
module QuittingGames

using LinearAlgebra
using Random
using Printf

export QuittingGame, payoffs, nplayers, coalition_mask, coalition_players,
       game_key, family_key, game_fingerprint, family_fingerprint, exact,
       quit_distribution, absorption_prob, stage_value, deviation_gain,
       stage_nash_violation, is_stage_nash,
       selfconsistent_value, stationary_violation, stationary_br_values,
       is_stationary_equilibrium, min_stationary_violation_grid,
       periodic_values, periodic_violation, periodic_margin, is_periodic_equilibrium,
       limit_value, directional_violation, min_directional_violation_grid,
       payoff_sup_norm, unilateral_diag,
       ftv1997, ftv1997_cycle, solan_vieille_4p, solan_vieille_4p_cycle,
       symmetric_game, unanimity_game,
       ss_shifted, normal_players, unilateral_matrix, lcp0_nontrivial,
       lcp_solvable, q_matrix_witness, filter_report,
       escape_gap, escape_pair_matrix, escape_pair_witness, escape_admissible,
       escape_bare_violation, escape_confirm, escape_margin, escape_witness,
       escape_screen,
       degenerate_indifference_pairs, full_coalition_degeneracies,
       fitness, rationalize_game, min_stationary_violation, min_periodic_violation,
       min_corner_violation,
       successor_sets, aps_fap_analysis

include("game.jl")
include("stage.jl")
include("stationary.jl")
include("periodic.jl")
include("directional.jl")
include("limit_floors.jl")
include("examples.jl")
include("filters.jl")
include("fitness.jl")
include("aps.jl")

end
