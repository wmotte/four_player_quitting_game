# V3 (continuous part): Essential-APS iteration for Flesch absorption paths
# (FAPs), after Ashkenazi-Golan, Krasikov, Rainer & Solan, "The APS approach
# for undiscounted quitting games", Internat. J. Game Theory 55(1), 2026,
# doi:10.1007/s00182-026-00982-6, and AKRS (Math. Programming 203(1), 2024;
# preprint arXiv:2012.04369) §5. Comments below say "Krasikov" as shorthand
# for the 2026 paper; the numbered results are from it.
#
# Setting: AKRS normalization r_{i},i = 0. `unilateral_matrix(g)` has entry
# (i,j) = shifted payoff to player i when player j quits alone (this is the
# transpose of Krasikov's R, whose ROWS are quit vectors).
#
# Machinery (Krasikov):
# * Lemma 4.1: along a sequentially perfect FAP, the successor of quitter i
#   lies in S_i = {j : payoff_to_i(j quits) < 0 < payoff_to_j(i quits)};
#   payoffs stay in R^I_+; the active quitter's payoff is 0.
# * Essential APS operator on per-first-quitter collections (E_i):
#       E_i ← R{i} ∪ T_i(∪_{j∈S_i} E_j),
#   T_i(E) = co({R^i} ∪ E) ∩ {w_i = 0} ∩ R^I_+  (per convex piece; unions are
#   preserved, NOT hulled). Iterating from the top per strongly connected
#   component yields nested outer bounds Ē_i ⊇ E_i of the true sequentially
#   perfect FAP payoff sets (Prop. 4.9).
# * Theorem 4.10 (tightness): if for every SCC N and every simple circuit
#   M ⊆ N we have F_N ∩ H_M = ∅ (no payoff giving 0 to a whole circuit),
#   then E = ∪_i Ē_i exactly.
#
# Trichotomy delivered by `aps_fap_analysis`:
#   :no_fap        — some iterate became empty ⇒ NO sequentially perfect FAP
#                    (certificate; refutation-relevant),
#   :fap_exists    — iteration stabilized nonempty AND the Thm 4.10 circuit
#                    condition holds ⇒ continuous equilibria EXIST
#                    (candidate must be rejected),
#   :inconclusive  — otherwise (e.g. bounds collapse onto circuit-degenerate
#                    payoffs, as in Krasikov Ex. 3.4 where Ē = {0} but E = ∅;
#                    a bespoke argument is then required).

using Polyhedra
import CDDLib

const APSLib = CDDLib.Library(:exact)
const PQ = Rational{BigInt}

"Successor sets S_i from the shifted unilateral matrix (entry (i,j): payoff to i when j quits)."
function successor_sets(R::Matrix{T}) where {T}
    n = size(R, 1)
    [ [j for j in 1:n if j != i && R[i, j] < 0 && R[j, i] > 0] for i in 1:n ]
end

"Strongly connected components of the successor graph, in topological order (sinks first)."
function scc_topo(S::Vector{Vector{Int}})
    n = length(S)
    # reachability closure
    reach = [falses(n) for _ in 1:n]
    for i in 1:n, j in S[i]
        reach[i][j] = true
    end
    for _ in 1:n, i in 1:n, j in 1:n, k in 1:n
        if reach[i][j] && reach[j][k]
            reach[i][k] = true
        end
    end
    comp = zeros(Int, n)
    comps = Vector{Vector{Int}}()
    for i in 1:n
        comp[i] != 0 && continue
        c = [i]
        comp[i] = length(comps) + 1
        for j in (i+1):n
            if comp[j] == 0 && reach[i][j] && reach[j][i]
                comp[j] = comp[i]
                push!(c, j)
            end
        end
        push!(comps, c)
    end
    # topological order: component A before B if A reaches B; we want sinks
    # (no outgoing reachability) processed FIRST.
    order = sortperm(1:length(comps);
        lt = (a, b) -> any(i -> any(j -> reach[i][j], comps[b]), comps[a]) &&
                       !any(i -> any(j -> reach[j][i], comps[b]), comps[a]),
        rev = true)
    comps[order], reach
end

# --- small polyhedral helpers (exact rational, CDD) ------------------------

function _box_hs(n::Int, bound::PQ)
    hs = HalfSpace{PQ,Vector{PQ}}[]
    for j in 1:n
        e = zeros(PQ, n); e[j] = -1
        push!(hs, HalfSpace(e, PQ(0)))            # w_j ≥ 0
        e2 = zeros(PQ, n); e2[j] = 1
        push!(hs, HalfSpace(e2, bound))           # w_j ≤ bound
    end
    hs
end

function isempty_pol(P)
    vr = vrep(P)
    npoints(vr) == 0 && nrays(vr) == 0 && nlines(vr) == 0
end

_verts(P) = collect(points(vrep(P)))

function _pol_contains(P, x::AbstractVector)
    for hs in halfspaces(hrep(P))
        sum(hs.a .* x) <= hs.β || return false
    end
    for hp in hyperplanes(hrep(P))
        sum(hp.a .* x) == hp.β || return false
    end
    true
end

poly_eq(P, Q) = (isempty_pol(P) && isempty_pol(Q)) ||
    (!isempty_pol(P) && !isempty_pol(Q) &&
     all(x -> _pol_contains(Q, x), _verts(P)) &&
     all(x -> _pol_contains(P, x), _verts(Q)))

"T_i applied to one convex piece given by its vertex list."
function _ti_piece(quitvec::Vector{PQ}, piece_verts::Vector{Vector{PQ}}, i::Int, n::Int)
    ei = zeros(PQ, n); ei[i] = 1
    # first restrict the continuation piece to {v_i = 0}
    Pc = polyhedron(vrep(piece_verts), APSLib)
    Pc0 = polyhedron(hrep(Pc) ∩ hrep([HyperPlane(ei, PQ(0))]), APSLib)
    base = isempty_pol(Pc0) ? Vector{Vector{PQ}}() : _verts(Pc0)
    allv = vcat(base, [quitvec])
    P = polyhedron(vrep(allv), APSLib)
    hs = HalfSpace{PQ,Vector{PQ}}[]
    for j in 1:n
        e = zeros(PQ, n); e[j] = -1
        push!(hs, HalfSpace(e, PQ(0)))
    end
    Q = polyhedron(hrep(P) ∩ hrep(hs) ∩ hrep([HyperPlane(ei, PQ(0))]), APSLib)
    isempty_pol(Q) ? nothing : Q
end

"""
    aps_fap_analysis(g; maxiter = 40, maxpieces = 24, verbose = false)
        -> (status, sets, ncircuit_failures)

Run the Essential-APS outer iteration (per-player unions of exact rational
polytopes) and the Theorem 4.10 circuit condition. See file header for the
trichotomy semantics. When the union size exceeds `maxpieces` the pieces are
hulled (still sound for `:no_fap`, but `:fap_exists` is then downgraded to
`:inconclusive`).
"""
function aps_fap_analysis(g::QuittingGame; maxiter::Int = 40, maxpieces::Int = 24,
                          verbose::Bool = false)
    Rm = Matrix{PQ}(unilateral_matrix(convert(QuittingGame{PQ}, g)))
    n = size(Rm, 1)
    S = successor_sets(Rm)
    bound = maximum(abs.(Rm)) + 1
    quitvecs = [PQ[Rm[l, i] for l in 1:n] for i in 1:n]

    hulled = false
    # Correct initialization (Krasikov Eq. (8)/(9)): the ambient set is
    # F_N = co({R^i}_i ∪ downstream sets) ∩ R^I_+, NOT the whole box — this
    # matters: the degenerate zero-rate-cycle payoff 0 often lies outside
    # co({R^i}), and only the F_N start prunes it. (Single-SCC formula used
    # for the ambient hull over all players; sound since it is a superset of
    # each per-SCC F_N.)
    FNall = polyhedron(vrep(quitvecs), APSLib)
    hsplus = HalfSpace{PQ,Vector{PQ}}[]
    for j in 1:n
        e = zeros(PQ, n); e[j] = -1
        push!(hsplus, HalfSpace(e, PQ(0)))
    end
    FN = polyhedron(hrep(FNall) ∩ hrep(hsplus), APSLib)
    sets = Vector{Vector{Any}}(undef, n)
    for i in 1:n
        ei = zeros(PQ, n); ei[i] = 1
        P = polyhedron(hrep(FN) ∩ hrep([HyperPlane(ei, PQ(0))]), APSLib)
        sets[i] = isempty_pol(P) ? Any[] : Any[P]
    end

    status = :maxiter
    for k in 1:maxiter
        newsets = Vector{Vector{Any}}(undef, n)
        for i in 1:n
            pieces = Any[]
            # R{i}: the constant FAP ι ≡ i, feasible iff R^i ≥ 0
            if all(quitvecs[i] .>= 0)
                push!(pieces, polyhedron(vrep([quitvecs[i]]), APSLib))
            end
            for j in S[i], piece in sets[j]
                Q = _ti_piece(quitvecs[i], _verts(piece), i, n)
                Q === nothing || push!(pieces, Q)
            end
            if length(pieces) > maxpieces
                hulled = true
                allv = reduce(vcat, _verts.(pieces))
                pieces = Any[polyhedron(vrep(allv), APSLib)]
            end
            newsets[i] = pieces
        end
        verbose && println("  iter $k: pieces ", [length(s) for s in newsets],
                           "  verts ", [sum(p -> npoints(vrep(p)), s; init = 0) for s in newsets])
        if all(isempty, newsets)
            return (:no_fap, newsets, 0)
        end
        stable = all(1:n) do i
            length(newsets[i]) == length(sets[i]) &&
                all(t -> poly_eq(newsets[i][t], sets[i][t]), 1:length(newsets[i]))
        end
        sets = newsets
        if stable
            status = :stable
            break
        end
    end

    # Theorem 4.10 circuit condition on F_N: for every simple circuit M of
    # the successor graph, F_N ∩ H_M = ∅ (no payoff giving 0 to a whole
    # circuit simultaneously).
    circuits = _simple_circuits(S)
    nfail = 0
    for M in circuits
        h = hrep(FN)
        for j in M
            ej = zeros(PQ, n); ej[j] = 1
            h = h ∩ hrep([HyperPlane(ej, PQ(0))])
        end
        isempty_pol(polyhedron(h, APSLib)) || (nfail += 1)
    end

    if status == :stable && nfail == 0 && !hulled
        return (:fap_exists, sets, 0)
    end
    (:inconclusive, sets, nfail)
end

"All simple directed circuits (distinct-vertex cycles) of the successor graph."
function _simple_circuits(S::Vector{Vector{Int}})
    n = length(S)
    out = Vector{Vector{Int}}()
    function dfs(path)
        u = path[end]
        for v in S[u]
            if v == path[1] && length(path) >= 2
                push!(out, copy(path))
            elseif v > path[1] && !(v in path)   # canonical: smallest vertex first
                push!(path, v)
                dfs(path)
                pop!(path)
            end
        end
    end
    for s in 1:n
        dfs([s])
    end
    out
end

# Backwards-compatible simple entry point used elsewhere/tests.
function aps_fap_iteration(g::QuittingGame; maxiter::Int = 40, verbose::Bool = false)
    st, sets, _ = aps_fap_analysis(g; maxiter = maxiter, verbose = verbose)
    flat = [isempty(s) ? polyhedron(vrep(Vector{Vector{PQ}}()), APSLib) : s[1] for s in sets]
    st2 = st == :no_fap ? :empty : (st == :fap_exists ? :stable : st)
    (st2, flat, maxiter)
end

# --- (L8): in these games, two players never quit at once -------------------
#
# `:no_fap` certifies the absence of a sequentially perfect FAP, and an FAP has
# exactly one player quitting at each instant ([K] Def. 2.4 with the appendix
# identification). Axiom (A.4) does not supply that: it forbids two players
# terminating simultaneously, not two players each quitting at a positive rate
# at the same instant. So the jump-free regime has a residue that `:no_fap`
# does not reach, and (L8) of docs/G3_MIXED_APS.md §12.2 closes it by a finite
# condition on the unilateral matrix alone:
#
#   for every B ⊆ I with |B| ≥ 2, the system
#       Σ_{j ∈ B} z_j · R̂_{j,i} = 0  (i ∈ B),   z_j > 0  (j ∈ B)
#   has no solution.
#
# `R̂_{j,i}` is the shifted payoff to i when j quits alone, so with
# `U = unilateral_matrix(g)` (entry (i,j) = payoff to i when j quits) the
# system is simply `U[B,B] * z = 0` with `z > 0`: a strictly positive kernel
# vector of the principal submatrix. Nonsingularity is sufficient and is what
# actually happens for the finalists, but it is not necessary, so a singular
# submatrix is decided exactly rather than reported as a failure.

"Exact reduced row echelon form over the rationals; returns (R, pivot columns)."
function _rref_q(A::Matrix{PQ})
    R = copy(A)
    m, n = size(R)
    piv = Int[]
    row = 1
    for col in 1:n
        row > m && break
        sel = findfirst(r -> !iszero(R[r, col]), row:m)
        sel === nothing && continue
        sel += row - 1
        sel == row || (R[[row, sel], :] = R[[sel, row], :])
        R[row, :] ./= R[row, col]
        for r in 1:m
            r == row && continue
            iszero(R[r, col]) && continue
            R[r, :] .-= R[r, col] .* R[row, :]
        end
        push!(piv, col)
        row += 1
    end
    R, piv
end

"Exact basis of the null space of `A` over the rationals."
function _kernel_q(A::Matrix{PQ})
    R, piv = _rref_q(A)
    n = size(A, 2)
    free = setdiff(1:n, piv)
    basis = Vector{Vector{PQ}}()
    for f in free
        v = zeros(PQ, n)
        v[f] = one(PQ)
        for (r, p) in enumerate(piv)
            v[p] = -R[r, f]
        end
        push!(basis, v)
    end
    basis
end

"""
    stiemke_witness(M) -> Vector{PQ} or nothing

A vector `y` with `Mᵀy ≥ 0` and `Mᵀy ≠ 0`, or `nothing` when none exists.

Such a `y` **refutes** `M z = 0, z > 0` in one line, with no appeal to any
theorem of alternatives: if `M z = 0` then `0 = ⟨M z, y⟩ = ⟨z, Mᵀy⟩`, while
`z > 0` and `Mᵀy ≥ 0` with some entry strictly positive force `⟨z, Mᵀy⟩ > 0`.
That is why the certificate exported for (L8) is this `y` and not the
determinant: a determinant says the kernel is trivial and then needs a separate
argument for the singular case, whereas `y` is checkable by substitution and
covers both cases in the same shape.

Existence in the other direction is Stiemke's lemma, so `nothing` is returned
exactly when a strictly positive kernel vector does exist. The search is the
exact LP `{y : Mᵀy ≥ 0, Σ_i (Mᵀy)_i ≥ 1}`, non-empty iff the cone
`{Mᵀy ≥ 0}` holds anything but `0`, since it is a cone.
"""
function stiemke_witness(M::Matrix{PQ})
    k = size(M, 1)
    hs = HalfSpace{PQ,Vector{PQ}}[]
    for i in 1:k
        push!(hs, HalfSpace(PQ[-M[j, i] for j in 1:k], PQ(0)))    # (Mᵀy)_i ≥ 0
    end
    push!(hs, HalfSpace(PQ[-sum(M[j, i] for i in 1:k) for j in 1:k], PQ(-1)))
    P = polyhedron(hrep(hs), APSLib)
    isempty_pol(P) && return nothing
    collect(PQ, first(points(vrep(P))))
end

"""
    simultaneous_quit_systems(g) -> Vector{NamedTuple}

One row per coalition `B` with `|B| ≥ 2`, in mask order. Each row reports the
principal submatrix `U[B,B]` of `unilateral_matrix(g)`, its exact determinant,
and whether the system of (L8) has a strictly positive solution `z`:

* `:nonsingular` — `det ≠ 0`, so `z = 0` is the only solution at all;
* `:no_positive_kernel` — singular, but the null space misses the open positive
  orthant, decided exactly;
* `:positive_kernel` — a strictly positive `z` exists and is returned in
  `witness`, so (L8)'s hypothesis fails for this `B`.

The first two statuses also carry `dual`, the refuting `y` of
`stiemke_witness` — which is what the certificate exports, the determinant
being a report rather than a proof. Primal and dual are computed
independently and must disagree about nothing: a `dual` is present exactly
when `witness` is absent, and this function checks that rather than assuming
it, so a bug in either search shows up as an error and not as a certificate.

Everything is `Rational{BigInt}`; nothing here goes through floating point.
"""
function simultaneous_quit_systems(g::QuittingGame)
    gq = convert(QuittingGame{PQ}, g)
    U = Matrix{PQ}(unilateral_matrix(gq))
    N = nplayers(gq)
    rows = NamedTuple[]
    for mask in 1:(2^N - 1)
        B = coalition_players(mask, N)
        length(B) >= 2 || continue
        M = U[B, B]
        d = det(M)
        y = stiemke_witness(M)
        # The primal side: a strictly positive kernel vector, if one exists.
        # The kernel is a cone through the origin, so it meets {z > 0} iff it
        # holds a point with every z_i ≥ 1.
        z = nothing
        if iszero(d)
            basis = _kernel_q(M)
            nb = length(basis)
            hs = [HalfSpace(PQ[-basis[t][i] for t in 1:nb], PQ(-1))
                  for i in 1:length(B)]
            P = polyhedron(hrep(hs), APSLib)
            if !isempty_pol(P)
                λ = collect(PQ, first(points(vrep(P))))
                z = [sum(λ[t] * basis[t][i] for t in 1:nb) for i in 1:length(B)]
            end
        end
        # Stiemke: exactly one of the two searches may succeed. They are run
        # independently, so requiring that here turns a bug in either into an
        # error instead of into a certificate.
        (z === nothing) == (y !== nothing) ||
            error("primal and dual disagree on B = $B: this is a bug, not a game")
        status = z !== nothing ? :positive_kernel :
                 iszero(d) ? :no_positive_kernel : :nonsingular
        push!(rows, (B = B, mask = mask, M = M, det = d,
                     status = status, witness = z, dual = y))
    end
    rows
end

"""
    no_simultaneous_quit(g) -> (ok, assumption28, rows)

`ok` is (L8)'s hypothesis: no coalition of two or more players admits a
strictly positive `z` solving the system above. When it holds, every 0-AP of
`g` has exactly one player quitting at a positive rate at almost every instant
of continuous time — so the jump-free residue of §12.1 is empty and `:no_fap`
covers the whole continuous regime.

`assumption28` is [K] Assumption 2.8, `R̂_{i,j} = 0 ⟺ i = j`, reported
alongside because it is what implies the `|B| = 2` cases on its own.
"""
function no_simultaneous_quit(g::QuittingGame)
    rows = simultaneous_quit_systems(g)
    gq = convert(QuittingGame{PQ}, g)
    U = Matrix{PQ}(unilateral_matrix(gq))
    N = nplayers(gq)
    a28 = all(iszero(U[i, j]) == (i == j) for i in 1:N, j in 1:N)
    (all(r -> r.status != :positive_kernel, rows), a28, rows)
end
