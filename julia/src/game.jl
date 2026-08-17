"""
    QuittingGame{T}

Payoff structure of an `N`-player quitting game. `r` has size `(2^N - 1, N)`;
row `mask` holds the payoff vector when exactly the coalition with bitmask
`mask` quits. The payoff when nobody ever quits is the zero vector (fixed by
normalization, as in the literature).
"""
struct QuittingGame{T<:Real}
    N::Int
    r::Matrix{T}
    function QuittingGame{T}(N::Int, r::Matrix{T}) where {T<:Real}
        size(r) == (2^N - 1, N) ||
            throw(ArgumentError("payoff matrix must be (2^N-1) × N = $((2^N-1, N)), got $(size(r))"))
        new{T}(N, r)
    end
end

QuittingGame(N::Int, r::Matrix{T}) where {T<:Real} = QuittingGame{T}(N, r)

"""
    QuittingGame(N, pairs::Pair{<:AbstractVector{<:Integer},<:AbstractVector}...)

Construct a game from `players_of_S => payoff_vector` pairs, e.g.
`QuittingGame(3, [1] => [1, 3, 0], [2] => [0, 1, 3], ...)`. Every non-empty
coalition must be specified exactly once.
"""
function QuittingGame(N::Int, pairs::Pair...)
    T = promote_type(map(p -> eltype(last(p)), pairs)...)
    r = Matrix{T}(undef, 2^N - 1, N)
    seen = falses(2^N - 1)
    for (S, v) in pairs
        m = coalition_mask(S)
        1 <= m <= 2^N - 1 || throw(ArgumentError("invalid coalition $S"))
        seen[m] && throw(ArgumentError("coalition $S specified twice"))
        length(v) == N || throw(ArgumentError("payoff vector for $S must have length $N"))
        seen[m] = true
        r[m, :] .= v
    end
    all(seen) || throw(ArgumentError("missing coalitions: $( [coalition_players(m, N) for m in findall(!, seen)] )"))
    QuittingGame{T}(N, r)
end

nplayers(g::QuittingGame) = g.N
payoffs(g::QuittingGame) = g.r

"Bitmask of a coalition given as an iterable of player indices."
coalition_mask(S) = mapreduce(i -> 1 << (i - 1), |, S; init = 0)

"Player indices of a coalition bitmask."
coalition_players(mask::Integer, N::Integer) = [i for i in 1:N if (mask >> (i - 1)) & 1 == 1]

"Convert the game to a different number type (e.g. `Rational{BigInt}` for exact work)."
Base.convert(::Type{QuittingGame{T}}, g::QuittingGame) where {T<:Real} =
    QuittingGame{T}(g.N, Matrix{T}(g.r))

exact(g::QuittingGame) = convert(QuittingGame{Rational{BigInt}}, g)

"""
    game_key(g) -> String

Canonical exact rendering of the payoff table: `N` followed by every entry as
`numerator/denominator` in row-major coalition order. Two games have the same
key exactly when their payoff tables are equal as rationals, whatever the
element type they are stored in.

This is the AUTHORITATIVE identity of a game. Use it, not `game_fingerprint`,
whenever a wrong answer would cost something: hashes collide, string equality
does not.

Why this exists: Phase-1 saves a snapshot on every fitness improvement
(`scripts/run_phase1.jl`), and two successive improvements can round to the
same game once payoffs are snapped to a coarse denominator. That happened —
`gen004` and `gen009` are the same 4-player game — and it went unnoticed
through resnapping, period-2 certification, margin witnesses and Lean export,
because nothing along that chain ever compared two candidates.
"""
function game_key(g::QuittingGame)
    gq = convert(QuittingGame{Rational{BigInt}}, g)
    io = IOBuffer()
    print(io, gq.N)
    for m in 1:(2^gq.N - 1), i in 1:gq.N
        c = gq.r[m, i]
        print(io, ';', numerator(c), '/', denominator(c))
    end
    String(take!(io))
end

"""
    family_key(g) -> String

Canonical exact rendering of the UNILATERAL rows only — the payoff vectors of
the singleton coalitions {i}, i.e. the matrix R. Games sharing a family key
share their R and are called a *family* here.

R alone decides the directional margin, `LCP(R,0)`, the Q-matrix filters and
the FAP/APS analysis (see `scripts/run_phase1.jl` stage A), so every rung of
the ladder that depends on R only gives the same answer for a whole family and
needs to be run once per family, not once per candidate.
"""
function family_key(g::QuittingGame)
    gq = convert(QuittingGame{Rational{BigInt}}, g)
    io = IOBuffer()
    print(io, gq.N)
    for j in 1:gq.N, i in 1:gq.N
        c = gq.r[1 << (j - 1), i]
        print(io, ';', numerator(c), '/', denominator(c))
    end
    String(take!(io))
end

"""
    fnv1a64(s) -> UInt64

FNV-1a over the bytes of `s`. Deliberately hand-rolled rather than `hash`:
`Base.hash` is only promised to be stable within one Julia session, and these
digests end up in written reports and certificate manifests where they have to
mean the same thing next year. Self-contained, so no new dependency either.
"""
function fnv1a64(s::AbstractString)
    h = 0xcbf29ce484222325
    for b in codeunits(s)
        h = (h ⊻ b) * 0x100000001b3
    end
    h
end

"Short stable digest of `game_key(g)`; for display and file naming only."
game_fingerprint(g::QuittingGame) = string(fnv1a64(game_key(g)); base = 16, pad = 16)[1:12]

"Short stable digest of `family_key(g)`; for display and file naming only."
family_fingerprint(g::QuittingGame) = string(fnv1a64(family_key(g)); base = 16, pad = 16)[1:8]

function Base.show(io::IO, g::QuittingGame{T}) where {T}
    print(io, "QuittingGame{$T}($(g.N) players)")
end

function Base.show(io::IO, ::MIME"text/plain", g::QuittingGame{T}) where {T}
    println(io, "QuittingGame{$T} with $(g.N) players; r_S per quitting coalition S:")
    for m in 1:(2^g.N - 1)
        println(io, "  ", rpad(string(coalition_players(m, g.N)), 14), " => ", g.r[m, :])
    end
end
