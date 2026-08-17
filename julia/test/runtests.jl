using Test
using Random
using QuittingGames
using QuittingGames: min_stationary_violation_grid, min_directional_violation_grid, exact

const Q = Rational{BigInt}

@testset "QuittingGames" begin

@testset "model basics" begin
    g = unanimity_game(3)
    @test nplayers(g) == 3
    @test coalition_mask([1, 3]) == 5
    @test coalition_players(5, 3) == [1, 3]

    x = [0.3, 0.5, 0.2]
    p = quit_distribution(x)
    @test sum(p) ≈ 1.0
    @test p[1] ≈ 0.7 * 0.5 * 0.8
    @test p[1 + coalition_mask([2])] ≈ 0.7 * 0.5 * 0.8 / 0.5 * 0.5 atol = 1e-12
    @test absorption_prob(x) ≈ 1 - 0.7 * 0.5 * 0.8

    xq = Q[1//3, 0, 1//2]
    pq = quit_distribution(xq)
    @test sum(pq) == 1
    @test pq[1] == 2//3 * 1 * 1//2
    @test eltype(pq) == Q
end

@testset "stage game consistency" begin
    g = ftv1997()
    x = Q[1//2, 0, 0]
    y = Q[0, 0, 1]
    for i in 1:3
        x1 = copy(x); x1[i] = 1
        x0 = copy(x); x0[i] = 0
        D = deviation_gain(g, i, x, y)
        @test stage_value(g, x1, y)[i] - stage_value(g, x0, y)[i] == D
    end
end

@testset "FTV 1997 ground truth" begin
    g = ftv1997()
    cyc = ftv1997_cycle()
    @test periodic_violation(g, cyc) == 0
    @test periodic_margin(g, cyc) == 0
    ys = periodic_values(g, cyc)
    @test ys[1] == Q[1, 2, 1]
    @test ys[2] == Q[1, 1, 2]
    @test ys[3] == Q[2, 1, 1]

    best, _ = min_stationary_violation_grid(convert(QuittingGame{Float64}, g); resolution = 15)
    @test best > 1e-3

    bestd, _ = min_directional_violation_grid(convert(QuittingGame{Float64}, g); resolution = 40)
    @test bestd > 1e-3

    @test stationary_violation(g, Q[0, 0, 0]) == 1
end

@testset "Solan–Vieille 4-player ground truth" begin
    g = solan_vieille_4p()
    for i in 1:4
        @test payoffs(g)[coalition_mask([i]), i] == 1
    end
    r = payoffs(g)
    for m in 1:15
        swapped = ((m & 1) << 1) | ((m & 2) >> 1) | ((m & 4) << 1) | ((m & 8) >> 1)
        @test r[m, 1] == r[swapped, 2]
        @test r[m, 3] == r[swapped, 4]
    end

    cyc = solan_vieille_4p_cycle(bits = 256)
    gF = convert(QuittingGame{BigFloat}, g)
    viol = setprecision(BigFloat, 256) do
        periodic_violation(gF, cyc)
    end
    @test viol < big"1e-60"

    best, _ = min_stationary_violation_grid(convert(QuittingGame{Float64}, g); resolution = 9)
    @test best > 1e-3

    @test stationary_violation(g, Q[0, 0, 0, 0]) == 1
end

@testset "existence classes behave" begin
    g = symmetric_game(3, Q[1, 1//2, 0], Q[2, 1//4])
    best, _ = min_stationary_violation_grid(convert(QuittingGame{Float64}, g); resolution = 15)
    @test best < 1e-8

    gu = unanimity_game(3)
    @test is_stationary_equilibrium(gu, Q[0, 0, 0])
    @test is_stationary_equilibrium(gu, Q[1, 1, 1])
end

@testset "filters (Solan–Solan / AKRS battery)" begin
    ftv = ftv1997()
    sv = solan_vieille_4p()

    @test normal_players(ftv) == [1, 2, 3]
    @test normal_players(sv) == [1, 2, 3, 4]

    Rftv = unilateral_matrix(ftv)
    @test Rftv == Q[0 -1 2; 2 0 -1; -1 2 0]
    @test lcp0_nontrivial(Rftv) === nothing
    @test q_matrix_witness(Rftv) === nothing

    I3 = Matrix{Q}(zeros(Q, 3, 3)); for i in 1:3 I3[i,i] = 1 end
    @test lcp_solvable(I3, Q[-1, 2, -3])
    @test q_matrix_witness(I3) === nothing
    @test q_matrix_witness(-I3) !== nothing

    @test !filter_report(unanimity_game(3)).viable
    gsym = symmetric_game(3, Q[1, 1//2, 0], Q[2, 1//4])
    @test !filter_report(gsym).viable

    repftv = filter_report(ftv)
    @test !repftv.viable
    @test any(startswith("F8"), repftv.reasons)

    repsv = filter_report(sv)
    @test !repsv.viable
    @test any(startswith("F2"), repsv.reasons)
end

@testset "escape-class screen (F9, Simon 2007 Thm 4 / 2012 §2.2)" begin
    ftv = ftv1997()
    sv = solan_vieille_4p()

    for g in (ftv, sv, unanimity_game(3), symmetric_game(3, Q[1, 1//2, 0], Q[2, 1//4]))
        for j in 1:g.N, t in (Q(1, 3), Q(3, 4), Q(1, 1000))
            ξ = [k == j ? t : Q(0) for k in 1:g.N]
            @test escape_gap(g, j, ξ) == 0
            @test !first(escape_admissible(g, ξ))
        end
    end

    for g in (ftv, sv)
        M = escape_pair_matrix(g)
        for j in 1:g.N, k in 1:g.N
            j == k && continue
            @test M[j, k] == g.r[coalition_mask([j, k]), j] - g.r[coalition_mask([k]), j]
            for t in (Q(1, 5), Q(1, 2), Q(7, 8))
                ξ = zeros(Q, g.N); ξ[j] = Q(1, 3); ξ[k] = t
                @test escape_gap(g, j, ξ) == t * M[j, k]
            end
        end
    end

    let g = sv, v = unilateral_diag(g)
        for j in 1:g.N
            ξ = Q[1//3, 1//5, 2//7, 1//2]
            xq = copy(ξ); xq[j] = Q(1)
            xc = copy(ξ); xc[j] = Q(0)
            @test escape_gap(g, j, ξ) ==
                  stage_value(g, xq, v)[j] - stage_value(g, xc, v)[j]
        end
    end

    @test escape_pair_witness(sv) !== nothing
    let sc = escape_screen(sv)
        @test sc.status === :violates
        @test sc.witness.kind === :pair
        @test sc.margin > 0
        (ok, x, viol) = escape_confirm(sv, sc.witness.ξ)
        @test ok
        @test iszero(viol)
        @test all(x .> unilateral_diag(exact(sv)))
    end

    let g = exact(sv), v = unilateral_diag(exact(sv)), t = Q(1, 3), j = 1
        ξ = [k == j ? t : Q(0) for k in 1:g.N]
        x = Vector{Q}(undef, g.N)
        for k in 1:g.N
            if k == j
                x[k] = v[k]
            else
                z = prod(Q[Q(1) - ξ[m] for m in 1:g.N if m != k])
                A = escape_gap(g, k, ξ) + z * v[k]
                x[k] = max(A / z, v[k] + 1)
            end
        end
        @test iszero(escape_bare_violation(g, ξ, x))
        @test x[j] == v[j]
        @test !first(escape_admissible(g, ξ))
    end

    let g = exact(sv)
        r_on = filter_report(g; qtrials = 20, escape = true)
        r_off = filter_report(g; qtrials = 20, escape = false)
        @test !any(startswith("F9"), r_on.reasons)
        @test r_on.escape.status === :violates
        @test r_off.escape === nothing
        @test setdiff(r_on.reasons, r_off.reasons) == String[]
    end
    let g = exact(ftv)
        r_on = filter_report(g; qtrials = 20, escape = true)
        @test any(startswith("F9"), r_on.reasons)
    end
end

@testset "rationalize + fitness plumbing" begin
    g = convert(QuittingGame{Float64}, ftv1997())
    gr = rationalize_game(g)
    @test convert(QuittingGame{Rational{BigInt}}, gr).r == ftv1997().r

    f = fitness(g; starts = 20, qtrials = 20)
    @test f.value == -Inf
end

@testset "periodic machinery" begin
    g = ftv1997()
    x = Q[1//3, 1//4, 0]
    @test periodic_margin(g, [x]) == stationary_violation(g, x)
    ys = periodic_values(g, [Q[0, 0, 0], Q[0, 0, 0]])
    @test all(all(iszero, y) for y in ys)
    sv = convert(QuittingGame{BigFloat}, solan_vieille_4p())
    m = setprecision(BigFloat, 256) do
        periodic_margin(sv, solan_vieille_4p_cycle(bits = 256))
    end
    @test m < big"1e-60"
end

@testset "essential APS / FAP analysis" begin
    rows = [Q[0, 4, -1, -1], Q[-1, 0, 4, 1], Q[-1, -1, 0, 4], Q[4, 1, -1, 0]]
    r = zeros(Q, 15, 4)
    for i in 1:4, j in 1:4
        r[1 << (i - 1), j] = rows[i][j]
    end
    gk = QuittingGame(4, r)
    @test successor_sets(unilateral_matrix(gk)) == [[2], [3], [4], [1]]
    st, _, nf = aps_fap_analysis(gk; maxiter = 60)
    @test st == :no_fap
    @test nf == 0

    st2, sets2, nf2 = aps_fap_analysis(ftv1997(); maxiter = 30)
    @test st2 == :fap_exists
    @test nf2 == 0
    verts1 = sort(collect(QuittingGames.points(QuittingGames.vrep(sets2[1][1]))))
    @test verts1 == [Q[0, 0, 1], Q[0, 1, 0]]
end

@testset "search reliability (corner seeding + descent termination)" begin
    t = @elapsed (m, _) = min_stationary_violation(
        convert(QuittingGame{Float64}, ftv1997()); starts = 50)
    @test t < 30.0
    @test m > 0.15

    for gq in (symmetric_game(3, Q[1, 1//2, 0], Q[2, 1//4]), solan_vieille_4p())
        gf = convert(QuittingGame{Float64}, gq)
        N = gf.N
        cornerbest = minimum(stationary_violation(gf,
                                 Float64[(m >> (i - 1)) & 1 for i in 1:N])
                             for m in 1:(2^N - 1))
        mc, _ = min_stationary_violation(gf; starts = 1)
        @test mc <= cornerbest + 1e-9
    end

    msym, _ = min_stationary_violation(
        convert(QuittingGame{Float64}, symmetric_game(3, Q[1, 1//2, 0], Q[2, 1//4]));
        starts = 5)
    @test msym < 1e-9
end

@testset "rational snap honours the denominator cap" begin
    rng = Random.Xoshiro(7)
    gf = QuittingGame(4, 4 .* rand(rng, 15, 4) .- 2)
    for D in (8, 16, 32)
        gs = rationalize_game(gf; denom = D)
        @test all(v -> denominator(v) <= D, gs.r)
        @test all(abs.(float.(gs.r) .- gf.r) .<= 1 / (2D) + 1e-12)
    end
end

@testset "game identity: key, family, fingerprint" begin
    g = ftv1997()
    @test game_key(g) == game_key(convert(QuittingGame{Rational{BigInt}}, g))
    @test game_key(g) == game_key(convert(QuittingGame{Float64}, g))
    @test game_fingerprint(g) == game_fingerprint(exact(g))

    r = Matrix{Q}(exact(g).r)
    r[2^3 - 1, 1] += 1
    h = QuittingGame(3, r)
    @test game_key(h) != game_key(g)
    @test family_key(h) == family_key(g)

    r2 = Matrix{Q}(exact(g).r)
    r2[1, 1] += 1
    @test family_key(QuittingGame(3, r2)) != family_key(g)
end

end
