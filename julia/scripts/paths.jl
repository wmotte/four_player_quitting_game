# The one place that knows the layout.

if !@isdefined REPO_ROOT
    const REPO_ROOT    = normpath(joinpath(@__DIR__, "..", ".."))
    const ARTIFACTS    = joinpath(REPO_ROOT, "artifacts")
    const CANDIDATES   = joinpath(ARTIFACTS, "candidates")
    const RESULTS      = joinpath(ARTIFACTS, "results")
end
