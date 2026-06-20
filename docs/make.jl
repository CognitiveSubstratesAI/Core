using Documenter
using MeTTaCore

DocMeta.setdocmeta!(MeTTaCore, :DocTestSetup, :(using MeTTaCore); recursive=true)

makedocs(;
    modules=[MeTTaCore],
    authors="CognitiveSubstrates AI",
    repo=Remotes.GitHub("CognitiveSubstratesAI", "Core"),
    sitename="MeTTaCore.jl",
    format=Documenter.HTML(;
        prettyurls=get(ENV, "CI", "false") == "true",
        canonical="https://cognitivesubstratesai.github.io/Core/stable/",
        edit_link="main",
        assets=String[]
    ),
    pages=[
        "Home" => "index.md",
        "Execution Backends" => "backends.md",
        "MeTTa-IL" => [
            "MeTTa-IL Lane" => "mettail.md",
            "GSLT Theory Algebra" => "gslt.md",
        ],
        "Pattern Mining" => [
            "Overview" => "pattern_mining/overview.md",
            "Mining Dialects" => "pattern_mining/dialects.md",
            "MORK-Native Miner" => "pattern_mining/mork_miner.md",
        ],
        "Dialect gaps (porting PeTTa-targeted algorithms)" => "dialect-gaps.md",
        "API Reference" => "api.md",
    ],
    warnonly=true
)

deploydocs(; repo="github.com/CognitiveSubstratesAI/Core", devbranch="main")
