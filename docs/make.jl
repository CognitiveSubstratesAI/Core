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
        "Connectome substrate" => "connectome.md",
    ],
    warnonly=true
)

deploydocs(; repo="github.com/CognitiveSubstratesAI/Core", devbranch="main")
