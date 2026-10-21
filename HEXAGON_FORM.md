# Hexagon submission fields

Title: No lattice tiling of Z^35 or Z^805 by Lee balls of radius three

Abstract: We prove that there is no lattice tiling of Z^35 or of Z^805 by Lee balls of radius three. These were the only cases left open by Xiao and Zhou among the Lee balls of dimension at least three and radius at least two with fewer than 2^30 points, so the lattice Golomb-Welch conjecture holds for all of them.

Primary subject: math.CO (Combinatorics)
Cross-list subjects: math.MG (Metric Geometry), cs.IT (Information Theory), math.NT (Number Theory)
Tags: Golomb-Welch conjecture, Lee metric, perfect code, lattice tiling, group ring
MSC2020: 52C22 Tilings in n dimensions (aspects of discrete geometry); 05B45 Combinatorial aspects of tessellation and tiling problems; 94B25 Combinatorial codes; 05C25 Graphs and abstract algebra (groups, rings, fields, etc.)

Contributor 1 (submitting): Deep Bhattacharjee; ORCID 0000-0003-0466-750X; affiliation: Formerly, Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India; formerly, University of Calcutta, Senate House, 87/1 College Street, Kolkata 700073, West Bengal, India; itsdeep@live.com (second address d.bhattacharjee@erl-forschung.de)
Contributor 2: Ushashi Bhattacharya; ORCID 0009-0002-2254-3914; affiliation: Formerly, National Taiwan University, Taipei 106319, Taiwan; rai.bhattacharya.in@gmail.com

Text of the contribution: A mix of human-written and AI-generated.
Human understanding: "All parts" only after both authors have read every proof; otherwise "Some parts, but not all".

Provenance statement: The proofs, the text, the figures, the Lean 4 formalisation and the C, C++, Python, Julia and shell programs were carried out by Deep Bhattacharjee with the help of AI assistance (Claude, Anthropic) in the Claude Code environment. The reduction of a lattice tiling to a group-ring equation follows Zhang and Zhou and Xiao and Zhou, and the paper credits them; the new steps are the constant term modulo 29^2 for n = 805 and the joint projection to Z/71 x Z/29 through dual numbers with the circulant systems for n = 35. Both theorems are proved in Lean 4 with Mathlib (GolombWelch.golomb_welch_35 and GolombWelch.golomb_welch_805), depending only on the axioms propext, Classical.choice and Quot.sound, with no sorry, native_decide or added axiom; the finite computations in F_29, F_71 and Z/841 are checked by the kernel, and every finite quantity of the paper is recomputed by programs in at least two languages. No statement rests on a floating-point computation. The paper does not prove the Golomb-Welch conjecture: it settles two cases of its lattice form, and tilings that are not lattice tilings are not covered because 59711 and 696845031 are not prime. Both authors approved the final version.

Tools used: Anthropic - Claude (Claude Code); Lean community - Lean 4 (v4.34.1) with Mathlib; C; C++; Python; Julia; shell.
arXiv identifier: none (not posted on arXiv).
Formalization: https://github.com/creelie/refactored-waddle/blob/main/lean/GolombWelch.lean (release v1.1.0: https://github.com/creelie/refactored-waddle/releases/tag/v1.1.0)

Source files or ZIP: GolombWelchRadiusThree_final2-tex.zip (the folder GolombWelchRadiusThree_final2-tex/ with main.tex and figures/ as PNG; seven entries; compiles with latexmk -pdf main.tex, no BibTeX pass, all fonts embedded). Do not upload the master zip or the Lean files here.
AI provenance files: AI_PROVENANCE_GolombWelchRadiusThree.md
License: CC BY 4.0

Data availability (in the paper): LaTeX source, the Lean 4 formalisation and the programs in release v1.1.0, https://github.com/creelie/refactored-waddle/releases/tag/v1.1.0; repository https://github.com/creelie/refactored-waddle; the folder preprintGolombWelchRadiusThree holds the PDF only.
AI disclosure (in the paper, Data and code availability): Deep Bhattacharjee carried out the computations and the Lean, Julia, C, C++, Python and shell verifications, and the proofs and the text were drafted, with AI assistance (Claude, Anthropic); both authors approved the final version. No separate AI declaration.
Funding: none. Competing interests: none.
Device folder: D:\Hexagon\12 GolombWelchRadiusThree.
