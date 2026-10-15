# Target journal: Journal of Combinatorial Theory, Series A

| Item | Details |
|---|---|
| Journal | Journal of Combinatorial Theory, Series A (JCTA) |
| Publisher | Elsevier |
| ISSN | 0097-3165 (print), 1096-0899 (electronic) |
| Guide for authors | https://www.sciencedirect.com/journal/journal-of-combinatorial-theory-series-a/publish/guide-for-authors |
| Submission | through Elsevier's online submission system linked from the guide for authors |
| Preprints | Elsevier allows submission of manuscripts posted as preprints |
| Class file | the paper uses plain `amsart`; Elsevier typesets accepted papers itself |

## Scope fit

JCTA publishes research in combinatorics, and the lattice form of the
Golomb–Welch conjecture has a line of papers there: T. Zhang and Y. Zhou,
*On the nonexistence of lattice tilings of ℤ^n by Lee spheres*, JCTA 165
(2019); K. H. Leung and Y. Zhou, *No lattice tiling of ℤ^n by Lee sphere of
radius 2*, JCTA 171 (2020); T. Zhang and G. Ge, *On linear diameter perfect
Lee codes with distance 6*, JCTA 201 (2024). The paper settles the two cases
(n, r) = (35, 3) and (805, 3) left open by A. Xiao and Y. Zhou,
arXiv:2610.19775, Theorem 5.1, and so completes the lattice form for every Lee
ball with fewer than 2^30 points.

MSC 2020: primary 52C22; secondary 05B45, 94B25, 05C25.

## Length and format

- 13 pages in `amsart`, with four schematic figures; built with no overfull or
  underfull boxes and no undefined references.
- A two-sentence abstract; MSC codes, keywords and the corresponding author in
  the first-page footnotes, as `amsart` places them.
- Two authors: Deep Bhattacharjee (corresponding author) and Ushashi
  Bhattacharya, with addresses, e-mail addresses and ORCID iDs.
- The source is a single file `main.tex` with the references in the source
  (`thebibliography`), so no `.bib` or `.bbl` file is needed.
  `dist/GolombWelchRadiusThree_final2-tex.zip` and the arXiv tarball contain
  this file and the figures as PNG.
- Declarations at the end: "Declaration of generative AI and AI-assisted
  technologies in the writing process", "Competing interests: None",
  "Funding: None" and "Data availability" (who computed what, the Zenodo DOI
  of the Lean formalization and the link to the PDF in
  `preprintGolombWelchRadiusThree/`).

## Policy on AI assistance

- Elsevier's policy on generative AI does not allow an AI tool to be listed as
  an author and asks authors who use such tools to say so in a section titled
  "Declaration of generative AI and AI-assisted technologies in the writing
  process", placed before the references; the authors remain responsible for
  the content.
- The paper has that section; it names Claude (Anthropic), used through
  Claude Code, and says how it was used. "Data availability" repeats it, and
  `AI_PROVENANCE_GolombWelchRadiusThree.md` gives the details. If the
  submission form has a field for AI provenance, upload that file.
- Every step of Sections 2 to 6 and both cases of the main theorem are checked
  by the Lean 4 kernel (Section 7 of the paper).
