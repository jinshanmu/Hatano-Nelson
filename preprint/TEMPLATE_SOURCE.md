# Preprints.org template source

The manuscript uses the Preprints.org LaTeX template with the unmodified
`Definitions/mdpi.cls` class dated **23 June 2026**.

- Official instructions: <https://www.preprints.org/instructions-for-authors>
- Official template archive linked by those instructions:
  <https://www.preprints.org/statics/file/preprints-template.zip>
- Publisher's official Overleaf template and documentation of the `preprints`
  class option:
  <https://www.overleaf.com/latex/templates/mdpi-article-template/fcpwsspfzsph>

The live archive returned HTTP 403 on 19 September 2026. The files in
`Definitions/`, together with the untouched reference file
`official-template/template.tex`, were copied from the existing local extracted
Preprints.org template directory `preprints_template_latex/`.
The reference template already selects `preprints` as its journal option.
No replacement or reconstructed class is used. The class, styles, and original
attribution comments have been retained without modification. The official
Overleaf listing identifies the template's license as CC BY 4.0:
<https://creativecommons.org/licenses/by/4.0/>.

## Manuscript options

```tex
\documentclass[preprints,article,accept,oneauthor]{Definitions/mdpi}
```

`accept` follows the template's documented option for a posting copy without
line numbers. It does not declare journal acceptance. `oneauthor` selects the
single-author layout. The manuscript has no assigned publication date or DOI.

The class supplies `amsmath`, `amssymb`, `amsthm`, `booktabs`, `graphicx`,
`microtype`, `natbib`, `hyperref`, and `cleveref`. It supplies numeric square
bracket citations for the `preprints` option; use `\cite{key}` or `\citep{key}`
and avoid `\citet`. The class loads `hyperref` and `cleveref` in a document
hook, so manuscript `\crefname` definitions belong after `\begin{document}`.

It defines capitalized mathematical environments (`Theorem`, `Lemma`,
`Proposition`, etc.) and reserves lowercase counters with those names. If
lowercase environments and a shared section-based numbering scheme are used,
create a fresh shared counter, for example:

```tex
\newcounter{result}[section]
\renewcommand{\theresult}{\thesection.\arabic{result}}
\theoremstyle{mdpi}
\newtheorem{theorem}[result]{Theorem}
\newtheorem{lemma}[result]{Lemma}
\newtheorem{proposition}[result]{Proposition}
```

The class prints the title, abstract, and keywords automatically when the
document begins. Do not add a second `\maketitle` or an `abstract` environment.

## Verification

The standalone smoke test in `.build/template-smoke.tex` compiled successfully
with TeX Live 2025 and `latexmk -pdf`, using the copied definitions. Its final
log has no LaTeX warnings or errors. The test checks the author front matter,
ORCID, theorem numbering, proof environment, numerical citation, and DOI URL.

SHA-256 checksums:

```text
881dbcd3cd97dc37432c2d0a55538ff9b2856ed6be07db4c97d20616aaaa1c80  Definitions/mdpi.cls
3b747eee144173c46a43562ead905c26322c7cb394e350a925d36dcf63884680  Definitions/mdpi.bst
30a7629adfb074e62683aa3acffe58c032b81b0d090c62f9ad5a6ea7344e7a09  Definitions/journalnames.tex
a90ab72aa379a1c22fee051b7e72b354a37f20421ab4080946b55317081a2246  official-template/template.tex
```
