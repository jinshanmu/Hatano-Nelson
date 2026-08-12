# Third-party notices

## ELA/SIAM standard LaTeX macros (2016)

The current ELA manuscript uses the unmodified `siamart1116.cls` version
1.4.1 and `siamplain.bst` distributed through ELA's official author-template
page.  The complete upstream 13-file macro distribution is retained as
`ELA/official-template/siamart_1116.zip`; its provenance and checksums are
recorded in `ELA/official-template/SOURCE.md`.  Convenience copies of the
class and bibliography style beside the manuscript are byte-for-byte
identical to the files in that archive.

The class notice permits redistribution only with the complete macro
distribution and prohibits alteration of the class.  The separate
`ELA/siamart1116-compat.tex` file is an original, conditional pre-class shim
for current LaTeX kernels; it does not modify the upstream class.  The
embedded upstream notice, rather than this summary, is controlling.  These
third-party macros are excluded from the repository's MIT grant.

## SIAM standard LaTeX macros

The historical SIMAX submission bundle includes the Society for Industrial
and Applied Mathematics (SIAM) standard LaTeX macros dated 2025-12-16. The
class identifies itself as `siamart251216` version 1.4.8.

The notice embedded in `siamart251216.cls` prohibits changing the class and
permits redistribution only when it is kept together with the complete
required macro set. It also prohibits distributing the class alone and
prohibits charging for the distribution or use except for a nominal copying
charge. The embedded notice—not this summary—is controlling.

The eight files expressly required by that notice are:

1. `siamart251216.cls`
2. `siamplain.bst`
3. `docsiamart.tex`
4. `docsiamart.pdf`
5. `references.bib`
6. `ex_article.tex`
7. `ex_supplement.tex`
8. `ex_shared.tex`

SIAM's current standard-macro download also lists five companion example
artifacts: `ex_article.pdf`, `ex_supplement.pdf`, `lexample_fig1.eps`,
`lexample_fig2.eps`, and `data.dat`. This repository keeps all 13 files
together where the class is retained:

- `SIMAX_submission_bundle/`

The authoritative upstream inventory is the
[SIAM Journal Authors macro page](https://epubs.siam.org/journal-authors#siam-macros).

### Documentation-source restoration and verification

The previously retained bundle contained SIAM's supplied `docsiamart.pdf` but
omitted the mandatory corresponding `docsiamart.tex`. On 2026-07-16, that
source was restored from a copy downloaded directly from SIAM's standard-macro
page. The restored documentation source compiles successfully with the
retained unmodified SIAM class and support files to a 20-page PDF. Its text was
checked against the supplied 20-page documentation PDF, with no substantive
difference.

The TeX Live 2025 verification produced no error and no unresolved reference
or citation. The unmodified upstream documentation does emit package, font,
and box warnings in that environment. They were recorded as upstream
documentation behavior and were not "fixed" by altering redistributed SIAM
source.

Key SHA-256 checksums are:

```text
99da5fb774a55fd982ddf5eea88f7555dba5930f4980c16ae7a65cdf220586e5  docsiamart.tex
eeb023a366fc66f9c28301729802094e56408a1b4998cac0d473b9ea2918eab2  docsiamart.pdf
33f2eb091c8bcbda9baed2e868489460da868047b0a518b4ce1b2f2c15fda530  siamart251216.cls
a5df7c482dc7d4459f08b91c28437c3779284dcd82591acf1c977de7508ac6c7  siamplain.bst
```

These files remain SIAM material. They are excluded from the repository's MIT
grant, and no ownership or relicensing claim is made for them.

## SIAM style guide

The copy of `SIAM_STYLE_GUIDE_2019.pdf` in
`SIMAX_submission_bundle/SIAM_template/` is also third-party SIAM material
and is excluded from the repository's MIT grant. Its own copyright and terms
control.
