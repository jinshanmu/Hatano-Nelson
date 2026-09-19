# Mathematical audit

This is an internal working note, not part of the article.

## Scope

The initial audit concerns the canonical family
\(A_n(a)=\operatorname{tridiag}(a,0,1)\), \(0<a<1\), in
`LMA/lma_pseudospectral_connectedness.tex`. It checks the logical structure,
the delicate algebraic identities, and representative numerical cases. It
is not a computer-verified proof or a claim that every possible error has
been excluded.

## Proof review

- The vertical determinant argument is valid provided its continuant
  certificate is included. The positive-definite continuation argument
  handles a positive starting singular value; a zero starting value follows
  from nonnegativity.
- The component argument and vertical deformation retraction give
  contractibility and the strict connectedness condition for the **open**
  pseudospectrum. Equality at the barrier is excluded.
- The even and odd signed-pencil inertia counts and interlacing comparisons
  select the stated ordered middle branch. Ties in minimum modulus cause no
  problem because an ordered eigenvalue remains continuous.
- The selected outer chord sheet remains separate from the inner variable;
  its open-and-closed continuation argument uses the strict outer-level
  bound to prevent exit through the lobe maximum.
- The noncentral comparison respects both the hyperbolic and elliptic
  portions of the same outer lobe. The central comparison additionally
  requires the scalar inequality and second-singular-value separation.
- The rectangular factorization, normal-vector overlap, and lower and upper
  bounds have the stated constants and the scale \((n+1)a^{n/2}\).
- Inverting those bounds gives the displayed two-term logarithmic critical
  order with an \(O_a(1)\) remainder. The two-site value is \(\gamma_2=a\).
- The boundary formulas for \(a=0\) (a disk, threshold zero) and \(a=1\)
  (half the largest adjacent eigenvalue gap) are consistent.

All six original appendix sections contain material used by the canonical
proof. Their contents should be integrated beside the relevant argument
when removing appendices.

One minor wording correction was identified: two hyperplanes have an
intersection of dimension **at least** \(n-1\), with equality when they
are distinct. The cross-Gram singular-value argument only needs the
at-least statement.

## Numerical identity checks

Checks used NumPy with a fixed pseudorandom seed, independently constructing
the matrices from their entries.

- Forty random parameter sets, dimensions 1–9: the six-step pure
  pentadiagonal continuant recurrence agreed with direct determinants.
  Maximum residual divided by \(1+|\det|\): \(7.5\times10^{-15}\).
- Forty random parameter sets, four steps in each parity: the signed
  four-dimensional folded transfer agreed with direct determinants of
  \(xI-A_n-sJ_n\). Maximum similarly scaled residual:
  \(2.3\times10^{-14}\).
- Five hundred random evaluations: the three expanded scalar identities
  used in the central lower comparison (the value at
  \(b=\rho+1/L\), the difference from \(b=1\), and the value at \(b=1\))
  agreed to scaled residuals below \(6\times10^{-15}\).
- Selected chord parametrizations were compared directly with least
  singular values for \(a=0.2,0.6,0.95,0.999\), orders 2–8, and 20 angular
  samples per order. The largest absolute discrepancy was
  \(4.2\times10^{-8}\), arising from ordinary floating-point cancellation
  in the square-root expression near a zero level. This is a diagnostic
  comparison, not a rigorous error bound.
- For \(a=0.02,0.2,0.6,0.95,0.999\), orders 2–15, and 601 angular samples
  per order, sampled barriers obeyed the two explicit bounds and strictly
  decreased with order. Eighty random vertical slices (101 heights each,
  orders 2–19) showed no decrease of the least singular value.

No substantive mathematical error was found in the audited canonical
arguments. Numerical sampling does not establish the universal statements;
the complete included proofs remain essential.

## New manuscript review

The integrated body of `connectedness_thresholds.tex` was reviewed after the six proof
supplements were inserted at their use sites. The central lower-comparison
proof now proceeds from the scalar inequality, through the signed product
and the second-singular-value separation, to the parity argument without
missing definitions. A source check found no duplicate labels, missing
cross-reference labels, or unmatched environments.

The hyperplane wording correction is incorporated. One further wording
clarification was recommended: for the two rectangular blocks at odd order,
specify the Gram matrices **in their smaller dimensions**, since one is
formed as \(C^*C\) and the other as \(CC^*\).

`preprint/make_figures.py` computes only the two figures used in the new
article, for the canonical family. Its grid sizes and methods match the
numerical section. Direct evaluation of the explicit bounds confirms the
caption's \(6\leq N_c\leq9\) bracket at \(a=1/4\),
\(\varepsilon=10^{-2}\). The copied script still had its old manuscript
name and command in its header when reviewed; updating those was requested.
The figure script was inspected, not rerun in full during this audit.

## Initial artifact checks

The rectangular-block clarification and figure-script names were updated.
The figure script was subsequently rerun in its pinned environment, reproducing
the transition at order 7 and the analytic bracket 6–9. The final manuscript
has 30 pages, with all proof details in the main text. The main build and an
independent build from the extracted source archive both completed with no
LaTeX warnings, unresolved references, or overfull boxes. Page images were
visually inspected, including the final front matter, two figures, and all
nine DOI-bearing references.

## Proof simplification (2026-09-19)

The preprint now uses direct generating-function elimination from the five
minors, two cases for the central scalar inequality, one factorization of
the central signed product, and adjacent-order logarithmic bounds for the
critical size. The odd middle-branch proof no longer needs the smaller-path
invertibility argument. The quantitative lower bound uses orthogonal
projection directly. Repeated vertical definitions and the second proof of
`gamma_2 = a` have been removed.

The initial formal five-minor states reproduce the actual terminal minors.
All formal-series denominators have constant term one. The central
comparison keeps the second-singular-value separation and the parity
argument after establishing positivity of the signed product. Its new
scalar identities and determinant prefactor agree with the corresponding
Lean proof. An independent numerical check of the signed product covered
20 parameter pairs (orders indexed by `L = 2,3,4,7`, including `rho = 1`);
the maximum relative residual was `2.8e-14` using a stable formula for `D`.

The introduction, theorem statements and assumptions, boundary section,
numerical section, figures, conclusions, declarations, and bibliography are
unchanged. The simplified manuscript has 28 pages. Its LaTeX build has no
warnings, unresolved references, or overfull boxes. All 106 cross-reference
labels are unique and resolve, and the page images have been inspected.
An independent build from the updated 19-file submission archive also
completed without warnings. Both archived figure PDFs match the unchanged
figure files. Lean validation and the proof correspondence are recorded in
`../lean/STATUS.md` and `../lean/FORMALIZATION_MAP.md`.
