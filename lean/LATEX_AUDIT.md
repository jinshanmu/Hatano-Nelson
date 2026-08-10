# LAA statement and proof alignment

Audited source: `../LAA/laa_connected_pseudospectra.tex`

## Main dependency chain

The LAA proof and the Lean assembly use the same sequence:

1. vertical least-singular-value monotonicity;
2. deformation to the real axis and the exact connectedness criterion;
3. signed-pencil selection of the least-modulus middle branch;
4. folded Chebyshev and endpoint-side chord classification;
5. noncentral and central gap comparisons;
6. strict adjacent-size decrease of the global barrier;
7. rectangular two-sided barrier estimates;
8. elementary logarithmic inversion of the tail model; and
9. the exact order-two endpoint.

No assumption in `ConnectedPseudospectrum.main_theorem` exceeds the LAA
hypotheses `0<a<1` and `epsilon>0`.

## Simplifications made for the LAA version

- The paper defines only the first connected size `N_c`.  Strict barrier
  decrease proves directly that the connected sizes form the tail
  `{n : n >= N_c}`.  This exact set identity is formalized as
  `connectedDimensions_eq_criticalThreshold_tail` and included in
  `main_theorem`; first-hit and eventual sets remain internal order-theoretic
  proof devices.
- The threshold asymptotic is derived directly from
  `beta x - log(x+1) = log(1/t)`.  The unused exact Lambert-`W` floor formula,
  its auxiliary domain condition, and the corresponding Lean module were
  removed.
- Repeated folded formulas and terminal-vector multiplications were kept only
  at the point where they are proved or used.
- The endpoint-side chord-exhaustion lemma now states all outputs consumed by
  the main comparison: bidirectional exhaustion, signed-root magnitude,
  distinct folded variables, and the odd central-half case.
- The diagonal shift in the affine Toeplitz corollary is allowed to be complex;
  the reduction uses translation, positive scaling, and unitary conjugation by
  the reversal permutation, none of which requires a real diagonal shift.

## Standalone corollary and backward-error endpoints

The pointwise norm-minimizing perturbation formula is formalized both in
general form as
`generalPseudospectralHeight_isLeast_spectralBackwardErrors` and in the
paper's path-matrix notation as
`realGapValue_isLeast_spectralBackwardErrors`.  The affine
Toeplitz reduction is formalized by the exact set identity
`positiveToeplitzPseudospectrum_eq_affine_image`; component contractibility,
the scaled connectedness criterion, strict scaled-barrier decrease, and the
exact connected-dimension tail are assembled in the remaining public
theorems of `GeneralToeplitz.lean`.  The first connected dimension is also
recorded as an attained minimum, while
`positiveToeplitz_threshold_bounds_and_asymptotic` transfers the threshold
bounds, the scaled-level asymptotic, and the exact size-two endpoint.
These endpoints use only the necessary positive-dimension or positive
unequal off-diagonal hypotheses appearing in the manuscript.

The figures, references, and physical Discussion are non-theorem material
outside the kernel scope.  They are not used to prove `main_theorem`.

`FORMALIZATION_MAP.md` lists the corresponding Lean endpoints, and
`STATUS.md` records the latest executable validation.
