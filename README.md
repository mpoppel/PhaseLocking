# Same Spectrum, Harder First-Order Training

Code, results and Lean formalisation for

> M. Poppel, D. Bucher, M. Zorn, M. Baumann, S. Wölckert, C. Linnhoff-Popien, P. Altmann, J. Stein.
> *Same Spectrum, Harder First-Order Training: Phase-Locking in Single- versus Multi-Qubit Re-Uploading Circuits.*
> arXiv:XXXX.XXXXX (2026).

For one-dimensional inputs, a single-qubit re-uploading (serial) circuit represents every function that a multi-qubit circuit
with the same encoding budget E can. The paper proves that the serial circuit has at most 2E + 2 tangent directions, one more
than its 2E + 1 Fourier coefficients need, against at least 6E + 6 for a two-qubit control with the same encoding budget and
model class, and measures what this costs in training: under gradient descent, Adam and Levenberg–Marquardt, on an exact loss
and on data, the serial circuit reaches its optimum less often than the control.

This repository contains everything behind the figures and tables of the paper: the simulation code, the result files, the
scripts that turn the result files into figures and tables, and the Lean 4 project that formalises the proofs.

## Contents

| Path | Content | Paper |
|---|---|---|
| `phaselock_core.py` | library: circuits, targets, optimisers (gradient descent with Armijo line search, Levenberg–Marquardt, Adam), statistics | Sec. 5, 6; App. A |
| `nb1_geometry.ipynb` | experiments on the exact loss: the three optimisers, conditioning along gradient descent, end points of Levenberg–Marquardt; writes `results/nb1/` | Sec. 5 |
| `nb2_practice.ipynb` | experiments on data: learning-rate tuning, evaluation, Levenberg–Marquardt on the same runs, checks of learning rate and step budget; writes `results/nb2/` | Sec. 6 |
| `screen_realdata.py` | the screen of real-world series, fixed before any circuit was run on a new series; writes `screening_results.csv` | App. A |
| `figures.ipynb` | all figures, from the result files alone; writes `figures/` | |
| `scripts/tables_exact.py` | tables of Section 5 and Appendix D, from `results/nb1/`; writes `tables/` | |
| `scripts/tables_data.py` | tables of Section 6 and Appendices A and D, from `results/nb2/`; writes `tables/` | |
| `results/` | the result files (CSV) of the runs reported in the paper | |
| `figures/`, `tables/` | the figures and tables as they appear in the paper | |
| `nottem.csv`, `gasprice.csv`, `ibmclose_ts.csv` | the three real-world series (see *Data* below) | Sec. 6 |
| `lean/` | Lean 4 / Mathlib formalisation of the lemmas, propositions, remarks and corollaries of Sections 3 and 4 and Appendix B; see `lean/README.md` | App. C |

## Installation

Python 3.12 with the packages in `requirements.txt`:

```
pip install -r requirements.txt
```

All simulations are exact statevector simulations in double precision with JAX 0.6.2 on a CPU; no GPU is needed.

## Reproducing the paper

Run everything from the root of the repository.

**Figures and tables from the stored results.** This runs no circuit and takes a few seconds:

```
jupyter nbconvert --to notebook --execute figures.ipynb
python scripts/tables_exact.py
python scripts/tables_data.py
```

**Rerunning the experiments.** Each notebook has a `RUN_MODE` in its first cell:

| `RUN_MODE` | scope | writes to |
|---|---|---|
| `'full'` | the runs of the paper (100 runs per circuit and configuration) | `results/` |
| `'reduced'` | fewer budgets and 30 runs | `results_reduced/` |
| `'quick'` | a few runs with short budgets, to check that everything runs | `results_quick/` |

Seeds are fixed per target and per initialisation (App. A, *Seeds*), so a full run reproduces the stored results.
Run times on a laptop CPU (Apple M2): `nb1_geometry` about [FILL IN], `nb2_practice` about [FILL IN].

**Lean.** See `lean/README.md`. In short, with `elan` installed:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

The last command prints the axioms behind every theorem named in `lean/README.md`; each line lists only `propext`,
`Classical.choice` and `Quot.sound`.

## Data

The real-world series are taken from Rdatasets (Arel-Bundock), which redistributes data sets from R packages:

- `nottem`: monthly mean air temperatures at Nottingham, 1920–1939 (R `datasets`; Anderson 1976, Series R);
- `gasprice`: weekly US gasoline prices, 1990–2003 (R package `quantreg`);
- `ibmclose`: daily IBM closing prices (Box & Jenkins 1970, Series B; R package `timeSeriesDataSets`).

`nb2_practice.ipynb` uses the local CSV files if present and otherwise downloads them from Rdatasets. The series remain under
the terms of their original sources.

## Citation

```bibtex
@article{poppel2026phaselocking,
  title   = {Same Spectrum, Harder First-Order Training: Phase-Locking in Single- versus Multi-Qubit Re-Uploading Circuits},
  author  = {Poppel, Michael and Bucher, David and Zorn, Maximilian and Baumann, Markus and W{\"o}lckert, Sebastian and
             Linnhoff-Popien, Claudia and Altmann, Philipp and Stein, Jonas},
  journal = {arXiv preprint arXiv:XXXX.XXXXX},
  year    = {2026}
}
```

## Acknowledgments

This work has been supported by the LMU Sustainability Fund (EfOiE), the BMFTR (QuCUN, QuaRDS, CAQAO), the Munich Quantum
Valley (K5, K7), and the Bavarian StMWi (6GQT).

## License

Code: MIT (see `LICENSE`). Result files, figures and tables: CC BY 4.0. The real-world series: see *Data*.
