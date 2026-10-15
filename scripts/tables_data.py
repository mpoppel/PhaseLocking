"""Tables for Section 6 and Appendices A and D from the NB2 result files (results/nb2/*.csv) and the screen
(data/screening_results.csv). Writes tables/tab_practice.tex, tab_real.tex, tab_screen.tex, tab_lr_data.tex, and, if the
robustness cells 2b and 2d of NB2 have been run, tab_lr_ext.tex and tab_budget.tex; if cell 3 (Levenberg-Marquardt) has
been run, tab_lm_data.tex, tab_heldout.tex and data_text_numbers.txt.

A run "reaches the optimum" if its log10 excess training loss is <= THR. THR = -6 (excess loss at most 1e-6 of the target
variance) lies between the failed runs (about -1 to -4.5) and the level at which the optimisers leave a converged run,
which depends on the optimiser and the schedule: -16 for Adam under the schedule of cell 2, -7 to -10 under a slower final
decay, -14 to -16 for Levenberg-Marquardt (it stops below 1e-14)."""
from pathlib import Path
import numpy as np, pandas as pd

R, OUT = Path('results/nb2'), Path('tables'); OUT.mkdir(exist_ok=True)
E_ = pd.read_csv(R / 'eval.csv')
THR, ARMS = -6, ['serial', 'ancilla', 'parallel2']
NAME = {'nottem': r'\texttt{nottem}', 'gasprice': r'\texttt{gasprice}', 'ibmclose': r'\texttt{ibmclose}', 'flat': 'flat', 'bump': 'Poisson kernel'}   # names as in the text of the paper (R data set names in typewriter)
TNAME = {'nottem': 'nottem', 'gasprice': 'gasprice', 'ibmclose': 'ibmclose'}   # plain names for data_text_numbers.txt

def wilson(k, n, z=1.959964):
    p = k / n; den = 1 + z * z / n; c = (p + z * z / (2 * n)) / den; h = z * np.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / den
    return c - h, c + h
def newcombe(k1, n1, k2, n2):
    """95% interval for p1 - p2 (Newcombe 1998, hybrid Wilson score); as in phaselock_core"""
    p1, p2 = k1 / n1, k2 / n2; l1, u1 = wilson(k1, n1); l2, u2 = wilson(k2, n2); d = p1 - p2
    return d, d - np.sqrt((p1 - l1) ** 2 + (u2 - p2) ** 2), d + np.sqrt((u1 - p1) ** 2 + (p2 - l2) ** 2)
def reach(d, a):
    """(runs of arm a that reach the optimum, runs)"""
    x = d[d.arm == a].lexc; return int((x <= THR).sum()), len(x)
def share(d, a):
    k, n = reach(d, a); return f'{k / n:.2f}'
def diff_cell(d):
    """ancilla - serial share of runs at the optimum, with Newcombe interval"""
    (ks, ns), (ka, na) = reach(d, 'serial'), reach(d, 'ancilla'); dd, lo, hi = newcombe(ka, na, ks, ns); return f'{dd:+.2f} [{lo:+.2f}, {hi:+.2f}]'
def err_ratio(d):
    """held-out error (1 - R^2), serial over ancilla, paired by run index (same target; for real series the same data):
    median, 10% and 90% quantiles of the ratio, and the share of pairs in which serial is worse"""
    a = d[d.arm == 'ancilla'].set_index('run').test_R2; s = d[d.arm == 'serial'].set_index('run').test_R2
    r = ((1 - s) / (1 - a)).dropna()
    return r.median(), r.quantile(.1), r.quantile(.9), float((r > 1).mean())

# Table: synthetic targets
rows = [r'\begin{tabular}{llccccccc}\toprule',
        r' & & \multicolumn{3}{c}{runs at the optimum} & ancilla$-$serial & \multicolumn{2}{c}{median test $R^2$} & held-out error \\',
        r'\cmidrule(lr){3-5}\cmidrule(lr){7-8}',
        r'target & $E$ & serial & ancilla & par.\,2 & difference [95\%] & serial & ancilla & serial/ancilla \\\midrule']
for fam in ['flat', 'bump']:
    for E in sorted(E_[E_.family == fam].E.unique()):
        d = E_[(E_.family == fam) & (E_.E == E)]
        r2 = {a: d[d.arm == a].test_R2.median() for a in ['serial', 'ancilla']}
        ratio = r'\textemdash' if fam == 'flat' else '{:.2f} [{:.2f}, {:.2f}]'.format(*err_ratio(d)[:3])
        rows.append(f'{NAME[fam]} & {E} & {share(d, "serial")} & {share(d, "ancilla")} & {share(d, "parallel2")} & {diff_cell(d)} & '
                    f'{r2["serial"]:.4f} & {r2["ancilla"]:.4f} & {ratio} \\\\')
    rows.append(r'\midrule' if fam == 'flat' else r'\bottomrule')
(OUT / 'tab_practice.tex').write_text('\n'.join(rows + [r'\end{tabular}']) + '\n')

# Table: real series
rows = [r'\begin{tabular}{lcccccccc}\toprule',
        r' & & \multicolumn{3}{c}{runs at the optimum} & \multicolumn{2}{c}{median test $R^2$} & held-out error & serial runs \\',
        r'\cmidrule(lr){3-5}\cmidrule(lr){6-7}',
        r'series & $E$ & serial & ancilla & par.\,2 & serial & ancilla & serial/ancilla [10\%, 90\%] & worse \\\midrule']
for fam in ['gasprice', 'ibmclose', 'nottem']:
    for E in sorted(E_[E_.family == fam].E.unique()):
        d = E_[(E_.family == fam) & (E_.E == E)]
        r2 = {a: d[d.arm == a].test_R2.median() for a in ['serial', 'ancilla']}; q = err_ratio(d)
        rows.append(f'{NAME[fam]} & {E} & {share(d, "serial")} & {share(d, "ancilla")} & {share(d, "parallel2")} & '
                    f'{r2["serial"]:.4f} & {r2["ancilla"]:.4f} & {q[0]:.2f} [{q[1]:.2f}, {q[2]:.2f}] & {q[3]:.2f} \\\\')
(OUT / 'tab_real.tex').write_text('\n'.join(rows + [r'\bottomrule', r'\end{tabular}']) + '\n')

# Table: screen
if Path('data/screening_results.csv').exists():
    SC = pd.read_csv('data/screening_results.csv'); s = SC[SC.status == 'screened'].sort_values('series')
    rows = [r'\begin{tabular}{lrcccccc}\toprule',
            r'series (Rdatasets) & length & $R^2_{16}$ & $R^2_{24}$ & $R^2_{32}$ & $R^2_{32}-R^2_{16}$ & $\sup|f_{32}|$ & passes \\\midrule']
    for _, r in s.iterrows():
        name = r.series.split(' (')[0].replace('_', r'\_')
        rows.append(f'\\texttt{{{name}}} & {int(r.n_total)} & ${r.R2_E16:.3f}$ & ${r.R2_E24:.3f}$ & ${r.R2_E32:.3f}$ & ${r.gain_16_32:+.3f}$ & '
                    f'{r.sup_fit_E32:.2f} & {"yes" if r["pass"] else ""} \\\\')
    (OUT / 'tab_screen.tex').write_text('\n'.join(rows + [r'\bottomrule', r'\end{tabular}']) + '\n')
else: print('data/screening_results.csv not found: tab_screen.tex not written')

# Table: selected learning rates (data)
lr = E_.drop_duplicates(['family', 'E', 'arm'])
rows = [r'\begin{tabular}{llccc}\toprule', r'target & $E$ & serial & ancilla & par.\,2 \\\midrule']
for fam in ['flat', 'bump', 'gasprice', 'ibmclose', 'nottem']:
    for E in sorted(lr[lr.family == fam].E.unique()):
        cell = lambda a: (lambda r: f'{r.lr:g}' + ('$^\\dagger$' if r.plateau_at_edge else ''))(lr[(lr.family == fam) & (lr.E == E) & (lr.arm == a)].iloc[0])
        rows.append(f'{NAME.get(fam, fam)} & {E} & {cell("serial")} & {cell("ancilla")} & {cell("parallel2")} \\\\')
(OUT / 'tab_lr_data.tex').write_text('\n'.join(rows + [r'\bottomrule', r'\end{tabular}']) + '\n')

# Robustness tables of NB2 (cells 2b and 2d); each is written only if its result files exist
if (R / 'ext_selection.csv').exists() and (R / 'eval_bracketed.csv').exists():
    # Table: learning rates after bracketing the grid; runs at the optimum, serial | ancilla, under tuned and bracketed rates
    SEL, BRK = pd.read_csv(R / 'ext_selection.csv'), pd.read_csv(R / 'eval_bracketed.csv')
    def lr_cell(fam, E, a):
        s = SEL[(SEL.family == fam) & (SEL.E == E) & (SEL.arm == a)]
        if not len(s): return r'\textemdash'
        s = s.iloc[0]; txt = f'{s.lr_tuned:g}' if np.isclose(s.lr_tuned, s.lr_bracketed) else f'{s.lr_tuned:g}$\\to${s.lr_bracketed:g}'
        return txt + ('$^\\ast$' if s.saturated else ('$^\\dagger$' if s.still_at_edge else ''))
    pair = lambda d: f'{share(d, "serial")} $|$ {share(d, "ancilla")}'
    rows = [r'\begin{tabular}{llccccc}\toprule',
            r' & & \multicolumn{3}{c}{peak rate (tuned $\to$ bracketed)} & \multicolumn{2}{c}{runs at the optimum, serial $|$ ancilla} \\',
            r'\cmidrule(lr){3-5}\cmidrule(lr){6-7}', r'target & $E$ & serial & ancilla & par.\,2 & tuned & bracketed \\\midrule']
    for fam in ['flat', 'bump', 'gasprice', 'ibmclose', 'nottem']:
        for E in sorted(SEL[SEL.family == fam].E.unique()):
            sel = lambda D: D[(D.family == fam) & (D.E == E)]
            rows.append(f'{NAME.get(fam, fam)} & {E} & ' + ' & '.join(lr_cell(fam, E, a) for a in ARMS) + f' & {pair(sel(E_))} & {pair(sel(BRK))} \\\\')
    (OUT / 'tab_lr_ext.tex').write_text('\n'.join(rows + [r'\bottomrule', r'\end{tabular}']) + '\n')
if (R / 'budget_rates.csv').exists():
    # Table: step budget. Runs at the optimum out of n, serial | ancilla, per schedule; ancilla - serial [Newcombe 95%] for the held schedule
    BR = pd.read_csv(R / 'budget_rates.csv'); BR = BR[BR.thr == THR]
    assert len(BR), f'budget_rates.csv has no rows for thr = {THR}: add it to BUDGET_THR in cell 2d of NB2'
    scheds = [s for s in ('1x', '4x held', '4x stretched') if s in set(BR.schedule)]; lab = lambda s: s.replace('x', r'$\times$', 1)
    ref = '4x held' if '4x held' in scheds else scheds[-1]
    rows = [r'\begin{tabular}{ll' + 'c' * len(scheds) + r'c}\toprule',
            r' & & \multicolumn{' + str(len(scheds)) + r'}{c}{runs at the optimum, serial $|$ ancilla} & ancilla$-$serial [95\%] \\',
            r'\cmidrule(lr){3-' + str(2 + len(scheds)) + '}',
            r'target & $E$ & ' + ' & '.join(lab(s) for s in scheds) + ' & ' + lab(ref) + r' \\\midrule']
    for (fam, E), b in BR.groupby(['family', 'E'], sort=False):
        q = {s: b[b.schedule == s].iloc[0] for s in scheds if len(b[b.schedule == s])}; h = q[ref]
        rows.append(f'{NAME.get(fam, fam)} & {int(E)} & ' + ' & '.join(f'{int(q[s].k_serial)}/{int(q[s].n_serial)} $|$ {int(q[s].k_ancilla)}/{int(q[s].n_ancilla)}' if s in q else r'\textemdash'
                                                                      for s in scheds) + f' & {h["diff"]:+.2f} [{h.lo:+.2f}, {h.hi:+.2f}] \\\\')
    (OUT / 'tab_budget.tex').write_text('\n'.join(rows + [r'\bottomrule', r'\end{tabular}']) + '\n')
# Table: Levenberg-Marquardt on the runs of cell 2 (NB2, cell 3; attribution.csv), next to Adam. Written if the file exists;
# a configuration that has not been run with Levenberg-Marquardt shows a dash.
if (R / 'attribution.csv').exists():
    A_ = pd.read_csv(R / 'attribution.csv'); A_ = A_[A_['mode'] == 'lm']
    cell = lambda d, a: share(d, a) if len(d[d.arm == a]) else r'\textemdash'
    def lm_diff(d):
        if not (len(d[d.arm == 'serial']) and len(d[d.arm == 'ancilla'])): return r'\textemdash'
        return diff_cell(d)
    rows = [r'\begin{tabular}{llccccccc}\toprule',
            r' & & \multicolumn{3}{c}{Adam} & \multicolumn{3}{c}{Levenberg--Marquardt} & ancilla$-$serial \\',
            r'\cmidrule(lr){3-5}\cmidrule(lr){6-8}',
            r'target & $E$ & serial & ancilla & par.\,2 & serial & ancilla & par.\,2 & Levenberg--Marquardt [95\%] \\\midrule']
    fams = [f for f in ['flat', 'bump', 'gasprice', 'ibmclose', 'nottem'] if f in set(E_.family)]
    for fam in fams:
        for E in sorted(E_[E_.family == fam].E.unique()):
            d, l = E_[(E_.family == fam) & (E_.E == E)], A_[(A_.family == fam) & (A_.E == E)]
            rows.append(f'{NAME[fam]} & {E} & ' + ' & '.join(cell(d, a) for a in ARMS) + ' & ' + ' & '.join(cell(l, a) for a in ARMS) + f' & {lm_diff(l)} \\\\')
        rows.append(r'\midrule' if fam != fams[-1] else r'\bottomrule')
    (OUT / 'tab_lm_data.tex').write_text('\n'.join(rows + [r'\end{tabular}']) + '\n')
    n_lm = A_.groupby(['family', 'E', 'arm']).size()
    T = ['Levenberg-Marquardt on data (attribution.csv): configurations ' + str(len(n_lm)) + ', runs per configuration ' + str(sorted(set(n_lm)))]
    for fam in fams:
        for E in sorted(A_[A_.family == fam].E.unique()):
            l = A_[(A_.family == fam) & (A_.E == E)]
            T.append(f'  {TNAME.get(fam, NAME[fam])} E={E}: ' + ', '.join(f'{a} {reach(l, a)[0]}/{reach(l, a)[1]}' for a in ARMS if len(l[l.arm == a])))
    m = E_.merge(A_, on=['arm', 'family', 'E', 'run'], suffixes=('_adam', '_lm')); m = m[m.arm == 'serial']
    ad, lm = m.lexc_adam <= THR, m.lexc_lm <= THR
    T.append(f'serial runs with both optimisers: {len(m)}; Adam at the optimum in {ad.sum()}, LM in {(ad & lm).sum()} of these and in {(~ad & lm).sum()} of the other {(~ad).sum()}')
    (OUT / 'data_text_numbers.txt').write_text('\n'.join(T) + '\n')
    # Table: held-out error of the serial circuit relative to the control, under Adam and under Levenberg-Marquardt (same runs).
    # Ratio (1 - R^2 serial) / (1 - R^2 ancilla), paired by run index as in tab_real (for the real series the pairing is arbitrary,
    # the data are the same): median [10%, 90%], and the share of serial runs more than 5% worse than the paired control run.
    def ratio_cells(d):
        if not (len(d[d.arm == 'serial']) and len(d[d.arm == 'ancilla'])): return [r'\textemdash'] * 2
        a = d[d.arm == 'ancilla'].set_index('run').test_R2; s_ = d[d.arm == 'serial'].set_index('run').test_R2
        r = ((1 - s_) / (1 - a)).dropna()
        return ['{:.2f} [{:.2f}, {:.2f}]'.format(r.median(), r.quantile(.1), r.quantile(.9)), f'{(r > 1.05).mean():.2f}']
    rows = [r'\begin{tabular}{llcccccc}\toprule',
            r' & & \multicolumn{3}{c}{Adam} & \multicolumn{3}{c}{Levenberg--Marquardt} \\',
            r'\cmidrule(lr){3-5}\cmidrule(lr){6-8}',
            r'target & $E$ & at optimum & error ratio [10\%, 90\%] & $>5\%$ worse & at optimum & error ratio [10\%, 90\%] & $>5\%$ worse \\\midrule']
    fh = [f for f in ['bump', 'gasprice', 'ibmclose', 'nottem'] if f in set(E_.family)]
    for fam in fh:
        for E in sorted(E_[E_.family == fam].E.unique()):
            d, l = E_[(E_.family == fam) & (E_.E == E)], A_[(A_.family == fam) & (A_.E == E)]
            rows.append(f'{NAME[fam]} & {E} & {cell(d, "serial")} & ' + ' & '.join(ratio_cells(d)) + f' & {cell(l, "serial")} & '
                        + ' & '.join(ratio_cells(l)) + r' \\')
        rows.append(r'\midrule' if fam != fh[-1] else r'\bottomrule')
    (OUT / 'tab_heldout.tex').write_text('\n'.join(rows + [r'\end{tabular}']) + '\n')
print('written:', sorted(p.name for p in OUT.glob('*.tex')))
