"""Tables for Section 5 and Appendix D from the NB1 result files (results/nb1/*.csv). Run from the project folder
(python tables_exact.py). Writes tables/tab_contrast.tex, tab_rates_exact.tex, tab_gd_budget.tex, tab_ordering.tex, tab_lm_failures.tex, tab_lr_exact.tex.

A run converges if its final loss (relative to the target variance) is <= EPS = 1e-6, the definition of Section 6.
The threshold fixed before the runs was 1e-8; it was changed after them, because Adam leaves converged runs at about
1e-9 to 1e-12, so that 1e-8 touches converged runs and 1e-10 cuts through them. tab_rates_exact.tex gives the counts
for 1e-4, 1e-6, 1e-8 and 1e-10; which differences are significant at each of them is written to
tables/exact_text_numbers.txt. Gradient descent and Levenberg-Marquardt stop below 1e-14, and their counts hardly
depend on the threshold.

Everything is computed from the run files; from the summaries of the notebook only g3_ordering_strict.csv is read
(it does not depend on EPS). The numbers quoted in the text of Section 5 that are in no table are written to
tables/exact_text_numbers.txt."""
from pathlib import Path
import numpy as np, pandas as pd

R, OUT = Path('results/nb1'), Path('tables'); OUT.mkdir(exist_ok=True)
EPS, THRS, ARMS, FAMS, STALL, TAU = 1e-6, (1e-4, 1e-6, 1e-8, 1e-10), ['serial', 'ancilla', 'parallel2'], ['flat', 'decay'], 0.01, '1e-08'
RUNS = {'GD': pd.read_csv(R / 'runs_gd.csv'), 'Adam': pd.read_csv(R / 'runs_adam.csv'), 'LM': pd.read_csv(R / 'runs_lm.csv')}
ES = sorted(RUNS['GD'].E.unique())
LABEL = {'GD': 'gradient descent', 'Adam': 'Adam', 'LM': 'Levenberg--Marquardt'}
SHORT = {'GD': 'GD', 'Adam': 'Adam', 'LM': 'LM'}
FAMNAME = {'flat': 'flat', 'decay': '$1/k$'}          # names of the target families as in the text of the paper

def wilson(k, n, z=1.959964):
    p = k / n; den = 1 + z * z / n; c = (p + z * z / (2 * n)) / den; h = z * np.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / den
    return c - h, c + h
def newcombe(k1, n1, k2, n2):
    """95% interval for p1 - p2 (Newcombe 1998, hybrid Wilson score); as in phaselock_core"""
    p1, p2 = k1 / n1, k2 / n2; l1, u1 = wilson(k1, n1); l2, u2 = wilson(k2, n2); d = p1 - p2
    return d, d - np.sqrt((p1 - l1) ** 2 + (u2 - p2) ** 2), d + np.sqrt((u1 - p1) ** 2 + (p2 - l2) ** 2)
def kn(D, arm, fam, E, thr=EPS):
    """(runs with final loss <= thr, runs)"""
    x = D[(D.arm == arm) & (D.family == fam) & (D.E == E)].final_loss; return int((x <= thr).sum()), len(x)
def expo(t): return f'$10^{{{int(round(np.log10(t)))}}}$'
def write(name, rows): (OUT / name).write_text('\n'.join(rows) + '\n'); print('wrote', OUT / name)

# Table (main text): runs converged, serial | ancilla, and ancilla - serial, per target family, E and optimiser
OPTS = ['GD', 'LM', 'Adam']                     # order of Sections 5.1, 5.3, 5.4, in every table; figures.ipynb uses the same order
rows = [r'\begin{tabular}{ll' + 'cc' * len(OPTS) + r'}\toprule',
        ' & & ' + ' & '.join(r'\multicolumn{2}{c}{' + LABEL[o] + '}' for o in OPTS) + r' \\' + ''.join(rf'\cmidrule(lr){{{3 + 2 * i}-{4 + 2 * i}}}' for i in range(len(OPTS))),
        r'targets & $E$ & ' + ' & '.join([r'runs & difference [95\%]'] * len(OPTS)) + r' \\\midrule']
for fam in FAMS:
    for E in ES:
        cells = []
        for opt in OPTS:
            (ka, na), (ks, ns) = kn(RUNS[opt], 'ancilla', fam, E), kn(RUNS[opt], 'serial', fam, E); d, lo, hi = newcombe(ka, na, ks, ns)
            cells += [f'{ks} $|$ {ka}', f'${d:+.2f}$ [${lo:+.2f}$, ${hi:+.2f}$]' + ('' if max(ka / na, ks / ns) >= 0.5 else r'$^\ast$')]
        rows.append((FAMNAME[fam] if E == ES[0] else '') + f' & {E} & ' + ' & '.join(cells) + r' \\')
    rows.append(r'\midrule' if fam == FAMS[0] else r'\bottomrule')
write('tab_contrast.tex', rows + [r'\end{tabular}'])

# Table: runs below the threshold, serial | ancilla | parallel, for four thresholds
rows = [r'\begin{tabular}{lll' + 'c' * len(ES) + r'}\toprule', r'optimiser & targets & threshold & ' + ' & '.join(f'$E={E}$' for E in ES) + r' \\\midrule']
for opt in OPTS:
    for fam in FAMS:
        for thr in THRS:
            cells = [' $|$ '.join(str(kn(RUNS[opt], a, fam, E, thr)[0]) for a in ARMS) for E in ES]
            rows.append((SHORT[opt] if (fam, thr) == (FAMS[0], THRS[0]) else '') + ' & ' + (FAMNAME[fam] if thr == THRS[0] else '') + f' & {expo(thr)} & ' + ' & '.join(cells) + r' \\')
        rows.append(r'\cmidrule(l){2-' + str(3 + len(ES)) + '}' if fam == FAMS[0] else (r'\midrule' if opt != OPTS[-1] else r'\bottomrule'))
write('tab_rates_exact.tex', rows + [r'\end{tabular}'])

# Table: gradient descent, runs with loss <= EPS at four checkpoints (kappa.csv holds the loss at the checkpoints; the
# loss decreases monotonically)
G, KP = RUNS['GD'], pd.read_csv(R / 'kappa.csv'); CKS = [7500, 14500, 27000, 50000]
rows = [r'\begin{tabular}{ll' + 'c' * (2 * len(CKS)) + r'}\toprule',
        r' & & \multicolumn{' + str(len(CKS)) + r'}{c}{serial} & \multicolumn{' + str(len(CKS)) + r'}{c}{ancilla} \\'
        + rf'\cmidrule(lr){{3-{2 + len(CKS)}}}\cmidrule(lr){{{3 + len(CKS)}-{2 + 2 * len(CKS)}}}',
        r'targets & $E$ & ' + ' & '.join([' & '.join(f'{c:,}'.replace(',', '{,}') for c in CKS)] * 2) + r' \\\midrule']
for fam in FAMS:
    for E in ES:
        cells = []
        for a in ['serial', 'ancilla']:
            kk = KP[(KP.arm == a) & (KP.family == fam) & (KP.E == E)]
            cells += [str(int((kk[kk.iter == c].loss <= EPS).sum())) for c in CKS]
        rows.append((FAMNAME[fam] if E == ES[0] else '') + f' & {E} & ' + ' & '.join(cells) + r' \\')
    rows.append(r'\midrule' if fam == FAMS[0] else r'\bottomrule')
write('tab_gd_budget.tex', rows + [r'\end{tabular}'])

# Table: order of "kappa_J above the threshold" and "loss <= 1e-4" along gradient descent (cell 5b of NB1), pooled over configurations
S = pd.read_csv(R / 'g3_ordering_strict.csv'); CATS = ['kappa_at_init', 'kappa_first', 'unresolved', 'loss_first', 'loss_only', 'kappa_only', 'neither']
P = S.groupby(['thr', 'arm'])[CATS].sum()
rows = [r'\begin{tabular}{llccccccc}\toprule',
        r' & & \multicolumn{5}{c}{loss reaches $10^{-4}$} & \multicolumn{2}{c}{loss does not reach $10^{-4}$} \\\cmidrule(lr){3-7}\cmidrule(lr){8-9}',
        r'threshold & circuit & above at start & $\kappa_J$ first & same interval & loss first & never above & above later & never above \\\midrule']
for thr in sorted(P.index.get_level_values(0).unique(), reverse=True):
    for a in ARMS:
        p = P.loc[(thr, a)]
        rows.append((expo(thr) if a == ARMS[0] else '') + f' & {a.replace("parallel2", "parallel")} & ' + ' & '.join(str(int(p[c])) for c in CATS) + r' \\')
    rows.append(r'\midrule' if thr != P.index.get_level_values(0).min() else r'\bottomrule')
write('tab_ordering.tex', rows + [r'\end{tabular}'])

# Table: end points of Levenberg-Marquardt runs that do not converge (cell 3b of NB1)
L = pd.read_csv(R / 'lm_endpoints.csv'); e, ini = L[L.point == 'end'], L[L.point == 'init']; med = lambda v: f'${np.median(v):.1f}$'
rows = [r'\begin{tabular}{llcccccccccc}\toprule',
        r' & & & & \multicolumn{3}{c}{$\sigma_i\le10^{-8}\sigma_1$ at the end point} & & \multicolumn{3}{c}{$\log_{10}\sigma_{\min}/\sigma_1$} & \\\cmidrule(lr){5-7}\cmidrule(lr){9-11}',
        r'targets & $E$ & failed & stalled & any & two & share $\ge0.99$ & $\log_{10}$ gradient & failed & converged & initial & $n_{\rm init}$ \\\midrule']
tot = np.zeros(5, int)
for fam in FAMS:
    for E in ES:
        d, i0 = e[(e.arm == 'serial') & (e.family == fam) & (e.E == E)], ini[(ini.arm == 'serial') & (ini.family == fam) & (ini.E == E)]
        f, cv = d[d.final_loss > EPS], d[d.final_loss <= EPS]
        if not len(f): continue
        c = [len(f), int((f.drop_last_quarter < STALL).sum()), int((f[f'n_weak_{TAU}'] > 0).sum()), int((f[f'n_weak_{TAU}'] == 2).sum()),
             int((f[f'weak_share_{TAU}'] >= 0.99).sum())]; tot += c
        rows.append(f'{FAMNAME[fam]} & {E} & ' + ' & '.join(map(str, c)) + f' & {med(f.log_rel_grad)} & {med(f.log_smin_rel)} & {med(cv.log_smin_rel)} & {med(i0.log_smin_rel)}'
                    f' & {np.median(i0[f"n_weak_{TAU}"]):g} \\\\')
rows += [r'\midrule', 'all & & ' + ' & '.join(map(str, tot)) + r' & & & & & \\', r'\bottomrule']
write('tab_lm_failures.tex', rows + [r'\end{tabular}'])

# Table: Adam, peak rates and runs converged under the tuned, the bracketed and the common rate (cells 4, 4b of NB1)
A = RUNS['Adam']
if (R / 'adam_ext_selection.csv').exists():
    SEL = pd.read_csv(R / 'adam_ext_selection.csv'); X = pd.read_csv(R / 'runs_adam_ext.csv') if (R / 'runs_adam_ext.csv').exists() else A.iloc[:0]
    C = pd.read_csv(R / 'runs_adam_common.csv') if (R / 'runs_adam_common.csv').exists() else A.iloc[:0]
    def lr(v): return f'{1e3 * v:g}'
    rows = [r'\begin{tabular}{llccccc}\toprule',
            r' & & \multicolumn{2}{c}{tuned} & \multicolumn{2}{c}{bracketed} & common \\\cmidrule(lr){3-4}\cmidrule(lr){5-6}\cmidrule(lr){7-7}',
            r'targets & $E$ & rate ($10^{-3}$) & runs & rate ($10^{-3}$) & runs & runs \\\midrule']
    for fam in FAMS:
        for E in ES:
            t, kt, b, kb, kc = [], [], [], [], []
            for a in ARMS:
                s = SEL[(SEL.arm == a) & (SEL.family == fam) & (SEL.E == E)].iloc[0]; k0 = kn(A, a, fam, E)[0]
                t.append(lr(s.lr_tuned)); kt.append(str(k0)); b.append(lr(s.lr_bracketed) + (r'$^\dagger$' if s.still_at_edge else ''))
                kb.append(str(kn(X, a, fam, E)[0] if s.rerun else k0)); kc.append(str(k0 if np.isclose(s.lr_tuned, 1e-3) else kn(C, a, fam, E)[0]))
            j = ' $|$ '.join
            rows.append((FAMNAME[fam] if E == ES[0] else '') + f' & {E} & {j(t)} & {j(kt)} & {j(b)} & {j(kb)} & {j(kc)} \\\\')
        rows.append(r'\midrule' if fam == FAMS[0] else r'\bottomrule')
    write('tab_lr_exact.tex', rows + [r'\end{tabular}'])

# Numbers of Section 5 that are in no table
T = [f'threshold EPS = {EPS:g}']
m = RUNS['GD'].merge(RUNS['LM'], on=['arm', 'family', 'E', 'run'], suffixes=('_gd', '_lm')); m = m[m.arm == 'serial']
g, l = m.final_loss_gd <= EPS, m.final_loss_lm <= EPS
T.append(f'serial runs: GD converges in {g.sum()}, LM in {(g & l).sum()} of these and in {(~g & l).sum()} of the other {(~g).sum()}')
ma = RUNS['Adam'].merge(RUNS['LM'], on=['arm', 'family', 'E', 'run'], suffixes=('_adam', '_lm')); ma = ma[ma.arm == 'serial']
aa, ll = ma.final_loss_adam <= EPS, ma.final_loss_lm <= EPS
T.append(f'serial runs: Adam (tuned) converges in {aa.sum()}, LM in {(aa & ll).sum()} of these and in {(~aa & ll).sum()} of the other {(~aa).sum()}')
mg = RUNS['GD'].merge(RUNS['Adam'], on=['arm', 'family', 'E', 'run'], suffixes=('_gd', '_adam')); mg = mg[mg.arm == 'serial']
gg, ad = mg.final_loss_gd <= EPS, mg.final_loss_adam <= EPS
T.append(f'serial runs: GD converges in {gg.sum()}, Adam (tuned) in {(gg & ad).sum()} of these and in {(~gg & ad).sum()} of the other {(~gg).sum()}')
T.append('configurations (of %d) in which the difference ancilla - serial is significant, per threshold; in brackets those in which serial - ancilla is:' % (len(FAMS) * len(ES)))
for opt in OPTS:
    for thr in THRS:
        iv = {(fam, E): newcombe(*kn(RUNS[opt], 'ancilla', fam, E, thr), *kn(RUNS[opt], 'serial', fam, E, thr)) for fam in FAMS for E in ES}
        pos, neg = [c for c, v in iv.items() if v[1] > 0], [c for c, v in iv.items() if v[2] < 0]
        T.append(f'  {opt} {thr:g}: {len(pos)} [{len(neg)}]; not significant: ' + ', '.join(f'{FAMNAME[f].strip("$")} E={E}' for (f, E) in iv if (f, E) not in pos and (f, E) not in neg))
T.append(f'two-qubit runs under LM: {(RUNS["LM"][RUNS["LM"].arm != "serial"].final_loss <= EPS).sum()} of {(RUNS["LM"].arm != "serial").sum()} converge')
K0 = KP[KP.iter == 0].merge(G[['arm', 'family', 'E', 'run', 'final_loss']], on=['arm', 'family', 'E', 'run']); K0['conv'] = K0.final_loss <= EPS
C0 = K0.groupby(['family', 'E', 'arm']).agg(med=('log_kJ', 'median'), k=('conv', 'sum'), n=('conv', 'size')).reset_index()
T.append('median log10 kappa_J at initialisation:\n' + C0.pivot_table(index=['family', 'arm'], columns='E', values='med').round(1).to_string())
T.append('configurations of different architectures with median initial log10 kappa_J within 0.5 (share converged under GD, ancilla/parallel minus serial, Newcombe 95%):')
for fam, d in C0.groupby('family'):
    d = d.reset_index(drop=True)
    for a in range(len(d)):
        for b in range(a + 1, len(d)):
            x, y = d.iloc[a], d.iloc[b]
            if x.arm != y.arm and abs(x.med - y.med) <= 0.5:
                if y.arm == 'serial' or (x.arm != 'serial' and x.arm > y.arm): x, y = y, x
                dd, lo, hi = newcombe(int(y.k), int(y.n), int(x.k), int(x.n))
                T.append(f'  {fam}: {x.arm} E={x.E} ({x.med:.1f}; {x.k}/{x.n}) | {y.arm} E={y.E} ({y.med:.1f}; {y.k}/{y.n}) | {dd:+.2f} [{lo:+.2f}, {hi:+.2f}]')
T.append('AUC of initial kappa_J for convergence under GD, configurations with >= 5 runs of each kind [bootstrap 95%, 1000 resamples]:')
u = lambda a, b: float(((a[:, None] > b[None, :]) + 0.5 * (a[:, None] == b[None, :])).mean())
for (fam, E, arm), d in K0.groupby(['family', 'E', 'arm']):
    a, b = d[d.conv].log_kJ.values, d[~d.conv].log_kJ.values
    if len(a) >= 5 and len(b) >= 5:
        rng = np.random.default_rng(0); bs = [u(rng.choice(a, len(a)), rng.choice(b, len(b))) for _ in range(1000)]
        T.append(f'  {fam} E={E} {arm}: {u(a, b):.2f} [{np.quantile(bs, .025):.2f}, {np.quantile(bs, .975):.2f}] ({len(a)} converged, {len(b)} not)')
last = KP.sort_values('iter').groupby(['arm', 'family', 'E', 'run']).last().reset_index().merge(G[['arm', 'family', 'E', 'run', 'final_loss']], on=['arm', 'family', 'E', 'run'])
c = last[last.final_loss <= EPS].log_kJ; T.append(f'log10 kappa_J at the last checkpoint of the {len(c)} converged GD runs: {c.min():.1f} to {c.max():.1f}')
P4 = P.loc[P.index.get_level_values(0).min()]; nev = P4.loss_only + P4.neither
T.append(f'kappa_J never above 1e-4 at a checkpoint: ' + ', '.join(f'{a} {int(nev[a])}' for a in ARMS) + f'; of these {int(P4.loss_only.sum())} reach loss 1e-4')
fl = e[(e.arm == 'serial') & (e.final_loss > EPS)]; w = fl[fl[f'n_weak_{TAU}'] > 0]; o = fl[fl[f'n_weak_{TAU}'] == 0]; cv = e[(e.arm == 'serial') & (e.final_loss <= EPS)]
T.append(f'LM, {len(fl)} failed serial runs: {len(w)} with singular values <= 1e-8 sigma_1 (median log10 relative gradient {w.log_rel_grad.median():.1f}); '
         f'{len(o)} without (log10 sigma_min/sigma_1 {o.log_smin_rel.min():.1f} to {o.log_smin_rel.max():.1f}); '
         f'{len(cv)} converged end points in the same configurations, smallest log10 sigma_min/sigma_1 {cv.log_smin_rel.min():.1f}')
a6 = A[(A.arm == 'ancilla') & (A.final_loss <= EPS)]; q = np.log10(a6.final_loss).quantile([.05, .5, .95])
T.append(f'Adam, ancilla, final log10 loss of the {len(a6)} converged runs (tuned rates {sorted(a6.lr.unique())}): median {q[.5]:.1f}, 5% {q[.05]:.1f}, 95% {q[.95]:.1f}')
if (R / 'runs_adam_ext.csv').exists():
    x6 = X[(X.arm == 'ancilla') & (X.final_loss <= EPS)]
    T.append('  under the bracketed rates: ' + '; '.join(f'rate {r:g}: median {np.log10(v).median():.1f} ({len(v)} runs)' for r, v in x6.groupby('lr').final_loss))
    T.append(f'Adam tuning: {int(np.isclose(SEL.lr_tuned, SEL.lr_tuned.min()).sum())} of {len(SEL)} configurations at the smallest grid rate; '
             f'{int(SEL.extended.notna().sum())} extended, {int(SEL.rerun.sum())} selections changed, {int(SEL.still_at_edge.sum())} still at an end of the grid')
(OUT / 'exact_text_numbers.txt').write_text('\n'.join(T) + '\n'); print('wrote', OUT / 'exact_text_numbers.txt')
