"""Shared core for the two paper notebooks: circuits on the group, targets, optimisers, statistics.

Circuits: U_L S(x) ... S(x) U_0 |0>, readout Z on the last wire, S(x) = tensor_w RX(x)^{e_w}.
Each block U_l is a product of `tbl` general SU(2^nq) gates. Parameters are the gates themselves (no chart):
gradients are taken in the right-trivialised Lie algebra (Pauli-word generators, operator norm 1) and updates are
U <- U exp(i th.P). Everything is float64 / complex128.
"""
import itertools
import numpy as np
import jax, jax.numpy as jnp
jax.config.update('jax_enable_x64', True)

ARMS = {  # nq qubits, encoding mask, L = E // div
    'serial':    dict(nq=1, enc=(1,),         div=1),
    'ancilla':   dict(nq=2, enc=(1, 0),       div=1),
    'parallel2': dict(nq=2, enc=(1, 1),       div=2),
    'parallel4': dict(nq=4, enc=(1, 1, 1, 1), div=4),
}
_P1 = [np.eye(2), np.array([[0, 1], [1, 0]]), np.array([[0, -1j], [1j, 0]]), np.diag([1., -1.])]

def paulis(nq):
    out = []
    for w in itertools.product(range(4), repeat=nq):
        if any(w):
            M = np.array([[1.]])
            for k in w: M = np.kron(M, _P1[k])
            out.append(M)
    return np.array(out, dtype=complex)

def rx_layer(X, enc):
    def one(x):
        r = jnp.array([[jnp.cos(x / 2), -1j * jnp.sin(x / 2)], [-1j * jnp.sin(x / 2), jnp.cos(x / 2)]]); M = jnp.array([[1. + 0j]])
        for e in enc: M = jnp.kron(M, r if e else jnp.eye(2, dtype=complex))
        return M
    return jax.vmap(one)(X)

def expi(h):
    """exp(i h) for Hermitian h via eigh (exact, unitary by construction). Not differentiated through."""
    w, Q = jnp.linalg.eigh(h); return (Q * jnp.exp(1j * w)) @ Q.conj().T

def haar(d, rng):
    Z = (rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))) / np.sqrt(2)
    Q, R = np.linalg.qr(Z); Q = Q * (np.diag(R) / np.abs(np.diag(R))); return Q / np.linalg.det(Q) ** (1 / d)

class Circuit:
    """All operations for one (arm, E, tbl). Us has shape (L+1, tbl, d, d)."""
    def __init__(self, arm, E, tbl=1):
        a = ARMS[arm]; self.arm, self.E, self.tbl = arm, E, tbl
        self.nq, self.enc, self.L, self.d = a['nq'], a['enc'], E // a['div'], 2 ** a['nq']
        self.P = jnp.asarray(paulis(self.nq)); self.nP = self.P.shape[0]; self.nparam = (self.L + 1) * tbl * self.nP
        self.z = jnp.asarray([1. if b % 2 == 0 else -1. for b in range(self.d)])       # Z on the last wire
        P, z, enc, tb, nP, L = self.P, self.z, self.enc, tbl, self.nP, self.L
        def f(Us, X):
            RX = rx_layer(X, enc); psi = jnp.zeros((X.shape[0], self.d), complex).at[:, 0].set(1.)
            for t in range(tb): psi = psi @ Us[0, t].T
            def layer(p, Ul):
                p = jnp.einsum('nab,nb->na', RX, p)
                for t in range(tb): p = p @ Ul[t].T
                return p, None
            psi, _ = jax.lax.scan(layer, psi, Us[1:])
            return jnp.real(jnp.sum(jnp.abs(psi) ** 2 * z, axis=1))
        def pert(Us, th): return Us + 1j * Us @ jnp.einsum('ltk,kab->ltab', th, P)       # U (I + i th.P): exact to first order
        def loss(Us, X, y, V): return jnp.mean((f(Us, X) - y) ** 2) / V
        def grad(Us, X, y, V): return jax.grad(lambda th: loss(pert(Us, th), X, y, V))(jnp.zeros((L + 1, tb, nP)))
        def jac(Us, X, y):                                                              # residual Jacobian (n, nparam)
            return jax.jacfwd(lambda th: f(pert(Us, th.reshape(L + 1, tb, nP)), X) - y)(jnp.zeros(self.nparam))
        def step(Us, th): return Us @ jax.vmap(jax.vmap(expi))(jnp.einsum('ltk,kab->ltab', th, P))
        self.f, self.loss, self.grad, self.jac, self.step = f, loss, grad, jac, step
        self.jf, self.jloss, self.jgrad, self.jjac, self.jstep = map(jax.jit, (f, loss, grad, jac, step))
    def init(self, seed):
        rng = np.random.default_rng(seed)
        return jnp.asarray(np.array([[haar(self.d, rng) for _ in range(self.tbl)] for _ in range(self.L + 1)]))

def check_definition(arm, E, tbl=1, seed=0, tol=1e-12):
    """Compare the simulator with a direct dense-matrix evaluation of the circuit definition (numpy/scipy only)."""
    from scipy.linalg import expm
    c = Circuit(arm, E, tbl); Us = np.asarray(c.init(seed)); X = np.linspace(-3, 3, 7)
    X1 = np.array([[0, 1], [1, 0]]); Z = np.diag([1., -1.]); I2 = np.eye(2)
    out = []
    for x in X:
        S = np.array([[1.]])
        for e in c.enc: S = np.kron(S, expm(-1j * x / 2 * X1) if e else I2)
        M = np.eye(c.d, dtype=complex)
        for t in range(tbl): M = Us[0, t] @ M
        for l in range(1, c.L + 1):
            M = S @ M
            for t in range(tbl): M = Us[l, t] @ M
        O = np.array([[1.]])
        for w in range(c.nq): O = np.kron(O, Z if w == c.nq - 1 else I2)
        psi = M[:, 0]; out.append(np.real(psi.conj() @ O @ psi))
    err = float(np.max(np.abs(np.array(out) - np.asarray(c.jf(jnp.asarray(Us), jnp.asarray(X))))))
    assert err < tol, (arm, err); return err

def check_gradient(c, X, y, V, seed=1, h=1e-6):
    """Lie gradient vs central finite difference along a random Lie direction."""
    Us = c.init(seed); g = c.jgrad(Us, X, y, V); D = np.random.default_rng(seed).standard_normal(g.shape)
    fd = (float(c.jloss(c.jstep(Us, h * D), X, y, V)) - float(c.jloss(c.jstep(Us, -h * D), X, y, V))) / (2 * h)
    an = float(jnp.sum(g * D)); assert abs(an - fd) < 1e-6 * max(1, abs(fd)), (an, fd); return an, fd

# ── targets ──────────────────────────────────────────────────────────────────
XD = np.linspace(-np.pi, np.pi, 8192, endpoint=False)
def trig_basis(x, E):
    k = np.arange(1, E + 1); return np.hstack([np.ones((len(x), 1)), np.cos(np.outer(x, k)), np.sin(np.outer(x, k))])
def random_target(family, E, seed, amp):
    """flat: degree-E polynomial, N(0,1) coefficients; decay: coefficients N(0,1)/k; bump: three Poisson kernels with
    geometric Fourier tail r^|k|, r^E = 0.05 (not representable at degree E). Scaled so that sup|y| = amp on a dense grid."""
    rng = np.random.default_rng(seed)
    if family in ('flat', 'decay'):
        k = np.arange(1, E + 1); w = np.ones(E) if family == 'flat' else 1 / k
        c0, a, b = rng.standard_normal(), w * rng.standard_normal(E), w * rng.standard_normal(E)
        g = lambda x: c0 + (a[:, None] * np.cos(np.outer(k, x)) + b[:, None] * np.sin(np.outer(k, x))).sum(0)
    elif family == 'bump':
        r = 0.05 ** (1 / E); ph = rng.uniform(-np.pi, np.pi, 3); sg = rng.choice([-1, 1], 3) * rng.uniform(0.5, 1, 3)
        g = lambda x: sum(s * (1 - r ** 2) / (1 - 2 * r * np.cos(x - p) + r ** 2) for s, p in zip(sg, ph))
    else: raise ValueError(family)
    gd = g(XD); m = (gd.max() + gd.min()) / 2; s = amp / np.max(np.abs(gd - m))
    return lambda x: s * (g(x) - m)

def ls_oracle(E, x, y):
    """Least-squares fit over real trig polynomials of degree <= E; returns (coefficients, train MSE, sup of the fit)."""
    B = trig_basis(x, E); c, *_ = np.linalg.lstsq(B, y, rcond=None)
    return c, float(np.mean((B @ c - y) ** 2)), float(np.max(np.abs(trig_basis(XD, E) @ c)))

# ── optimisers (vectorised over runs) ────────────────────────────────────────
def gd_armijo(c, U0, X, Y, V, iters, chunk=500, ck=(), freeze=1e-14, armijo=1e-4):
    """Riemannian gradient descent with Armijo backtracking (step doubles as the first trial). No learning rate.
    Returns loss history (runs, iters+1) and unitaries at the checkpoint iterations."""
    J0 = jax.vmap(lambda U, y: c.jac(U, X, y))(U0, Y)
    lam = 2 * jax.vmap(lambda J: jnp.linalg.svd(J, compute_uv=False)[0])(J0) ** 2 / (X.shape[0] * V)
    def one(state, _):
        Us, eta, Lc, y, v = state
        g = c.grad(Us, X, y, v); gn2 = jnp.sum(g ** 2); active = Lc > freeze
        def cond(s): e, Ln = s; return (Ln > Lc - armijo * e * gn2) & (e > 1e-30)
        def body(s): e, _ = s; e = e / 2; return e, c.loss(c.step(Us, -e * g), X, y, v)
        e0 = 2.0 * eta; e, Ln = jax.lax.while_loop(cond, body, (e0, c.loss(c.step(Us, -e0 * g), X, y, v)))
        ok = active & (e > 1e-30) & (Ln <= Lc - armijo * e * gn2)
        return (jnp.where(ok, c.step(Us, -e * g), Us), jnp.where(ok, e, eta), jnp.where(ok, Ln, Lc), y, v), jnp.where(ok, Ln, Lc)
    @jax.jit
    def run_chunk(Us, eta, Lc, Y, V):
        return jax.vmap(lambda Us, eta, Lc, y, v: (lambda s, h: (s[:3], h))(*jax.lax.scan(one, (Us, eta, Lc, y, v), None, length=chunk)))(Us, eta, Lc, Y, V)
    Us, eta, Lc = U0, 1.0 / lam, jax.vmap(lambda U, y, v: c.loss(U, X, y, v))(U0, Y, V)
    H, snaps = [np.asarray(Lc)[:, None]], {0: np.asarray(U0)}
    for k in range(iters // chunk):
        (Us, eta, Lc), h = run_chunk(Us, eta, Lc, Y, V); H.append(np.asarray(h))
        if (k + 1) * chunk in ck: snaps[(k + 1) * chunk] = np.asarray(Us)
        if bool(jnp.all(Lc <= freeze)):
            for kk in [x for x in ck if x > (k + 1) * chunk]: snaps[kk] = np.asarray(Us)
            break
    H = np.concatenate(H, 1)
    if H.shape[1] < iters + 1: H = np.concatenate([H, np.repeat(H[:, -1:], iters + 1 - H.shape[1], 1)], 1)   # frozen runs keep their loss
    return H, snaps

def lm_svd(c, U0, X, Y, V, iters, freeze=1e-14):
    """Levenberg-Marquardt on the group; the linear system is solved via the SVD of J (the condition number is not squared).
    Returns loss history (runs, iters) and final unitaries."""
    def one(state, _):
        Us, lamd, Lc, y, v = state
        r = c.f(Us, X) - y; J = c.jac(Us, X, y); Uj, s, Vt = jnp.linalg.svd(J, full_matrices=False)
        th = -(Vt.T @ ((s / (s ** 2 + lamd * s[0] ** 2)) * (Uj.T @ r))).reshape(c.L + 1, c.tbl, c.nP)
        Un = c.step(Us, th); Ln = c.loss(Un, X, y, v); ok = (Ln < Lc) & (Lc > freeze)
        return (jnp.where(ok, Un, Us), jnp.clip(jnp.where(ok, lamd * 0.3, lamd * 5.0), 1e-15, 1e8), jnp.where(ok, Ln, Lc), y, v), jnp.where(ok, Ln, Lc)
    @jax.jit
    def run(U0, Y, V):
        def per(Us, y, v):
            s, h = jax.lax.scan(one, (Us, 1e-3, c.loss(Us, X, y, v), y, v), None, length=iters); return s[0], h
        return jax.vmap(per)(U0, Y, V)
    UF, H = run(U0, Y, V); return np.asarray(H), UF

def adam(c, U0, X, Y, V, lr, iters, batch=None, key=None, chunk=500, b1=0.9, b2=0.999, eps=1e-12, hold=0):
    """Adam on the right-trivialised Lie-algebra coordinates, cosine schedule lr -> lr/100.
    hold > 0: the rate stays at lr for the first `hold` steps and then follows the cosine schedule over the remaining iters - hold steps.
    batch=None: full batch; otherwise minibatches of that size drawn from X (per run). Returns full-X loss per chunk (runs, iters//chunk+1)
    and final unitaries. Every run always completes the full schedule and is scored at its end. (An earlier version stopped all runs
    once all were below 1e-14 at a chunk boundary; since Adam's normalised steps do not vanish at an optimum, runs pass through
    low losses and are kicked out again, so that rule caught transient dips with 5 tuning runs but almost never with 100 evaluation
    runs, and tuning and evaluation measured different things.)"""
    n = X.shape[0]; key = jax.random.PRNGKey(0) if key is None else key
    def one(state, k):
        Us, m, v2, kk, y, vv = state
        if batch is None: g = c.grad(Us, X, y, vv)
        else:
            kk, sub = jax.random.split(kk); idx = jax.random.randint(sub, (batch,), 0, n); g = c.grad(Us, X[idx], y[idx], vv)
        m = b1 * m + (1 - b1) * g; v2 = b2 * v2 + (1 - b2) * g ** 2; t = k + 1.0
        if hold: lr_t = lr * (0.01 + 0.99 * 0.5 * (1 + jnp.cos(jnp.pi * jnp.maximum(k - hold, 0.0) / (iters - hold))))   # constant for `hold` steps, then the same decay
        else: lr_t = lr * (0.01 + 0.99 * 0.5 * (1 + jnp.cos(jnp.pi * k / iters)))
        return (c.step(Us, -lr_t * (m / (1 - b1 ** t)) / (jnp.sqrt(v2 / (1 - b2 ** t)) + eps)), m, v2, kk, y, vv), None
    @jax.jit
    def run_chunk(Us, m, v2, keys, Y, V, k0):
        def per(Us, m, v2, kk, y, vv):
            s, _ = jax.lax.scan(one, (Us, m, v2, kk, y, vv), k0 + jnp.arange(chunk, dtype=float)); return s[:4], c.loss(s[0], X, y, vv)
        return jax.vmap(per)(Us, m, v2, keys, Y, V)
    R = U0.shape[0]; m = jnp.zeros((R, c.L + 1, c.tbl, c.nP)); v2 = jnp.zeros_like(m); keys = jax.random.split(key, R)
    Us = U0; H = [np.asarray(jax.vmap(lambda U, y, v: c.loss(U, X, y, v))(U0, Y, V))[:, None]]
    for k in range(iters // chunk):
        (Us, m, v2, keys), l = run_chunk(Us, m, v2, keys, Y, V, float(k * chunk)); H.append(np.asarray(l)[:, None])
    return np.concatenate(H, 1), Us

def plateau_centre(scores, tol=0.25):
    """scores: {lr: q75 of log10 loss}. Near-best plateau (within tol decades), pick the rate closest to its geometric centre."""
    best = min(scores.values()); pl = sorted(k for k, v in scores.items() if v <= best + tol)
    c = (np.log10(pl[0]) + np.log10(pl[-1])) / 2; return min(pl, key=lambda k: abs(np.log10(k) - c)), pl

# ── statistics ───────────────────────────────────────────────────────────────
def wilson(k, n, z=1.959964):
    if n == 0: return (np.nan, np.nan)
    p = k / n; den = 1 + z * z / n; c = (p + z * z / (2 * n)) / den; h = z * np.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / den
    return (c - h, c + h)
def newcombe(k1, n1, k2, n2):
    """95% CI for p1 - p2 (Newcombe 1998, hybrid Wilson score)."""
    p1, p2 = k1 / n1, k2 / n2; l1, u1 = wilson(k1, n1); l2, u2 = wilson(k2, n2); d = p1 - p2
    return d, d - np.sqrt((p1 - l1) ** 2 + (u2 - p2) ** 2), d + np.sqrt((u1 - p1) ** 2 + (p2 - l2) ** 2)
def hl_shift(a, b, B=2000, seed=0):
    """Hodges-Lehmann shift a - b (median of pairwise differences) with a 95% percentile-bootstrap CI (independent runs)."""
    a, b = np.asarray(a), np.asarray(b); est = np.median(np.subtract.outer(a, b)); rng = np.random.default_rng(seed)
    bs = [np.median(np.subtract.outer(rng.choice(a, len(a)), rng.choice(b, len(b)))) for _ in range(B)]
    return float(est), float(np.quantile(bs, .025)), float(np.quantile(bs, .975))
