"""Pre-specified screening of real 1-D series for the NB2 real-data illustration.

Question answered (classical least squares only, no circuits): does the series' least-squares fit by a real
trigonometric polynomial of degree E keep improving *held-out* R^2 up to E = 24-32? Only such series can show
whether failing to reach the least-squares optimum costs test accuracy, which is what the paper needs to test.

Protocol (fixed before any run; change nothing after seeing results):
  source      every univariate, regularly sampled time series in Rdatasets (CSV columns rownames,time,value)
              with >= MIN_LEN observations, plus any CSV the user drops into ./manual/ (one numeric column, or
              columns time,value)
  window      the last min(n, N_WINDOW) observations (series need >= MIN_LEN, so Nottingham's 240 qualify);
              skipped if it contains NaN or is constant
  inputs      x_k = -pi + 2 pi k / n_w   (the input grid convention of the paper)
  target      affine trend in k removed, then centred and scaled so that max |y| = SUP (as the bump family)
  split       interpolation split: a random 2/3 of the window trains, the rest tests; SPLIT_SEEDS splits
  fit         least squares on the train points over 1, cos kx, sin kx, k <= E, for E in E_GRID
  score       test R^2 per E; median over split seeds
  pass        R2(32) - R2(16) >= DELTA_GAIN  and  R2(32) >= R2(24) - TOL_TOP  and  R2(32) >= MIN_R2
              (the fit keeps improving to the top degree and does not overfit there; and the held-out error is
              small, so that an optimiser stalling ~1e-3 above the least-squares optimum is visible against the
              noise -- on a noisy series such a stall cannot show in test R^2, whatever the circuit)
  feasibility sup |f| of the E=32 fit (on all window points) must be <= 1: otherwise the circuit model class
              (|f| <= 1) cannot contain the least-squares optimum; recorded, and such series do not pass
  duplicates  identical windows (e.g. sunspot.month vs sunspots) are screened once
  selection   circuits are run on ALL passing series; if more than MAX_SELECT pass, on the MAX_SELECT with the
              largest gain R2(32) - R2(16) (a classical quantity, not a circuit result). Every screened series is
              listed in screening_results.csv, and Nottingham stays in the paper regardless.

Usage:  python screen_realdata.py            (downloads into ./cache, writes screening_results.csv)
Requirements: numpy, pandas. Network access to raw.githubusercontent.com (Rdatasets mirror).
"""
import hashlib, io, os, sys, time, urllib.request
import numpy as np
import pandas as pd

# ---------------- pre-specified constants ----------------
N_WINDOW, MIN_LEN = 300, 240
SUP = 0.8
E_GRID = [4, 8, 12, 16, 24, 32]
SPLIT_SEEDS = [0, 1, 2, 3, 4]
DELTA_GAIN, TOL_TOP, MIN_R2 = 0.02, 0.005, 0.95
MAX_SELECT = 3
RD = "https://raw.githubusercontent.com/vincentarelbundock/Rdatasets/master"
CACHE, MANUAL = "cache", "manual"
# ----------------------------------------------------------


def fetch(url, path, rng=None):
    if path is not None and os.path.exists(path) and rng is None:
        return open(path, "rb").read()
    req = urllib.request.Request(url, headers={"User-Agent": "screen/1.0", **({"Range": rng} if rng else {})})
    for attempt in range(3):
        try:
            with urllib.request.urlopen(req, timeout=60) as r:
                data = r.read()
            if rng is None:
                os.makedirs(os.path.dirname(path), exist_ok=True)
                open(path, "wb").write(data)
            return data
        except Exception as ex:  # noqa: BLE001
            err = ex
            time.sleep(2 * (attempt + 1))
    raise RuntimeError(f"download failed: {url} ({err})")


def rdatasets_candidates():
    idx = pd.read_csv(io.BytesIO(fetch(f"{RD}/datasets.csv", os.path.join(CACHE, "datasets.csv"))))
    idx = idx[(idx.Rows >= MIN_LEN) & (idx.Cols <= 3)]
    out = []
    for _, row in idx.iterrows():
        rel = row.CSV.split("/csv/", 1)[1]                      # e.g. datasets/nottem.csv
        url = f"{RD}/csv/{rel}"
        try:
            head = fetch(url, None, rng="bytes=0-200").decode("utf-8", "replace").splitlines()[0]
        except RuntimeError:
            continue
        cols = [c.strip('"') for c in head.split(",")]
        if cols == ["rownames", "time", "value"]:               # univariate, regularly sampled ts object
            out.append((f"{row.Package}/{row.Item}", url, os.path.join(CACHE, rel)))
    return out


def load_rdataset(url, path):
    df = pd.read_csv(io.BytesIO(fetch(url, path)))
    return df.sort_values("time")["value"].to_numpy(dtype=float)


def load_manual():
    out = []
    if not os.path.isdir(MANUAL):
        return out
    for f in sorted(os.listdir(MANUAL)):
        if f.endswith(".csv"):
            df = pd.read_csv(os.path.join(MANUAL, f))
            num = df.select_dtypes("number")
            if "value" in df.columns:
                y = (df.sort_values("time") if "time" in df.columns else df)["value"].to_numpy(dtype=float)
            elif num.shape[1] == 1:
                y = num.iloc[:, 0].to_numpy(dtype=float)
            else:
                print(f"  manual/{f}: skipped (need one numeric column or time,value)")
                continue
            out.append((f"manual/{f}", y))
    return out


def design(x, E):
    k = np.arange(1, E + 1)
    return np.hstack([np.ones((len(x), 1)), np.cos(np.outer(x, k)), np.sin(np.outer(x, k))])


def preprocess(y):
    w = y[-N_WINDOW:]
    if len(w) < MIN_LEN or not np.all(np.isfinite(w)) or np.ptp(w) == 0:
        return None
    t = np.arange(len(w), dtype=float)
    w = w - np.polyval(np.polyfit(t, w, 1), t)                  # remove affine trend
    w = w - w.mean()
    m = np.max(np.abs(w))
    return None if m == 0 else SUP * w / m


def screen(y):
    n = len(y)
    x = -np.pi + 2 * np.pi * np.arange(n) / n
    r2 = {E: [] for E in E_GRID}
    for s in SPLIT_SEEDS:
        perm = np.random.default_rng(s).permutation(n)
        tr, te = perm[:2 * n // 3], perm[2 * n // 3:]
        for E in E_GRID:
            c, *_ = np.linalg.lstsq(design(x[tr], E), y[tr], rcond=None)
            res = y[te] - design(x[te], E) @ c
            r2[E].append(1 - np.sum(res ** 2) / np.sum((y[te] - y[te].mean()) ** 2))
    med = {E: float(np.median(v)) for E, v in r2.items()}
    c, *_ = np.linalg.lstsq(design(x, max(E_GRID)), y, rcond=None)
    xf = np.linspace(-np.pi, np.pi, 4096, endpoint=False)
    sup_fit = float(np.max(np.abs(design(xf, max(E_GRID)) @ c)))
    gain = med[32] - med[16]
    ok = gain >= DELTA_GAIN and med[32] >= med[24] - TOL_TOP and med[32] >= MIN_R2 and sup_fit <= 1.0
    return med, gain, sup_fit, ok


def main():
    os.makedirs(CACHE, exist_ok=True)
    print("collecting candidates ...")
    cands = [(n, load_rdataset(u, p)) for n, u, p in rdatasets_candidates()] + load_manual()
    rows, seen = [], {}
    for name, y in cands:
        w = preprocess(y)
        if w is None:
            rows.append({"series": name, "status": "skipped (short, NaN or constant)"})
            continue
        h = hashlib.sha1(np.round(w, 12).tobytes()).hexdigest()
        if h in seen:
            rows.append({"series": name, "status": f"duplicate of {seen[h]}"})
            continue
        seen[h] = name
        med, gain, sup_fit, ok = screen(w)
        rows.append({"series": name, "status": "screened", "n_total": len(y),
                     **{f"R2_E{E}": round(v, 4) for E, v in med.items()},
                     "gain_16_32": round(gain, 4), "sup_fit_E32": round(sup_fit, 3), "pass": ok})
    res = pd.DataFrame(rows)
    res.to_csv("screening_results.csv", index=False)
    sc = res[res.status == "screened"]
    passed = sc[sc["pass"]].sort_values("gain_16_32", ascending=False)
    print(f"\nscreened {len(sc)} distinct series ({len(res) - len(sc)} skipped or duplicate); {len(passed)} pass")
    cols = ["series"] + [f"R2_E{E}" for E in E_GRID] + ["gain_16_32", "sup_fit_E32"]
    if len(passed):
        print(passed[cols].to_string(index=False))
        print(f"\nselected for the circuit runs (pre-specified rule, at most {MAX_SELECT}):")
        print("\n".join("  " + s for s in passed.series.head(MAX_SELECT)))
    print("\nfull table: screening_results.csv")


if __name__ == "__main__":
    sys.exit(main())
