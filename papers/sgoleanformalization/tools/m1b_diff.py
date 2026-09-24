#!/usr/bin/env python3
# m1b_diff.py — differential for the decoherent family (milestone 1
# continued): Lean SgoDelta.dsgoEv / kEv vs an independent Python
# reference of the printed Δ / E_DSGo / E_k, built on the engine's
# hardened primitives: place (placement + stamps + collision -> r),
# branch_children (P's priority tiers), resolve_turn(., None, None)
# (= the objective reduction OR, stages with no placement).
# Caveat, stated: the Δ-round/re-cut/verdict logic is implemented twice
# from the same printed text (Lean here, Python there) by the same
# author — weaker than the engine-vs-Lean independence of the SGo slice,
# but the classical, placement and OR components remain fully
# independent. Emits TestDelta.lean with a native_decide checker.
import random, sys
sys.path.insert(0, '/home/claude/sgo')
import sgo_engine as E

random.seed(4177)
assert not E.DSGO and not E.JCR

def enc_disp(board, ts, N):
    out = []
    for x in range(N):
        for y in range(N):
            p = (x, y)
            out.append(f"{board[p]}{ts.get(p, 0)}" if p in board else ".")
    return ",".join(out)

def enc_branch(a, N):
    return "".join(a.get((x, y), ".") for x in range(N) for y in range(N))

def rand_move(board, N, pass_p):
    if random.random() < pass_p:
        return None
    empties = [(x, y) for x in range(N) for y in range(N) if (x, y) not in board]
    if not empties:
        return None
    return random.choice(empties)

def mstr(m):
    return "p" if m is None else str(m)

# ---------------- independent reference of the printed family ----------------

def decoherence(branches, m0, m1, N):
    out = {}
    for a in branches:
        for ch in E.branch_children(a, m0, m1, N):
            out[E.key(ch)] = ch
    return list(out.values())

def delta_py(N, t, board, ts, M):
    board = dict(board); ts = dict(ts)
    while True:
        b2 = {}
        for p, k in board.items():
            cols = {a[p] for a in M if p in a}
            if not cols:
                continue
            if k == 'r' and ts.get(p) == t and len(cols) == 1:
                b2[p] = next(iter(cols))
            else:
                b2[p] = k
        M = [a for a in M if all(p in b2 for p in a)]
        if b2 == board:
            return b2, {p: ts[p] for p in b2}, M
        board = b2

def dsgo_step(N, board, ts, branches, n, m0, m1):
    dec = decoherence(branches, m0, m1, N)
    b2, t2 = E.place(dict(board), dict(ts), n, m0, m1, N)
    return delta_py(N, n, b2, t2, dec)

def ver_of(N, n, board, ts):
    R, _ = E.resolve_turn(dict(board), dict(ts), n, None, None, N)
    rem = sorted((p[0] * N + p[1], ts.get(p, 0)) for p in board if p not in R)
    rec = sorted((p[0] * N + p[1], ts.get(p, 0), R[p])
                 for p in board if board[p] == 'r' and p in R and R[p] != 'r')
    return {'rem': rem, 'rec': rec}

def exec_v(N, v, board, ts):
    board = dict(board); ts = dict(ts)
    for (i, st) in v['rem']:
        p = (i // N, i % N)
        if p in board and ts.get(p, 0) == st:
            del board[p]; ts.pop(p, None)
    for (i, st, c) in v['rec']:
        p = (i // N, i % N)
        if p in board and ts.get(p, 0) == st:
            board[p] = c
    return board, ts

def k_step(N, board, ts, branches, verdicts, n, m0, m1):
    v1, vrest = verdicts[0], verdicts[1:]
    dec = decoherence(branches, m0, m1, N)
    bx, tx = exec_v(N, v1, board, ts)
    b2, t2 = E.place(bx, tx, n, m0, m1, N)
    D, T, M = delta_py(N, n, b2, t2, dec)
    return D, T, M, vrest + [ver_of(N, n, D, T)]

# ---------------- playout generation ----------------

def gen_games(N, games, maxt, mode):
    # mode: 0 = DSGo, k >= 1 = k-DSGo
    cases = []
    for g in range(games):
        board, ts, branches = {}, {}, [dict()]
        verdicts = [{'rem': [], 'rec': []} for _ in range(mode)]
        n = 1
        moves, disps, ents, fins, probes = [], [], [], [], []
        for turn in range(maxt):
            pr = []
            if board and random.random() < 0.35:
                occ = random.choice(list(board.keys()))
                other = rand_move(board, N, 0.2)
                a = occ[0] * N + occ[1]
                b = None if other is None else other[0] * N + other[1]
                pr.append((a, b) if random.random() < 0.5 else (b, a))
            probes.append(pr)
            m0 = rand_move(board, N, 0.10)
            m1 = rand_move(board, N, 0.10)
            if m0 is not None and random.random() < 0.12:
                m1 = m0  # collision
            fin = m0 is None and m1 is None
            if mode == 0:
                board, ts, branches = dsgo_step(N, board, ts, branches, n, m0, m1)
            else:
                board, ts, branches, verdicts = \
                    k_step(N, board, ts, branches, verdicts, n, m0, m1)
            n += 1
            moves.append((m0[0] * N + m0[1] if m0 else None,
                          m1[0] * N + m1[1] if m1 else None))
            disps.append(enc_disp(board, ts, N))
            ents.append(sorted({enc_branch(a, N) for a in branches}))
            fins.append(fin)
            if fin or len(branches) > 40 or not branches:
                break
        movesS = ";".join(f"{mstr(a)}:{mstr(b)}" for a, b in moves)
        dispsS = "|".join(disps)
        entsS = "|".join(",".join(bs) for bs in ents)
        finsS = "".join("1" if f else "0" for f in fins)
        probesS = "|".join(" ".join(f"{mstr(a)}:{mstr(b)}" for a, b in pr)
                           for pr in probes[:len(moves)])
        cases.append((mode, N, movesS, dispsS, entsS, finsS, probesS))
    return cases

HEADER = r'''/- TestDelta.lean — GENERATED by m1b_diff.py. Differential for the
   decoherent family: dsgoEv / kEv vs an independent Python reference of
   the printed Δ / E_DSGo / E_k (engine primitives: place,
   branch_children, resolve_turn-as-OR). String-encoded cases; inline
   unavailability probes. mode 0 = DSGo, k >= 1 = k-DSGo. -/
import SgoDelta
open SgoGo SgoDisplay SgoSerial SgoDelta

structure DCase where
  mode : Nat
  n : Nat
  movesS : String
  dispsS : String
  entsS : String
  finsS : String
  probesS : String

def kindChar : DKind → String | .b => "b" | .w => "w" | .r => "r"

def encDisp (n : Nat) (D : Display n) : String :=
  String.intercalate "," ((allIdx n).map fun i =>
    match D.get i with
    | none => "."
    | some (k, st) => kindChar k ++ toString st)

def encBranch (n : Nat) (b : Display n) : String :=
  ((allIdx n).map fun i =>
    match kindAt b i with
    | none => "." | some k => kindChar k).foldl (· ++ ·) ""

def setEq (xs ys : List String) : Bool :=
  xs.all ys.contains && ys.all xs.contains

def dMv (s : String) : Option Nat :=
  if s == "p" then none else some s.toNat!

def dPair (s : String) : Option Nat × Option Nat :=
  match s.splitOn ":" with
  | [a, b] => (dMv a, dMv b)
  | _ => (some 999999, some 999999)

def dPairs (s : String) : List (Option Nat × Option Nat) :=
  if s == "" then [] else (s.splitOn " ").map dPair

def dSplit (s : String) : List String :=
  if s == "" then [] else s.splitOn ","

/-- One replay engine for both games: the state is either a DSGo state
    (SGoState) or a k-DSGo state (KState), stepped by the matching
    evolution. -/
inductive FState (n : Nat) where
  | d (s : SGoState n)
  | k (s : KState n)

def FState.step {n : Nat} : FState n → Option Nat → Option Nat → Option (FState n)
  | .d s, m0, m1 => (dsgoEv n s m0 m1).map .d
  | .k s, m0, m1 => (kEv n s m0 m1).map .k

def FState.disp {n : Nat} : FState n → Display n
  | .d s => s.disp
  | .k s => s.disp

def FState.ent {n : Nat} : FState n → List (Display n)
  | .d s => s.ent
  | .k s => s.ent

def FState.fin {n : Nat} : FState n → Bool
  | .d s => s.final
  | .k s => s.final

def runSteps (n : Nat) : FState n → List (String × (String × (String × (Char × String)))) → Bool
  | _, [] => true
  | s, (mv, (d, (es, (f, prS)))) :: rest =>
    ((dPairs prS).all fun (a, b) => (s.step a b).isNone) &&
    (let (m0, m1) := dPair mv
     match s.step m0 m1 with
     | none => false
     | some s' =>
       encDisp n s'.disp == d &&
       setEq (s'.ent.map (encBranch n)) (dSplit es) &&
       s'.fin == (f == '1') &&
       runSteps n s' rest)

def runGame (c : DCase) : Bool :=
  let ms := c.movesS.splitOn ";"
  let ds := c.dispsS.splitOn "|"
  let es := c.entsS.splitOn "|"
  let fs := c.finsS.data
  let ps := c.probesS.splitOn "|"
  let s0 : FState c.n :=
    if c.mode == 0 then .d (initSGo c.n) else .k (initK c.n c.mode)
  ms.length == ds.length && ms.length == es.length &&
  ms.length == fs.length && ms.length == ps.length &&
  runSteps c.n s0 (ms.zip (ds.zip (es.zip (fs.zip ps))))

def cases : List DCase := ['''

TAIL = r''']

/-- The decoherent-family differential: DSGo and k-DSGo playouts match
    the independent reference turn by turn (display with stamps,
    entanglement as a set, finality), and every unavailability probe is
    rejected. -/
theorem m1b_differential : cases.all runGame = true := by native_decide
'''

def emit(cases, path):
    rows = []
    for (mode, N, movesS, dispsS, entsS, finsS, probesS) in cases:
        rows.append(f'  ⟨{mode}, {N}, "{movesS}", "{dispsS}", "{entsS}", "{finsS}", "{probesS}"⟩,')
    with open(path, "w") as f:
        f.write(HEADER + "\n" + "\n".join(rows) + TAIL)

allc = []
allc += gen_games(3, 120, 12, 0)   # DSGo 3x3
allc += gen_games(5, 25, 8, 0)     # DSGo 5x5
allc += gen_games(3, 120, 12, 1)   # 1-DSGo 3x3
allc += gen_games(3, 100, 12, 2)   # 2-DSGo 3x3
allc += gen_games(5, 25, 8, 2)     # 2-DSGo 5x5
emit(allc, "/home/claude/sgolean/TestDelta.lean")
nt = sum(len(c[2].split(";")) for c in allc)
print(f"games {len(allc)}, turns {nt}")
