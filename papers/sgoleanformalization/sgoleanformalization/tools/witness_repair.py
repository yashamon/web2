#!/usr/bin/env python3
# witness_repair.py — the k-DSGo lower-bound witness with far-corner
# padding (his ruling: padding moves need not be quiet, only
# non-interacting; never a double pass). Verifies, per (N, k):
#   setup B1/A1 then A4/pass (N >= 4; on 3x3 no A4), conflict A2/A2,
#   k-1 padding turns (greedy: a move outside the witness zone, partner
#   passes), finale B3/A3 — then the printed violation triple:
#   (1) A3 occupied on the display, (2) A3 empty in EVERY branch,
#   (3) the entanglement nonempty.
import sys
sys.path.insert(0, '/home/claude/sgo')
import sgo_engine as E

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
            if not cols: continue
            if k == 'r' and ts.get(p) == t and len(cols) == 1:
                b2[p] = next(iter(cols))
            else:
                b2[p] = k
        M = [a for a in M if all(p in b2 for p in a)]
        if b2 == board:
            return b2, {p: ts[p] for p in b2}, M
        board = b2

def ver_of(N, n, board, ts):
    R, _ = E.resolve_turn(dict(board), dict(ts), n, None, None, N)
    rem = sorted((p, ts.get(p, 0)) for p in board if p not in R)
    rec = sorted((p, ts.get(p, 0), R[p]) for p in board
                 if board[p] == 'r' and p in R and R[p] != 'r')
    return {'rem': rem, 'rec': rec}

def exec_v(N, v, board, ts):
    board = dict(board); ts = dict(ts)
    for (p, st) in v['rem']:
        if p in board and ts.get(p, 0) == st:
            del board[p]; ts.pop(p, None)
    for (p, st, c) in v['rec']:
        if p in board and ts.get(p, 0) == st:
            board[p] = c
    return board, ts

def k_step(N, st, m0, m1):
    board, ts, branches, verdicts, n = st
    v1, vrest = verdicts[0], verdicts[1:]
    dec = decoherence(branches, m0, m1, N)
    bx, tx = exec_v(N, v1, board, ts)
    b2, t2 = E.place(bx, tx, n, m0, m1, N)
    D, T, M = delta_py(N, n, b2, t2, dec)
    return (D, T, M, vrest + [ver_of(N, n, D, T)], n + 1)

# coordinates: (x, y) = (column index, row index); A1=(0,0), A2=(0,1),
# A3=(0,2), A4=(0,3), B1=(1,0), B3=(1,2)
def zone(N):
    z = {(0,0),(0,1),(0,2),(1,0),(1,2),(1,1)}          # A1 A2 A3 B1 B3 B2
    if N >= 4: z |= {(0,3),(1,3)}                       # A4 B4
    return z

def far_moves(board, N):
    z = zone(N)
    out = [(x,y) for x in range(N) for y in range(N)
           if (x,y) not in board and (x,y) not in z]
    out.sort(key=lambda p: -(p[0]))   # farthest columns first
    return out

def run_witness(N, k, verbose=False):
    st = ({}, {}, [dict()], [{'rem': [], 'rec': []} for _ in range(k)], 1)
    # setup, by commuting turns
    st = k_step(N, st, (1,0), (0,0))            # B1 black / A1 white
    if N >= 4:
        st = k_step(N, st, (0,3), None)         # A4 black / pass
    # conflict
    st = k_step(N, st, (0,1), (0,1))            # A2/A2
    # padding: k-1 turns, far moves, partner passes, never a double pass
    pads = 0
    black_turn = True
    while pads < k - 1:
        fm = far_moves(st[0], N)
        if not fm:
            return ('PAD-EXHAUSTED', pads)
        mv = fm[0]
        st = k_step(N, st, mv, None) if black_turn else k_step(N, st, None, mv)
        black_turn = not black_turn
        pads += 1
    # finale
    st = k_step(N, st, (1,2), (0,2))            # B3 black / A3 white
    board, ts, branches, verdicts, n = st
    a3 = (0,2)
    disp_occ = a3 in board
    all_empty = all(a3 not in a for a in branches)
    nonempty = len(branches) > 0
    ok = disp_occ and all_empty and nonempty
    return ('VIOLATION' if ok else
            f'FAIL disp_occ={disp_occ} all_empty={all_empty} branches={len(branches)}',
            len(branches))

for N in (3, 4, 5):
    row = []
    for k in (1, 2, 3, 4, 5, 6, 8, 12):
        res, extra = run_witness(N, k)
        row.append(f"k={k}:{res}({extra})")
    print(f"N={N}: " + "  ".join(row))
