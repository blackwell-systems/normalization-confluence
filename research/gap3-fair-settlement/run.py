import sys, time, json
from pysat.solvers import Solver
from enc import Enc
import verify as V


def sd_tt():
    n = 4
    b = V.bit
    fs = [lambda x: int((not b(x, 1)) and (not b(x, 2))),
          lambda x: int(b(x, 0) or (not b(x, 2)) or b(x, 3)),
          lambda x: int(b(x, 0) and b(x, 1) and b(x, 3)),
          lambda x: int(not b(x, 0))]
    return [[fs[i](x) for x in range(16)] for i in range(n)]


def solve(n, A, B, target, fixed=None, solver="cadical195"):
    t0 = time.time()
    e = Enc(n, A=A, B=B, target=target, fixed=fixed)
    t1 = time.time()
    with Solver(name=solver, bootstrap_with=e.cnf.clauses) as s:
        sat = s.solve()
        model = s.get_model() if sat else None
    t2 = time.time()
    res = {"n": n, "A": A, "B": B, "target": target, "fixed": fixed is not None, "sat": sat,
           "vars": e.pool.top, "clauses": len(e.cnf.clauses),
           "t_encode": round(t1 - t0, 2), "t_solve": round(t2 - t1, 2)}
    if sat:
        tt = e.decode(model)
        res["tt"] = tt
        res["chk_A"] = V.check_A(tt, n)
        res["chk_B"] = V.check_B(tt, n)
        res["chk_async_cyclic"] = V.async_cyclic(tt, n)
        fw = V.fair_witness(tt, n)
        if fw:
            comp, word = fw
            res["fair_start"] = V.fmt(comp[0], n)
            res["fair_word"] = word
            res["fair_ok"] = V.verify_fair_run(tt, n, comp[0], word)
        else:
            res["fair_start"] = None
    return res


if __name__ == "__main__":
    n = int(sys.argv[1]); A = sys.argv[2] == "1"; B = sys.argv[3] == "1"; target = sys.argv[4]
    fixed = sd_tt() if len(sys.argv) > 5 and sys.argv[5] == "sd" else None
    r = solve(n, A, B, target, fixed)
    print(json.dumps(r))
