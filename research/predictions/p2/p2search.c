/* Exhaustive search for prediction P2 (see README.md in this directory).

   Usage: p2search n [shard nshards]      (n = 1..4)
          p2search check n < profiles        (one profile per line: 2n lists of digits, men
                                              first, e.g. "012 012 120 201 120 201"; prints
                                              "k cyc fair" per line; used by the tests)

   For every preference profile of the n-by-n marriage market, up to relabeling men and women,
   count the stable matchings and decide whether the blocking-pair state graph has a pair-fair
   strongly connected component (the exact criterion for a bad fair lasso; see p2ref.py).

   Symmetry reduction: the men's profile runs over one representative of each orbit under
   (relabel men) x (relabel women); the women's profile runs over all n!^n profiles. Every
   profile is equivalent to one enumerated profile, and the count of profiles of the full space
   with a given (invariant) property is the sum over representatives r of
   |orbit(r)| * #{women profiles wp : (r, wp) has the property}. The "weighted" counts below are
   those exact full-space counts; the side swap is not used.

   Output: one line per number k of stable matchings:
     k <k> checked <c> weighted <W> cyc_checked <c> cyc_weighted <W> fair_checked <c> fair_weighted <W>
   where cyc = some nontrivial SCC exists, fair = some pair-fair SCC exists. Witnesses with a
   unique stable matching and a fair SCC are printed as lines starting with "WITNESS". */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4
#define MAXP 24
#define MAXS 209
#define MAXK 64

static int n, P, NS, NJ;
static int perm[MAXP][MAXN];          /* perm[p][k] = item at position k (best first) */
static int rankof[MAXP][MAXN];        /* rankof[p][x] = position of x in perm p */
static int permap[MAXP][MAXP];        /* permap[t][p] = index of the list t(perm p) */
static int wifeS[MAXS][MAXN], husS[MAXS][MAXN];
static int tgt[MAXS][MAXN * MAXN];    /* state after forcing pair j = m*n+w */
static int idx_of[1024];

static int perm_index(const int *a) {
  for (int p = 0; p < P; p++) {
    int ok = 1;
    for (int k = 0; k < n; k++) if (perm[p][k] != a[k]) { ok = 0; break; }
    if (ok) return p;
  }
  return -1;
}

static int wcode(const int *wife) { int c = 0; for (int m = 0; m < n; m++) c = c * (n + 1) + (wife[m] + 1); return c; }

static void gen_perms(void) {
  int a[MAXN]; P = 0;
  /* lexicographic generation */
  for (int k = 0; k < n; k++) a[k] = k;
  for (;;) {
    memcpy(perm[P], a, sizeof a); P++;
    int i = n - 2; while (i >= 0 && a[i] > a[i + 1]) i--;
    if (i < 0) break;
    int j = n - 1; while (a[j] < a[i]) j--;
    int t = a[i]; a[i] = a[j]; a[j] = t;
    for (int l = i + 1, r = n - 1; l < r; l++, r--) { t = a[l]; a[l] = a[r]; a[r] = t; }
  }
  for (int p = 0; p < P; p++) for (int k = 0; k < n; k++) rankof[p][perm[p][k]] = k;
  for (int t = 0; t < P; t++) for (int p = 0; p < P; p++) {
    int b[MAXN]; for (int k = 0; k < n; k++) b[k] = perm[t][perm[p][k]];
    permap[t][p] = perm_index(b);
  }
}

static void gen_states(void) {
  NS = 0; NJ = n * n;
  int wife[MAXN];
  /* enumerate all partial matchings */
  int total = 1; for (int m = 0; m < n; m++) total *= (n + 1);
  for (int c = 0; c < total; c++) {
    int x = c, used = 0, ok = 1;
    for (int m = n - 1; m >= 0; m--) { wife[m] = x % (n + 1) - 1; x /= (n + 1); }
    for (int m = 0; m < n; m++) if (wife[m] >= 0) { if (used & (1 << wife[m])) ok = 0; used |= 1 << wife[m]; }
    if (!ok) continue;
    memcpy(wifeS[NS], wife, sizeof wife);
    for (int w = 0; w < n; w++) husS[NS][w] = -1;
    for (int m = 0; m < n; m++) if (wife[m] >= 0) husS[NS][wife[m]] = m;
    idx_of[c] = NS; NS++;
  }
  for (int s = 0; s < NS; s++) for (int m = 0; m < n; m++) for (int w = 0; w < n; w++) {
    int nw[MAXN]; memcpy(nw, wifeS[s], sizeof nw);
    if (husS[s][w] >= 0) nw[husS[s][w]] = -1;
    nw[m] = w;
    tgt[s][m * n + w] = idx_of[wcode(nw)];
  }
}

/* ---- analysis of one profile ---- */
static int rm[MAXN][MAXN], rw[MAXN][MAXN];
static unsigned block[MAXS];
static int comp[MAXS];

static void blocks(void) {
  for (int s = 0; s < NS; s++) {
    unsigned b = 0;
    const int *wf = wifeS[s], *hs = husS[s];
    for (int m = 0; m < n; m++) {
      int cw = wf[m];
      for (int w = 0; w < n; w++) {
        if (cw == w) continue;
        if (cw >= 0 && rm[m][w] > rm[m][cw]) continue;
        int ch = hs[w];
        if (ch >= 0 && rw[w][m] > rw[w][ch]) continue;
        b |= 1u << (m * n + w);
      }
    }
    block[s] = b;
  }
}

/* Tarjan, iterative. Returns number of components; comp[] filled. */
static int tarjan(void) {
  static int index[MAXS], low[MAXS], onst[MAXS], st[MAXS], cs_v[MAXS], cs_j[MAXS];
  int counter = 0, sp = 0, nc = 0;
  for (int s = 0; s < NS; s++) index[s] = -1;
  for (int r = 0; r < NS; r++) {
    if (index[r] >= 0) continue;
    int top = 0;
    cs_v[0] = r; cs_j[0] = 0; index[r] = low[r] = counter++; st[sp++] = r; onst[r] = 1;
    while (top >= 0) {
      int v = cs_v[top];
      unsigned rest = block[v] >> cs_j[top];
      int pushed = 0;
      while (rest) {
        int j = cs_j[top] + __builtin_ctz(rest);
        cs_j[top] = j + 1;
        int t = tgt[v][j];
        if (index[t] < 0) {
          index[t] = low[t] = counter++; st[sp++] = t; onst[t] = 1;
          top++; cs_v[top] = t; cs_j[top] = 0; pushed = 1; break;
        } else if (onst[t] && index[t] < low[v]) low[v] = index[t];
        rest = (j + 1 < 32) ? block[v] >> (j + 1) : 0;
      }
      if (pushed) continue;
      top--;
      if (top >= 0) { int u = cs_v[top]; if (low[v] < low[u]) low[u] = low[v]; }
      if (low[v] == index[v]) {
        int x;
        do { x = st[--sp]; onst[x] = 0; comp[x] = nc; } while (x != v);
        nc++;
      }
    }
  }
  return nc;
}

/* returns k (stable count); *cyc, *fair set */
static int analyse(int *cyc, int *fair) {
  blocks();
  int k = 0;
  for (int s = 0; s < NS; s++) if (!block[s]) k++;
  int nc = tarjan();
  static int csize[MAXS]; static unsigned nb[MAXS], ie[MAXS];
  unsigned full = (NJ == 32) ? 0xffffffffu : ((1u << NJ) - 1);
  for (int c = 0; c < nc; c++) { csize[c] = 0; nb[c] = 0; ie[c] = 0; }
  for (int s = 0; s < NS; s++) {
    int c = comp[s]; csize[c]++; nb[c] |= ~block[s] & full;
    unsigned b = block[s];
    while (b) { int j = __builtin_ctz(b); b &= b - 1; if (comp[tgt[s][j]] == c) ie[c] |= 1u << j; }
  }
  *cyc = 0; *fair = 0;
  for (int c = 0; c < nc; c++) if (csize[c] > 1) {
    *cyc = 1;
    if ((nb[c] | ie[c]) == full) *fair = 1;
  }
  return k;
}

static void decode(int code, int *prof) { for (int m = 0; m < n; m++) { prof[m] = code % P; code /= P; } }
static int encode(const int *prof) { int c = 0; for (int m = n - 1; m >= 0; m--) c = c * P + prof[m]; return c; }

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: p2search n [shard nshards] | p2search check n\n"); return 2; }
  if (strcmp(argv[1], "check") == 0 && argc > 2) {
    n = atoi(argv[2]);
    if (n < 1 || n > MAXN) return 2;
    gen_perms(); gen_states();
    char buf[16];
    for (;;) {
      int ok = 1;
      for (int a = 0; a < 2 * n && ok; a++) {
        if (scanf("%15s", buf) != 1) { ok = 0; break; }
        for (int x = 0; x < n; x++) {
          int r = buf[x] - '0';
          if (a < n) rm[a][r] = x; else rw[a - n][r] = x;
        }
      }
      if (!ok) break;
      int cyc, fair, k = analyse(&cyc, &fair);
      printf("%d %d %d\n", k, cyc, fair);
    }
    return 0;
  }
  n = atoi(argv[1]);
  int shard = argc > 3 ? atoi(argv[2]) : 0, nsh = argc > 3 ? atoi(argv[3]) : 1;
  if (n < 1 || n > MAXN) return 2;
  gen_perms(); gen_states();
  int NP = 1; for (int m = 0; m < n; m++) NP *= P;   /* profiles of one side */
  uint64_t chk[MAXK] = {0}, wt[MAXK] = {0}, cchk[MAXK] = {0}, cwt[MAXK] = {0}, fchk[MAXK] = {0}, fwt[MAXK] = {0};
  long nreps = 0, witnesses = 0;
  clock_t t0 = clock();
  for (int code = 0; code < NP; code++) {
    int mp[MAXN]; decode(code, mp);
    /* canonical check and orbit size under (sigma on men, tau on women); sigma ranges over the
       index positions via perm[], tau via permap[] */
    int minimal = 1, stab = 0;
    for (int sg = 0; sg < P && minimal; sg++) for (int t = 0; t < P; t++) {
      int img[MAXN];
      for (int m = 0; m < n; m++) img[perm[sg][m]] = permap[t][mp[m]];
      int ic = encode(img);
      if (ic < code) { minimal = 0; break; }
      if (ic == code) stab++;
    }
    if (!minimal) continue;
    if ((nreps++ % nsh) != shard) continue;
    uint64_t orbit = (uint64_t)(P * P) / stab;
    for (int m = 0; m < n; m++) for (int w = 0; w < n; w++) rm[m][w] = rankof[mp[m]][w];
    for (int wc = 0; wc < NP; wc++) {
      int wp[MAXN]; decode(wc, wp);
      for (int w = 0; w < n; w++) for (int m = 0; m < n; m++) rw[w][m] = rankof[wp[w]][m];
      int cyc, fair, k = analyse(&cyc, &fair);
      chk[k]++; wt[k] += orbit;
      if (cyc) { cchk[k]++; cwt[k] += orbit; }
      if (fair) { fchk[k]++; fwt[k] += orbit; }
      if (fair && k == 1 && witnesses < 20) {
        witnesses++;
        printf("WITNESS men");
        for (int m = 0; m < n; m++) { printf(" ["); for (int x = 0; x < n; x++) printf("%d", perm[mp[m]][x]); printf("]"); }
        printf(" women");
        for (int w = 0; w < n; w++) { printf(" ["); for (int x = 0; x < n; x++) printf("%d", perm[wp[w]][x]); printf("]"); }
        printf("\n"); fflush(stdout);
      }
    }
  }
  printf("n %d shard %d/%d reps_total %ld cpu_seconds %.1f\n", n, shard, nsh, nreps,
         (double)(clock() - t0) / CLOCKS_PER_SEC);
  for (int k = 0; k < MAXK; k++) if (chk[k])
    printf("k %d checked %llu weighted %llu cyc_checked %llu cyc_weighted %llu fair_checked %llu fair_weighted %llu\n",
           k, (unsigned long long)chk[k], (unsigned long long)wt[k], (unsigned long long)cchk[k],
           (unsigned long long)cwt[k], (unsigned long long)fchk[k], (unsigned long long)fwt[k]);
  return 0;
}
