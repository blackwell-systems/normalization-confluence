/* Brute force over all 2^24 Boolean networks on n=3 vertices.
   tt bits: bit (i*8 + x) is f_i(x). Counts networks by (A, B, async cyclic, fair non-settling). */
#include <stdio.h>
#include <stdint.h>
#define n 3
#define N 8
static int f(uint32_t t, int i, int x) { return (t >> (i * N + x)) & 1; }
static int arc(uint32_t t, int x, int j, int i) { return f(t, i, x ^ (1 << j)) != f(t, i, x); }
static int unst(uint32_t t, int x, int v) { return f(t, v, x) != ((x >> v) & 1); }

static int localcyc(uint32_t t, int x) {
  /* elementary cycles of length 1..3 on {0,1,2} */
  for (int a = 0; a < n; a++) if (arc(t, x, a, a)) return 1;
  for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++)
    if (arc(t, x, a, b) && arc(t, x, b, a)) return 1;
  if (arc(t, x, 0, 1) && arc(t, x, 1, 2) && arc(t, x, 2, 0)) return 1;
  if (arc(t, x, 0, 2) && arc(t, x, 2, 1) && arc(t, x, 1, 0)) return 1;
  return 0;
}
static int outdeg_ok(uint32_t t, int x) {
  for (int j = 0; j < n; j++) { int d = 0; for (int i = 0; i < n; i++) d += arc(t, x, j, i); if (d > 1) return 0; }
  return 1;
}
int main(void) {
  long cnt[2][2][3] = {{{0}}}; /* [A][B][0=total,1=cyclic,2=fair] */
  for (uint64_t tt = 0; tt < (1ull << 24); tt++) {
    uint32_t t = (uint32_t)tt;
    int A = 1, B = 1;
    for (int x = 0; x < N; x++) { if (A && localcyc(t, x)) A = 0; if (B && !outdeg_ok(t, x)) B = 0; }
    /* reachability matrix of the async state graph */
    uint8_t R[N];
    for (int x = 0; x < N; x++) { R[x] = 0; for (int v = 0; v < n; v++) if (unst(t, x, v)) R[x] |= 1 << (x ^ (1 << v)); }
    for (int k = 0; k < N; k++) for (int x = 0; x < N; x++) if (R[x] >> k & 1) R[x] |= R[k];
    int cyc = 0, fair = 0;
    for (int x = 0; x < N; x++) if (R[x] >> x & 1) cyc = 1;
    if (cyc) {
      for (int r = 0; r < N && !fair; r++) {
        if (!(R[r] >> r & 1)) continue;
        uint8_t C = 0; for (int y = 0; y < N; y++) if ((R[r] >> y & 1) && (R[y] >> r & 1)) C |= 1 << y;
        int ok = 1;
        for (int w = 0; w < n && ok; w++) {
          int cov = 0;
          for (int y = 0; y < N; y++) if (C >> y & 1) {
            if (!unst(t, y, w)) cov = 1; else if (C >> (y ^ (1 << w)) & 1) cov = 1;
          }
          if (!cov) ok = 0;
        }
        if (ok) fair = 1;
      }
    }
    cnt[A][B][0]++; cnt[A][B][1] += cyc; cnt[A][B][2] += fair;
  }
  for (int A = 0; A < 2; A++) for (int B = 0; B < 2; B++)
    printf("A=%d B=%d total=%ld async_cyclic=%ld fair_nonsettling=%ld\n", A, B, cnt[A][B][0], cnt[A][B][1], cnt[A][B][2]);
  return 0;
}
