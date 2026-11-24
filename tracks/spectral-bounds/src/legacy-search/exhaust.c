/* exhaust.c - exact contextuality degree by exhaustive Gray-code enumeration (small configurations).
 * Gauge: multiplying f by a linear character (-1)^{<a,v>} preserves every line product (u^v^w = 0), so f can be
 * fixed to +1 on a GF(2)-basis of the span of S; the remaining |S| - rank points are enumerated (2^(|S|-rank)).
 * Usage: exhaust N kind      prints the exact minimum and the histogram minimum count. */
#include "geom.h"
int main(int argc, char **argv) {
    if (argc != 3) return 2;
    int N = atoi(argv[1]); char kind = argv[2][0];
    geom_t *g = geom_build(N, kind);
    /* choose basis points greedily */
    uint32_t basis[64], piv[64]; int r = 0; uint8_t *fixed = calloc(g->npts, 1);
    for (uint32_t i = 0; i < g->npts; i++) {
        uint32_t x = g->pts[i];
        for (int k = 0; k < r; k++) if ((x >> piv[k]) & 1) x ^= basis[k];
        if (x) { basis[r] = x; piv[r] = 31 - __builtin_clz(x); r++; fixed[i] = 1; }
    }
    uint32_t nfree = 0, *freev = malloc(sizeof(uint32_t) * g->npts);
    for (uint32_t i = 0; i < g->npts; i++) if (!fixed[i]) freev[nfree++] = i;
    if (nfree > 40) { fprintf(stderr, "too many free points (%u)\n", nfree); free(freev); free(fixed); geom_free(g); return 2; }
    int8_t *f = malloc(g->npts); memset(f, 1, g->npts);
    uint8_t *bad = malloc(g->L); long long v = 0;
    for (uint64_t l = 0; l < g->L; l++) { bad[l] = f[g->line[l][0]] * f[g->line[l][1]] * f[g->line[l][2]] != g->sgn[l]; v += bad[l]; }
    long long best = v, nbest = 1;
    for (uint64_t m = 1; m < (1ull << nfree); m++) {
        uint32_t i = freev[__builtin_ctzll(m)];
        for (uint32_t o = g->inc_off[i]; o < g->inc_off[i + 1]; o++) { uint32_t l = g->inc[o]; v += bad[l] ? -1 : 1; bad[l] ^= 1; }
        f[i] = -f[i];
        if (v < best) { best = v; nbest = 1; } else if (v == best) nbest++;
    }
    printf("N=%d kind=%c points=%u lines=%llu rank=%d enumerated=2^%u exact_degree=%lld (attained by %lld gauge classes)\n",
           N, kind, g->npts, (unsigned long long)g->L, r, nfree, best, nbest);
    free(bad); free(f); free(freev); free(fixed); geom_free(g);
    return 0;
}
