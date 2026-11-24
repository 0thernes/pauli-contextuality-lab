/* wcheck.c - second independent witness checker (C, letter-table phases; shares no code with src/hoggar.c
 * or the Python verifiers under verify/).  Usage: wcheck FILE...   exit 1 on any mismatch. */
#include "geom.h"
int main(int argc, char **argv) {
    int bad = 0;
    for (int a = 1; a < argc; a++) {
        int N; char kind; long long claim; uint8_t *bits;
        if (witness_read(argv[a], &N, &kind, &claim, &bits)) { printf("%s: unreadable\n", argv[a]); bad = 1; continue; }
        geom_t *g = geom_build(N, kind);
        int8_t *f = xmalloc(g->npts);
        for (uint32_t i = 0; i < g->npts; i++) f[i] = bits[g->pts[i]] ? -1 : 1;
        long long v = count_viol(g, f);
        printf("%s: N=%d type=%c points=%u lines=%llu claimed=%lld recomputed=%lld %s\n", argv[a], N, kind, g->npts,
               (unsigned long long)g->L, claim, v, v == claim ? "OK" : "MISMATCH");
        if (v != claim) bad = 1;
        free(f);
        free(bits);
        geom_free(g);
    }
    return bad;
}
