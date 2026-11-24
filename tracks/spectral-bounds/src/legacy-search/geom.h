/* geom.h - independent Pauli geometry for the search/checker tools (not derived from src/hoggar.c).
 * Point v = a | (c << N): qubit j carries letter (a_j,c_j) = (0,0) I, (1,0) X, (1,1) Y, (0,1) Z.
 * Line signs are computed by multiplying single-qubit Pauli letters with an explicit table. */
#pragma once
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

static inline void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) { fprintf(stderr, "out of memory\n"); exit(1); }
    return p;
}
static inline void *xcalloc(size_t nmemb, size_t size) {
    void *p = calloc(nmemb ? nmemb : 1, size ? size : 1);
    if (!p) { fprintf(stderr, "out of memory\n"); exit(1); }
    return p;
}
static inline void *xrealloc(void *ptr, size_t n) {
    void *p = realloc(ptr, n ? n : 1);
    if (!p) { fprintf(stderr, "out of memory\n"); exit(1); }
    return p;
}

/* letter codes: 0 I, 1 X, 2 Y, 3 Z.  MUL[p][q] = r, PH[p][q] = k with sigma_p sigma_q = i^k sigma_r */
static const int MUL[4][4] = {{0,1,2,3},{1,0,3,2},{2,3,0,1},{3,2,1,0}};
static const int PH[4][4]  = {{0,0,0,0},{0,0,1,3},{0,3,0,1},{0,1,3,0}};

static inline int letter(int N, uint32_t v, int j) {
    int a = (v >> j) & 1, c = (v >> (N + j)) & 1;
    return a ? (c ? 2 : 1) : (c ? 3 : 0);
}
/* returns k mod 4 with P_u P_v = i^k P_{u^v} */
static inline int prodphase(int N, uint32_t u, uint32_t v) {
    int k = 0;
    for (int j = 0; j < N; j++) k += PH[letter(N, u, j)][letter(N, v, j)];
    return k & 3;
}
/* membership: kind 'f' all, 'h' real matrices (even # of Y), 'e' fixed by Y_{N-1}K */
static inline int in_set(int N, char kind, uint32_t v) {
    if (!v) return 0;
    int ny = 0; for (int j = 0; j < N; j++) ny += letter(N, v, j) == 2;
    if (kind == 'f') return 1;
    if (kind == 'h') return (ny & 1) == 0;
    /* Y_{top} conj(P) Y_{top}: conj gives (-1)^{#Y}; Y on top flips sign iff top letter is X or Z */
    int t = letter(N, v, N - 1);
    int flip = (ny & 1) ^ (t == 1 || t == 3);
    return flip == 0;
}

typedef struct {
    int N; char kind; uint32_t npts, nall; uint64_t L;
    uint32_t *pts; int32_t *pos;           /* pos[v] = index or -1 */
    uint32_t (*line)[3]; int8_t *sgn;       /* lines as point indices */
    uint32_t *inc_off, *inc;                /* incidence point -> line ids */
} geom_t;

static geom_t *geom_build(int N, char kind) {
    geom_t *g = xcalloc(1, sizeof *g);
    g->N = N; g->kind = kind; g->nall = 1u << (2 * N);
    g->pos = xmalloc(sizeof(int32_t) * g->nall); g->pts = xmalloc(sizeof(uint32_t) * g->nall);
    for (uint32_t v = 0; v < g->nall; v++) { g->pos[v] = -1; if (in_set(N, kind, v)) { g->pos[v] = g->npts; g->pts[g->npts++] = v; } }
    size_t cap = 1024; g->line = xmalloc(cap * sizeof *g->line); g->sgn = xmalloc(cap);
    for (uint32_t i = 0; i < g->npts; i++) for (uint32_t j = i + 1; j < g->npts; j++) {
        uint32_t u = g->pts[i], v = g->pts[j], w = u ^ v;
        int32_t k = g->pos[w];
        if (k <= (int32_t)j) continue;
        int ph = prodphase(N, u, v);
        if (ph & 1) continue;                       /* anticommuting: P_u P_v = +-i P_w */
        if (g->L == cap) { cap *= 2; g->line = xrealloc(g->line, cap * sizeof *g->line); g->sgn = xrealloc(g->sgn, cap); }
        g->line[g->L][0] = i; g->line[g->L][1] = j; g->line[g->L][2] = (uint32_t)k;
        g->sgn[g->L] = ph == 0 ? 1 : -1;            /* P_u P_v P_w = i^ph I */
        g->L++;
    }
    g->inc_off = xcalloc(g->npts + 1, sizeof(uint32_t));
    for (uint64_t l = 0; l < g->L; l++) for (int t = 0; t < 3; t++) g->inc_off[g->line[l][t] + 1]++;
    for (uint32_t i = 0; i < g->npts; i++) g->inc_off[i + 1] += g->inc_off[i];
    g->inc = xmalloc(sizeof(uint32_t) * 3 * g->L);
    uint32_t *fill = xcalloc(g->npts, sizeof(uint32_t));
    for (uint64_t l = 0; l < g->L; l++) for (int t = 0; t < 3; t++) { uint32_t p = g->line[l][t]; g->inc[g->inc_off[p] + fill[p]++] = (uint32_t)l; }
    free(fill);
    return g;
}

static inline void geom_free(geom_t *g) {
    if (!g) return;
    free(g->pts);
    free(g->pos);
    free(g->line);
    free(g->sgn);
    free(g->inc_off);
    free(g->inc);
    free(g);
}

/* witness I/O: header "N type viol", then 4^N/4 hex chars, MS nibble first, bit v set <=> f(v) = -1 */
static inline int witness_read(const char *path, int *N, char *kind, long long *claim, uint8_t **bits_out) {
    FILE *fp = fopen(path, "r"); if (!fp) return -1;
    if (fscanf(fp, "%d %c %lld", N, kind, claim) != 3) { fclose(fp); return -2; }
    size_t len = (size_t)1 << (2 * *N - 2);
    char *hex = xmalloc(len + 8);
    if (fscanf(fp, "%s", hex) != 1 || strlen(hex) != len) { fclose(fp); free(hex); return -3; }
    uint8_t *bits = xcalloc((size_t)1 << (2 * *N), 1);
    for (size_t k = 0; k < len; k++) {
        char ch = hex[k]; unsigned x = (ch <= '9') ? (unsigned)(ch - '0') : (unsigned)(ch - 'a' + 10);
        size_t nib = len - 1 - k;
        for (int b = 0; b < 4; b++) bits[nib * 4 + b] = (x >> b) & 1;
    }
    free(hex); fclose(fp); *bits_out = bits; return 0;
}
static inline void witness_write(const char *path, const geom_t *g, const int8_t *f, long long viol) {
    char tmp[4096]; snprintf(tmp, sizeof tmp, "%s.tmp", path);
    FILE *fp = fopen(tmp, "w"); if (!fp) { perror(tmp); return; }
    fprintf(fp, "%d %c %lld\n", g->N, g->kind, viol);
    for (long long nib = (long long)(g->nall / 4) - 1; nib >= 0; nib--) {
        unsigned x = 0;
        for (int b = 0; b < 4; b++) { int32_t p = g->pos[nib * 4 + b]; if (p >= 0 && f[p] < 0) x |= 1u << b; }
        fputc("0123456789abcdef"[x], fp);
    }
    fputc('\n', fp); fclose(fp); rename(tmp, path);
}
static inline long long count_viol(const geom_t *g, const int8_t *f) {
    long long v = 0;
    for (uint64_t l = 0; l < g->L; l++) v += f[g->line[l][0]] * f[g->line[l][1]] * f[g->line[l][2]] != g->sgn[l];
    return v;
}
