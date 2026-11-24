/* tabu.c - iterated tabu search for noncontextual assignments with few violated lines.
 * Usage: tabu N kind seed seconds out.txt [start.txt]
 * Env: TABU_DIV (tenure = npts/TABU_DIV + 3, default 10), TABU_FRESH (% of restarts from a fresh random point, default 12)
 * RNG: xoshiro256** (classical PRNG), seeded from the command line.
 * Moves: single-point sign flips.  delta[i] = change of #violated if point i flips.
 * Tabu tenure random in [T, 2T]; aspiration on new global best; perturbation of the best-so-far after
 * a stagnation window.  Prints improvements and writes the best witness to out.txt. */
#include "geom.h"
#include <time.h>
#include <math.h>

static uint64_t s4[4];
static inline uint64_t rotl(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static uint64_t rnd(void) { uint64_t r = rotl(s4[1] * 5, 7) * 9, t = s4[1] << 17; s4[2] ^= s4[0]; s4[3] ^= s4[1]; s4[1] ^= s4[2]; s4[0] ^= s4[3]; s4[2] ^= t; s4[3] = rotl(s4[3], 45); return r; }
static void seed(uint64_t x) { for (int i = 0; i < 4; i++) { x += 0x9e3779b97f4a7c15ull; uint64_t z = x; z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ull; z = (z ^ (z >> 27)) * 0x94d049bb133111ebull; s4[i] = z ^ (z >> 31); } }
static inline uint32_t below(uint32_t m) { return (uint32_t)(((rnd() >> 32) * m) >> 32); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static geom_t *g; static int8_t *f; static uint8_t *bad; static int32_t *delta; static long long viol;

static void recount(void) {
    viol = 0; memset(delta, 0, sizeof(int32_t) * g->npts);
    for (uint64_t l = 0; l < g->L; l++) {
        bad[l] = f[g->line[l][0]] * f[g->line[l][1]] * f[g->line[l][2]] != g->sgn[l];
        viol += bad[l];
        for (int t = 0; t < 3; t++) delta[g->line[l][t]] += bad[l] ? -1 : 1;
    }
}
static inline void flip(uint32_t i) {
    for (uint32_t o = g->inc_off[i]; o < g->inc_off[i + 1]; o++) {
        uint32_t l = g->inc[o]; int d = bad[l] ? 2 : -2;   /* bad->good: other points' delta goes from -1 to +1 */
        for (int t = 0; t < 3; t++) { uint32_t p = g->line[l][t]; if (p != i) delta[p] += d; }
        viol += bad[l] ? -1 : 1; bad[l] ^= 1;
    }
    delta[i] = -delta[i]; f[i] = -f[i];
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: tabu N kind seed seconds out [start]\n"); return 2; }
    int N = atoi(argv[1]); char kind = argv[2][0]; uint64_t sd = strtoull(argv[3], 0, 10); double secs = atof(argv[4]);
    const char *out = argv[5];
    seed(sd); g = geom_build(N, kind);
    f = malloc(g->npts); bad = malloc(g->L); delta = malloc(sizeof(int32_t) * g->npts);
    int8_t *best = malloc(g->npts); uint64_t *tabu = calloc(g->npts, sizeof(uint64_t));
    if (argc > 6) {
        int n2; char k2; long long c; uint8_t *bits;
        if (witness_read(argv[6], &n2, &k2, &c, &bits) || n2 != N || k2 != kind) {
            fprintf(stderr, "bad start\n");
            free(tabu); free(best); free(delta); free(bad); free(f); geom_free(g);
            return 2;
        }
        for (uint32_t i = 0; i < g->npts; i++) f[i] = bits[g->pts[i]] ? -1 : 1;
        free(bits);
    } else for (uint32_t i = 0; i < g->npts; i++) f[i] = (rnd() >> 63) ? -1 : 1;
    recount();
    long long bestv = viol; memcpy(best, f, g->npts);
    const char *td = getenv("TABU_DIV"); const char *fr = getenv("TABU_FRESH");
    uint32_t T = g->npts / (td ? atoi(td) : 10) + 3; int fresh_pct = fr ? atoi(fr) : 12; uint64_t it = 0, last_imp = 0, window = 20ull * g->npts;
    long long cur_best = viol;
    double t0 = now(), tend = t0 + secs;
    fprintf(stderr, "N=%d kind=%c pts=%u lines=%llu start=%lld\n", N, kind, g->npts, (unsigned long long)g->L, viol);
    uint32_t *cand = malloc(sizeof(uint32_t) * g->npts);
    while (1) {
        it++;
        if ((it & 1023) == 0 && now() > tend) break;
        int bd = 1 << 30; uint32_t nc = 0;
        for (uint32_t i = 0; i < g->npts; i++) {
            int d = delta[i];
            if (tabu[i] > it && !(viol + d < bestv)) continue;
            if (d < bd) { bd = d; nc = 0; }
            if (d == bd) cand[nc++] = i;
        }
        if (!nc) continue;
        uint32_t i = cand[below(nc)];
        flip(i); tabu[i] = it + T + below(T + 1);
        if (viol < cur_best) { cur_best = viol; last_imp = it; }
        if (viol < bestv) {
            bestv = viol; memcpy(best, f, g->npts);
            printf("%.1fs it=%llu best=%lld\n", now() - t0, (unsigned long long)it, bestv); fflush(stdout);
            witness_write(out, g, best, bestv);
        }
        if (it - last_imp > window) {                       /* perturb: restart near the global best */
            memcpy(f, best, g->npts);
            uint32_t k = 1 + below(g->npts / 8 + 1);
            for (uint32_t r = 0; r < k; r++) f[below(g->npts)] *= -1;
            recount(); cur_best = viol; last_imp = it; memset(tabu, 0, sizeof(uint64_t) * g->npts);
            if ((int)(rnd() % 100) < fresh_pct) { for (uint32_t q = 0; q < g->npts; q++) f[q] = (rnd() >> 63) ? -1 : 1; recount(); cur_best = viol; }
        }
    }
    long long chk = count_viol(g, best);
    printf("final N=%d kind=%c best=%lld recount=%lld iters=%llu\n", N, kind, bestv, chk, (unsigned long long)it);
    witness_write(out, g, best, bestv);
    free(cand); free(tabu); free(best); free(delta); free(bad); free(f); geom_free(g);
    return chk == bestv ? 0 : 1;
}
