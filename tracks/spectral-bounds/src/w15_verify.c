/* SPDX-FileCopyrightText: 2026 Alexander S. Donahue
 * SPDX-License-Identifier: Apache-2.0
 *
 * w15_verify.c — Exact 64-bit integer (zero floating-point) Pauli contextuality
 * witness verifier via integer Walsh-Hadamard transform and exact Hermitian A^2.
 *
 * Verifies witnesses in standard `data/witness/` format (`N kind claimed_viol`
 * followed by 4^N/4 hex characters, MSB nibble first, bit v set <=> f(v) = -1)
 * for kind 'f' (full W(2N-1,2)) and kind 'h' (hyperbolic quadric Q+(2N-1,2)),
 * for any 2 <= N <= 9 (including 8-qubit W(15,2) with 357,886,635 contexts and
 * Q+(15,2) with 90,516,075 contexts) with exact divisibility and excess-sum
 * invariants:
 *   1. Ar == Ar^T and Ai == -Ai^T (exact Hermiticity)
 *   2. tr(A^3) % (6 * D) == 0
 *   3. (L - beta) % 2 == 0
 *   4. tr(A^2 P_v) % (2 * D) == 0 for every nonzero v in S
 *   5. sum_{v in S} excess(v) == 3 * beta
 *
 * Usage: w15_verify [--strict-local-opt] FILE...
 * Exits 0 iff every file parses cleanly and matches its claimed violation count.
 */
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void *xcalloc(size_t nmemb, size_t size) {
    void *p = calloc(nmemb ? nmemb : 1, size ? size : 1);
    if (!p) {
        fprintf(stderr, "w15_verify: out of memory\n");
        exit(1);
    }
    return p;
}

static inline int popcount_u32(uint32_t x) {
    int c = 0;
    while (x) {
        x &= x - 1u;
        c++;
    }
    return c;
}

/* In-place integer Walsh-Hadamard transform of length D (power of two). */
static void fwht_i64(int64_t *v, uint32_t D) {
    for (uint32_t len = 1; len < D; len <<= 1) {
        for (uint32_t i = 0; i < D; i += (len << 1)) {
            for (uint32_t j = 0; j < len; j++) {
                int64_t a = v[i + j];
                int64_t b = v[i + j + len];
                v[i + j] = a + b;
                v[i + j + len] = a - b;
            }
        }
    }
}

static int read_witness_file(
    const char *path, int *N_out, char *kind_out, int64_t *claim_out, uint8_t **bits_out
) {
    FILE *fp = fopen(path, "r");
    if (!fp) {
        fprintf(stderr, "w15_verify: cannot open %s\n", path);
        return -1;
    }
    long long claim_ll = 0;
    if (fscanf(fp, "%d %c %lld", N_out, kind_out, &claim_ll) != 3) {
        fprintf(stderr, "w15_verify: malformed header in %s\n", path);
        fclose(fp);
        return -2;
    }
    int N = *N_out;
    char kind = *kind_out;
    if (N < 2 || N > 9 || (kind != 'f' && kind != 'h')) {
        fprintf(stderr, "w15_verify: unsupported N=%d or kind='%c' in %s\n", N, kind, path);
        fclose(fp);
        return -2;
    }
    size_t nall = (size_t)1u << (2 * N);
    size_t hex_len = nall / 4;
    char *hex = (char *)xcalloc(hex_len + 1, 1);

    int ch;
    while ((ch = fgetc(fp)) != EOF && (ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n')) {
    }
    size_t got = 0;
    while (ch != EOF && !(ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n')) {
        if (got >= hex_len) {
            fprintf(stderr, "w15_verify: hex payload too long in %s\n", path);
            free(hex);
            fclose(fp);
            return -3;
        }
        int ok = (ch >= '0' && ch <= '9') || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F');
        if (!ok) {
            fprintf(stderr, "w15_verify: non-hex character in %s\n", path);
            free(hex);
            fclose(fp);
            return -3;
        }
        hex[got++] = (char)((ch >= 'A' && ch <= 'F') ? (ch - 'A' + 'a') : ch);
        ch = fgetc(fp);
    }
    fclose(fp);
    if (got != hex_len) {
        fprintf(stderr, "w15_verify: expected %zu hex chars, got %zu in %s\n", hex_len, got, path);
        free(hex);
        return -3;
    }

    uint8_t *bits = (uint8_t *)xcalloc(nall, 1);
    for (size_t k = 0; k < hex_len; k++) {
        char c = hex[k];
        unsigned x = (c <= '9') ? (unsigned)(c - '0') : (unsigned)(c - 'a' + 10);
        size_t nib = hex_len - 1 - k;
        for (int b = 0; b < 4; b++) {
            bits[nib * 4 + (size_t)b] = (uint8_t)((x >> b) & 1u);
        }
    }
    free(hex);
    *claim_out = (int64_t)claim_ll;
    *bits_out = bits;
    return 0;
}

static int verify_one(const char *path, int strict_local_opt) {
    int N = 0;
    char kind = 0;
    int64_t claim = 0;
    uint8_t *bits = NULL;
    if (read_witness_file(path, &N, &kind, &claim, &bits) != 0) {
        return 1;
    }

    const uint32_t D = 1u << N;
    const size_t DD = (size_t)D * (size_t)D;
    const int real_only = (kind == 'h');

    int8_t *f = (int8_t *)xcalloc(DD, sizeof(int8_t));
    int64_t *gr = (int64_t *)xcalloc(DD, sizeof(int64_t));
    int64_t *gi = (int64_t *)xcalloc(DD, sizeof(int64_t));
    int64_t *Ar = (int64_t *)xcalloc(DD, sizeof(int64_t));
    int64_t *Ai = (int64_t *)xcalloc(DD, sizeof(int64_t));
    int64_t *Br = (int64_t *)xcalloc(DD, sizeof(int64_t));
    int64_t *Bi = (int64_t *)xcalloc(DD, sizeof(int64_t));
    int64_t *hr = (int64_t *)xcalloc(DD, sizeof(int64_t));
    int64_t *hi = (int64_t *)xcalloc(DD, sizeof(int64_t));

    int64_t npts = 0;
    for (uint32_t a = 0; a < D; a++) {
        for (uint32_t c = 0; c < D; c++) {
            if (a == 0 && c == 0) {
                continue;
            }
            uint32_t v = a | (c << N);
            int k = popcount_u32(a & c) & 3;
            if (real_only && (k & 1)) {
                continue;
            }
            int8_t sv = bits[v] ? (int8_t)-1 : (int8_t)1;
            f[(size_t)a * D + c] = sv;
            npts++;
            if (k == 0) {
                gr[(size_t)a * D + c] = sv;
            } else if (k == 1) {
                gi[(size_t)a * D + c] = sv;
            } else if (k == 2) {
                gr[(size_t)a * D + c] = -sv;
            } else {
                gi[(size_t)a * D + c] = -sv;
            }
        }
    }

    for (uint32_t a = 0; a < D; a++) {
        fwht_i64(gr + (size_t)a * D, D);
        fwht_i64(gi + (size_t)a * D, D);
        for (uint32_t b = 0; b < D; b++) {
            uint32_t r = b ^ a;
            Ar[(size_t)r * D + b] = gr[(size_t)a * D + b];
            Ai[(size_t)r * D + b] = gi[(size_t)a * D + b];
        }
    }

    int herm_ok = 1;
    for (uint32_t r = 0; r < D && herm_ok; r++) {
        for (uint32_t b = r; b < D; b++) {
            if (Ar[(size_t)r * D + b] != Ar[(size_t)b * D + r] ||
                Ai[(size_t)r * D + b] != -Ai[(size_t)b * D + r]) {
                herm_ok = 0;
                break;
            }
        }
    }
    if (!herm_ok) {
        fprintf(stderr, "FAIL %s: matrix A is not Hermitian\n", path);
        goto fail;
    }

    /* Compute exact integer B = A * A using A Hermitian (transpose cache-friendly). */
    for (uint32_t i = 0; i < D; i++) {
        const int64_t *Ari = Ar + (size_t)i * D;
        const int64_t *Aii = Ai + (size_t)i * D;
        for (uint32_t j = i; j < D; j++) {
            const int64_t *Arj = Ar + (size_t)j * D;
            const int64_t *Aij = Ai + (size_t)j * D;
            int64_t sr = 0;
            int64_t si = 0;
            for (uint32_t k = 0; k < D; k++) {
                /* A[k, j] = Ar[j, k] - i * Ai[j, k] because A is Hermitian. */
                sr += Ari[k] * Arj[k] + Aii[k] * Aij[k];
                si += Aii[k] * Arj[k] - Ari[k] * Aij[k];
            }
            Br[(size_t)i * D + j] = sr;
            Bi[(size_t)i * D + j] = si;
            if (i != j) {
                Br[(size_t)j * D + i] = sr;
                Bi[(size_t)j * D + i] = -si;
            }
        }
    }

    int64_t trA3 = 0;
    for (size_t idx = 0; idx < DD; idx++) {
        trA3 += Br[idx] * Ar[idx] + Bi[idx] * Ai[idx];
    }
    if (trA3 % (int64_t)(6u * D) != 0) {
        fprintf(stderr, "FAIL %s: tr(A^3)=%" PRId64 " not divisible by 6*D\n", path, trA3);
        goto fail;
    }
    int64_t beta = trA3 / (int64_t)(6u * D);

    int64_t D64 = (int64_t)D;
    int64_t L_tot = real_only
        ? ((D64 - 1) * (D64 + 2) * (D64 - 2) * (D64 + 4)) / 48
        : ((D64 * D64 - 1) * (D64 * D64 - 4)) / 12;
    if (((L_tot - beta) & 1) != 0) {
        fprintf(stderr, "FAIL %s: parity mismatch L=%" PRId64 ", beta=%" PRId64 "\n", path, L_tot, beta);
        goto fail;
    }
    int64_t viol = (L_tot - beta) / 2;

    /* Compute exact per-point excess e(v) = f(v) * tr(A^2 P_v) / (2 * D). */
    for (uint32_t a = 0; a < D; a++) {
        for (uint32_t b = 0; b < D; b++) {
            uint32_t r = b ^ a;
            hr[(size_t)a * D + b] = Br[(size_t)b * D + r];
            hi[(size_t)a * D + b] = Bi[(size_t)b * D + r];
        }
        fwht_i64(hr + (size_t)a * D, D);
        fwht_i64(hi + (size_t)a * D, D);
    }

    int64_t sum_exc = 0;
    int64_t neg_exc = 0;
    for (uint32_t a = 0; a < D; a++) {
        for (uint32_t c = 0; c < D; c++) {
            int8_t sv = f[(size_t)a * D + c];
            if (sv == 0) {
                continue;
            }
            int k = popcount_u32(a & c) & 3;
            int64_t trMP = 0;
            if (k == 0) {
                trMP = hr[(size_t)a * D + c];
            } else if (k == 1) {
                trMP = -hi[(size_t)a * D + c];
            } else if (k == 2) {
                trMP = -hr[(size_t)a * D + c];
            } else {
                trMP = hi[(size_t)a * D + c];
            }
            if (trMP % (int64_t)(2u * D) != 0) {
                fprintf(stderr, "FAIL %s: tr(A^2 P_v) not divisible by 2*D\n", path);
                goto fail;
            }
            int64_t exc = (int64_t)sv * (trMP / (int64_t)(2u * D));
            sum_exc += exc;
            if (exc < 0) {
                neg_exc++;
            }
        }
    }
    if (sum_exc != 3 * beta) {
        fprintf(
            stderr, "FAIL %s: sum(exc)=%" PRId64 " != 3*beta=%" PRId64 "\n",
            path, sum_exc, 3 * beta
        );
        goto fail;
    }

    int ok = (viol == claim) && (!strict_local_opt || neg_exc == 0);
    printf(
        "%s: N=%d kind=%c pts=%" PRId64 " lines=%" PRId64 " claimed=%" PRId64
        " exact=%" PRId64 " beta=%" PRId64 " negE=%" PRId64 " %s\n",
        path, N, kind, npts, L_tot, claim, viol, beta, neg_exc, ok ? "OK" : "MISMATCH"
    );
    free(bits);
    free(f);
    free(gr);
    free(gi);
    free(Ar);
    free(Ai);
    free(Br);
    free(Bi);
    free(hr);
    free(hi);
    return ok ? 0 : 1;

fail:
    free(bits);
    free(f);
    free(gr);
    free(gi);
    free(Ar);
    free(Ai);
    free(Br);
    free(Bi);
    free(hr);
    free(hi);
    return 1;
}

int main(int argc, char **argv) {
    int strict_local_opt = 0;
    int files = 0;
    int bad = 0;
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--strict-local-opt") == 0) {
            strict_local_opt = 1;
            continue;
        }
        files++;
        if (verify_one(argv[i], strict_local_opt) != 0) {
            bad = 1;
        }
    }
    if (files == 0) {
        fprintf(stderr, "Usage: w15_verify [--strict-local-opt] FILE...\n");
        return 2;
    }
    return bad;
}
