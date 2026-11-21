/* Thin OpenSSL (>= 3.5) harness for SLH-DSA-SHA2-128s, called from Rust.
 * Keys are held as EVP_PKEY handles (as an OpenSSL user would); each sign or
 * verify call creates and frees its own EVP_PKEY_CTX, as typical callers do. */
#include <openssl/core_names.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <stdio.h>
#include <openssl/params.h>
#include <stdint.h>
#include <string.h>

#define ALG "SLH-DSA-SHA2-128s"

static EVP_SIGNATURE *g_sig = NULL;

int bench_ossl_init(void) {
    if (g_sig == NULL) g_sig = EVP_SIGNATURE_fetch(NULL, ALG, NULL);
    return g_sig != NULL;
}

/* Key generation from seed = SK.seed || SK.prf || PK.seed (48 bytes).
 * Returns the new key (caller frees with bench_ossl_free) or NULL. */
EVP_PKEY *bench_ossl_keygen_seed(const uint8_t *seed48) {
    EVP_PKEY *pkey = NULL;
    EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new_from_name(NULL, ALG, NULL);
    if (ctx == NULL) return NULL;
    OSSL_PARAM params[2];
    params[0] = OSSL_PARAM_construct_octet_string(OSSL_PKEY_PARAM_SLH_DSA_SEED, (void *)seed48, 48);
    params[1] = OSSL_PARAM_construct_end();
    if (EVP_PKEY_keygen_init(ctx) <= 0 || EVP_PKEY_CTX_set_params(ctx, params) <= 0 ||
        EVP_PKEY_generate(ctx, &pkey) <= 0) {
        pkey = NULL;
    }
    EVP_PKEY_CTX_free(ctx);
    return pkey;
}

void bench_ossl_free(EVP_PKEY *k) { EVP_PKEY_free(k); }

static EVP_PKEY *from_raw(const uint8_t *b, size_t len, int priv) {
    EVP_PKEY *pkey = NULL;
    EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new_from_name(NULL, ALG, NULL);
    if (ctx == NULL) return NULL;
    OSSL_PARAM params[2];
    params[0] = OSSL_PARAM_construct_octet_string(priv ? OSSL_PKEY_PARAM_PRIV_KEY : OSSL_PKEY_PARAM_PUB_KEY,
                                                  (void *)b, len);
    params[1] = OSSL_PARAM_construct_end();
    if (EVP_PKEY_fromdata_init(ctx) <= 0 ||
        EVP_PKEY_fromdata(ctx, &pkey, priv ? EVP_PKEY_KEYPAIR : EVP_PKEY_PUBLIC_KEY, params) <= 0)
        pkey = NULL;
    EVP_PKEY_CTX_free(ctx);
    return pkey;
}

EVP_PKEY *bench_ossl_load_priv(const uint8_t *sk64) { return from_raw(sk64, 64, 1); }
EVP_PKEY *bench_ossl_load_pub(const uint8_t *pk32) { return from_raw(pk32, 32, 0); }

/* Raw key export. Returns 1 on success. */
int bench_ossl_export(EVP_PKEY *k, uint8_t *sk64, uint8_t *pk32) {
    size_t l = 64;
    if (sk64 && EVP_PKEY_get_octet_string_param(k, OSSL_PKEY_PARAM_PRIV_KEY, sk64, 64, &l) <= 0) return 0;
    l = 32;
    if (pk32 && EVP_PKEY_get_octet_string_param(k, OSSL_PKEY_PARAM_PUB_KEY, pk32, 32, &l) <= 0) return 0;
    return 1;
}

/* Pure SLH-DSA sign, empty context. deterministic=1 uses opt_rand = PK.seed.
 * Returns signature length, or 0 on failure. */
size_t bench_ossl_sign(EVP_PKEY *k, const uint8_t *msg, size_t msglen, uint8_t *sig, size_t siglen,
                 int deterministic) {
    EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new_from_pkey(NULL, k, NULL);
    if (ctx == NULL) { fprintf(stderr, "bench_ossl_sign: no ctx\n"); ERR_print_errors_fp(stderr); return 0; }
    int det = deterministic;
    OSSL_PARAM params[2];
    params[0] = OSSL_PARAM_construct_int(OSSL_SIGNATURE_PARAM_DETERMINISTIC, &det);
    params[1] = OSSL_PARAM_construct_end();
    size_t out = siglen;
    int r1 = EVP_PKEY_sign_message_init(ctx, g_sig, params), r2 = -9;
    if (r1 <= 0 || (r2 = EVP_PKEY_sign(ctx, sig, &out, msg, msglen)) <= 0) {
        fprintf(stderr, "bench_ossl_sign: init=%d sign=%d out=%zu\n", r1, r2, out);
        ERR_print_errors_fp(stderr);
        out = 0;
    }
    EVP_PKEY_CTX_free(ctx);
    return out;
}

/* Returns 1 if valid, 0 otherwise. */
int bench_ossl_verify(EVP_PKEY *k, const uint8_t *msg, size_t msglen, const uint8_t *sig, size_t siglen) {
    EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new_from_pkey(NULL, k, NULL);
    if (ctx == NULL) return 0;
    int ok = EVP_PKEY_verify_message_init(ctx, g_sig, NULL) > 0 &&
             EVP_PKEY_verify(ctx, sig, siglen, msg, msglen) == 1;
    EVP_PKEY_CTX_free(ctx);
    return ok;
}

/* SHA-256 via EVP, for the hash micro-benchmark. */
static EVP_MD *g_md = NULL;
static EVP_MD_CTX *g_mdctx = NULL;
int bench_ossl_sha256(const uint8_t *msg, size_t len, uint8_t *out) {
    if (g_md == NULL) { g_md = EVP_MD_fetch(NULL, "SHA256", NULL); g_mdctx = EVP_MD_CTX_new(); }
    unsigned int l = 32;
    return EVP_DigestInit_ex2(g_mdctx, g_md, NULL) && EVP_DigestUpdate(g_mdctx, msg, len) &&
           EVP_DigestFinal_ex(g_mdctx, out, &l);
}
