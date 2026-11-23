// Benchmark the OpenSSL default provider's public pure SLH-DSA operations.
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/params.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static void check(int ok) {
    if (!ok) {
        ERR_print_errors_fp(stderr);
        abort();
    }
}

static uint64_t now(void) {
    struct timespec t;
    check(clock_gettime(CLOCK_MONOTONIC, &t) == 0);
    return (uint64_t)t.tv_sec * 1000000000ULL + t.tv_nsec;
}

static void row(const char *set, const char *op, int round, unsigned count, uint64_t start) {
    uint64_t elapsed = now() - start;
    printf("%s,%s,%d,%.3f\n", set, op, round, (double)elapsed / count);
}

static void save(const char *set, const char *suffix, const unsigned char *data, size_t len) {
    const char *dir = getenv("SLH_VECTORS");
    if (dir == NULL) return;
    char path[512];
    int length = snprintf(path, sizeof(path), "%s/%s.%s", dir, set, suffix);
    check(length > 0 && (size_t)length < sizeof(path));
    FILE *file = fopen(path, "wb");
    check(file && fwrite(data, 1, len, file) == len && fclose(file) == 0);
}

static void bench(const char *family, int bits, char variant, unsigned char *msg,
                  size_t len, int round) {
    char set[32], name[40];
    size_t n = bits / 8;
    snprintf(set, sizeof(set), "%s_%d%c", family, bits, variant);
    snprintf(name, sizeof(name), "SLH-DSA-%s-%d%c", strcmp(family, "sha2") ? "SHAKE" : "SHA2", bits, variant);
    unsigned char seed[96], entropy[32], sk[128], pk[64];
    for (size_t i = 0; i < 3*n; ++i) seed[i] = (unsigned char)(i + 42 + round);
    memset(entropy, 123 ^ round, n);
    OSSL_PARAM seed_params[] = { OSSL_PARAM_octet_string("seed", seed, 3*n), OSSL_PARAM_END };
    EVP_PKEY_CTX *generator = EVP_PKEY_CTX_new_from_name(NULL, name, NULL);
    EVP_SIGNATURE *alg = EVP_SIGNATURE_fetch(NULL, name, NULL);
    EVP_PKEY *key = NULL;
    check(generator && alg && EVP_PKEY_keygen_init(generator) > 0);
    check(EVP_PKEY_CTX_set_params(generator, seed_params) > 0);
    uint64_t start = now();
    check(EVP_PKEY_generate(generator, &key) > 0);
    row(set, "keygen", round, 1, start);
    size_t used;
    start = now();
    for (int i = 0; i < 256; ++i)
        check(EVP_PKEY_get_octet_string_param(key, "pub", pk, sizeof(pk), &used) > 0);
    row(set, "public_key", round, 256, start);
    check(used == 2*n);
    save(set, "pk", pk, used);
    check(EVP_PKEY_get_octet_string_param(key, "priv", sk, sizeof(sk), &used) > 0 && used == 4*n);
    save(set, "sk", sk, used);
    EVP_PKEY *pub = EVP_PKEY_new_raw_public_key_ex(NULL, name, NULL, pk, 2*n);
    int deterministic = 1;
    OSSL_PARAM det[] = { OSSL_PARAM_int("deterministic", &deterministic), OSSL_PARAM_END };
    OSSL_PARAM hedge[] = { OSSL_PARAM_octet_string("test-entropy", entropy, n), OSSL_PARAM_END };
    size_t siglen = (size_t)EVP_PKEY_get_size(key);
    unsigned char *sig = NULL;
    check(pub != NULL);
    for (int h = 0; h < 2; ++h) {
        start = now();
        unsigned char *out = malloc(siglen);
        EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new_from_pkey(NULL, key, NULL);
        check(ctx && out && EVP_PKEY_sign_message_init(ctx, alg, h ? hedge : det) > 0);
        check(EVP_PKEY_sign(ctx, out, &siglen, msg, len) > 0);
        EVP_PKEY_CTX_free(ctx);
        row(set, h ? "sign_hedged" : "sign", round, 1, start);
        save(set, h ? "hedged" : "sig", out, siglen);
        if (h) free(out); else sig = out;
    }
    start = now();
    for (int i = 0; i < 32; ++i) {
        EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new_from_pkey(NULL, pub, NULL);
        check(ctx && EVP_PKEY_verify_message_init(ctx, alg, NULL) > 0);
        check(EVP_PKEY_verify(ctx, sig, siglen, msg, len) == 1);
        EVP_PKEY_CTX_free(ctx);
    }
    row(set, "verify", round, 32, start);
    unsigned char wrong[] = "wrong";
    OSSL_PARAM bad_ctx[] = { OSSL_PARAM_octet_string("context-string", wrong, 5), OSSL_PARAM_END };
    EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new_from_pkey(NULL, pub, NULL);
    check(ctx && EVP_PKEY_verify_message_init(ctx, alg, bad_ctx) > 0);
    check(EVP_PKEY_verify(ctx, sig, siglen, msg, len) == 0);
    EVP_PKEY_CTX_free(ctx);
    free(sig);
    EVP_PKEY_free(pub);
    EVP_PKEY_free(key);
    EVP_SIGNATURE_free(alg);
    EVP_PKEY_CTX_free(generator);
}

int main(int argc, char **argv) {
    check(argc == 3);
    int round = atoi(argv[1]);
    size_t len = strtoul(argv[2], NULL, 10);
    unsigned char *msg = malloc(len);
    check(msg != NULL);
    memset(msg, 17 ^ round, len);
    for (int family = 0; family < 2; ++family)
        for (int bits = 128; bits <= 256; bits += 64)
            for (int v = 0; v < 2; ++v)
                bench(family ? "shake" : "sha2", bits, v ? 'f' : 's', msg, len, round);
    free(msg);
    return 0;
}
