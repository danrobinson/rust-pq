#define main signature_benchmark_main
#include "openssl.c"
#undef main
#include <openssl/x509.h>

// EVP returns owned key objects. Include destruction of all but the retained last result.
static void codec(const char *family, int bits, char variant, int round) {
    char set[32], name[40];
    size_t n = bits / 8;
    snprintf(set, sizeof(set), "%s_%d%c", family, bits, variant);
    snprintf(name, sizeof(name), "SLH-DSA-%s-%d%c", strcmp(family, "sha2") ? "SHAKE" : "SHA2", bits, variant);
    unsigned char sk[128], pk[64];
    for (size_t i = 0; i < 4*n; ++i) sk[i] = (unsigned char)(i + 42 + round);
    memcpy(pk, sk + 2*n, 2*n);
    EVP_PKEY *secret = NULL, *public = NULL, *dec = NULL;
    int count = 256;
    uint64_t start = now();
    for (int i=0; i<count; ++i) {
        EVP_PKEY_free(secret);
        secret = EVP_PKEY_new_raw_private_key_ex(NULL, name, NULL, sk, 4*n);
        check(secret != NULL);
    }
    row(set, "secret_key_from", round, count, start);
    start = now();
    for (int i=0; i<count; ++i) {
        EVP_PKEY_free(public);
        public = EVP_PKEY_new_raw_public_key_ex(NULL, name, NULL, pk, 2*n);
        check(public != NULL);
    }
    row(set, "public_key_from", round, count, start);
    unsigned char *p8 = NULL, *spki = NULL;
    int p8len = 0, spkilen = 0;
    start = now();
    for (int i=0; i<count; ++i) {
        OPENSSL_free(p8);
        p8 = NULL;
        PKCS8_PRIV_KEY_INFO *info = EVP_PKEY2PKCS8(secret);
        check(info && (p8len = i2d_PKCS8_PRIV_KEY_INFO(info, &p8)) > 0);
        PKCS8_PRIV_KEY_INFO_free(info);
    }
    row(set, "pkcs8_encode", round, count, start);
    save(set, "p8", p8, p8len);
    start = now();
    for (int i=0; i<count; ++i) {
        OPENSSL_free(spki);
        spki = NULL;
        check((spkilen = i2d_PUBKEY(public, &spki)) > 0);
    }
    row(set, "spki_encode", round, count, start);
    save(set, "spki", spki, spkilen);
    start = now();
    for (int i=0; i<count; ++i) {
        EVP_PKEY_free(dec);
        const unsigned char *ptr = p8;
        PKCS8_PRIV_KEY_INFO *info = d2i_PKCS8_PRIV_KEY_INFO(NULL, &ptr, p8len);
        check(info && ptr == p8+p8len && (dec = EVP_PKCS82PKEY(info)) != NULL);
        PKCS8_PRIV_KEY_INFO_free(info);
    }
    row(set, "pkcs8_decode", round, count, start);
    size_t used = 0;
    unsigned char raw[128];
    check(EVP_PKEY_get_octet_string_param(dec, "priv", raw, sizeof(raw), &used) && used == 4*n && !memcmp(raw, sk, used));
    EVP_PKEY_free(dec);
    dec = NULL;
    start = now();
    for (int i=0; i<count; ++i) {
        EVP_PKEY_free(dec);
        const unsigned char *ptr = spki;
        dec = d2i_PUBKEY(NULL, &ptr, spkilen);
        check(dec && ptr == spki+spkilen);
    }
    row(set, "spki_decode", round, count, start);
    check(EVP_PKEY_get_octet_string_param(dec, "pub", raw, sizeof(raw), &used) && used == 2*n && !memcmp(raw, pk, used));
    EVP_PKEY_free(dec);
    EVP_PKEY_free(public);
    EVP_PKEY_free(secret);
    OPENSSL_free(p8);
    OPENSSL_free(spki);
}

int main(int argc, char **argv) {
    check(argc == 2);
    int round = atoi(argv[1]);
    for (int family = 0; family < 2; ++family)
        for (int bits = 128; bits <= 256; bits += 64)
            for (int v = 0; v < 2; ++v)
                codec(family ? "shake" : "sha2", bits, v ? 'f' : 's', round);
    return 0;
}
